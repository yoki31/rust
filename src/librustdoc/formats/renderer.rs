use rustc_data_structures::profiling::SelfProfilerRef;
use rustc_middle::ty::TyCtxt;

use crate::clean;
use crate::config::RenderOptions;
use crate::error::Error;
use crate::formats::cache::Cache;

/// Allows for different backends to rustdoc to be used with the `run_format()` function. Each
/// backend renderer has hooks for initialization, documenting an item, entering and exiting a
/// module, and cleanup/finalizing output.
pub(crate) trait FormatRenderer<'tcx>: Sized {
    /// Gives a description of the renderer. Used for performance profiling.
    fn descr() -> &'static str;

    /// Whether to call `item` recursively for modules
    ///
    /// This is true for html, and false for json. See #80664
    const RUN_ON_MODULE: bool;
    type InfoType;

    /// Sets up any state required for the renderer. When this is called the cache has already been
    /// populated.
    fn init(
        krate: clean::Crate,
        options: RenderOptions,
        cache: Cache,
        tcx: TyCtxt<'tcx>,
    ) -> Result<(Self, clean::Crate), Error>;

    /// Make a new renderer to render a child of the item currently being rendered.
    fn make_child_renderer(&mut self) -> Self::InfoType;
    fn set_back_info(&mut self, _info: Self::InfoType);

    /// Renders a single non-module item. This means no recursive sub-item rendering is required.
    fn item(&mut self, item: clean::Item) -> Result<(), Error>;

    /// Renders a module (should not handle recursing into children).
    fn mod_item_in(&mut self, item: &clean::Item) -> Result<(), Error>;

    /// Runs after recursively rendering all sub-items of a module.
    fn mod_item_out(&mut self) -> Result<(), Error> {
        Ok(())
    }

    /// Post processing hook for cleanup and dumping output to files.
    fn after_krate(&mut self) -> Result<(), Error>;

    fn cache(&self) -> &Cache;
}

fn run_format_inner<'tcx, T: FormatRenderer<'tcx>>(
    cx: &mut T,
    item: clean::Item,
    prof: &SelfProfilerRef,
) -> Result<(), Error> {
    if item.is_mod() && T::RUN_ON_MODULE {
        // modules are special because they add a namespace. We also need to
        // recurse into the items of the module as well.
        let _timer =
            prof.generic_activity_with_arg("render_mod_item", item.name.unwrap().to_string());

        cx.mod_item_in(&item)?;
        let (clean::StrippedItem(box clean::ModuleItem(module)) | clean::ModuleItem(module)) =
            item.inner.kind
        else {
            unreachable!()
        };
        for it in module.items {
            let info = cx.make_child_renderer();
            run_format_inner(cx, it, prof)?;
            cx.set_back_info(info);
        }

        cx.mod_item_out()?;
    // FIXME: checking `item.name.is_some()` is very implicit and leads to lots of special
    // cases. Use an explicit match instead.
    } else if let Some(item_name) = item.name
        && !item.is_extern_crate()
    {
        prof.generic_activity_with_arg("render_item", item_name.as_str()).run(|| cx.item(item))?;
    }
    Ok(())
}

/// Main method for rendering a crate.
pub(crate) fn run_format<'tcx, T: FormatRenderer<'tcx>>(
    krate: clean::Crate,
    options: RenderOptions,
    cache: Cache,
    tcx: TyCtxt<'tcx>,
) -> Result<(), Error> {
    let prof = &tcx.sess.prof;

    let emit_crate = options.should_emit_crate();
    let (mut format_renderer, krate) = prof
        .verbose_generic_activity_with_arg("create_renderer", T::descr())
        .run(|| T::init(krate, options, cache, tcx))?;

    if !emit_crate {
        return Ok(());
    }

    // Render the crate documentation
    run_format_inner(&mut format_renderer, krate.module, prof)?;

    prof.verbose_generic_activity_with_arg("renderer_after_krate", T::descr())
        .run(|| format_renderer.after_krate())
}
