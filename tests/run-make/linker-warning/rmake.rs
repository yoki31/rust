use run_make_support::{Rustc, rustc};

fn run_rustc() -> Rustc {
    let mut rustc = rustc();
    rustc.arg("main.rs").output("main").linker("./fake-linker");
    rustc
}

fn main() {
    // first, compile our linker
    rustc().arg("fake-linker.rs").output("fake-linker").run();

    // Run rustc with our fake linker, and make sure it shows warnings
    let warnings = run_rustc().link_arg("run_make_warn").run();
    warnings.assert_stderr_contains("warning: linker stderr: bar");

    // Make sure it shows stdout, but only when --verbose is passed
    run_rustc()
        .link_arg("run_make_info")
        .verbose()
        .run()
        .assert_stderr_contains("warning: linker stdout: foo");
    run_rustc()
        .link_arg("run_make_info")
        .run()
        .assert_stderr_not_contains("warning: linker stdout: foo");

    // Make sure we short-circuit this new path if the linker exits with an error
    // (so the diagnostic is less verbose)
    run_rustc().link_arg("run_make_error").run_fail().assert_stderr_contains("note: error: baz");

    // Make sure we don't show the linker args unless `--verbose` is passed
    run_rustc()
        .link_arg("run_make_error")
        .verbose()
        .run_fail()
        .assert_stderr_contains_regex("fake-linker.*run_make_error")
        .assert_stderr_not_contains("object files omitted")
        .assert_stderr_contains_regex(r"lib(/|\\\\)libstd");
    run_rustc()
        .link_arg("run_make_error")
        .run_fail()
        .assert_stderr_contains("fake-linker")
        .assert_stderr_contains("object files omitted")
        .assert_stderr_contains_regex(r"\{")
        .assert_stderr_not_contains_regex(r"lib(/|\\\\)libstd");

    // Make sure we show linker warnings even across `-Z no-link`
    rustc()
        .arg("-Zno-link")
        .input("-")
        .stdin_buf("#![deny(linker_messages)] \n fn main() {}")
        .run()
        .assert_stderr_equals("");
    rustc()
        .arg("-Zlink-only")
        .arg("rust_out.rlink")
        .linker("./fake-linker")
        .link_arg("run_make_warn")
        .run_fail()
        // NOTE: the error message here is quite bad (we don't have a source
        // span, but still try to print the lint source). But `-Z link-only` is
        // unstable and this still shows the linker warning itself so this is
        // probably good enough.
        .assert_stderr_contains("linker stderr: bar");

    // Same thing, but with json output.
    rustc()
        .error_format("json")
        .arg("-Zlink-only")
        .arg("rust_out.rlink")
        .linker("./fake-linker")
        .link_arg("run_make_warn")
        .run_fail()
        .assert_stderr_contains(r#""$message_type":"diagnostic""#);
}
