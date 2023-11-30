// revisions: x86_64 i686
// assembly-output: emit-asm
//[x86_64] compile-flags: --target x86_64-unknown-linux-gnu
//[x86_64] needs-llvm-components: x86
//[i686] compile-flags: --target i686-unknown-linux-gnu
//[i686] needs-llvm-components: x86
// compile-flags: -C llvm-args=-x86-asm-syntax=intel

#![feature(no_core, lang_items)]
#![crate_type = "lib"]
#![no_core]

#[lang = "sized"]
trait Sized {}
#[lang = "copy"]
trait Copy {}

impl Copy for u8 {}

// Check that inline-asm stack probes are generated correctly.
// To avoid making this test fragile to slight asm changes,
// we only check that the stack pointer is decremented by a page at a time,
// instead of matching the whole probe sequence.

// CHECK-LABEL: small_stack_probe:
#[no_mangle]
pub fn small_stack_probe(x: u8, f: fn(&mut [u8; 8192])) {
    // CHECK-NOT: __rust_probestack
    // x86_64: sub rsp, 4096
    // i686: sub esp, 4096
    f(&mut [x; 8192]);
}

// CHECK-LABEL: big_stack_probe:
#[no_mangle]
pub fn big_stack_probe(x: u8, f: fn(&[u8; 65536])) {
    // CHECK-NOT: __rust_probestack
    // x86_64: sub rsp, 4096
    // i686: sub esp, 4096
    f(&mut [x; 65536]);
}
