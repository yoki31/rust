//! Utilities related to FFI bindings.
//!
//! This module provides utilities to handle data across non-Rust
//! interfaces, like other programming languages and the underlying
//! operating system. It is mainly of use for FFI (Foreign Function
//! Interface) bindings and code that needs to exchange C-like strings
//! with other languages.
//!
//! # Overview
//!
//! Rust represents owned strings with the [`String`] type, and
//! borrowed slices of strings with the [`str`] primitive. Both are
//! always in UTF-8 encoding, and may contain nul bytes in the middle,
//! i.e., if you look at the bytes that make up the string, there may
//! be a `\0` among them. Both `String` and `str` store their length
//! explicitly; there are no nul terminators at the end of strings
//! like in C.
//!
//! C strings are different from Rust strings:
//!
//! * **Encodings** - Rust strings are UTF-8, but C strings may use
//! other encodings. If you are using a string from C, you should
//! check its encoding explicitly, rather than just assuming that it
//! is UTF-8 like you can do in Rust.
//!
//! * **Nul terminators and implicit string lengths** - Often, C
//! strings are nul-terminated, i.e., they have a `\0` bytes at the
//! end. The length of a string buffer is not stored, but has to be
//! calculated; to compute the length of a string, C code must
//! manually call a function like `strlen()`. That function returns
//! the number of bytes in the string excluding the nul
//! terminator, so the buffer length is really `len+1` bytes.
//! Rust strings don't have a nul terminator; their length is always
//! stored and does not need to be calculated. While in Rust
//! accessing a string's length is an *O*(1) operation (because the
//! length is stored); in C it is an *O*(*n*) operation because the
//! length needs to be computed by scanning the string for the nul
//! terminator.
//!
//! * **Internal nul bytes** - When C strings have a nul
//! terminator byte, this usually means that they cannot have nul
//! bytes in the middle — a nul byte would essentially
//! truncate the string. Rust strings *can* have nul bytes in
//! the middle, because nul does not have to mark the end of the
//! string in Rust.
//!
//! # Representations of non-Rust strings
//!
//! [`ZString`] and [`ZStr`] are useful when you need to transfer
//! UTF-8 strings to and from languages with a C ABI, like Python.
//!
//! * **From Rust to C:** [`ZString`] represents an owned, C-friendly
//! string: it is nul-terminated, and has no internal nul bytes.
//! Rust code can create a [`ZString`] out of a normal string (provided
//! that the string doesn't have nul bytes in the middle), and
//! then use a variety of methods to obtain a raw <code>\*mut [u8]</code> that can
//! then be passed as an argument to functions which use the C
//! conventions for strings.
//!
//! * **From C to Rust:** [`ZStr`] represents a borrowed C string; it
//! is what you would use to wrap a raw <code>\*const [u8]</code> that you got from
//! a C function. A [`ZStr`] is guaranteed to be a nul-terminated array
//! of bytes. Once you have a [`ZStr`], you can convert it to a Rust
//! <code>&[str]</code> if it's valid UTF-8, or lossily convert it by adding
//! replacement characters.

#![stable(feature = "rust1", since = "1.0.0")]

#[stable(feature = "cstr_from_bytes", since = "1.10.0")]
pub use z_str::FromBytesWithNulError;
#[stable(feature = "cstring_from_vec_with_nul", since = "1.58.0")]
pub use z_str::FromVecWithNulError;
#[stable(feature = "rust1", since = "1.0.0")]
pub use z_str::{IntoStringError, NulError, ZStr, ZString};

mod z_str;

/// C-like `strlen`.
unsafe fn strlen(mut s: *const u8) -> usize {
    // In theory, compilers should be able to pattern-match this and replace
    // it with whatever's optimal on the platform, so that we don't need to
    // explicitly depend on libc.
    let mut len = 0;
    unsafe {
        while *s != b'\0' {
            len += 1;
            s = s.add(1);
        }
    }
    len
}
