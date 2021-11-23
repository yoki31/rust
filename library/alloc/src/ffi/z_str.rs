//! `ZString`s are like std's `CString`s except that they use `u8` instead of
//! `c_char`, so that they're not platform-dependent. The signedness of a
//! platform's `c_char` isn't all that meaningful anyway.

#![deny(unsafe_op_in_unsafe_fn)]

use super::strlen;
use crate::borrow::Borrow;
use crate::borrow::{Cow, ToOwned};
use crate::boxed::Box;
use crate::rc::Rc;
use crate::string::String;
use crate::sync::Arc;
use crate::vec::Vec;
use core::fmt;
use core::mem;
use core::num::NonZeroU8;
use core::ops;
use core::ptr;
use core::slice;
use core::slice::memchr;
use core::str::{self, Utf8Error};

/// A type representing an owned, C-compatible, nul-terminated string with no nul bytes in the
/// middle.
///
/// This type serves the purpose of being able to safely generate a
/// C-compatible string from a Rust byte slice or vector. An instance of this
/// type is a static guarantee that the underlying bytes contain no interior 0
/// bytes ("nul characters") and that the final byte is 0 ("nul terminator").
///
/// `ZString` is to <code>&[ZStr]</code> as [`String`] is to <code>&[str]</code>: the former
/// in each pair are owned strings; the latter are borrowed
/// references.
///
/// # Creating a `ZString`
///
/// A `ZString` is created from either a byte slice or a byte vector,
/// or anything that implements <code>[Into]<[Vec]<[u8]>></code> (for
/// example, you can build a `ZString` straight out of a [`String`] or
/// a <code>&[str]</code>, since both implement that trait).
///
/// The [`ZString::new`] method will actually check that the provided <code>&[[u8]]</code>
/// does not have 0 bytes in the middle, and return an error if it
/// finds one.
///
/// # Extracting a raw pointer to the whole C string
///
/// `ZString` implements an [`as_ptr`][`ZStr::as_ptr`] method through the [`Deref`]
/// trait. This method will give you a `*const u8` which you can
/// feed directly to extern functions that expect a nul-terminated
/// string, like C's `strdup()`. Notice that [`as_ptr`][`ZStr::as_ptr`] returns a
/// read-only pointer; if the C code writes to it, that causes
/// undefined behavior.
///
/// # Extracting a slice of the whole C string
///
/// Alternatively, you can obtain a <code>&[[u8]]</code> slice from a
/// `ZString` with the [`ZString::as_bytes`] method. Slices produced in this
/// way do *not* contain the trailing nul terminator. This is useful
/// when you will be calling an extern function that takes a `*const
/// u8` argument which is not necessarily nul-terminated, plus another
/// argument with the length of the string — like C's `strndup()`.
/// You can of course get the slice's length with its
/// [`len`][slice::len] method.
///
/// If you need a <code>&[[u8]]</code> slice *with* the nul terminator, you
/// can use [`ZString::as_bytes_with_nul`] instead.
///
/// Once you have the kind of slice you need (with or without a nul
/// terminator), you can call the slice's own
/// [`as_ptr`][slice::as_ptr] method to get a read-only raw pointer to pass to
/// extern functions. See the documentation for that function for a
/// discussion on ensuring the lifetime of the raw pointer.
///
/// [str]: prim@str "str"
/// [`Deref`]: ops::Deref
///
/// # Examples
///
/// ```ignore (extern-declaration)
/// # fn main() {
/// use alloc::ffi::ZString;
///
/// extern "C" {
///     fn my_printer(s: *const u8);
/// }
///
/// // We are certain that our string doesn't have 0 bytes in the middle,
/// // so we can .expect()
/// let c_to_print = ZString::new("Hello, world!").expect("ZString::new failed");
/// unsafe {
///     my_printer(c_to_print.as_ptr());
/// }
/// # }
/// ```
///
/// # Safety
///
/// `ZString` is intended for working with traditional C-style strings
/// (a sequence of non-nul bytes terminated by a single nul byte); the
/// primary use case for these kinds of strings is interoperating with C-like
/// code. Often you will need to transfer ownership to/from that external
/// code. It is strongly recommended that you thoroughly read through the
/// documentation of `ZString` before use, as improper ownership management
/// of `ZString` instances can lead to invalid memory accesses, memory leaks,
/// and other memory errors.
#[derive(PartialEq, PartialOrd, Eq, Ord, Hash, Clone)]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct ZString {
    // Invariant 1: the slice ends with a zero byte and has a length of at least one.
    // Invariant 2: the slice contains only one zero byte.
    // Improper usage of unsafe function can break Invariant 2, but not Invariant 1.
    inner: Box<[u8]>,
}

/// Representation of a borrowed C string.
///
/// This type represents a borrowed reference to a nul-terminated
/// array of bytes. It can be constructed safely from a <code>&[[u8]]</code>
/// slice, or unsafely from a raw `*const u8`. It can then be
/// converted to a Rust <code>&[str]</code> by performing UTF-8 validation, or
/// into an owned [`ZString`].
///
/// `&ZStr` is to [`ZString`] as <code>&[str]</code> is to [`String`]: the former
/// in each pair are borrowed references; the latter are owned
/// strings.
///
/// Note that this structure is **not** `repr(C)` and is not recommended to be
/// placed in the signatures of FFI functions. Instead, safe wrappers of FFI
/// functions may leverage the unsafe [`ZStr::from_ptr`] constructor to provide
/// a safe interface to other consumers.
///
/// # Examples
///
/// Inspecting a foreign C string:
///
/// ```ignore (extern-declaration)
/// use alloc::ffi::ZStr;
///
/// extern "C" { fn my_string() -> *const u8; }
///
/// unsafe {
///     let slice = ZStr::from_ptr(my_string());
///     println!("string buffer size without nul terminator: {}", slice.to_bytes().len());
/// }
/// ```
///
/// Passing a Rust-originating C string:
///
/// ```ignore (extern-declaration)
/// use alloc::ffi::{ZString, ZStr};
///
/// fn work(data: &ZStr) {
///     extern "C" { fn work_with(data: *const u8); }
///
///     unsafe { work_with(data.as_ptr()) }
/// }
///
/// let s = ZString::new("data data data data").expect("ZString::new failed");
/// work(&s);
/// ```
///
/// Converting a foreign C string into a Rust [`String`]:
///
/// ```ignore (extern-declaration)
/// use alloc::ffi::ZStr;
///
/// extern "C" { fn my_string() -> *const u8; }
///
/// fn my_string_safe() -> String {
///     unsafe {
///         ZStr::from_ptr(my_string()).to_string_lossy().into_owned()
///     }
/// }
///
/// println!("string: {}", my_string_safe());
/// ```
///
/// [str]: prim@str "str"
#[stable(feature = "rust1", since = "1.0.0")]
pub use core::ffi::ZStr;

/// An error indicating that an interior nul byte was found.
///
/// While Rust strings may contain nul bytes in the middle, C strings
/// can't, as that byte would effectively truncate the string.
///
/// This error is created by the [`new`][`ZString::new`] method on
/// [`ZString`]. See its documentation for more.
///
/// # Examples
///
/// ```
/// use alloc::ffi::{ZString, NulError};
///
/// let _: NulError = ZString::new(b"f\0oo".to_vec()).unwrap_err();
/// ```
#[derive(Clone, PartialEq, Eq, Debug)]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct NulError(usize, Vec<u8>);

/// An error indicating that a nul byte was not in the expected position.
///
/// The slice used to create a [`ZStr`] must have one and only one nul byte,
/// positioned at the end.
///
/// This error is created by the [`ZStr::from_bytes_with_nul`] method.
/// See its documentation for more.
///
/// # Examples
///
/// ```
/// use alloc::ffi::{ZStr, FromBytesWithNulError};
///
/// let _: FromBytesWithNulError = ZStr::from_bytes_with_nul(b"f\0oo").unwrap_err();
/// ```
#[stable(feature = "cstr_from_bytes", since = "1.10.0")]
pub use core::ffi::FromBytesWithNulError;

/// An error indicating that a nul byte was not in the expected position.
///
/// The vector used to create a [`ZString`] must have one and only one nul byte,
/// positioned at the end.
///
/// This error is created by the [`ZString::from_vec_with_nul`] method.
/// See its documentation for more.
///
/// # Examples
///
/// ```
/// use alloc::ffi::{ZString, FromVecWithNulError};
///
/// let _: FromVecWithNulError = ZString::from_vec_with_nul(b"f\0oo".to_vec()).unwrap_err();
/// ```
#[derive(Clone, PartialEq, Eq, Debug)]
#[stable(feature = "cstring_from_vec_with_nul", since = "1.58.0")]
pub struct FromVecWithNulError {
    error_kind: FromBytesWithNulErrorKind,
    bytes: Vec<u8>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum FromBytesWithNulErrorKind {
    InteriorNul(usize),
    NotNulTerminated,
}

#[stable(feature = "cstring_from_vec_with_nul", since = "1.58.0")]
impl FromVecWithNulError {
    /// Returns a slice of [`u8`]s bytes that were attempted to convert to a [`ZString`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// // Some invalid bytes in a vector
    /// let bytes = b"f\0oo".to_vec();
    ///
    /// let value = ZString::from_vec_with_nul(bytes.clone());
    ///
    /// assert_eq!(&bytes[..], value.unwrap_err().as_bytes());
    /// ```
    #[must_use]
    #[stable(feature = "cstring_from_vec_with_nul", since = "1.58.0")]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// Returns the bytes that were attempted to convert to a [`ZString`].
    ///
    /// This method is carefully constructed to avoid allocation. It will
    /// consume the error, moving out the bytes, so that a copy of the bytes
    /// does not need to be made.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// // Some invalid bytes in a vector
    /// let bytes = b"f\0oo".to_vec();
    ///
    /// let value = ZString::from_vec_with_nul(bytes.clone());
    ///
    /// assert_eq!(bytes, value.unwrap_err().into_bytes());
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "cstring_from_vec_with_nul", since = "1.58.0")]
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

/// An error indicating invalid UTF-8 when converting a [`ZString`] into a [`String`].
///
/// `ZString` is just a wrapper over a buffer of bytes with a nul terminator;
/// [`ZString::into_string`] performs UTF-8 validation on those bytes and may
/// return this error.
///
/// This `struct` is created by [`ZString::into_string()`]. See
/// its documentation for more.
#[derive(Clone, PartialEq, Eq, Debug)]
#[stable(feature = "cstring_into", since = "1.7.0")]
pub struct IntoStringError {
    inner: ZString,
    error: Utf8Error,
}

impl ZString {
    /// Creates a new C-compatible string from a container of bytes.
    ///
    /// This function will consume the provided data and use the
    /// underlying bytes to construct a new string, ensuring that
    /// there is a trailing 0 byte. This trailing 0 byte will be
    /// appended by this function; the provided data should *not*
    /// contain any 0 bytes in it.
    ///
    /// # Examples
    ///
    /// ```ignore (extern-declaration)
    /// use alloc::ffi::ZString;
    ///
    /// extern "C" { fn puts(s: *const u8); }
    ///
    /// let to_print = ZString::new("Hello!").expect("ZString::new failed");
    /// unsafe {
    ///     puts(to_print.as_ptr());
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// This function will return an error if the supplied bytes contain an
    /// internal 0 byte. The [`NulError`] returned will contain the bytes as well as
    /// the position of the nul byte.
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn new<T: Into<Vec<u8>>>(t: T) -> Result<ZString, NulError> {
        trait SpecIntoVec {
            fn into_vec(self) -> Vec<u8>;
        }
        impl<T: Into<Vec<u8>>> SpecIntoVec for T {
            default fn into_vec(self) -> Vec<u8> {
                self.into()
            }
        }
        // Specialization for avoiding reallocation.
        impl SpecIntoVec for &'_ [u8] {
            fn into_vec(self) -> Vec<u8> {
                let mut v = Vec::with_capacity(self.len() + 1);
                v.extend(self);
                v
            }
        }
        impl SpecIntoVec for &'_ str {
            fn into_vec(self) -> Vec<u8> {
                let mut v = Vec::with_capacity(self.len() + 1);
                v.extend(self.as_bytes());
                v
            }
        }

        Self::_new(SpecIntoVec::into_vec(t))
    }

    fn _new(bytes: Vec<u8>) -> Result<ZString, NulError> {
        match memchr::memchr(0, &bytes) {
            Some(i) => Err(NulError(i, bytes)),
            None => Ok(unsafe { ZString::from_vec_unchecked(bytes) }),
        }
    }

    /// Creates a C-compatible string by consuming a byte vector,
    /// without checking for interior 0 bytes.
    ///
    /// Trailing 0 byte will be appended by this function.
    ///
    /// This method is equivalent to [`ZString::new`] except that no runtime
    /// assertion is made that `v` contains no 0 bytes, and it requires an
    /// actual byte vector, not anything that can be converted to one with Into.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// let raw = b"foo".to_vec();
    /// unsafe {
    ///     let z_string = ZString::from_vec_unchecked(raw);
    /// }
    /// ```
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub unsafe fn from_vec_unchecked(mut v: Vec<u8>) -> ZString {
        v.reserve_exact(1);
        v.push(0);
        ZString { inner: v.into_boxed_slice() }
    }

    /// Retakes ownership of a `ZString` that was transferred to C via
    /// [`ZString::into_raw`].
    ///
    /// Additionally, the length of the string will be recalculated from the pointer.
    ///
    /// # Safety
    ///
    /// This should only ever be called with a pointer that was earlier
    /// obtained by calling [`ZString::into_raw`]. Other usage (e.g., trying to take
    /// ownership of a string that was allocated by foreign code) is likely to lead
    /// to undefined behavior or allocator corruption.
    ///
    /// It should be noted that the length isn't just "recomputed," but that
    /// the recomputed length must match the original length from the
    /// [`ZString::into_raw`] call. This means the [`ZString::into_raw`]/`from_raw`
    /// methods should not be used when passing the string to C functions that can
    /// modify the string's length.
    ///
    /// > **Note:** If you need to borrow a string that was allocated by
    /// > foreign code, use [`ZStr`]. If you need to take ownership of
    /// > a string that was allocated by foreign code, you will need to
    /// > make your own provisions for freeing it appropriately, likely
    /// > with the foreign code's API to do that.
    ///
    /// # Examples
    ///
    /// Creates a `ZString`, pass ownership to an `extern` function (via raw pointer), then retake
    /// ownership with `from_raw`:
    ///
    /// ```ignore (extern-declaration)
    /// use alloc::ffi::ZString;
    ///
    /// extern "C" {
    ///     fn some_extern_function(s: *mut u8);
    /// }
    ///
    /// let z_string = ZString::new("Hello!").expect("ZString::new failed");
    /// let raw = z_string.into_raw();
    /// unsafe {
    ///     some_extern_function(raw);
    ///     let z_string = ZString::from_raw(raw);
    /// }
    /// ```
    #[must_use = "call `drop(from_raw(ptr))` if you intend to drop the `ZString`"]
    #[stable(feature = "cstr_memory", since = "1.4.0")]
    pub unsafe fn from_raw(ptr: *mut u8) -> ZString {
        // SAFETY: This is called with a pointer that was obtained from a call
        // to `ZString::into_raw` and the length has not been modified. As such,
        // we know there is a NUL byte (and only one) at the end and that the
        // information about the size of the allocation is correct on Rust's
        // side.
        unsafe {
            let len = strlen(ptr) + 1; // Including the NUL byte
            let slice = slice::from_raw_parts_mut(ptr, len as usize);
            ZString { inner: Box::from_raw(slice as *mut [u8]) }
        }
    }

    /// Consumes the `ZString` and transfers ownership of the string to a C caller.
    ///
    /// The pointer which this function returns must be returned to Rust and reconstituted using
    /// [`ZString::from_raw`] to be properly deallocated. Specifically, one
    /// should *not* use the standard C `free()` function to deallocate
    /// this string.
    ///
    /// Failure to call [`ZString::from_raw`] will lead to a memory leak.
    ///
    /// The C side must **not** modify the length of the string (by writing a
    /// `null` somewhere inside the string or removing the final one) before
    /// it makes it back into Rust using [`ZString::from_raw`]. See the safety section
    /// in [`ZString::from_raw`].
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// let z_string = ZString::new("foo").expect("ZString::new failed");
    ///
    /// let ptr = z_string.into_raw();
    ///
    /// unsafe {
    ///     assert_eq!(b'f', *ptr as u8);
    ///     assert_eq!(b'o', *ptr.offset(1) as u8);
    ///     assert_eq!(b'o', *ptr.offset(2) as u8);
    ///     assert_eq!(b'\0', *ptr.offset(3) as u8);
    ///
    ///     // retake pointer to free memory
    ///     let _ = ZString::from_raw(ptr);
    /// }
    /// ```
    #[inline]
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "cstr_memory", since = "1.4.0")]
    pub fn into_raw(self) -> *mut u8 {
        Box::into_raw(self.into_inner()) as *mut u8
    }

    /// Converts the `ZString` into a [`String`] if it contains valid UTF-8 data.
    ///
    /// On failure, ownership of the original `ZString` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// let valid_utf8 = vec![b'f', b'o', b'o'];
    /// let zstring = ZString::new(valid_utf8).expect("ZString::new failed");
    /// assert_eq!(zstring.into_string().expect("into_string() call failed"), "foo");
    ///
    /// let invalid_utf8 = vec![b'f', 0xff, b'o', b'o'];
    /// let zstring = ZString::new(invalid_utf8).expect("ZString::new failed");
    /// let err = zstring.into_string().err().expect("into_string().err() failed");
    /// assert_eq!(err.utf8_error().valid_up_to(), 1);
    /// ```
    #[stable(feature = "cstring_into", since = "1.7.0")]
    pub fn into_string(self) -> Result<String, IntoStringError> {
        String::from_utf8(self.into_bytes()).map_err(|e| IntoStringError {
            error: e.utf8_error(),
            inner: unsafe { ZString::from_vec_unchecked(e.into_bytes()) },
        })
    }

    /// Consumes the `ZString` and returns the underlying byte buffer.
    ///
    /// The returned buffer does **not** contain the trailing nul
    /// terminator, and it is guaranteed to not have any interior nul
    /// bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// let z_string = ZString::new("foo").expect("ZString::new failed");
    /// let bytes = z_string.into_bytes();
    /// assert_eq!(bytes, vec![b'f', b'o', b'o']);
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "cstring_into", since = "1.7.0")]
    pub fn into_bytes(self) -> Vec<u8> {
        let inner = self.into_inner();
        #[cfg(test)]
        let mut vec = super::super::slice::into_vec(inner);
        #[cfg(not(test))]
        let mut vec = inner.into_vec();
        let _nul = vec.pop();
        debug_assert_eq!(_nul, Some(0u8));
        vec
    }

    /// Equivalent to [`ZString::into_bytes()`] except that the
    /// returned vector includes the trailing nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// let z_string = ZString::new("foo").expect("ZString::new failed");
    /// let bytes = z_string.into_bytes_with_nul();
    /// assert_eq!(bytes, vec![b'f', b'o', b'o', b'\0']);
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "cstring_into", since = "1.7.0")]
    pub fn into_bytes_with_nul(self) -> Vec<u8> {
        let inner = self.into_inner();
        #[cfg(test)]
        let vec = super::super::slice::into_vec(inner);
        #[cfg(not(test))]
        let vec = inner.into_vec();
        vec
    }

    /// Returns the contents of this `ZString` as a slice of bytes.
    ///
    /// The returned slice does **not** contain the trailing nul
    /// terminator, and it is guaranteed to not have any interior nul
    /// bytes. If you need the nul terminator, use
    /// [`ZString::as_bytes_with_nul`] instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// let z_string = ZString::new("foo").expect("ZString::new failed");
    /// let bytes = z_string.as_bytes();
    /// assert_eq!(bytes, &[b'f', b'o', b'o']);
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn as_bytes(&self) -> &[u8] {
        // SAFETY: ZString has a length at least 1
        unsafe { self.inner.get_unchecked(..self.inner.len() - 1) }
    }

    /// Equivalent to [`ZString::as_bytes()`] except that the
    /// returned slice includes the trailing nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// let z_string = ZString::new("foo").expect("ZString::new failed");
    /// let bytes = z_string.as_bytes_with_nul();
    /// assert_eq!(bytes, &[b'f', b'o', b'o', b'\0']);
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn as_bytes_with_nul(&self) -> &[u8] {
        &self.inner
    }

    /// Extracts a [`ZStr`] slice containing the entire string.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::{ZString, ZStr};
    ///
    /// let z_string = ZString::new(b"foo".to_vec()).expect("ZString::new failed");
    /// let zstr = z_string.as_z_str();
    /// assert_eq!(zstr,
    ///            ZStr::from_bytes_with_nul(b"foo\0").expect("ZStr::from_bytes_with_nul failed"));
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "as_c_str", since = "1.20.0")]
    pub fn as_z_str(&self) -> &ZStr {
        &*self
    }

    /// Converts this `ZString` into a boxed [`ZStr`].
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::{ZString, ZStr};
    ///
    /// let z_string = ZString::new(b"foo".to_vec()).expect("ZString::new failed");
    /// let boxed = z_string.into_boxed_z_str();
    /// assert_eq!(&*boxed,
    ///            ZStr::from_bytes_with_nul(b"foo\0").expect("ZStr::from_bytes_with_nul failed"));
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "into_boxed_c_str", since = "1.20.0")]
    pub fn into_boxed_z_str(self) -> Box<ZStr> {
        unsafe { Box::from_raw(Box::into_raw(self.into_inner()) as *mut ZStr) }
    }

    /// Bypass "move out of struct which implements [`Drop`] trait" restriction.
    #[inline]
    fn into_inner(self) -> Box<[u8]> {
        // Rationale: `mem::forget(self)` invalidates the previous call to `ptr::read(&self.inner)`
        // so we use `ManuallyDrop` to ensure `self` is not dropped.
        // Then we can return the box directly without invalidating it.
        // See https://github.com/rust-lang/rust/issues/62553.
        let this = mem::ManuallyDrop::new(self);
        unsafe { ptr::read(&this.inner) }
    }

    /// Converts a <code>[Vec]<[u8]></code> to a [`ZString`] without checking the
    /// invariants on the given [`Vec`].
    ///
    /// # Safety
    ///
    /// The given [`Vec`] **must** have one nul byte as its last element.
    /// This means it cannot be empty nor have any other nul byte anywhere else.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc::ffi::ZString;
    /// assert_eq!(
    ///     unsafe { ZString::from_vec_with_nul_unchecked(b"abc\0".to_vec()) },
    ///     unsafe { ZString::from_vec_unchecked(b"abc".to_vec()) }
    /// );
    /// ```
    #[must_use]
    #[stable(feature = "cstring_from_vec_with_nul", since = "1.58.0")]
    pub unsafe fn from_vec_with_nul_unchecked(v: Vec<u8>) -> Self {
        Self { inner: v.into_boxed_slice() }
    }

    /// Attempts to converts a <code>[Vec]<[u8]></code> to a [`ZString`].
    ///
    /// Runtime checks are present to ensure there is only one nul byte in the
    /// [`Vec`], its last element.
    ///
    /// # Errors
    ///
    /// If a nul byte is present and not the last element or no nul bytes
    /// is present, an error will be returned.
    ///
    /// # Examples
    ///
    /// A successful conversion will produce the same result as [`ZString::new`]
    /// when called without the ending nul byte.
    ///
    /// ```
    /// use alloc::ffi::ZString;
    /// assert_eq!(
    ///     ZString::from_vec_with_nul(b"abc\0".to_vec())
    ///         .expect("ZString::from_vec_with_nul failed"),
    ///     ZString::new(b"abc".to_vec()).expect("ZString::new failed")
    /// );
    /// ```
    ///
    /// An incorrectly formatted [`Vec`] will produce an error.
    ///
    /// ```
    /// use alloc::ffi::{ZString, FromVecWithNulError};
    /// // Interior nul byte
    /// let _: FromVecWithNulError = ZString::from_vec_with_nul(b"a\0bc".to_vec()).unwrap_err();
    /// // No nul byte
    /// let _: FromVecWithNulError = ZString::from_vec_with_nul(b"abc".to_vec()).unwrap_err();
    /// ```
    #[stable(feature = "cstring_from_vec_with_nul", since = "1.58.0")]
    pub fn from_vec_with_nul(v: Vec<u8>) -> Result<Self, FromVecWithNulError> {
        let nul_pos = memchr::memchr(0, &v);
        match nul_pos {
            Some(nul_pos) if nul_pos + 1 == v.len() => {
                // SAFETY: We know there is only one nul byte, at the end
                // of the vec.
                Ok(unsafe { Self::from_vec_with_nul_unchecked(v) })
            }
            Some(nul_pos) => Err(FromVecWithNulError {
                error_kind: FromBytesWithNulErrorKind::InteriorNul(nul_pos),
                bytes: v,
            }),
            None => Err(FromVecWithNulError {
                error_kind: FromBytesWithNulErrorKind::NotNulTerminated,
                bytes: v,
            }),
        }
    }

    /// Converts a `ZStr` into a <code>[Cow]<[str]></code>.
    ///
    /// If the contents of the `ZStr` are valid UTF-8 data, this
    /// function will return a <code>[Cow]::[Borrowed]\(&[str])</code>
    /// with the corresponding <code>&[str]</code> slice. Otherwise, it will
    /// replace any invalid UTF-8 sequences with
    /// [`U+FFFD REPLACEMENT CHARACTER`][U+FFFD] and return a
    /// <code>[Cow]::[Owned]\(&[str])</code> with the result.
    ///
    /// [str]: prim@str "str"
    /// [Borrowed]: Cow::Borrowed
    /// [Owned]: Cow::Owned
    /// [U+FFFD]: crate::char::REPLACEMENT_CHARACTER "std::char::REPLACEMENT_CHARACTER"
    ///
    /// # Examples
    ///
    /// Calling `to_string_lossy` on a `ZStr` containing valid UTF-8:
    ///
    /// ```
    /// use alloc::borrow::Cow;
    /// use alloc::ffi::{ZStr, ZString};
    ///
    /// let zstr = ZStr::from_bytes_with_nul(b"Hello World\0")
    ///                  .expect("ZStr::from_bytes_with_nul failed");
    /// assert_eq!(ZString::to_string_lossy(zstr), Cow::Borrowed("Hello World"));
    /// ```
    ///
    /// Calling `to_string_lossy` on a `ZStr` containing invalid UTF-8:
    ///
    /// ```
    /// use alloc::borrow::Cow;
    /// use alloc::ffi::{ZStr, ZString};
    ///
    /// let zstr = ZStr::from_bytes_with_nul(b"Hello \xF0\x90\x80World\0")
    ///                  .expect("ZStr::from_bytes_with_nul failed");
    /// assert_eq!(
    ///     ZString::to_string_lossy(zstr),
    ///     Cow::Owned(String::from("Hello �World")) as Cow<'_, str>
    /// );
    /// ```
    #[must_use = "this returns the result of the operation, \
                  without modifying the original"]
    #[stable(feature = "cstr_to_str", since = "1.4.0")]
    pub fn to_string_lossy<'a>(s: &'a ZStr) -> Cow<'a, str> {
        String::from_utf8_lossy(s.to_bytes())
    }

    /// Converts a <code>[Box]<[ZStr]></code> into a [`ZString`] without copying or allocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// let z_string = ZString::new(b"foo".to_vec()).expect("ZString::new failed");
    /// let boxed = z_string.into_boxed_z_str();
    /// assert_eq!(ZString::into_z_string(boxed), ZString::new("foo").expect("ZString::new failed"));
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "into_boxed_c_str", since = "1.20.0")]
    pub fn into_z_string(s: Box<ZStr>) -> ZString {
        let raw = Box::into_raw(s) as *mut [u8];
        ZString { inner: unsafe { Box::from_raw(raw) } }
    }
}

// Turns this `ZString` into an empty string to prevent
// memory-unsafe code from working by accident. Inline
// to prevent LLVM from optimizing it away in debug builds.
#[stable(feature = "cstring_drop", since = "1.13.0")]
impl Drop for ZString {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            *self.inner.get_unchecked_mut(0) = 0;
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl ops::Deref for ZString {
    type Target = ZStr;

    #[inline]
    fn deref(&self) -> &ZStr {
        unsafe { ZStr::from_bytes_with_nul_unchecked(self.as_bytes_with_nul()) }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Debug for ZString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

#[stable(feature = "cstring_into", since = "1.7.0")]
impl From<ZString> for Vec<u8> {
    /// Converts a [`ZString`] into a <code>[Vec]<[u8]></code>.
    ///
    /// The conversion consumes the [`ZString`], and removes the terminating NUL byte.
    #[inline]
    fn from(s: ZString) -> Vec<u8> {
        s.into_bytes()
    }
}

#[stable(feature = "cstr_default", since = "1.10.0")]
impl Default for ZString {
    /// Creates an empty `ZString`.
    fn default() -> ZString {
        let a: &ZStr = Default::default();
        a.to_owned()
    }
}

#[stable(feature = "cstr_borrow", since = "1.3.0")]
impl Borrow<ZStr> for ZString {
    #[inline]
    fn borrow(&self) -> &ZStr {
        self
    }
}

#[stable(feature = "cstring_from_cow_cstr", since = "1.28.0")]
impl<'a> From<Cow<'a, ZStr>> for ZString {
    #[inline]
    fn from(s: Cow<'a, ZStr>) -> Self {
        s.into_owned()
    }
}

#[stable(feature = "box_from_c_str", since = "1.17.0")]
#[cfg(not(test))] // FIXME: Are the conflicts in test mode fixable?
impl From<&ZStr> for Box<ZStr> {
    fn from(s: &ZStr) -> Box<ZStr> {
        let boxed: Box<[u8]> = Box::from(s.to_bytes_with_nul());
        unsafe { Box::from_raw(Box::into_raw(boxed) as *mut ZStr) }
    }
}

#[stable(feature = "box_from_cow", since = "1.45.0")]
#[cfg(not(test))] // FIXME: Are the conflicts in test mode fixable?
impl From<Cow<'_, ZStr>> for Box<ZStr> {
    #[inline]
    fn from(cow: Cow<'_, ZStr>) -> Box<ZStr> {
        match cow {
            Cow::Borrowed(s) => Box::from(s),
            Cow::Owned(s) => Box::from(s),
        }
    }
}

#[stable(feature = "c_string_from_box", since = "1.18.0")]
impl From<Box<ZStr>> for ZString {
    /// Converts a <code>[Box]<[ZStr]></code> into a [`ZString`] without copying or allocating.
    #[inline]
    fn from(s: Box<ZStr>) -> ZString {
        ZString::into_z_string(s)
    }
}

#[stable(feature = "cstring_from_vec_of_nonzerou8", since = "1.43.0")]
impl From<Vec<NonZeroU8>> for ZString {
    /// Converts a <code>[Vec]<[NonZeroU8]></code> into a [`ZString`] without
    /// copying nor checking for inner null bytes.
    #[inline]
    fn from(v: Vec<NonZeroU8>) -> ZString {
        unsafe {
            // Transmute `Vec<NonZeroU8>` to `Vec<u8>`.
            let v: Vec<u8> = {
                // SAFETY:
                //   - transmuting between `NonZeroU8` and `u8` is sound;
                //   - `alloc::Layout<NonZeroU8> == alloc::Layout<u8>`.
                let (ptr, len, cap): (*mut NonZeroU8, _, _) = Vec::into_raw_parts(v);
                Vec::from_raw_parts(ptr.cast::<u8>(), len, cap)
            };
            // SAFETY: `v` cannot contain null bytes, given the type-level
            // invariant of `NonZeroU8`.
            ZString::from_vec_unchecked(v)
        }
    }
}

#[cfg(not(test))] // FIXME: Are the conflicts in test mode fixable?
#[stable(feature = "more_box_slice_clone", since = "1.29.0")]
impl Clone for Box<ZStr> {
    #[inline]
    fn clone(&self) -> Self {
        (**self).into()
    }
}

#[stable(feature = "box_from_c_string", since = "1.20.0")]
impl From<ZString> for Box<ZStr> {
    /// Converts a [`ZString`] into a <code>[Box]<[ZStr]></code> without copying or allocating.
    #[inline]
    fn from(s: ZString) -> Box<ZStr> {
        s.into_boxed_z_str()
    }
}

#[stable(feature = "cow_from_cstr", since = "1.28.0")]
impl<'a> From<ZString> for Cow<'a, ZStr> {
    /// Converts a [`ZString`] into an owned [`Cow`] without copying or allocating.
    #[inline]
    fn from(s: ZString) -> Cow<'a, ZStr> {
        Cow::Owned(s)
    }
}

#[stable(feature = "cow_from_cstr", since = "1.28.0")]
impl<'a> From<&'a ZStr> for Cow<'a, ZStr> {
    /// Converts a [`ZStr`] into a borrowed [`Cow`] without copying or allocating.
    #[inline]
    fn from(s: &'a ZStr) -> Cow<'a, ZStr> {
        Cow::Borrowed(s)
    }
}

#[stable(feature = "cow_from_cstr", since = "1.28.0")]
impl<'a> From<&'a ZString> for Cow<'a, ZStr> {
    /// Converts a `&`[`ZString`] into a borrowed [`Cow`] without copying or allocating.
    #[inline]
    fn from(s: &'a ZString) -> Cow<'a, ZStr> {
        Cow::Borrowed(s.as_z_str())
    }
}

#[stable(feature = "shared_from_slice2", since = "1.24.0")]
impl From<ZString> for Arc<ZStr> {
    /// Converts a [`ZString`] into an <code>[Arc]<[ZStr]></code> without copying or allocating.
    #[inline]
    fn from(s: ZString) -> Arc<ZStr> {
        let arc: Arc<[u8]> = Arc::from(s.into_inner());
        unsafe { Arc::from_raw(Arc::into_raw(arc) as *const ZStr) }
    }
}

#[stable(feature = "shared_from_slice2", since = "1.24.0")]
impl From<&ZStr> for Arc<ZStr> {
    #[inline]
    fn from(s: &ZStr) -> Arc<ZStr> {
        let arc: Arc<[u8]> = Arc::from(s.to_bytes_with_nul());
        unsafe { Arc::from_raw(Arc::into_raw(arc) as *const ZStr) }
    }
}

#[stable(feature = "shared_from_slice2", since = "1.24.0")]
impl From<ZString> for Rc<ZStr> {
    /// Converts a [`ZString`] into an <code>[Rc]<[ZStr]></code> without copying or allocating.
    #[inline]
    fn from(s: ZString) -> Rc<ZStr> {
        let rc: Rc<[u8]> = Rc::from(s.into_inner());
        unsafe { Rc::from_raw(Rc::into_raw(rc) as *const ZStr) }
    }
}

#[stable(feature = "shared_from_slice2", since = "1.24.0")]
impl From<&ZStr> for Rc<ZStr> {
    #[inline]
    fn from(s: &ZStr) -> Rc<ZStr> {
        let rc: Rc<[u8]> = Rc::from(s.to_bytes_with_nul());
        unsafe { Rc::from_raw(Rc::into_raw(rc) as *const ZStr) }
    }
}

#[cfg(not(test))] // FIXME: Are the conflicts in test mode fixable?
#[stable(feature = "default_box_extra", since = "1.17.0")]
impl Default for Box<ZStr> {
    fn default() -> Box<ZStr> {
        let boxed: Box<[u8]> = Box::from([0]);
        unsafe { Box::from_raw(Box::into_raw(boxed) as *mut ZStr) }
    }
}

impl NulError {
    /// Returns the position of the nul byte in the slice that caused
    /// [`ZString::new`] to fail.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// let nul_error = ZString::new("foo\0bar").unwrap_err();
    /// assert_eq!(nul_error.nul_position(), 3);
    ///
    /// let nul_error = ZString::new("foo bar\0").unwrap_err();
    /// assert_eq!(nul_error.nul_position(), 7);
    /// ```
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn nul_position(&self) -> usize {
        self.0
    }

    /// Consumes this error, returning the underlying vector of bytes which
    /// generated the error in the first place.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc::ffi::ZString;
    ///
    /// let nul_error = ZString::new("foo\0bar").unwrap_err();
    /// assert_eq!(nul_error.into_vec(), b"foo\0bar");
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn into_vec(self) -> Vec<u8> {
        self.1
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl NulError {
    /// ```rust
    /// if let Err(e) = "xc".parse::<u32>() {
    ///     // Print `e` itself, no need for description().
    ///     eprintln!("Error: {}", e);
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_deprecated(since = "1.42.0", reason = "use the Display impl or to_string()")]
    #[allow(deprecated)]
    pub fn description(&self) -> &str {
        "nul byte found in data"
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Display for NulError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "nul byte found in provided data at position: {}", self.0)
    }
}

#[stable(feature = "cstring_from_vec_with_nul", since = "1.58.0")]
impl fmt::Display for FromVecWithNulError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.error_kind {
            FromBytesWithNulErrorKind::InteriorNul(pos) => {
                write!(f, "data provided contains an interior nul byte at pos {}", pos)
            }
            FromBytesWithNulErrorKind::NotNulTerminated => {
                write!(f, "data provided is not nul terminated")
            }
        }
    }
}

impl IntoStringError {
    /// Consumes this error, returning original [`ZString`] which generated the
    /// error.
    #[must_use = "`self` will be dropped if the result is not used"]
    #[stable(feature = "cstring_into", since = "1.7.0")]
    pub fn into_zstring(self) -> ZString {
        self.inner
    }

    /// Access the underlying UTF-8 error that was the cause of this error.
    #[must_use]
    #[stable(feature = "cstring_into", since = "1.7.0")]
    pub fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

#[stable(feature = "cstring_into", since = "1.7.0")]
impl IntoStringError {
    /// ```rust
    /// if let Err(e) = "xc".parse::<u32>() {
    ///     // Print `e` itself, no need for description().
    ///     eprintln!("Error: {}", e);
    /// }
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_deprecated(since = "1.42.0", reason = "use the Display impl or to_string()")]
    #[allow(deprecated)]
    pub fn description(&self) -> &str {
        "C string contained non-utf8 bytes"
    }

    /* FIXME: Figure out the lifetimes here.
    pub fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.error)
    }
    */
}

#[stable(feature = "cstring_into", since = "1.7.0")]
impl fmt::Display for IntoStringError {
    #[allow(deprecated, deprecated_in_future)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.description().fmt(f)
    }
}

#[stable(feature = "cstr_borrow", since = "1.3.0")]
impl ToOwned for ZStr {
    type Owned = ZString;

    fn to_owned(&self) -> ZString {
        ZString { inner: self.to_bytes_with_nul().into() }
    }

    #[cfg(not(test))] // FIXME: Are the conflicts in test mode fixable?
    fn clone_into(&self, target: &mut ZString) {
        let mut b = Vec::from(mem::take(&mut target.inner));
        self.to_bytes_with_nul().clone_into(&mut b);
        target.inner = b.into_boxed_slice();
    }
}

#[stable(feature = "cstring_asref", since = "1.7.0")]
impl From<&ZStr> for ZString {
    fn from(s: &ZStr) -> ZString {
        s.to_owned()
    }
}

#[stable(feature = "cstring_asref", since = "1.7.0")]
impl ops::Index<ops::RangeFull> for ZString {
    type Output = ZStr;

    #[inline]
    fn index(&self, _index: ops::RangeFull) -> &ZStr {
        self
    }
}

#[stable(feature = "cstring_asref", since = "1.7.0")]
impl AsRef<ZStr> for ZString {
    #[inline]
    fn as_ref(&self) -> &ZStr {
        self
    }
}
