//! `ZStr`s are like std's `CStr`s except that they use `u8` instead of
//! `c_char`, so that they're not platform-dependent. The signedness of a
//! platform's `c_char` isn't all that meaningful anyway.

#![deny(unsafe_op_in_unsafe_fn)]

use super::strlen;
use crate::ascii;
use crate::cmp::Ordering;
use crate::fmt::{self, Write};
use crate::ops;
use crate::slice;
use crate::slice::memchr;
use crate::str;

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
/// use std::ffi::ZStr;
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
/// use std::ffi::{ZString, ZStr};
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
/// use std::ffi::ZStr;
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
#[derive(Hash)]
#[stable(feature = "rust1", since = "1.0.0")]
// FIXME:
// `fn from` in `impl From<&ZStr> for Box<ZStr>` current implementation relies
// on `ZStr` being layout-compatible with `[u8]`.
// When attribute privacy is implemented, `ZStr` should be annotated as `#[repr(transparent)]`.
// Anyway, `ZStr` representation and layout are considered implementation detail, are
// not documented and must not be relied upon.
pub struct ZStr {
    // FIXME: this should not be represented with a DST slice but rather with
    //        just a raw `u8` along with some form of marker to make
    //        this an unsized type. Essentially `sizeof(&ZStr)` should be the
    //        same as `sizeof(&u8)` but `ZStr` should be an unsized type.
    inner: [u8],
}

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
/// use std::ffi::{ZStr, FromBytesWithNulError};
///
/// let _: FromBytesWithNulError = ZStr::from_bytes_with_nul(b"f\0oo").unwrap_err();
/// ```
#[derive(Clone, PartialEq, Eq, Debug)]
#[stable(feature = "cstr_from_bytes", since = "1.10.0")]
pub struct FromBytesWithNulError {
    kind: FromBytesWithNulErrorKind,
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum FromBytesWithNulErrorKind {
    InteriorNul(usize),
    NotNulTerminated,
}

impl FromBytesWithNulError {
    fn interior_nul(pos: usize) -> FromBytesWithNulError {
        FromBytesWithNulError { kind: FromBytesWithNulErrorKind::InteriorNul(pos) }
    }
    fn not_nul_terminated() -> FromBytesWithNulError {
        FromBytesWithNulError { kind: FromBytesWithNulErrorKind::NotNulTerminated }
    }
}

#[stable(feature = "cstr_debug", since = "1.3.0")]
impl fmt::Debug for ZStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"")?;
        for byte in self.to_bytes().iter().flat_map(|&b| ascii::escape_default(b)) {
            f.write_char(byte as char)?;
        }
        write!(f, "\"")
    }
}

#[stable(feature = "cstr_default", since = "1.10.0")]
impl Default for &ZStr {
    fn default() -> Self {
        const SLICE: &[u8] = &[0];
        unsafe { ZStr::from_ptr(SLICE.as_ptr()) }
    }
}

#[stable(feature = "frombyteswithnulerror_impls", since = "1.17.0")]
impl FromBytesWithNulError {
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
        match self.kind {
            FromBytesWithNulErrorKind::InteriorNul(..) => {
                "data provided contains an interior nul byte"
            }
            FromBytesWithNulErrorKind::NotNulTerminated => "data provided is not nul terminated",
        }
    }
}

#[stable(feature = "frombyteswithnulerror_impls", since = "1.17.0")]
impl fmt::Display for FromBytesWithNulError {
    #[allow(deprecated, deprecated_in_future)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.description())?;
        if let FromBytesWithNulErrorKind::InteriorNul(pos) = self.kind {
            write!(f, " at byte pos {}", pos)?;
        }
        Ok(())
    }
}

impl ZStr {
    /// Wraps a raw C string with a safe C string wrapper.
    ///
    /// This function will wrap the provided `ptr` with a `ZStr` wrapper, which
    /// allows inspection and interoperation of non-owned C strings. The total
    /// size of the raw C string must be smaller than `isize::MAX` **bytes**
    /// in memory due to calling the `slice::from_raw_parts` function.
    /// This method is unsafe for a number of reasons:
    ///
    /// * There is no guarantee to the validity of `ptr`.
    /// * The returned lifetime is not guaranteed to be the actual lifetime of
    ///   `ptr`.
    /// * There is no guarantee that the memory pointed to by `ptr` contains a
    ///   valid nul terminator byte at the end of the string.
    /// * It is not guaranteed that the memory pointed by `ptr` won't change
    ///   before the `ZStr` has been destroyed.
    ///
    /// > **Note**: This operation is intended to be a 0-cost cast but it is
    /// > currently implemented with an up-front calculation of the length of
    /// > the string. This is not guaranteed to always be the case.
    ///
    /// # Examples
    ///
    /// ```ignore (extern-declaration)
    /// # fn main() {
    /// use std::ffi::ZStr;
    ///
    /// extern "C" {
    ///     fn my_string() -> *const u8;
    /// }
    ///
    /// unsafe {
    ///     let slice = ZStr::from_ptr(my_string());
    ///     println!("string returned: {}", slice.to_str().unwrap());
    /// }
    /// # }
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub unsafe fn from_ptr<'a>(ptr: *const u8) -> &'a ZStr {
        // SAFETY: The caller has provided a pointer that points to a valid C
        // string with a NUL terminator of size less than `isize::MAX`, whose
        // content remain valid and doesn't change for the lifetime of the
        // returned `ZStr`.
        //
        // Thus computing the length is fine (a NUL byte exists), the call to
        // from_raw_parts is safe because we know the length is at most `isize::MAX`, meaning
        // the call to `from_bytes_with_nul_unchecked` is correct.
        //
        // The cast from u8 to u8 is ok because a u8 is always one byte.
        unsafe {
            let len = strlen(ptr);
            ZStr::from_bytes_with_nul_unchecked(slice::from_raw_parts(ptr, len as usize + 1))
        }
    }

    /// Creates a C string wrapper from a byte slice.
    ///
    /// This function will cast the provided `bytes` to a `ZStr`
    /// wrapper after ensuring that the byte slice is nul-terminated
    /// and does not contain any interior nul bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ffi::ZStr;
    ///
    /// let cstr = ZStr::from_bytes_with_nul(b"hello\0");
    /// assert!(cstr.is_ok());
    /// ```
    ///
    /// Creating a `ZStr` without a trailing nul terminator is an error:
    ///
    /// ```
    /// use std::ffi::ZStr;
    ///
    /// let cstr = ZStr::from_bytes_with_nul(b"hello");
    /// assert!(cstr.is_err());
    /// ```
    ///
    /// Creating a `ZStr` with an interior nul byte is an error:
    ///
    /// ```
    /// use std::ffi::ZStr;
    ///
    /// let cstr = ZStr::from_bytes_with_nul(b"he\0llo\0");
    /// assert!(cstr.is_err());
    /// ```
    #[stable(feature = "cstr_from_bytes", since = "1.10.0")]
    pub fn from_bytes_with_nul(bytes: &[u8]) -> Result<&ZStr, FromBytesWithNulError> {
        let nul_pos = memchr::memchr(0, bytes);
        if let Some(nul_pos) = nul_pos {
            if nul_pos + 1 != bytes.len() {
                return Err(FromBytesWithNulError::interior_nul(nul_pos));
            }
            Ok(unsafe { ZStr::from_bytes_with_nul_unchecked(bytes) })
        } else {
            Err(FromBytesWithNulError::not_nul_terminated())
        }
    }

    /// Unsafely creates a C string wrapper from a byte slice.
    ///
    /// This function will cast the provided `bytes` to a `ZStr` wrapper without
    /// performing any sanity checks. The provided slice **must** be nul-terminated
    /// and not contain any interior nul bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ffi::{ZStr, ZString};
    ///
    /// unsafe {
    ///     let cstring = ZString::new("hello").expect("ZString::new failed");
    ///     let cstr = ZStr::from_bytes_with_nul_unchecked(cstring.to_bytes_with_nul());
    ///     assert_eq!(cstr, &*cstring);
    /// }
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "cstr_from_bytes", since = "1.10.0")]
    #[rustc_const_unstable(feature = "const_cstr_unchecked", issue = "90343")]
    pub const unsafe fn from_bytes_with_nul_unchecked(bytes: &[u8]) -> &ZStr {
        // SAFETY: Casting to ZStr is safe because its internal representation
        // is a [u8] too (safe only inside std).
        // Dereferencing the obtained pointer is safe because it comes from a
        // reference. Making a reference is then safe because its lifetime
        // is bound by the lifetime of the given `bytes`.
        unsafe { &*(bytes as *const [u8] as *const ZStr) }
    }

    /// Returns the inner pointer to this C string.
    ///
    /// The returned pointer will be valid for as long as `self` is, and points
    /// to a contiguous region of memory terminated with a 0 byte to represent
    /// the end of the string.
    ///
    /// **WARNING**
    ///
    /// The returned pointer is read-only; writing to it (including passing it
    /// to C code that writes to it) causes undefined behavior.
    ///
    /// It is your responsibility to make sure that the underlying memory is not
    /// freed too early. For example, the following code will cause undefined
    /// behavior when `ptr` is used inside the `unsafe` block:
    ///
    /// ```no_run
    /// # #![allow(unused_must_use)] #![allow(temporary_cstring_as_ptr)]
    /// use std::ffi::ZString;
    ///
    /// let ptr = ZString::new("Hello").expect("ZString::new failed").as_ptr();
    /// unsafe {
    ///     // `ptr` is dangling
    ///     *ptr;
    /// }
    /// ```
    ///
    /// This happens because the pointer returned by `as_ptr` does not carry any
    /// lifetime information and the [`ZString`] is deallocated immediately after
    /// the `ZString::new("Hello").expect("ZString::new failed").as_ptr()`
    /// expression is evaluated.
    /// To fix the problem, bind the `ZString` to a local variable:
    ///
    /// ```no_run
    /// # #![allow(unused_must_use)]
    /// use std::ffi::ZString;
    ///
    /// let hello = ZString::new("Hello").expect("ZString::new failed");
    /// let ptr = hello.as_ptr();
    /// unsafe {
    ///     // `ptr` is valid because `hello` is in scope
    ///     *ptr;
    /// }
    /// ```
    ///
    /// This way, the lifetime of the [`ZString`] in `hello` encompasses
    /// the lifetime of `ptr` and the `unsafe` block.
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_stable(feature = "const_str_as_ptr", since = "1.32.0")]
    pub const fn as_ptr(&self) -> *const u8 {
        self.inner.as_ptr()
    }

    /// Converts this C string to a byte slice.
    ///
    /// The returned slice will **not** contain the trailing nul terminator that this C
    /// string has.
    ///
    /// > **Note**: This method is currently implemented as a constant-time
    /// > cast, but it is planned to alter its definition in the future to
    /// > perform the length calculation whenever this method is called.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ffi::ZStr;
    ///
    /// let cstr = ZStr::from_bytes_with_nul(b"foo\0").expect("ZStr::from_bytes_with_nul failed");
    /// assert_eq!(cstr.to_bytes(), b"foo");
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, \
                  without modifying the original"]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn to_bytes(&self) -> &[u8] {
        let bytes = self.to_bytes_with_nul();
        // SAFETY: to_bytes_with_nul returns slice with length at least 1
        unsafe { bytes.get_unchecked(..bytes.len() - 1) }
    }

    /// Converts this C string to a byte slice containing the trailing 0 byte.
    ///
    /// This function is the equivalent of [`ZStr::to_bytes`] except that it
    /// will retain the trailing nul terminator instead of chopping it off.
    ///
    /// > **Note**: This method is currently implemented as a 0-cost cast, but
    /// > it is planned to alter its definition in the future to perform the
    /// > length calculation whenever this method is called.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ffi::ZStr;
    ///
    /// let cstr = ZStr::from_bytes_with_nul(b"foo\0").expect("ZStr::from_bytes_with_nul failed");
    /// assert_eq!(cstr.to_bytes_with_nul(), b"foo\0");
    /// ```
    #[inline]
    #[must_use = "this returns the result of the operation, \
                  without modifying the original"]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn to_bytes_with_nul(&self) -> &[u8] {
        unsafe { &*(&self.inner as *const [u8]) }
    }

    /// Yields a <code>&[str]</code> slice if the `ZStr` contains valid UTF-8.
    ///
    /// If the contents of the `ZStr` are valid UTF-8 data, this
    /// function will return the corresponding <code>&[str]</code> slice. Otherwise,
    /// it will return an error with details of where UTF-8 validation failed.
    ///
    /// [str]: prim@str "str"
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ffi::ZStr;
    ///
    /// let cstr = ZStr::from_bytes_with_nul(b"foo\0").expect("ZStr::from_bytes_with_nul failed");
    /// assert_eq!(cstr.to_str(), Ok("foo"));
    /// ```
    #[stable(feature = "cstr_to_str", since = "1.4.0")]
    pub fn to_str(&self) -> Result<&str, str::Utf8Error> {
        // N.B., when `ZStr` is changed to perform the length check in `.to_bytes()`
        // instead of in `from_ptr()`, it may be worth considering if this should
        // be rewritten to do the UTF-8 check inline with the length calculation
        // instead of doing it afterwards.
        str::from_utf8(self.to_bytes())
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl PartialEq for ZStr {
    fn eq(&self, other: &ZStr) -> bool {
        self.to_bytes().eq(other.to_bytes())
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl Eq for ZStr {}
#[stable(feature = "rust1", since = "1.0.0")]
impl PartialOrd for ZStr {
    fn partial_cmp(&self, other: &ZStr) -> Option<Ordering> {
        self.to_bytes().partial_cmp(&other.to_bytes())
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl Ord for ZStr {
    fn cmp(&self, other: &ZStr) -> Ordering {
        self.to_bytes().cmp(&other.to_bytes())
    }
}

#[stable(feature = "cstr_range_from", since = "1.47.0")]
impl ops::Index<ops::RangeFrom<usize>> for ZStr {
    type Output = ZStr;

    fn index(&self, index: ops::RangeFrom<usize>) -> &ZStr {
        let bytes = self.to_bytes_with_nul();
        // we need to manually check the starting index to account for the null
        // byte, since otherwise we could get an empty string that doesn't end
        // in a null.
        if index.start < bytes.len() {
            unsafe { ZStr::from_bytes_with_nul_unchecked(&bytes[index.start..]) }
        } else {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                bytes.len(),
                index.start
            );
        }
    }
}

#[stable(feature = "cstring_asref", since = "1.7.0")]
impl AsRef<ZStr> for ZStr {
    #[inline]
    fn as_ref(&self) -> &ZStr {
        self
    }
}
