//! Type definitions for core I/O functionality.

#![stable(feature = "rust1", since = "1.0.0")]

/// Enumeration of possible methods to seek within an I/O object.
///
/// It is used by the [`Seek`] trait.
///
/// [`Seek`]: std::io::Seek
#[derive(Copy, PartialEq, Eq, Clone, Debug)]
#[stable(feature = "rust1", since = "1.0.0")]
pub enum SeekFrom {
    /// Sets the offset to the provided number of bytes.
    #[stable(feature = "rust1", since = "1.0.0")]
    Start(#[stable(feature = "rust1", since = "1.0.0")] u64),

    /// Sets the offset to the size of this object plus the specified number of
    /// bytes.
    ///
    /// It is possible to seek beyond the end of an object, but it's an error to
    /// seek before byte 0.
    #[stable(feature = "rust1", since = "1.0.0")]
    End(#[stable(feature = "rust1", since = "1.0.0")] i64),

    /// Sets the offset to the current position plus the specified number of
    /// bytes.
    ///
    /// It is possible to seek beyond the end of an object, but it's an error to
    /// seek before byte 0.
    #[stable(feature = "rust1", since = "1.0.0")]
    Current(#[stable(feature = "rust1", since = "1.0.0")] i64),
}
