//! Raw Unix-like file descriptors.

#![stable(feature = "rust1", since = "1.0.0")]

use crate::fs;
use crate::io;
#[cfg(unix)]
use crate::os::unix::io::OwnedFd;
#[cfg(target_os = "wasi")]
use crate::os::wasi::io::OwnedFd;
use crate::sys_common::{AsInner, IntoInner};

#[cfg(unix)]
pub use core::os::unix::io::{AsRawFd, FromRawFd, IntoRawFd, RawFd};
#[cfg(target_os = "wasi")]
pub use core::os::wasi::io::{AsRawFd, FromRawFd, IntoRawFd, RawFd};

#[stable(feature = "rust1", since = "1.0.0")]
impl AsRawFd for fs::File {
    #[inline]
    fn as_raw_fd(&self) -> RawFd {
        self.as_inner().as_raw_fd()
    }
}
#[stable(feature = "from_raw_os", since = "1.1.0")]
impl FromRawFd for fs::File {
    #[inline]
    unsafe fn from_raw_fd(fd: RawFd) -> fs::File {
        unsafe { fs::File::from(OwnedFd::from_raw_fd(fd)) }
    }
}
#[stable(feature = "into_raw_os", since = "1.4.0")]
impl IntoRawFd for fs::File {
    #[inline]
    fn into_raw_fd(self) -> RawFd {
        self.into_inner().into_inner().into_raw_fd()
    }
}

#[stable(feature = "asraw_stdio", since = "1.21.0")]
impl AsRawFd for io::Stdin {
    #[inline]
    fn as_raw_fd(&self) -> RawFd {
        libc::STDIN_FILENO
    }
}

#[stable(feature = "asraw_stdio", since = "1.21.0")]
impl AsRawFd for io::Stdout {
    #[inline]
    fn as_raw_fd(&self) -> RawFd {
        libc::STDOUT_FILENO
    }
}

#[stable(feature = "asraw_stdio", since = "1.21.0")]
impl AsRawFd for io::Stderr {
    #[inline]
    fn as_raw_fd(&self) -> RawFd {
        libc::STDERR_FILENO
    }
}

#[stable(feature = "asraw_stdio_locks", since = "1.35.0")]
impl<'a> AsRawFd for io::StdinLock<'a> {
    #[inline]
    fn as_raw_fd(&self) -> RawFd {
        libc::STDIN_FILENO
    }
}

#[stable(feature = "asraw_stdio_locks", since = "1.35.0")]
impl<'a> AsRawFd for io::StdoutLock<'a> {
    #[inline]
    fn as_raw_fd(&self) -> RawFd {
        libc::STDOUT_FILENO
    }
}

#[stable(feature = "asraw_stdio_locks", since = "1.35.0")]
impl<'a> AsRawFd for io::StderrLock<'a> {
    #[inline]
    fn as_raw_fd(&self) -> RawFd {
        libc::STDERR_FILENO
    }
}
