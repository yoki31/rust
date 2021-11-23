//! Owned and borrowed Unix-like file descriptors.

#![unstable(feature = "io_safety", issue = "87074")]
#![deny(unsafe_op_in_unsafe_fn)]

use super::raw::{AsRawFd, FromRawFd, IntoRawFd, RawFd};
use crate::fmt;
use crate::fs;
use crate::sys_common::{AsInner, FromInner, IntoInner};

#[cfg(unix)]
pub use core::os::unix::io::{AsFd, BorrowedFd};
#[cfg(target_os = "wasi")]
pub use core::os::wasi::io::{AsFd, BorrowedFd};

use rustix::io::OwnedFd as RustixOwnedFd;

/// An owned file descriptor.
///
/// This closes the file descriptor on drop.
///
/// This uses `repr(transparent)` and has the representation of a host file
/// descriptor, so it can be used in FFI in places where a file descriptor is
/// passed as a consumed argument or returned as an owned value, and it never
/// has the value `-1`.
#[repr(transparent)]
#[unstable(feature = "io_safety", issue = "87074")]
pub struct OwnedFd {
    fd: RustixOwnedFd,
}

#[unstable(feature = "io_safety", issue = "87074")]
impl AsRawFd for OwnedFd {
    #[inline]
    fn as_raw_fd(&self) -> RawFd {
        self.fd.as_raw_fd()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl IntoRawFd for OwnedFd {
    #[inline]
    fn into_raw_fd(self) -> RawFd {
        self.fd.into_raw_fd()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl FromRawFd for OwnedFd {
    /// Constructs a new instance of `Self` from the given raw file descriptor.
    ///
    /// # Safety
    ///
    /// The resource pointed to by `fd` must be open and suitable for assuming
    /// ownership. The resource must not require any cleanup other than `close`.
    #[inline]
    unsafe fn from_raw_fd(fd: RawFd) -> Self {
        unsafe { Self { fd: rustix::io::OwnedFd::from_raw_fd(fd) } }
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl fmt::Debug for OwnedFd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OwnedFd").field("fd", &self.as_raw_fd()).finish()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl AsFd for OwnedFd {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        self.fd.as_fd()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl FromInner<RustixOwnedFd> for OwnedFd {
    #[inline]
    fn from_inner(fd: RustixOwnedFd) -> Self {
        Self { fd }
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl IntoInner<RustixOwnedFd> for OwnedFd {
    #[inline]
    fn into_inner(self) -> RustixOwnedFd {
        self.fd
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl AsFd for fs::File {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        self.as_inner().as_fd()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl From<fs::File> for OwnedFd {
    #[inline]
    fn from(file: fs::File) -> OwnedFd {
        file.into_inner().into_inner().into_inner()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl From<OwnedFd> for fs::File {
    #[inline]
    fn from(owned_fd: OwnedFd) -> Self {
        Self::from_inner(FromInner::from_inner(FromInner::from_inner(owned_fd)))
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl AsFd for crate::net::TcpStream {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        self.as_inner().socket().as_fd()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl From<crate::net::TcpStream> for OwnedFd {
    #[inline]
    fn from(tcp_stream: crate::net::TcpStream) -> OwnedFd {
        tcp_stream.into_inner().into_socket().into_inner().into_inner().into()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl From<OwnedFd> for crate::net::TcpStream {
    #[inline]
    fn from(owned_fd: OwnedFd) -> Self {
        Self::from_inner(FromInner::from_inner(FromInner::from_inner(FromInner::from_inner(
            owned_fd,
        ))))
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl AsFd for crate::net::TcpListener {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        self.as_inner().socket().as_fd()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl From<crate::net::TcpListener> for OwnedFd {
    #[inline]
    fn from(tcp_listener: crate::net::TcpListener) -> OwnedFd {
        tcp_listener.into_inner().into_socket().into_inner().into_inner().into()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl From<OwnedFd> for crate::net::TcpListener {
    #[inline]
    fn from(owned_fd: OwnedFd) -> Self {
        Self::from_inner(FromInner::from_inner(FromInner::from_inner(FromInner::from_inner(
            owned_fd,
        ))))
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl AsFd for crate::net::UdpSocket {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        self.as_inner().socket().as_fd()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl From<crate::net::UdpSocket> for OwnedFd {
    #[inline]
    fn from(udp_socket: crate::net::UdpSocket) -> OwnedFd {
        udp_socket.into_inner().into_socket().into_inner().into_inner().into()
    }
}

#[unstable(feature = "io_safety", issue = "87074")]
impl From<OwnedFd> for crate::net::UdpSocket {
    #[inline]
    fn from(owned_fd: OwnedFd) -> Self {
        Self::from_inner(FromInner::from_inner(FromInner::from_inner(FromInner::from_inner(
            owned_fd,
        ))))
    }
}
