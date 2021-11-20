#![unstable(reason = "not public", issue = "none", feature = "fd")]

#[cfg(test)]
mod tests;

use crate::io::{self, Initializer, IoSlice, IoSliceMut, Read};
use crate::os::unix::io::{AsFd, AsRawFd, BorrowedFd, FromRawFd, IntoRawFd, OwnedFd, RawFd};
use crate::sys_common::{AsInner, FromInner, IntoInner};

use rustix::fs::FdFlags;
#[cfg(not(target_os = "linux"))]
use rustix::fs::OFlags;

#[derive(Debug)]
pub struct FileDesc(OwnedFd);

impl FileDesc {
    pub fn read(&self, buf: &mut [u8]) -> io::Result<usize> {
        let ret = rustix::io::read(self, buf)?;
        Ok(ret)
    }

    #[cfg(not(target_os = "espidf"))]
    pub fn read_vectored(&self, bufs: &mut [IoSliceMut<'_>]) -> io::Result<usize> {
        let ret = rustix::io::readv(self, unsafe { crate::mem::transmute(bufs) })?;
        Ok(ret)
    }

    #[cfg(target_os = "espidf")]
    pub fn read_vectored(&self, bufs: &mut [IoSliceMut<'_>]) -> io::Result<usize> {
        return crate::io::default_read_vectored(|b| self.read(b), unsafe {
            crate::mem::transmute(bufs)
        });
    }

    #[inline]
    pub fn is_read_vectored(&self) -> bool {
        cfg!(not(target_os = "espidf"))
    }

    pub fn read_to_end(&self, buf: &mut Vec<u8>) -> io::Result<usize> {
        let mut me = self;
        (&mut me).read_to_end(buf)
    }

    pub fn read_at(&self, buf: &mut [u8], offset: u64) -> io::Result<usize> {
        let ret = rustix::io::pread(self, buf, offset)?;
        Ok(ret)
    }

    pub fn write(&self, buf: &[u8]) -> io::Result<usize> {
        let ret = rustix::io::write(self, buf)?;
        Ok(ret)
    }

    #[cfg(not(target_os = "espidf"))]
    pub fn write_vectored(&self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        let ret = rustix::io::writev(self, unsafe { crate::mem::transmute(bufs) })?;
        Ok(ret)
    }

    #[cfg(target_os = "espidf")]
    pub fn write_vectored(&self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        return crate::io::default_write_vectored(|b| self.write(b), unsafe {
            crate::mem::transmute(bufs)
        });
    }

    #[inline]
    pub fn is_write_vectored(&self) -> bool {
        cfg!(not(target_os = "espidf"))
    }

    pub fn write_at(&self, buf: &[u8], offset: u64) -> io::Result<usize> {
        let ret = rustix::io::pwrite(self, buf, offset)?;
        Ok(ret)
    }

    #[cfg(target_os = "linux")]
    pub fn get_cloexec(&self) -> io::Result<bool> {
        Ok(rustix::fs::fcntl_getfd(self)?.contains(FdFlags::CLOEXEC))
    }

    #[cfg(not(any(
        target_env = "newlib",
        target_os = "solaris",
        target_os = "illumos",
        target_os = "emscripten",
        target_os = "fuchsia",
        target_os = "l4re",
        target_os = "linux",
        target_os = "haiku",
        target_os = "redox",
        target_os = "vxworks"
    )))]
    pub fn set_cloexec(&self) -> io::Result<()> {
        rustix::io::ioctl_fioclex(self)?;
        Ok(())
    }
    #[cfg(any(
        all(target_env = "newlib", not(target_os = "espidf")),
        target_os = "solaris",
        target_os = "illumos",
        target_os = "emscripten",
        target_os = "fuchsia",
        target_os = "l4re",
        target_os = "linux",
        target_os = "haiku",
        target_os = "redox",
        target_os = "vxworks"
    ))]
    pub fn set_cloexec(&self) -> io::Result<()> {
        let previous = rustix::fs::fcntl_getfd(self)?;
        let new = previous | FdFlags::CLOEXEC;
        if new != previous {
            rustix::fs::fcntl_setfd(self, new)?;
        }
        Ok(())
    }
    #[cfg(target_os = "espidf")]
    pub fn set_cloexec(&self) -> io::Result<()> {
        // FD_CLOEXEC is not supported in ESP-IDF but there's no need to,
        // because ESP-IDF does not support spawning processes either.
        Ok(())
    }

    #[cfg(target_os = "linux")]
    pub fn set_nonblocking(&self, nonblocking: bool) -> io::Result<()> {
        rustix::io::ioctl_fionbio(self, nonblocking)?;
        Ok(())
    }

    #[cfg(not(target_os = "linux"))]
    pub fn set_nonblocking(&self, nonblocking: bool) -> io::Result<()> {
        unsafe {
            let previous = rustix::fs::fcntl_getfl(self)?;
            let new = if nonblocking {
                previous | OFlags::NONBLOCK;
            } else {
                previous & !OFlags::NONBLOCK;
            };
            if new != previous {
                rustix::fcntl_setfl(self, new)?;
            }
            Ok(())
        }
    }

    pub fn duplicate(&self) -> io::Result<FileDesc> {
        // We want to atomically duplicate this file descriptor and set the
        // CLOEXEC flag, and currently that's done via F_DUPFD_CLOEXEC. This
        // is a POSIX flag that was added to Linux in 2.6.24.
        #[cfg(not(target_os = "espidf"))]
        let fd = rustix::fs::fcntl_dupfd_cloexec(self, 0)?;

        // For ESP-IDF, F_DUPFD is used instead, because the CLOEXEC semantics
        // will never be supported, as this is a bare metal framework with
        // no capabilities for multi-process execution.  While F_DUPFD is also
        // not supported yet, it might be (currently it returns ENOSYS).
        #[cfg(target_os = "espidf")]
        let fd = rustix::fs::fcntl_dupfd(self, 0)?;

        Ok(FileDesc::from_inner(fd))
    }
}

impl<'a> Read for &'a FileDesc {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        (**self).read(buf)
    }

    #[inline]
    unsafe fn initializer(&self) -> Initializer {
        Initializer::nop()
    }
}

impl AsInner<OwnedFd> for FileDesc {
    fn as_inner(&self) -> &OwnedFd {
        &self.0
    }
}

impl IntoInner<OwnedFd> for FileDesc {
    fn into_inner(self) -> OwnedFd {
        self.0
    }
}

impl FromInner<rustix::io::OwnedFd> for FileDesc {
    fn from_inner(owned_fd: rustix::io::OwnedFd) -> Self {
        Self(OwnedFd::from_inner(owned_fd))
    }
}

impl FromInner<OwnedFd> for FileDesc {
    fn from_inner(owned_fd: OwnedFd) -> Self {
        Self(owned_fd)
    }
}

impl AsFd for FileDesc {
    fn as_fd(&self) -> BorrowedFd<'_> {
        self.0.as_fd()
    }
}

impl AsRawFd for FileDesc {
    fn as_raw_fd(&self) -> RawFd {
        self.0.as_raw_fd()
    }
}

impl IntoRawFd for FileDesc {
    fn into_raw_fd(self) -> RawFd {
        self.0.into_raw_fd()
    }
}

impl FromRawFd for FileDesc {
    unsafe fn from_raw_fd(raw_fd: RawFd) -> Self {
        Self(FromRawFd::from_raw_fd(raw_fd))
    }
}
