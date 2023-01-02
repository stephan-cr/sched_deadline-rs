#![warn(rust_2018_idioms)]

use libc::{
    __errno_location, c_char, c_int, c_uint, pid_t, strerror_r, syscall, SYS_sched_getattr,
    SYS_sched_setattr,
};
use std::convert::TryInto;
use std::error::Error;
use std::ffi::CStr;
use std::fmt;
use std::mem::size_of;
use std::ptr::{addr_of, addr_of_mut};
use std::result::Result;
use std::time::Duration;

use flagset::{flags, FlagSet};

#[repr(C)]
#[derive(Default)]
pub(crate) struct sched_attr {
    size: u32,
    sched_policy: u32,
    sched_flags: u64,
    // SCHED_NORMAL, SCHED_BATCH
    sched_nice: i32,
    // SCHED_FIFO, SCHED_RR
    sched_priority: u32,
    // SCHED_DEADLINE
    sched_runtime_ns: u64,
    sched_deadline_ns: u64,
    sched_period_ns: u64,
}

/// Flags for sched_{set,get}attr() calls, taken from linux/sched.h
///
/// It is introduced in Linux 3.14
pub const SCHED_DEADLINE: c_int = 6;

pub const SCHED_FLAG_RESET_ON_FORK: c_int = 0x01;
/// since Linux 4.13
pub const SCHED_FLAG_RECLAIM: c_int = 0x02;
/// since Linux 4.16
pub const SCHED_FLAG_DL_OVERRUN: c_int = 0x04;

/// # Safety
///
/// `sched_getattr` checks its pointer argument for null before it
/// dereferences the pointer. If the pointer is null it returns
/// `libc::EINVAL`.
#[cfg(target_pointer_width = "32")]
pub(crate) unsafe fn sched_getattr(
    pid: pid_t,
    attr: *mut sched_attr,
    size: c_uint,
    flags: c_uint,
) -> c_int {
    syscall(SYS_sched_getattr, pid, attr, size, flags)
}

#[cfg(target_pointer_width = "64")]
pub(crate) unsafe fn sched_getattr(
    pid: pid_t,
    attr: *mut sched_attr,
    size: c_uint,
    flags: c_uint,
) -> c_int {
    syscall(SYS_sched_getattr, pid, attr, size, flags)
        .try_into()
        .unwrap()
}

/// In order to be successful, the process needs the CAP_SYS_NICE
/// capability or needs to be started as root.
///
/// # Safety
///
/// `sched_setattr` checks its pointer argument for null before it
/// dereferences the pointer. If the pointer is null it returns
/// `libc::EINVAL`.
#[cfg(target_pointer_width = "32")]
pub(crate) unsafe fn sched_setattr(pid: pid_t, attr: *const sched_attr, flags: c_uint) -> c_int {
    syscall(SYS_sched_setattr, pid, attr, flags)
}

#[cfg(target_pointer_width = "64")]
pub(crate) unsafe fn sched_setattr(pid: pid_t, attr: *const sched_attr, flags: c_uint) -> c_int {
    syscall(SYS_sched_setattr, pid, attr, flags)
        .try_into()
        .unwrap()
}

#[derive(Debug, Eq, PartialEq)]
pub enum SchedDeadlineError {
    Syscall(c_int),
    Logic,
}

impl fmt::Display for SchedDeadlineError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SchedDeadlineError::Logic => write!(f, "logical error"),
            SchedDeadlineError::Syscall(error_num) => {
                let mut buf = [0 as c_char; 128];
                // # Safety
                //
                // If `libc::strerror_r` returns 0, it is guaranteed
                // that it filled the buffer with a zero terminated
                // string. In case `libc::strerror_r` return non-zero,
                // we panic.
                if unsafe { strerror_r(*error_num, buf.as_mut_ptr(), buf.len()) } != 0 {
                    panic!("libc::strerror_r failed");
                }
                write!(
                    f,
                    "{}",
                    unsafe { CStr::from_ptr(buf.as_ptr()) }.to_string_lossy()
                )
            }
        }
    }
}

impl Error for SchedDeadlineError {}

flags! {
    pub enum SchedFlag: u8 {
        ResetOnFork = 0x1,
        Reclaim = 0x2,
        DlOverrun = 0x4,
    }
}

#[derive(Clone, Copy)]
pub enum Target {
    /// Apply deadline scheduling to calling thread
    CallingThread,
    /// Apply deadline scheduling to the thread or process identified
    /// by its PID
    PID(pid_t),
}

pub fn is_sched_deadline_enabled(target: Target) -> Result<bool, SchedDeadlineError> {
    let pid: pid_t = match target {
        Target::CallingThread => 0,
        Target::PID(pid) => pid,
    };

    let mut attr = sched_attr::default();

    match unsafe {
        sched_getattr(
            pid,
            addr_of_mut!(attr),
            size_of::<sched_attr>().try_into().unwrap(),
            0,
        )
    } {
        0 => Ok(attr.sched_policy == SCHED_DEADLINE.try_into().unwrap()),
        -1 => Err(SchedDeadlineError::Syscall(unsafe { *__errno_location() })),
        _ => unreachable!("sched_getattr cannot return anything other than 0 or -1"),
    }
}

pub fn configure_sched_deadline(
    target: Target,
    sched_flags: impl Into<FlagSet<SchedFlag>>,
    runtime: Duration,
    deadline: Duration,
    period: Duration,
) -> Result<(), SchedDeadlineError> {
    let pid: pid_t = match target {
        Target::CallingThread => 0,
        Target::PID(pid) => pid,
    };

    // TODO return proper return code
    if runtime > deadline || deadline > period {
        return Err(SchedDeadlineError::Logic);
    }

    let sched_flags: c_int = sched_flags.into().bits() as c_int;

    let attr: sched_attr = sched_attr {
        size: size_of::<sched_attr>().try_into().unwrap(),
        sched_policy: SCHED_DEADLINE.try_into().unwrap(),
        sched_flags: sched_flags as u64,
        sched_nice: 0,                                 // unused
        sched_priority: 0,                             // unused
        sched_deadline_ns: deadline.as_nanos() as u64, // in nanoseconds
        sched_runtime_ns: runtime.as_nanos() as u64,   // in nanoseconds
        sched_period_ns: period.as_nanos() as u64,     // in nanoseconds
    };

    match unsafe { sched_setattr(pid, addr_of!(attr), 0) } {
        0 => Ok(()),
        -1 => Err(SchedDeadlineError::Syscall(unsafe { *__errno_location() })),
        _ => unreachable!("sched_setattr cannot return anything other than 0 or -1"),
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryInto;
    use std::mem::size_of;
    use std::time::Duration;

    use caps::{CapSet, Capability};
    use libc::{
        __errno_location, getpid, getuid, sched_yield, syscall, SYS_gettid, EPERM, SCHED_OTHER,
    };

    #[test]
    fn test_get_setattr() {
        let mut attr = super::sched_attr::default();

        let ret = unsafe {
            super::sched_getattr(
                0,
                &mut attr as *mut _,
                size_of::<super::sched_attr>().try_into().unwrap(),
                0,
            )
        };

        assert_eq!(ret, 0);
        assert_eq!(attr.sched_policy, SCHED_OTHER as u32);

        let ret = unsafe {
            super::sched_getattr(
                syscall(SYS_gettid).try_into().unwrap(),
                &mut attr as *mut _,
                size_of::<super::sched_attr>().try_into().unwrap(),
                0,
            )
        };

        assert_eq!(ret, 0);
        assert_eq!(attr.sched_policy, SCHED_OTHER as u32);
    }

    #[test]
    fn test_sched_setattr() {
        let attr: super::sched_attr = super::sched_attr {
            size: size_of::<super::sched_attr>().try_into().unwrap(),
            sched_policy: super::SCHED_DEADLINE.try_into().unwrap(),
            sched_flags: super::SCHED_FLAG_RESET_ON_FORK as u64,
            sched_nice: 0,                     // unused
            sched_priority: 0,                 // unused
            sched_deadline_ns: 1000 * 1000,    // in nanoseconds
            sched_runtime_ns: 1000 * 1000,     // in nanoseconds
            sched_period_ns: 10 * 1000 * 1000, // in nanoseconds
        };

        let has_cap_sys_nice = caps::has_cap(None, CapSet::Permitted, Capability::CAP_SYS_NICE)
            .expect("has_cap must not fail");

        let ret = {
            let _guard = if has_cap_sys_nice {
                caps::raise(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap();
                assert!(caps::has_cap(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap());
                Some(scopeguard::guard((), |_| {
                    caps::drop(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap();
                }))
            } else {
                None
            };

            unsafe { super::sched_setattr(0, &attr as *const _, 0) }
        };

        // check if we have CAP_SYS_NICE capability or root access.
        if has_cap_sys_nice || unsafe { getuid() } == 0 {
            assert_eq!(ret, 0);
        } else {
            assert_eq!(ret, -1);
            // This is expected to fail if we don't have permission.
            assert_eq!(EPERM, unsafe { *__errno_location() });
        }

        unsafe {
            sched_yield();
        };
    }

    #[test]
    fn test_configure_sched_deadline() {
        let has_cap_sys_nice = caps::has_cap(None, CapSet::Permitted, Capability::CAP_SYS_NICE)
            .expect("has_cap must not fail");
        let has_permission = has_cap_sys_nice || unsafe { getuid() } == 0;

        let ret = {
            let _guard = if has_cap_sys_nice {
                caps::raise(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap();
                assert!(caps::has_cap(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap());
                Some(scopeguard::guard((), |_| {
                    caps::drop(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap();
                }))
            } else {
                None
            };

            super::configure_sched_deadline(
                super::Target::CallingThread,
                super::SchedFlag::ResetOnFork,
                Duration::from_nanos(1000 * 1000),
                Duration::from_nanos(1000 * 1000),
                Duration::from_nanos(10 * 1000 * 1000),
            )
        };

        if has_permission {
            assert_eq!(ret, Ok(()));
        } else {
            assert_eq!(ret, Err(super::SchedDeadlineError::Syscall(libc::EPERM)));
            if let Err(error) = ret {
                format!("{}", error);
            }
        }

        let ret = {
            let _guard = if has_cap_sys_nice {
                caps::raise(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap();
                assert!(caps::has_cap(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap());
                Some(scopeguard::guard((), |_| {
                    caps::drop(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap();
                }))
            } else {
                None
            };

            super::configure_sched_deadline(
                super::Target::PID(unsafe { getpid() }),
                super::SchedFlag::ResetOnFork | super::SchedFlag::Reclaim,
                Duration::from_nanos(1000 * 1000),
                Duration::from_nanos(1000 * 1000),
                Duration::from_nanos(10 * 1000 * 1000),
            )
        };

        if has_permission {
            assert_eq!(ret, Ok(()));
        } else {
            assert_eq!(ret, Err(super::SchedDeadlineError::Syscall(libc::EPERM)));
        }

        let ret = {
            let _guard = if has_cap_sys_nice {
                caps::raise(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap();
                assert!(caps::has_cap(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap());
                Some(scopeguard::guard((), |_| {
                    caps::drop(None, CapSet::Effective, Capability::CAP_SYS_NICE).unwrap();
                }))
            } else {
                None
            };

            super::configure_sched_deadline(
                super::Target::PID(unsafe { syscall(SYS_gettid) }.try_into().unwrap()),
                super::SchedFlag::ResetOnFork | super::SchedFlag::Reclaim,
                Duration::from_nanos(1000 * 1000),
                Duration::from_nanos(1000 * 1000),
                Duration::from_nanos(10 * 1000 * 1000),
            )
        };

        if has_permission {
            assert_eq!(ret, Ok(()));
        } else {
            assert_eq!(ret, Err(super::SchedDeadlineError::Syscall(libc::EPERM)));
        }
    }

    #[test]
    fn test_is_sched_deadline_enabled() {
        let ret = super::is_sched_deadline_enabled(super::Target::CallingThread);

        assert_eq!(ret, Ok(false));
    }
}
