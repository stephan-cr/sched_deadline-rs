use libc::{__errno_location, c_int, c_uint, pid_t, syscall, SYS_sched_setattr};
use std::convert::TryInto;
use std::mem::size_of;
use std::result::Result;

#[repr(C)]
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
pub const SCHED_DEADLINE: c_int = 6;
pub const SCHED_FLAG_RESET_ON_FORK: c_int = 0x01;
pub const SCHED_FLAG_RECLAIM: c_int = 0x02;
pub const SCHED_FLAG_DL_OVERRUN: c_int = 0x04;

/// In order to be successful, the process needs the CAP_SYS_NICE
/// capability or needs to be started as root.
///
/// # Safety
///
/// `sched_setattr` checks its pointer argument for null before it
/// dereferences the pointer , in this case it returns libc::EINVAL.
pub(crate) unsafe fn sched_setattr(pid: pid_t, attr: *const sched_attr, flags: c_uint) -> c_int {
    syscall(SYS_sched_setattr, pid, attr, flags)
}

pub enum SchedFlag {
    None = 0,
    ResetOnFork,
    Reclaim,
    DlOverrun,
}

pub enum Target {
    /// Apply deadline scheduling to calling thread
    CallingThread,
    /// Apply deadline scheduling to the thread or process identified
    /// by its PID
    PID(pid_t),
}

// TODO use std::time::Duration for runtime_ns, deadline_ns and period_ns
pub fn configure_sched_deadline(
    target: Target,
    sched_flags: SchedFlag,
    runtime_ns: u64,
    deadline_ns: u64,
    period_ns: u64,
) -> Result<(), c_int> {
    let pid: pid_t = match target {
        Target::CallingThread => 0,
        Target::PID(pid) => pid,
    };

    let sched_flags: c_int = match sched_flags {
        SchedFlag::None => 0,
        SchedFlag::ResetOnFork => SCHED_FLAG_RESET_ON_FORK,
        SchedFlag::Reclaim => SCHED_FLAG_RECLAIM,
        SchedFlag::DlOverrun => SCHED_FLAG_DL_OVERRUN,
    };

    let attr: sched_attr = sched_attr {
        size: size_of::<sched_attr>().try_into().unwrap(),
        sched_policy: SCHED_DEADLINE.try_into().unwrap(),
        sched_flags: sched_flags as u64,
        sched_nice: 0,                  // unused
        sched_priority: 0,              // unused
        sched_deadline_ns: deadline_ns, // in nanoseconds
        sched_runtime_ns: runtime_ns,   // in nanoseconds
        sched_period_ns: period_ns,     // in nanoseconds
    };

    match unsafe { sched_setattr(pid, &attr as *const sched_attr, 0) } {
        0 => Ok(()),
        -1 => Err(unsafe { *__errno_location() }),
        _ => unreachable!("sched_setattr cannot return anything other than 0 or -1"),
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryInto;
    use std::ffi::CString;
    use std::mem::size_of;

    use libc::{__errno_location, perror, sched_yield, EPERM};

    #[test]
    fn it_works() {
        let mut attr: super::sched_attr = super::sched_attr {
            size: size_of::<super::sched_attr>().try_into().unwrap(),
            sched_policy: super::SCHED_DEADLINE.try_into().unwrap(),
            sched_flags: super::SCHED_FLAG_RESET_ON_FORK as u64,
            sched_nice: 0,                     // unused
            sched_priority: 0,                 // unused
            sched_deadline_ns: 1000 * 1000,    // in nanoseconds
            sched_runtime_ns: 1000 * 1000,     // in nanoseconds
            sched_period_ns: 10 * 1000 * 1000, // in nanoseconds
        };

        let ret = unsafe { super::sched_setattr(0, &mut attr as *const super::sched_attr, 0) };
        assert_eq!(ret, -1);
        // TODO check if we have CAP_SYS_NICE capability or root
        // access. In this case the following assertion fails.
        assert_eq!(EPERM, unsafe { *__errno_location() });

        unsafe {
            perror(CString::new("sched_setattr").unwrap().into_raw());
            sched_yield();
            perror(CString::new("sched_yield").unwrap().into_raw());
        };
    }
}
