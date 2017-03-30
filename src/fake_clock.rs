use std::cell::{RefCell, RefMut};
use std::rc::Rc;
use std::time::{Duration, Instant};

/// Trait representing an object tracking the flow of time
pub trait Clock {
    /// Returns an instance representing the current moment in time
    fn now() -> Self;
    /// Returns the duration between `self` and `earlier`
    fn duration_since(&self, earlier: &Self) -> Duration;
    /// Returns the amount of time elapsed since creation of `self`
    fn elapsed(&self) -> Duration;
}

impl Clock for Instant {
    fn now() -> Self {
        Self::now()
    }

    fn duration_since(&self, earlier: &Self) -> Duration {
        self.duration_since(*earlier)
    }

    fn elapsed(&self) -> Duration {
        self.elapsed()
    }
}

/// Struct representing a fake instant
pub struct FakeClock {
    time: Rc<RefCell<u64>>,
    time_created: u64,
}

impl FakeClock {
    /// Returns `Rc<RefCell<u64>>` representing the thread-local fake time
    pub fn rc_time() -> Rc<RefCell<u64>> {
        thread_local!{
            static LOCAL_TIME: Rc<RefCell<u64>> = Rc::new(RefCell::new(0));
        }
        LOCAL_TIME.with(|t| t.clone())
    }

    /// Sets the thread-local fake time to the given value
    pub fn set_time(time: u64) {
        let rc_time = Self::rc_time();
        *rc_time.borrow_mut() = time;
    }

    /// Advances the thread-local fake time by the given amount of milliseconds
    pub fn advance_time(millis: u64) {
        let rc_time = Self::rc_time();
        *rc_time.borrow_mut() += millis;
    }

    /// Returns the current thread-local fake time
    pub fn time(&self) -> u64 {
        *self.time.borrow()
    }

    /// Returns a mutable reference to the thread-local fake time
    pub fn time_mut(&self) -> RefMut<u64> {
        self.time.borrow_mut()
    }
}

impl Clock for FakeClock {
    fn now() -> Self {
        let rc_time = Self::rc_time();
        let time = *rc_time.borrow();
        FakeClock {
            time: rc_time,
            time_created: time,
        }
    }

    fn duration_since(&self, earlier: &Self) -> Duration {
        Duration::from_millis(self.time_created - earlier.time_created)
    }

    fn elapsed(&self) -> Duration {
        Duration::from_millis(self.time() - self.time_created)
    }
}
