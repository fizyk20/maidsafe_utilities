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
