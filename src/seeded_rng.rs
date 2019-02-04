// Copyright 2018 MaidSafe.net limited.
//
// This SAFE Network Software is licensed to you under the MIT license <LICENSE-MIT
// https://opensource.org/licenses/MIT> or the Modified BSD license <LICENSE-BSD
// https://opensource.org/licenses/BSD-3-Clause>, at your option. This file may not be copied,
// modified, or distributed except according to those terms. Please review the Licences for the
// specific language governing permissions and limitations relating to use of the SAFE Network
// Software.

use rand::{self, Error, Rng, RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;
use std::cell::RefCell;
use std::fmt::{self, Debug, Display, Formatter};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;
use std::thread;

lazy_static! {
    static ref SEED: Mutex<Option<[u32; 4]>> = Mutex::new(None);
    static ref ALREADY_PRINTED: AtomicBool = AtomicBool::new(false);
}

thread_local! {
    static THREAD_RNG: RefCell<Option<SeededRng>> = RefCell::new(None);
}

/// A [fast pseudorandom number
/// generator](https://doc.rust-lang.org/rand/rand/struct.XorShiftRng.html)
/// for use in tests which allows seeding and prints the seed when the thread
/// in which it is created panics.
pub struct SeededRng(XorShiftRng);

/// Compatibility function: converts the old-style seed (`[u32; 4]`) to a new-style one (`[u8; 16]`)
pub fn convert_seed(arr: [u32; 4]) -> [u8; 16] {
    [
        (arr[0] & 0xFF) as u8,
        ((arr[0] >> 8) & 0xFF) as u8,
        ((arr[0] >> 16) & 0xFF) as u8,
        ((arr[0] >> 24) & 0xFF) as u8,
        (arr[1] & 0xFF) as u8,
        ((arr[1] >> 8) & 0xFF) as u8,
        ((arr[1] >> 16) & 0xFF) as u8,
        ((arr[1] >> 24) & 0xFF) as u8,
        (arr[2] & 0xFF) as u8,
        ((arr[2] >> 8) & 0xFF) as u8,
        ((arr[2] >> 16) & 0xFF) as u8,
        ((arr[2] >> 24) & 0xFF) as u8,
        (arr[3] & 0xFF) as u8,
        ((arr[3] >> 8) & 0xFF) as u8,
        ((arr[3] >> 16) & 0xFF) as u8,
        ((arr[3] >> 24) & 0xFF) as u8,
    ]
}

impl SeededRng {
    /// Construct a new `SeededRng` using a seed generated from cryptographically secure random
    /// data.
    ///
    /// The seed is only set once for the whole process, so every call to this will yield internal
    /// RNGs which are all seeded identically.
    pub fn new() -> Self {
        let optional_seed = &mut *unwrap!(SEED.lock());
        let seed = if let Some(current_seed) = *optional_seed {
            current_seed
        } else {
            let new_seed = [
                rand::random(),
                rand::random(),
                rand::random(),
                rand::random(),
            ];
            *optional_seed = Some(new_seed);
            new_seed
        };
        SeededRng(XorShiftRng::from_seed(convert_seed(seed)))
    }

    /// Construct a new `SeededRng` using `seed`.
    ///
    /// If the underlying static seed has already been initialised to a value different to `seed`,
    /// then this function will panic.
    pub fn from_seed(seed: [u32; 4]) -> Self {
        let optional_seed = &mut *unwrap!(SEED.lock());
        if let Some(current_seed) = *optional_seed {
            if current_seed != seed {
                panic!(
                    "\nThe static seed has already been initialised to a different value via \
                     a call to `SeededRng::new()`\nor `SeededRng::from_seed(...)`.  This \
                     could be due to setting a hard-coded value for the seed in a\nsingle \
                     test case, but running the whole test suite.  If so, try running just \
                     the single test case.\n"
                );
            }
        } else {
            *optional_seed = Some(seed);
        }

        SeededRng(XorShiftRng::from_seed(convert_seed(seed)))
    }

    /// Constructs a thread-local `SeededRng`. The seed is generated via a global `SeededRng` using
    /// the global seed.
    pub fn thread_rng() -> SeededRng {
        THREAD_RNG.with(|optional_rng_cell| {
            let mut optional_rng = optional_rng_cell.borrow_mut();
            let mut rng = optional_rng.take().unwrap_or_else(SeededRng::new);
            let new_rng = rng.new_rng();
            *optional_rng = Some(rng);
            new_rng
        })
    }

    /// Construct a new `SeededRng`
    /// using a seed generated from random data provided by `self`.
    pub fn new_rng(&mut self) -> SeededRng {
        let new_seed = [
            self.0.next_u32().wrapping_add(self.0.next_u32()),
            self.0.next_u32().wrapping_add(self.0.next_u32()),
            self.0.next_u32().wrapping_add(self.0.next_u32()),
            self.0.next_u32().wrapping_add(self.0.next_u32()),
        ];
        SeededRng(XorShiftRng::from_seed(convert_seed(new_seed)))
    }
}

impl Default for SeededRng {
    fn default() -> Self {
        SeededRng::new()
    }
}

impl Display for SeededRng {
    fn fmt(&self, formatter: &mut Formatter) -> fmt::Result {
        write!(
            formatter,
            "RNG seed: {:?}",
            *SEED.lock().unwrap_or_else(|e| e.into_inner())
        )
    }
}

impl Debug for SeededRng {
    fn fmt(&self, formatter: &mut Formatter) -> fmt::Result {
        <Self as Display>::fmt(self, formatter)
    }
}

impl Drop for SeededRng {
    fn drop(&mut self) {
        if thread::panicking() && !ALREADY_PRINTED.compare_and_swap(false, true, Ordering::SeqCst) {
            let msg = format!("{:?}", *SEED.lock().unwrap_or_else(|e| e.into_inner()));
            let border = (0..msg.len()).map(|_| "=").collect::<String>();
            println!("\n{}\n{}\n{}\n", border, msg, border);
        }
    }
}

// TODO: make sure that the values being returned are consistent across CPU architectures (32/64
// bit, big/little-endian)
impl RngCore for SeededRng {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u64() as u32
    }

    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.0.try_fill_bytes(dest)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;
    use std::sync::atomic::Ordering;

    // We need the expected message here to ensure that any assertion failure in the test causes the
    // test to fail.  Only the final statement should cause a panic (calling `from_seed()` with a
    // different seed value).  This check can't be moved to its own test case since if it runs
    // first it will poison the mutex protecting the static seed, causing this test to fail.
    #[test]
    #[should_panic(
        expected = "\nThe static seed has already been initialised to a different value via a call \
                    to `SeededRng::new()`\nor `SeededRng::from_seed(...)`.  This could be due to \
                    setting a hard-coded value for the seed in a\nsingle test case, but running \
                    the whole test suite.  If so, try running just the single test case.\n"
    )]
    fn seeded_rng() {
        assert!(!ALREADY_PRINTED.load(Ordering::Relaxed));
        {
            let seed = [0, 1, 2, 3];
            let mut seeded_rng1 = SeededRng::from_seed(seed);
            assert!(!ALREADY_PRINTED.load(Ordering::Relaxed));
            let mut seeded_rng2 = SeededRng::new();
            let expected = 12_884_903_946;
            assert_eq!(seeded_rng1.next_u64(), expected);
            assert_eq!(seeded_rng2.next_u64(), expected);

            let mut rng1_from_seeded_rng1 = seeded_rng1.new_rng();
            let mut rng2_from_seeded_rng1 = seeded_rng1.new_rng();
            let expected1 = 36_629_641_468_946_701;
            let expected2 = 1_225_987_531_410_437_264;
            assert_eq!(rng1_from_seeded_rng1.next_u64(), expected1);
            assert_eq!(rng2_from_seeded_rng1.next_u64(), expected2);

            let mut rng1_from_seeded_rng2 = seeded_rng2.new_rng();
            let mut rng2_from_seeded_rng2 = seeded_rng2.new_rng();
            assert_eq!(rng1_from_seeded_rng2.next_u64(), expected1);
            assert_eq!(rng2_from_seeded_rng2.next_u64(), expected2);
        }

        for _ in 0..2 {
            let j = thread::spawn(move || {
                let _rng = SeededRng::new();
                panic!(
                    "This is an induced panic to test if `ALREADY_PRINTED` global is toggled only \
                     once on panic"
                );
            });

            assert!(j.join().is_err());
            assert!(ALREADY_PRINTED.load(Ordering::Relaxed));
        }

        let _ = SeededRng::from_seed([3, 2, 1, 0]);
    }
}
