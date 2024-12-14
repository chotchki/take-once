//! A thread-safe container for one-time storage and one-time consumption of a value.
//!
//! This module provides the [`TakeOnce`] type, which enables safe storage
//! and consumption of a value in concurrent contexts. It ensures that:
//!
//! * A value can be stored exactly once
//! * A stored value can be taken out exactly once
//! * All operations are thread-safe
//!
//! This is similar to [`std::sync::OnceLock`], but with different semantics regarding
//! value consumption. `TakeOnce` allows the stored value to be taken out (moved) exactly once,
//! whereas `OnceLock` allows the value to be accessed in place multiple times.
//!
//! # Example
//!
#![cfg_attr(feature = "_shuttle", doc = "```ignore")]
#![cfg_attr(not(feature = "_shuttle"), doc = "```rust")]
//! use take_once::TakeOnce;
//!
//! let cell = TakeOnce::new();
//!
//! // Store a value
//! assert_eq!(cell.store(42), Ok(()));
//!
//! // Subsequent stores do not consume the value.
//! assert_eq!(cell.store(24), Err(24));
//!
//! // Take the stored value
//! assert_eq!(cell.take(), Some(42));
//!
//! // Value can only be taken once
//! assert_eq!(cell.take(), None);
//! ```
//!
//! # Thread Safety
//!
//! `TakeOnce<T>` is both [`Send`] and [`Sync`] when `T: Send`, making it suitable for
//! sharing across thread boundaries. All operations are atomic and properly synchronized.
//!
#![cfg_attr(feature = "_shuttle", doc = "```ignore")]
#![cfg_attr(not(feature = "_shuttle"), doc = "```rust")]
//! # use std::sync::Arc;
//! # use std::thread;
//! # use take_once::TakeOnce;
//! let shared = Arc::new(TakeOnce::new());
//! let shared2 = shared.clone();
//!
//! // Store in one thread
//! thread::spawn(move || {
//!     shared.store(42).unwrap();
//! }).join().unwrap();
//!
//! // Take in another thread
//! thread::spawn(move || {
//!     if let Some(value) = shared2.take() {
//!         println!("Got value: {}", value);
//!     }
//! });

use std::marker::PhantomData;

#[cfg(feature = "_shuttle")]
pub(crate) use shuttle::sync::{
    atomic::{AtomicPtr, Ordering},
    Once,
};

#[cfg(not(feature = "_shuttle"))]
pub(crate) use std::sync::{
    atomic::{AtomicPtr, Ordering},
    Once,
};

/// A thread-safe container that allows storing a value once and taking it exactly once.
/// This is useful in scenarios where:
///
/// * A value needs to be initialized lazily but only once
/// * The initialized value should be consumable (moved out) rather than just accessible.
///   See [`std::sync::OnceLock`] for a similar use case where the value can be accessed in place.
/// * Multiple threads might attempt to initialize or consume the value, but only one should succeed
///
/// # Thread Safety
///
/// `TakeOnce<T>` implements `Send` and `Sync` when `T: Send`, making it safe to share
/// across thread boundaries. All operations are atomic and properly synchronized.
///
/// # Memory Management
///
/// The stored value is heap-allocated and properly cleaned up when the `TakeOnce` is dropped.
///
/// # Examples
///
/// Basic usage:
#[cfg_attr(feature = "_shuttle", doc = "```ignore")]
#[cfg_attr(not(feature = "_shuttle"), doc = "```rust")]
/// use take_once::TakeOnce;
///
/// let cell = TakeOnce::new();
///
/// // Initial store succeeds
/// assert_eq!(cell.store(42), None);
///
/// // Subsequent stores return the provided value
/// assert_eq!(cell.store(24), Some(24));
///
/// // Take the value
/// assert_eq!(cell.take(), Some(42));
///
/// // Can't take twice
/// assert_eq!(cell.take(), None);
/// ```
///
/// Concurrent usage:
#[cfg_attr(feature = "_shuttle", doc = "```ignore")]
#[cfg_attr(not(feature = "_shuttle"), doc = "```rust")]
/// use std::sync::Arc;
/// use std::thread;
/// use take_once::TakeOnce;
///
/// let shared = Arc::new(TakeOnce::new());
/// let threads: Vec<_> = (0..3)
///     .map(|i| {
///         let shared = shared.clone();
///         thread::spawn(move || {
///             // Only one thread will successfully store
///             shared.store(i)
///         })
///     })
///     .collect();
/// ```
#[derive(Debug)]
pub struct TakeOnce<T> {
    once: Once,
    // Whether or not the value is initialized is tracked by `once.is_completed()`.
    value: AtomicPtr<T>,
    _marker: PhantomData<T>,
}

impl<T> TakeOnce<T> {
    /// Creates a new empty cell.
    #[inline]
    #[must_use]
    pub const fn new() -> TakeOnce<T> {
        TakeOnce {
            once: Once::new(),
            value: AtomicPtr::new(std::ptr::null_mut()),
            _marker: PhantomData,
        }
    }

    /// Stores a value into this `TakeOnce` if it has not been initialized.
    ///
    /// If the `TakeOnce` has already been initialized, the value is returned as [`Err`].
    /// Otherwise, the value is stored and [`Ok`] is returned.
    ///
    /// This method allocates memory on the heap to store the value.
    #[inline]
    pub fn store(&self, val: T) -> Result<(), T> {
        let mut val = Some(val);
        self.once.call_once(|| {
            let val = val.take().unwrap();
            let ptr = Box::into_raw(Box::new(val));
            self.value.store(ptr, Ordering::Release);
        });

        val.map_or(Ok(()), Err)
    }

    /// Takes the value out of this `TakeOnce`, if it has been initialized.
    ///
    /// If the `TakeOnce` has not been initialized, or if the value has already been taken,
    /// this method returns `None`.
    #[inline]
    #[must_use]
    pub fn take(&self) -> Option<T> {
        if self.once.is_completed() {
            let ptr = self.value.swap(std::ptr::null_mut(), Ordering::Acquire);
            if ptr.is_null() {
                None
            } else {
                // SAFETY: `self.value` is initialized (since `self.once.is_completed()`)
                // and has not been taken before (since `ptr` is not null).
                Some(*unsafe { Box::from_raw(ptr) })
            }
        } else {
            None
        }
    }

    /// Returns true if the value has been initialized, regardless of whether it has been taken.
    /// In other words, this returns true if `store` has been called at least once.
    #[inline]
    #[must_use]
    pub fn is_completed(&self) -> bool {
        self.once.is_completed()
    }
}

impl<T> Default for TakeOnce<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for TakeOnce<T> {
    fn drop(&mut self) {
        if self.once.is_completed() {
            let ptr = self.value.swap(std::ptr::null_mut(), Ordering::Acquire);
            if !ptr.is_null() {
                // SAFETY: `self.value` is initialized (since `self.once.is_completed()`)
                // and has not been taken before (since `ptr` is not null).
                drop(unsafe { Box::from_raw(ptr) });
            }
        }
    }
}

// SAFETY: `TakeOnce` is `Send` iff `T` is `Send`.
unsafe impl<T: Send> Send for TakeOnce<T> {}
// SAFETY: `TakeOnce` does not allow shared access to the inner value.
unsafe impl<T: Send> Sync for TakeOnce<T> {}

#[cfg(all(test, feature = "_shuttle"))]
mod tests {
    use super::TakeOnce;
    use shuttle::sync::Arc;
    use shuttle::thread;

    #[test]
    fn concurrent_store_operations() {
        shuttle::check_random(
            || {
                let once_take = Arc::new(TakeOnce::new());
                let num_threads = 6;
                let threads: Vec<_> = (0..num_threads)
                    .map(|i| {
                        let once_take = once_take.clone();
                        thread::spawn(move || once_take.store(i))
                    })
                    .collect();

                let results: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();

                // Exactly one store should succeed
                assert_eq!(results.iter().filter(|r| r.is_ok()).count(), 1);
                // All other stores should return Err
                assert_eq!(
                    results.iter().filter(|r| r.is_err()).count(),
                    num_threads - 1
                );
            },
            100,
        );
    }

    #[test]
    fn concurrent_take_operations() {
        shuttle::check_random(
            || {
                let once_take = Arc::new(TakeOnce::new());

                // First store
                assert_eq!(once_take.store(42), Ok(()));

                // Concurrent takes
                let threads: Vec<_> = (0..3)
                    .map(|_| {
                        let once_take = once_take.clone();
                        thread::spawn(move || once_take.take())
                    })
                    .collect();

                let results: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();

                // Exactly one take should succeed
                assert_eq!(results.iter().filter(|r| r.is_some()).count(), 1);
                // The successful take should return 42
                assert!(results.iter().any(|r| r == &Some(42)));
                // All other takes should return None
                assert_eq!(results.iter().filter(|r| r.is_none()).count(), 2);
            },
            100,
        );
    }

    #[test]
    fn mixed_store_take_operations() {
        shuttle::check_random(
            || {
                let once_take = Arc::new(TakeOnce::new());

                // Alternate between store and take
                let num_threads = 6;
                let threads: Vec<_> = (0..num_threads)
                    .map(|i| {
                        let once_take = once_take.clone();
                        thread::spawn(move || {
                            if i % 2 == 0 {
                                once_take.store(i)
                            } else {
                                once_take.take().map_or(Err(i), |_| Ok(()))
                            }
                        })
                    })
                    .collect();

                let results = threads
                    .into_iter()
                    .map(|t| t.join().unwrap())
                    .collect::<Vec<_>>();

                // At least one operation should succeed
                assert!(results.iter().any(|r| r.is_ok()));
            },
            100,
        );
    }

    #[test]
    fn completion_status_consistency() {
        shuttle::check_random(
            || {
                let once_take = Arc::new(TakeOnce::new());
                let once_take2 = once_take.clone();

                assert!(!once_take.is_completed());

                let t1 = thread::spawn(move || {
                    once_take.store(42).unwrap();
                    once_take.is_completed()
                });

                let completed_after_store = t1.join().unwrap();
                assert!(completed_after_store);
            },
            100,
        );
    }

    #[test]
    fn store_take_ordering() {
        shuttle::check_random(
            || {
                let once_take = Arc::new(TakeOnce::new());
                let once_take2 = once_take.clone();
                let once_take3 = once_take.clone();

                let t1 = thread::spawn(move || {
                    once_take.store(42).unwrap();
                    // This release store should be visible to the take thread
                    true
                });

                let t2 = thread::spawn(move || {
                    // This acquire load should see the store if completed
                    if once_take2.is_completed() {
                        once_take2.take()
                    } else {
                        None
                    }
                });

                let t3 = thread::spawn(move || {
                    // Should never see a partial state
                    if once_take3.is_completed() {
                        assert!(once_take3.take().is_some() || once_take3.take().is_none());
                    }
                });

                assert!(t1.join().unwrap());
                t2.join().unwrap();
                t3.join().unwrap();
            },
            100,
        );
    }

    #[test]
    fn drop_consistency() {
        shuttle::check_random(
            || {
                let once_take = Arc::new(TakeOnce::new());
                let once_take2 = once_take.clone();

                // Store a value that implements Drop
                #[derive(Debug, PartialEq)]
                struct DropTest(i32);
                static DROPPED: shuttle::sync::Once = shuttle::sync::Once::new();
                impl Drop for DropTest {
                    fn drop(&mut self) {
                        let mut called = false;
                        DROPPED.call_once(|| called = true);
                        assert!(called);
                    }
                }

                once_take.store(DropTest(42)).unwrap();

                let t = thread::spawn(move || {
                    // Take the value in another thread
                    once_take2.take()
                });

                // The value should only be dropped once.
                let taken = t.join().unwrap();
                if let Some(val) = taken {
                    assert_eq!(val.0, 42);
                    drop(val);
                }

                assert!(DROPPED.is_completed());
            },
            100,
        );
    }
}
