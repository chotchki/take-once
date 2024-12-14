# take-once

[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/AmitPr/take-once)
[![Cargo](https://img.shields.io/crates/v/take-once.svg)](https://crates.io/crates/take-once)
[![Documentation](https://docs.rs/take-once/badge.svg)](https://docs.rs/take-once)

A thread-safe container for one-time storage and one-time consumption of a value.

## Usage

```rust
use take_once::TakeOnce;

let cell = TakeOnce::new();

// Initial store succeeds
assert_eq!(cell.store(42), None);

// Subsequent stores return the provided value
assert_eq!(cell.store(24), Some(24));

// Take the value
assert_eq!(cell.take(), Some(42));

// Can't take twice
assert_eq!(cell.take(), None);

// Can be used across threads via `Arc`
use std::sync::Arc;
use std::thread;

let cell = Arc::new(TakeOnce::new());

let cell_clone = cell.clone();
let handle = thread::spawn(move || {
    assert_eq!(cell_clone.take(), Some(42));
});
handle.join().unwrap();

assert_eq!(cell.take(), Some(42));
```

See the [documentation](https://docs.rs/take-once) for more details.

## Testing

This crate uses [shuttle](https://docs.rs/shuttle) for (more) exhaustive testing. To run the shuttle tests, run:

```sh
cargo test --features _shuttle
```

## License

MIT
