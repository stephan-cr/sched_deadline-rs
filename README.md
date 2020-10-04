sched\_deadline - Setup SCHED\_DEADLINE in Rust
===============================================

## Usage

```toml
[dependencies]
sched_deadline = { git = "https://github.com/stephan-cr/rust_sched_deadline" }
```

## Execution

To gain realtime capability, the executable must either run as root or
must have the
[`CAP_SYS_NICE`](https://man7.org/linux/man-pages/man2/nice.2.html)
capability.

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
