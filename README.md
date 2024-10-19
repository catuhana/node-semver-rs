This crate is a pure Rust-based implementation of JavaScript's
[`node-semver`](https://npm.im/semver). That is, it's designed to be
compatible with Node/NPM's particular flavor of semver (which the [`semver`
crate](https://crates.io/crates/semver) is not).

It is designed for Rust programs and libraries meant for JavaScript tooling,
and does its best to stay compatible with `node-semver`.

It also supports [`serde`](https://crates.io/crates/serde) serialization,
converting versions and ranges to strings. Enable `serde` feature to use them.

For advanced diagnostics with `miette`, enable `miette` feature.

> [!IMPORTANT]
> This fork is tailored for my use case, e.g. fixing Clippy issues, bumping dependencies and if it's not updated regularly, cherry-picking some PRs that I need. You most likely don't want to use this, so please go to the upstream repository. If you end up using this and if a behaviour is different/unexpected, do NOT create an issue about it in the upstream.

## Usage

`node-semver` includes two main types: [Version] and [Range]. See [the
documentation](https://docs.rs/node-semver) for more details.:

```rust
use node_semver::{Range, Version};

let version: Version = "1.2.3".parse().unwrap();
let range: Range = "^1.2".parse().unwrap();

assert!(version.satisfies(&range));
```

## Minimum Suggested Rust Version (MSRV)

You must be 1.70.0 or taller to get on this ride.
