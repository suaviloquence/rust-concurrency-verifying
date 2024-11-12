# rust-concurrency-verifying

## installation

1. Clone the repository with submodules

  ```sh
  git clone git@github.com:suaviloquence/rust-concurrency-verifying --recurse-submodules
  ```

2. Install/update [`rustup`](https://rustup.rs).

  The install script `tools/activate` invokes `rustup` directly to build the
  `vargo` binary, so you need to have `rustup` (vs system Rust install).

3. Install Z3, and set the `VERUS_Z3_PATH` environment variable

  `verus` docs say that you can use `verus/tools/get-z3.sh` but I haven't tested it.
  `verus` requires Z3 v4.12.5 (unless you run with the `--no-solver-version-check` flag).
  For me, I used:

  ```sh
  export VERUS_Z3_PATH="$(which z3)"
  ```

4. Build Verus:

  ```sh
  cd verus
  # this step builds `vargo`
  source tools/activate
  cd source
  # omit `--release` to build with debug symbols and checks
  vargo build --release
  ```

  This should build `vargo` and verus, as well as build and verify the `vstd`
  standard library.  For more help with this step, see `verus/INSTALL.md`.
