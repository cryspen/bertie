

t13 is a minimal, high-assurance implementation of TLS 1.3 written in a subset of Rust called [hacspec].

It is built upon the following design principles:

1) **Purely functional**: no mutable data structures or externally visible side-effects.
2) **Verification friendly**: written in hacspec and translates to [F*].
3) **Succinct and minimal**: configured with a single protocol version and cipher suite.


### USING t13

An example HTTPS client using t13 is provided in the `simple_https_client` crate.
The client retrieves a web page using t13 as the underlying TLS implementation.

You can try it out by executing ...

```bash
$ cargo run -p simple_https_client -- google.com
```

There is also a HTTPS server available as `simple_https_server`.

*WARNING*: Do not use in production. This is an early draft of t13 and strictly work-in-progress.


### WORKING ON t13

Note: You do not need to do any of this when you just want to build and run t13. This is only if you intend to *work* on t13, i.e., change its core and contribute the changes to the project.

Keep in mind that t13 is written in [hacspec] -- a more "restrictive" version of Rust that lends itself to formal verification.
Working on t13 feels a lot like working on a typical Rust crate but all code needs to be valid according to hacspec.
Thus, you may also find that some code is "unusual" compared to vanilla Rust.

But no worries!
There is a Cargo plugin to verify that everything is valid according to hacspec.
Just follow the instructions on the [hacspec] website to install it.
Then, set a [rustup override](https://rust-lang.github.io/rustup/overrides.html) to the channel currently used in the [hacspec repository](https://github.com/hacspec/hacspec/blob/master/rust-toolchain), i.e., ...

```sh
rustup override set <channel>
```

You can then `cargo clean`, `cargo build`, and `cargo hacspec` to verify that your changes conform to the hacspec specification.

### CONTRIBUTING


Before contributing, please have a look at the [contributing guidelines] and the [code of conduct].

#### PROJECT STRUCTURE

* `.github` contains the configuration for GitHub Actions CI.
* `bogo_shim` contains the BoGo shim application that is used for testing against BoringSSL's test runner.
* `record` is a crate that provides common functionality used in `simple_https_client` and `simple_https_server`.
* `simple_https_client` is an example crate that implements a t13 HTTPS client.
* `simple_https_server` is an example crate that implements a t13 HTTPS server.
* `src` contains the t13 source code (that must be valid according to hacspec.)
* `tests` contains all tests.

### PUBLICATIONS

t13 is inspired by a number of prior research works, including works on [hacspec] and TLS 1.3.

Some of the most relevant publications are listed below:

* *Verified Models and Reference Implementations for the TLS 1.3 Standard Candidate.* Karthikeyan Bhargavan, Bruno Blanchet, Nadim Kobeissi.  38th IEEE Symposium on Security and Privacy, 2017. [hal-01575920](https://hal.inria.fr/hal-01575920)
* *A Messy State of the Union: Taming the Composite State Machines of TLS.* Benjamin Beurdouche, Karthikeyan Bhargavan, Antoine Delignat-Lavaud, Cédric Fournet, Markulf Kohlweiss, Alfredo Pironti, Pierre-yves Strub, Jean Karim Zinzindohoue. IEEE Symposium on Security & Privacy, 2015. [hal-01114250](https://hal.inria.fr/hal-01114250/)



### ACKNOWLEDGEMENTS


[code of conduct]: CODE_OF_CONDUCT.md
[contributing guidelines]: CONTRIBUTING.md
[hacspec]: https://github.com/hacspec/hacspec
[F*]: https://www.fstar-lang.org/
