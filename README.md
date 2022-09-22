<img src="assets/bertie-logo.png" width="200px"/>

[![CI](https://github.com/cryspen/bertie/actions/workflows/ci.yml/badge.svg)](https://github.com/cryspen/bertie/actions/workflows/ci.yml)
[![Scheduled](https://github.com/cryspen/bertie/actions/workflows/scheduled.yml/badge.svg)](https://github.com/cryspen/bertie/actions/workflows/scheduled.yml)

Bertie is a minimal, high-assurance implementation of TLS 1.3 written in a subset of Rust called [hacspec].

It is built upon the following design principles:

1) **Purely functional**: no mutable data structures or externally visible side-effects.
2) **Verification friendly**: written in hacspec and translates to [F*].
3) **Succinct and minimal**: configured with a single protocol version and cipher suite.

Karthikeyan Bhargavan first authored Bertie at Inria in 2021 and transferred it to [Cryspen] in 2022.
It is licensed under [Apache 2.0](LICENSE) but not yet ready for public consumption.

### USING BERTIE

An example HTTPS client using Bertie is provided in the `simple_https_client` crate.
The client retrieves a web page using Bertie as the underlying TLS implementation.

You can try it out by executing ...

```bash
$ cd simple_https_client
$ cargo run -- example.com
```

There is also a HTTPS server available as `simple_https_server`.

*WARNING*: Do not use in production. This is an early draft of Bertie and strictly work-in-progress.

If you are looking for commercial support for Bertie, please [reach out to Crypsen](mailto:info@cryspen.com).

### CONTRIBUTING

To see what we are working on and what is in the pipeline, you can follow our [project tasks].

Before contributing, please have a look at the [contributing guidelines] and the [code of conduct].

#### PROJECT STRUCTURE

* `.github` contains the configuration for GitHub Actions CI.
* `assets` contains non-code files that are used in the Bertie project. (Only logo for now.)
* `bogo_shim` contains the BoGo shim application that is used for testing against BoringSSL's test runner.
* `record` is a crate that provides common functionality used in `simple_https_client` and `simple_https_server`.
* `simple_https_client` is an example crate that implements a Bertie HTTPS client.
* `simple_https_server` is an example crate that implements a Bertie HTTPS server.
* `src` contains the Bertie source code (that must be valid according to hacspec.)
* `tests` contains all tests.

### PUBLICATIONS

Bertie is inspired by a number of prior research works, including works on [hacspec] and TLS 1.3.

Some of the most relevant publications are listed below:

* *Hacspec: succinct, executable, verifiable specifications for high-assurance cryptography embedded in Rust.* Denis Merigoux, Franziskus Kiefer, Karthikeyan Bhargavan.  Inria Technical Report, 2021. [hal-03176482](https://hal.inria.fr/hal-03176482)
* *Verified Models and Reference Implementations for the TLS 1.3 Standard Candidate.* Karthikeyan Bhargavan, Bruno Blanchet, Nadim Kobeissi.  38th IEEE Symposium on Security and Privacy, 2017. [hal-01575920](https://hal.inria.fr/hal-01575920)
* *A Messy State of the Union: Taming the Composite State Machines of TLS.* Benjamin Beurdouche, Karthikeyan Bhargavan, Antoine Delignat-Lavaud, Cédric Fournet, Markulf Kohlweiss, Alfredo Pironti, Pierre-yves Strub, Jean Karim Zinzindohoue. IEEE Symposium on Security & Privacy, 2015. [hal-01114250](https://hal.inria.fr/hal-01114250/)

### LICENSE

Bertie is licensed under [Apache 2.0](LICENSE).

### ACKNOWLEDGEMENTS

The Bertie project is supported by [Inria] and the [nlnet foundation].

[project tasks]: https://github.com/orgs/cryspen/projects/2/views/2
[code of conduct]: CODE_OF_CONDUCT.md
[contributing guidelines]: CONTRIBUTING.md
[hacspec]: https://github.com/hacspec/hacspec
[F*]: https://www.fstar-lang.org/
[Cryspen]: https://www.cryspen.com/
[Inria]: https://www.inria.fr
[nlnet foundation]: https://nlnet.nl/project/Bertie/
