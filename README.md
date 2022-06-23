<img src="assets/bertie-logo.png" width="200px"/>

Bertie is a minimal, high-assurance implementation of TLS 1.3 written in subset of Rust called [hacspec](https://github.com/hacspec/hacspec).

It follows design principles:

1) It is purely functional: it has no mutable data structures or externally visible side-effects
2) It is verification friendly: it is written in hacspec and translates to F*
3) It is succinct and minimal: it is configured with a single protocol version and ciphersuite

Bertie was first authored by Karthikeyan Bhargavan at Inria in 2021 and subsequently transferred to Cryspen in 2022.
It is licensed under [Apache 2.0](LICENSE) but is not yet ready for public consumption.

**USING BERTIE**

An example application using Bertie is provided in the `simple_https_client` crate that implements an HTTPS client that
connects to and retrieves a web page using Bertie as the underlying TLS implementation.

You can try out this client by executing in `simple_https_client`:
```
cargo run example.com
```

*WARNING*: This is an early draft of Bertie and strictly work-in-progress. Do not use in production.

If you are looking for commercial support for Bertie, please [reach out](mailto:info@cryspen.com).

**CONTRIBUTING**

To see what we are working on and what is in the pipeline, you can follow our [project tasks](https://github.com/orgs/cryspen/projects/2/views/2).

Before contributing please have a look at the [contributing guidelines](CONTRIBUTING.md) and the [code of conduct](CODE_OF_CONDUCT.md).

**PUBLICATIONS**

Bertie is inspired by a number of prior research works, including works on [hacspec](https://github.com/hacspec/hacspec) and TLS 1.3.
Some of the most relevant publications are listed below:

* Hacspec: succinct, executable, verifiable specifications for high-assurance cryptography embedded in Rust. Denis Merigoux, Franziskus Kiefer, Karthikeyan Bhargavan.  Inria Technical Report, 2021. [hal-03176482](https://hal.inria.fr/hal-03176482)
* Verified Models and Reference Implementations for the TLS 1.3 Standard Candidate. Karthikeyan Bhargavan, Bruno Blanchet, Nadim Kobeissi.  38th IEEE Symposium on Security and Privacy, 2017. [hal-01575920](https://hal.inria.fr/hal-01575920)
* A Messy State of the Union: Taming the Composite State Machines of TLS. Benjamin Beurdouche, Karthikeyan Bhargavan, Antoine Delignat-Lavaud, Cédric Fournet, Markulf Kohlweiss, Alfredo Pironti, Pierre-yves Strub, Jean Karim Zinzindohoue.  IEEE Symposium on Security & Privacy, 2015. [hal-01114250](https://hal.inria.fr/hal-01114250/)

**ACKNOWLEDGEMENTS**

The Bertie project is supported by [Inria](https://www.inria.fr) and the [nlnet foundation](https://nlnet.nl/project/Bertie/).


