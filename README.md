<img src="bertie-logo.png" width="200px"/>

Bertie is a minimal, high-assurance implementation of TLS 1.3 written in subset of Rust called [hacspec](https://github.com/hacspec/hacspec).

It follows design principles:

1) It is purely functional: it has no mutable data structures or externally visible side-effects
2) It is verification friendly: it is written in hacspec and translates to F*
3) It is succinct and minimal: it is configured with a single protocol version and ciphersuite

Bertie was first authored by Karthikeyan Bhargavan at Inria in 2021 and subsequently transferred to Cryspen in 2022.
It is licensed under [Apache 2.0](LICENSE) but is not yet ready for public consumption.

Before contributing please have a look at the [contributing guidelines](CONTRIBUTING.md) and the [code of conduct](CODE_OF_CONDUCT.md).

If you are looking for commercial support for Bertie, please [reach out](info@cryspen.com).

The Bertie project is supported by the [nlnet foundation](https://nlnet.nl/project/Bertie/).

*WARNING*: This is an early draft and work-in-progress. Do not use in production.

