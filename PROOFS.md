# Security and Functional Correctness Proofs for Bertie

The `proofs/` directory holds ProVerif F\* proofs for code compiled by
hax from the Bertie Rust implementation of TLS 1.3.

## Correctness Proofs in F\*

Each Rust module `m` in the implementation is translated to two files:
`M.fst` contains the functionalized F\* code compiled from Rust, and
`M.fsti` contains the F\* types for each function, along with correctness
specifications in the form of pre- and post-conditions.

The first step before verification is to ensure that the generated F\* code
typechecks in "lax" mode, that is all its functions are well-typed when ignoring
the pre- and post-conditions. This is a basic well-formedness check akin
to typechecking the code in a language like Rust or OCaml. It also ensures
that all the dependencies of the code have been defined and correctly extracted.
The code in the `proofs/fstar/extraction-lax` directory has been lax-typechecked.

Then, the main correctness guarantee we prove for the Rust code is
that it never panics and that each function meets its specificaiton.
In particular, we would like to prove that:

- arithmetic operations never over- or under-flow
- array and vector operations never go out of bounds
- `unwrap`s always succeed and `panic`s are always unreachable

To achieve this, we compile each primitive operation in Rust to the
equivalent operation in F\*, as specified in
`hax/proof-libs/fstar/rust_primitives`. For example, the Rust
addition operation `+` translates to the polymorphic, strict machine
integer operation `+!` in F\*, which requires, as a precondition, that
the addition of its inputs does not overflow the target type.

Similarly, each array access is compiled to an instance of the `Index`
or `IndexMut` typeclass in F\*, both of which require as preconditions
that the index is not out-of-bounds.

Consequently, when we typecheck the code in `M.fst` we need to prove
that all its arithmetic operations, array accesses, etc are
type-safe. This proof often requires the pre-conditions to be
propagated to the calling functions, leading to additional annotations
to the functions types in the `M.fsti` interface files.

For the TLS 1.3 code in Bertie, the most interesting aspects of these
proofs are when we try to prove that the formatting and parsing functions
do not overflow. Indeed, by typechecking in F*, we found a number of
bugs in our packet parsing code.

The code in the `proofs/fstar/extraction-panic-free` directory has
been verified for panic freedom on all possible inputs. This means that
even in the presence of an attacker sending Bertie malformed messages,
the verified code will never create a panic. Of course, there is other
code outside the verification boundary that may yet panic and we intend
to expand the scope of our verification ocer time.

## Security Proofs in ProVerif

We also prove security for the TLS 1.3 protocol code in Bertie.
Using hax, we generate a ProVerif model of the TLS 1.3 handshake
in `proofs/proverif/extraction/lib.pvl`.  This file contains the bulk of the extraction,
while `analysis.pv` contains the top-level processes are set up and analysis queries.

We provide patches that include changes to the extracted model (described below), which allow us to show
* that the modeled handshake can fully complete for both parties (as a baseline for further analysis)
* Server authenticity, assuming neither the certificate signing key nor a potential pre-shared key have been compromised
* Secrecy of the resulting session key under the same assumptions.

The intended flow using the driver is to run

./hax-driver.py extract-proverif to extract the ProVerif model to proofs/proverif/extraction.
./hax-driver.py patch-proverif to apply the patches on the extracted model.
./hax-driver.py typecheck-proverif to run the analysis on the patched model.

The patches are necessary for parts of the model that we cannot currently generate (properly, or at all):
* a top-level process structure which instantiates Client and Server with ciphersuites and psk-mode configuration,
* event definitions and analysis queries,
* cryptographic operations and their semantics
* tls13formats related code, especially anything that relates to concatenation primitives

Additionally, the patches introduce the following modifications:
* A mock certificate validation, checking that the name in the certificate agrees with the name of the expected peer from the top-level process. This is because Bertie does not include full certificate validation at this time, but some binding between the name and the certificate is necessary for showing server authentication.
* A model-side fix for the issue that is fixed on the Rust side in Correct argument order for process_psk_binder_zero_rtt #101 (until that is fixed on the Rust side).
* The removal of all automatically generated events, since that leads to poor performance from ProVerif and is not necessary at all for the analysis (cf. [ProVerif] Emitting events unnecessarily blows up the extracted model hacspec/hax#581)
