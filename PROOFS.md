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

We can show
* that the modeled handshake can fully complete for both parties (as a baseline for further analysis)
* Server authenticity, assuming the certificate signing key is not
  compromised 
* Forward secrecy of the resulting session key under the same assumptions.

The intended flow using the driver is to run
```
./hax-driver.py extract-proverif to extract the ProVerif model to proofs/proverif/extraction.
./hax-driver.py typecheck-proverif to run the analysis
```

## Security of the Key Schedule in SSProve

We extract the implementation of the Key Schedule from SSProve.
We then fix the implementation to only include the parts we need and make sure the translation is actually valid.
This is done with a patch file to allow easier updates to the implementation.

The proof for security of the key schedule is done on a specification.
The entry functions of the specification are generalized and then instantiated with the functions in the implementation.
We show the implemented functions fulfill some properties to be valid in the key schedule proof.

The proof for the specification follows the proof in "Key-schedule Security for the TLS 1.3 Standard."
We prove the Core Key Schedule Theorem by showing the main lemma D6.
The other lemmas are a direct consequence of the correct implementation of the cryptographic primitives, which we inherit from libcrux.
These lemmas are therefore only stated, and the proof is Admitted.
