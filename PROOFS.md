# Security and Functional Correctness Proofs for Bertie

The `proofs/` directory holds ProVerif, F\*, and SSProve proofs for code compiled by
hax from the Bertie Rust implementation of TLS 1.3.

## Prerequisites
### Setting up the hax toolchain
We use the hax toolchain to extract proof artifacts from the Rust
source code in `src`. To be able to reproduce this extraction for
yourself, please follow the installation instructions for `hax`
provided at:

https://github.com/cryspen/hax?tab=readme-ov-file#installation

#### `hax-driver.py`
We use the Python 3 script `hax-driver.py` to drive extraction and
verification of the proof artifacts, so an installation of Python 3 is
required.

### Setting up F*
We use F* version 2025.03.25 to prove runtime safety and transcript
unambiguity as described in section 7 of the paper submission. To
reproduce these results for yourself, please install F* following the
instructions at:

https://fstar-lang.org/index.html#download

### Setting up Rocq + SSProve
We use Rocq version 8.18.0 and SSProve for the security proofs of the
key schedule as described in section 5 of the paper submission. Installation
instructions can be found at:

https://rocq-prover.org/install
https://github.com/SSProve/ssprove

Furthermore, Rust core library, which is used by the Hax translation, for Rocq/SSProve is located at:

https://github.com/cryspen/hax/tree/main/proof-libs

### Setting up ProVerif
We use ProVerif version 2.05 to perform protocol security analysis of the
implementation, as described in section 6 of the paper submission.
To be able to reproduce the analysis, please follow the installation
instructions provided at:

https://bblanche.gitlabpages.inria.fr/proverif/

## Proof extraction using hax
### F*
To regenerate the extraction to F*, run
```
./hax-driver.py extract-fstar
```

### SSProve
To regenerate the extraction for the key schedule in SSProve, run
```
./hax-driver.py extract-ssprove
```

To get the code running we apply a patch
```
patch -d extraction/ < extraction.patch
rm -rf fextraction/
mv extraction/ fextraction/
```

### ProVerif
The ProVerif proofs described in section 6 of the paper submission can
be extracted from the Rust source code by running
```
./hax-driver.py extract-proverif
```

This will generate the file `proofs/proverif/extraction/lib.pvl` from
the Rust source code.

## Running the Proofs
### F*
To run the F* proofs, run the following command:
```
./hax-driver.py typecheck
```

### SSProve
First generate the Makefile from the _CoqProject
```
coq_makefile -f _CoqProject -o Makefile
```
and run `make`.

### ProVerif
To run the ProVerif analysis, as described in section 6 of the paper
submission, run
```
./hax-driver.py typecheck-proverif
```

This will run the command 
```
proverif -lib proofs/proverif/handwritten_lib.pvl -lib
proofs/proverif/extraction/lib.pvl proofs/proverif/extraction/analysis.pv
```
to start the analysis. The file `handwritten_lib.pvl` exists for
technical reasons and contains early
definitions of certain terms. The file `analysis.pvl` contains the
top-level protocol process and analysis queries, as described in
section 6 of the paper submission.

## Results

### Correctness Proofs in F\*

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

### Security Proofs in ProVerif

We also prove security for the TLS 1.3 protocol code in Bertie.
Using hax, we generate a ProVerif model of the TLS 1.3 handshake
in `proofs/proverif/extraction/lib.pvl`.  This file contains the bulk of the extraction,
while `analysis.pv` contains the top-level processes are set up and analysis queries.

We can show
* that the modeled handshake can fully complete for both parties (as a baseline for further analysis)
* Server authenticity, assuming the certificate signing key is not
  compromised 
* Forward secrecy of the resulting session key under the same assumptions.

### Security of the Key Schedule in SSProve

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
