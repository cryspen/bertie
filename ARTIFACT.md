# Instructions for artifact evaluation

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
