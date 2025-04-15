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
### Setting up Roq + SSProve
### Setting up ProVerif
We use ProVerif version 2.05 to perform protocol security analysis of the
implementation, as described in section 6 of the paper submission.
To be able to reproduce the analysis, please follow the installation
instructions provided at:

https://bblanche.gitlabpages.inria.fr/proverif/

## Proof extraction using hax
### F*
### SSProve
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
### SSProve
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
