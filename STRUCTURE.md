# Structure of the artifact

The tool is located at `/usr/src/artifact/smt-scope` within the image (the working directory when running the image). A copy of this directory is included in `smt-scope` at the root of the artifact, to allow files to be inspected locally (the `eval/smt-logs` directory is missing from the local copy to reduce size). We now explain the structure of this directory.

- The `smt-scope-lib` directory contains the code for the parsing and analysis of z3 trace files. This directory can be built as a standalone Rust crate to produce the two command line tools used in the artifact (`z3-scope` and `smt-scope`). This crate is also published on [crates.io](https://crates.io/crates/smt-scope-lib) and can be used as a library in other Rust projects.
- The `smt-scope-gui` directory contains the code for the GUI frontend. It depends on `smt-scope-lib` for parsing and analysis and visualizes the results.
- The `test-smtlib` directory contains various `.smt2` files used for CI testing of the tool.
  - The `test-smtlib/custom/paper` directory contains the `.smt2` presented in Section 2 of the paper.
- The `eval` directory contains the evaluation scripts and data, used in Section 3 of the paper.
  - The `eval/build.sh` script builds both SMTScope and downloads the Axiom Profiler. It must be run before the evaluation scripts.
  - The `eval/eval.sh` script runs both tools on the collected `.smt2` files and dumps the results to `eval/data`.
  - The `eval/smt-logs/smt2` directory contains the `.smt2` files used in the evaluation.
  - The `eval/Analyse.ipynb` notebook is used to analyse the results and produce the tables and graphs in the paper.
