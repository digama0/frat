# The FRAT format and FRAT-rs

Given a propositional formula in the DIMACS format and its proof 
of unsatisfiability in the FRAT format, FRAT-rs can be used to 
verify that the latter is a correct proof of the former. 

## Usage

FRAT-rs can be compiled using `make`.

`frat-rs elab DIMACSFILE FRATFILE LRATFILE` : Elaborates `FRATFILE`, the unsatisfiability proof of `DIMACSFILE`, and produces the corresponding `LRATFILE`

`frat-rs fratchk FRATFILE` : Analyzes `FRATFILE` and displays statistics

`frat-rs dratchk DIMACSFILE DRATFILE` : Checks `DRATFILE` against the input problem `DIMACSFILE`

`frat-rs lratchk DIMACSFILE LRATFILE` : Checks `LRATFILE` against the input problem `DIMACSFILE`

`frat-rs strip-frat FRATFILE NEWFRATFILE` : Processes `FRATFILE`, and produces a corresponding `NEWFRATFILE` with 0% annotations 

`frat-rs refrat ELABFILE FRATFILE` : Processes `ELABFILE`, a temporary file produced by the first elaboration pass of frat-rs, and produces `FRATFILE`, a corresponding FRAT proof with 100% annotations

`frat-rs from-drat DIMACSFILE DRATFILE FRATFILE` : Processes `DIMACSFILE` and `DRATFILE` to produce a corresponding `FRATFILE` with 0% annotations




