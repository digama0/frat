# The FRAT format and FRAT-rs

FRAT-rs is a toolchain for processing and transforming files in the [FRAT format](https://link.springer.com/chapter/10.1007/978-3-030-72016-2_4).

## Usage

FRAT-rs can be compiled using `make`. (It is written in Rust, so you will need to
[get Rust](https://rustup.rs/) first to put `cargo` in your path.)

* `frat-rs elab FRATFILE [--full] [-s|-ss] [-m[NUM] LRATFILE [DIMACSFILE] [-v] [-c]]`:
  Elaborates `FRATFILE`, the unsatisfiability proof of `DIMACSFILE`,
  and produces the corresponding `LRATFILE`.

  * If `--full` is specified, the entire FRAT file is checked,
    including steps that do not contribute to the final contradiction.
    (The default is to skip these steps, so we might generate a valid proof
    without ever noticing that the step that was skipped is not well formed.)

  * If `-s` is specified, the FRAT file is checked in "strict mode", which means
    that bogus proofs in `l` steps will be rejected. (The default behavior
    is to instead fall back on no-hint mode if the hint is wrong.)

  * If `-ss` is specified, the FRAT file is checked in "extra-strict mode",
    in which `l` steps cannot be omitted.

  * If `-m` is specified, the intermediate file (between FRAT and LRAT) will
    be generated in memory instead of on disk, which might be faster.
    The optional `NUM` argument is a size hint for the initial allocation in
    bytes, which defaults to 5 times the size of the `FRATFILE`.

  * If `DIMACSFILE` is specified, the resulting output will be checked against
    the given CNF, otherwise only the first phase of elaboration will run,
    producing a `FRATFILE.temp` file but no other output.
    (This temporary file is useful as input to `refrat`.)

  * If `LRATFILE` is specified, the output will be placed in `LRATFILE`,
    otherwise the elaborator will run but no output will be produced.

  * If `-v` is specified, the LRAT file is passed directly to `lratchk`.
    Omitting `LRATFILE` and specifying `-v` is a way to verify FRAT files
    without otherwise generating output.

  * If `-c` is specified (requires `LRATFILE`), comment lines from the original
    FRAT file will be transmitted to the `LRATFILE`. This is a good way to align
    important points in the proof with the output, but it is disabled by default
    since some LRAT checkers don't support comments.

  This is the main subcommand you want to use, if you are a solver developer
  producing FRAT files.

* `frat-rs lratchk DIMACSFILE LRATFILE`:
  Checks `LRATFILE` against the input problem `DIMACSFILE`.

  This is essentially the same as
  [`lrat-check.c`](https://github.com/marijnheule/drat-trim/blob/master/lrat-check.c)
  but it is more robust (at the time of writing) and has
  no known bugs. It is provided as a convenience for FRAT and LRAT file testing,
  but for actual high assurance scenarios you should use `elab` to generate an
  LRAT file and then use a formally verified LRAT checker like
  [`cake_lpr`](https://github.com/tanyongkiam/cake_lpr) to check the resulting file.

* `frat-rs stat FRATFILE`:
  Analyzes `FRATFILE` and displays statistics

* `frat-rs strip-frat FRATFILE NEWFRATFILE`:
  Processes `FRATFILE`, and produces a corresponding `NEWFRATFILE` with 0% annotations

* `frat-rs refrat ELABFILE FRATFILE`:
  Processes `ELABFILE`, a temporary file produced by the first elaboration
  pass of frat-rs, and produces `FRATFILE`, a corresponding FRAT proof with
  100% annotations

* `frat-rs to-cnf FRATFILE > DIMACSFILE`:
  FRAT files contain a copy of the CNF inside them. This command constructs
  a CNF file that `FRATFILE` could be a proof of, and writes it to stdout
  (or pipes it to `DIMACSFILE` in this example)

* `frat-rs from-drat DIMACSFILE DRATFILE FRATFILE`:
  Processes `DIMACSFILE` and `DRATFILE` to produce a corresponding `FRATFILE`
  with 0% annotations. Note that despite the name, this also works on PR files,
  and will translate them into FRAT files with PR steps.

* `frat-rs from-pr DIMACSFILE PRFILE FRATFILE`:
  Processes `DIMACSFILE` and `PRFILE` to produce a corresponding `FRATFILE`
  with no PR steps. This implements the
  [`pr2drat`](https://github.com/marijnheule/pr2drat) algorithm, but with proofs
  supplied in the resulting FRAT file.

  Note that `elab` can directly handle PR steps in FRAT files, and they will
  be preserved in the output (resulting in LPR files instead of LRAT). So the
  main reason you would use this command is if you want pure LRAT output,
  or just as another way to slice data to get another data set.

* Experimental subcommands:

  * `frat-rs drat-trim`: A clone of
    [`drat-trim`](https://github.com/marijnheule/drat-trim/) in true
    "Rewrite it in Rust" fashion. It has exactly the same behavior and options
    as the original, see the README there for more info.

  * `frat-rs dratchk DIMACSFILE DRATFILE`:
    Checks `DRATFILE` against the input problem `DIMACSFILE` (unmaintained)
