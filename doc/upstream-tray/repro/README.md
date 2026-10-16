# Reproducers for the upstream Lem drafts

One directory per reproducer. Each holds the `.lem` source, an OCaml
driver where the values need printing (`main.ml`), and the transcript of
the run on 2026-10-03 (`transcript-2026-10-03.txt`).

| Directory | Drafts |
|---|---|
| `blk/` | 01 |
| `sect/` | 02 |
| `b10/` | 03 |
| `failarg/` | 04 |
| `mword/` | 05, 06, 07, 08, 09, 21 |
| `divmod/` | 10 |
| `libdefs/` | 11, 12, 16, 20 |
| `x1/` | 13 |
| `the/` | 14 (`transcript-norep-2026-10-03.txt`: the comparison case) |
| `transform/` | 15 |
| `replicate/` | 17 |
| `genlist/` | 18 |
| `bitwise/` | 19 |
| `nat63/` | 22 |
| `andsep/` | 23 (its own `run.sh`; needs only `LEM`) |

## Re-running

You need an upstream Lem checkout built with `make` (`LEMSRC`, its `lem`
binary as `LEM`), and that checkout's `ocaml-lib` compiled into
`extract.cmxa` (`LEM_OCAMLLIB`; the name avoids the compiler's own
`OCAMLLIB` variable, which would break `ocamlopt`). For the transcripts
here the library was copied to a scratch directory and compiled with

```
make -f no_ocamlbuild.mk BUILD_DEPS=false     # compiles the .cmx files
ocamlfind ocamlopt -g -a -o extract.cmxa -I num_impl_zarith <the .cmx files, in the Makefile's order>
```

(the archive step of `no_ocamlbuild.mk` passes the `.mli` files to
`ocamlopt -a` and fails, so it was done by hand). Then

```
LEM=… LEMSRC=… LEM_OCAMLLIB=… ./run-all.sh /some/new/workdir
```

copies this directory to the work directory, runs everything there and
writes `<case>/transcript.txt`. The 2026-10-03 run printed
`lem -v: Lem 3802cb0`, `5.4.0` and `zarith (version: 1.14)` first.
Timings (`genlist/`, `replicate/`) vary between runs.

The checks of the fixes quoted in drafts 01 and 03 were run by hand on
local branch builds, which have since been deleted (README §5); they are
not part of `run-all.sh`. To run a patched upstream build, use the `lem`
symlink at the root of the checkout (to `src/main.native`), not
`bin/lem`: `bin/lem` looks for the library next to `bin/` and fails to
find `Pervasives` (an independent verifier's note, 2026-10-03).
