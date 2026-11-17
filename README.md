# Callcc Logics

Program logics for `call/cc` and `call/1cc`.

Follow the [installation instructions](#installation) to build the project (automatically or manually).

## Theories

### Language

* [syntax.v](/theories/syntax.v)
* [notation.v](/theories/notation.v)
* [semantics.v](/theories/semantics.v)
* [iris_instantiation.v](/theories/iris_instantiation.v)

### Logic

* [logic.v](/theories/logic.v): Weakest precondition, Hoare triples, and reasoning rules.
* [adequacy.v](/theories/adequacy.v)

### Case studies

* [callcc_from_callcc_one_shot.v](/theories/case_studies/callcc_from_callcc_one_shot.v)
* [concurrency.v](/theories/case_studies/concurrency.v)
* [control_inversion.v](/theories/case_studies/control_inversion.v)
* [effect_handlers.v](/theories/case_studies/effect_handlers.v)
* [with_perform.v](/theories/case_studies/with_perform.v)

## Code

Implementation of `call/1cc` and `call/1cc0` in OCaml 5 and code for examples in the paper:

* [src/call1cc0.ml](/src/call1cc0.ml)


## Installation

### Automatic

After installing a recent version (`2.3.0` or later) of [`opam`](https://opam.ocaml.org/doc/Install.html), the OCaml package manager, simply run the script `setup.sh` to install a *local opam switch* with the correct versions of the dependencies (`Rocq`, `stdpp`, and `Iris`) and compile the proofs:

```
chmod +x ./setup.sh
```
```
./setup.sh
```

### Manual

**Step 1.** Install a fresh *opam switch*:

```
opam switch create ocaml-base-compiler.5.3.0
```

**Step 2.** Add `Rocq`'s and `Iris`'s `opam` repositories:

```
opam repo add rocq-prover-released https://rocq-prover.org/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```

**Step 3.** Install `Rocq` and `Iris` with the following commands:

```
opam install rocq-prover.9.3.0
opam install rocq-iris-heap-lang.dev.2026-11-16.0.e20f2f0f
```

**Step 4.** Run `make` to compile the proofs.


### Troubleshooting

**Conflicting `iris-dev`.** When running `./setup.sh`, `opam` may complain that the repository `iris-dev` already exists with a different URL. If this happens, please run

```
opam repo remove iris-dev --all
```

and then try `./setup.sh` again. (You will later need to re-declare the `iris-dev` repository.)

**RocqIDE.** If you want to browse the proofs using RocqIDE, you might need to install and use a fresh copy of the IDE on the new opam switch. To install RocqIDE, it suffices to run:

```
opam install coqide.8.20.1
```
