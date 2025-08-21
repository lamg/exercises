# Exercises in Logical Foundations

Create Opam switch:

```bash
opam switch create rocq9 ocaml-base-compiler.5.3.0
opam install rocq-prover
eval $(opam env --switch=rocq9 --set-switch)
opam pin add rocq-prover 9.0.0
opam install coq
```

Build:

```bash
rocq makefile -o Makefile -R src LogicalFoundations src/*.v
make
```

or:

```bash
coq_makefile -f _CoqProject -o Makefile 
```

or:

```bash
dune build        # compile theories
dune runtest      # run your tests
```

