src/Basics.vo src/Basics.glob src/Basics.v.beautified src/Basics.required_vo: src/Basics.v /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
src/Basics.vos src/Basics.vok src/Basics.required_vos: src/Basics.v /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
src/Induction.vo src/Induction.glob src/Induction.v.beautified src/Induction.required_vo: src/Induction.v src/Basics.vo /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
src/Induction.vos src/Induction.vok src/Induction.required_vos: src/Induction.v src/Basics.vos /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
src/Lists.vo src/Lists.glob src/Lists.v.beautified src/Lists.required_vo: src/Lists.v src/Basics.vo src/Induction.vo /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
src/Lists.vos src/Lists.vok src/Lists.required_vos: src/Lists.v src/Basics.vos src/Induction.vos /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
src/Logic.vo src/Logic.glob src/Logic.v.beautified src/Logic.required_vo: src/Logic.v src/Basics.vo src/Poly.vo src/Tactics.vo /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
src/Logic.vos src/Logic.vok src/Logic.required_vos: src/Logic.v src/Basics.vos src/Poly.vos src/Tactics.vos /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
src/Poly.vo src/Poly.glob src/Poly.v.beautified src/Poly.required_vo: src/Poly.v src/Basics.vo src/Lists.vo /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
src/Poly.vos src/Poly.vok src/Poly.required_vos: src/Poly.v src/Basics.vos src/Lists.vos /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
src/Tactics.vo src/Tactics.glob src/Tactics.v.beautified src/Tactics.required_vo: src/Tactics.v src/Basics.vo src/Induction.vo src/Poly.vo /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
src/Tactics.vos src/Tactics.vok src/Tactics.required_vos: src/Tactics.v src/Basics.vos src/Induction.vos src/Poly.vos /home/lamg/.opam/default/lib/rocq-runtime/rocqworker
