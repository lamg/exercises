src/Basics.vo src/Basics.glob src/Basics.v.beautified src/Basics.required_vo: src/Basics.v 
src/Basics.vio: src/Basics.v 
src/Basics.vos src/Basics.vok src/Basics.required_vos: src/Basics.v 
src/Induction.vo src/Induction.glob src/Induction.v.beautified src/Induction.required_vo: src/Induction.v src/Basics.vo
src/Induction.vio: src/Induction.v src/Basics.vio
src/Induction.vos src/Induction.vok src/Induction.required_vos: src/Induction.v src/Basics.vos
test/Rocq_test.vo test/Rocq_test.glob test/Rocq_test.v.beautified test/Rocq_test.required_vo: test/Rocq_test.v 
test/Rocq_test.vio: test/Rocq_test.v 
test/Rocq_test.vos test/Rocq_test.vok test/Rocq_test.required_vos: test/Rocq_test.v 
