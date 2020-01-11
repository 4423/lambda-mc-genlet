naive: fix_functor.naive.ml bench.ml
	metaocamlc -c fix_functor.naive.ml -o fix_functor
	metaocamlc -c bench.ml -o bench
	metaocamlc fix_functor.cmo bench.cmo -o bench.out

codegen: fix_functor.gen.ml fix_functor.opt.ml bench.ml
	metaocamlc -c fix_functor.gen.ml -o fix_functor_gen
	metaocamlc -c fix_functor.opt.ml -o fix_functor
	metaocamlc -c bench.ml -o bench
	metaocamlc fix_functor_gen.cmo fix_functor.cmo bench.cmo -o bench.out

pepm20: fix_functor.gen.pepm20.ml fix_functor.opt.ml bench.ml
	metaocamlc -c fix_functor.gen.pepm20.ml -o fix_functor_gen
	metaocamlc -c fix_functor.opt.ml -o fix_functor
	metaocamlc -c bench.ml -o bench
	metaocamlc fix_functor_gen.cmo fix_functor.cmo bench.cmo -o bench.out

clean:
	rm -f *.mli *.cmo *.cmi *.cmx *.a *.o *.out
