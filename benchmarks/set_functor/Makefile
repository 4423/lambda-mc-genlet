naive: set_functor.naive.ml bench.ml
	metaocamlc -c set_functor.naive.ml -o set_functor
	metaocamlc -c bench.ml -o bench
	metaocamlc set_functor.cmo bench.cmo -o bench.out

codegen: set_functor.gen.ml set_functor.opt.ml bench.ml
	metaocamlc -c set_functor.gen.ml -o set_functor_gen
	metaocamlc -c set_functor.opt.ml -o set_functor
	metaocamlc -c bench.ml -o bench
	metaocamlc set_functor_gen.cmo set_functor.cmo bench.cmo -o bench.out

clean:
	rm -f *.mli *.cmo *.cmi *.cmx *.a *.o *.out
