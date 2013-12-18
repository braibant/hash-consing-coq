

test:
	rm -rf _build/
	ocamlbuild -I extracted -lib unix test.p.native
	ocamlbuild -tag debug -I extracted -lib unix test.native

vo:
	coqc monads.v
	coqc smart_common.v
	coqc reference_lambda.v
	coqc smart_lambda.v
	coqc smart_bdd.v
	coqc bdd_canonical.v
	coqc extraction.v

prof:
	ocamlbuild -I extracted helpers.inferred.mli
	cp _build/helpers.inferred.mli helpers.mli
	ocamlbuild -ocamlopt "ocamloptp -P a" -I extracted -lib unix test.native
	rm helpers.mli
