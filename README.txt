Implementing hash-consed structures in Coq
==========================================

This is a public git repository associated with our submission to JAR. The Coq development and the OCaml handlers have been tested with Coq 8.4pl2 and OCaml 4.01. 

Description. 
============

pure/ contains two "pure" implementations of BDDs in Coq, and one implementation of reduction of hash-consed lambda-terms. 

smart/ contains the "smart" implementation of BDD in Coq, and one implementation of reduction of hash-consed lambda-terms. 

bdd-reference/ contains the reference implementation of BDDs by Filliâtre, that we use in our benchmarks

bench_bdd.{ml,v} corresponds to the frontend we used in our benchmarks. In order to generate the extracted code, please do "mkdir extracted; coqc bench_bdd.v". This will compile and extract the pure-deep, pure-shallow and smart implementations. 

script.ml contains the driver we used to to run our benchmarks. Execute it using "ocaml script.ml"


