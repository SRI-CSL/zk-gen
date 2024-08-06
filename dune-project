(lang dune 3.14)

(name zk-gen)

(generate_opam_files true)

(source
 (github SRI-CSL/zk-gen))

(authors "Vitor Pereira and Stéphane Graham-Lengrand")

(maintainers "Vitor Pereira <vitor.pereira@sri.com>")

(license "MIT License")

; (documentation https://url/to/documentation)

(package
 (name zk-gen)
 (synopsis "ZKgen: an OCaml platform for zero knowledge computations")
 (description "ZKgen is a ZK platform that aggregates multiple ZK protocols into a single solution, giving the user the flexibility to chose which ZK protocol best fit its application scenario. It supports the evaluation of ZK relations written in SIEVE IR format.")
 (depends ocaml dune evocrypt wiztoolkit timer domainslib yojson str tracing)
 )

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
