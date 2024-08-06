# ZKgen: an OCaml platform for zero knowledge computations

ZKgen is a ZK platform that aggregates multiple ZK protocols into a single solution, giving the user the flexibility to chose which ZK protocol best fit its application scenario. 
It supports the evaluation of ZK relations written in SIEVE IR format.

## Usage

ZKgen provides two binaries: `zk-gen-prover` and `zk-gen-verifier`. We next provide instructions on how to use both of them.

Inside ZKgen, a ZK protocol always starts with the **verifier**. It needs to be invoked together with the following command line arguments:

- `--backend` - sets the ZK backend to be used
- `--cores` - sets the number of parallel cores to be used
- `--relation` - relation file, in the SIEVE IR format
- `--instance` - instance file, in the SIEVE IR format
- `--port` - the port where the verifier will be listening to

Next the **prover** is called with the following arguments:

- `--backend` - sets the ZK backend to be used
- `--cores` - sets the number of parallel cores to be used
- `--relation` - relation file, in the SIEVE IR format
- `--instance` - instance file, in the SIEVE IR format
- `--witness` - witness file, in the SIEVE IR format
- `--verip` - the verifier IP
- `--verport` - the port where the verifier is listening to

For example, the evaluation of a ZK statement using ZKgen can be done by running

```
$> zk-gen-verifier --backend lpzk --cores 8 --relation relation.txt --instance instance.txt --port 12345
```

which will boot a ZKgen verifier that will use the LPZK protocol as the ZK backend, will use 8 parallel cores to speed up the evaluation and will be listening in port 12345. The verifier will be in a idle state, waiting for the prover to start, which can be done via

```
$> zk-gen-prover --backend lpzk --cores 8 --relation relation.txt --instance instance.txt --witness witness.txt --verip 73.227.130.85 --verport 12345
```

Additional instructions on how to correctly invoke both of them can be found by typing

```
$> zk-gen-prover --help
```

or 

```
$> zk-gen-verifer --help
```

respectively. However, we summarize usage instructions in this

## Supported ZK backends 

So far, we support the following ZK protocols:
- MPC-in-the-Head, using BGW as the underlying MPC protocol, which can be used with backend argument `mith-bgw`
- Line-Point Zero Knowledge (LPZK), assuming pre-computed correlated randomness, which can be used with backend argument `lpzk`

## Instalation requirements

ZKgen uses the following third-party tools/libraries:
- OCaml (>= 4.14.0) - available at [https://ocaml.org/](https://ocaml.org/)
- Dune (>= 3.14) - available at [https://github.com/ocaml/dune](https://github.com/ocaml/dune)
- EVOCrypt - available at [https://github.com/SRI-CSL/evocrypt](https://github.com/SRI-CSL/evocrypt)
- Wiztoolkit OCaml bindings - available at [https://github.com/SRI-CSL/wiztoolkit_ocaml](https://github.com/SRI-CSL/wiztoolkit_ocaml)
- Timer - available at [https://github.com/disteph/timer](https://github.com/disteph/timer)
- Domainslib - available at [https://github.com/ocaml-multicore/domainslib](https://github.com/ocaml-multicore/domainslib)
- Yojson - available at [https://github.com/ocaml-community/yojson](https://github.com/ocaml-community/yojson)

We recommend installing the above dependencies using `opam`. However, they can be installed by cloning the corresponding repository and manually installing the tool/library.

After installing `OCaml` and `opam`, typing

```
$> opam install dune domainslib yojson
$> opam pin git+https://github.com/SRI-CSL/evocrypt.git#main
$> opam pin git+https://github.com/SRI-CSL/wiztoolkit-ocaml-bindings.git#main
$> opam pin git+https://github.com/disteph/timer.git#main
```

installs all ZKgen required dependencies

## Installing/Compiling EVOCrypt

If installing from source, running

```
$> make
$> make install
```

builds and install ZKGen (with corresponding binaries named `zk-gen-prover` and `zk-gen-verifier`) assuming that all dependencies have been successfully installed. 

ZKgen can also be installed via `opam`, by running

```
$> opam pin git+https://github.com/SRI-CSL/zk-gen.git#main
```

which installs ZKgen and its dependencies via `opam`.

## Examples

Examples of how to use ZKgen can be found in the `test` directory.

## Acknowledgments

This material is based upon work supported by DARPA under Contract No. HR001120C0086. Any opinions, findings and conclusions or recommendations expressed in this material are those the author(s) and do not necessarily reflect the views of the United States Government or DARPA.

Distribution Statement ‘A’ (Approved for Public Release, Distribution Unlimited)
