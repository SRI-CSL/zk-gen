# ZK-gen proof systems based on polynomial commitment schemes.
This library constitutes one of [the two main parts of the `zk-gen` platform](../README.md).

In this first prototype of the library, we implemented a recently published polynomial commitment scheme and plugged it into the Marlin protocol. The library includes the following components:   

1. **FRI**: FRI is a standalone library implementing the Interactive Oracle Proof of Proximity (IOPP) described in [Fast Reed-Solomon Interactive Oracle Proofs of Proximity](https://www.semanticscholar.org/paper/Fast-Reed-Solomon-Interactive-Oracle-Proofs-of-Ben-Sasson-Bentov/2415603b4e8799f575b788706be21862c055e25b).
2. **VLPA19** VLPA19 is an implementation of the polynomial commitment scheme desribed in [Transparent Polynomial Commitment Schemes with Polylogarithmic Complexity](https://eprint.iacr.org/2019/1020.pdf). It uses FRI as a black-box.  
3. **zk-interace / Marlin Integration** This is a frontend that reads in an R1CS zkif file from zkinterface, and runs Marlin on it using VP19

More details about these components can be found in [software_overview.md](software_overview.md).


### Testing with cargo:
Make sure you  have exactly one version of `rustc` installed on your computer. Run `rustup install stable`. Then: 

- `fri`: Navigate to `zk-gen/fri` and run `cargo test`

- `vlpa19`: Navigate to `zk-gen/vlpa19` and run `cargo test --lib vlpa19`

- `zkinterace-marlin`: Navigate to `zk-gen/zkinterface-marlin` and run `cargo test`.  
 
### Proving and verifying a statement from an R1CS instance using zkinterface. 
1. Ensure you have an R1CS instance, witness, and relation. 
2. Navigate to `verifier_setup` and run `cargo run -- {instance} {relation}`. This will create a file called `srs`. Do `cp srs ../prover`
3. Navigate to `prover` and run `cargo run -- {instance} {relation} {witness} {key} {proof}`. This will create two files, `key` and `proof`. Do `cp key ../verifier` and `cp proof ../verifier`.  
4. Navigate to `verifier` and run `cargo run -- {instance} {relation} {key} {proof} {output}`. This will create a file called `output` that contains a `1` if the proof was accepted and a `0` otherwise.






 
