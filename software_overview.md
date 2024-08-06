## Software Overview

### FRI
`(zk-gen/fri/src/fri.rs)`

The Fri Protocol is expressed as a collection of functions located in `fri/src/fri.rs`. The two entry points are the `prover` function and the `verifier` function. This file also has a number of unit tests. The most important ones are `test_completeness` and `test_soundness` as they directly test the security properties of the IOPP.

FRI works as follows: A prover has a polynomial in mind that they claim has degree less than d, where d is an agreed upon degree bound.

First  (in function `prover`) , the prover evaluates this polynomial over some public domain, producing a Reed-Solomon codeword with rate = 2^(log\_degree\_bound - domain\_size).

Next, (in function `get_next_round`) the prover splits all of the x-coordinates (domain points) into equivalence classes and maps each equivalence class to a y-coordinate (evaluations of domain points) using the function y = q(x) = 2^(2^x). For each equivalence class, the prover interpolates the codeword over the subset of points associated with this equivalence class and the evaluates it as a random field element provided by the verifier. This produces a field element, f. (y,f) becomes a point in the next codeword.

(`collect_rounds`) This process is repeated r times, where r = (log\_domain - rate\_param)/n, 2^(-(rate\_param)) = rate and n is an integer smaller than log\_domain\_size.

Finally, in the terminal round, the interpolates over the entire final codeword and commits to the first d coefficients, where d = rate * last\_round\_domain\_size - 1.

(function `verifier`) The verifier function essentially reproduces and checks the work of the prover. Because the equivalence classes were domain specific and not codeword specific, the verifier samples an x-value from the domain, and finds all other x-values that map to the same y. From there, the verifier can reproduce the provers work.

### Vlpa19
`(zk-gen/vlpa19/src/vlpa19.rs)`.

`Vlpa19` is a polynomial commitment scheme that relies heavily on `FRI`. It works as follows:

`setup`: Setup outputs the `initial_domain`, the `max_degree_bound` and the integer `n` which determines the domain size of each subsequent round in FRI.

`commit`: Takes paramaters from setup and the prover's polynomial and produces a commitment, where the commitment is FRI Proof. Later, the verifier will verify this FRI proof as apart of the verification function.

`open`: The verifier provides the verifier with a random field element that is not in the initial domain and requests that the prover publish the evaluation of the committed polynomial at this point. To do this, the prover will use the challenge and evaluation point to generate a witness polynomial, which is
(F(x) - z) / (x - i) . Then, the prover provides a FRI proof that this witness polynomial is less than the `degree_bound - 1`.

`verify`: The verifier checks that

 1) The proof of the witness polynomial is valid,

 2) The proof of the original polynomial is valid,

 3) That the verifiers querys of the first codeword of the proof of the committed polynomial, match up with the querys of the first codeword of the proof of the witness polynomial.


### Vlpa19_Marlin.
`(zk-gen/vlpa19/src/vlpa19_marlin.rs)`.

Marlin requires a polynomial committment scheme that can support multiple degree bounds and multiple query points. The `Marlin` prover commits to a set of n polynomials, each with it's own individual degree bound. Next, the prover creates a set of m linear combinations of these polynomials. The verifier will request a proof of evaluation for each linear combination and then verify it against its associated group of commitments.

`setup`: public parameters are set

`commit`: The prover produces a `Vlpa19` commitment, which is a FRI proof that a polynomial is less than its degree bound.

`open_combination_individual_opening_challenges`:
Group polynomials into a two dimensional vector according to linear combination so that element (i,j) is the j'th polynomial of linear combination i. For each group of polynomials, call the following:

`open_individual_opening_challenges`compute a new linear combination where coefficient for polynomial i is k^(i), where k is a verifier challenge. Commit to this new polynomial, where the commitment is a FRI proof. In addition to this commitment, output a proof of evaluation at the query point.

`check_combinations_individual_opening_challenges`:
Group commitments into a two dimension vector by linear combination, as was done with the polynomials. Get the proof, evaluation, and query point associated with each linear combination. Then for each (commitments, proof, evaluation, query_point) compute the following:

`check_individual_opening_challenges`: The verifier checks that:

1) The FRI verifier queries of the first codeword of the linear combination matches up with the FRI verifier queries of the first codewords of the individual commitments.

2)Each commitment is indeed a committment to a polynomial of degree less than it's individual degree bound.

3) Let d be the maximum degree bound of all the polynomials in the linear combination. The verifier checks that the commitment corresponds to a polynomial with degree less than d

If all these checks go through, the verifier accepts.

