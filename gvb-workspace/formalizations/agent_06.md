# Gilbert–Varshamov bound — agent_06

**Form chosen:** the direct combinatorial/existential form (option given first in the
background, not the linear-code/dimension form, not the asymptotic rate-distance form).
Given alphabet size `q ≥ 2`, block length `n ≥ 1`, target minimum distance `1 ≤ d ≤ n`,
and a positive integer `M` with `M * (∑_{i=0}^{d-2} C(n-1,i) * (q-1)^i) < q^n`, the
theorem asserts existence of a `Finset` `C` of codewords with `|C| = M` in which every
two distinct codewords have Hamming distance at least `d`.

**Encoding choices.** The alphabet is `Fin q`; codewords are functions `Fin n → Fin q`;
a code is a `Finset (Fin n → Fin q)`. The sum `∑_{i=0}^{d-2} ...` is written as
`∑ i ∈ Finset.range (d - 1), ...`, since `Finset.range (d-1) = {0, ..., d-2}` gives
exactly `d-1` terms matching the natural-language upper limit `d-2`. Hamming distance
is written using `hammingDist`, which I believe comes from
`Mathlib.InformationTheory.Hamming` and is defined (modulo the `Hamming` type-synonym
wrapper) as the cardinality of the filter of coordinates where two functions disagree;
I was not 100% sure of the exact current name/API (it may require unwrapping via
`Hamming.toHamming`/`ofHamming`, or need `DecidableEq` instances that are automatically
inferred here since `Fin q` and `Fin n` are finite with decidable equality). If it
doesn't typecheck as written, the same quantity is easily written inline as
`(Finset.univ.filter (fun i => x i ≠ y i)).card`. No proof is attempted (`:= by sorry`).
