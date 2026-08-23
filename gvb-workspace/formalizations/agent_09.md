# Agent 09 — Gilbert–Varshamov bound

**Form chosen:** the classical combinatorial/existential counting bound (form
given first in the prompt), not the rate-distance asymptotic form or the
linear-code/dimension form. Concretely: given alphabet size `q ≥ 2`, block
length `n > 0`, target minimum distance `1 ≤ d ≤ n`, and a codeword count
`M > 0` satisfying `M * (∑_{i=0}^{d-2} C(n-1,i) (q-1)^i) < q^n`, there exists a
code (a `Finset` of codewords) of size exactly `M` in which every two distinct
codewords have Hamming distance at least `d`.

**Encoding choices.** The alphabet is `Fin q` and a codeword is a function
`Fin n → Fin q`; the whole codeword space is `Fin n → Fin q`, which is a
`Fintype` of cardinality `q^n` and has decidable equality (needed for
`Finset (Fin n → Fin q)`). A code is a `Finset (Fin n → Fin q)`. Rather than
invoking a Mathlib Hamming-distance function (unsure of the exact name/API,
e.g. `hammingDist`), I spelled "differ in at least `d` coordinates" out
explicitly and precisely as
`d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card`. The sum
`∑_{i=0}^{d-2} C(n-1,i)(q-1)^i` is written as
`∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i`, since
`Finset.range (d-1)` enumerates `0, …, d-2` and matching this to natural
number subtraction is safe given the hypothesis `1 ≤ d`.

**Simplifications/uncertainties.** No proof is supplied (`:= by sorry`). I am
fairly confident in `Nat.choose`, `Finset.range`, `Finset.filter`, and
`Finset.univ` usage, but slightly less sure whether the ambient
`Fintype`/`DecidableEq` instances for `Fin n → Fin q` resolve automatically
without extra imports beyond `import Mathlib`; I assumed the umbrella import
suffices.
