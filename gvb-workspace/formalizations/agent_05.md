# Gilbert–Varshamov bound — agent_05

**Form chosen:** the classical combinatorial/existential (non-asymptotic, non-linear) form directly
from the prompt: given alphabet size `q ≥ 2`, length `n ≥ 1`, minimum distance target `1 ≤ d ≤ n`,
and a positive integer `M` such that `M * (∑_{i=0}^{d-2} C(n-1,i) (q-1)^i) < q^n`, there exists a
code (arbitrary, not necessarily linear) of exactly `M` codewords over an alphabet of size `q` and
length `n` with pairwise Hamming distance at least `d`.

**Encoding choices:** Codewords are modeled as `Fin n → Fin q` and a code as a `Finset (Fin n → Fin
q)`; the size condition is `C.card = M`. Hamming distance uses Mathlib's `hammingDist` (from
`Mathlib.InformationTheory.Hamming`), which counts differing coordinates via
`Finset.filter`/`Finset.card` under the hood, so no ad hoc distance definition was needed. The sum
`∑_{i=0}^{d-2} C(n-1,i)(q-1)^i` is written as `∑ i ∈ Finset.range (d - 1), (n-1).choose i * (q-1)^i`;
since `Finset.range (d-1)` is `{0, …, d-2}`, this correctly reduces to the empty sum (value `0`) when
`d = 1`, matching the usual convention for that edge case. All arithmetic is kept in `ℕ` since every
quantity involved (choose, powers, cardinalities) is a natural number, avoiding any need for casts.

**Uncertain identifiers:** `hammingDist` — I'm fairly confident this is the correct Mathlib name
(in `Mathlib.InformationTheory.Hamming`, stated for `∀ i, β i` with `DecidableEq` on each fiber,
which specializes to `Fin n → Fin q`), but I could not compile-check it. `Nat.choose` is accessed via
the standard dot-notation `(n - 1).choose i`.

**Not proved:** the theorem body is `sorry`, as requested; only the statement is formalized.
