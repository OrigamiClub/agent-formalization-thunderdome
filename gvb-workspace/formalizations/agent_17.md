# Gilbert–Varshamov bound — agent_17

**Form chosen:** the primary combinatorial/existential form given in the background — a direct existence claim for a code, not the rate-distance asymptotic form or the linear/dimension-`k` form. This is the most literal and Mathlib-friendly rendering of the classical statement.

**Encoding choices:**
- Codewords are modeled as functions `Fin n → Fin q` (length-`n` sequences over an alphabet of size `q`), and a code is a `Finset (Fin n → Fin q)`; this type is automatically a `Fintype` with decidable equality since `Fin n` and `Fin q` are.
- Hamming distance is not invoked as a named Mathlib lemma/definition (I was unsure of the exact canonical name, e.g. `hammingDist`, in the currently available Mathlib) and is instead written out inline as `(Finset.univ.filter (fun i => x i ≠ y i)).card`, i.e. the number of coordinates where two codewords differ. This avoids dependence on an uncertain identifier while remaining precise.
- The sum `∑_{i=0}^{d-2} C(n-1,i)(q-1)^i` is encoded as `∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i`, since `Finset.range (d - 1)` ranges over `{0, ..., d-2}` for `d ≥ 1`, and correctly degenerates to the empty sum (`0`) when `d = 1`.
- All quantities (`q, n, d, M`) are natural numbers with hypotheses `2 ≤ q`, `0 < n`, `1 ≤ d ≤ n`, `0 < M` matching the stated preconditions, plus the strict inequality hypothesis `hbound`.
- The conclusion asserts existence of `C : Finset (Fin n → Fin q)` with `C.card = M` and pairwise Hamming distance `≥ d` for all distinct pairs of codewords in `C`.

No identifiers I was seriously unsure about remain in the final statement, since I inlined the Hamming-distance notion rather than guessing a Mathlib name for it; `Nat.choose`, `Finset.range`, `Finset.univ.filter`, and `Finset.card` are all standard and I'm confident in their names/signatures.
