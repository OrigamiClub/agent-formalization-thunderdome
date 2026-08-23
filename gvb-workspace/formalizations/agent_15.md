# Agent 15: Gilbert–Varshamov bound

**Form chosen:** the combinatorial/existential form (the first form given in the prompt), stated directly as a code-existence claim rather than the linear-code/dimension form or the asymptotic rate-distance form. This is the most literal, "raw counting" statement of GVB and avoids needing a finite-field structure or an asymptotic limit.

**Encoding.** The alphabet of size `q` is modeled as the type `Fin q`; a codeword of length `n` is a function `Fin n → Fin q`; a code is a `Finset (Fin n → Fin q)`. Hamming distance uses Mathlib's `hammingDist` (from `Mathlib.InformationTheory.Hamming`), which for Pi-types with decidable-equality fibers counts the coordinates where two functions disagree — exactly the standard Hamming distance, so no inline redefinition was needed.

**Hypotheses.** `q ≥ 2`, `n > 0`, `1 ≤ d ≤ n`, `M > 0`, and the Gilbert–Varshamov inequality `M * (∑_{i=0}^{d-2} C(n-1,i)*(q-1)^i) < q^n`, encoded as `M * (∑ i ∈ Finset.range (d-1), (n-1).choose i * (q-1)^i) < q^n` — `Finset.range (d-1)` ranges over `i = 0, …, d-2`, matching the sum's upper index exactly since `d ≥ 1` makes the natural-number subtraction well-behaved.

**Conclusion.** There exists a `Finset C` of codewords with `C.card = M` such that every two *distinct* codewords in `C` have Hamming distance at least `d`.

**Uncertainty notes.** I was not 100% certain of the exact Mathlib name/location of `hammingDist` (I believe it lives in `Mathlib.InformationTheory.Hamming` and has signature `(∀ i, β i) → (∀ i, β i) → ℕ` given `Fintype ι` and `DecidableEq (β i)` for each `i`), but it matched the intended semantics closely enough that I used it directly rather than an inline `Finset.filter`/`card` definition. I imported the whole `Mathlib` library for simplicity since no compiler was available to check more targeted imports. The proof is left as `sorry` as instructed.
