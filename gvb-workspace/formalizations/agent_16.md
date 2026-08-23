# Gilbert–Varshamov bound — agent_16 notes

I chose the **combinatorial/existential form** (the primary form given in the prompt), rather
than the linear-code/dimension form or the asymptotic rate-distance form: given `q ≥ 2`,
`n ≥ 1`, `1 ≤ d ≤ n`, and a positive integer `M` satisfying
`M * (∑_{i=0}^{d-2} C(n-1,i)(q-1)^i) < q^n`, there exists a code `C ⊆ (Fin n → Fin q)` with
`|C| = M` and pairwise Hamming distance at least `d`.

Codewords are modeled as functions `Fin n → Fin q` (a finite alphabet `Fin q` indexed by
positions `Fin n`), so the ambient space is exactly the `Fintype` of cardinality `q^n`
mentioned in the informal statement. I did **not** use Mathlib's `hammingDist`/`Hamming` type
synonym (from `Mathlib.InformationTheory.Hamming`) since I wasn't fully confident of its exact
API for this Pi-type setting; instead I defined the "differ in at least `d` coordinates"
condition inline as `(Finset.univ.filter (fun i => x i ≠ y i)).card`, which is definitionally
the Hamming distance and avoids relying on an unverified identifier name.

The sum `∑_{i=0}^{d-2} C(n-1,i)(q-1)^i` is encoded as
`∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i`, using natural-number
subtraction `d - 1`, which is correct since `Finset.range (d-1) = {0, ..., d-2}` matches the
intended upper limit `d - 2` when `d ≥ 1`. All arithmetic (`q - 1`, `n - 1`, `d - 1`) uses `ℕ`
truncated subtraction, which is safe given the hypotheses `2 ≤ q`, `0 < n`, `1 ≤ d`. The proof
body is `sorry` as instructed; the only identifiers I was mildly unsure about are the exact
`Finset.filter`/`Finset.univ` decidability instance resolution for `Fin n → Fin q` (should be
automatic via `DecidableEq (Fin q)`) and whether Mathlib prefers `Nat.choose` vs. `n.choose`
notation (both should work).
