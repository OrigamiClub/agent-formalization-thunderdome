# Gilbert–Varshamov bound — agent 14

**Chosen form:** the classical *combinatorial/existential* version stated directly
in terms of a target code size `M` (not the "M = q^k linear code" variant, and
not the asymptotic rate-distance entropy form). This is the most literal
translation of the bound as given: given `q, n, d, M` satisfying the numeric
inequality `M * (∑_{i=0}^{d-2} C(n-1,i) (q-1)^i) < q^n`, there exists a set of
exactly `M` codewords, pairwise Hamming distance `≥ d`.

**Encoding choices:**
- Codewords are functions `Fin n → Fin q` (length-`n` strings over an
  alphabet of size `q`), and a code is a `Finset` of such functions (finite,
  so `.card` gives its size directly as `M`).
- Rather than guessing the exact Mathlib name/API for Hamming distance
  (e.g. `hammingDist`, which lives under the `Hamming` type synonym in
  `Mathlib.InformationTheory.Hamming` and I wasn't fully confident about its
  exact signature/argument order), I defined "differ in at least `d`
  coordinates" inline as `d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card`,
  i.e. the cardinality of the set of disagreeing coordinates — this is
  definitionally the Hamming distance and avoids any risk of a
  wrong/nonexistent identifier.
- The sum `∑_{i=0}^{d-2} C(n-1,i)(q-1)^i` is written as
  `∑ i ∈ Finset.range (d - 1), (n-1).choose i * (q-1)^i`, since
  `Finset.range (d-1) = {0, ..., d-2}` for `d ≥ 1`, matching the upper limit
  `d-2` in the natural-language statement.
- Hypotheses `2 ≤ q`, `0 < n`, `1 ≤ d ≤ n`, `0 < M` mirror the stated
  preconditions on the parameters. No proof is attempted (`:= by sorry`).

**Uncertain identifiers:** none used directly beyond core `Finset`/`Nat`
API (`Finset.range`, `Finset.filter`, `Finset.univ`, `Nat.choose` via dot
notation, `Finset.card`), which are standard and stable in Mathlib.
