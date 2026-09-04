# Agent 071 — formalization note

## What I stated

All three pieces, as separate `theorem ... := by sorry` statements:

1. `positive_direction` — the main Filmus–Ihringer result: for `d ≥ 1`, an
   existentially-quantified `M = m(d)` with: `k ≥ 2d`, `n ≥ 2k`, `f` Boolean of
   degree `≤ d` on `binom([n],k)` ⇒ `f` is an `M`-junta.
2. `converse_direction` — for `1 ≤ k < 2d` and every `m`, some `n ≥ 2k` and some
   Boolean degree-`≤ d` function on `binom([n],k)` that is not an `m`-junta.
3. `witness_family` — the explicit witnesses realize the converse: the slice
   function `witnessFn n d k ℓ` induced by
   `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` (`e = min d k`) is Boolean, degree
   `≤ d`, and not an `m`-junta for any `m < ℓ·e`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)` is the lightest representation and makes `S ∩ J` and
  cardinalities directly available. Ambient coordinate set is `Fin n`; `n`, `k`,
  `d`, `ℓ` are all carried as explicit `ℕ` arguments.
- **Boolean codomain**: real-valued `f : Slice n k → ℝ` together with
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Chosen over `Bool`/`Fin 2`/`ZMod 2`
  because the degree notion needs a common ring with the polynomial; keeping `f`
  in `ℝ` avoids coercion bookkeeping in the statement.
- **Degree ≤ d**: `HasDegreeLE` = existence of `P : MvPolynomial (Fin n) ℝ` that
  is multilinear (`IsMultilinear`: every support monomial has all exponents
  `≤ 1`) with `P.totalDegree ≤ d` and `f S = MvPolynomial.eval (indicator S.1) P`
  for all `S`, where `indicator S i = if i ∈ S then 1 else 0`. This is the
  standard "restriction of a low-degree polynomial" definition. I included the
  explicit multilinearity clause because the theorem text says "multilinear";
  it does not change the representable class (squares reduce on the `0/1` cube)
  but keeps the statement faithful.
- **m-junta**: `IsJunta m f` = `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`. Direct transcription of "value depends
  only on `S ∩ J`".
- **m(d)**: existential `∃ M : ℕ` inside `positive_direction`, matching "there is
  a constant m(d)". Not exposed as an explicit `m : ℕ → ℕ`.
- **Explicit family indexing**: `witnessPoly n d k ℓ` sums over `i ∈ range ℓ` a
  product over `j ∈ range (min d k)` of `X ⟨i * min d k + j, _⟩`, i.e. `ℓ`
  consecutive disjoint blocks of size `e = min d k` covering coordinates
  `0 .. ℓ·e - 1` (0-based form of `(i-1)e + j`). Out-of-range indices fall back to
  `0` via `dite`; the hypothesis `2·(ℓ·e) ≤ n` makes that branch vacuous.
  `witness_family` also assumes `k ≤ ℓ·e` (the paper's "ℓ large" regime), which
  also gives `n ≥ 2k`. The non-junta conclusion is phrased as "not an `m`-junta
  for every `m < ℓ·e`"; since `ℓ` is a free parameter this yields non-`m`-juntas
  for every `m`.

## Uncertainties

- **Product vs. sum in the witness family.** The prompt wrote
  `∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})` (product of sums). Taken literally on
  `binom([n],k)` that polynomial is **not** `{0,1}`-valued (e.g. `d = e = 3`,
  `k = 5 < 2d`, `S = {1..5}` gives block sums `3` and `2`, product `6`), and, as
  a polynomial in only the first `ℓ·e` variables, it is trivially an `ℓ·e`-junta,
  contradicting "not `ℓe`-juntas". The **sum of products**
  `Σ_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` fixes both: each monomial has degree
  `e ≤ d`; on the slice it counts fully-covered blocks, and two disjoint full
  blocks would need `2·min(d,k) > k` elements exactly when `k < 2d`, so the value
  lies in `{0,1}`; and every one of the `ℓ·e` coordinates is essential (when
  `n ≥ 2ℓe`), so it is not an `m`-junta for `m < ℓe`. I formalized the
  sum-of-products reading and believe the prompt swapped `∏`/`Σ`.
- **Mathlib identifiers used** (from memory, not compiler-checked):
  `MvPolynomial`, `MvPolynomial.X`, `MvPolynomial.eval`,
  `MvPolynomial.totalDegree`, `MvPolynomial.support`, `Finset.card`,
  `Finset.range`, `Finset` `∩`, `∑ _ ∈ _, _` / `∏ _ ∈ _, _` notation. `Finsupp`
  coercion `m i` for `m : Fin n →₀ ℕ` in `IsMultilinear`. If big-operator
  notation needs it, `open scoped BigOperators` is included.
- I did not verify the side conditions in `witness_family` are exactly minimal
  (e.g. whether `k ≤ ℓ·e` can be dropped); they are sufficient and keep the
  statement true, which is all that matters for a statement-only formalization.
- No claim is made that these `sorry`s are provable from current Mathlib; only
  the statements are intended to be meaningful.
