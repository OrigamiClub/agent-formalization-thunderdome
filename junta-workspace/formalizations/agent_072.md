# agent_072 — formalization note

## What I stated

All three pieces, each `:= by sorry`:

1. `boolean_degree_le_isSliceJunta` — the forward direction: `∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k, …`.
2. `exists_boolean_degree_le_not_isSliceJunta` — the converse, existential witness form:
   `1 ≤ k < 2d → ∀ m, ∃ n ≥ 2k, ∃ f, Boolean ∧ degree ≤ d ∧ ¬ m-junta`.
3. `blockProdSlice_isBoolean_degree_le_not_isSliceJunta` — the converse with the explicit
   product family `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`.

## Encoding decisions

- **Slice.** `S : Finset (Fin n)` plus the hypothesis `S.card = k` carried explicitly in
  every definition/quantifier. Chosen over `{S // S.card = k}` / `Sym` because polynomial
  evaluation at the indicator vector stays syntactically clean and Mathlib-native.
- **Boolean codomain.** Functions are `Finset (Fin n) → ℝ`; "Boolean" is
  `∀ S, S.card = k → f S = 0 ∨ f S = 1` (`{0,1} ⊆ ℝ`). Keeps degree and Booleanity in the
  same type; no coercion bookkeeping.
- **Degree ≤ d.** `HasSliceDegreeLE f k d`: existence of `p : MvPolynomial (Fin n) ℝ` with
  `MvPolynomial.totalDegree p ≤ d`, *multilinear* (`∀ i, MvPolynomial.degreeOf i p ≤ 1`,
  included to match "multilinear real polynomial" literally — it does not change which
  functions qualify since evaluation is at 0/1), agreeing with `f` on every size-`k` set
  under `MvPolynomial.eval (indicator S) p`, where `indicator S i = if i ∈ S then 1 else 0`.
- **m-junta.** `IsSliceJunta f k m`: `∃ J, J.card ≤ m ∧ ∀ S T` on the slice,
  `S ∩ J = T ∩ J → f S = f T`. This is the "value depends only on `S ∩ J`" reading.
- **m(d).** Kept as an existential `∃ m : ℕ` *inside* the statement (uniform over `k` and
  `n`), matching "there is a constant m(d)". Alternative not taken: a top-level
  `m : ℕ → ℕ`.
- **n, k, d, coordinates.** All natural numbers; the ambient coordinate set is `Fin n`,
  with `n` an explicit variable of each theorem and size conditions written `2*d ≤ k`,
  `2*k ≤ n`, `2*(ℓ * min d k) ≤ n`.
- **Explicit family.** `blockProdSlice n e ℓ S = ∏_{i∈range ℓ} ∑_{j∈range e}
  [ (i*e+j) ∈ S.map Fin.valEmbedding ]`. Blocks are the consecutive size-`e` intervals of
  coordinates `{0,…,ℓe−1}` (0-indexed image of the paper's `(i−1)e+j`), named in `ℕ` via
  `Fin.valEmbedding` so no in-term `Fin` bound proof is needed. `e := min d k`.
- **"not ℓe-juntas".** Taken as "genuinely depends on all `ℓe` coordinates", formalized as
  `∀ m, m < ℓ * e → ¬ IsSliceJunta … m`. A literal `¬ IsSliceJunta … (ℓ*e)` would be
  vacuously false (the function trivially is an `ℓe`-junta), so I read the phrase as the
  intended strong statement; combined with "`ℓ` arbitrary" it yields non-`m`-junta for
  every `m`.

## Uncertainties

- `Fin.valEmbedding : Fin n ↪ ℕ` — name guessed from memory (alternatives: `Fin.coeEmbedding`,
  `Fin.valEmbedding`); the intent is `S.map` into `Finset ℕ`.
- `MvPolynomial.totalDegree`, `MvPolynomial.degreeOf`, `MvPolynomial.eval` — standard
  Mathlib names, high confidence; exact argument order of `degreeOf`/`eval` written as
  `degreeOf i p` and `eval (indicator S) p`.
- I am not certain the *literal* product `∏ (∑ x_j)` is `{0,1}`-valued on `binom([n],k)`
  for all `S` (a quick case analysis suggests values `≥ 2` can occur unless the paper
  applies a Booleanization step). I formalized the family exactly as the task describes it
  and as a Boolean degree-`d` witness; if the published construction Booleanizes the
  product, theorem (3) would need that adjustment while theorems (1)–(2) are unaffected.
- No Mathlib notion of "Boolean degree-d function on the slice" / "junta" was assumed to
  exist; all four predicates are defined locally.
- Added `n ≥ 2k` (`hn'`) to theorem (3) so the slice is nonempty even for small `ℓ`;
  the paper's stated hypothesis there is only `n ≥ 2ℓe`.
