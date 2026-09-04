# agent_017 — formalization note

## What is stated

All three, statement-only (`:= by sorry`):

1. `filmus_ihringer_forward` — the forward direction. `∀ d ≥ 1, ∃ m, ∀ k ≥ 2d,
   ∀ n ≥ 2k, ∀ f` Boolean of slice-degree `≤ d`, `f` is an `m`-junta. `m(d)` is an
   existential *inside* the statement, placed before `k` and `n`, so it depends
   only on `d` ("there is a constant `m(d)`").
2. `filmus_ihringer_converse` — the converse. `∀ d ≥ 1, ∀ k` with `1 ≤ k < 2d`,
   `∀ m, ∃ n ≥ 2k, ∃ f` Boolean of slice-degree `≤ d` that is not an `m`-junta.
3. `filmus_ihringer_family` — the explicit witnessing family
   `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`, as `blockProduct`.
   For `ℓ ≥ 1` and `n ≥ 2k`, `n ≥ 2ℓe` it asserts the function is Boolean, has
   slice-degree `≤ d`, and is not an `m`-junta for any `m < ℓe`. Taking `ℓ = m+1`
   recovers theorem 2.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Coordinate
  set `{1,…,n}` is `Fin n`. `Finset` (not `Sym`/`Set`) so `∩ J` and `card` are
  directly available.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a predicate
  `IsBooleanValued f : ∀ S, f S = 0 ∨ f S = 1`. Chosen (over `Bool`/`Fin 2`) so
  the same `ℝ`-valued `f` can be compared to a polynomial without a cast.
- **Degree ≤ d**: `HasSliceDegreeAtMost d f` = `∃ p : MvPolynomial (Fin n) ℝ`
  with `p.totalDegree ≤ d` and `f S = MvPolynomial.eval (indicatorVec S.1) p` for
  every slice point. `indicatorVec S i = if i ∈ S then 1 else 0`. Multilinearity
  is not imposed (irrelevant on the cube); "agrees on the slice" is exactly the
  paper's notion.
- **m-junta**: `IsJunta m f` = `∃ J, J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J →
  f S = f T` — value depends only on `S ∩ J`.
- **Explicit family indexing**: `block n e i = {t : Fin n | i·e ≤ t < i·e + e}` as
  a `Finset (Fin n)` via `Finset.univ.filter`; `blockProduct n k e ℓ S =
  ∏ i ∈ range ℓ, ∑ t ∈ block n e i, indicatorVec S.1 t`. Using block *sets*
  avoids constructing `Fin n` elements with inline `i·e + j < n` proofs in a
  statement. `n`, `k`, `d`, `e`, `ℓ` are all explicit `ℕ` arguments; the ambient
  coordinate set is `Fin n`.

## Uncertainties / judgement calls

- The source says the witnesses "are not `ℓe`-juntas", yet the value of
  `blockProduct` manifestly depends only on the `ℓe` block coordinates, so it *is*
  an `ℓe`-junta in the literal sense. I read the phrase as "junta arity `≥ ℓe`"
  and encoded the conclusion as `∀ m < ℓe, ¬ IsJunta m (…)`, which is what powers
  the converse. Flagged here in case the intended reading differs.
- Whether the formal product `∏_{i=1}^{ℓ} (linear)` (formal degree `ℓ`) really has
  a degree-`≤ d` representative on the slice is a mathematical claim I did not
  verify; it is asserted via `HasSliceDegreeAtMost d`, faithful to "Boolean
  degree-`d` function".
- Mathlib identifiers used, believed current: `MvPolynomial.eval`,
  `MvPolynomial.totalDegree`, `Finset.univ.filter`, `Finset.range`, `∏ … ∈ …`
  (`open scoped BigOperators`). `open scoped BigOperators` may emit a deprecation
  warning on very recent Mathlib but should still resolve.
- `n ≥ 2k` is added as an extra hypothesis in `filmus_ihringer_family` (on top of
  `n ≥ 2ℓe`) to keep the slice nonempty for all admissible `k`; the source's
  converse phrasing only guarantees `n ≥ 2k`.
