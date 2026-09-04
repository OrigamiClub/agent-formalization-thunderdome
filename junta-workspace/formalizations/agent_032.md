# Agent 032 — note

## What was stated

All three parts, as separate `theorem … := by sorry`:

1. `filmus_ihringer_junta_bound` — forward direction: `∃ m(d)` such that for `k ≥ 2d`,
   `n ≥ 2k`, every Boolean degree-`≤ d` function on the slice is an `m`-junta.
2. `filmus_ihringer_not_junta` — converse in pure existential form: for `1 ≤ k < 2d` and
   every `m`, some `n ≥ 2k` and some Boolean degree-`≤ d` non-`m`-junta exist.
3. `filmus_ihringer_witness` — the explicit family
   `∏_{i}(Σ_j x_{ie+j})` with `e = min d k`, asserting it is Boolean, slice-degree `≤ d`,
   and not an `(ℓe)`-junta once `n ≥ 2ℓe`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset`,
  and `abbrev` so `.1` projections unfold for the elaborator. Coordinate set is `Fin n`,
  carried as an explicit `n`; `k`, `d` explicit naturals.
- **Boolean codomain**: functions are `Slice n k → ℝ` plus a predicate
  `IsBooleanFun f := ∀ x, f x = 0 ∨ f x = 1`. Real-valued was chosen so that "degree via a
  real polynomial" needs no coercion gymnastics.
- **Degree `≤ d`**: `HasSliceDegreeLE d f` = `∃ p : MvPolynomial (Fin n) ℝ`, with
  (a) multilinear — every exponent in every `p.support` monomial is `≤ 1`,
  (b) `p.totalDegree ≤ d`,
  (c) `f x = MvPolynomial.eval (0/1 indicator of x.1) p` for every slice point.
  Being an `∃` over `p`, this is exactly the minimal-degree-representative notion (polynomials
  differing by a multiple of `Σ xᵢ − k` agree on the slice), which is what the theorem needs.
- **`m`-junta**: `IsJunta m f` = `∃ J, J.card ≤ m ∧ ∀ x y, x.1 ∩ J = y.1 ∩ J → f x = f y`.
- **`m(d)`**: existential `∃ m : ℕ` inside the forward theorem, `d` a parameter — matches
  "there is a constant m(d)". Not rendered as an explicit `m : ℕ → ℕ`.
- **Explicit family**: `witnessFun n k e ℓ S = ∏_{i∈range ℓ} (card of S in block i)`, where
  block `i` is the coordinates `x` with `i*e ≤ x.val < i*e + e`. `0`-based indexing; the
  `Fin n` coordinate `i*e+j` is identified with the nat `i*e+j` with no modular wrap (the
  needed range bound `ℓe ≤ n` comes from `hn : 2*(ℓ*e) ≤ n`).

## Uncertainties

- Mathlib identifiers used: `MvPolynomial.totalDegree`, `MvPolynomial.support`,
  `MvPolynomial.eval`, `Finset.filter`, `Finset.range`, `∏ i ∈ s, _` big-operator syntax.
  These are standard; I am fairly confident but had no compiler to check.
- The `filmus_ihringer_witness` statement transcribes the product literally with the only
  side condition `1 ≤ ℓ`. The paper's guarantee that this literal product is genuinely
  `{0,1}`-valued and drops to slice-degree `≤ d` may require an extra constraint linking `ℓ`
  to `k` (e.g. `ℓ ≤ k`, or `ℓ = k`), and the degree drop relies on reduction modulo the
  slice ideal `Σ xᵢ = k`. As written the witness theorem may therefore be slightly stronger
  than what is literally provable; flagged here rather than silently narrowed.
- The bridge from `filmus_ihringer_witness` to `filmus_ihringer_not_junta` uses monotonicity
  of `IsJunta` in `m`; that lemma is not stated.
- Multilinearity is encoded via a support-exponent bound; there is no canonical single
  Mathlib predicate for "multilinear `MvPolynomial`" that I wanted to rely on.
