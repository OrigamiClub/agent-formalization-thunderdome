# Agent 048 — formalization note

## What is stated

Both directions of Filmus–Ihringer, as two `:= by sorry` theorems:

- `filmus_ihringer_junta_of_degree` — the positive direction: `∃ m(d)` such that for
  `k ≥ 2d`, `n ≥ 2k`, every Boolean degree-`d` slice function is an `m`-junta.
- `filmus_ihringer_not_junta` — the sharpness direction: for `1 ≤ k < 2d` and every `m`
  there is `n ≥ 2k` and a Boolean degree-`d` slice function that is not an `m`-junta.

The explicit witnessing family is **not** included (see "Omissions" below).

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}` — the subtype of
  `Finset (Fin n)` at fixed cardinality. Direct, and makes `S ∩ J` literally a `Finset`
  intersection for the junta definition.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a separate
  `IsBooleanSlice` hypothesis (`∀ S, f S = 0 ∨ f S = 1`). Chosen over `Bool`/`Fin 2`
  because the degree notion needs a real-valued function to compare against a real
  polynomial; keeping one carrier avoids coercions.
- **Degree ≤ d** (`IsSliceDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d` agreeing with `f` at every slice point, evaluated
  (`MvPolynomial.eval`) at the `{0,1}` indicator vector `sliceIndicator S`. This is the
  standard "agrees on the slice with a total-degree-`≤ d` polynomial" definition.
  Multilinearity is not imposed: on `{0,1}` inputs it does not change the class of
  representable functions, and the standard definition quantifies over all polynomials.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and `f S = f T`
  whenever `S ∩ J = T ∩ J`. This is "value depends only on `S ∩ J`".
- **`m(d)`**: an existential *inside* the statement (`∃ m : ℕ, …`) rather than an
  explicit `m : ℕ → ℕ`, matching "there is a constant `m(d)`".
- **`n, k, d` and coordinates**: all carried as universally quantified `ℕ` inside each
  theorem; the ambient coordinate set is `Fin n`. No section variables, so each theorem
  is self-contained.
- Hypotheses transcribed as: `1 ≤ d`, `2 * d ≤ k`, `2 * k ≤ n` (positive direction);
  `1 ≤ d`, `1 ≤ k`, `k < 2 * d`, and the produced `2 * k ≤ n` (converse).

## Omissions / uncertainties

- **Explicit family not formalized.** The one-line description
  `∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})`, `e = min(d,k)`, taken literally as a real
  product of block-sums, is *not* `{0,1}`-valued (a single block-sum ranges over
  `0..e`), and for `ℓ = 1` it is literally a `min(d,k)`-junta — so it cannot be "not an
  `ℓe`-junta". The actual paper's Boolean witness is evidently a function *derived* from
  this product via slice-specific degree-collapse phenomena that the short description
  underdetermines. Rather than formalize a guess that would be false, I stated only the
  clean existential converse, which carries the same mathematical content
  (Boolean ∧ degree `≤ d` ∧ not an `m`-junta).
- **Guessed Mathlib identifiers**: `MvPolynomial.eval`, `MvPolynomial.totalDegree`, and
  the `Finset` intersection notation `∩`. Fairly confident on all three; `eval` is used
  as `MvPolynomial.eval (v : Fin n → ℝ) p`.
- `import Mathlib` (whole library) for safety; the statement uses only `MvPolynomial`,
  `Finset`, `Fin`, and `ℝ`.
