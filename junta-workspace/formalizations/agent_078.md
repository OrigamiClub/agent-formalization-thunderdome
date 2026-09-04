# Agent 078 — formalization note

## What is stated

All three, statement-only (`:= by sorry`, no proofs):

1. `junta_of_boolean_degree` — the junta / upper-bound direction: `∀ d ≥ 1, ∃ M, …`
   with `M` quantified right after `d` so it depends only on `d` (this is the
   `m(d)` of the theorem). Then `k ≥ 2d`, `n ≥ 2k`, and every Boolean
   degree-`d` function on the slice is an `M`-junta.
2. `not_junta_of_boolean_degree` — the converse / lower-bound direction with an
   **existential** witness: for `1 ≤ k < 2d` and every `m`, some `n ≥ 2k` and some
   Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta.
3. `blockFun_not_junta` — the converse with the **explicit family** from the prompt.

## Encoding decisions

- **Ground set / slice.** `Slice n k := {S : Finset ℕ // S ⊆ Finset.range n ∧ S.card = k}`.
  I use `ℕ` (restricted to `range n`) rather than `Fin n` so that
  `MvPolynomial ℕ ℝ` variables can be addressed by raw arithmetic
  (`i * e + j`) with no `Fin` coercions or `NeZero`/bound side-goals in the
  definitions of the explicit family.
- **Boolean codomain.** Real-valued functions `Slice n k → ℝ` together with a
  predicate `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1`. Real-valued is convenient
  because "degree" is defined by comparison with a real polynomial.
- **Degree ≤ d.** `HasSliceDegreeLE f d`: there exists `p : MvPolynomial ℕ ℝ`
  with `p.totalDegree ≤ d`, `∀ i, p.degreeOf i ≤ 1` (multilinear), and
  `∀ S, f S = eval (indicatorVec S) p`. This is the "agrees on the slice with a
  multilinear polynomial of total degree ≤ d" definition. The multilinearity
  conjunct is stated for faithfulness; it does not change the function class and
  could be removed.
- **m-junta.** `IsJunta f m`: `∃ J : Finset ℕ, J.card ≤ m ∧ ∀ S T, S ∩ J = T ∩ J → f S = f T`.
  `J` is not required to lie in `range n` (harmless / WLOG).
- **`m(d)`.** Existential inside the statement (`∃ M : ℕ`), placed after `d` and
  before `k, n, f`, so the "constant depends only on `d`" content is captured.
- **`n, k, d`.** Plain `ℕ` hypotheses; inequalities as `2 * d ≤ k`, `2 * k ≤ n`,
  `k < 2 * d`, `1 ≤ d`, `1 ≤ k`.
- **Explicit family.** `blockSumPoly e ℓ := ∏_{i<ℓ} ∑_{j<e} X (i*e+j)` — the `ℓ`
  disjoint blocks of `e` consecutive variables, `e = min d k`. The prompt's
  literal `∏(Σ x_j)` is integer- (not `{0,1}`-) valued on the slice, so I take
  the **Boolean function it witnesses** to be the support indicator of that
  product: `blockFun n k e ℓ S = if eval (indicatorVec S) (blockSumPoly e ℓ) = 0 then 0 else 1`
  (equivalently: `S` meets all `ℓ` blocks). `blockFun_not_junta` then asserts, for
  `e = min d k`, `ℓ ≥ 1`, `n ≥ 2ℓe`, `n ≥ 2k`: `IsBoolean`, `HasSliceDegreeLE _ d`,
  and `¬ IsJunta _ (ℓ*e)`. Large `ℓ` beats any `m`.

## Uncertainties

- Mathlib identifiers assumed to exist with these signatures:
  `MvPolynomial.eval`, `MvPolynomial.totalDegree`, `MvPolynomial.degreeOf`
  (`σ → MvPolynomial σ R → ℕ`), `MvPolynomial.X`. `degreeOf` is the least certain;
  dropping the multilinearity conjunct removes the dependency.
- `if … = 0` on `ℝ` relies on the classical `DecidableEq ℝ` instance; `blockFun`
  is marked `noncomputable` accordingly.
- Interpretation of the explicit family: I read "Boolean function witnessed by
  `∏(Σx)`" as the nonzero-support indicator, since the raw product is not
  `{0,1}`-valued (e.g. `ℓ = 1`, `e ≥ 2` gives values `0..e`). The intended
  construction in Filmus–Ihringer may instead be a parity / exact-hitting variant
  of the same blocks; the degree claim (slice-degree `≤ d = ` collapses far below
  the naive product degree `ℓ`) is the paper's content and is left to `sorry`.
- The `blockFun_not_junta` conclusion includes `IsBoolean` and
  `HasSliceDegreeLE _ d` as genuine claims (not hypotheses); if my reading of the
  witness is off, that theorem's statement could be false. The first two theorems
  do not depend on the explicit family and are the safe core.
