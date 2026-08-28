# agent_024 — improved sunflower lemma (statement only)

## Form chosen

A single existential theorem: `∃ C : ℝ, 0 < C ∧ ∀ ...`. The constant `C` is
existentially bound at the very outside, before the quantifier over the ambient
type `α`, so one absolute constant serves every set system.

The "threshold implies sunflower" form is used (rather than the numeric
`f(k,r) ≤ ...` form) because it does not require introducing the sunflower
function; the two are equivalent and the docstring records the equivalence.

## Encoding decisions

- **Set representation.** `W : Finset (Finset α)` over an arbitrary
  `[DecidableEq α]`. Finiteness of the family and of each member is then free,
  and distinctness of members is automatic (`Finset` has no duplicates).
- **"Sunflower".** Defined locally, for self-containedness:
  - `IsSunflowerWith petals core` : `∀ S T ∈ petals, S ≠ T → S ∩ T = core`
    (explicit core; the "all pairwise intersections coincide" phrasing).
  - `HasSunflower W r` : `∃ petals ⊆ W, ∃ core, petals.card = r ∧ IsSunflowerWith petals core`.
  I did not require petals to be nonempty, nor `core ⊂ S`, nor `2 ≤ r`; these are
  standard non-degeneracy add-ons that do not make the statement false. The
  problem's parenthetical facts (petals pairwise disjoint; an element in ≥2 sets
  is in all) are consequences of the intersection condition, so they are not
  stated.
- **Cardinality.** `Finset.card`. Members have card *exactly* `k`
  (`∀ S ∈ W, S.card = k`).
- **Logarithm.** `Real.log` (natural log). Bound compared in `ℝ` after casting
  `W.card`, `r`, `k`.
- **k = 0 / k = 1.** Handled by using `Real.log (k + 1)` instead of `Real.log k`.
  This weakens the bound only by an absolute-constant factor, is a form that
  appears in the literature variants, is true at `k = 1` (with plain `log k` the
  RHS would be `0` and the implication false, since size-1 sets need `|W| ≥ r`,
  not `|W| > 0`), and is vacuous at `k = 0`. Positivity hypotheses `0 < k`,
  `0 < r` are still included to match "positive integers `k` and `r`".
- **C.** Existentially quantified inside the theorem (not a hypothesis, not a
  named constant), matching "there is an absolute constant `C`".

## Uncertainties

- Mathlib already has `Mathlib/Combinatorics/SetFamily/Sunflower.lean` with, I
  believe, predicates along the lines of `Finset.SunflowerWith` /
  `Finset.Sunflower` and the classical Erdős–Rado bound
  (`Finset.exists_sunflower`, bound `k ! * (r - 1) ^ k`). I did **not** rely on
  those identifiers (names/argument order uncertain) and defined my own
  predicates instead. A reviewer may prefer to `rw` these onto the Mathlib API.
- `import Mathlib` (the umbrella import) is used for convenience; only
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` (for `Real.log`) and the
  `Finset` core are actually needed.
- The bound exponent/shape (`(C * r * log (k+1))^k`) follows the statement given;
  I have not verified the constant-factor bookkeeping of the `k+1` shift against
  a specific paper's constant.
