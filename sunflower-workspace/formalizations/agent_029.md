# Agent 029 — Improved sunflower lemma, statement-only formalization

## Form chosen

A single `theorem improved_sunflower_lemma : <prop> := by sorry`, preceded by two
self-contained auxiliary definitions (`ImprovedSunflower.IsSunflower`,
`ImprovedSunflower.HasSunflower`). No proof is attempted. Only `import Mathlib`
is required.

## Encoding decisions and rationale

- **Set representation.** Sets are `Finset α` over an ambient type `α` with
  `[DecidableEq α]`; the family `W` is a `Finset (Finset α)`. This gives
  finiteness of `W` for free, makes the members of `W` automatically distinct,
  and makes `A ∩ B` and `Finset.card` directly available. An indexed family
  would have forced an explicit injectivity/distinctness hypothesis; `Set` with a
  `Set.Finite` hypothesis would have added bookkeeping with no gain.

- **"Sunflower with `r` petals".** Defined via an explicit core:
  `IsSunflower T Y := ∀ A ∈ T, ∀ B ∈ T, A ≠ B → A ∩ B = Y`
  ("all pairwise intersections coincide", with the common value named `Y`), and
  `HasSunflower W r := ∃ T ⊆ W, T.card = r ∧ ∃ Y, IsSunflower T Y`.
  The `A ≠ B` guard is what makes a family of size `r` a genuine `r`-petal
  sunflower; distinctness of the `r` petals comes from `T : Finset _` with
  `T.card = r`, so it need not be stated separately.

- **Petals nonempty / core proper.** Not imposed. The classical and improved
  sunflower lemmas do not need it, and for `k`-sets with `r ≥ 2` it follows
  anyway (`Y ⊊ A`, `|A| = k`). Keeping the predicate minimal is closer to the
  standard "pairwise intersections equal" definition.

- **The constant `C`.** Existentially quantified at the front, with `0 < C`,
  matching "there is an absolute constant `C`". `C` does not depend on `α`, `k`,
  `r`, or `W`. The type variable `α` is quantified *inside* the `∃ C` so that a
  single `C` works across all ambient types.

- **Which logarithm.** `Real.log` (natural log). The base is irrelevant because a
  base change multiplies the bound by a constant that is absorbed into `C`.

- **`k = 1` and `k = 0`.** `k = 0` is ruled out by the hypothesis `0 < k`
  (sets of size 0 are all `∅`, so `|W| ≤ 1` and no `r ≥ 2` sunflower can exist;
  the implication would still be vacuously fine, but excluding it is cleaner).
  For `k = 1` and `k = 2`, `Real.log k < 1`, and the literal bound
  `(C r log k)^k` would be too weak / degenerate. The factor used is therefore
  `max 1 (Real.log k)`. For `k ≥ 3` this is exactly `Real.log k`, so the
  statement carries the full strength of the ALWZ / Rao / Bell–Chueluecha–Warnke
  theorem; for `k ∈ {1, 2}` it becomes a finite base case that any sufficiently
  large absolute `C` satisfies. The existential-`C` phrasing makes the
  `max`-regularized statement equivalent to "the literal bound holds for all
  `k ≥ 3`", which is the real content.

- **Cardinality.** `Finset.card` throughout (`W.card`, `T.card`, `A.card`),
  coerced to `ℝ` only for the size inequality `(W.card : ℝ) > (…)^k`.

- **Inequality direction.** Stated as `|W| > (C r log k)^k` to mirror the problem
  statement's phrasing verbatim.

## Uncertainties

- **Mathlib's own sunflower API.** I believe Mathlib has
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean` containing a predicate along
  the lines of `Finset.IsSunflower` and the classical Erdős–Rado bound
  (`(t-1)^r * r!`-style), but I am not certain of the exact identifier or
  signature (petal count as an argument vs. derived; `Set` vs. `Finset` of
  finsets; core as explicit argument). I did **not** rely on it and instead gave
  a local definition, since (a) it keeps the file self-contained and (b) the
  *improved* (polylog) bound is, to my knowledge, not in Mathlib, so no
  ready-made statement exists to reuse. If the Mathlib predicate does exist with
  a compatible shape, `ImprovedSunflower.IsSunflower` could be replaced by it.

- **Syntax points I could not machine-check** (no Lean compiler available):
  - an instance-implicit binder `[DecidableEq α]` in the middle of a `∀`
    telescope that itself sits under `∃ C : ℝ, 0 < C ∧ …` (expected to
    elaborate, making the theorem universe-polymorphic in `α`);
  - the `∃ T ⊆ W, …` bounded-existential binder notation (standard in Mathlib);
  - coercions `((k : ℝ))`, `((r : ℝ))`, `((W.card : ℝ))` and that
    `max 1 (Real.log (k : ℝ))` forces `1 : ℝ`.
  These are all routine, but flagged since they are unverified.
