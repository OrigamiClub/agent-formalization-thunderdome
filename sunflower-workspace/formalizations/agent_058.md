# Agent 058 — improved sunflower lemma, statement only

## Form chosen

A single `theorem improved_sunflower_lemma : ∃ C : ℝ, 0 < C ∧ (∀ ...) := by sorry`,
plus two auxiliary `def`s (`IsSunflower`, `HasSunflowerOfSize`). Everything is in
namespace `ImprovedSunflowerLemma` and imports all of `Mathlib`.

## Encoding decisions

- **Set representation.** `Finset (Finset α)` for an arbitrary `α` with
  `[DecidableEq α]`. Finsets give cardinality directly via `Finset.card` and make
  the "distinct members" requirement automatic (a `Finset` has no duplicates,
  and `P ⊆ W` with `P.card = r` yields exactly `r` distinct sets).

- **Sunflower predicate.** Defined explicitly with a core:
  `IsSunflower P Y := ∀ S₁ ∈ P, ∀ S₂ ∈ P, S₁ ≠ S₂ → S₁ ∩ S₂ = Y`.
  This is the verbatim "there is a core set `Y` with `Sᵢ ∩ Sⱼ = Y` for all `i ≠ j`"
  formulation. I did not add `Y ⊆ S` as a separate clause: for `r ≥ 2` it already
  follows from the pairwise-intersection condition.

- **Petals nonempty?** Not imposed. With all members of size exactly `k` and
  `k ≥ 2`, any two distinct members `S₁ ≠ S₂` with `S₁ ∩ S₂ = Y` have
  `|Y| < k`, so every petal `S \ Y` is nonempty automatically. Imposing it would
  be redundant here.

- **"Contains a sunflower with `r` petals."** `HasSunflowerOfSize W r :=
  ∃ P ⊆ W, P.card = r ∧ ∃ Y, IsSunflower P Y`. The core `Y` is existentially
  quantified (not required to be a member-independent input).

- **Logarithm.** `Real.log` (natural log). The bound is `(C * r * Real.log k) ^ k`
  with `r`, `k` cast to `ℝ`. Any other base (`Real.logb 2`, etc.) only changes
  `C` by a constant factor, and `C` is existential, so the choice is immaterial.

- **`C`.** Existentially quantified *inside* the theorem, bundled with `0 < C`.
  The ambient type `α` and the instance `[DecidableEq α]` are quantified *after*
  the `∃ C`, so `C` is a single absolute constant not allowed to depend on the
  ground set / its size.

- **`k = 0` / `k = 1`.** Handled by the hypothesis `2 ≤ k`. At `k = 1`,
  `Real.log 1 = 0` makes the RHS `(C·r·0)^1 = 0`, so the literal inequality
  `0 < |W|` would not force a sunflower (`f(1, r) = r`). Restricting to `k ≥ 2`
  is the standard convention (e.g. Bell–Chueluecha–Warnke) and loses nothing:
  the `k = 1` case is elementary. `r` is constrained by `1 ≤ r`.
  Alternative encodings that keep all positive `k` honest would use
  `Real.log k + 1`, `max 1 (Real.log k)`, or `Real.logb 2 (k + 1)` in place of
  `Real.log k`; I preferred the plainer `Real.log k` with `2 ≤ k`.

- **Cardinality comparison.** `|W|` is `Finset.card` (a `ℕ`); the inequality is
  stated in `ℝ` as `(...) ^ k < (W.card : ℝ)`.

- **Cardinality of members.** `∀ S ∈ W, S.card = k` — exactly `k`, uniform family.

## Uncertainties / guessed identifiers

- I do **not** believe current Mathlib contains the sunflower lemma or a
  `Finset.IsSunflower` / `Set.IsSunflower` predicate, so I defined my own. If such
  a predicate does exist, it is likely shaped as `(family) (core)` similar to
  mine, and `IsSunflower` here could be replaced by it.
- `Real.log` is a genuine Mathlib identifier (natural logarithm on `ℝ`), as is the
  `∃ P ⊆ W, _` bounded-existential notation. These I am confident about.
- The nested binder `∀ {α : Type*} [DecidableEq α] ...` under an `∃` is valid Lean
  4 / Mathlib syntax; universe generalization of `α` happens at the theorem level.
- Not machine-checked (no Lean compiler available); minor elaboration/coercion
  adjustments may be needed.
