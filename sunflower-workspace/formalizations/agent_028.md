# Agent 028 — note on the formalization

## Form chosen

A single `theorem improved_sunflower_lemma : ∃ C : ℝ, 0 < C ∧ ∀ ... := by sorry`,
plus two auxiliary definitions (`IsSunflower`, `ContainsSunflower`).

## Encoding decisions

- **Set representation.** Sets are `Finset α` over an arbitrary ambient type
  `α` with `[DecidableEq α]` (needed for `∩` and `card`). The family is
  `W : Finset (Finset α)`. This is the lightest faithful encoding: finiteness of
  `W` and of each member is automatic, and distinctness of members is automatic.
- **Sunflower predicate.** Defined explicitly:
  `P.card = r ∧ ∀ S₁ ∈ P, ∀ S₂ ∈ P, S₁ ≠ S₂ → S₁ ∩ S₂ = Y`.
  Explicit core `Y`. Equivalent to
  `(P : Set _).Pairwise (fun S₁ S₂ => S₁ ∩ S₂ = Y)`. I chose the spelled-out
  form for transparency in a statement-only deliverable. "Contains a sunflower"
  is `∃ P ⊆ W, ∃ Y, IsSunflower r Y P`.
- **`r` petals = `r` distinct members.** Captured by `P.card = r` together with
  `P : Finset _`. No separate distinctness hypothesis needed.
- **Petals nonempty?** Not required (standard convention). The improved lemma
  does not need it.
- **Constant `C`.** Existentially quantified *before* the quantification over
  `α, k, r, W`, so it is a single absolute constant, with `0 < C`.
- **Logarithm.** `Real.log` (natural log). Base is irrelevant — absorbed into
  `C`. Bound written exactly as `(C * r * Real.log k) ^ k` with `^ k` the
  natural-number power on `ℝ`. Compared against `(W.card : ℝ)` with strict `<`
  (matching `|W| > (C r log k)^k`).
- **Edge cases `k = 0, 1`.** Excluded via hypothesis `2 ≤ k`. Reason: `k = 1`
  gives `Real.log 1 = 0`, so the displayed bound is `0` and the statement would
  claim every nonempty family of singletons of size `≥ 1` contains a sunflower
  with `r` petals, which fails when `|W| < r`. Standard references state the
  improved bound for `k ≥ 2` (or write `log(k)` with an implicit `k` large, or
  use `1 + log k`). Restricting to `k ≥ 2` keeps the bound literally as given.
- **`r`.** Hypothesis `0 < r` ("positive integer"). For `r = 1` the pairwise
  condition is vacuous and `Y` is unconstrained; this degeneracy is harmless.
- **Cardinality.** `Finset.card` throughout.

## Uncertainties

- Mathlib is believed to contain a sunflower file
  (`Mathlib.Combinatorics.SetFamily.Sunflower`) with a predicate along the lines
  of `Finset.IsSunflower (r : ℕ) (t : Finset α) (𝒮 : Finset (Finset α))` (the
  classical Erdős–Rado bound is formalized there). I did **not** rely on it:
  argument order and whether it uses `Set.Pairwise` are uncertain, and the
  *improved* bound is not in Mathlib. My local `Agent028.IsSunflower` is
  self-contained and namespaced to avoid any clash.
- `import Mathlib` (blanket import) is used for safety since no compiler is
  available. `Real.log`, `Finset.card`, `Finset.inter`, and the `ℕ → ℝ` / `ℕ`
  power coercions are all standard and should resolve.
- Binding `∀ (α : Type*) [DecidableEq α] ...` inside the statement (after the
  existential for `C`) is valid Lean 4; the instance is picked up when applying
  `ContainsSunflower`.
