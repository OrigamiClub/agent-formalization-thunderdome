# Agent 033 — note on the formalization

## Form chosen

Two `theorem ... := by sorry` statements in namespace `ImprovedSunflower`, plus one
auxiliary definition `ContainsSunflower`.

- `improved_sunflower_lemma`: the "counting" form — a large enough family of
  `k`-sets contains a sunflower with `r` petals.
- `improved_sunflower_lemma_bound`: the contrapositive / "sunflower function" form —
  any sunflower-free family of `k`-sets has size `≤ (C r log k)^k`.

Both assert `∃ C : ℝ, 0 < C ∧ ...` with `C` a single absolute constant placed
outside all other quantifiers (type `α`, `k`, `r`, `W`).

## Encoding decisions and why

| Choice | Decision | Reason |
| --- | --- | --- |
| Set representation | `Finset α` over an arbitrary `[DecidableEq α]`; family is `W : Finset (Finset α)` | Standard Mathlib idiom for set families (`Mathlib.Combinatorics.SetFamily.*`); avoids finiteness side-hypotheses. `α` is left arbitrary so families of every size are expressible. |
| Cardinality | `Finset.card` throughout, cast to `ℝ` only where compared to the real bound | Everything is genuinely finite. |
| "Sunflower with `r` petals" | self-defined `ContainsSunflower r W` : `∃ P ⊆ W, ∃ Y, P.card = r ∧ ∀ distinct s t ∈ P, s ∩ t = Y` | "All pairwise intersections coincide" is the crispest core-free phrasing. It implies the usual formulation: for `|P| ≥ 2` it forces `Y ⊆ s` for each `s ∈ P`, and `x ∈ (s\Y) ∩ (t\Y)` would give `x ∈ s ∩ t = Y`, so petals are automatically pairwise disjoint. With equal positive cardinalities and `r ≥ 2` the petals are also automatically nonempty (equal-card distinct sets can't be nested), so no nonemptiness hypothesis is added. |
| Distinctness of the `r` petals | not stated explicitly | Automatic: the petals are the elements of a `Finset P` with `P.card = r`. |
| Logarithm | `Real.log` (natural log) of `(k : ℝ)` | The base only rescales the constant, and `C` is existential, so the choice is immaterial. `Real.log` is a stable Mathlib identifier. |
| `k = 1`, `k = 0` | excluded via hypothesis `2 ≤ k` | `Real.log 1 = 0` collapses the RHS to `0`, and `|W| > 0` does not imply `|W| ≥ r`, so the `k = 1` instance of the literal `(C r log k)^k` bound is not true as stated; `k = 0` forces `W ⊆ {∅}`. The refined bound in the literature is the standard statement exactly for `k ≥ 2`. The task explicitly delegates this handling. |
| `r` | hypothesis `1 ≤ r` ("positive integers `r`") | Matches the theorem statement; `r = 1` is trivially true. |
| `C` | existentially quantified inside the theorem, with `0 < C` | Matches "there is an absolute constant `C`"; keeps the statement self-contained (no free parameter). |
| Comparison | `(C * r * Real.log k) ^ k < (W.card : ℝ)` (strict), exponent `k : ℕ` | Faithful to `|W| > (C r log k)^k`. |

## Uncertainties

- **Mathlib sunflower predicate.** Mathlib has
  `Mathlib.Combinatorics.SetFamily.Sunflower` (Erdős–Rado). I believe it defines a
  predicate along the lines of
  `Finset.IsSunflower (petals : ℕ) (core : Finset α) (𝒮 : Finset (Finset α))` or an
  unbundled `(𝒮 : Set (Finset α)).PairwiseDisjoint (· \ core)` with
  `∀ s ∈ 𝒮, core ⊆ s`, but I am not certain of the exact name, argument order, or
  whether the petal count is a field. To avoid depending on a signature I cannot
  check, I defined `ContainsSunflower` myself. A reviewer with a compiler may wish
  to replace it with the library predicate (e.g. `∃ Y, Finset.IsSunflower r Y P`).
- **`import Mathlib`** is used for convenience; the only real dependencies are
  `Finset` basics and `Real.log`
  (`Mathlib.Analysis.SpecialFunctions.Log.Basic`).
- The instance binder `[DecidableEq α]` appearing mid-`∀`-telescope after explicit
  `k r : ℕ` is accepted by Lean 4 / Mathlib, but the ordering is slightly unusual;
  an alternative is to fix `variable {α} [DecidableEq α]` and universally close over
  `α` outside the `∃ C` (which would let `C` depend on `α` unless `α` is quantified
  inside — hence the chosen in-telescope form).
- Whether to prefer the "counting" form or the "sunflower function ≤" form is a
  matter of taste; both are given.
