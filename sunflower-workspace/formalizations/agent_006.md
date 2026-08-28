# Agent 006 — note on the formalization

## Form chosen

Two `sorry`-terminated theorems, statement only:

1. `improved_sunflower_lemma` — existence of an absolute constant `C > 0` such that
   any large-enough family of `k`-sets contains an `r`-petal sunflower.
2. `improved_sunflower_lemma_bound` — the contrapositive "sunflower function"
   phrasing: a sunflower-free family of `k`-sets has cardinality `≤ (C r log k)^k`.

Both carry the same content; the second is included because the task explicitly
mentions the `f(k,r) ≤ (C r log k)^k` phrasing.

## Encoding decisions

- **Set representation.** `Finset α` for individual sets, `W : Finset (Finset α)`
  for the family, with `[DecidableEq α]`. Rationale: everything (cardinality,
  intersection, subfamily) is then computable/finite with no side finiteness
  hypotheses, and `Finset` membership gives distinctness of family members for
  free, so "the `r` sets are distinct" needs no separate statement. `α` is
  universally quantified inside the theorem; small `α` just makes the hypotheses
  unsatisfiable (vacuous), which is harmless for a statement.

- **Sunflower predicate.** Defined locally as `IsSunflower T`:
  `∃ Y, ∀ S₁ ∈ T, ∀ S₂ ∈ T, S₁ ≠ S₂ → S₁ ∩ S₂ = Y`.
  This is the "all pairwise intersections coincide with a core `Y`" formulation,
  matching the task statement verbatim. For `|T| ≥ 2` it implies `Y ⊆ S` for all
  `S ∈ T` and pairwise-disjoint petals `S \ Y`, so it is equivalent to the
  "core + disjoint petals" definition on the nondegenerate range.

- **Number of petals.** `T.card = r` with `T ⊆ W`. Members of a `Finset` are
  distinct, so this is exactly "`r` distinct sets".

- **Petals nonempty?** Not required (classical Erdős–Rado convention). Noted in
  the docstring. If desired one could add `∀ S ∈ T, ¬ S ⊆ Y`.

- **Logarithm.** `Real.log` (natural log). The improved bound is stable under the
  choice of base up to the absolute constant `C`, so any fixed base works; natural
  log is the Mathlib default and needs no `open`. The bound literal
  `(C * r * Real.log k) ^ k` is kept exactly as in the task statement.

- **`k = 0` / `k = 1`.** Excluded by the hypothesis `2 ≤ k`. For `k = 1`,
  `Real.log 1 = 0` collapses the bound to `0`, so the statement would assert that
  any nonempty family of singletons contains an `r`-petal sunflower — false when
  `|W| < r`. `k = 0` is similarly degenerate. Requiring `2 ≤ k` is the minimal
  honest fix that keeps the bound expression verbatim. (Alternative not taken:
  keep `1 ≤ k` and replace `Real.log k` by `max (Real.log k) 1` or
  `Real.log (k+1)`; this rescues `k = 1` but perturbs the literal expression.)

- **`r`.** `1 ≤ r` (positive, per "positive integers `r`"). `r = 1` is
  vacuously true (any single set is a sunflower).

- **Constant `C`.** Existentially quantified *inside* each theorem, together with
  `0 < C`. This is the standard "there is an absolute constant" reading and keeps
  the statement self-contained (no free parameter / hypothesis).

- **Coercions.** `W.card`, `r`, `k` are cast to `ℝ` for the inequality; the
  comparison is `(C * r * Real.log k) ^ k < (W.card : ℝ)` (strict, matching
  "`|W| > (C r log k)^k`").

## Uncertainties

- I am not aware of a sunflower predicate or sunflower lemma in Mathlib as of the
  knowledge cutoff (Mathlib has `Combinatorics/SetFamily/` files for shadows,
  Kruskal–Katona, LYM, Kleitman, Ahlswede–Zhang, but not, to my knowledge,
  sunflowers). Hence `IsSunflower` is defined locally. If a Mathlib definition
  exists it might be named something like `Finset.IsSunflower` /
  `Set.IsSunflower` / `SunflowerFamily`; I did not assume it.

- `import Mathlib` (the whole library) is used for simplicity of a statement-only
  file; a minimal import would be roughly
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` plus `Mathlib.Data.Finset.Card`.

- `Real.log` is applied to the `Nat`→`ℝ` cast `(k : ℝ)`; identifier assumed
  stable.

- The bound orientation follows the task's `|W| > (C r log k)^k`. Rao's and
  Bell–Chueluecha–Warnke's papers sometimes state `log(k)` vs `log(rk)` vs
  `log(k+1)`; I followed the task's `log k` literally.
