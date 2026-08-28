# Agent 078 — note on the formalization

## Form chosen

Statement-only Lean 4 / Mathlib file. Two theorems, both `:= by sorry`:

1. `Agent078.improved_sunflower_lemma` — the primary statement: an absolute
   constant `C > 0` such that any finite family of `k`-sets larger than
   `(C · r · log k)^k` contains an `r`-petal sunflower.
2. `Agent078.improved_sunflower_bound` — an "equivalent" packaging in terms of a
   sunflower function `f k r`, showing `f k r ≤ (C r log k)^k`. This is a
   convenience restatement; its hypotheses (`hf`, `hmin`) characterise `f k r` as
   the least valid threshold. Included only because the task text mentions the
   `f(k,r)` phrasing; the first theorem is the canonical one.

## Encoding decisions

- **Set representation.** `Finset (Finset α)` over an arbitrary ambient type `α`
  with `[DecidableEq α]`. This keeps everything finite without carrying explicit
  finiteness hypotheses, and `∩` on `Finset` is available. The ambient `α` is
  re-quantified inside the `∃ C` so the constant is genuinely universal over all
  types.
- **Cardinality.** `Finset.card` throughout, both for "each set has size `k`"
  (`∀ s ∈ W, s.card = k`) and for the family size `W.card`.
- **Sunflower predicate.** Defined locally as
  `IsSunflowerWith (r : ℕ) (core : Finset α) (P : Finset (Finset α))` :=
  `P.card = r ∧ ∀ s ∈ P, ∀ t ∈ P, s ≠ t → s ∩ t = core`.
  I used the explicit-core "pairwise intersections all equal `core`" form. The
  core `core` is existentially quantified in the theorem alongside `P`.
- **Distinctness of the `r` sets.** Free: members of a `Finset (Finset α)` are
  distinct, and `P.card = r` fixes the petal count at exactly `r`.
- **Petals nonempty?** Not required (matches the standard statement; `r = 1` and
  degenerate cores are allowed).
- **Which logarithm.** `Real.log` (natural log). The literature's constant `C`
  absorbs the base, so the choice is immaterial to the statement's truth; natural
  log is the Mathlib default and needs no extra `open`.
- **`k = 0, 1` handling.** Assumed `2 ≤ k`. For `k ≤ 1`, `Real.log k ≤ 0` and the
  `(C r log k)^k` expression degenerates / the statement becomes false as written
  (e.g. `k = 1`, `W = {{a}}`: `|W| = 1 > 0` but no 2-petal sunflower). Standard
  treatments state the bound for `k ≥ 2` and dispatch `k ≤ 1` separately. An
  alternative encoding keeping all positive `k` would replace `Real.log k` by
  `max (Real.log k) 1` or `Real.log k + 1`; I kept the literal `log k` form and
  restricted `k`.
- **`r`.** Assumed `1 ≤ r` ("positive integers r"). `r = 1` gives a degenerate
  (single-set) sunflower, which the predicate admits.
- **Constant `C`.** Existentially quantified inside the theorem (`∃ C : ℝ, 0 < C ∧
  …`), so the file is self-contained and there is no free parameter.
- **Comparison.** Done in `ℝ`: `((C * r * Real.log k) ^ k) < (W.card : ℝ)`, i.e.
  strict `|W| > bound`, with `k`, `r`, `W.card` coerced from `ℕ`.

## Uncertainties

- Mathlib does contain a sunflower development (roughly
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean`) with a predicate along the
  lines of `Finset.IsSunflower` / `Set.Pairwise (· ∩ · = core)` and the classical
  Erdős–Rado bound. I did **not** rely on it: I could not verify the exact
  identifier, argument order, or whether it fixes a petal count, so I defined
  `IsSunflowerWith` locally. If the Mathlib predicate is
  `Finset.IsSunflower 𝒮 core` meaning pairwise intersections equal `core`, then
  `IsSunflowerWith r core P ↔ P.card = r ∧ Finset.IsSunflower P core` (modulo the
  exact spelling).
- The improved sunflower lemma itself is (to my knowledge) not in Mathlib, so no
  existing theorem name was targeted.
- `import Mathlib` (the whole library) is used for simplicity in a
  statement-only file; a minimal import set would be
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` plus the `Finset` combinatorics
  files.
- `improved_sunflower_bound` is my own reformulation; its `hmin` hypothesis (that
  `f k r` is the *least* working threshold) is one plausible way to make "`f` is
  the sunflower function" precise, not a canonical Mathlib notion.
