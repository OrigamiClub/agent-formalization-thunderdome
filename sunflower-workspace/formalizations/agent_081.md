# agent_081 — improved sunflower lemma, statement only

## Form chosen

A single `theorem improved_sunflower_lemma : ∃ C : ℝ, 0 < C ∧ ∀ … := by sorry`,
plus two auxiliary `def`s (`IsSunflower`, `HasSunflower`). Self-contained on top
of `import Mathlib`.

## Encoding decisions and why

- **Set representation:** `Finset α` for individual sets, `Finset (Finset α)` for
  the family `W`, with `[DecidableEq α]` on an ambient type `α`. This makes
  `∩`, `card`, and `⊆` all computable/canonical and makes distinctness of family
  members automatic (elements of a `Finset`), so no separate injectivity
  hypothesis is needed. Alternatives (`Set` + finiteness, indexed families) were
  rejected as heavier for a pure statement.

- **Sunflower predicate:** explicit core.
  `IsSunflower P Y := ∀ s ∈ P, ∀ t ∈ P, s ≠ t → s ∩ t = Y`.
  This is the "all pairwise intersections coincide (and equal `Y`)"
  formulation. When `P` has ≥ 2 members it forces `Y ⊆ s` for each `s ∈ P` and
  the petals `s \ Y` to be pairwise disjoint, matching the informal statement,
  so I did not add those as separate conjuncts. I did **not** require petals
  `s \ Y` to be nonempty; with `k` fixed and `Y` a proper subset this is the
  usual situation anyway, and leaving it out keeps the conclusion weaker hence
  the theorem statement stronger.

- **"r petals":** `HasSunflower W r := ∃ P Y, P ⊆ W ∧ P.card = r ∧ IsSunflower P Y`.
  `r` is exactly the number of petals (`P.card = r`, not `r ≤ P.card`), matching
  "a family of `r` distinct sets".

- **Cardinality:** `Finset.card` throughout (`s.card = k`, `P.card = r`,
  `W.card`).

- **The constant `C`:** existentially quantified as the outermost binder,
  *before* the universal quantifier over `α, k, r, W`. Hence it is a true
  absolute constant, independent of everything including the ambient type. An
  explicit `universe u` is declared and `α : Type u` is bound inside the
  existential so that `C` cannot depend on the universe either.

- **Logarithm:** `Real.log (k : ℝ)` (natural log; base is irrelevant since it
  only changes `C`). The size bound is compared in `ℝ`:
  `(C * r * Real.log k) ^ k < (W.card : ℝ)`, a strict inequality as in
  "`|W| > (C r log k)^k`".

- **Small `k`:** restricted to `2 ≤ k`. For `k = 1`, `Real.log 1 = 0` so the RHS
  is `0` and the hypothesis would reduce to `W.Nonempty`, which does not force an
  `r`-petal sunflower for `r ≥ 2`; for `k = 0`, `Real.log 0 = 0` likewise and
  also the "sets of card `0`" family has at most one member. `2 ≤ k` is the
  meaningful range for the bound and is the standard hypothesis in the
  literature (Rao). `r` is kept at `1 ≤ r` ("positive integers"); `r = 1` makes
  the conclusion trivial but true.

## Uncertainties

- I believe Mathlib has a sunflower development in
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean` with a predicate along the
  lines of `Finset.SunflowerWith (𝒜 : Finset (Finset α)) (t : ℕ) (u : Finset α)`
  and a classical Erdős–Rado bound theorem (name possibly
  `Finset.exists_sunflower` / `Finset.Sunflower...`). I did **not** rely on those
  identifiers because I am not certain of their exact names/signatures and could
  not check against a compiler; instead I gave self-contained definitions. If
  `Finset.SunflowerWith` exists with the expected meaning, `IsSunflower P Y`
  here should correspond to its "all distinct pairs meet in `u`" clause (mine
  omits the `t ≤ 𝒜.card` size clause, which I carry separately as `P.card = r`).
- Coercion/`^` elaboration (`(C * (r:ℝ) * Real.log (k:ℝ)) ^ k` with `k : ℕ`) is
  the intended `Monoid.npow`; not compiler-checked.
- `∀ {α : Type u} [DecidableEq α] …` appearing inside a `∃`-body term is, to my
  knowledge, accepted by Lean 4 / Mathlib, but was not verified here.
