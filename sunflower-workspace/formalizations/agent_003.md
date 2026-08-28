# Agent 003 — note on the formalization

## Form chosen

Two `theorem ... := by sorry` statements in namespace `ImprovedSunflower`,
plus two auxiliary `def`s:

- `IsSunflowerCore (𝒮 : Finset (Finset α)) (Y : Finset α) : Prop` — `𝒮` is a
  sunflower with core `Y`.
- `HasSunflower (W : Finset (Finset α)) (r : ℕ) : Prop` — `W` contains a
  sunflower with `r` petals.
- `improved_sunflower_lemma` — the main `|W| > (C r log k)^k ⇒ sunflower` form.
- `improved_sunflower_lemma_function` — the equivalent `f(k,r) ≤ (C r log k)^k`
  form, with `f` and its defining property passed as hypotheses (Mathlib has no
  canonical "sunflower function", so it is abstracted).

## Encoding decisions

**Set representation.** `W : Finset (Finset α)` over an ambient `α` with
`[DecidableEq α]`. This is the most idiomatic Mathlib encoding of "a finite
family of finite sets" and gives `Finset.card`, `∩`, `⊆` directly.
Distinctness of the members of `W` and of a sunflower subfamily `𝒮` is free:
`Finset` membership is by definition without repetition. Hence no explicit
distinctness hypothesis; "`r` distinct sets" is captured by `𝒮.card = r`.

**Sunflower definition.** Explicit core. `IsSunflowerCore 𝒮 Y` asks:
1. `∀ S ∈ 𝒮, Y ⊆ S`, and
2. `∀ S₁ S₂ ∈ 𝒮, S₁ ≠ S₂ → S₁ ∩ S₂ = Y`.

Condition (2) is exactly the prompt's "there is a core `Y` with `Sᵢ ∩ Sⱼ = Y`
for all `i ≠ j`". From (2) alone, whenever `|𝒮| ≥ 2`: any element in two members
lies in `Y`, and `Y = S₁ ∩ S₂ ⊆ every member`, so the classic consequences
(element in ≥ 2 sets is in all; petals `S \ Y` pairwise disjoint) follow.
Condition (1) is therefore redundant for `|𝒮| ≥ 2`; it is included so the
predicate is still meaningful for `|𝒮| ≤ 1` and so "petal = `S \ Y`" is a clean
complement. Petals are **not** required to be nonempty (they are automatically
nonempty here only if members strictly contain `Y`); the improved lemma does not
need that, and demanding it would exclude the degenerate `k = |Y|` situation.

**`r` petals.** `HasSunflower W r` = `∃ 𝒮 ⊆ W, 𝒮.card = r ∧ ∃ Y, IsSunflowerCore 𝒮 Y`.
So "`r` petals" ↔ "`r` members in the sunflower subfamily".

**Logarithm.** `Real.log` (natural logarithm). Any fixed base only rescales the
absolute constant `C`, so the base is immaterial to the statement; `Real.log` is
the lowest-friction choice in Mathlib. The size comparison is done in `ℝ`:
`(C * r * Real.log k) ^ k < (W.card : ℝ)` with `r`, `k`, `W.card` coerced from
`ℕ`, and `^ k` the natural-number power.

**Handling `k = 0, 1`.** Restricted to `2 ≤ k`. For `k = 0` a `k`-uniform family
has at most one member (the empty set), no lemma needed. For `k = 1`,
`Real.log 1 = 0` makes the RHS `0`, so the hypothesis would reduce to
`0 < |W|` and force an `r`-petal sunflower in every nonempty family of
singletons; that statement is actually *true* (any `r` distinct singletons form
a sunflower with core `∅`) but only for `|W| ≥ r`, which `0 < |W|` does not give.
Rather than patch the bound (e.g. `Real.log (k+1)` or `max 1 (Real.log k)`), I
excluded `k ≤ 1`, matching how the ALWZ/Rao/BCW statements are used
asymptotically. `1 ≤ r` is kept as stated ("positive integers").

**The constant `C`.** Existentially quantified as the **outermost** binder
(`∃ C : ℝ, 0 < C ∧ ∀ {α} ... `), with `α, k, r, W` all universally quantified
*inside*. This is the faithful reading of "there is an absolute constant `C`":
one `C` uniform over everything, in particular independent of the ambient type.

**Cardinality.** `Finset.card` throughout (`W.card`, `𝒮.card`, `S.card`).

## Uncertainties / guessed identifiers

- **No Mathlib sunflower API assumed.** To my knowledge Mathlib (early 2026) has
  no sunflower lemma or `Sunflower` predicate (the `Mathlib.Combinatorics.SetFamily.*`
  files cover Kruskal–Katona, LYM, Kleitman, shattering, compressions, etc., but
  not sunflowers). If one exists it might be named `Finset.IsSunflower` /
  `SetFamily.Sunflower` / `IsSunflower`; I defined my own `IsSunflowerCore` to be
  safe. This is the main uncertainty.
- `Real.log` is correct in Mathlib (`Mathlib.Analysis.SpecialFunctions.Log.Basic`).
  `import Mathlib` pulls everything, so no import risk, at the cost of not being
  minimal.
- Binding `∀ {α : Type*} [DecidableEq α]` inside the body of an `∃ C, ...` is
  legal Lean 4 term syntax; I am mildly unsure whether the pretty-printer / an
  elaboration quirk would prefer these hoisted, but it should typecheck.
- Coercion arrows: written as `(r : ℝ)`, `(k : ℝ)`, `(W.card : ℝ)` explicitly to
  avoid ambiguity in `C * r * Real.log k`.
- The second theorem's `hf` hypothesis is a hand-rolled abstraction of "`f` is a
  valid sunflower-threshold function"; there is no standard Mathlib name for it.
