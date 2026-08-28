# agent_034 — improved sunflower lemma, statement only

## Form chosen

A single primary theorem `Agent034.improved_sunflower_lemma`, stated with an
**existentially quantified absolute constant `C`**, plus two supporting
definitions and one optional corollary phrased via an abstract sunflower
function `f`. Everything ends in `:= by sorry`; nothing is proved.

## Encoding decisions

- **Set representation.** `Finset (Finset α)` over an ambient
  `α : Type*` with `[DecidableEq α]`. Reasons: the "family" is genuinely finite
  and its cardinality is compared to a bound, so `Finset` is natural; using a
  `Finset` for the family makes distinctness of members automatic (no separate
  `Set.InjOn` / pairwise-`≠` hypothesis needed), and likewise the sunflower
  subfamily `T : Finset (Finset α)` with `T.card = r` directly encodes
  "`r` distinct petals".

- **Sunflower predicate.** Custom `IsSunflower T Y`:
  `∀ s ∈ T, ∀ t ∈ T, s ≠ t → s ∩ t = Y`. This is the "all pairwise
  intersections coincide (with an explicit core `Y`)" formulation. The stated
  equivalent properties (element in ≥ 2 sets ⇒ in all; petals pairwise
  disjoint) follow from this and are noted in the docstring, not imposed.
  `HasSunflower W r := ∃ T ⊆ W, ∃ Y, T.card = r ∧ IsSunflower T Y`.

- **Petal nonemptiness.** Not imposed. When all members of `T` have equal
  cardinality and `2 ≤ T.card`, `s ∩ t = Y` forces `Y ⊊ s`, so each petal
  `s \ Y` is automatically nonempty. Keeping the definition minimal avoids a
  redundant hypothesis.

- **Distinctness of members.** Free from the `Finset` encoding (both for `W` and
  for the sunflower subfamily `T`), so not stated explicitly.

- **Uniform cardinality.** `∀ s ∈ W, s.card = k` (exact size `k`), via
  `Finset.card`.

- **Logarithm.** `Real.log` (natural log). The classical statement writes
  `(C r log k)^k`; I use `Real.log ((k:ℝ) + 1)` instead. Rationale: at `k = 1`,
  `log k = 0` makes the bound `0`, and `|W| > 0` does **not** guarantee an
  `r`-petal sunflower (need `≥ r` distinct singletons). Shifting to `k + 1`
  keeps the argument `≥ 2 > 1`, so the bound is positive and, with `C` chosen
  large, `≥ r` at `k = 1`, making the statement true for every positive `k`.
  For `k ≥ 2`, `log(k+1) ≤ 2 log k`, so with an existential absolute constant
  the shifted form is equivalent to the textbook form. The choice of natural log
  vs `log_2` vs `Nat.log` is immaterial for the same absorb-into-`C` reason.

- **Range of `k`, `r`.** Hypotheses `1 ≤ k` and `1 ≤ r` ("all positive
  integers"). `k = 0` (empty sets) is excluded.

- **The constant `C`.** `∃ C : ℝ, 0 < C ∧ …` — the honest rendering of "there is
  an absolute constant". Not a free variable, not a hypothesis.

- **Cardinality comparison.** `Finset.card`, cast to `ℝ`; strict inequality
  `(C * r * Real.log (k+1))^k < (W.card : ℝ)` matching "`|W| > …`".

- **Exponent `^k`.** Natural-number power of a real base (`Monoid.npow`), base is
  nonnegative here.

## Corollary (`improved_sunflower_bound`)

Because Mathlib has no canonical "sunflower function", the `f(k,r) ≤ (C r log k)^k`
form is given by taking `f : ℕ → ℕ → ℕ` together with its defining threshold
property as hypotheses, then concluding the bound on `f`. This is a faithful
restatement modulo that abstraction.

## Uncertainties

- **Mathlib overlap.** I believe Mathlib contains the *classical* sunflower
  lemma and possibly a sunflower predicate (plausibly around
  `Mathlib/Combinatorics/SetFamily/…`, a name like `Finset.IsSunflower` or
  `Set.IsSunflower`). I did not rely on it and defined my own predicate inside
  `namespace Agent034` to avoid any name clash under `import Mathlib`. The
  *improved* bound is definitely not in Mathlib.
- **`Real.log` argument coercion.** Wrote `Real.log ((k : ℝ) + 1)`; the exact
  elaboration of `k + 1` vs `(k : ℝ) + 1` is the only spot I could not check
  against a compiler. Semantics are unambiguous.
- **Universe / binder placement.** `∀ {α : Type*} [DecidableEq α] …` appears
  under `∃ C, 0 < C ∧ …`. This is a well-formed `Prop`; not compiler-checked.
- `import Mathlib` used for convenience; a minimal import set would be
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` plus `Mathlib.Data.Finset.*`.
