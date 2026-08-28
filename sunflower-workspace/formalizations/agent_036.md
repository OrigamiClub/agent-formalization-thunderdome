# Agent 036 — improved sunflower lemma (statement only)

## Form chosen

Single theorem `improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (α : Type*) [DecidableEq α] (k r : ℕ),
  2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α), (∀ A ∈ W, A.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ T ⊆ W, T.card = r ∧ ∃ Y, IsSunflower T Y
```

i.e. the "large family contains a sunflower" form rather than an explicit
`f(k,r) ≤ …` bound on a sunflower function (avoids having to define `f`; the two
are equivalent).

## Encoding decisions

- **Set representation.** Sets are `Finset α` over an ambient `α : Type*` with
  `[DecidableEq α]`; the family is `W : Finset (Finset α)`. This gives
  `Finset.card` for all cardinalities and makes "finite family" automatic.
- **Constant `C`.** Existentially quantified *inside* the theorem but *outside*
  the type `α` and all of `k, r, W`, so it is a true absolute constant. Only
  `0 < C` is asserted (no need for `1 ≤ C` in this direction).
- **`α` quantified inside the statement.** Written `∀ (α : Type*) [DecidableEq α]`
  after `∃ C`, so `C` cannot depend on `α`. The theorem is universe-polymorphic
  in `α`.
- **Sunflower predicate.** Defined locally as
  `IsSunflower petals core := (↑petals : Set _).Pairwise (fun A B => A ∩ B = core)`.
  This is the "all pairwise intersections coincide" formulation. `Set.Pairwise`
  only constrains distinct members, matching "for every i ≠ j". Core `Y` is
  existentially quantified in the conclusion. The disjoint-petals / "element in
  ≥ 2 sets is in all" properties are consequences (for `r ≥ 2`) and are not
  separately stated.
- **Number of petals / distinctness.** `T.card = r` with `T : Finset (Finset α)`;
  distinctness of the `r` sets is automatic (Finset members are distinct), so no
  extra hypothesis.
- **Petals nonempty.** Not required in `IsSunflower`; in the theorem each member
  of `W` has card `k ≥ 2`, hence is nonempty anyway.
- **Logarithm.** `Real.log` (natural log). Base is irrelevant since it only
  changes the absolute constant `C`.
- **`k = 0` / `k = 1`.** Excluded via hypothesis `2 ≤ k`. This is the standard
  hypothesis for the improved lemma (Rao states it for `k ≥ 2`): for `k ≤ 1`,
  `Real.log k ≤ 0` and `(C r log k)^k` no longer represents the intended growing
  bound. `r` is required `≥ 1` (a sunflower needs at least one petal; `r = 1` is
  the trivial case).
- **Strict inequality.** `(C r log k)^k < |W|` (matches "|W| > …").
- **Cardinality.** `Finset.card` throughout (`A.card = k`, `W.card`, `T.card`).

## Uncertainties

- I did not run a Lean compiler. Risk points:
  - `∀ (α : Type*) [DecidableEq α] (k r : ℕ), …` as a nested binder inside a term
    (after `∃ C, 0 < C ∧ …`): believed valid Lean 4 (instance-implicit binders in
    `∀`), but this exact nesting is the least-certain syntactic element.
  - `(↑petals : Set (Finset α)).Pairwise …` — relies on the `Finset → Set`
    coercion and `Set.Pairwise` taking the relation as an explicit second arg.
- Mathlib already contains the *classical* Erdős–Rado sunflower lemma (roughly
  `Finset.exists_sunflower` together with a sunflower predicate, in
  `Mathlib.Combinatorics.SetFamily.Sunflower`); exact identifier names not
  verified here. I deliberately defined my own `IsSunflower` to keep the file
  self-contained and unambiguous. The *improved* bound `(C r log k)^k` is, to my
  knowledge, not in Mathlib.
- `import Mathlib` used for brevity; the minimal imports would be the sunflower /
  set-family combinatorics file plus `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
