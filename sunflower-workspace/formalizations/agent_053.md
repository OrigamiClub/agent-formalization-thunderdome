# Agent 053 — improved sunflower lemma, statement only

## Form chosen

Two `theorem ... := by sorry` statements in `namespace ImprovedSunflower`, plus two auxiliary
`def`s.

- `improved_sunflower_lemma` — the family form: `∃ C : ℝ, 0 < C ∧ ∀ k r, 0 < k → 0 < r → ∀ α
  [DecidableEq α] (W : Finset (Finset α)), (∀ S ∈ W, S.card = k) → (C·r·max (log k) 1)^k <
  |W| → ContainsSunflower W r`.
- `improved_sunflower_lemma_function` — the equivalent statement about the sunflower function
  `f k r ≤ (C·r·max (log k) 1)^k`. `f` is not defined in Mathlib, so I pass it abstractly with
  hypotheses saying it is the least threshold with the covering property (an "upper bound" and a
  "minimality" clause). This is essentially a corollary of the first theorem and is included only
  because the task mentions the "equivalently" phrasing.

## Auxiliary definitions

- `IsSunflower (r : ℕ) (petals : Finset (Finset α)) : Prop` :=
  `petals.card = r ∧ ∃ core, (petals : Set (Finset α)).Pairwise (fun S T => S ∩ T = core)`.
  I bundle the core as an existential inside the predicate (the task lists this as an allowed
  choice). `Set.Pairwise` quantifies over *distinct* members, matching "`S_i ∩ S_j = Y` for
  every `i ≠ j`".
- `ContainsSunflower (W : Finset (Finset α)) (r : ℕ) : Prop` := `∃ petals ⊆ W, IsSunflower r
  petals`.

## Encoding decisions and rationale

- **Set representation:** `Finset α` over an ambient `[DecidableEq α]` type; family is
  `Finset (Finset α)`. Keeps everything finite and decidable, `∩` and `card` are the plain
  `Finset` operations, and "finite family" is literal. Distinctness of members is free.
- **`C` absolute:** `∃ C` is placed *outside* the `∀ α`, so `C` cannot depend on the ambient
  type, on `k`, or on `r`. Required `0 < C`. Existential (not a hypothesis / named constant)
  because "there is an absolute constant" is the faithful reading and gives one closed
  proposition.
- **Logarithm:** `Real.log` (natural log). The exact base only changes `C`.
- **`k = 1` / `k = 0`:** `k` is required positive (`0 < k`). For `k = 1`, `Real.log 1 = 0`
  makes `(C·r·log k)^k = 0`, so the literal bound would be vacuous and the statement false.
  I use `max (Real.log k) 1` in the base: for `k ≥ 2` this is `Real.log k` up to enlarging the
  absolute constant, and for `k = 1` it makes the bound `C·r`, under which the statement is true
  (more than `C·r` singletons give `r` disjoint ones for `C ≥ 1`). This preserves the "for all
  positive integers `k`" wording. An alternative would have been to add `2 ≤ k`; I preferred not
  to weaken the range.
- **Comparison in `ℝ`:** RHS `|W|` is cast to `ℝ`; strict `<` matches "`|W| > (…)^k`".
- **Cardinality:** `Finset.card` throughout (`S.card = k`, `W.card`).
- **Petals:** not required nonempty (matches the usual Erdős–Rado Δ-system convention and lets
  at most one degenerate petal `S = core` occur).
- **`r`:** required positive (`0 < r`); for `r ≥ 2` the core is forced.

## Uncertainties

- **Mathlib already has a sunflower file.** I believe it is
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean`, defining a predicate along the lines of
  `Finset.IsSunflower (r : ℕ) (core : Finset α) (𝒮 : Finset (Finset α))` and proving the
  *classical* bound (`(r-1)^k · k! < |𝒮|`), e.g. `Finset.exists_sunflower`. I did **not** rely
  on it: the exact identifier names, argument order, and whether the core is an explicit argument
  vs. existential are unverified from memory, and the improved bound is not in Mathlib. My
  self-contained `IsSunflower` should be interchangeable with the library one up to moving the
  `core` in/out of the predicate.
- `Set.Pairwise` is assumed to mean `∀ x ∈ s, ∀ y ∈ s, x ≠ y → r x y` (excludes equal pairs) —
  standard, but stated from memory.
- Coercion insertion (`(r : ℝ)`, `Real.log (k : ℝ)`, `(W.card : ℝ)`) written explicitly to
  avoid elaboration ambiguity; not compiler-checked.
- `import Mathlib` used for convenience; a minimal import set is not determined.
- In `improved_sunflower_lemma_function`, the abstract characterization of `f` via an upper
  bound + minimality clause is my own scaffolding, not a standard Mathlib object.
