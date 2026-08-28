# agent_016 — improved sunflower lemma (statement)

## Form chosen

A single existential-constant theorem:

```
∃ C : ℝ, 0 < C ∧
  ∀ {α} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
    2 ≤ k → 1 ≤ r →
    (∀ s ∈ W, s.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ S ⊆ W, S.card = r ∧ ∃ Y : Finset α, IsSunflower S Y
```

## Encoding decisions and why

- **Set representation:** `Finset α` over an arbitrary ambient type `α` with
  `[DecidableEq α]`, and the family as `W : Finset (Finset α)`. This keeps
  everything finite with no side finiteness hypotheses, and `Finset.card` /
  `Finset.inter` are directly available. `α` is universe-polymorphic
  (`Type*`) and bound after `C` so that `C` is genuinely absolute.

- **Sunflower predicate:** defined locally as
  `IsSunflower S Y := ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → s₁ ∩ s₂ = Y`
  ("all pairwise intersections coincide", with an explicit named core `Y`).
  I made it self-contained rather than relying on a Mathlib identifier
  (see uncertainties). "Sunflower with `r` petals" is then
  `S.card = r ∧ ∃ Y, IsSunflower S Y`.

- **Number of petals / distinctness:** `S ⊆ W` with `S.card = r`. Members of a
  `Finset` are automatically distinct, so `S.card = r` already encodes "r
  distinct sets"; no separate distinctness clause is needed. For `r ≥ 2` the
  definition forces `Y ⊆ s` for every `s ∈ S`, and the petals `s \ Y` are
  pairwise disjoint, matching the informal statement.

- **Petals nonempty:** not required. The classical statement does not demand
  proper containment of the core; leaving it out makes the theorem (slightly)
  stronger and matches Erdős–Rado / ALWZ conventions.

- **Logarithm:** `Real.log` (natural log). Since the constant `C` is absolute,
  the choice of base only rescales `C`, so natural log is the least-committal
  choice. The cardinality inequality is stated in `ℝ` with `Nat.cast` on
  `r`, `k`, and `W.card`; `Real.log (k : ℝ)` is the intended reading of
  `log k`.

- **Edge cases `k = 0, 1`:** handled by requiring `2 ≤ k`. For `k = 1`,
  `Real.log 1 = 0`, so the bound degenerates to `0 < |W|`, and
  "`|W| ≥ 1 ⟹ r-sunflower among singletons" is false (one needs `r` distinct
  singletons). For `k = 0` the family is at most `{∅}`. Both are trivial/known
  and standardly excluded; the ALWZ/Rao/BCW bound is a statement about `k ≥ 2`.
  `r ≥ 1` is imposed as "positive integer `r`".

- **`C` existential vs hypothesis:** existentially quantified *inside* the
  theorem, with `0 < C`, so the statement is a closed proposition asserting the
  existence of an absolute constant (the "`f(k,r) ≤ (C r log k)^k`" reading).

## Uncertainties

- **Mathlib sunflower API:** Mathlib contains a formalization of the classical
  (Erdős–Rado) sunflower lemma. I believe the relevant names are around
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean` with something like
  `Finset.IsSunflower` / `IsSunflower` (a predicate on a `Finset (Finset α)`
  with an explicit core) and a lemma such as
  `Finset.exists_sunflower` / `IsSunflower.exists_of_...`. I did not want to
  bet the statement on the exact signature, so I defined `IsSunflower` locally.
  If the Mathlib predicate exists with the same shape
  `(Finset (Finset α)) → (Finset α) → Prop`, this local definition can be
  replaced by it verbatim.

- **Binder placement:** `∀ {α : Type*} [DecidableEq α] ...` appearing after the
  numeric/Prop hypotheses inside the existential is syntactically fine in
  Lean 4 Mathlib, but if a checker objects, moving `{α} [DecidableEq α]` to
  just after `0 < C ∧ ∀` (still inside the scope of `C`) is an equivalent
  formulation.

- **Cast form:** I wrote `(C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ)`.
  The exponent `k : ℕ` uses monoid power on `ℝ`, which is the intended meaning.

- **`Real.log` vs a clamped `max 1 (Real.log k)`:** using `max 1 (Real.log k)`
  (or `Real.log k + 1`) would let the statement cover all positive `k` with the
  same "absolute constant" content. I kept the literal `Real.log k` with
  `2 ≤ k` to stay closest to the quoted bound.
