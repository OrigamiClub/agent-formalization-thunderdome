# agent_042 — improved sunflower lemma, statement only

## Form chosen

Primary theorem `improved_sunflower_lemma`:

```
∃ C : ℝ, 0 < C ∧
  ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
    ∀ W : Finset (Finset α),
      (∀ s ∈ W, s.card = k) →
      (C * r * Real.log k) ^ k < (W.card : ℝ) →
      ∃ S ⊆ W, ∃ core : Finset α, S.card = r ∧ IsSunflower S core
```

A secondary equivalent phrasing `improved_sunflower_lemma_indexed` uses an
indexed family `A : ι → Finset α` over an index finset `T` with `Set.InjOn A T`
for distinctness, to make the "sunflower function `f k r`" reading explicit.

## Encoding decisions and why

- **Set representation.** Sets are `Finset α` over an ambient type `α` with
  `[DecidableEq α]`; the family is `W : Finset (Finset α)`. This gives free
  finiteness and free distinctness of members (a `Finset` has no duplicates),
  and `S ⊆ W` picks out the sub-family. `Finset.card` is used throughout.
  The indexed variant instead states distinctness explicitly via `Set.InjOn`.

- **Sunflower predicate.** Defined locally as
  `IsSunflower petals core := (↑petals : Set (Finset α)).Pairwise (fun s t => s ∩ t = core)`.
  `Set.Pairwise` already quantifies over *distinct* elements, so this is exactly
  "every pairwise intersection equals the core". This deliberately matches
  `Finset.IsSunflower` in `Mathlib.Combinatorics.Sunflower` (see uncertainties);
  it is restated so the file is self-contained and independent of that
  identifier being correct. The core is given explicitly as an existential
  witness `∃ core`.

- **`r` petals.** Captured by `S.card = r` together with `IsSunflower S core`.
  With `r ≥ 1` (the task's "positive integer r"). The nontrivial content is
  `r ≥ 3`; `r = 1, 2` are degenerate but the statement still holds for them.

- **Petals nonempty.** Not stated separately: with `(∀ s ∈ W, s.card = k)` and
  `r ≥ 2`, no petal `s \ core` can be empty (an empty petal would force
  `core = s`, and by equal cardinality every other member would also equal
  `core`, contradicting distinctness). So nonemptiness is automatic and left
  implicit.

- **Logarithm.** `Real.log` (natural logarithm). The base only changes the
  absolute constant `C`, which is existentially quantified, so the choice of
  base is immaterial to the statement's truth; natural log is the Mathlib
  default and the literature's usual convention.

- **Handling small `k`.** Restricted to `2 ≤ k`. For `k = 1`,
  `Real.log 1 = 0`, so `(C r log k)^k = 0` and the bound would claim a sunflower
  whenever `|W| > 0`, which is false (need `|W| ≥ r`). `k ≥ 2` is the range in
  which the improved bound is stated by ALWZ / Rao / Bell–Chueluecha–Warnke, and
  `k = 0, 1` are trivial separately. This is the main deviation from the literal
  "all positive integers k".

- **The constant `C`.** Existentially quantified *inside* the theorem and
  *outside* the quantifiers over `α`, `k`, `r`, `W`, so it is a single absolute
  constant not depending on the ground type or the parameters — the whole point
  of the "improved" lemma. `0 < C` is asserted.

- **Strict inequality.** `(C r log k)^k < |W|` (i.e. `|W| > (C r log k)^k`),
  matching the task's `>`. Coercions: `(r : ℝ)`, `(k : ℝ)` inside `Real.log`,
  and `(W.card : ℝ)` on the right.

## Uncertainties / guessed identifiers

- `Finset.IsSunflower` — I believe Mathlib has this in
  `Mathlib/Combinatorics/Sunflower.lean` with signature
  `IsSunflower (petals : Finset (Finset α)) (core : Finset α) : Prop :=
  (petals : Set (Finset α)).Pairwise fun s t => s ∩ t = core`, plus a classical
  Erdős–Rado bound `Finset.exists_isSunflower` (bound `(r-1)^k * k!`). I did not
  rely on the name: the predicate is redefined locally as `ImprovedSunflower.IsSunflower`.
  The *improved* bound is, to my knowledge, not in Mathlib as of early 2026.

- Interleaving `∀ (α : Type*) [DecidableEq α] (k r : ℕ), …` (instance binder
  inside a `∀`) is valid Lean 4 syntax and used in Mathlib; if a checker
  dislikes it, moving `α` and `[DecidableEq α]` to `variable`s (with `C` then
  possibly depending on `α`) is the fallback.

- `import Mathlib` is used for brevity; the minimal imports would be the
  `Finset`, `Set.Pairwise`, and `Real.log` files.

- No claim that this equals any particular `f k r` definition in Mathlib; the
  "sunflower function" reading is conveyed by the indexed variant.
