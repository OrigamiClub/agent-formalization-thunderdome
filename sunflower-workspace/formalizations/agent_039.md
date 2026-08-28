# Agent 039 — improved sunflower lemma, statement only

## Form chosen

Primary theorem `Agent039.improved_sunflower_lemma`:

```
∃ C : ℝ, 0 < C ∧
  ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
    2 ≤ k → 1 ≤ r →
    (∀ s ∈ W, s.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ S ⊆ W, ∃ Y : Finset α, S.card = r ∧ IsSunflower S Y
```

A secondary reformulation `improved_sunflower_lemma_function` phrases the same bound
for an abstract "sunflower function" `f : ℕ → ℕ → ℕ` (any `f` with the forcing
property), concluding `f k r ≤ (C r log k)^k`.

## Encoding decisions

- **Set representation.** `Finset α` for individual sets, `Finset (Finset α)` for the
  family `W` and for the sunflower subfamily `S`. Consequences: membership distinctness
  is automatic, the number of petals is just `S.card`, "subfamily" is `S ⊆ W`, and no
  extra finiteness hypotheses are needed. `α` is an arbitrary type carrying
  `DecidableEq` (needed for `Finset.inter`). `α` is universally quantified *after* the
  existential `C`, so `C` does not depend on the ambient type.

- **Sunflower predicate.** Defined locally as
  `IsSunflower S Y := ∀ s ∈ S, ∀ t ∈ S, s ≠ t → s ∩ t = Y`
  (pairwise intersections all equal the core `Y`). For `S.card ≥ 2` this is equivalent
  to the "petals `s \ Y` pairwise disjoint with `Y = ⋂ s`" definition of
  Alweiss–Lovett–Wu–Zhang, and it forces `Y ⊆ s` for every `s ∈ S`. I did not add a
  separate `Y ⊆ s` clause or a nonempty-petals requirement, matching the standard
  combinatorial statement. Number of petals recorded as `S.card = r` (exactly `r`).

- **Constant `C`.** Existentially quantified inside the theorem, with `0 < C`, as the
  most direct reading of "there is an absolute constant `C`". Placed outermost so it is
  independent of `α, k, r, W`.

- **Logarithm.** `Real.log` (natural log) applied to `(k : ℝ)`. The base only changes
  `C`, so natural log is the neutral choice. `W.card` is cast to `ℝ`; the inequality is
  `(C * r * Real.log k) ^ k < (W.card : ℝ)` with `^ k` the natural-number power on `ℝ`.

- **Edge cases `k = 0, 1`.** Excluded via `2 ≤ k`. For `k = 1`, `Real.log 1 = 0` makes
  the bound `0`, and `|W| > 0` cannot force a multi-petal sunflower, so the statement
  would be false; `k = 0` is degenerate. This matches how the result is stated in the
  literature (bound meaningful for `k ≥ 2`). `1 ≤ r` excludes the vacuous `r = 0`.

- **Cardinality.** `Finset.card` throughout (`s.card = k`, `S.card = r`, `W.card`).

## Uncertainties / guessed identifiers

- I did **not** rely on any Mathlib sunflower API. Mathlib may contain a sunflower
  file (plausibly `Mathlib/Combinatorics/SetFamily/Sunflower.lean`) with a predicate
  such as `Finset.IsSunflower` and the classical Erdős–Rado bound
  (`f(k,r) ≤ k! (r-1)^k`); names guessed, not verified. The *improved* ALW/Rao bound is
  almost certainly not in Mathlib. To stay self-contained and avoid a name clash I put
  my own `IsSunflower` in namespace `Agent039`.

- `import Mathlib` (blanket import) is used for `Real.log`; no other Mathlib lemmas are
  referenced, so the statement should typecheck against any recent Mathlib once the
  `sorry`s are accepted.

- Syntax point I am slightly unsure of: an instance binder `[DecidableEq α]` inside a
  `∀`-telescope in term position. This is standard Lean 4 and should be fine, but I have
  no compiler to confirm.

- In `improved_sunflower_lemma_function` the hypothesis quantifies `α` over `Type`
  (not `Type*`) to keep the universe handling trivial; this is a cosmetic choice.
