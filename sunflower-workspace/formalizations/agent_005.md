# agent_005 — improved sunflower lemma, statement

## Form chosen

A single `theorem improved_sunflower_lemma` whose conclusion is

```
∃ C : ℝ, 0 < C ∧ ∀ (α) [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
  ∀ W : Finset (Finset α),
    (∀ A ∈ W, A.card = k) →
    (W.card : ℝ) > (C * r * (Real.log k + 1)) ^ k →
    ∃ S ⊆ W, IsSunflowerWithPetals r S
```

plus one auxiliary `def IsSunflowerWithPetals`.

## Encoding decisions

- **Set family.** `W : Finset (Finset α)` over an arbitrary ambient type `α` with
  `[DecidableEq α]`. `Finset (Finset α)` gives "finite family" and "distinct members" for
  free; members are `Finset α`, i.e. finite sets. `α` is left fully general (may be
  infinite), so no loss of generality versus a `Set`-with-finiteness phrasing.
- **Cardinality.** `Finset.card`: `A.card = k` for each member; `W.card` compared to the
  bound. The comparison is cast into `ℝ` because the right-hand side is real-valued.
- **Sunflower predicate.** Defined locally as `IsSunflowerWithPetals r S`:
  `S.card = r ∧ ∃ Y, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = Y`. Explicit core `Y`, pairwise
  intersections all equal to it. Distinctness of the `r` sets is automatic (`Finset`) and
  their count is fixed by `S.card = r`. Petal-disjointness and "an element in two members
  is in all members" are consequences, not part of the definition. Petals are **not**
  required nonempty (matches the classical statement). The subfamily is delivered as
  `∃ S ⊆ W, ...`.
- **Constant `C`.** Existentially quantified inside the theorem, with `0 < C`, since it is
  an absolute constant independent of everything else (in particular of `α`, which is bound
  under the `∃ C`).
- **Logarithm.** `Real.log` (natural log). Base is irrelevant: it rescales the `log` factor
  by a constant absorbed by `C`.
- **`k = 1` / `k = 0` degeneracy.** Handled by using `Real.log k + 1` instead of
  `Real.log k`. At `k = 1`, `Real.log 1 = 0` but the sunflower function is `f(1,r) = r`, so
  the bound must be `≥ r`; `+1` yields `C·r`, and `∃ C` picks `C ≥ 1`. For `k ≥ 2`,
  `Real.log k + 1 ≤ (1 + (Real.log 2)⁻¹)·Real.log k`, a bounded distortion absorbed by `C`,
  so the statement is faithful to the `(C r log k)^k` bound. `k = 0` is excluded by the
  `0 < k` hypothesis (and would be vacuous anyway: all members would be `∅`, so `#W ≤ 1`).
- **Positivity hypotheses.** `0 < k`, `0 < r` ("positive integers k and r").

## Uncertainties

- Mathlib already has sunflower material in `Mathlib/Combinatorics/SetFamily/Sunflower.lean`
  (contributors Bhavik Mehta / Yaël Dillies). From memory it defines something like
  `Finset.IsSunflower (r : ℕ) (t : Finset α) (𝒮 : Finset (Finset α))` as
  `𝒮.card = r ∧ (𝒮 : Set (Finset α)).Pairwise (fun a b => a ∩ b = t)`, together with the
  classical Erdős–Rado bound `(r - 1)^k * k!` (theorem name guessed:
  `Finset.exists_isSunflower` or similar). I could not verify the exact identifiers,
  argument order, or whether the core is bundled or an explicit argument, so I defined my
  own predicate for self-containedness. If the Mathlib predicate exists as above, my
  `IsSunflowerWithPetals r S` corresponds to `∃ t, Finset.IsSunflower r t S`.
- Mathlib has `Set.Sized k (𝒜 : Set (Finset α))` (`∀ A ∈ 𝒜, A.card = k`) for uniform
  families; I inlined `∀ A ∈ W, A.card = k` instead of relying on that spelling.
- The improved bound has several published forms (`(C r log k)^k`,
  `(C r (log k + log r))^k`, `(C r log(rk))^k`, ...). I used the commonly cited
  `(C r log k)^k` form (Rao / Bell–Chueluecha–Warnke). The `∃ C` makes it robust to the
  constant-factor differences between these variants for `k ≥ 2`.
- No Lean compiler was available; syntax (e.g. instance-implicit binder inside `∀`,
  `∃ S ⊆ W, _` sugar, `ℕ → ℝ` coercions in the bound) is written from knowledge of Lean 4 /
  Mathlib conventions but unchecked.
