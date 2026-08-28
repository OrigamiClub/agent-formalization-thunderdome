# agent_080 — improved sunflower lemma (statement only)

## Form chosen

Single `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (α) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  1 ≤ r → 2 ≤ k → (∀ A ∈ W, A.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ S ⊆ W, S.card = r ∧ ∃ Y, IsSunflower S Y
```

plus an auxiliary `def IsSunflower`.

## Encoding decisions

- **Set representation.** `Finset α` for a single set, `Finset (Finset α)` for
  the family `W`, over an arbitrary ambient type `α` with `[DecidableEq α]`
  (needed so `Finset.inter` / `Finset.sdiff` are defined). Chosen over
  `Set`+finiteness because the statement is entirely about finite cardinalities
  and this keeps `card` as plain `Finset.card : ℕ`.
- **Distinctness of members.** Free: elements of a `Finset (Finset α)` are
  distinct by construction, so "r distinct sets" is just `S.card = r`.
- **Sunflower predicate.** Defined locally as
  `(∀ A ∈ S, Y ⊆ A) ∧ (∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = Y)`.
  This is the "all pairwise intersections coincide (with an explicit core `Y`)"
  formulation from the problem statement. The `Y ⊆ A` conjunct is redundant when
  `S` has ≥ 2 members but makes the `r = 1` degenerate case still say "`Y` is a
  core". Petals `A \ Y` pairwise-disjoint is a consequence, not part of the def;
  petals are not required to be nonempty.
- **"r petals".** `S.card = r`.
- **Logarithm.** `Real.log (k : ℝ)` (natural log). The constant `C` absorbs the
  base, so the choice of base is immaterial to the truth of the statement.
- **Small `k`.** Hypothesis `2 ≤ k` is imposed so that `Real.log k > 0` and the
  bound is meaningful. For `k ≤ 1` the RHS `(… · log k)^k` is `≤ 0` (or the
  `k = 0` corner), which would make the implication vacuously wrong; `k = 1`
  (families of singletons) is the trivial separate case `f(1, r) = r`.
- **Constant `C`.** Existentially quantified at the very front
  ("there is an absolute constant"), with `0 < C`.
- **Cardinality.** `Finset.card` throughout; comparison with the real-valued
  bound via a cast `(W.card : ℝ)`, strict `<` as in `|W| > (…)^k`.

## Uncertainties

- Mathlib already has `Mathlib/Combinatorics/SetFamily/Sunflower.lean`, which (to
  the best of my recollection) defines a sunflower predicate — plausibly
  `Finset.IsSunflower` / `Set.IsSunflower` phrased via `Set.Pairwise (· ∩ · = t)`
  — and proves the classical Erdős–Rado bound (identifier maybe
  `Finset.exists_sunflower` / `exists_sunflower_of_...`). I could not verify the
  exact names without a compiler, so I introduced a local `IsSunflower` to keep
  the file self-contained. If the Mathlib name/shape is as above, this local def
  is definitionally close (mine adds the explicit `Y ⊆ A` clause).
- The improved lemma itself is not in Mathlib as far as I know; only the
  classical (factorial-bound) sunflower lemma is.
- `∀ (α : Type*) [DecidableEq α] …` appearing under an existential is expected to
  elaborate fine in Lean 4 / Mathlib, but I have not machine-checked it.
