# Agent 067 — improved sunflower lemma (statement only)

## Form chosen

One primary theorem `improved_sunflower_lemma`, plus a secondary
`improved_sunflower_lemma_function` giving the `f(k,r) ≤ (C r log k)^k` phrasing.
Both end in `:= by sorry`; nothing is proved.

Shape of the primary statement:

```
∃ C : ℝ, 0 < C ∧
  ∀ {α} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
    ∀ W : Finset (Finset α), (∀ s ∈ W, s.card = k) →
      (C * r * Real.log k) ^ k < (W.card : ℝ) → ContainsSunflower r W
```

## Encoding decisions

- **Set representation.** Ambient type `α` with `[DecidableEq α]`; a family is
  `Finset (Finset α)`; set operations are `Finset` operations. Chosen over
  `Set`+finiteness because cardinalities (`Finset.card`) and "subfamily" (`⊆`) are
  frictionless, and `DecidableEq` is a cost-free assumption for this
  combinatorial statement.

- **Sunflower predicate.** Defined locally, not taken from Mathlib. Two defs:
  - `IsSunflower r Y P` := `P.card = r ∧ (∀ s₁ ∈ P, ∀ s₂ ∈ P, s₁ ≠ s₂ → s₁ ∩ s₂ = Y)`.
    Uses the "explicit core `Y`, all pairwise intersections coincide"
    formulation. The petals-disjoint / absorption properties are consequences,
    noted in a docstring but not baked in.
  - `ContainsSunflower r W` := `∃ Y, ∃ P ⊆ W, IsSunflower r Y P`.

- **Constant `C`.** Existentially quantified as the *outermost* binder, before
  `∀ α`, `∀ k`, `∀ r`. This is what makes it an "absolute constant": it may not
  depend on the ambient type, `k`, or `r`. Not supplied as a hypothesis and not
  given a numeric value (the known proofs give large unspecified constants).

- **Logarithm.** `Real.log` (natural logarithm), with `k : ℕ` coerced to `ℝ`. The
  whole bound is evaluated in `ℝ` and compared strictly (`<`) against
  `(W.card : ℝ)`. Changing the log base only rescales `C`, so `Real.log` vs
  `Real.logb 2` is immaterial to the statement's truth.

- **Handling `k = 0, 1`.** Hypothesis `2 ≤ k`. For `k ≤ 1`, `Real.log k ≤ 0`
  makes `(C r log k)^k` equal `1` (k=0) or `≤ 0` (k=1), and the statement is
  then false (k=1, r≥2: a family of `> 0` distinct singletons need not have `r`
  of them). These cases are genuinely degenerate, so they are excluded rather
  than papered over by writing `log (k+1)` or `max (log k) 1` (which would
  deviate from the stated expression `(C · r · log k)^k`).

- **`r`.** Hypothesis `1 ≤ r` ("positive integer `r`"). The statement is
  vacuously/trivially true for `r ≤ 2`; real content starts at `r ≥ 3`.

- **Cardinality "exactly `k`".** `∀ s ∈ W, s.card = k` via `Finset.card`.

- **Distinctness of sunflower members.** Automatic: `P : Finset (Finset α)` has no
  repeats, and `P.card = r` pins down exactly `r` distinct sets. Not separately
  stated.

- **Petals nonempty.** Not required. With equal cardinalities and `r ≥ 2` an
  empty petal `s \ Y = ∅` forces `s = Y ⊆ s'` hence `s = s'` (equal cards),
  contradicting distinctness — so nonemptiness is a theorem, not an axiom here.

- **Membership of sunflower sets in `W` / their size `k`.** Follows from
  `P ⊆ W` and the size hypothesis on `W`; not restated on `P`.

## Uncertainties

- I did not run a Lean compiler. Risks:
  - `∀ {α : Type*} [DecidableEq α] ...` appearing *inside* `∃ C : ℝ, 0 < C ∧ …`
    should be well-formed (the body is a `Prop`), but the nesting of a
    universe-polymorphic `∀` under an existential is the least-certain syntactic
    point.
  - `∃ P ⊆ W, IsSunflower r Y P` relies on Mathlib's bounded-existential sugar
    (`∃ x ⊆ s, p x` ↦ `∃ x, x ⊆ s ∧ p x`); believed standard.
  - `Real.log (k : ℝ)` coercion and `(_ : ℝ) ^ (k : ℕ)` via `Monoid.npow` should
    elaborate; wrote coercions explicitly to reduce ambiguity.
- Mathlib does contain `Mathlib/Combinatorics/SetFamily/Sunflower.lean`. From
  memory it defines something like `Finset.IsSunflower` / an `IsSunflower`
  predicate and proves the classical Erdős–Rado bound
  (`(r-1)^k * k! < 𝒮.card → …`), under a name I would guess to be
  `Finset.exists_isSunflower` or similar — I am not confident of the exact
  identifier or signature, so I defined my own predicate to stay self-contained.
  The improved (ALWZ/Rao/BCW) bound is, to my knowledge, not in Mathlib as of the
  knowledge cutoff.
- `improved_sunflower_lemma_function` takes the sunflower-free bounding function
  `f` and its defining property as hypotheses (rather than defining `f` via
  `sInf`/`Nat.find`) to keep the file short and avoid well-definedness
  obligations; this is a modelling choice, not a transcription of a standard
  statement.
