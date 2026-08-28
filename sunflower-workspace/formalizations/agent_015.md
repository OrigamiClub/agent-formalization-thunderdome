# Agent 015 — Improved Sunflower Lemma, formalization note

## Form chosen

A single existential over an absolute constant `C : ℝ`, then universally quantified
over the ambient type, `k`, `r`, and the family:

```
∃ C : ℝ, 0 < C ∧
  ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
    ∀ W : Finset (Finset α),
      (∀ S ∈ W, S.card = k) →
      (C * r * Real.log k) ^ k < (W.card : ℝ) →
        ∃ P ⊆ W, ∃ Y : Finset α, P.card = r ∧ IsSunflower P Y
```

Plus a second theorem `sunflower_function_upper_bound` giving the contrapositive
"`f(k,r) ≤ (C r log k)^k`" phrasing (family with no `r`-petal sunflower has
`|W| ≤ (C r log k)^k`).

Both end in `:= by sorry`. Nothing is proved.

## Encoding decisions

- **Set representation.** `Finset (Finset α)` over an arbitrary `α` with
  `[DecidableEq α]`. Cleanest for finite set families; `∩` and `card` are
  directly available. Members of a `Finset` are automatically distinct, so
  distinctness of the family's members and of the sunflower's petals needs no
  separate hypothesis.
- **Absolute constant.** `C` is bound by `∃` *outside* the `∀ α`, so it cannot
  depend on the ambient type, `k`, `r`, or `W` — matching "absolute constant".
  Chosen existential (not a hypothesis / not a named literal) because the lemma
  asserts existence of such a `C` and no explicit value is pinned down in the
  literature (it varies by write-up).
- **Sunflower definition.** Custom predicate
  `IsSunflower P Y := ∀ S ∈ P, ∀ T ∈ P, S ≠ T → S ∩ T = Y`
  (explicit core `Y`). "`r` petals" is `P.card = r`. The stated conclusion asks
  for `P ⊆ W`, `P.card = r`, and a core `Y`. Pairwise-disjoint petals and the
  "in ≥2 ⇒ in all" property are consequences (for `P.card ≥ 2`) and are recorded
  in the docstring rather than baked in.
- **Petals nonempty.** Not required. The bound holds regardless; adding it would
  only weaken the statement.
- **Logarithm.** `Real.log` (natural log). Base choice only rescales `C`, which
  is existentially quantified, so it is immaterial. RHS is a real; `|W|` is
  coerced `ℕ → ℝ`. Exponent `^ k` is `Monoid.npow` (`k : ℕ`).
- **Small `k`.** Hypothesis `2 ≤ k`. For `k ≤ 1`, `Real.log k ≤ 0` makes
  `(C r log k)^k` vanish or go negative and the literal inequality would falsely
  force a sunflower in any nonempty family of singletons. The `k ≥ 2` restriction
  is the standard fix (e.g. Tao's exposition states the bound for `k ≥ 2`; the
  `k = 1` case is the trivial exact `f(1,r) = r`).
- **`r`.** `1 ≤ r` to match "all positive integers `r`". For `r ≤ 2` the
  conclusion is trivially satisfiable (any one/two members form a sunflower);
  genuine content is `r ≥ 3`.
- **Strictness.** Hypothesis is strict `>` (written `RHS < W.card`), matching
  "`|W| > (C · r · log k)^k`".
- **Cardinality.** `Finset.card` throughout.

## Uncertainties

- **Mathlib sunflower predicate.** I could not confirm from memory whether
  current Mathlib exports a sunflower predicate (candidate names:
  `Finset.IsSunflower`, `IsSunflower`, `Finset.Sunflower`, a
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean`). The classical sunflower
  lemma (`f(k,r) ≤ k!(r-1)^k`) may be in Mathlib (Bhavik Mehta), but I am not
  certain of the identifier or exact shape. To stay self-contained I defined my
  own `IsSunflower`. If a Mathlib predicate exists it may differ (e.g. petals
  as an indexed family, or core required `⊆` each set explicitly).
- **`import Mathlib`** used as a blanket import; `Real.log` lives in
  `Mathlib.Analysis.SpecialFunctions.Log.Basic`, `Finset` basics are core. The
  blanket import is safe but heavy.
- **Binder notation** `∃ P ⊆ W, ...` and `∀ (α : Type*) [DecidableEq α]` inside
  the body of an `∃ C` are believed valid Lean 4 / Mathlib syntax; not
  compiler-checked here.
- Coercions written explicitly (`(r : ℝ)`, `Real.log (k : ℝ)`, `(W.card : ℝ)`)
  to avoid elaboration ambiguity; not compiler-checked.
