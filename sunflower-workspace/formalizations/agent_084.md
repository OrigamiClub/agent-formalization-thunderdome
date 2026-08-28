# agent_084 — Improved sunflower lemma (statement only)

## Form chosen

A single existential-constant theorem:

```
∃ C : ℝ, 0 < C ∧
  ∀ (α : Type) [DecidableEq α] (k r : ℕ), 1 ≤ r → 2 ≤ k →
    ∀ W : Finset (Finset α),
      (∀ S ∈ W, S.card = k) →
      (C * r * Real.log k) ^ k < (W.card : ℝ) →
      ∃ 𝒮 ⊆ W, IsSunflowerWith 𝒮 r
```

Two auxiliary defs:

* `IsSunflower 𝒮 Y` — any two distinct members of `𝒮` intersect in exactly `Y`
  ("pairwise intersections all coincide, and equal `Y`").
* `IsSunflowerWith 𝒮 r` — `𝒮.card = r ∧ ∃ Y, IsSunflower 𝒮 Y`.

## Encoding decisions and why

- **Set representation.** `Finset (Finset α)` over an arbitrary `α : Type`.
  Rationale: members of a `Finset` are automatically distinct (so "distinctness
  of the `r` petals" needs no separate hypothesis), `W.card` is literally `|W|`,
  and finiteness is built in. `DecidableEq α` is needed only to write `S ∩ T`.

- **"Sunflower with core."** Explicit core `Y` via the pairwise-intersection
  condition `∀ S T ∈ 𝒮, S ≠ T → S ∩ T = Y`. This is the cleanest faithful
  encoding. I did **not** add the derived consequences (`Y ⊆ S`, petals
  pairwise disjoint, "an element in ≥2 sets is in all") as conjuncts, since they
  follow from the pairwise condition once `|𝒮| ≥ 2`; a docstring records them.

- **Petals nonempty?** Not required. The classical statement does not need it,
  and `r`-petal sunflowers with empty petals (e.g. `𝒮 = {Y}` extended) are still
  legitimate; the bound is the interesting content. Requiring `Y ⊊ S` would be a
  reasonable stricter variant.

- **`r` petals.** Encoded as `𝒮.card = r`. Kept `1 ≤ r` ("positive integers");
  `r = 1, 2` give trivially-true instances, `r ≥ 3` is the substantive range.

- **Cardinality.** `Finset.card` throughout (`S.card = k`, `𝒮.card = r`,
  `W.card`).

- **Logarithm.** `Real.log` (natural log). The asymptotics are identical for any
  base, and `Real.log` is the most standard in Mathlib. The size comparison is
  done in `ℝ`: `(… )^k < (W.card : ℝ)`, matching `|W| > (C r log k)^k`.

- **`k = 1` / `k = 0`.** Handled by the hypothesis `2 ≤ k`. At `k = 1`,
  `Real.log 1 = 0` makes the RHS `0`, but `f(1, r) = r`, so the
  `(C r log k)^k` form is false for `k = 1`; the literature (ALWZ, Rao,
  Bell–Chueluecha–Warnke, and the usual textbook statement) restricts to
  `k ≥ 2`. `k = 0` is excluded a fortiori. An alternative faithful-to-"all
  positive `k`" choice would be to replace `Real.log k` by `Real.log (k + 1)`
  or `Real.log k + 1`; I preferred keeping the literal `log k` plus `k ≥ 2`.

- **The constant `C`.** Existentially quantified, and placed *outside* the
  `∀ α` so it cannot depend on the ambient type — a genuine absolute constant.
  `0 < C` is included so the statement is not vacuously satisfiable by a
  degenerate `C`.

- **Conclusion shape.** `∃ 𝒮 : Finset (Finset α), 𝒮 ⊆ W ∧ IsSunflowerWith 𝒮 r`
  — the sunflower is exhibited as an actual subfamily of `W`.

## Uncertainties

- **No Mathlib sunflower predicate.** Checked the available Mathlib source
  (`Mathlib/Combinatorics/SetFamily/`): files are `AhlswedeZhang`, `Compression`,
  `FourFunctions`, `HarrisKleitman`, `Intersecting`, `Kleitman`, `KruskalKatona`,
  `LYM`, `Shadow`, `Shatter`; `grep -ri sunflower` over the whole tree returns
  nothing. So there is no `Finset.IsSunflower` / `SetFamily.Sunflower` to reuse;
  the predicate here is bespoke. If a later Mathlib adds one, this could be
  swapped.

- **Instance binder inside `∀`.** `∀ (α : Type) [DecidableEq α] (k r : ℕ), …`
  is, to my knowledge, valid term-mode syntax in current Lean 4 / Mathlib
  (instance-implicit binders are allowed in `∀`-telescopes). Not machine-checked
  here (no compiler available).

- **`Real.log` on a `Nat` cast.** Written `Real.log (k : ℝ)` explicitly to force
  the coercion; `Real.log` is `Real → Real`.

- Everything ends in `:= by sorry`; no proof attempted, as instructed.
