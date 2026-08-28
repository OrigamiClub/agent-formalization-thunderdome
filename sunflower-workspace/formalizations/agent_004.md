# agent_004 — improved sunflower lemma (statement only)

## Form chosen

One existential theorem `improved_sunflower_lemma`:

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α),
    (∀ S ∈ W, S.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ContainsSunflower W r
```

plus two supporting `def`s: `IsSunflower 𝒮 Y` and `ContainsSunflower W r`.

## Encoding decisions and why

- **Set representation.** Ambient type `α` with `[DecidableEq α]`; individual sets
  are `Finset α`; the family is `W : Finset (Finset α)`. `DecidableEq` is needed
  only so that `S₁ ∩ S₂` (`Finset` intersection) is available. Finsets avoid
  carrying separate finiteness hypotheses and give distinctness of members for
  free.
- **Sunflower predicate.** Defined explicitly via the "all pairwise
  intersections coincide" formulation: `IsSunflower 𝒮 Y` says every two distinct
  members of `𝒮` intersect in exactly `Y`. This is equivalent to the
  core/petals description and does not need the core to be `⊆` any member stated
  separately (it follows). I did **not** rely on a Mathlib predicate — see
  uncertainties.
- **"Contains a sunflower with r petals."** `∃ 𝒮 ⊆ W, 𝒮.card = r ∧ ∃ Y, IsSunflower 𝒮 Y`.
  Using `𝒮.card = r` on a `Finset` simultaneously fixes the petal count and
  forces the `r` members to be pairwise distinct, so no separate distinctness
  clause is needed.
- **Petals nonempty.** Not required. The classical definition does not demand it;
  at most one member can equal the core anyway (two would coincide, contradicting
  distinctness for `r ≥ 2`).
- **Cardinality.** `Finset.card` throughout; `W.card` cast to `ℝ` for the
  comparison.
- **Logarithm.** `Real.log` (natural log). The base of the log only changes the
  absolute constant `C`, so the specific base is immaterial to the statement.
- **`k = 0, 1` handling.** Guarded out with `2 ≤ k`. For `k ≤ 1`,
  `Real.log k ≤ 0` and `(C r log k)^k` is `0` or negative, which would make the
  threshold vacuous/false; the mathematical content of the lemma is for `k ≥ 2`
  (`f(1, r) = r` exactly). This is one of the sanctioned ways to deal with the
  edge case. `1 ≤ r` similarly excludes `r = 0`.
- **Constant `C`.** Existentially quantified *inside* the theorem but *outside*
  the `∀ {α}`, so it is a single absolute constant independent of the ambient
  type and of `k, r, W`. This matches "there is an absolute constant `C`".
- **Strictness.** `<` (strict), matching "`|W| > (C · r · log k)^k`".

## Uncertainties

- **Mathlib sunflower API.** Mathlib has
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean` which proves the *classical*
  Erdős–Rado bound. I believe it defines something like `Finset.IsSunflower`
  (possibly `IsSunflower (r) (𝒮) (t)` as a bundled predicate) and a theorem
  named along the lines of `Finset.exists_isSunflower`. I was not confident
  enough of the exact name / argument order to reuse it, so `IsSunflower` here
  is a local definition in namespace `ImprovedSunflower` (which also avoids any
  name clash). If the Mathlib predicate exists, this local one should be
  provably equivalent.
- **Exact published bound.** The literature has minor variants
  (`(C r log k)^k`, `(C r log(rk))^k`, `O(r log k)^k` for `k ≥ 2`, etc.). I used
  the form given in the task, `(C r log k)^k`, verbatim.
- `import Mathlib` is used for brevity; the precise minimal import is
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` (for `Real.log`) plus
  `Mathlib.Data.Finset.*`. Not compiler-checked.
