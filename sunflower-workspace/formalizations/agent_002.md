# agent_002 — improved sunflower lemma (statement only)

## Form chosen

A single `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (α : Type*) [DecidableEq α] (k r : ℕ),
  2 ≤ k → 1 ≤ r → ∀ W : Finset (Finset α),
    (∀ s ∈ W, s.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ Y : Finset α, ∃ S ⊆ W, IsSunflower r Y S
```

plus an auxiliary `def IsSunflower r Y S`.

## Encoding decisions and rationale

- **Set representation.** Sets are `Finset α` over an arbitrary ambient type `α`
  (`[DecidableEq α]` needed for `∩`). The family `W` is `Finset (Finset α)`. This is the
  standard Mathlib combinatorics idiom, keeps `|W|` and `|S|` as plain `Finset.card`, and
  makes "distinct members" automatic. `α` is not assumed finite, so this is fully general.

- **Sunflower predicate.** Defined explicitly rather than assuming a Mathlib one:
  `S.card = r` (this both fixes the number of petals and forces the `r` members to be
  distinct) together with `(↑S : Set _).Pairwise (fun s t => s ∩ t = Y)` for an explicit
  core `Y`. I used the "all pairwise intersections coincide" formulation with a named core;
  the "element in ≥ 2 sets ⇒ in all", "petals pairwise disjoint", and (under uniform size,
  `r ≥ 2`) "petals nonempty" statements are consequences and are deliberately omitted from
  the definition. Petals are therefore *not* explicitly required nonempty.

- **Which logarithm.** `Real.log` (natural log). The base of the bound is a real number and
  `|W|` a natural, so the hypothesis is `(C * r * Real.log k)^k < (W.card : ℝ)`. The
  constant absorbs any change of log base, so the choice is immaterial to the statement's
  truth.

- **`k = 0, 1` handling.** Sidestepped by hypothesis `2 ≤ k`, which gives
  `Real.log k ≥ Real.log 2 > 0`. This matches the usual textbook phrasing (e.g. Tao's
  exposition: "for `k ≥ 2`"). For `k ∈ {0,1}` we have `log k ≤ 0` and the bound is
  degenerate; not covered.

- **`r`.** Hypothesis `1 ≤ r`. `r = 1` is trivially true (any singleton subfamily); kept
  for faithfulness to "all positive integers r".

- **The constant `C`.** Existentially quantified, and bound *outside* the `∀ α k r`, so it
  is a single absolute constant. `0 < C` added as a harmless normalization.

- **Inequality direction.** `|W| > (C r log k)^k` rendered as
  `(C * r * Real.log k) ^ k < (W.card : ℝ)`. Strict, as in the source statement.

- **`f(k,r)` version.** Mentioned in the docstring as the equivalent reformulation but not
  separately formalized, to avoid committing to a particular definition of the sunflower
  function via `sInf`/`Nat.find`.

## Uncertainties

- **Mathlib may already have a sunflower predicate.** I believe there is a file along the
  lines of `Mathlib/Combinatorics/SetFamily/Sunflower.lean` (Bhavik Mehta) with something
  like `Finset.IsSunflower (𝒮 : Finset (Finset α)) (core : Finset α)` defined via
  `Set.Pairwise`, and an Erdős–Rado bound `Finset.exists_isSunflower` (or similar name).
  I did not rely on it and could not verify the exact identifiers; I defined my own
  `IsSunflower` to stay self-contained. If the Mathlib name exists it likely does not carry
  the `card = r` conjunct (petal count would be `𝒮.card`).

- **Binder `∀ (α : Type*) [DecidableEq α]` inside a `∃`/`∧`.** I am fairly confident Lean 4
  accepts an instance-implicit binder in a `∀`-telescope inside a proposition, but I have no
  compiler to confirm. If it is rejected, the fix is to pull `α` and `[DecidableEq α]` out
  as theorem parameters before `∃ C` (mildly weakening "absolute" to "absolute per type",
  still standard).

- `Real.log (k : ℝ)` with `k : ℕ`: coercion written explicitly; assumed elaboration is
  fine.

- `import Mathlib` (whole library) used for a statement-only file; assumed acceptable.
