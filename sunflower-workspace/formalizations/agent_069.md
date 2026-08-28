# Agent 069 — Improved sunflower lemma, statement only

## Form chosen

A single existential-constant theorem:

```
∃ C : ℝ, 0 < C ∧
  ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
    ∀ W : Finset (Finset α), (∀ s ∈ W, s.card = k) →
      (W.card : ℝ) > (C * r * Real.log k) ^ k →
        ∃ S ⊆ W, S.card = r ∧ ∃ Y, IsSunflower S Y
```

with a local self-contained definition

```
def IsSunflower (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ S → s ≠ t → s ∩ t = Y
```

Ends with `:= by sorry`. No proof attempted.

## Encoding decisions and why

- **Set representation.** `Finset (Finset α)` over an arbitrary ambient type `α` with
  `[DecidableEq α]`. This is the representation Mathlib uses for its existing sunflower
  material, keeps everything finite without side finiteness hypotheses, and makes
  cardinalities plain `Nat` via `Finset.card`.
- **Distinctness of members.** Free: elements of a `Finset` are distinct, so
  "`r` distinct sets" is exactly `S.card = r`, and "family `W`" carries no multiplicity.
- **Sunflower predicate.** Defined locally as "all pairwise intersections of distinct
  members equal the core `Y`", using strict-implicit binders so it matches the shape of
  `Set.Pairwise`. I did not depend on a Mathlib predicate to keep the file self-contained
  (see uncertainties). The stated consequences (elements in ≥2 members are in all; petals
  pairwise disjoint) follow from this predicate and are not part of the statement.
- **Core `Y`.** Existentially quantified explicitly rather than derived. For `r ≥ 2` it is
  forced (`Y = s ∩ t` for any two members); for `r = 1` the predicate is vacuous, which is
  the correct trivial reading of "1 petal".
- **Petals.** Not required nonempty. With `r ≥ 2` at most one petal can be empty anyway;
  requiring nonemptiness is a stronger, nonstandard variant, so I left it out.
- **Logarithm.** `Real.log` (natural log). The base only rescales `C`, which is
  existentially quantified, so any fixed base gives an equivalent statement. Comparison
  `|W| > (C r log k)^k` is done in `ℝ` with `W.card` coerced.
- **`k = 1` / `k = 0` handling.** Added hypothesis `2 ≤ k`. For `k = 1`,
  `Real.log 1 = 0` makes the RHS `0`, and `|W| > 0` does not force `r` singletons to
  appear, so the literal statement would be false; the usual references either take
  `k ≥ 2` or read `log k` as `max 1 (Real.log k)`. I chose the `2 ≤ k` hypothesis as the
  least invasive faithful option. `k = 0` is excluded a fortiori.
- **`r`.** `1 ≤ r`, matching "all positive integers r".
- **Constant `C`.** Existentially quantified as an "absolute constant", with `α, k, r`
  all quantified inside the `∃ C`, so `C` is genuinely uniform (independent of the ambient
  type and of `k, r`). Sign fixed by `0 < C`; combined with `2 ≤ k`, `1 ≤ r` the power
  base `C * r * Real.log k` is positive, so no even/odd-power subtleties.
- **Conclusion shape.** `∃ S, S ⊆ W ∧ S.card = r ∧ ∃ Y, IsSunflower S Y` — the subfamily
  is explicitly a subset of `W`, has exactly `r` members, and has a common core.

## Uncertainties

- **Mathlib identifiers.** I believe Mathlib has `Mathlib.Combinatorics.SetFamily.Sunflower`
  with something like `Finset.IsSunflower (𝒮 : Finset (Finset α)) (core : Finset α)` defined
  via `Set.Pairwise` and an Erdős–Rado result `Finset.exists_sunflower` with the classical
  bound `(r - 1) ^ k * k !`. I did not rely on these names; the local `IsSunflower` is
  independent. If the Mathlib predicate exists, this local definition should be
  definitionally close to it.
- `import Mathlib` is used for convenience (`Real.log`, `Finset`). A minimal import set was
  not determined.
- Whether the community-preferred phrasing keeps `α` as a theorem parameter (making `C`
  possibly type-dependent) or inside the `∃` as done here. I chose "inside" to honour
  "absolute constant".
- Not machine-checked: no Lean compiler was available. Binder syntax
  `∀ (α : Type*) [DecidableEq α] (k r : ℕ), …` inside the existential is believed valid
  Lean 4; the universe variable is auto-bound on the theorem.
