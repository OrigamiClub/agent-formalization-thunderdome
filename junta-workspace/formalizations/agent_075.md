# Agent 075 — formalization note

## What I stated

**Both directions**, plus the **explicit witnessing family**, as two theorems:

1. `filmus_ihringer` — a conjunction:
   - *Forward*: `∃ m : ℕ → ℕ`, for all `d ≥ 1`, `k ≥ 2d`, `n ≥ 2k`, every Boolean
     degree-`d` function on the slice `binom([n],k)` is an `m d`-junta.
   - *Converse*: for `d ≥ 1`, `1 ≤ k < 2d`, and every `m`, there exist `n ≥ 2k` and a
     Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta.
2. `filmus_ihringer_converse_explicit` — the same converse but with the concrete witness
   `witnessFun n d k ℓ` induced by `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`,
   asserting it is Boolean, degree `≤ d`, and not an `m`-junta once `m < ℓ·e` and `n ≥ 2·ℓ·e`.

All theorems end in `:= by sorry`. Nothing is proved.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. `Fin n` stands for
  `{1,…,n}`; a subtype of `Finset` bundling the cardinality constraint is the most direct
  reading of `{S ⊆ {1,…,n} : |S| = k}`.
- **Boolean codomain**: functions are `Slice n k → ℝ` with a separate predicate
  `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1`. Keeping values in `ℝ` lets "Boolean" and
  "degree ≤ d" be stated uniformly against the same real polynomial evaluation.
- **Degree ≤ d** (`HasDegreeLE`): existence of `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `∀ i, p.degreeOf i ≤ 1` (multilinear, per the problem's "Terms"),
  agreeing with `f` on every slice point when evaluated at the `0/1` indicator vector
  `indicator S i = if i ∈ S then 1 else 0`. Multilinearity is included to match the
  problem text; it is WLOG on the slice, so dropping it would give an equivalent function
  class. It slightly *weakens* the forward direction (junta claim for a subclass) and is
  neutral/consistent for the converse (the explicit witness is genuinely multilinear).
- **m-junta** (`IsJunta f m`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and `f S = f T`
  whenever `S ∩ J = T ∩ J` (Finset intersection of the underlying sets). This is exactly
  "value depends only on `S ∩ J`".
- **`m(d)`**: an existential *inside* the statement, as a single function
  `∃ m : ℕ → ℕ, ∀ d ≥ 1, …` (equivalent to, and cleaner than, `∀ d ≥ 1, ∃ m`).
- **Carrying `n,k,d`**: explicit `ℕ` arguments/quantifiers with the inequalities
  (`1 ≤ d`, `2*d ≤ k`, `2*k ≤ n`, `1 ≤ k`, `k < 2*d`) as hypotheses; ambient coordinate
  set is `Fin n`.
- **Explicit family indexing**: 0-indexed. `blockSum n e i = ∑_{j ∈ range e} X_{i·e+j}`
  (out-of-range terms set to `0` via `dite`), and
  `witnessPoly n d k ℓ = ∏_{i ∈ range ℓ} blockSum n (min d k) i`. `witnessFun` evaluates
  this polynomial at slice indicator vectors. The problem's 1-based
  `x_{(i-1)e+j}, i∈[1,ℓ], j∈[1,e]` covers coordinates `1..ℓe`; my 0-based version covers
  `0..ℓe-1`, i.e. the same `ℓe` coordinates.

## Uncertainties

- I did not find a dedicated Mathlib notion of "Boolean degree-`d` function on the slice"
  or "junta"; both are spelled out by hand.
- Mathlib identifiers used from memory: `MvPolynomial.totalDegree`, `MvPolynomial.degreeOf`,
  `MvPolynomial.eval`, `MvPolynomial.X`, `Finset.range`, `Finset.card`, `∑ / ∏` `BigOperators`
  notation. These are standard; exact names should be current but were not machine-checked
  (no compiler available).
- The problem says the explicit family members are "not `ℓe`-juntas". Taken literally a
  function that mentions only `ℓe` coordinates *is* an `ℓe`-junta, so I read the intended
  content as "for every `m`, choosing `ℓ` with `ℓe > m` yields a family member that is not
  an `m`-junta" and encoded exactly that (`m < ℓ * min d k` in the hypotheses, conclusion
  `¬ IsJunta … m`). This is the safe faithful reading of the surrounding sentence
  ("for every `m` … not an `m`-junta").
- `filmus_ihringer_converse_explicit` asserts `IsBoolean (witnessFun …)` and
  `HasDegreeLE (witnessFun …) d` as conclusions, i.e. that the raw product is already
  `{0,1}`-valued on the slice and slice-degree `≤ d`. If the source instead applies a
  threshold/Boolean-ization to the product, that conclusion would need a wrapper
  `S ↦ if witnessFun … S = 0 then 0 else 1`; I chose the direct form to match the phrase
  "these functions … are Boolean degree-`d` functions".
- `noncomputable` is placed on the polynomial/indicator defs because `MvPolynomial _ ℝ`
  carries no executable instances; irrelevant to a statement-only file.
