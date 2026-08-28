# agent_050 — improved sunflower lemma (statement only)

## Form chosen

A single existential-constant theorem:

```
∃ C : ℝ, 0 < C ∧ ∀ (α : Type*) [DecidableEq α] (k r : ℕ),
  2 ≤ k → 1 ≤ r → ∀ W : Finset (Finset α),
    (∀ S ∈ W, S.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ Y P, P ⊆ W ∧ IsSunflower r Y P
```

plus a local definition `IsSunflower r Y P`.

## Encoding decisions and rationale

- **Set representation.** `Finset α` over an arbitrary ambient type `α` with
  `[DecidableEq α]`; the family is `W : Finset (Finset α)`. This is the lightest
  representation for "finite family of finite sets" and matches Mathlib's
  set-family combinatorics. No `Fintype α` is assumed, so `α` may be infinite.

- **`C` as an absolute constant.** `C` is `∃`-bound at the very outside, *before*
  the `∀ (α : Type*)`, so it cannot depend on the ambient type, on `k`, `r`, or
  on `W`. This is the precise meaning of "absolute constant". I preferred this to
  supplying `C` as a hypothesis, which would leave "absolute" implicit.

- **Sunflower predicate.** Defined locally (in `namespace
  ImprovedSunflowerLemma`) as: `P.card = r` together with "any two distinct
  members of `P` intersect in exactly `Y`". Rationale:
  - Distinctness of the `r` members is automatic because `P : Finset (Finset α)`
    and `P.card = r`.
  - "Pairwise intersections all equal `Y`" is the cleanest faithful rendering of
    the core condition. For `r ≥ 2` it implies `Y ⊆ S` for every `S ∈ P` and
    that the petals `S \ Y` are pairwise disjoint, i.e. the "every element in ≥ 2
    sets is in all of them" formulation. I therefore did not separately assume
    `Y ⊆ S` or petal-nonemptiness (nonemptiness of petals is anyway forced in
    the theorem, since all members have the same cardinality `k` and are
    distinct).
  - The sunflower is returned as a sub-family `P ⊆ W`, so its members inherit
    `card = k`.

- **Logarithm.** `Real.log` (natural log), with the size comparison done in `ℝ`
  via casts `(W.card : ℝ)` and `(k : ℝ)`. The exponent `^ k` is `Monoid.npow`
  with `k : ℕ`.

- **Small `k`.** Guarded by `2 ≤ k`. At `k = 1`, `Real.log 1 = 0` makes the
  right-hand side `0`, so `|W| > 0` would have to force an `r`-petal sunflower,
  which fails (e.g. `|W|` between `1` and `r-1`). The literature bound
  `(C r log k)^k` is standardly read for `k ≥ 2`; `k = 0, 1` are degenerate.
  `k = 0` (empty sets) is also excluded by `2 ≤ k`.

- **`r`.** Hypothesis `1 ≤ r` ("positive integer `r`"). `r = 1` makes the
  conclusion trivial (any single member is a 1-petal sunflower), consistently
  with the statement.

## Uncertainties / guessed identifiers

- Mathlib has a file `Mathlib/Combinatorics/SetFamily/Sunflower.lean` (the
  classical Erdős–Rado lemma). I am not certain of the exact name/signature of
  its sunflower predicate (possibly `Finset.IsSunflower` or similar), and the
  *improved* bound is not in Mathlib. To stay self-contained and avoid a name
  clash I defined my own `IsSunflower` inside `namespace
  ImprovedSunflowerLemma`. If the Mathlib predicate exists and is defeq/iff to
  mine, one could substitute it.

- `import Mathlib` is used for safety rather than a minimal import list. The only
  library items referenced are `Finset`, `Finset.card`, `Finset.inter`, and
  `Real.log`, all long-standing.

- Coercion `Real.log (k : ℝ)` with `k : ℕ` is written explicitly to avoid any
  elaboration ambiguity.

## Alternative encodings considered but not used

- Explicit petals-pairwise-disjoint + `Y ⊆ S` conjunction (more verbose, same
  content for `r ≥ 2`).
- `Set (Set α)` with `Set.Finite` / `Set.ncard` hypotheses (heavier).
- An indexed family `S : Fin r → Finset α` with injectivity (makes distinctness
  explicit but adds an index bookkeeping layer).
- `Real.logb 2` — same degeneracy at `k = 1`, no advantage.
