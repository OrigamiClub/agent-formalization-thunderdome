# Agent 093 — notes on the formalization

## Form chosen

Two `:= by sorry` theorems in a namespace `Agent093`, plus one auxiliary
definition `IsSunflower`.

- `improved_sunflower_lemma`: existence form — a large uniform family contains a
  sunflower with `r` petals.
- `improved_sunflower_lemma_bound`: the contrapositive "sunflower function" form —
  a sunflower-free uniform family has size `≤ (C r log k)^k`.

## Encoding decisions

- **Set representation.** Sets are `Finset α` over an arbitrary ambient type `α`
  with `[DecidableEq α]` (needed for `Finset` intersection). The family is
  `W : Finset (Finset α)`. Using `Finset` throughout means finiteness of `W` and
  distinctness of its members are automatic, so neither is stated as a
  hypothesis. `α` is `Type*` (universe-polymorphic).

- **Uniformity.** "each of cardinality exactly `k`" is `∀ A ∈ W, A.card = k`
  (`Finset.card`).

- **`IsSunflower r S`.** Defined as: `S.card = r` together with
  `∃ Y : Finset α, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = Y`.
  - Explicit core `Y` (rather than "all pairwise intersections coincide"); with
    `r ≥ 2` the two are equivalent, and the explicit core matches the informal
    statement.
  - The "element in ≥ 2 members ⇒ in all members" property and the
    pairwise-disjointness of the petals `A \ Y` both follow from this condition,
    so they are not stated separately.
  - Petals are **not** required to be nonempty (at most one member can coincide
    with the core anyway). This is a deliberate choice; some authors demand
    proper/nonempty petals.
  - Distinctness of the `r` members is automatic (`S : Finset _`); combined with
    `S.card = r` we genuinely get `r` distinct petals.
  - The conclusion `∃ S ⊆ W, IsSunflower r S` unfolds to
    `∃ S, S ⊆ W ∧ IsSunflower r S`.

- **The constant `C`.** Existentially quantified at the very top, *before* the
  quantifiers over `α`, `k`, `r`, `W`, so it is a single absolute constant
  (cannot depend on the type or the parameters). `0 < C` is asserted. An
  alternative (constant supplied as an explicit hypothesis with lower bound) was
  rejected as less faithful to "there is an absolute constant".

- **Logarithm.** `Real.log` (natural log). The literature's `log k` is
  base-agnostic since a change of base is a constant factor absorbed into `C`.
  The bound is stated over `ℝ` with the obvious coercions:
  `(C * r * Real.log k) ^ k < (W.card : ℝ)`, exponent kept as `ℕ`.

- **Small `k`.** Hypothesis `2 ≤ k`. For `k = 1`, `Real.log 1 = 0`, so the
  right-hand side collapses to `0` and the literal inequality
  `|W| > 0 ⇒ sunflower with r petals` is false (a one-element family of
  singletons has no `r`-petal sunflower for `r ≥ 2`). `k = 0` is likewise
  excluded. Requiring `k ≥ 2` is the standard reading (Rao;
  Bell–Chueluecha–Warnke) and keeps the statement true for a suitable absolute
  `C`. `r ≥ 1` is kept as "positive integer `r`".

## Uncertainties

- Mathlib (checked against the local copy) has **no** `Sunflower` / `IsSunflower`
  notion, so `IsSunflower` is defined here from scratch. Identifier name is my
  own.
- Minor: the `∃ C, ... ∀ (α : Type*) [DecidableEq α] ...` shape makes the
  statement technically universe-polymorphic in a way that lets `C` differ per
  universe; morally still one constant. Could be pinned to `Type` if that matters.
- `Real.log`, `Finset.card`, coercion `ℕ → ℝ`, and the `∃ x ⊆ s, p x` binder
  notation are all standard current Mathlib; not independently recompiled here
  (no Lean compiler available).
- The `improved_sunflower_lemma_bound` form phrases "sunflower function" via the
  negation of the existence statement rather than defining `f(k,r)` explicitly,
  to keep the file self-contained.
