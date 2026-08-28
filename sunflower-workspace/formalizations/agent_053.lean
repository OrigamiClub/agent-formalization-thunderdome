import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke:

> There is an absolute constant `C` such that for all positive integers `k` and `r`, every
> finite family `W` of sets each of cardinality exactly `k` with
> `|W| > (C · r · log k)^k` contains a sunflower with `r` petals.

Only the statement is formalized here; the proof is `sorry`.
-/

namespace ImprovedSunflower

/-- A finite family `petals` of finite sets is a **sunflower with `r` petals** when it has
exactly `r` members (which are then automatically distinct, being elements of a `Finset`) and
there is a common **core** `core : Finset α` with `S ∩ T = core` for every pair of distinct
members `S, T`.

Standard consequences, not needed for the statement below: for `r ≥ 2` the core is forced to be
the intersection of all members, every element lying in two members lies in all of them, and the
"petals proper" `S \ core` are pairwise disjoint. Degenerate members with `S = core` (hence an
empty petal, possible for at most one member) are permitted, matching the usual Erdős–Rado
Δ-system definition. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (petals : Finset (Finset α)) : Prop :=
  petals.card = r ∧
    ∃ core : Finset α, (petals : Set (Finset α)).Pairwise (fun S T => S ∩ T = core)

/-- `W` **contains a sunflower with `r` petals** if some sub-family of `W` is a sunflower with
`r` petals. -/
def ContainsSunflower {α : Type*} [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ petals : Finset (Finset α), petals ⊆ W ∧ IsSunflower r petals

/-- **Improved sunflower lemma.**

There is an absolute positive constant `C` such that for all positive integers `k` and `r`, and
for every ambient type `α` with decidable equality, every finite family `W : Finset (Finset α)`
whose members all have cardinality exactly `k` and which satisfies
`(C · r · max (log k) 1)^k < |W|` contains a sunflower with `r` petals.

Encoding decisions:
* Sets are `Finset α` over an ambient `DecidableEq` type `α`; the family is `W : Finset (Finset α)`.
* The constant `C` is existentially quantified (and required `0 < C`) *outside* the quantifier
  over `α`, so it is genuinely absolute — independent of `k`, `r`, and the ambient type.
* `log` is the natural logarithm `Real.log`. The factor `max (Real.log k) 1` handles the
  degenerate case `k = 1` (where `Real.log 1 = 0` would make the bound vacuously `0`): replacing
  `log k` by `max (log k) 1` only enlarges the absolute constant for `k ≥ 2` and keeps the
  statement true and nontrivial for `k = 1`.
* Cardinalities are `Finset.card`. The comparison is in `ℝ` (the right-hand side `|W|` is cast).
* Distinctness of the `r` sunflower members is automatic from `petals.card = r`.
* Petals are not required to be nonempty. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 0 < k → 0 < r →
        ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * max (Real.log (k : ℝ)) 1) ^ k < (W.card : ℝ) →
          ContainsSunflower W r := by
  sorry

/-- Reformulation via the sunflower function `f k r`, the least `N` such that any family of `N`
`k`-element sets contains a sunflower with `r` petals. With the same absolute constant `C`,
`f k r ≤ (C · r · max (log k) 1)^k`. Here `f` is supplied abstractly by its defining property. -/
theorem improved_sunflower_lemma_function
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ (k r : ℕ), 0 < k → 0 < r →
      ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
        (∀ S ∈ W, S.card = k) → f k r ≤ W.card → ContainsSunflower W r)
    (hf_min : ∀ (k r : ℕ) (N : ℕ),
      (∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
        (∀ S ∈ W, S.card = k) → N ≤ W.card → ContainsSunflower W r) → f k r ≤ N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 0 < k → 0 < r →
        (f k r : ℝ) ≤ (C * (r : ℝ) * max (Real.log (k : ℝ)) 1) ^ k := by
  sorry

end ImprovedSunflower
