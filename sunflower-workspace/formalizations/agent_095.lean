import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the refined bound of Rao and of
Bell–Chueluecha–Warnke:

> There is an absolute constant `C` such that for all positive integers `k` and `r`,
> every finite family `W` of sets, each of cardinality exactly `k`, with
> `|W| > (C · r · log k)^k`, contains a sunflower with `r` petals.

Only the statement is given; the proof is `sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*}

/-- A finite family `petals` of finite sets is a **sunflower** with **core** `core`
when any two distinct members of the family meet in exactly `core`.

Equivalently: every element that lies in at least two members lies in every member,
and the "petals" `S \ core` (for `S ∈ petals`) are pairwise disjoint.

Distinctness of the members is built in because `petals : Finset (Finset α)`.
When `petals.card ≥ 2` one automatically gets `core ⊆ S` for each `S ∈ petals`
(as `core = S ∩ T ⊆ S`), and if in addition all members have the same cardinality
then `core ⊊ S`, so the petals are genuinely nonempty; hence no separate
nonemptiness hypothesis is imposed here. -/
def IsSunflower [DecidableEq α]
    (petals : Finset (Finset α)) (core : Finset α) : Prop :=
  ∀ S ∈ petals, ∀ T ∈ petals, S ≠ T → S ∩ T = core

/-- `HasSunflower W r` : the family `W` contains a sunflower with exactly `r` petals,
i.e. there is an `r`-element subfamily `𝒮 ⊆ W` and a core `Y` with `IsSunflower 𝒮 Y`. -/
def HasSunflower [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ 𝒮 : Finset (Finset α), 𝒮 ⊆ W ∧ 𝒮.card = r ∧ ∃ Y : Finset α, IsSunflower 𝒮 Y

/-- **Improved sunflower lemma.**
There is an absolute real constant `C > 0` such that for every type `α` with
decidable equality, all positive integers `k` and `r`, and every finite family
`W : Finset (Finset α)` whose members all have cardinality exactly `k`, if
`(C · r · log (k + 1)) ^ k < |W|` then `W` contains a sunflower with `r` petals.

Encoding decisions:
* `C` is quantified **outside** the type variable `α` and the parameters `k`, `r`,
  so it is genuinely an absolute constant.
* `Real.log` (natural logarithm) is used. We take `log (k + 1)` instead of `log k`
  so the threshold behaves well at `k = 1` (where `log 1 = 0` would collapse the
  bound); replacing `k` by `k + 1` only changes the bound by a constant factor,
  absorbed into `C`, and keeps the `(C r log k)^k` growth rate.
* The nontrivial range is `r ≥ 3`; for `r ∈ {1, 2}` the conclusion is trivial.
* `f(k, r) ≤ (C r log k)^k` is the contrapositive reading: if `|W|` exceeds the
  bound a sunflower must appear, i.e. the sunflower function is at most the bound. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 1 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log ((k : ℝ) + 1)) ^ k < (W.card : ℝ) →
          HasSunflower W r := by
  sorry

end ImprovedSunflower
