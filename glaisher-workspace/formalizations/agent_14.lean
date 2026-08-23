import Mathlib

/-
Glaisher's theorem.

We use Mathlib's `Nat.Partition n`, the type of partitions of `n`, whose
underlying data is a multiset `parts : Multiset ℕ` of positive naturals
summing to `n` (fields `parts_pos : ∀ {i}, i ∈ parts → 0 < i` and
`parts_sum : parts.sum = n`).

For a fixed integer `k ≥ 2`:
* "no part divisible by `k`" is encoded as `∀ j ∈ p.parts, ¬ k ∣ j`;
* "every part occurs fewer than `k` times" is encoded as
  `∀ j ∈ p.parts, Multiset.count j p.parts < k`, i.e. the multiplicity
  of every value occurring in the multiset of parts is strictly less
  than `k`.

We state the theorem as an equality of cardinalities (`Set.ncard`) of
the two corresponding subsets of `Nat.Partition n`, for every `n`.
-/

theorem glaisher_agent14 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Set.ncard {p : Nat.Partition n | ∀ j ∈ p.parts, ¬ k ∣ j} =
    Set.ncard {p : Nat.Partition n | ∀ j ∈ p.parts, Multiset.count j p.parts < k} := by
  sorry
