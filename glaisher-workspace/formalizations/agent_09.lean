import Mathlib

/-
Glaisher's theorem.

Representation of "a partition of n": we use Mathlib's `Nat.Partition n`, a structure
  parts     : Multiset ℕ
  parts_pos : ∀ ⦃i⦄, i ∈ parts → 0 < i
  parts_sum : parts.sum = n

- "No part divisible by k" is encoded as: ∀ j ∈ p.parts, ¬ (k ∣ j).
- "Every part occurs fewer than k times" (no part repeated k or more times) is encoded via
  the multiset's `count` function: ∀ j ∈ p.parts, Multiset.count j p.parts < k.

We state the theorem as an equality of `Nat.card` of the two subtypes of `Nat.Partition n`
cut out by these conditions, for every k ≥ 2 and every n : ℕ.
-/

theorem glaisher_agent09 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ j ∈ p.parts, ¬ (k ∣ j)} =
    Nat.card {p : Nat.Partition n // ∀ j ∈ p.parts, Multiset.count j p.parts < k} := by
  sorry
