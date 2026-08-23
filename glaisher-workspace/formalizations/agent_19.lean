import Mathlib

open Nat

/-- **Glaisher's theorem.**
Fix `k ≥ 2`. For every `n`, the number of partitions of `n` in which no part
is divisible by `k` equals the number of partitions of `n` in which every
part occurs fewer than `k` times (i.e. with multiplicity at most `k - 1`).

We represent a partition of `n` via Mathlib's `Nat.Partition n`, whose
underlying data is a multiset `parts : Multiset ℕ` of positive naturals
summing to `n`. "No part divisible by `k`" is `∀ i ∈ p.parts, ¬ k ∣ i`.
"Every part occurs fewer than `k` times" is `∀ i ∈ p.parts, p.parts.count i < k`,
using `Multiset.count`. The theorem is stated as an equality of `Nat.card`
of the two corresponding subtypes of `Nat.Partition n`. -/
theorem glaisher_agent19 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ (k ∣ i)} =
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, p.parts.count i < k} := by
  sorry
