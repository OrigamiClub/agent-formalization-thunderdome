import Mathlib

/-!
Glaisher's theorem.

Representation of "a partition of `n`": Mathlib's `Nat.Partition n`, a structure
bundling a multiset `parts : Multiset ℕ` together with proofs that every part is
positive (`parts_pos`) and that the parts sum to `n` (`parts_sum`). `Nat.Partition n`
carries a `Fintype` instance, so subtypes of it cut out by decidable predicates are
finite and `Nat.card` gives the honest (finite) count.

- "No part of `p` is divisible by `k`" is encoded as `∀ i ∈ p.parts, ¬ k ∣ i`.
- "Every part occurs fewer than `k` times" (i.e. at most `k - 1` times) is encoded
  using `Multiset.count`, as `∀ i ∈ p.parts, p.parts.count i < k`.

The theorem is stated as an equality of `Nat.card` of the two subtypes of
`Nat.Partition n` satisfying these predicates, for every `k ≥ 2` and every `n`.
-/

theorem glaisher_agent07 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : n.Partition // ∀ i ∈ p.parts, ¬ k ∣ i} =
      Nat.card {p : n.Partition // ∀ i ∈ p.parts, p.parts.count i < k} := by
  sorry
