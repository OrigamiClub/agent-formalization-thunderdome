import Mathlib

open Nat

/-- **Glaisher's theorem.**
For a fixed `k ≥ 2` and every `n : ℕ`, the number of partitions of `n` all of
whose parts are *not* divisible by `k` equals the number of partitions of `n`
in which every part occurs *fewer than `k` times* (i.e. no part is repeated
`k` or more times).

We use Mathlib's `Nat.Partition n`, whose underlying data is a multiset
`parts : Multiset ℕ` of positive naturals with `parts.sum = n`.
- "No part divisible by `k`" is encoded as `∀ i ∈ p.parts, ¬ k ∣ i`.
- "Every part occurs fewer than `k` times" is encoded via multiset
  multiplicity as `∀ i ∈ p.parts, p.parts.count i < k`.

We state the theorem as an equality of `Nat.card` of the two subtypes
(`Nat.card` gracefully handles finiteness, and each subtype here is finite
since it is a subtype of the finite type `Nat.Partition n`). Taking `k = 2`
recovers Euler's theorem: partitions into odd parts biject with partitions
into distinct parts. -/
theorem glaisher_agent20 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i} =
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, p.parts.count i < k} := by
  sorry
