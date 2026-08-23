import Mathlib

open Nat

/-!
Glaisher's theorem.

We represent a partition of `n` using Mathlib's `Nat.Partition n`, a structure
bundling a multiset `parts : Multiset ℕ` of positive naturals summing to `n`
(fields `parts`, `parts_pos`, `parts_sum`).

- "No part of `p` is divisible by `k`" is encoded as
  `∀ i ∈ p.parts, ¬ (k ∣ i)`.
- "Every part occurs fewer than `k` times" (no part repeated `k` or more
  times) is encoded via multiset multiplicity as
  `∀ i ∈ p.parts, p.parts.count i < k`.

We state the theorem as an equality of cardinalities (`Nat.card`) of the two
subtypes of `Nat.Partition n` cut out by these predicates; `Nat.card` is used
so that no `Fintype`/`Decidable` instances need to be supplied explicitly
(both subtypes are finite since `Nat.Partition n` is finite for each `n`).
-/

/-- **Glaisher's theorem.** Fix `k ≥ 2`. For every `n`, the number of
partitions of `n` into parts none of which is divisible by `k` equals the
number of partitions of `n` in which every part occurs fewer than `k` times
(i.e. no part is repeated `k` or more times). The case `k = 2` recovers
Euler's theorem that partitions into odd parts biject with partitions into
distinct parts. -/
theorem glaisher_agent12 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card { p : Nat.Partition n // ∀ i ∈ p.parts, ¬ (k ∣ i) } =
    Nat.card { p : Nat.Partition n // ∀ i ∈ p.parts, p.parts.count i < k } := by
  sorry
