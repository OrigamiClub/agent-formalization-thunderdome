import Mathlib

/-
Glaisher's theorem.

We represent a partition of `n` using Mathlib's `Nat.Partition n`, a structure
bundling a multiset `parts : Multiset ℕ` of positive naturals with
`parts.sum = n`.

For a fixed `k ≥ 2` we consider, among all partitions of `n`:
  * `A_k(n)`: those partitions all of whose parts are NOT divisible by `k`;
  * `B_k(n)`: those partitions in which every part value occurs with
    multiplicity strictly less than `k` (i.e. no part is repeated `k`
    or more times), expressed via `Multiset.count`.

Glaisher's theorem asserts these two collections have the same cardinality,
for every `n`. We state this as an equality of `Set.ncard`s of the
corresponding subsets of `Nat.Partition n` (equivalently, one could give an
explicit bijection; we chose the cardinality-equality form as more natural
for a direct statement).
-/

theorem glaisher_agent15 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Set.ncard {p : Nat.Partition n | ∀ i ∈ p.parts, ¬ k ∣ i} =
    Set.ncard {p : Nat.Partition n | ∀ i ∈ p.parts, p.parts.count i < k} := by
  sorry
