import Mathlib

/-
Glaisher's theorem.

Fix k ≥ 2. For every n : ℕ, the number of partitions of n in which no part is
divisible by k equals the number of partitions of n in which every distinct
part occurs strictly fewer than k times (i.e. at most k - 1 times).

Representation choice: we use Mathlib's `Nat.Partition n`, a structure with
field `parts : Multiset ℕ` satisfying `parts_pos` (all parts positive) and
`parts_sum : parts.sum = n`. We do not need those fields explicitly here,
only `p.parts`.

- "no part of p is divisible by k" is encoded as `∀ i ∈ p.parts, ¬ k ∣ i`.
- "every part of p occurs fewer than k times" is encoded via multiset
  multiplicity `Multiset.count`, as `∀ i ∈ p.parts, p.parts.count i < k`.

We state the theorem as an equality of `Set.ncard` of the two defining sets
of partitions of n, rather than as an explicit bijection. `Set.ncard` is used
(instead of `Finset.card`) so that we do not need to separately supply
`Fintype`/`Decidable` instances for these subsets; the statement is correct
regardless (both sets are in fact finite, being subsets of the finite type
`Nat.Partition n`).
-/

theorem glaisher_agent08 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Set.ncard {p : Nat.Partition n | ∀ i ∈ p.parts, ¬ k ∣ i} =
    Set.ncard {p : Nat.Partition n | ∀ i ∈ p.parts, p.parts.count i < k} := by
  sorry
