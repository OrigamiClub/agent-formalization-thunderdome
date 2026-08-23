import Mathlib

/-
Glaisher's theorem.

We use Mathlib's `Nat.Partition n`, defined as a structure bundling
`parts : Multiset ℕ`, a proof that every part is positive, and a proof
that the parts sum to `n`.

For `k ≥ 2` and `n : ℕ`:
* `A_k(n)` is the set of partitions of `n` all of whose parts are *not*
  divisible by `k` (formalized as: for every `i` in the parts multiset,
  `¬ (k ∣ i)`).
* `B_k(n)` is the set of partitions of `n` in which every part value
  occurs with multiplicity strictly less than `k` (formalized via
  `Multiset.count`: for every `i : ℕ`, `p.parts.count i < k`; note that
  if `i` does not occur at all this count is `0 < k`, which is
  automatically satisfied since `k ≥ 2`).

We state the theorem as an equality of cardinalities of these two
subtypes of `Nat.Partition n`, using `Nat.card`, which needs no
`Fintype`/`Decidable` instances since `Nat.Partition n` is already
known to be finite in Mathlib.
-/

theorem glaisher_agent17 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ (k ∣ i)} =
    Nat.card {p : Nat.Partition n // ∀ i : ℕ, p.parts.count i < k} := by
  sorry
