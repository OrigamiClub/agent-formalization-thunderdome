import Mathlib

/-
Glaisher's theorem.

We use Mathlib's `Nat.Partition n`, a structure bundling
  * `parts : Multiset ℕ`
  * `parts_pos : ∀ ⦃i⦄, i ∈ parts → 0 < i`
  * `parts_sum : parts.sum = n`
i.e. a multiset of positive naturals summing to `n`.

For a fixed `k ≥ 2` we consider, among all partitions of `n`:
  * `A_k(n)`: those none of whose parts is divisible by `k`
      (`∀ x ∈ p.parts, ¬ k ∣ x`);
  * `B_k(n)`: those in which every part value occurs strictly fewer than
      `k` times (`∀ x ∈ p.parts, p.parts.count x < k`), i.e. no part is
      repeated `k` or more times.

Glaisher's theorem asserts these two collections of partitions of `n`
have the same (finite) cardinality, for every `n`. We phrase this as an
equality of `Nat.card` on the corresponding subtypes of `Nat.Partition n`;
`Nat.card` is well-behaved here since both subtypes are finite (they sit
inside the finite type of all partitions of `n`), and using it lets us
avoid committing to a particular `Fintype`/`Decidable` instance.
-/

theorem glaisher_agent10 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ x ∈ p.parts, ¬ k ∣ x} =
    Nat.card {p : Nat.Partition n // ∀ x ∈ p.parts, p.parts.count x < k} := by
  sorry
