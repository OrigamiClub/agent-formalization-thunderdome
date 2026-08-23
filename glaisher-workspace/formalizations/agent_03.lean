import Mathlib

/-
Glaisher's theorem.

For a fixed integer `k ≥ 2` and every natural number `n`, the number of
partitions of `n` all of whose parts are *not* divisible by `k` equals
the number of partitions of `n` in which every part occurs (with
multiplicity) strictly fewer than `k` times.

We use Mathlib's `Nat.Partition n`, a structure bundling
`parts : Multiset ℕ` together with proofs that every part is positive
(`parts_pos`) and that the parts sum to `n` (`parts_sum`).

- "no part divisible by k" is encoded as `∀ i ∈ p.parts, ¬ k ∣ i`.
- "every part occurs fewer than k times" is encoded via multiset
  multiplicity as `∀ i, p.parts.count i < k` (for `i` not occurring at
  all, `count i = 0 < k` holds automatically, so this correctly only
  constrains parts that actually occur).

`Nat.Partition n` is a finite type (there are finitely many partitions
of a natural number), so we state the theorem as an equality of
`Nat.card` of the two subtypes cut out by these predicates; `Nat.card`
gives the honest finite cardinality here since both subtypes are
finite.
-/

theorem glaisher_agent03 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i} =
      Nat.card {p : Nat.Partition n // ∀ i, p.parts.count i < k} := by
  sorry
