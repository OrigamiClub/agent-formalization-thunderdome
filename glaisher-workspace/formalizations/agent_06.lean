import Mathlib

open Nat

/-- **Glaisher's theorem.**
For a fixed integer `k ≥ 2` and any natural number `n`, the number of
partitions of `n` in which no part is divisible by `k` equals the number of
partitions of `n` in which every part value occurs with multiplicity
strictly less than `k` (i.e. no part is repeated `k` or more times).

We represent a partition of `n` via Mathlib's `Nat.Partition n`, whose
underlying data is a multiset `parts : Multiset ℕ` of positive naturals
summing to `n`. The condition "no part divisible by `k`" is stated as
`∀ x ∈ p.parts, ¬ k ∣ x`, and the condition "every part occurs fewer than
`k` times" is stated using the multiset multiplicity function
`p.parts.count x < k` for every part `x` occurring in `p.parts`. The two
counts are compared as `Nat.card` of the corresponding subtypes of
`Nat.Partition n`.

The special case `k = 2` recovers Euler's classical theorem: partitions
into odd parts (no part divisible by `2`) are equinumerous with partitions
into distinct parts (every part occurs at most once, i.e. with
multiplicity `< 2`). -/
theorem glaisher_agent06 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card { p : Nat.Partition n // ∀ x ∈ p.parts, ¬ (k ∣ x) } =
    Nat.card { p : Nat.Partition n // ∀ x ∈ p.parts, p.parts.count x < k } := by
  sorry
