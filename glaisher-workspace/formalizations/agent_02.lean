import Mathlib

/-!
# Glaisher's theorem

For a fixed integer `k ≥ 2`, the number of partitions of `n` into parts
none of which is divisible by `k` equals the number of partitions of `n`
in which no part occurs `k` or more times (i.e. every distinct part
value occurs with multiplicity at most `k - 1`).

A partition of `n` is represented directly as a `Multiset ℕ`, `s`,
satisfying:
  * `∀ i ∈ s, 0 < i`   (all parts are positive), and
  * `s.sum = n`        (the parts sum to `n`).

"No part divisible by `k`" is `∀ i ∈ s, ¬ k ∣ i`.
"No part repeated `k` or more times" is `∀ i ∈ s, s.count i < k`.

The two families of partitions are packaged as `Set (Multiset ℕ)`, and
the theorem is stated as an equality of their `Set.ncard` (cardinality),
matching the classical statement `A_k(n) = B_k(n)`. The special case
`k = 2` recovers Euler's theorem: partitions into odd parts biject with
partitions into distinct parts.
-/

theorem glaisher_agent02 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    {s : Multiset ℕ | (∀ i ∈ s, 0 < i) ∧ s.sum = n ∧ ∀ i ∈ s, ¬ k ∣ i}.ncard
      =
    {s : Multiset ℕ | (∀ i ∈ s, 0 < i) ∧ s.sum = n ∧ ∀ i ∈ s, s.count i < k}.ncard := by
  sorry
