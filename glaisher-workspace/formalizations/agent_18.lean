import Mathlib

/-
Glaisher's theorem.

We represent a partition of `n` using Mathlib's `Nat.Partition n`, a structure
bundling a multiset `parts : Multiset ℕ` of positive naturals summing to `n`.

Given `k ≥ 2`:
* "no part divisible by `k`" is expressed as `∀ p ∈ c.parts, ¬ k ∣ p`.
* "every part occurs fewer than `k` times" is expressed via multiset
  multiplicity: `∀ p ∈ c.parts, c.parts.count p < k`.

We state the theorem as an equality of `Nat.card` of the two corresponding
subtypes of `Nat.Partition n` (both are in fact finite, since `Nat.Partition n`
itself is finite, so `Nat.card` agrees with the naive count).
-/

theorem glaisher_agent18 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {c : Nat.Partition n // ∀ p ∈ c.parts, ¬ (k ∣ p)} =
    Nat.card {c : Nat.Partition n // ∀ p ∈ c.parts, c.parts.count p < k} := by
  sorry
