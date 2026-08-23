import Mathlib

open Multiset

/-- A partition of `n`, represented directly (not via `Nat.Partition`) as a multiset of
positive natural numbers ("parts") whose sum is `n`. Working with `Multiset ℕ` avoids
having to recall the exact field/lemma names of Mathlib's `Nat.Partition` API. -/
def IsPartition (n : ℕ) (μ : Multiset ℕ) : Prop :=
  (∀ x ∈ μ, 0 < x) ∧ μ.sum = n

/-- `A_k(n)`: partitions of `n` none of whose parts is divisible by `k`. -/
def NoMultipleParts (n k : ℕ) : Set (Multiset ℕ) :=
  {μ | IsPartition n μ ∧ ∀ x ∈ μ, ¬ k ∣ x}

/-- `B_k(n)`: partitions of `n` in which every distinct part occurs fewer than `k` times
(i.e. with multiplicity at most `k - 1`), using `Multiset.count` for the multiplicity of a
part. -/
def BoundedMultiplicityParts (n k : ℕ) : Set (Multiset ℕ) :=
  {μ | IsPartition n μ ∧ ∀ x ∈ μ, μ.count x < k}

/-- **Glaisher's theorem.** For every `k ≥ 2` and every `n`, the number of partitions of `n`
into parts not divisible by `k` equals the number of partitions of `n` in which no part is
repeated `k` or more times. Both sets are finite (parts are bounded by `n`, multisets sum to
`n`), so `Nat.card` (applied to the sets via the `Set → Type` coercion) faithfully reports
their cardinalities; the theorem is stated as an equality of these two cardinalities rather
than as an explicit bijection. The case `k = 2` recovers Euler's odd/distinct-parts theorem. -/
theorem glaisher_agent01 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card (NoMultipleParts n k) = Nat.card (BoundedMultiplicityParts n k) := by
  sorry
