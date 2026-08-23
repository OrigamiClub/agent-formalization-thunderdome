import Mathlib

/-!
Glaisher's theorem: for `k ≥ 2`, the number of partitions of `n` into parts none of
which is divisible by `k` equals the number of partitions of `n` in which every part
occurs fewer than `k` times.

We represent a partition of `n` explicitly, without using `Nat.Partition`, as a
`Multiset ℕ` all of whose elements are positive and which sums to `n`.
-/

/-- `s` is a partition of `n`: a multiset of positive naturals summing to `n`. -/
def IsPartition (n : ℕ) (s : Multiset ℕ) : Prop :=
  (∀ x ∈ s, 0 < x) ∧ s.sum = n

/-- Partitions of `n` into parts none of which is divisible by `k`. -/
def GlaisherA (k n : ℕ) : Set (Multiset ℕ) :=
  {s | IsPartition n s ∧ ∀ x ∈ s, ¬ k ∣ x}

/-- Partitions of `n` in which every (distinct) part occurs fewer than `k` times,
i.e. no part is repeated `k` or more times. -/
def GlaisherB (k n : ℕ) : Set (Multiset ℕ) :=
  {s | IsPartition n s ∧ ∀ x ∈ s, s.count x < k}

/-- Glaisher's theorem: for `k ≥ 2` and every `n`, the number of partitions of `n`
into parts not divisible by `k` equals the number of partitions of `n` in which
every part occurs at most `k - 1` times. Stated as an equality of cardinalities of
the two (finite, though finiteness is not asserted here) sets of partitions. -/
theorem glaisher_agent05 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card (GlaisherA k n) = Nat.card (GlaisherB k n) := by sorry
