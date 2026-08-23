import Mathlib

/-
Glaisher's theorem.

We use Mathlib's `Nat.Partition n`, which represents a partition of `n` as a
structure bundling a multiset `parts : Multiset ℕ` together with proofs that
every part is positive and that the parts sum to `n`.

  A_k(n) = partitions of `n` none of whose parts is divisible by `k`
         : { p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i }

  B_k(n) = partitions of `n` in which every part value occurs strictly
           fewer than `k` times (i.e. at most `k - 1` times), where the
           multiplicity of a value `i` in the partition is the multiset
           count `p.parts.count i`
         : { p : Nat.Partition n // ∀ i, p.parts.count i < k }

We state Glaisher's theorem as an equality of `Nat.card` of these two
subtypes, for every `k ≥ 2` and every `n`. `Nat.card` is used rather than
`Fintype.card` so that we do not need to exhibit `Fintype`/`Decidable`
instances explicitly; both subtypes are in fact finite since
`Nat.Partition n` is finite for each `n`.
-/

theorem glaisher_agent04 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i} =
    Nat.card {p : Nat.Partition n // ∀ i, p.parts.count i < k} := by
  sorry
