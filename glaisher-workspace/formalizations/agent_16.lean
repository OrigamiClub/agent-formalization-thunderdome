import Mathlib

/-
Glaisher's theorem.

We use Mathlib's `Nat.Partition n`, which represents a partition of `n` as a
structure bundling a multiset `parts : Multiset ℕ` together with proofs that
every element of `parts` is positive (`parts_pos`) and that `parts.sum = n`
(`parts_sum`). `Nat.Partition n` carries a `Fintype`/`DecidableEq` instance in
Mathlib (it is finite, since the parts are bounded by `n`), so we can count
partitions satisfying a predicate with `Finset.filter` over `Finset.univ` and
take `.card`.

* "No part of λ is divisible by k" is encoded as: for every `i ∈ p.parts`,
  `¬ k ∣ i`.
* "Every part occurs at most `k - 1` times" (equivalently, strictly fewer than
  `k` times) is encoded via the multiset multiplicity function
  `Multiset.count`: for every `i ∈ p.parts`, `p.parts.count i < k`.

We state Glaisher's theorem as an equality of `Finset.card`s of these two
filtered sets of partitions, for every `n : ℕ` and every `k ≥ 2`.
-/

theorem glaisher_agent16 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    (Finset.univ.filter
        (fun p : n.Partition => ∀ i ∈ p.parts, ¬ k ∣ i)).card
      =
    (Finset.univ.filter
        (fun p : n.Partition => ∀ i ∈ p.parts, p.parts.count i < k)).card := by
  sorry
