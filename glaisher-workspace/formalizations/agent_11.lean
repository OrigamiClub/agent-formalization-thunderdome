import Mathlib

open Nat

/-!
Glaisher's theorem.

Representation of "a partition of `n`": we use Mathlib's `Nat.Partition n`,
a structure with field `parts : Multiset ℕ` satisfying `parts_pos`
(every part is positive) and `parts_sum : parts.sum = n`. Multiplicities
are tracked by the multiset structure itself (a part `i` occurring `m`
times has `p.parts.count i = m`).

- "No part of `p` is divisible by `k`" is encoded as
  `∀ i ∈ p.parts, ¬ k ∣ i`.
- "Every part occurs fewer than `k` times" (i.e. at most `k - 1` times) is
  encoded as `∀ i, p.parts.count i < k`. Note this is stated for *all*
  naturals `i`, not just `i ∈ p.parts`: for `i ∉ p.parts` we have
  `p.parts.count i = 0 < k` automatically (since `k ≥ 2`), so the
  quantifier over all `i` is equivalent to quantifying only over the
  parts that actually occur.

We state the theorem as an equality of cardinalities (`Nat.card`) of the
two subtypes of `Nat.Partition n` cut out by these predicates, rather than
as an explicit bijection. `Nat.card` is used (instead of `Fintype.card`)
so that we do not have to separately supply/derive `Fintype`/`Decidable`
instances for the subtypes; `Nat.Partition n` is itself a finite type in
Mathlib, so both subtypes are finite and `Nat.card` computes their actual
sizes.
-/

/-- **Glaisher's theorem.** Fix `k ≥ 2`. For every `n`, the number of
partitions of `n` with no part divisible by `k` equals the number of
partitions of `n` in which every part occurs fewer than `k` times
(equivalently, at most `k - 1` times). The case `k = 2` is Euler's
theorem: partitions into odd parts biject with partitions into distinct
parts. -/
theorem glaisher_agent11 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i} =
      Nat.card {p : Nat.Partition n // ∀ i, p.parts.count i < k} := by
  sorry
