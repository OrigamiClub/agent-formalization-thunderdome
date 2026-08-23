# Glaisher's theorem — agent_07

I represented a "partition of `n`" using Mathlib's `Nat.Partition n`, a structure with
field `parts : Multiset ℕ` (plus proofs that all parts are positive and sum to `n`).
Since `Nat.Partition n` has a `Fintype` instance, the two subtypes below are finite and
`Nat.card` computes their true cardinalities. "No part divisible by `k`" is encoded as
`∀ i ∈ p.parts, ¬ k ∣ i`; "every part occurs fewer than `k` times" is encoded via
`Multiset.count` as `∀ i ∈ p.parts, p.parts.count i < k` (multiplicity strictly less
than `k`, i.e. at most `k − 1` repetitions). I stated the theorem as a `Nat.card`
equality between the two subtypes of `Nat.Partition n`, for all `k ≥ 2` and all `n`,
rather than as an explicit bijection, since that is the more direct/faithful reading
of "the number of partitions ... equals the number of partitions ...". The only
identifiers I was not 100% certain of are the exact field name `parts` on
`Nat.Partition` and the dot-notation `n.Partition` for `Nat.Partition n`, both of
which I believe are correct per Mathlib's `Mathlib.Combinatorics.Enumerative.Partition`.
