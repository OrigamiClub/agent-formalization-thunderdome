# Glaisher's theorem — formalization notes (agent 03)

I represented a partition of `n` using Mathlib's `Nat.Partition n`, the structure with field
`parts : Multiset ℕ` (plus proofs `parts_pos` that all parts are positive and `parts_sum` that
they sum to `n`), rather than rolling my own multiset-of-positive-naturals type, since it is the
standard library representation and comes with the needed API (`Multiset.count`, membership,
etc.).

"No part divisible by k" is encoded as the predicate `∀ i ∈ p.parts, ¬ k ∣ i` on the underlying
multiset. "Every part occurs fewer than k times" is encoded via multiplicity as
`∀ i, p.parts.count i < k`, using `Multiset.count`; this is correct even for values `i` that don't
occur at all, since `count i = 0 < k` holds vacuously in that case, so the constraint only bites on
parts that actually appear in the partition.

I stated the theorem as an equality of `Nat.card` of the two subtypes `{p : Nat.Partition n // ...}`
cut out by these predicates, rather than as an explicit bijection, since `Nat.Partition n` is a
finite type for fixed `n` and `Nat.card` gives the correct finite count on these subtypes without
requiring me to construct/name a `Fintype` or `DecidablePred` instance explicitly. The hypothesis
`k ≥ 2` is included as an explicit argument, matching the "fix an integer k ≥ 2" premise; the
k = 2 case recovers Euler's odd/distinct-parts theorem. One identifier I was not 100% certain of
is the exact implicit/explicit argument shape of `Nat.Partition.parts_pos`, but it is unused in
the statement itself, so this does not affect the theorem as written.
