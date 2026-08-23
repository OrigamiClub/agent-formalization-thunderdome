# Glaisher's theorem — formalization notes (agent 15)

I represented "a partition of `n`" using Mathlib's built-in `Nat.Partition n` structure,
which bundles a multiset `parts : Multiset ℕ` of positive naturals together with a proof
that `parts.sum = n`. This avoids re-deriving positivity/summation facts and lets me
directly reuse `Multiset.count` for multiplicities.

The condition "no part divisible by `k`" is encoded as `∀ i ∈ p.parts, ¬ k ∣ i`. The
condition "every part occurs fewer than `k` times" is encoded as
`∀ i ∈ p.parts, p.parts.count i < k`, using `Multiset.count` to get the multiplicity of
each part value within the partition's own multiset.

I stated the theorem as a cardinality equality — `Set.ncard` of the two subsets of
`Nat.Partition n` cut out by these predicates — rather than as an explicit bijection,
since a direct equality of counts is the more literal reading of "the number of
partitions ... equals the number of partitions ...". I used `Set.ncard` (rather than
`Finset.card`/`Nat.card`) so the statement does not depend on recalling whether Mathlib
supplies a `Fintype (Nat.Partition n)` instance; `Set.ncard` is defined for arbitrary
sets and agrees with the natural finite cardinality here since both sets are finite
subsets of the (finite) set of partitions of `n`. The hypothesis `2 ≤ k` encodes "fix an
integer k ≥ 2" from the problem statement.
