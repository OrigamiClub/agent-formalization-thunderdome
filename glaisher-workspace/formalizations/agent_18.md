# Glaisher's theorem — formalization notes (agent 18)

I represented "a partition of n" using Mathlib's `Nat.Partition n` structure, which
bundles a multiset `parts : Multiset ℕ` of positive naturals with `parts.sum = n`.
The condition "no part divisible by k" is encoded as `∀ p ∈ c.parts, ¬ (k ∣ p)`,
directly quantifying over multiset membership. The condition "every part occurs
fewer than k times" is encoded via multiset multiplicity as
`∀ p ∈ c.parts, c.parts.count p < k`, i.e. each distinct value's count in the
parts multiset is strictly less than k (equivalently, at most k − 1 repetitions).

I stated the theorem as a `Nat.card` equality between the two corresponding
subtypes of `Nat.Partition n` (partitions satisfying the divisibility restriction
vs. partitions satisfying the multiplicity restriction), rather than as an
explicit bijection, since a cardinality statement is more directly comparable
across independently-produced formalizations and avoids committing to any
particular (and Glaisher's classical proof uses several) bijection construction.
I used `Nat.card` instead of `Fintype.card`/`Set.ncard` to sidestep needing an
explicit `Fintype`/`DecidablePred` instance for the subtype predicates in the
statement; since `Nat.Partition n` is itself finite, both subtypes are finite and
`Nat.card` coincides with their true cardinality. I added the hypothesis `2 ≤ k`
since the theorem is only meaningful (and only classically stated) for k ≥ 2; the
k = 2 case recovers Euler's odd-parts/distinct-parts theorem. I was not fully
certain of the exact field/lemma names in Mathlib's `Partition` API beyond
`parts`, `parts_pos`, and `parts_sum`, so I avoided relying on any named lemmas
about it beyond basic multiset membership and `Multiset.count`.
