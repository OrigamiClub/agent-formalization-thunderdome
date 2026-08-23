# Glaisher's theorem — formalization notes (agent_19)

I represented "a partition of `n`" using Mathlib's `Nat.Partition n` structure, whose
field `parts : Multiset ℕ` holds the parts (each positive, by `parts_pos`) with
`parts.sum = n` (`parts_sum`). This is a standard, ready-made Mathlib representation
rather than a hand-rolled multiset type.

The two conditions are encoded directly on `p.parts`: "no part divisible by `k`" is
`∀ i ∈ p.parts, ¬ (k ∣ i)`, and "every part occurs fewer than `k` times" is
`∀ i ∈ p.parts, p.parts.count i < k`, using `Multiset.count` to get the multiplicity
of a given part value within the multiset.

I stated the theorem as an equality of cardinalities (`Nat.card`) of the two subtypes
`{p : Nat.Partition n // ...}` cut out by these predicates, rather than as an explicit
bijection, since `Nat.card` cleanly captures "same count" without committing to a
specific (and much harder to state/prove) bijective map. The hypothesis `k ≥ 2` is
included as `hk : 2 ≤ k` per the theorem's standard statement; for `k = 2` this
recovers Euler's odd-parts/distinct-parts theorem. I was not fully certain of the
exact field names `parts_pos`/`parts_sum` in current Mathlib, but `parts` and
`Multiset.count` are used correctly and are the load-bearing identifiers for the
statement itself.
