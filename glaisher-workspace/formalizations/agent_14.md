# Glaisher's theorem — formalization notes (agent 14)

I represent "a partition of `n`" via Mathlib's `Nat.Partition n`, whose underlying data is a
multiset `parts : Multiset ℕ` of positive naturals summing to `n` (I did not re-derive partitions
from scratch as raw multisets, trusting the existing Mathlib structure and its `parts` field).

The condition "no part is divisible by `k`" is stated as `∀ j ∈ p.parts, ¬ k ∣ j`, quantifying
over elements of the parts multiset directly. The condition "every part occurs fewer than `k`
times" is stated as `∀ j ∈ p.parts, Multiset.count j p.parts < k`, using `Multiset.count` to get
the multiplicity of each occurring value within the same multiset (rather than introducing a
separate multiplicity function).

I stated the theorem as an equality of `Set.ncard` cardinalities of the two subsets of
`Nat.Partition n` cut out by these predicates, universally quantified over `n : ℕ`, with the
hypothesis `2 ≤ k` fixed once as a parameter of the theorem (matching the "fix an integer k ≥ 2"
framing). I chose the cardinality-equality form over an explicit-bijection statement since it is
the more direct/literal reading of "the number of partitions ... equals the number of partitions
...". I used `Set.ncard` rather than `Finset.card` to avoid committing to a particular `Fintype`
instance/decidability setup for these subsets, since `Set.ncard` is defined for arbitrary sets
(and correctly reduces to the finite cardinality when the set is finite, as it is here). I was
fairly confident about `Nat.Partition`, its `parts` field, and `Multiset.count`, but did not have
a compiler available to confirm exact naming/typeclass details.
