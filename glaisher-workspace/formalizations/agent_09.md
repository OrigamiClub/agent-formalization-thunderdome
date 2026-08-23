# Glaisher's theorem — formalization notes (agent 09)

I represented "a partition of n" using Mathlib's built-in `Nat.Partition n` structure, which
bundles a multiset `parts : Multiset ℕ` together with proofs that every part is positive
(`parts_pos`) and that the parts sum to `n` (`parts_sum`). This avoids re-deriving finiteness
and basic partition API from scratch.

The two side conditions are encoded directly on the underlying multiset: "no part divisible by
k" is `∀ j ∈ p.parts, ¬ (k ∣ j)`, and "every part occurs fewer than k times" is
`∀ j ∈ p.parts, Multiset.count j p.parts < k`, using `Multiset.count` to get the multiplicity of
each distinct part value within the multiset.

I stated the theorem as an equality of `Nat.card` applied to the two subtypes of `Nat.Partition n`
cut out by these predicates (rather than as an explicit bijection), since `Nat.card` sidesteps
needing an explicit `Fintype`/`DecidablePred` instance while still capturing "same number of
partitions of each kind." The statement is universally quantified over `k ≥ 2` and `n : ℕ`,
matching the general Glaisher theorem (of which Euler's odd/distinct-parts theorem is the k = 2
case). One simplification: I did not attempt to supply decidability/fintype instances explicitly,
trusting that Mathlib's classical/instance search would resolve them for the `Nat.card` statement
to type-check; I could not verify this compiles since no Lean compiler was available.
