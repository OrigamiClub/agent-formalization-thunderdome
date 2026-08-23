# Glaisher's theorem — formalization notes (agent 11)

I represented "a partition of `n`" using Mathlib's built-in `Nat.Partition n`
type, whose `parts : Multiset ℕ` field records the parts with multiplicity
(`parts_pos` ensures all parts are positive, `parts_sum` ensures they sum to
`n`). Using a multiset means multiplicity of a part `i` is directly given by
`Multiset.count i p.parts`, which made both side conditions easy to state
without introducing a separate multiplicity function.

The "no part divisible by `k`" condition (set A_k) is `∀ i ∈ p.parts, ¬ k ∣ i`.
The "every part occurs fewer than `k` times" condition (set B_k) is
`∀ i, p.parts.count i < k`, quantified over all of `ℕ` rather than just over
`i ∈ p.parts` — this is harmless since `count i = 0 < k` automatically for
any `i` not actually appearing as a part (given `k ≥ 2 > 0`), so the two
phrasings are equivalent; I chose the all-`i` version because it reads more
directly as "no part is repeated `k` or more times."

I stated the theorem as a cardinality equality (`Nat.card` of the two
subtypes `{p : Nat.Partition n // ...}`) rather than as an explicit
bijection, since Glaisher's theorem is most commonly quoted as a counting
identity and `Nat.card` sidesteps needing to supply explicit
`Fintype`/`Decidable` instances (it is defined for arbitrary types and
correctly computes the size of a finite type, and `Nat.Partition n` is
already known to be finite in Mathlib). The hypothesis `k ≥ 2` is included
as an explicit premise `hk : 2 ≤ k`, matching the "fix an integer k ≥ 2"
condition in the informal statement; `k = 2` specializes to Euler's
odd-parts/distinct-parts theorem. I am not 100% certain of the exact field
names in Mathlib's `Nat.Partition` (I used `parts`, `parts_pos`,
`parts_sum` from memory), but the theorem statement itself only relies on
the `parts` field and `Multiset.count`/`Multiset.mem`, which I am confident
about.
