# Glaisher's theorem — formalization notes (agent_02)

I represented a partition of `n` directly as a `Multiset ℕ`, `s`, subject to two
conditions: `∀ i ∈ s, 0 < i` (parts are positive) and `s.sum = n` (parts sum to
`n`). I deliberately avoided Mathlib's `Nat.Partition n` structure since I was
not fully confident of its exact field/API names, and a raw multiset predicate
is easy to state precisely and unambiguously.

"No part divisible by `k`" becomes `∀ i ∈ s, ¬ k ∣ i`, and "every part occurs
fewer than `k` times" becomes `∀ i ∈ s, s.count i < k`, using
`Multiset.count`. Both partition families are then defined as
`Set (Multiset ℕ)` via set-builder notation combining the base conditions with
the respective extra condition.

I stated the theorem as a cardinality equality, `Set.ncard` of the first set
equals `Set.ncard` of the second, rather than as an explicit bijection — this
mirrors the classical `A_k(n) = B_k(n)` phrasing and avoids having to write
down (and get right) the actual Glaisher bijection (repeatedly halving/
multiplying part counts by `k`) in the statement itself. `Set.ncard` is
well-defined (via `Nat.card`) without needing a separate finiteness proof to
state the theorem, which keeps the statement itself independent of any
finiteness lemmas. The hypothesis `k ≥ 2` is taken as an explicit argument
`hk : 2 ≤ k`, matching the theorem's standing assumption. The one Mathlib
identifier I was not 100% certain about is `Set.ncard` itself (as opposed to
`Nat.card` applied to the coerced subtype), but I believe it is the standard
Mathlib name for cardinality of a `Set` with junk value `0` on infinite sets.
