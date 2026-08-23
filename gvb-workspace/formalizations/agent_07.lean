import Mathlib

open Finset

/-- **Gilbert–Varshamov bound** (combinatorial / existential form).

If `q ≥ 2` is an alphabet size, `n ≥ 1` a block length, `d` with `1 ≤ d ≤ n`
a target minimum Hamming distance, and `M ≥ 1` satisfies the
Gilbert–Varshamov inequality

  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,

then there exists a code `C ⊆ (Fin n → Fin q)` (i.e. a set of codewords of
length `n` over an alphabet of size `q`) with `|C| = M` such that every two
distinct codewords of `C` have Hamming distance at least `d`. -/
theorem gvb_bound_agent07
    (q n d M : ℕ)
    (hq : 2 ≤ q)
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd2 : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
