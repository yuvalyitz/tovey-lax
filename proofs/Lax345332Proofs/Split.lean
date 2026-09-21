import Mathlib.Tactic
import Lax345332Proofs.Pad

/-!
# Splitting clauses and bounding occurrences

From an arbitrary CNF formula with `N` literal occurrences over variables below `V`, a
formula with at most three literals per clause in which every variable occurs at most
three times. The occurrence at position `p` of the variable `v` becomes the fresh variable
`w v p`; a clause is chained through link variables `z p`; and for every `v` the variables
`w v 0, …, w v (N-1)` are tied together by the cycle of implications `w v (p+1) → w v p`.
-/

namespace Lax345332Proofs.Split

open Lax345332.Construction Lax429075.CNF Lax345332Proofs.Pad

/-! ### Arithmetic of the numbering -/

theorem wv_mod {V v p : ℕ} (hv : v < V) : wv V v p % V = v := by
  rw [wv, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

theorem wv_div {V v p : ℕ} (hv : v < V) : wv V v p / V = p := by
  rw [wv, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, Nat.zero_add]

theorem wv_lt {V N v p : ℕ} (hv : v < V) (hp : p < N) : wv V v p < V * N := by
  have : (p + 1) * V ≤ N * V := Nat.mul_le_mul_right V hp
  rw [wv, Nat.mul_comm V N]; nlinarith

theorem wv_div_mod {V k : ℕ} : wv V (k % V) (k / V) = k := by
  rw [wv, Nat.mul_comm]; exact Nat.mod_add_div k V

theorem index_lt_foldr (C : Clause) : ∀ l ∈ C, l.index < C.foldr (fun l b => max (l.index + 1) b) 1 := by
  induction C with
  | nil => simp
  | cons a C ih =>
      intro l hl
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hl with rfl | h
      · omega
      · have := ih l h; omega

theorem index_lt_bound {F : Formula} {C : Clause} (hC : C ∈ F) {l : Literal} (hl : l ∈ C) :
    l.index < bound F := by
  induction F with
  | nil => simp at hC
  | cons D F ih =>
      simp only [bound]
      rcases List.mem_cons.mp hC with rfl | h
      · have := index_lt_foldr C l hl; omega
      · have := ih h; omega

end Lax345332Proofs.Split
