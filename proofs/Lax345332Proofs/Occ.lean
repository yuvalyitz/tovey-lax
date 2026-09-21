import Lax345332.Construction

/-!
# Counting occurrences

`occurrences` over appends and `flatMap`s, and two bounds on a sum over a range whose
terms vanish away from one or two indices.
-/

namespace Lax345332Proofs.Occ

open Lax345332.Construction Lax429075.CNF Lax345332.ThreeFourSat

/-- The number of occurrences of the variable `i` in the clause `C`. -/
def cnt (C : Clause) (i : ℕ) : ℕ := (C.filter fun l => l.index == i).length

theorem occ_cons (C : Clause) (F : Formula) (i : ℕ) :
    occurrences (C :: F) i = cnt C i + occurrences F i := by
  simp [occurrences, cnt]

theorem occ_append (F G : Formula) (i : ℕ) :
    occurrences (F ++ G) i = occurrences F i + occurrences G i := by
  simp [occurrences, List.flatMap_append]

theorem occ_flatMap {α : Type} (l : List α) (f : α → Formula) (i : ℕ) :
    occurrences (l.flatMap f) i = (l.map fun a => occurrences (f a) i).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, occ_append, ih]; simp

theorem occ_map {α : Type} (l : List α) (f : α → Clause) (i : ℕ) :
    occurrences (l.map f) i = (l.map fun a => cnt (f a) i).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, occ_cons, ih]; simp

theorem sum_range_two_point (f : ℕ → ℕ) (k1 k2 a : ℕ) (n : ℕ)
    (h0 : ∀ k < n, k ≠ k1 → k ≠ k2 → f k = 0) (h1 : ∀ k < n, f k ≤ a) :
    ((List.range n).map f).sum ≤ (if k1 < n then a else 0) + (if k2 < n ∧ k2 ≠ k1 then a else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ih' := ih (fun k hk => h0 k (by omega)) (fun k hk => h1 k (by omega))
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      have hn := h1 n (by omega)
      by_cases e1 : n = k1
      · subst e1
        split_ifs at ih' ⊢ <;> omega
      · by_cases e2 : n = k2
        · subst e2
          split_ifs at ih' ⊢ <;> omega
        · have := h0 n (by omega) e1 e2
          split_ifs at ih' ⊢ <;> omega

theorem sum_range_le_two (f : ℕ → ℕ) (k1 k2 a n : ℕ)
    (h0 : ∀ k < n, k ≠ k1 → k ≠ k2 → f k = 0) (h1 : ∀ k < n, f k ≤ a) :
    ((List.range n).map f).sum ≤ 2 * a := by
  have := sum_range_two_point f k1 k2 a n h0 h1
  split_ifs at this <;> omega

theorem sum_range_le_one (f : ℕ → ℕ) (k1 a n : ℕ)
    (h0 : ∀ k < n, k ≠ k1 → f k = 0) (h1 : ∀ k < n, f k ≤ a) :
    ((List.range n).map f).sum ≤ a := by
  have := sum_range_two_point f k1 k1 a n (fun k hk e _ => h0 k hk e) h1
  split_ifs at this <;> omega

theorem sum_range_eq_zero (f : ℕ → ℕ) (n : ℕ) (h0 : ∀ k < n, f k = 0) :
    ((List.range n).map f).sum = 0 := by
  have := sum_range_le_one f 0 0 n (fun k hk _ => h0 k hk) (fun k hk => by rw [h0 k hk])
  omega

end Lax345332Proofs.Occ
