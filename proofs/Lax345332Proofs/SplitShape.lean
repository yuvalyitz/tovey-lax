import Mathlib.Tactic
import Lax345332Proofs.SplitSound
import Lax345332Proofs.PadOcc

/-!
# The shape of the split formula

Clauses of at most three literals, variables below `V * N + N`, and at most three
occurrences of each variable.
-/

namespace Lax345332Proofs.Split

open Lax345332.Construction Lax429075.CNF Lax345332.ThreeFourSat Lax345332Proofs.Occ Lax345332Proofs.Pad

variable {V N : ℕ}

theorem cnt_single (l : Literal) (j : ℕ) : cnt [l] j = if l.index = j then 1 else 0 := by
  by_cases h : l.index = j <;> simp [cnt, h]

theorem cnt_chainClause (o : ℕ) (C : Clause) (i j : ℕ) :
    cnt (chainClause V N o C i) j =
      (if i ≠ 0 ∧ zv V N (o + i - 1) = j then 1 else 0) +
      (if wv V (C.getD i dflt).index (o + i) = j then 1 else 0) +
      (if i + 1 ≠ C.length ∧ zv V N (o + i) = j then 1 else 0) := by
  rw [chainClause, cnt_append, cnt_append, cnt_single]
  congr 1
  · congr 1
    by_cases h : i = 0 <;> simp [h, cnt_single, show cnt [] j = 0 from rfl]
  · by_cases h : i + 1 = C.length <;> simp [h, cnt_single, show cnt [] j = 0 from rfl]

theorem getD_mem {C : Clause} {i : ℕ} (hi : i < C.length) : C.getD i dflt ∈ C := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

/-- The position a variable belongs to. -/
def pos (V N j : ℕ) : ℕ := if j < V * N then j / V else j - V * N

theorem chainClauses_occ (o : ℕ) (C : Clause) (j : ℕ) (ho : o + C.length ≤ N)
    (hV : ∀ l ∈ C, l.index < V) :
    occurrences (chainClauses V N o C) j ≤ 2 ∧
      (pos V N j < o ∨ o + C.length ≤ pos V N j → occurrences (chainClauses V N o C) j = 0) := by
  by_cases h0 : C.length = 0
  · rw [chainClauses, if_pos h0]; simp [occurrences]
  rw [chainClauses, if_neg h0, occ_map]
  simp only [cnt_chainClause]
  have hw : ∀ i < C.length, wv V (C.getD i dflt).index (o + i) < V * N ∧
      wv V (C.getD i dflt).index (o + i) / V = o + i := fun i hi =>
    ⟨wv_lt (hV _ (getD_mem hi)) (by omega), wv_div (hV _ (getD_mem hi))⟩
  by_cases hj : j < V * N
  · have hp : pos V N j = j / V := by rw [pos, if_pos hj]
    have hterm : ∀ i < C.length, i ≠ j / V - o ∨ j / V < o →
        ((if i ≠ 0 ∧ zv V N (o + i - 1) = j then 1 else 0) +
        (if wv V (C.getD i dflt).index (o + i) = j then 1 else 0) +
        (if i + 1 ≠ C.length ∧ zv V N (o + i) = j then 1 else 0)) = 0 := by
      intro i hi hne
      have := (hw i hi).2
      rw [if_neg (by unfold zv; omega), if_neg (by intro e; rw [e] at this; omega),
        if_neg (by unfold zv; omega)]
    constructor
    · refine le_trans (sum_range_le_one _ (j / V - o) 1 _ (fun i hi hne => hterm i hi (Or.inl hne))
        fun i hi => ?_) (by omega)
      have hz1 : ¬ (i ≠ 0 ∧ zv V N (o + i - 1) = j) := by unfold zv; omega
      have hz2 : ¬ (i + 1 ≠ C.length ∧ zv V N (o + i) = j) := by unfold zv; omega
      rw [if_neg hz1, if_neg hz2]
      split_ifs <;> omega
    · intro hout
      apply sum_range_eq_zero
      intro i hi
      apply hterm i hi
      rw [hp] at hout; omega
  · have hp : pos V N j = j - V * N := by rw [pos, if_neg hj]
    have hwz : ∀ i < C.length, ¬ wv V (C.getD i dflt).index (o + i) = j := fun i hi e => by
      have := (hw i hi).1; omega
    constructor
    · refine le_trans (sum_range_le_two _ (j - V * N - o) (j - V * N - o + 1) 1 _ ?_ ?_) (by omega)
      · intro i hi h1 h2
        rw [if_neg (hwz i hi), if_neg (by unfold zv; omega), if_neg (by unfold zv; omega)]
      · intro i hi
        rw [if_neg (hwz i hi)]
        unfold zv
        split_ifs <;> omega
    · intro hout
      apply sum_range_eq_zero
      intro i hi
      rw [if_neg (hwz i hi), if_neg (by unfold zv; omega), if_neg (by unfold zv; omega)]

theorem chains_occ (j : ℕ) : ∀ (F : Formula) (o : ℕ), o + size F ≤ N →
    (∀ C ∈ F, ∀ l ∈ C, l.index < V) →
    occurrences (chains V N o F) j ≤ 2 ∧
      (pos V N j < o ∨ o + size F ≤ pos V N j → occurrences (chains V N o F) j = 0) := by
  intro F
  induction F with
  | nil => intro o _ _; simp [chains, occurrences]
  | cons C F ih =>
      intro o hsz hV
      simp only [size, List.map_cons, List.sum_cons] at hsz ⊢
      have hA := chainClauses_occ (V := V) (N := N) o C j (by omega) (hV C List.mem_cons_self)
      have hR := ih (o + C.length) (by simp only [size]; omega)
        fun D hD => hV D (List.mem_cons_of_mem _ hD)
      simp only [size] at hR
      rw [chains, occ_append]
      constructor
      · by_cases h : pos V N j < o + C.length
        · have := hR.2 (Or.inl h); omega
        · have := hA.2 (Or.inr (by omega)); omega
      · intro hout
        have h1 := hA.2 (by omega)
        have h2 := hR.2 (by omega)
        omega

theorem cycles_occ (j : ℕ) : occurrences (cycles V N) j ≤ 2 := by
  rw [cycles, occ_map]
  have e : (fun k => cnt [(⟨k, true⟩ : Literal), ⟨wv V (k % V) (next N (k / V)), false⟩] j) =
      fun k => (if k = j then 1 else 0) + (if wv V (k % V) (next N (k / V)) = j then 1 else 0) := by
    funext k
    rw [show [(⟨k, true⟩ : Literal), ⟨wv V (k % V) (next N (k / V)), false⟩] =
      [⟨k, true⟩] ++ [⟨wv V (k % V) (next N (k / V)), false⟩] from rfl, cnt_append, cnt_single,
      cnt_single]
  rw [e, List.sum_map_add]
  have h1 := sum_range_le_one (fun k => if k = j then 1 else 0) j 1 (V * N)
    (fun k _ hne => if_neg hne) (fun k _ => by split_ifs <;> omega)
  have h2 := sum_range_le_one (fun k => if wv V (k % V) (next N (k / V)) = j then 1 else 0)
    (wv V (j % V) (if j / V = 0 then N - 1 else j / V - 1)) 1 (V * N)
    (fun k hk hne => by
      have hVp : 0 < V := Nat.pos_of_ne_zero fun h => by simp [h] at hk
      have hkN : k / V < N := Nat.div_lt_of_lt_mul hk
      rw [if_neg]
      intro e
      apply hne
      have hm : k % V = j % V := by rw [← e, wv_mod (Nat.mod_lt k hVp)]
      have hd : next N (k / V) = j / V := by rw [← e, wv_div (Nat.mod_lt k hVp)]
      have hq : k / V = if j / V = 0 then N - 1 else j / V - 1 := by
        clear hne e hm
        generalize k / V = a at *
        generalize j / V = b at *
        unfold next at hd
        split_ifs at hd ⊢ <;> omega
      rw [← hm, ← hq, wv_div_mod])
    (fun k _ => by split_ifs <;> omega)
  omega

theorem split_occ (F : Formula) (j : ℕ) : occurrences (split F) j ≤ 4 := by
  rw [split, occ_append]
  have h1 := (chains_occ (V := bound F) (N := size F) j F 0 (by omega)
    fun C hC l hl => index_lt_bound hC hl).1
  have h2 := cycles_occ (V := bound F) (N := size F) j
  omega

end Lax345332Proofs.Split
