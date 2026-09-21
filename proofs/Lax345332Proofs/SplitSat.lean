import Mathlib.Tactic
import Lax345332Proofs.Split

/-!
# Splitting preserves satisfiability
-/

namespace Lax345332Proofs.Split

open Lax345332.Construction Lax429075.CNF Lax345332Proofs.Pad

variable {V N : ℕ}

/-- The value of literal `i` of `C` under `ρ`. -/
def ev (ρ : Assignment) (C : Clause) (i : ℕ) : Bool := (C.getD i dflt).eval ρ

theorem any_take_succ (ρ : Assignment) (C : Clause) {i : ℕ} (hi : i < C.length) :
    ((C.take (i + 1)).any fun l => l.eval ρ) = (((C.take i).any fun l => l.eval ρ) || ev ρ C i) := by
  rw [List.take_add_one, List.any_append]
  simp [ev, List.getElem?_eq_getElem hi]

theorem any_take_length (ρ : Assignment) (C : Clause) :
    ((C.take C.length).any fun l => l.eval ρ) = C.any fun l => l.eval ρ := by
  rw [List.take_length]

/-- How `σ` reads the variables of one chain, relative to `ρ`. -/
structure Reads (σ ρ : Assignment) (V N o : ℕ) (C : Clause) : Prop where
  w : ∀ i < C.length, σ (wv V (C.getD i dflt).index (o + i)) = ρ (C.getD i dflt).index

theorem eval_lit (σ ρ : Assignment) (o : ℕ) (C : Clause) (h : Reads σ ρ V N o C) {i : ℕ}
    (hi : i < C.length) :
    (⟨wv V (C.getD i dflt).index (o + i), (C.getD i dflt).positive⟩ : Literal).eval σ = ev ρ C i := by
  have := h.w i hi
  simp only [Literal.eval, ev]
  rw [this]

theorem eval_chainClause (σ ρ : Assignment) (o : ℕ) (C : Clause) (h : Reads σ ρ V N o C) {i : ℕ}
    (hi : i < C.length) :
    ((chainClause V N o C i).any fun l => l.eval σ) =
      ((if i = 0 then false else !σ (zv V N (o + i - 1))) || ev ρ C i ||
        (if i + 1 = C.length then false else σ (zv V N (o + i)))) := by
  rw [chainClause, List.any_append, List.any_append]
  congr 1
  · congr 1
    · split_ifs <;> simp [Literal.eval]
    · simp only [List.any_cons, List.any_nil, Bool.or_false]; exact eval_lit σ ρ o C h hi
  · split_ifs <;> simp [Literal.eval]

/-! ### From the original formula to the split one -/

/-- The value of the link after literal `i`: no literal up to `i` is true. -/
def zval (ρ : Assignment) (C : Clause) (i : ℕ) : Bool := !((C.take (i + 1)).any fun l => l.eval ρ)

theorem chainClauses_true (σ ρ : Assignment) (o : ℕ) (C : Clause) (h : Reads σ ρ V N o C)
    (hz : ∀ i < C.length, σ (zv V N (o + i)) = zval ρ C i)
    (hC : (C.any fun l => l.eval ρ) = true) : eval (chainClauses V N o C) σ = true := by
  have hne : C.length ≠ 0 := by
    intro h0; rw [List.length_eq_zero_iff.mp h0] at hC; simp at hC
  rw [chainClauses, if_neg hne, eval_iff]
  intro D hD
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hD
  have hi := List.mem_range.mp hi
  rw [eval_chainClause σ ρ o C h hi]
  have hs := any_take_succ ρ C hi
  by_cases h0 : i = 0
  · subst h0
    simp only [List.take_zero, List.any_nil, Bool.false_or] at hs
    by_cases hl : 0 + 1 = C.length
    · have : (C.any fun l => l.eval ρ) = ev ρ C 0 := by
        rw [← any_take_length, ← hl, hs]
      simp [hl, ← this, hC]
    · have := hz 0 hi
      simp only [Nat.add_zero] at this
      simp [hl, this, zval, hs]
  · have hz1 := hz (i - 1) (by omega)
    have e : o + (i - 1) = o + i - 1 := by omega
    have e2 : i - 1 + 1 = i := by omega
    rw [e, zval, e2] at hz1
    by_cases hl : i + 1 = C.length
    · have : (C.any fun l => l.eval ρ) = (((C.take i).any fun l => l.eval ρ) || ev ρ C i) := by
        rw [← any_take_length, ← hl, hs]
      rw [this] at hC
      simp [h0, hl, hz1, hC]
    · have := hz i hi
      rw [zval, hs] at this
      simp only [h0, hl, if_false, hz1, this, Bool.not_not]
      cases ((C.take i).any fun l => l.eval ρ) <;> cases ev ρ C i <;> rfl

/-- The links of the whole formula, in order. -/
def zsOf (ρ : Assignment) (F : Formula) : List Bool :=
  F.flatMap fun C => (List.range C.length).map (zval ρ C)

/-- The assignment of the split formula built from `ρ`. -/
def lift (V N : ℕ) (ρ : Assignment) (zs : List Bool) : Assignment :=
  fun i => if i < V * N then ρ (i % V) else zs.getD (i - V * N) false

theorem lift_wv {ρ : Assignment} {zs : List Bool} {v p : ℕ} (hv : v < V) (hp : p < N) :
    lift V N ρ zs (wv V v p) = ρ v := by
  rw [lift, if_pos (wv_lt hv hp), wv_mod hv]

theorem lift_zv {ρ : Assignment} {zs : List Bool} {p : ℕ} :
    lift V N ρ zs (zv V N p) = zs.getD p false := by
  rw [lift, zv, if_neg (by omega), Nat.add_sub_cancel_left]

theorem chains_true (ρ : Assignment) (zs : List Bool) :
    ∀ (F : Formula) (o : ℕ), zs.drop o = zsOf ρ F → o + size F ≤ N →
      (∀ C ∈ F, ∀ l ∈ C, l.index < V) → eval F ρ = true →
      eval (chains V N o F) (lift V N ρ zs) = true := by
  intro F
  induction F with
  | nil => intro o _ _ _ _; rfl
  | cons C F ih =>
      intro o hd hsz hV hF
      rw [eval_cons, Bool.and_eq_true] at hF
      simp only [size, List.map_cons, List.sum_cons] at hsz
      simp only [zsOf, List.flatMap_cons] at hd
      rw [chains, eval_append, Bool.and_eq_true]
      constructor
      · apply chainClauses_true _ ρ o C ⟨fun i hi => ?_⟩ (fun i hi => ?_) hF.1
        · have hm : C.getD i dflt ∈ C := by
            rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
          exact lift_wv (hV C List.mem_cons_self _ hm) (by omega)
        · rw [lift_zv, List.getD_eq_getElem?_getD, ← List.getElem?_drop, hd,
            List.getElem?_append_left (by simpa using hi)]
          simp [hi]
      · apply ih (o + C.length) _ (by simp only [size]; omega)
          (fun D hD => hV D (List.mem_cons_of_mem _ hD)) hF.2
        have := congrArg (List.drop C.length) hd
        rw [List.drop_drop] at this
        rw [this, List.drop_append_of_le_length (by simp)]
        simp [zsOf]

end Lax345332Proofs.Split
