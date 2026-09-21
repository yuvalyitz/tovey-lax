import Mathlib.Tactic
import Lax345332Proofs.SplitSat

/-!
# The split formula is satisfiable exactly when the original is
-/

namespace Lax345332Proofs.Split

open Lax345332.Construction Lax429075.CNF Lax345332Proofs.Pad

variable {V N : ℕ}

theorem next_lt {p : ℕ} (hN : 0 < N) : next N p < N := by
  unfold next; split_ifs <;> omega

theorem cycles_true (ρ : Assignment) (zs : List Bool) :
    eval (cycles V N) (lift V N ρ zs) = true := by
  rw [eval_iff]
  intro D hD
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hD
  have hk := List.mem_range.mp hk
  have hV : 0 < V := Nat.pos_of_ne_zero fun h => by simp [h] at hk
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at hk
  have h1 : lift V N ρ zs k = ρ (k % V) := by rw [lift, if_pos hk]
  have h2 := lift_wv (ρ := ρ) (zs := zs) (Nat.mod_lt k hV) (next_lt (p := k / V) hN)
  simp only [List.any_cons, List.any_nil, Literal.eval, h1, h2]
  cases ρ (k % V) <;> rfl

theorem split_of_sat {F : Formula} {ρ : Assignment} (h : eval F ρ = true) :
    eval (split F) (lift (bound F) (size F) ρ (zsOf ρ F)) = true := by
  rw [split, eval_append, cycles_true, Bool.and_true]
  exact chains_true ρ _ F 0 (by simp) (by omega) (fun C hC l hl => index_lt_bound hC hl) h

/-! ### Back -/

theorem cycle_step {σ : Assignment} (h : eval (cycles V N) σ = true) {v p : ℕ} (hv : v < V)
    (hp : p < N) (hs : σ (wv V v (next N p)) = true) : σ (wv V v p) = true := by
  have hm : [(⟨wv V v p, true⟩ : Literal), ⟨wv V (wv V v p % V) (next N (wv V v p / V)), false⟩]
      ∈ cycles V N := List.mem_map.mpr ⟨_, List.mem_range.mpr (wv_lt hv hp), rfl⟩
  have := (eval_iff _ _).mp h _ hm
  rw [wv_mod hv, wv_div hv] at this
  simpa [Literal.eval, hs] using this

theorem cycle_const {σ : Assignment} (h : eval (cycles V N) σ = true) {v : ℕ} (hv : v < V) :
    ∀ p < N, σ (wv V v p) = σ (wv V v 0) := by
  have down : ∀ p, p < N → σ (wv V v p) = true → σ (wv V v 0) = true := by
    intro p
    induction p with
    | zero => intro _ h0; exact h0
    | succ p ih =>
        intro hp h1
        refine ih (by omega) (cycle_step h hv (by omega) ?_)
        rw [next, if_pos hp]; exact h1
  have top : ∀ d p, p + d + 1 = N → σ (wv V v (N - 1)) = true → σ (wv V v p) = true := by
    intro d
    induction d with
    | zero => intro p hp h1; have : p = N - 1 := by omega
              rw [this]; exact h1
    | succ d ih =>
        intro p hp h1
        refine cycle_step h hv (by omega) ?_
        rw [next, if_pos (by omega)]
        exact ih (p + 1) (by omega) h1
  intro p hp
  have wrap : σ (wv V v 0) = true → σ (wv V v (N - 1)) = true := fun h0 =>
    cycle_step h hv (by omega) (by rw [next, if_neg (by omega)]; exact h0)
  cases h1 : σ (wv V v p) <;> cases h0 : σ (wv V v 0) <;> try rfl
  · have := top (N - 1 - p) p (by omega) (wrap h0); rw [h1] at this; cases this
  · have := down p hp h1; rw [h0] at this; cases this

theorem chainClauses_sound {σ ρ : Assignment} {o : ℕ} {C : Clause} (h : Reads σ ρ V N o C)
    (he : eval (chainClauses V N o C) σ = true) : (C.any fun l => l.eval ρ) = true := by
  by_contra hno
  have hev : ∀ i < C.length, ev ρ C i = false := by
    intro i hi
    have hm : C.getD i dflt ∈ C := by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    simp only [Bool.not_eq_true, List.any_eq_false] at hno
    simpa [ev] using hno _ hm
  by_cases h0 : C.length = 0
  · rw [chainClauses, if_pos h0] at he; simp [eval] at he
  rw [chainClauses, if_neg h0, eval_iff] at he
  have hcl : ∀ i < C.length, ((if i = 0 then false else !σ (zv V N (o + i - 1))) ||
      (if i + 1 = C.length then false else σ (zv V N (o + i)))) = true := by
    intro i hi
    have := he _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    rw [eval_chainClause σ ρ o C h hi, hev i hi, Bool.or_false] at this
    exact this
  have key : ∀ i, i < C.length → i + 1 < C.length ∧ σ (zv V N (o + i)) = true := by
    intro i
    induction i with
    | zero =>
        intro hi
        have := hcl 0 hi
        by_cases hl : 0 + 1 = C.length
        · simp [hl] at this
        · simp only [hl, if_false, if_true, Bool.false_or, Nat.add_zero] at this
          exact ⟨by omega, this⟩
    | succ i ih =>
        intro hi
        have hp := ih (by omega)
        have := hcl (i + 1) hi
        have e : o + (i + 1) - 1 = o + i := by omega
        rw [e, hp.2] at this
        by_cases hl : i + 1 + 1 = C.length
        · simp [hl] at this
        · simp only [hl, if_false, Nat.succ_ne_zero, Bool.not_true, Bool.false_or] at this
          exact ⟨by omega, this⟩
  have := (key (C.length - 1) (by omega)).1
  omega

theorem chains_sound {σ ρ : Assignment} (hE : ∀ v < V, ∀ p < N, σ (wv V v p) = ρ v) :
    ∀ (F : Formula) (o : ℕ), eval (chains V N o F) σ = true → o + size F ≤ N →
      (∀ C ∈ F, ∀ l ∈ C, l.index < V) → eval F ρ = true := by
  intro F
  induction F with
  | nil => intro _ _ _ _; rfl
  | cons C F ih =>
      intro o he hsz hV
      simp only [size, List.map_cons, List.sum_cons] at hsz
      rw [chains, eval_append, Bool.and_eq_true] at he
      rw [eval_cons, Bool.and_eq_true]
      refine ⟨chainClauses_sound ⟨fun i hi => ?_⟩ he.1,
        ih (o + C.length) he.2 (by simp only [size]; omega)
          fun D hD => hV D (List.mem_cons_of_mem _ hD)⟩
      have hm : C.getD i dflt ∈ C := by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      exact hE _ (hV C List.mem_cons_self _ hm) _ (by omega)

theorem sat_of_split {F : Formula} {σ : Assignment} (h : eval (split F) σ = true) :
    eval F (fun v => σ (wv (bound F) v 0)) = true := by
  rw [split, eval_append, Bool.and_eq_true] at h
  exact chains_sound (fun v hv p hp => cycle_const h.2 hv p hp) F 0 h.1 (by omega)
    fun C hC l hl => index_lt_bound hC hl

theorem split_sat (F : Formula) : Satisfiable F ↔ Satisfiable (split F) :=
  ⟨fun ⟨_, h⟩ => ⟨_, split_of_sat h⟩, fun ⟨_, h⟩ => ⟨_, sat_of_split h⟩⟩

end Lax345332Proofs.Split
