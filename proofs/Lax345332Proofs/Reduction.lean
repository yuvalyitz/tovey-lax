import Lax345332Proofs.Transform
import Lax429075.SATHard
import Lax429075.EncodingCorrect
import Lax429075Proofs.DecoderSoundness
import Lax434930Proofs.PolynomialComposition

/-!
# The reduction on words

A word that encodes a formula `F` is sent to the encoding of `transform F`; any other word
is sent to the image of the unsatisfiable formula with one empty clause.
-/

namespace Lax345332Proofs.Reduction

open Lax345332.Construction Lax429075.CNF Lax429075.Encoding Lax429075.Satisfiability Lax429075.Reductions
open Lax434930.PolynomialTime Lax345332.ThreeFourSat Lax345332Proofs.Transform

theorem not_sat_empty_clause : ¬ Satisfiable [[]] := by
  rintro ⟨ρ, h⟩; simp [eval] at h

theorem encodeCNF_inj {F G : Formula} (h : encodeCNF F = encodeCNF G) : F = G := by
  have h1 := Lax429075.EncodingCorrect.roundtrip F
  rw [h, Lax429075.EncodingCorrect.roundtrip G] at h1
  exact (Option.some.inj h1).symm

/-- Polynomial-time many-one reductions compose. -/
theorem manyOne_trans {A B C : Language} (hAB : ManyOne A B) (hBC : ManyOne B C) :
    ManyOne A C := by
  obtain ⟨f, ⟨hf⟩, hfc⟩ := hAB
  obtain ⟨g, ⟨hg⟩, hgc⟩ := hBC
  refine ⟨g ∘ f, Lax434930Proofs.PolynomialComposition.comp hf hg, fun x => ?_⟩
  rw [hfc x, hgc (f x)]
  rfl

/--
---
conclusion: Lax345332.Construction.reduce_correct
---
The encoding is injective and a decoded word is the encoding of what it decodes to, so the
statement is that of the reduction on formulas; a word that encodes nothing is sent to the
image of an unsatisfiable formula.
-/
theorem reduce_correct (w : Word) : w ∈ SAT ↔ reduce w ∈ SAT34 := by
  constructor
  · rintro ⟨F, rfl, hsat⟩
    have : parseF (encodeCNF F) = F := by
      rw [parseF, Lax429075.EncodingCorrect.roundtrip]; rfl
    exact ⟨transform F, by rw [reduce, this], Lax345332Proofs.Transform.transform_isThreeFour F,
      (Lax345332Proofs.Transform.transform_sat F).mp hsat⟩
  · rintro ⟨G, hG, -, hsat⟩
    have hGe : G = transform (parseF w) := encodeCNF_inj hG
    rw [hGe, ← Lax345332Proofs.Transform.transform_sat] at hsat
    cases hd : decodeCNF w with
    | none => rw [parseF, hd] at hsat; exact absurd hsat not_sat_empty_clause
    | some F =>
        rw [parseF, hd] at hsat
        exact ⟨F, Lax429075Proofs.decode_cnf_sound w F hd, hsat⟩

/--
---
conclusion: Lax345332.ThreeFourSat.npHard
---
Satisfiability is NP-hard by the Cook–Levin theorem, the reduction is correct and runs in
polynomial time, and polynomial-time many-one reductions compose.
-/
theorem npHard :
    ∀ A : Language, A ∈ Lax434930.NondeterministicPolynomialTime.NP → ManyOne A SAT34 :=
  fun A hA => manyOne_trans (Lax429075.SATHard.hardness A hA)
    ⟨reduce, Lax345332.Construction.reduce_polyTime, reduce_correct⟩

end Lax345332Proofs.Reduction
