module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecomposition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.RowRepAtGN

@[expose] public section

noncomputable section

namespace UpperTheory.GalN

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def GalAwayN (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)),
      Continuous (fun g => ((r g : GL (Fin a) (Qbar (D.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i)))) ∧
      ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
        RelW D.nd D.naut (D.naut.wdOf i r w) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

def IsStringRepN (D : D7) (i : D.nd.Loc) (p : Part D.naut.CG)
    (R : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i))) : Prop :=
  Continuous (fun g => ((R g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i)))) ∧ IsSSRep R ∧
    ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut
      (D.naut.wdOf i R w) (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2))

theorem strN' {D : D7} {i : D.nd.Loc} {p : Part D.naut.CG} {R : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i))}
    (h : IsStringRepN D i p R) : IsStringRepN D i p R := h

theorem unr_part {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {w : PlE H} :
    ∀ L : List (Part A.CG), A.unr (isoLoc N A L w) → ∀ p ∈ L, 1 ≤ p.d → A.unr (A.locG p.π w) := by
  intro L
  induction L with
  | nil =>
    intro _ _ hp _
    exact absurd hp List.not_mem_nil
  | cons q L ih =>
    intro hun p hp hd
    have h12 := (A.unr_sum (spehLoc N A q w) (isoLoc N A L w)).1 hun
    rcases List.mem_cons.1 hp with rfl | hp
    · have h := h12.1
      obtain ⟨d, hd'⟩ : ∃ d, p.d = d + 1 := ⟨p.d - 1, by omega⟩
      rw [GlobalTheory.StringDecomp.spehLoc_eq, hd', List.range_succ_eq_map, List.foldr_cons,
        A.unr_sum] at h
      exact (A.unr_tw (A.locG p.π w) _).1 h.1
    · exact ih h12.2 p hp hd

end UpperTheory.GalN
