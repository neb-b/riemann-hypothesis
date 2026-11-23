module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.RowRepOcc

theorem charLaws_of_tie (D : D7) (h : Formalism.MainNotions.SumRepresentations.tie0 D) : GlobalTheory.TypeLeaf.CharLaws D := fun w a χ χ' h1 h2 =>
  let H := h.1 w a a χ χ' 0 h1 h2
  ⟨H.2.2.2.1, H.2.2.2.2.1⟩

theorem isoLoc_one (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

theorem cuspidalStrongMultiplicityOne_of_analytic (D : D7) (h : Formalism.MainNotions.SumRepresentations.adm5 D) : GlobalTheory.TypeLeaf.MultOne D := by
  intro a π π' ha hloc
  have hp := h.1 [⟨a, π, 1⟩] [⟨a, π', 1⟩] (by simp [ha]) (by simp [ha])
    (Filter.Eventually.of_forall fun w => by rw [isoLoc_one, isoLoc_one, hloc w])
  rw [List.singleton_perm_singleton] at hp
  exact eq_of_heq (Formalism.BasicNotions.Part.mk.inj hp).2.1

theorem etaShift (D : D7) (h : Formalism.MainNotions.SumRepresentations.tie0 D) (τ : D.host.E →+* ℂ) :
    ∀ z ∈ D.naut.infG D.naut.etaTinv τ, ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) := by
  intro z hz
  obtain ⟨h1, h2⟩ := h.2.1.2.1 τ
  obtain ⟨c, hc⟩ := D.R.t_odd
  have hc' : (D.R.t : ℂ) = 2 * c + 1 := by exact_mod_cast hc
  rw [h2] at hz
  rcases h1 with e | e <;> rw [e] at hz <;> simp at hz <;> subst hz
  · exact ⟨-(c + 1), by push_cast; rw [hc']; ring⟩
  · exact ⟨-c, by push_cast; rw [hc']; ring⟩

theorem pointPar (D : D7) (hT : Formalism.MainNotions.SumRepresentations.tie0 D) (h5 : Formalism.MainNotions.SumRepresentations.adm5 D) : GlobalTheory.TypeLeaf.PointPar D :=
  GlobalTheory.TypeLeaf.pointPar_of_twist D
    (GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne D (charLaws_of_tie D hT) (cuspidalStrongMultiplicityOne_of_analytic D h5))
    hT.2.1.1.1 (etaShift D hT)

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

theorem mapRep_mapRep {Γ : Type} [Group Γ] {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {a : ℕ}
    (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) :
    mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  ext x i j
  simp [mapRep]

theorem coe_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ}
    (f : A →+* B) (ρ : Γ →* GL (Fin a) A) (x : Γ) :
    ((mapRep f ρ x : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) = ((ρ x : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f := by
  simp [mapRep]

theorem isSSRep_map {Γ : Type} [Group Γ] {K L : Type} [Field K] [CharZero K] [Field L] {a : ℕ}
    (f : K →+* L) (ρ : Γ →* GL (Fin a) K) (h : IsSSRep ρ) : IsSSRep (mapRep f ρ) := by
  letI : Algebra K L := f.toAlgebra
  exact ssAscent K L Γ a ρ h

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)


include A in
theorem charZero_Kf (i : N.Loc) : CharZero (Kf N i) :=
  (RingHom.charZero_iff (ϕ := A.iotaQ i) (A.iotaQ i).injective).2 inferInstance

theorem isRepOfSig_transport {i i' : N.Loc} (φ : N.O i' ≃+* N.O i) (hφc : Continuous φ)
    (hφι : ∀ z, iotaO N A i (φ z) = iotaO N A i' z) (Sig : List (Formalism.BasicNotions.Part A.CG))
    (ρ₀ : G H.E N.Om →* GL (Fin R.r) (N.O i')) (h : IsRepOfSig N A i' Sig ρ₀) :
    IsRepOfSig N A i Sig (mapRep φ.toRingHom ρ₀) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [coe_mapRep]
    exact h1.matrix_map hφc
  · haveI := charZero_Kf N A i'
    let ψ : Kf N i' ≃+* Kf N i := IsFractionRing.ringEquivOfRingEquiv φ
    have e : mapRep (algebraMap (N.O i) (Kf N i)) (mapRep φ.toRingHom ρ₀) =
        mapRep ψ.toRingHom (mapRep (algebraMap (N.O i') (Kf N i')) ρ₀) := by
      rw [mapRep_mapRep, mapRep_mapRep]
      congr 1
      ext z
      simp [ψ]
    rw [e]
    exact isSSRep_map ψ.toRingHom _ h2
  · refine h3.mono fun w hw B σ hB hσ => ?_
    rw [coe_mapRep, Matrix.charpoly_map, Polynomial.map_map]
    have : (iotaO N A i).comp φ.toRingHom = iotaO N A i' := by
      ext z
      exact hφι z
    rw [this]
    exact hw B σ hB hσ

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

end GlobalTheory.RowRepOcc
