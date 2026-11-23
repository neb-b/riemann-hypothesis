module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0026
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0969
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0322

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.IsUnitaryCharInv
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL

namespace UpperTheory.Gal.TP.Loc

theorem isUnitaryChar_mul {G : Type} [Group G] {a b : G →* ℂˣ} (ha : IsUnitaryChar a) (hb : IsUnitaryChar b) :
    IsUnitaryChar (a * b) := fun g => by
  simp [MonoidHom.mul_apply, ha g, hb g]

theorem isUnitaryChar_inv {G : Type} [Group G] {a : G →* ℂˣ} (ha : IsUnitaryChar a) : IsUnitaryChar a⁻¹ := fun g => by
  simp [ha g]

theorem liftIso_of (hP : PairOfLift) (hS : SrcGood) (hI : ContraIrr) (hU : ContraUnit) : LiftIso := by
  intro k _ _ _ _ n t ν b V _ _ W _ _ σ π hnt sν uν sb ub hs hi hu hs' hi' hL
  obtain ⟨a1, a2, a3⟩ := hS k n (ν * b) V σ (sν.mul sb) (isUnitaryChar_mul uν ub) hs hi hu
  exact GlobalTheory.T.theta_lift_general_linear GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible
    k n t b⁻¹ _ _ (contra (src (ν * b) σ)) (contra π) hnt sb.inv (isUnitaryChar_inv ub) (isSmooth_contra _)
    (hI k n V _ a1 a2).1 (hU k n V _ a1 a2 a3).1 (isSmooth_contra _) (hI k _ W π hs' hi').1
    (hP k n (n + t) ν b V W σ π sν sb hs' hL)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem liftSat_of (hL : LiftIso) (hS : SrcGood) (hI : ContraIrr) (hU : ContraUnit) (hC : SatContra) (hT : SatTwist)
    (hV : SatInvT) (hD : SatDet) (hP : SatProd) (hG : SegInv) : LiftSat := by
  intro K _ _ w n d ν b V _ _ W _ _ σ π hd nν uν nb ub hs hi hu hs' hi' hl ϖ hϖ B hB
  obtain ⟨t, rfl⟩ : ∃ t, d = n + t := ⟨d - n, by omega⟩
  have sν := isSmoothChar_of_isUnram nν
  have sb := isSmoothChar_of_isUnram nb
  obtain ⟨e⟩ := hL _ n t ν b V W σ π (by omega) sν uν sb ub hs hi hu hs' hi' hl
  obtain ⟨a1, a2, a3⟩ := hS _ n (ν * b) V σ (sν.mul sb) (isUnitaryChar_mul uν ub) hs hi hu
  have nm : IsUnram (ν * b) := fun x hx => by rw [MonoidHom.mul_apply, nν x hx, nb x hx, one_mul]
  have ni : IsUnram b⁻¹ := fun x hx => by rw [MonoidHom.inv_apply, nb x hx, inv_one]
  have s1 : GlobalTheory.LFun.HasSatGL w (src (ν * b) σ) ((B.map (·⁻¹)).map (· * (ν * b) ϖ)) :=
    hT K w n (ν * b) V _ nm ϖ hϖ _ (hV K w n V σ B hB)
  have s2 := hC K w n V _ a1 a2 a3 _ s1
  have s3 := hD K w t b⁻¹ ni ϖ hϖ
  have ud : IsUnitarisable (detRep (Fin t) b⁻¹) := (isUnitarisable_ofChar_iff _).2 fun _ => isUnitaryChar_inv ub _
  set_option synthInstance.maxHeartbeats 200000 in
  have s4 := hP K w n t _ _ _ _ (isSmooth_contra _) (hI _ n V _ a1 a2).1
    ((isSmooth_ofChar_iff _).2 sb.inv.detChar) (isIrreducible_ofChar _) _ _ s2 s3
  have s5 := GlobalTheory.PrinSat.hasSatGL_of_equiv e s4
  have u5 : IsUnitarisable (contra π) :=
    GlobalTheory.GenericUnitary.isUnitarisable_of_equiv e.symm (GlobalTheory.SmGL.UnitInd.isUnitarisable_prod₂ (hU _ n V _ a1 a2 a3).1 ud)
  have s6 := hC K w (n + t) _ _ (isSmooth_contra π) (hI _ _ W π hs' hi').1 u5 _ s5
  obtain ⟨e'⟩ := (hI _ _ W π hs' hi').2
  have s7 := GlobalTheory.PrinSat.hasSatGL_of_equiv e' s6
  rw [Multiset.map_add (f := _), hG] at s7
  simpa [Multiset.map_map, mul_comm] using s7

end UpperTheory.Gal.TP.Loc

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LiftSatUPf
section
open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.liftSatU :
    UpperTheory.Gal.TP.Loc.PairSat → UpperTheory.Gal.TP.Loc.CompUnit → UpperTheory.Gal.TP.Loc.LiftSatU := by
  intro hPS hCU E _ _ _ n d hnd Bs χX χW mX mW lam U U' hU hL w hw hX hW B hB
  obtain ⟨v, hvw⟩ : ∃ v, w.under (𝓞 (maximalRealSubfield E)) = v := ⟨_, rfl⟩
  have hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v := by
    obtain ⟨u, hne, hu⟩ := id hw
    subst hvw
    exact ⟨w, u, hne.symm, rfl, congrArg HeightOneSpectrum.asIdeal hu⟩
  obtain ⟨t, rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.GalOfCusp.isCMExt_real E) hv hvw
  obtain ⟨τ, hτ, hs⟩ := hB
  obtain ⟨⟨τ', hτ'⟩, -⟩ := GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E d U' hL.aut _ hw
  exact ⟨τ', hτ', hPS E n d hnd v t χX χW τ τ' (hL.loc v t τ τ' hτ hτ')
    (hCU E n U hU _ hw τ hτ) hX hW B hs⟩
end

