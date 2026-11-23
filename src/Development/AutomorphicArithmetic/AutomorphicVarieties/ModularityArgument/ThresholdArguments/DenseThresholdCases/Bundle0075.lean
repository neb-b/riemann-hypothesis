module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.AutNewform2A
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RROrdAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutNewformAOfEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0063
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.JPT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0074
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.EndoscopyRank2Ordinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0073
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0059
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelUFast
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutNewform2A
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.Gal.SV
namespace UpperTheory.V.Z.Win.RR
theorem ordAway_a_alt : _root_.UpperTheory.V.Af.HypothesesH' → Sd.OrdAway := fun P => _root_.UpperTheory.V.Z.Win.RR.ordAway_of_alt (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) gd P
theorem ordAbove_of_printsH : _root_.UpperTheory.V.Af.HypothesesH' → Sd.OrdAbove := fun P => _root_.UpperTheory.V.Z.Win.RR.ordAbove_of_alt (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) gd P
theorem autNewformA_of_printsH_of_repNewAE : _root_.UpperTheory.V.Af.HypothesesH' → Br.RepNewAE → AutNewformA := fun P =>
  _root_.UpperTheory.V.Z.Win.RR.autNewformA_of_exRS_of_compatT_of_repNewAE (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) (compatTOf (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) plainRec) P
end UpperTheory.V.Z.Win.RR
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthAwChain
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd GlobalTheory.CuspRep GlobalTheory.GalOfCusp Formalism.ConjugateSelfDual ReciprocityTheory.Gal
private theorem contTwist {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {n : ℕ} {r : Γ →* GL (Fin n) k} {χ : Γ →* kˣ} (hr : Continuous r) (hχ : Continuous χ) :
    Continuous (tw r χ) := by
  have h : Continuous fun s => ((tw r χ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    simp only [tw_val]
    exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hr)
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  have e : (fun s => (((tw r χ s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      (fun s => ((tw r χ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ∘ fun s => s⁻¹ := by
    funext s
    simp only [Function.comp_apply, map_inv]
  rw [e]
  exact h.comp continuous_inv
theorem UpperTheory.V.Z.Win.Birth.awChain_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Win.Birth.AwChain := by
  intro hH F E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE l _ ι r κ hr hPR hκ hirr
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  haveI : Fact ((2 : ℕ) = 2) := ⟨rfl⟩
  have hirrE : IsIrr (r.comp (galEmb F E Ω)) :=
    ⟨hirr.1, fun _ _ _ => Submodule.mem_top, fun W hW hI => hirr.2.2 W hW fun g v hv => hI (galEmb E M Ω g) v hv⟩
  have hW := UpperTheory.V.Z.Win.Birth.awReal F E Ω hE l ι r hr hirrE hPR
  have hcE : Continuous (r.comp (galEmb F E Ω)) := hr.comp (continuous_restrictScalarsHom F E Ω)
  obtain ⟨π, hreg, hatt, -⟩ := hPR
  have hAut : IsAutC ι (r.comp (galEmb F E Ω)) :=
    _root_.UpperTheory.V.Sd.up_quad_of_printed_results hH.toClassicalTheorems F E Ω l ι hE 2 one_le_two r hr ⟨π, hreg, hatt⟩ hirrE
  have hTw := UpperTheory.V.Z.Win.Birth.awTw E Ω l 2 le_rfl ι _ κ hκ hAut hW
  have hAutT := _root_.UpperTheory.V.Sd.twist_conjugate_selfDual hH.toClassicalTheorems E Ω l ι 2 _ κ hκ hAut
  have e2 : (tw (r.comp (galEmb F E Ω)) κ).comp (galEmb E M Ω) =
      tw ((r.comp (galEmb F E Ω)).comp (galEmb E M Ω)) (κ.comp (galEmb E M Ω)) := rfl
  have hirrT : IsIrr ((tw (r.comp (galEmb F E Ω)) κ).comp (galEmb E M Ω)) :=
    e2 ▸ (shapeFacts l _ 2 _ _).2.2.2.2.2 hirr
  exact UpperTheory.V.Z.Win.Birth.awUp (_root_.UpperTheory.V.Z.Bc.upCyc_of_alt hH.toClassicalTheorems hH.cyc) E M Ω l ι 2 le_rfl _
    (contTwist hcE hκ.1) hAutT hirrT hTw
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckePolyCoeffZero
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
theorem UpperTheory.V.Hi.hecke_ideal_point_properties :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → B.PointTheoremBaseObject ι J :=
  fun PH => _root_.UpperTheory.V.Z.Desc.W.twisted_point_property_of_isJ_arith_rep_autCsd PH PH.descU
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JEndOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
theorem UpperTheory.Gal.projectedFormsSystemPart.arithPointDecomposition_and_irrAutomorphic_of_isJ (hL : _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.Gal.projectedFormsSystemPart.PartLinkAlt) :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ArithmeticPointDecomposition B ι J ∧ IrrArithPointsAutomorphicAway B ι J :=
  fun H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K hS J hJ =>
    ⟨_root_.UpperTheory.V.Hi.arithmeticPointDecomposition_of_isJ H l L Ω s n hn V Q c r ι B Λ R K hS J hJ,
      _root_.UpperTheory.Gal.projectedFormsSystemPart.irrArithPointsAutomorphicAway_of_isJ H (hL H) (_root_.UpperTheory.V.Z.Ord.conj_torsion_of_printed_results H.toClassicalTheorems) (_root_.UpperTheory.V.Z.Ord.endOrd_of_printsH H) (_root_.UpperTheory.V.Z.Ord.born_j_of_printed_polarization_window H.toClassicalTheorems ImaginaryQuadraticEtaCharacter.winOf) l L Ω s n hn V Q c r ι B Λ R K hS J hJ⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLevelU
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
open UpperTheory.V.Hi.LvR
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance 2000] UpperTheory.V.W.coefLocal
theorem UpperTheory.V.Hi.level_of_is_j_unitary_hecke_data :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → _root_.UpperTheory.V.Pa.LevelAlt B J :=
  _root_.UpperTheory.V.Hi.level_of_isJ_unitaryHeckeData
end
end

