module

public import Mathlib
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsIsWeilDatumOF
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsIsUWeilPairCm
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0002

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace PositivityTheory.ThKW.S

theorem exists_isWeil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW M hM χX χW hcX hcW rX rW
  obtain ⟨ξ₀, hξ, hσξ⟩ := _root_.GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg F E σ B hB
  have hXu := _root_.GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hX
  have hWu := _root_.GlobalTheory.SkewUnit.isUnit_det_of_isSkew F E σ B d W r' s' hW
  have hT : IsHermND σ X.Jᵀ := ⟨fun i j => by simpa using hX.herm j i, by rw [Matrix.det_transpose]; exact hXu.ne_zero⟩
  have hS : IsHermND σ (-ξ₀ • W.J⁻¹) := _root_.GlobalTheory.skew_dual_isHermND F E σ d W.J hW.skew hWu ξ₀ hξ hσξ
  have hLat : PositivityTheory.ThKW.LatH σ (-ξ₀ • W.J⁻¹) X.Jᵀ ξ₀ := PositivityTheory.ThKW.latH_of hB.cm hX hW hXu hWu hξ
  obtain ⟨ω, hω⟩ := PositivityTheory.ThKW.S.exists_isWeilDatumOF F E σ B hB d n (-ξ₀ • W.J⁻¹) X.Jᵀ hS hT ξ₀ hξ hσξ hLat χW χX hcW hcX
    (GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow F E σ B hB χW d rW) (GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow F E σ B hB χX n rX)
  have eB : (-1 : AF F ⊗[F] E) • incM F W.J = incM F (ξ₀ • (-ξ₀ • W.J⁻¹)⁻¹) := by
    have e1 : (-ξ₀ • W.J⁻¹)⁻¹ = (-ξ₀)⁻¹ • W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hWu,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : ξ₀ • (-ξ₀)⁻¹ • W.J = -W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    rw [e1, e2]
    funext i j
    simp [incM]
  exact PositivityTheory.ThKW.S.exists_isUWeilPair_cm F E σ B hB d n (-ξ₀ • W.J⁻¹) X.Jᵀ hS hT ξ₀ hξ hσξ hLat χW χX hcW hcX
    (GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow F E σ B hB χW d rW) (GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow F E σ B hB χX n rX) ω hω X.J W.J (-1) (by simp) eB
    (Fin n × Fin d) M.co hM.rat

theorem weilEx : PositivityTheory.ThKG.Tow.WeilEx := exists_isWeil

end PositivityTheory.ThKW.S

end
