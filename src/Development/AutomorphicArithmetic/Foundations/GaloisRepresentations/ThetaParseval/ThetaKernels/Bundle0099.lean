module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.DecompW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0070
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0041
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0042
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0075
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.WeilEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0093
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WpSPair
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0020

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilFinal
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem decompW_k : _root_.PositivityTheory.SiegelWeilFormula.Kdil.DecompW_k := fun _ _ _ _ _ _ _ _ d R w g => _root_.PositivityTheory.SiegelWeilFormula.KSplitW.decompW_k d R w g
theorem gIdil_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) (hS : GlobalTheory.Published.SiegelSetUnitary)
    (hLF : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k) (hBD : BigDense) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.gIdil_of_k hT hAux hLE (_root_.PositivityTheory.SiegelWeilFormula.Kdil.thetaPt_of_k hT) (fun _ _ P => KFock.isSw_fP P) matCount (_root_.PositivityTheory.SiegelWeilFormula.Kdil.splitDom_of_k hT hAw _root_.PositivityTheory.SiegelWeilFormula.Kdil.decompW_k)
    (_root_.PositivityTheory.SiegelWeilFormula.Kdil.thetaBdd_of_k hS) hLF hBD holMean derCont stripOK
theorem gIdil'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) (hLF : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.gIdil_k hT hAux hLE hAw _root_.GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary hLF bigDense
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WpSTop
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace PositivityTheory.ThKW.S
theorem exists_isWeil_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW M hM χX χW hcX hcW rX rW
  obtain ⟨ξ₀, hξ, hσξ⟩ := _root_.GlobalTheory.T.exists_trace_zero_element F E σ B hB
  have hXu := _root_.GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hX
  have hWu := _root_.GlobalTheory.SkewUnit.isUnit_det_of_isSkew F E σ B d W r' s' hW
  have hT : IsHermND σ X.Jᵀ := ⟨fun i j => by simpa using hX.herm j i, by rw [Matrix.det_transpose]; exact hXu.ne_zero⟩
  have hS : IsHermND σ (-ξ₀ • W.J⁻¹) := _root_.GlobalTheory.skew_dual_isHermND F E σ d W.J hW.skew hWu ξ₀ hξ hσξ
  have hLat : PositivityTheory.ThKW.LatH σ (-ξ₀ • W.J⁻¹) X.Jᵀ ξ₀ := PositivityTheory.ThKW.latH_of hB.cm hX hW hXu hWu hξ
  obtain ⟨ω, hω⟩ := _root_.PositivityTheory.ThKW.S.exists_isWeilDatumOF_k F E σ B hB d n (-ξ₀ • W.J⁻¹) X.Jᵀ hS hT ξ₀ hξ hσξ hLat χW χX hcW hcX
    (_root_.GlobalTheory.T.restricted_eta_power_character F E σ B hB χW d rW) (_root_.GlobalTheory.T.restricted_eta_power_character F E σ B hB χX n rX)
  have eB : (-1 : AF F ⊗[F] E) • incM F W.J = incM F (ξ₀ • (-ξ₀ • W.J⁻¹)⁻¹) := by
    have e1 : (-ξ₀ • W.J⁻¹)⁻¹ = (-ξ₀)⁻¹ • W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hWu,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : ξ₀ • (-ξ₀)⁻¹ • W.J = -W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    rw [e1, e2]
    funext i j
    simp [incM]
  exact _root_.PositivityTheory.ThKW.S.exists_isUWeilPair_cm_k F E σ B hB d n (-ξ₀ • W.J⁻¹) X.Jᵀ hS hT ξ₀ hξ hσξ hLat χW χX hcW hcX
    (_root_.GlobalTheory.T.restricted_eta_power_character F E σ B hB χW d rW) (_root_.GlobalTheory.T.restricted_eta_power_character F E σ B hB χX n rX) ω hω X.J W.J (-1) (by simp) eB
    (Fin n × Fin d) M.co hM.rat
theorem weilEx_k : _root_.PositivityTheory.ThKG.Tow.WeilEx_k := _root_.PositivityTheory.ThKW.S.exists_isWeil_k
end PositivityTheory.ThKW.S
end
end
end

