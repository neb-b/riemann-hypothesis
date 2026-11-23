module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.TThetaSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SpanInfRatF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.Bundle0001
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0018
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTparMain
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem frameData_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ t0 : GL (Fin d.n) E,
    incM F d.b.1 = Matrix.fromCols (incM F d.b.1.toCols₁) (incM F d.b.1.toCols₂) ∧
    incM F d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 ∧
    ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1.toCols₂).map (cA σ) = 1 ∧
    incM F t0.1 * incM F (t0⁻¹).1 = 1 := by
  obtain ⟨t0, ht0'⟩ := d.ok.frame.2
  have ht0 : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * t0.1 := ht0'
  have hBx : incM F d.b.1.toCols₁ =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 := by
    rw [ht0, incM_mul, incM_diagCols]
  refine ⟨t0, incM_fromCols _, hBx, ?_, ?_⟩
  · rw [← hBx]; exact frame_xy_A d.ok.frame
  · rw [← incM_mul, Units.mul_inv, incM_one]
set_option backward.isDefEq.respectTransparency false in
theorem tPar_k : _root_.PositivityTheory.SiegelWeilFormula.TPar_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, hB, hBx, hf, hT⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  have mem : ∀ w, d.dd.rho d.B.ψ w Φ ∈ schA F d.κ := fun w => GlobalTheory.HeisSchA.schr_mem_schA _ hψ _ Φ hΦ
  refine ⟨fun x β hx X => ?_, fun x t u hx X => ?_, fun g X => ?_⟩
  · have h1 := inFrame_mul hx
    have h2 := inv_mul_frame h1 (N' := Matrix.fromBlocks 1 (-β) 0 1)
      (by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one])
    rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
    replace h1 := Matrix.fromCols_inj h1
    replace h2 := Matrix.fromCols_inj h2
    rw [hBx] at h1 h2
    have hpar : IsPar x 1 := by
      have e := par_of hT (show mat2 x * ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) *
          incM F t0.1) = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 * 1 by
        rw [h1.1]; simp)
      rw [Matrix.mul_one, hT] at e
      unfold IsPar
      rw [Units.val_one]
      exact e
    have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 x⁻¹)ᵀ = -(X * βᵀ * (incM F t0.1)ᵀ) *
        (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ + X * (incM F d.b.1.toCols₂)ᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, h2.2]
      simp [Matrix.transpose_mul, Matrix.transpose_add, Matrix.mul_add, Matrix.mul_assoc, Matrix.transpose_neg]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
    rw [l_rho_om h x _ hΦ, l_om_par h hpar (mem _), key, l_shift h hψ _ _ hΦ]
    have he := symp_N X β (incM F t0.1) (incM F d.b.1.toCols₂) (incM F d.A.J) (dbl (incM F d.Y.J)) hf
    dsimp only [incM, cA] at he
    dsimp only [incM, cA]
    rw [he]
    simp
  · have h1 := inFrame_mul hx
    have h2 := inv_mul_frame h1 (N' := Matrix.fromBlocks (t⁻¹ : GL (Fin d.n) (AE F E)).1 0 0 (u⁻¹ : GL (Fin d.n) (AE F E)).1)
      (by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one])
    rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
    replace h1 := Matrix.fromCols_inj h1
    replace h2 := Matrix.fromCols_inj h2
    rw [hBx] at h1 h2
    obtain ⟨G0, hG0⟩ : ∃ G0 : GL (Fin d.n) (AE F E), G0 = Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t0 :=
      ⟨_, rfl⟩
    have g1 : (G0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F t0.1 := by
      rw [hG0]; rfl
    have g2 : ((G0⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F (t0⁻¹).1 := by
      rw [hG0, ← map_inv]; rfl
    have hpar : IsPar x (G0 * t * G0⁻¹) := by
      have e := par_of hT (show mat2 x * ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) *
          incM F t0.1) = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 * t.1 by
        rw [h1.1]; simp)
      unfold IsPar
      rw [Units.val_mul, Units.val_mul, g1, g2]
      exact e
    have hdet : Matrix.GeneralLinearGroup.det (G0 * t * G0⁻¹) = Matrix.GeneralLinearGroup.det t := by
      rw [map_mul, map_mul, map_inv]
      exact mul_inv_cancel_comm _ _
    have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 x⁻¹)ᵀ = X * (u⁻¹).1ᵀ * (incM F d.b.1.toCols₂)ᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, h2.2]
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [l_rho_om h x _ hΦ, l_om_par h hpar (mem _), hdet, key]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [l_rho_S h hψ g _ hΦ, Matrix.mul_assoc]
def TThetaSum_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch, HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => d.T Φ (incM F X)) (thetaSum F Φ)
set_option backward.isDefEq.respectTransparency false in
theorem tThetaSum_k : _root_.PositivityTheory.SiegelWeilFormula.Tpar.TThetaSum_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, ht0'⟩ := d.ok.frame.2
  have ht0 : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * t0.1 := ht0'
  obtain ⟨Am, hAm⟩ : ∃ Am : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E, Am = Matrix.fromRows 1 (-1) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = (d.b⁻¹).1 * Am := ⟨_, rfl⟩
  have hA : Am = d.b.1.toCols₁ * M.toRows₁ + d.b.1.toCols₂ * M.toRows₂ := by
    rw [← Matrix.fromCols_mul_fromRows, Matrix.fromCols_toCols, Matrix.fromRows_toRows, hM, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]
  have hinj : ∀ v, M.toRows₂ *ᵥ v = 0 → v = 0 := by
    intro v hv
    have e1 : Am *ᵥ v = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) *ᵥ (t0.1 *ᵥ (M.toRows₁ *ᵥ v)) := by
      rw [hA, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero, ht0,
        ← Matrix.mulVec_mulVec]
    funext i
    have a1 := congrFun e1 (Sum.inl i)
    have a2 := congrFun e1 (Sum.inr i)
    simp [hAm, diagCols, Matrix.fromRows_mulVec, Matrix.neg_mulVec] at a1 a2
    have : (2 : E) * v i = 0 := by linear_combination a1 - a2
    simpa using this
  have hu : IsUnit M.toRows₂.det := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.mulVec_injective_iff_isUnit.1 fun v w e => sub_eq_zero.1 (hinj _ (by rw [Matrix.mulVec_sub, e, sub_self])))
  let e : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E :=
    { toFun := fun y => y * M.toRows₂ᵀ
      invFun := fun X => X * (M.toRows₂)⁻¹ᵀ
      left_inv := fun y => by
        simp only
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hu, Matrix.transpose_one, Matrix.mul_one]
      right_inv := fun X => by
        simp only
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one, Matrix.mul_one] }
  have hterm : ∀ y : Matrix (Fin d.m) (Fin d.n) E,
      d.l (d.dd.rho d.B.ψ (incM F (Matrix.fromCols y (-y))) Φ) = d.T Φ (incM F (e y)) := by
    intro y
    have hy : Matrix.fromCols y (-y) = y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E)ᵀ + y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ := by
      have : Matrix.fromCols y (-y) = y * Amᵀ := by simp [hAm, Matrix.transpose_fromRows, Matrix.mul_fromCols]
      rw [this, hA, ht0]
      simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.mul_add, Matrix.mul_assoc]
    have ea : incM F (y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E)ᵀ) = incM F (y * M.toRows₁ᵀ * t0.1ᵀ) *
        (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ := by
      simp only [incM_mul, incM_transpose, incM_diagCols]
    have ec : incM F (y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ) = incM F (y * M.toRows₂ᵀ) * (incM F d.b.1.toCols₂)ᵀ := by
      simp only [incM_mul, incM_transpose]
    have hr := psi_rat h hψ (y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E)ᵀ) (y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ)
    have ea' := ea
    have ec' := ec
    dsimp only [incM] at ea' ec'
    dsimp only [] at hr
    rw [ea', ec'] at hr
    rw [hy, incM_add, ea, ec, l_shift h hψ _ _ hΦ]
    dsimp only [incM, cA]
    rw [hr, one_mul]
    rfl
  have hs := h.theta Φ hΦ
  rw [show (fun y : Matrix (Fin d.m) (Fin d.n) E => d.l (d.dd.rho d.B.ψ (incM F (Matrix.fromCols y (-y))) Φ)) =
      (fun X => d.T Φ (incM F X)) ∘ e from funext hterm] at hs
  exact (Equiv.hasSum_iff e).1 hs
theorem tTheta_of_k
    (h2 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
      ∀ Φ ∈ d.sch, ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ)) : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k :=
  fun F E _ _ _ _ _ σ d Φ hΦ => ⟨_root_.PositivityTheory.SiegelWeilFormula.Tpar.tThetaSum_k F E σ d Φ hΦ, h2 F E σ d Φ hΦ⟩
end PositivityTheory.SiegelWeilFormula.Tpar
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SpanInfRatFK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW.TauSpanIdentities
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
theorem piWF_ratWF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    piWF θ (ratWF (F := F) y) = infRatF (tauB B) y := by
  funext p
  exact PositivityTheory.ThKW.RealC.theta_inc (C.inf p.2) _
theorem continuous_piWF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : Continuous (piWF (nS := nS) (nT := nT) θ) :=
  continuous_pi fun p => (PositivityTheory.ThKW.RealC.continuous_theta (C.inf p.2)).comp
    ((continuous_apply p.1.2).comp (continuous_apply p.1.1))
theorem beta_iota_right_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x : WOF F E nS nT) (v : IxF F nS nT → ℂ) :
    B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWF θ x) v : ℝ)) := by
  have hx := finIdem_add_iota C.chart x
  have h0 := (_root_.GlobalTheory.WeilDatumF.symplOHF_fin_real_orth F E σ nS nT JS JT ξ₀ (finIdem F E • x) (iotaVF ι v) (finIdem_smul_fin x)
    (real_iotaVF C.chart v)).1
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.symplOHF_add_left, h0, zero_add,
    _root_.GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart, omV_apply]
  congr 1
  push_cast
  ring
theorem beta_iota_left_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) (x : WOF F E nS nT) :
    B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι v) x) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) v (piWF θ x) : ℝ)) := by
  have hx := finIdem_add_iota C.chart x
  have h0 := (_root_.GlobalTheory.WeilDatumF.symplOHF_fin_real_orth F E σ nS nT JS JT ξ₀ (finIdem F E • x) (iotaVF ι v) (finIdem_smul_fin x)
    (real_iotaVF C.chart v)).2
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.symplOHF_add_right, h0, zero_add,
    _root_.GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart, omV_apply]
  congr 1
  push_cast
  ring
theorem piWF_actOF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) :
    piWF θ (actOF σ JS JT g h x) = mMF σ JS JT θ (g, h) *ᵥ piWF θ x := by
  have hx := finIdem_add_iota C.chart x
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.actOF_add, piWF_add, piWF_of_fin (actOF_fin g h (finIdem_smul_fin x)), zero_add,
    _root_.GlobalTheory.T.actOF_iotaVF_eq_iotaVF_mulVec F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart g h, piWF_iotaVF C.chart]
theorem psi_rat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    B.ψ (symplOHF σ JS JT ξ₀ (ratWF x) (ratWF y)) = 1 := by
  rw [symplOHF_rat]
  exact C.good.std.2.1 _
theorem symplOF_actOF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [hOF_actOF C.hS]
theorem gamQF_eq_one_iff_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔
      ∃ z : ℤ, omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y) = z := by
  have hx : ratWF (F := F) x = finIdem F E • ratWF (F := F) x + iotaVF ι (infRatF (tauB B) x) := by
    have := finIdem_add_iota C.chart (ratWF (F := F) x); rwa [_root_.PositivityTheory.ThKW.TauSpanIdentities.piWF_ratWF_k C] at this
  have hy : ratWF (F := F) y = finIdem F E • ratWF (F := F) y + iotaVF ι (infRatF (tauB B) y) := by
    have := finIdem_add_iota C.chart (ratWF (F := F) y); rwa [_root_.PositivityTheory.ThKW.TauSpanIdentities.piWF_ratWF_k C] at this
  have cross : ∀ (a : WOF F E nS nT) (b : IxF F nS nT → ℂ), a.map (infPartF F E) = 0 →
      symplOHF σ JS JT ξ₀ a (iotaVF ι b) = 0 ∧ symplOHF σ JS JT ξ₀ (iotaVF ι b) a = 0 :=
    fun a b ha => _root_.GlobalTheory.WeilDatumF.symplOHF_fin_real_orth F E σ nS nT JS JT ξ₀ a (iotaVF ι b) ha (real_iotaVF C.chart b)
  have hr := _root_.PositivityTheory.ThKW.TauSpanIdentities.psi_rat_k C x y
  rw [hx, hy, GlobalTheory.RealWeilF.symplOHF_add_left, GlobalTheory.RealWeilF.symplOHF_add_right, GlobalTheory.RealWeilF.symplOHF_add_right,
    (cross _ _ (finIdem_smul_fin _)).1, (cross _ _ (finIdem_smul_fin _)).2, add_zero, zero_add,
    AddChar.map_add_eq_mul, _root_.PositivityTheory.ThKW.TauSpanIdentities.beta_iota_right_k C, piWF_iotaVF C.chart] at hr
  set om := omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y)
  set P := B.ψ (symplOHF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y))
  have hg : gamQF σ JS JT ξ₀ B.ψ x y = P * P := by
    show B.ψ (symplOF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y)) = _
    rw [symplOF_eq_add, AddChar.map_add_eq_mul]
  have hP : P = Complex.exp (Real.pi * Complex.I * (om : ℂ)) := by
    calc P = P * (Complex.exp (-(Real.pi * Complex.I) * (om : ℂ)) * Complex.exp (Real.pi * Complex.I * (om : ℂ))) := by
          rw [← Complex.exp_add, show -(Real.pi * Complex.I) * (om : ℂ) + Real.pi * Complex.I * (om : ℂ) = 0 by ring,
            Complex.exp_zero, mul_one]
      _ = _ := by rw [← mul_assoc, hr, one_mul]
  rw [hg, hP, ← Complex.exp_add, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 : ℂ) * (Real.pi * Complex.I) ≠ 0 :=
      mul_ne_zero two_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero)
    have : (om : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      linear_combination hn
    exact_mod_cast this
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; push_cast; ring⟩
section Lin
variable {κ : Type} [Fintype κ]
end Lin
theorem sig_sig_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
theorem gamQF_eq_one_iff'_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y) = n := by
  haveI : IsTotallyReal F := C.good.cm.1
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : gamQF σ JS JT ξ₀ B.ψ x y =
      B.ψ (pairA F 0 (algebraMap F (Af F) (Algebra.trace F E (ξ₀ * hRatF σ JS JT x y)))) := by
    have := LatC.sympl_ft (σ := σ) (JS := JS) (JT := JT) (ξ₀ := ξ₀) (_root_.PositivityTheory.ThKW.TauSpanIdentities.sig_sig_k C.good) 1 1 x y
    rw [one_mul, one_mul] at this
    show B.ψ (symplOF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y)) = _
    exact congrArg B.ψ this
  have h2 : ∀ t : F, pairA F 0 (algebraMap F (Af F) t) = algebraMap F (AF F) t + pairA F (-(algebraMap F (Ainf F) t)) 0 := by
    intro t
    refine Prod.ext ?_ ?_
    · show (0 : Ainf F) = algebraMap F (Ainf F) t + -(algebraMap F (Ainf F) t)
      rw [add_neg_cancel]
    · show algebraMap F (Af F) t = algebraMap F (Af F) t + 0
      rw [add_zero]
  have h3 : ∀ t : F, B.ψ (pairA F (-(algebraMap F (Ainf F) t)) 0) =
      Complex.exp (2 * Real.pi * Complex.I * algebraMap ℚ ℂ (Algebra.trace ℚ F t)) := by
    intro t
    have hw : ∀ w, θ w ((-(algebraMap F (Ainf F) t)) ⊗ₜ[F] (1 : E)) = -(w.embedding t) := by
      intro w
      have e : (algebraMap F (Ainf F) t) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E t := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rw [TensorProduct.neg_tmul, map_neg, e, (C.inf w).1]
      exact congrArg Neg.neg (RingHom.congr_fun (B.emb w).2 t)
    rw [GlobalTheory.StdCharWeilDatum.psi_pairA C.good.std, ← GlobalTheory.StdCharWeilDatum.sum_infFam B θ C.inf, trace_places]
    congr 1
    simp only [hw, Finset.sum_neg_distrib]
    ring
  rw [h1, h2, AddChar.map_add_eq_mul, C.good.std.2.1, one_mul, h3, Complex.exp_eq_one_iff, Algebra.trace_trace]
  have hpi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h4 : algebraMap ℚ ℂ (Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y)) = (n : ℂ) :=
      mul_left_cancel₀ hpi (by linear_combination hn)
    rw [eq_ratCast (algebraMap ℚ ℂ)] at h4
    exact_mod_cast h4
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, map_intCast]; ring⟩
section Span
theorem span_tau_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) :
    Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) = ⊤ := by
  haveI : IsTotallyComplex E := hB.cm.2.1
  have hall : ∀ z ∈ Submodule.span ℝ (Set.range (mixedEmbedding E)),
      Lm B z ∈ Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨e, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨e, ?_⟩
      funext w
      show (B.emb w).1 e = cw B w ((wE B w).embedding e)
      rw [cw_emb]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have htop : Submodule.span ℝ (Set.range (mixedEmbedding E)) = ⊤ := by
    refine eq_top_iff.2 (le_trans (le_of_eq (mixedEmbedding.latticeBasis E).span_eq.symm) (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    exact ⟨_, (mixedEmbedding.latticeBasis_apply E i).symm⟩
  rw [eq_top_iff]
  rintro f -
  let z : mixedEmbedding.mixedSpace E :=
    (0, fun W => cw B (W.1.comap (algebraMap F E)) (f (W.1.comap (algebraMap F E))))
  have hz : Lm B z = f := by
    funext w
    show cw B w (cw B ((wE B w).comap (algebraMap F E)) (f ((wE B w).comap (algebraMap F E)))) = f w
    rw [wE_comap, cw_cw]
  rw [← hz]
  exact hall z (htop ▸ Submodule.mem_top)
theorem span_infRatF_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) :
    Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B))) = ⊤ := by
  set V := Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B)))
  have key : ∀ (q : Fin nT × Fin nS) (g : InfinitePlace F → ℂ),
      (fun p : IxF F nS nT => if p.1 = q then g p.2 else 0) ∈ V := by
    intro q g
    have hg : g ∈ Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) := by
      rw [_root_.PositivityTheory.ThKW.TauSpanIdentities.span_tau_k hB]; trivial
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨e, rfl⟩ := hg
      apply Submodule.subset_span
      refine ⟨Matrix.of fun a b => if (a, b) = q then e else 0, ?_⟩
      funext p
      show (B.emb p.2).1 (if (p.1.1, p.1.2) = q then e else 0) = if p.1 = q then (B.emb p.2).1 e else 0
      by_cases h : p.1 = q
      · rw [if_pos h, if_pos (by rw [← h])]
      · rw [if_neg h, if_neg (by intro h'; exact h (by rw [← h'])), map_zero]
    | zero =>
      convert V.zero_mem using 1
      funext p
      split_ifs <;> rfl
    | add g g' _ _ hg hg' =>
      convert V.add_mem hg hg' using 1
      funext p
      by_cases h : p.1 = q <;> simp [h]
    | smul c g _ hg =>
      convert V.smul_mem c hg using 1
      funext p
      by_cases h : p.1 = q <;> simp [h]
  rw [eq_top_iff]
  rintro v -
  have hv : v = ∑ q : Fin nT × Fin nS, (fun p : IxF F nS nT => if p.1 = q then v (q, p.2) else 0) := by
    funext p
    rw [Finset.sum_apply, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [hv]
  exact V.sum_mem fun q _ => key q (fun w => v (q, w))
end Span
end PositivityTheory.ThKW.TauSpanIdentities
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.THeisK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
def TUnit_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ν : Measure (Mx F E d.m d.n), ν.IsAddHaarMeasure → ∀ x, ∀ Φ ∈ d.sch, ∀ Φ' ∈ d.sch,
  ∫ X, d.T (d.om x Φ) X * star (d.T (d.om x Φ') X) ∂ν = ∫ X, d.T Φ X * star (d.T Φ' X) ∂ν
def THeis_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch, ∀ Z X : Mx F E d.m d.n,
  d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₂)ᵀ) Φ) X = d.T Φ (X + Z) ∧
  d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₁)ᵀ) Φ) X = d.B.ψ (d.tt (d.gram Z X)) * d.T Φ X
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicOfK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
namespace PositivityTheory.ThKF0
theorem thetaBasic_of_k (harch : _root_.PositivityTheory.ThKF0.ArchBd_k) : _root_.GlobalTheory.ThK.ThetaBasic_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hS := hP.weil.isUSplitting
  obtain ⟨l, hl, hlt⟩ := (_root_.GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F (Fin n × Fin d)).2.1
  refine ⟨fun Φ hΦ => ⟨?_, ?_, _root_.PositivityTheory.ThKF0.norm_theta_le_mul_ht_pow_of_isPair harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ⟩, ?_⟩
  · refine (hS.cont l hl Φ hΦ).congr fun x => ?_
    simp only [theta]
    exact hlt _ (hS.pres _ _ hΦ)
  · intro γ hγ γ' hγ' g h
    simp only [theta]
    have e : om (γ * g, γ' * h) Φ = om (γ, γ') (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul]; rfl
    rw [e]
    exact _root_.PositivityTheory.ThKF0.thetaSum_rational_pair_invariant F E σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' _ (hS.pres _ _ hΦ)
  · intro φ hφ g h
    obtain ⟨T, hT⟩ := hS.adm (g, h) l hl φ hφ
    refine T.continuous.congr fun f => ?_
    simp only [theta]
    have hm : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) φ ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, φ, hφ, rfl⟩
    rw [← hlt _ (hS.pres _ _ hm)]
    exact (hT f).symm
end PositivityTheory.ThKF0
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepresentationPairUnitary
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_pair_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  first | exact @_root_.GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF_k | exact _root_.GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF_k | (intros; apply _root_.GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF_k <;> assumption)
end
end

