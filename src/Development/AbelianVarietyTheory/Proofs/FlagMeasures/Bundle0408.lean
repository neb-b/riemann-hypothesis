module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0404
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0017
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqHarishChandraRatioLargeGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapDegreeRatio

theorem deg_eq_of_goodS (hH : GlobalTheory.GapIn.Hyp) (D : D7) :
    ∃ c : ℝ, 0 < c ∧ ∀ (W : LocW D.R.k D.R.rS) (l : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ),
      GoodS D l A → GapAtLeast (epsSH D.R) l h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h →
      A.deg = c * Formalism.QuantumDeterminants.fdegHC l := by
  obtain ⟨c, hc, hF⟩ := hH.1.2.2.2.2.2.2 D.R.k D.R.rS (epsSH D.R) (Formalism.MainNotions.S.Inh.obj_cayleyU_rows D)
  set s : NNReal := D.s.cdScale _ (epsSH D.R) with hs
  have hs0 : 0 < s := D.s.cdScale_pos _ _
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  refine ⟨c / s, div_pos hc hs0', fun W l A h hA hg hok => ?_⟩
  obtain ⟨hl, ⟨Q, hQ, hDS⟩, -, -, -, -, -, -, -, -, P, hP, hd⟩ := hA
  have hFQ : IsFdeg (Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q)) (c * Formalism.QuantumDeterminants.fdegHC l) :=
    hF l A.H (fun g => A.σ (Q⁻¹ * g * Q)) ⟨h, hg, hok⟩ hl hDS
  have hFQs : IsFdeg ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q))
      (c * Formalism.QuantumDeterminants.fdegHC l / s) := by
    refine ⟨div_pos hFQ.1 hs0', fun v w v' w' => ⟨(hFQ.2 v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
    rw [integral_smul_measure, (hFQ.2 v w v' w').2, ENNReal.coe_toReal, Complex.real_smul]
    have hd0 : ((c * Formalism.QuantumDeterminants.fdegHC l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hFQ.1.ne'
    have hcc : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0'.ne'
    push_cast at hd0 ⊢
    field_simp
  have : Nontrivial A.H := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : A.H)
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  let u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ := ⟨Q * P⁻¹, P * Q⁻¹,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩
  let a : Formalism.REAL.UJ (epsSH D.R) := ⟨u, GlobalTheory.FormalDegreeDatum.inUJ_of_cayley _ P Q _ hP.1 hP.2 hQ.1.2⟩
  have h1 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
    (fun g => A.σ (P⁻¹ * g * P)) (fun g => A.σ (Q⁻¹ * g * Q)) a (fun g => by
      have e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹) := rfl
      have e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q = (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      simp only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 A.deg hd w hw
  have h2 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
    (fun g => A.σ (Q⁻¹ * g * Q)) (fun g => A.σ (Q⁻¹ * g * Q)) 1 (fun g => by simp) hDS.2.2.1 _ hFQs w hw
  rw [← h1, h2]
  ring

theorem deg_ratio : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (W : LocW D.R.k D.R.rS) (l l' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A A' : LocS W) (h : ℝ), GoodS D l A → GoodS D l' A' → GapAtLeast (epsSH D.R) l h → GapAtLeast (epsSH D.R) l' h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → A'.deg / A.deg = Formalism.QuantumDeterminants.fdegHC l' / Formalism.QuantumDeterminants.fdegHC l := by
  intro hH D W l l' A A' h hA hA' hg hg' hok
  obtain ⟨c, hc, hk⟩ := deg_eq_of_goodS hH D
  rw [hk W l A h hA hg hok, hk W l' A' h hA' hg' hok]
  exact mul_div_mul_left _ _ hc.ne'

end GlobalTheory.GapDegreeRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameGramMulEqConjTransposeMulFrameMatrices
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.ZxMul

theorem zx_mul : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (g γ h : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (C B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat (g⁻¹ v)) (Formalism.L2.SG.RealObj.frm X u 1 v) C → GlobalTheory.LoopAct.IsMatOn (uMat (h v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) B → Formalism.L2.SG.RealObj.ZX X u u' 1 (g * γ * h) v = Cᴴ * Formalism.L2.SG.RealObj.ZX X u u' 1 γ v * B := by
  intro D X u u' g γ h v C B hC hB
  have hU : (uMat (g⁻¹ v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (g⁻¹ v) = Formalism.REAL.Jm (X.B.I.ε v) := (g⁻¹ v).2
  have e : uMat ((g * γ * h) v) = uMat (g v) * uMat (γ v) * uMat (h v) := rfl
  have hL : ∀ a, uMat (g⁻¹ v) *ᵥ Formalism.L2.SG.RealObj.frm X u 1 v a =
      ∑ c, Cᵀ a c • Formalism.L2.SG.RealObj.frm X u 1 v c := fun a => by
    rw [hC a]; rfl
  have hM : ∀ b, uMat (h v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v b =
      ∑ d, Bᵀ b d • Formalism.L2.SG.RealObj.frm X u' 1 v d := fun b => by
    rw [hB b]; rfl
  unfold Formalism.L2.SG.RealObj.ZX
  rw [e, GlobalTheory.GxConj.zhat_conj _ _ _ _ _ _ _
    (GlobalTheory.GxConj.hJ_adj _ _ _ hU (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (g v))) _ _ hL hM,
    Matrix.transpose_transpose]
  rfl

end GlobalTheory.ZxMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixMemUnipotentStabilizerFrameGram
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

open scoped Classical

namespace GlobalTheory.FrameStab

open Formalism.L2.SG.RealObj

variable {n m r : ℕ}

def colMat (f : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin m) ℂ := Matrix.of fun i a => f a i

theorem isMatOn_iff (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin m → Fin n → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.LoopAct.IsMatOn g f M ↔ g * colMat f = colMat f * M := by
  constructor
  · intro h
    ext i b
    have := congrFun (h b) i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, colMat, Matrix.of_apply, this, mul_comm]
  · intro h b
    ext i
    have := congrFun (congrFun h i) b
    simp only [Matrix.mul_apply, colMat, Matrix.of_apply] at this
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, this, mul_comm]

theorem zhat_eq (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.L2.SG.RealObj.Zhat ε f f' G = (colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  ext a b
  simp only [Formalism.L2.SG.RealObj.Zhat, Formalism.L2.SG.HidaSetting.hJ, Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat,
    Matrix.of_apply, Matrix.conjTranspose_apply, Pi.star_apply]

theorem conjTranspose_mul_zhat_mul {ε : Fin n → Bool} {f f' : Fin (r + 1) → Fin n → ℂ}
    {Y G Gi : Matrix (Fin n) (Fin n) ℂ} {P M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hY : Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε) (hG : G * Gi = 1)
    (hP : GlobalTheory.LoopAct.IsMatOn Y f P) (hM : GlobalTheory.LoopAct.IsMatOn (Gi * Y * G) f' M) :
    Pᴴ * (Formalism.L2.SG.RealObj.Zhat ε f f' G * M) = Formalism.L2.SG.RealObj.Zhat ε f f' G := by
  rw [isMatOn_iff] at hP hM
  rw [zhat_eq]
  calc Pᴴ * ((colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' * M)
      = (colMat f * P)ᴴ * Formalism.REAL.Jm ε * G * (colMat f' * M) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Y * colMat f)ᴴ * Formalism.REAL.Jm ε * G * (Gi * Y * G * colMat f') := by rw [hP, hM]
    _ = (colMat f)ᴴ * (Yᴴ * Formalism.REAL.Jm ε * ((G * Gi) * Y)) * G * colMat f' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' := by
        rw [hG, Matrix.one_mul, hY]

theorem isLoUni_conjTranspose {N : ℕ} {P : Matrix (Fin N) (Fin N) ℂ} (h : Formalism.MainNotions.S.IsUpUni P) :
    Formalism.MainNotions.S.IsLoUni Pᴴ := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.conjTranspose_apply, (h j i).1 hij, star_zero]
  · rw [Matrix.conjTranspose_apply, (h j i).2 hij.symm, star_one]

theorem mem_stabU_of_conjTranspose_mul {N : ℕ} {Z P M : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det)
    (hP : Formalism.MainNotions.S.IsUpUni P) (hM : Formalism.MainNotions.S.IsUpUni M) (h : Pᴴ * (Z * M) = Z) :
    M ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨hM, ?_⟩
  have e : Pᴴ * (Z * M * Z⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_nonsing_inv _ hZ]
  rw [← Matrix.inv_eq_right_inv e]
  exact (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv (isLoUni_conjTranspose hP)).1

end GlobalTheory.FrameStab

namespace GlobalTheory.FrameStab

variable {n r : ℕ}

theorem exists_coeff_of_mem_spanLt {e : Fin r → Fin n → ℂ} {k : ℕ} {x : Fin n → ℂ}
    (hx : x ∈ Formalism.L2.SG.HidaSetting.spanLt e k) :
    ∃ c : Fin r → ℂ, (∀ b : Fin r, ¬ b.1 < k → c b = 0) ∧ x = ∑ b, c b • e b := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hx
  refine ⟨l, fun b hb => ?_, ?_⟩
  · exact (Finsupp.mem_supported' ℂ l).1 hl b hb
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul _ _

theorem exists_isUpUni_isMatOn {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.L2.SG.HidaSetting.InS e z Y) :
    ∃ P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, Formalism.MainNotions.S.IsUpUni P ∧
      GlobalTheory.LoopAct.IsMatOn Y (Formalism.L2.SG.RealObj.fam e z) P := by
  choose ca hca0 hcae using fun a : Fin r => exists_coeff_of_mem_spanLt (h.1 a)
  obtain ⟨cz, -, hcz⟩ := exists_coeff_of_mem_spanLt h.2
  let Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := fun i j =>
    Fin.lastCases (motive := fun _ => ℂ) 0
      (fun c : Fin r => Fin.lastCases (motive := fun _ => ℂ) (cz c) (fun a : Fin r => ca a c) j) i
  have hQl : ∀ j, Q (Fin.last r) j = 0 := fun j => by simp [Q]
  have hQcl : ∀ c, Q (Fin.castSucc c) (Fin.last r) = cz c := fun c => by simp [Q]
  have hQcc : ∀ c a, Q (Fin.castSucc c) (Fin.castSucc a) = ca a c := fun c a => by simp [Q]
  refine ⟨1 + Q, fun i j => ?_, fun b => ?_⟩
  · refine Fin.lastCases ?_ (fun c => ?_) i
    · refine ⟨fun hj => ?_, fun hj => ?_⟩
      · rw [Matrix.add_apply, hQl, Matrix.one_apply_ne (ne_of_lt hj).symm, add_zero]
      · rw [Matrix.add_apply, hQl, hj, Matrix.one_apply_eq, add_zero]
    · refine Fin.lastCases ?_ (fun a => ?_) j
      · exact ⟨fun hj => absurd hj (not_lt.2 (Fin.castSucc_lt_last c).le),
          fun hj => absurd hj (Fin.castSucc_lt_last c).ne⟩
      · refine ⟨fun hj => ?_, fun hj => ?_⟩
        · rw [Matrix.add_apply, hQcc, Matrix.one_apply_ne (ne_of_lt hj).symm, zero_add]
          exact hca0 a c (not_lt.2 (Fin.castSucc_lt_castSucc_iff.1 hj).le)
        · rw [Matrix.add_apply, hQcc, hj, Matrix.one_apply_eq, Fin.castSucc_inj.1 hj]
          rw [hca0 a a (lt_irrefl _), add_zero]
  · rw [Fin.sum_univ_castSucc]
    simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, Fin.snoc_last, Matrix.add_apply, add_smul,
      Finset.sum_add_distrib, hQl, zero_smul, add_zero]
    refine Fin.lastCases ?_ (fun a => ?_) b
    · simp only [Fin.snoc_last, hQcl, Matrix.one_apply_eq, one_smul,
        Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne, zero_smul, Finset.sum_const_zero, zero_add]
      rw [← hcz, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
    · simp only [Fin.snoc_castSucc, hQcc, Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne', zero_smul,
        add_zero]
      have e1 : ∑ x : Fin r, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.castSucc x) (Fin.castSucc a) • e x
          = e a := by
        simp only [Matrix.one_apply, Fin.castSucc_inj, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [e1, ← hcae a, Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]

end GlobalTheory.FrameStab

namespace GlobalTheory.FrameStab

theorem frameMat_mem_stabU : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ y : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), y ∈ Formalism.L2.SG.RealObj.StInf X u u' γ → IsUpUni M → GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * y * γ) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) M → IsUnit (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v).det → M ∈ GlobalTheory.LoopV.stabU (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v) := by
  intro D X u u' γ y v M hy hMu hM hZ
  obtain ⟨P, hPu, hP⟩ := exists_isUpUni_isMatOn ((hy.1 v).1)
  have hf : Formalism.L2.SG.RealObj.frm X u 1 v = Formalism.L2.SG.RealObj.fam
      (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc]
  rw [← hf] at hP
  have hY : (uMat (y v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (y v) = Formalism.REAL.Jm (X.B.I.ε v) := (y v).2
  have hG : uMat (γ v) * uMat (γ⁻¹ v) = 1 := by
    show uMat ((γ * γ⁻¹) v) = 1
    rw [mul_inv_cancel]
    rfl
  exact mem_stabU_of_conjTranspose_mul hZ hPu hMu (conjTranspose_mul_zhat_mul hY hG hP hM)

end GlobalTheory.FrameStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapNearPlaceParameterHalfNoncompactGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapNear

theorem gap_near : ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r → GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) := by
  intro Cn
  refine ⟨max Cn 1000, fun D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm₀ τ lam' hl => ?_⟩
  have hdim := dimS_eq D.R
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hmk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hnR : (D.R.r : ℝ) = 2 * D.R.rS + D.R.k + 1 := by rw [← hdim]; push_cast; ring
  have hmC : Cn ≤ (D.R.m : ℝ) := le_trans (le_max_left _ _) hm₀
  have hm1000 : (1000 : ℝ) ≤ D.R.m := le_trans (le_max_right _ _) hm₀
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.k ≤ D.R.r)
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.m ≤ D.R.r)
  have hr1000 : (1000 : ℝ) ≤ D.R.r := le_trans hm1000 hmr
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _

  have hsize : Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r ≤ (D.R.r : ℝ) ^ 19 / 2 := by
    have h1 : Cn * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hmC (show (0 : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 3 by positivity)
      linarith [show Cn * D.R.k * (D.R.m : ℝ) ^ 3 = Cn * (D.R.k * (D.R.m : ℝ) ^ 3) by ring,
        show (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = (D.R.m : ℝ) * (D.R.k * (D.R.m : ℝ) ^ 3) by ring]
    have h2 : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 5 := by
      have e : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = D.R.k * (D.R.m : ℝ) ^ 4 := by ring
      have e' : (D.R.r : ℝ) ^ 5 = D.R.r * (D.R.r : ℝ) ^ 4 := by ring
      rw [e, e']
      exact mul_le_mul hkr (pow_le_pow_left₀ (by positivity) hmr 4) (by positivity) (by positivity)
    have h3 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
    have h4 : (4 : ℝ) ≤ (D.R.r : ℝ) ^ 14 := le_trans (by norm_num) (le_trans hr1000 (le_self_pow₀ (by linarith) (by norm_num)))
    have h5 : 4 * (D.R.r : ℝ) ^ 5 ≤ (D.R.r : ℝ) ^ 19 := by
      have := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 5 by positivity)
      linarith [show (D.R.r : ℝ) ^ 5 * (D.R.r : ℝ) ^ 14 = (D.R.r : ℝ) ^ 19 by ring]
    linarith

  have hf : 1 ≤ D.R.f := by
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hG0 := Formalism.MainNotions.BridgeLemma.szh_gap hZ.1 τ
  have hG : (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have hf' : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hf)
    have h5 : (1 : ℝ) ≤ Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_mul_of_one_le_of_one_le hf' hL)
    have h6 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity)
    have h7 : (D.R.r : ℝ) ^ 19 * (Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L)) =
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by ring
    linarith
  refine ⟨fun a b hne => ?_, ?_⟩
  · have hab : a ≠ b := fun e => hne (e ▸ rfl)
    have g := hG0 a b hne
    change _ ≤ |lamD D τ a - lamD D τ b| at g
    have hpair : |lam' a - lamD D τ a| + |lam' b - lamD D τ b| ≤ l1dist lam' (lamD D τ) := by
      unfold l1dist
      rw [← Finset.sum_pair (f := fun i => |lam' i - lamD D τ i|) hab]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => abs_nonneg _)
    have tri : |lamD D τ a - lamD D τ b| ≤ |lam' a - lam' b| + |lam' a - lamD D τ a| + |lam' b - lamD D τ b| := by
      rw [abs_le]
      constructor <;>
      linarith [le_abs_self (lam' a - lam' b), neg_abs_le (lam' a - lam' b), le_abs_self (lam' a - lamD D τ a),
        neg_abs_le (lam' a - lamD D τ a), le_abs_self (lam' b - lamD D τ b), neg_abs_le (lam' b - lamD D τ b)]
    linarith
  · have hok := (GlobalTheory.SizeNum.gapOK D.R.k D.R.rS D.R.r hnR (by omega) hr1000).1
    exact GlobalTheory.NumFam.gapOK_mono D.R.k D.R.rS (by linarith [show (0:ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity]) hok

end GlobalTheory.GapNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InputsOfSubsetWidths
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem inputs_of_subset_widths : ∀ S S' : Set ℝ, S ⊆ S' → (AmpOn S' → AmpOn S) ∧ (SmallOn S' → SmallOn S) ∧ (CntOn S' → CntOn S) ∧ (CountBoundOn S' → CountBoundOn S) ∧ (TieOn S' → TieOn S) := by
  intro S S' hSS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h Cg cb Cu cT CT hb hT
    obtain ⟨C, C2, Ch, h1, h2, h3⟩ := h Cg cb Cu cT CT hb hT
    refine ⟨C, C2, Ch, h1, h2, fun Cpr δ hδ => ?_⟩
    obtain ⟨thr, ht⟩ := h3 Cpr δ hδ
    exact ⟨thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT δ hb hT hδ
    obtain ⟨thr, ht⟩ := h Cg cb Cu cT CT δ hb hT hδ
    exact ⟨thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨c3, cH, cS, c4, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨c3, cH, cS, c4, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨c3, cH, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨c3, cH, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨cV, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨cV, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩

end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableCellOrbitalIntegralRankOneKFinite
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellOrbIntG

open GlobalTheory.CellOrbInt

theorem orbInt_integrable : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  intro H k r L h μG γ μR νR ν hgap hok _ hC
  obtain ⟨hγ, -, -, -, hR, hQ, -⟩ := hC
  have hae := ae_quot L hR hQ
  refine ⟨hae, fun b _ hb hint v v' hv hv' ξ ξ' => ?_⟩
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hsm := H.1.1.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ v' hv'
  obtain ⟨C, Ws, -, hdec⟩ := H.1.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v hv
  have hd := hdec v' hsm
  generalize C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W v'‖).sum = A at hd
  have hF : ContinuousOn (coefF L v v' ξ ξ') (UH (Hpk k r)) := by
    have e : coefF L v v' ξ ξ' = fun g => ⟪v, L.σ g v'⟫_ℂ • (innerSL ℂ ξ').smulRight ξ :=
      funext (coefF_eq L v v' ξ ξ')
    rw [e]
    exact (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ v')).smul continuousOn_const
  haveI : BorelSpace (PairSp k r) := Prod.borelSpace
  have hm : AEStronglyMeasurable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
    have := (contOn_intg L hγ hF).aestronglyMeasurable (μ := ν) (meas_pairSet L)
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at this
  refine (hint.const_mul (|A| * ‖(innerSL ℂ ξ').smulRight ξ‖)).mono' hm ?_
  filter_upwards [hae] with p hp
  refine (norm_intg_le L γ _ hp).trans ?_
  have hx := point_mem L hγ hp
  unfold pairMaj
  set x := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1
  have h1 : 1 ≤ Formalism.FourierDecayAlt.B.gN x := PI.PolynomialProperness.GN.gN_ge_one hx
  have h2 : Formalism.FourierDecayAlt.B.gN x ^ (1 - Formalism.FourierDecayAlt.ThreeDimData.aOf r h) ≤ Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have h3 : ‖⟪v, L.σ x v'⟫_ℂ‖ ≤ |A| * Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
    (hd x hx).trans ((mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg A)))
  rw [coefF_eq, norm_smul, mul_right_comm]
  exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

end GlobalTheory.CellOrbIntG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantLiftNormalisedDataExist
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem pinAll_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PinAll (Y := Y) u u' :=
  fun _ _ _ u u' => Formalism.L2.SG.Pf.LoopBPin.pinAll_holds u u'

end GlobalTheory
end

