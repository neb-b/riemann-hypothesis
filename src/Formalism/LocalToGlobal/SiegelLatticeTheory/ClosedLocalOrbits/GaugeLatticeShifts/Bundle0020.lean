module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0018

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolP
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem ballDim : BallDim := by
  intro E _ _ _ _ _ s
  let f := (stdOrthonormalBasis ℝ E).repr
  have hf : MeasurePreserving f := f.measurePreserving
  have e : f ⁻¹' Metric.ball 0 s = Metric.ball 0 s := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  rw [← e, hf.measure_preimage measurableSet_ball.nullMeasurableSet]

variable {k r : ℕ}

theorem measurableSet_expImage_univ (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :
    MeasurableSet ((fun x : Formalism.MainNotions.S.lieE S =>
      fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j : Formalism.MainNotions.S.lieE S → Mt k r) '' Set.univ) := by
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) S
  have hU : (Set.univ : Set (Formalism.MainNotions.S.lieE S)) = ⋃ n : ℕ, Metric.closedBall 0 (n : ℝ) := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, Metric.mem_closedBall, dist_zero_right, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact ⟨n, hn⟩
  rw [hU, Set.image_iUnion]
  exact MeasurableSet.iUnion fun n => ((isCompact_closedBall _ _).image hE).isClosed.measurableSet

theorem rhoMeas : RhoMeas := by
  intro k r S
  refine measurable_of_Iio fun t => ?_
  have e : rhoS k r S ⁻¹' Set.Iio t = (fun x : Formalism.MainNotions.S.lieE S =>
      fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j : Formalism.MainNotions.S.lieE S → Mt k r) ''
        {Y | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞) < t} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, rhoS, iInf_lt_iff, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨Y, hY, hlt⟩; exact ⟨Y, hlt, hY⟩
    · rintro ⟨Y, hlt, hY⟩; exact ⟨Y, hY, hlt⟩
  rw [e]
  rcases eq_or_ne t ⊤ with rfl | ht
  · have : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
        < ⊤} = Set.univ := by
      ext Y; simp
    rw [this]
    exact measurableSet_expImage_univ S
  · rcases eq_or_ne t 0 with rfl | ht0
    · have : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
          < 0} = ∅ := by ext Y; simp
      rw [this, Set.image_empty]; exact MeasurableSet.empty
    · have hb : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
          < t} = Metric.ball 0 t.toReal := by
        ext Y
        simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
        rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) ht]
        rfl
      have hpos : 0 < t.toReal := ENNReal.toReal_pos ht0 ht
      rw [hb]
      exact measurableSet_expBall (k := k) (r := r) S t.toReal hpos

theorem rhoN : RhoN := by
  intro k r Y
  have hinj : ∀ Y' : Formalism.MainNotions.S.lieE (Nset k r), expL k r (Nset k r) Y' = expL k r (Nset k r) Y → Y' = Y := by
    intro Y' h
    have hY : (Y : EuclideanSpace ℝ _) ∈ (Formalism.MainNotions.BridgeCSB.lieNS k r).map Formalism.MainNotions.BridgeCSB.RL := by
      rw [← Formalism.MainNotions.BridgeCSB.lieE_N]; exact Y.2
    have hY' : (Y' : EuclideanSpace ℝ _) ∈ (Formalism.MainNotions.BridgeCSB.lieNS k r).map Formalism.MainNotions.BridgeCSB.RL := by
      rw [← Formalism.MainNotions.BridgeCSB.lieE_N]; exact Y'.2
    obtain ⟨X, hX, hXY⟩ := hY
    obtain ⟨X', hX', hXY'⟩ := hY'
    have e1 : Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _) = X := by
      rw [← hXY]; exact Formalism.MainNotions.BridgeCSB.unrealify_RL X
    have e2 : Formalism.MainNotions.S.unrealify (Y' : EuclideanSpace ℝ _) = X' := by
      rw [← hXY']; exact Formalism.MainNotions.BridgeCSB.unrealify_RL X'
    have hexp : NormedSpace.exp X' = NormedSpace.exp X := by
      have h2 : (fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y' : EuclideanSpace ℝ _)) i j : Mt k r) =
          fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j := h
      rw [e1, e2] at h2
      ext i j
      exact congrFun (congrFun h2 i) j
    have hXX : X' = X := Formalism.MainNotions.BridgeCSB.exp_injOn hX'.1 hX.1 hexp
    apply Subtype.ext
    rw [← hXY, ← hXY', hXX]
  unfold rhoS
  refine le_antisymm (iInf_le_of_le Y (iInf_le_of_le rfl le_rfl)) (le_iInf₂ fun Y' hY' => ?_)
  rw [hinj Y' hY']
  exact le_of_eq rfl

end Formalism.L2.SG.Pf.BH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWbGlue
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB Formalism.L2.SG.Pf.Jac

variable {k r : ℕ}

def gA (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r) : Mt k r :=
  fun i j => ((Matrix.of a)⁻¹ * E * Matrix.of b) i j

def gB (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r) : Mt k r :=
  fun i j => (Matrix.of a * E * (Matrix.of b)⁻¹) i j

theorem meas_gA (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {f : Mt k r → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun p : Mt k r × Mt k r => f (gA E p.1 p.2) := by
  have e : (fun p : Mt k r × Mt k r => gA E p.1 p.2) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => ((Matrix.of p.1)⁻¹) i j : Mt k r) *
        Matrix.of (E : Mt k r)) i j : Mt k r) * Matrix.of p.2) i j : Mt k r) := by
    funext p; rfl
  have : Measurable fun p : Mt k r × Mt k r => gA E p.1 p.2 := by
    rw [e]
    exact mulMt_meas (mulMt_meas (invMt_meas measurable_fst) measurable_const) measurable_snd
  exact hf.comp this

theorem measurable_comp_group_action (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a0 : Mt k r) {f : Mt k r → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun b : Mt k r => f (gA E a0 b) := by
  let P : Mt k r → Mt k r := fun b =>
    ((Matrix.of a0)⁻¹ * E * Matrix.of b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
  have hP : Continuous P := by
    show Continuous fun b : Mt k r =>
      ((Matrix.of a0)⁻¹ * E * Matrix.of b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    fun_prop
  exact hf.comp hP.measurable

theorem gA_inv (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r)
    (ha : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det) :
    gA E (Formalism.FourierDecayAlt.B2.invM a) (Formalism.FourierDecayAlt.B2.invM b) = gB E a b := by
  have h1 : ((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ = Matrix.of a :=
    Matrix.nonsing_inv_nonsing_inv _ ha
  show (fun i j => (((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ * E *
      (Matrix.of b)⁻¹) i j : Mt k r) = fun i j => (Matrix.of a * E * (Matrix.of b)⁻¹) i j
  rw [h1]

theorem prod_to_iter {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z')
    (hT' : 0 < Tz k r z') {μW μW' : Measure (Mt k r)} (hW : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW)
    (hW' : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z') μW') (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    {f : Mt k r → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p : Mt k r × Mt k r, f ((Matrix.of p.1)⁻¹ * E * Matrix.of p.2) ∂(μW.prod μW') =
      ∫⁻ h, ∫⁻ h', f (fun i j => (Matrix.of h * E * (Matrix.of h')⁻¹) i j) ∂μW' ∂μW := by
  have sW := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW
  have sW' := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW'
  have hinv : μW.map Formalism.FourierDecayAlt.B2.invM = μW :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z) μW (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hW
  have hinv' : μW'.map Formalism.FourierDecayAlt.B2.invM = μW' :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z') μW' (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z') hW'
  have hA := meas_gA (k := k) (r := r) E hf
  have e0 : (fun p : Mt k r × Mt k r => f ((Matrix.of p.1)⁻¹ * E * Matrix.of p.2)) = fun p => f (gA E p.1 p.2) := by
    funext p; rfl
  rw [e0, lintegral_prod (fun p : Mt k r × Mt k r => f (gA E p.1 p.2)) hA.aemeasurable]
  have key : ∀ (ν : Measure (Mt k r)), ν.map Formalism.FourierDecayAlt.B2.invM = ν → ∀ F : Mt k r → ℝ≥0∞, Measurable F →
      ∫⁻ a, F a ∂ν = ∫⁻ a, F (Formalism.FourierDecayAlt.B2.invM a) ∂ν := by
    intro ν hν F hF
    conv_lhs => rw [← hν]
    exact lintegral_map hF Formalism.FourierDecayAlt.P.B2x1.invM_meas
  refine (key μW hinv _ hA.lintegral_prod_right').trans ?_
  have hae : ∀ᵐ a ∂μW, (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z :=
    ae_iff.2 hW.conc
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with a ha
  have hau : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det := unit_of_UH ha.1
  refine (key μW' hinv' _ (measurable_comp_group_action E (Formalism.FourierDecayAlt.B2.invM a) hf)).trans ?_
  refine lintegral_congr fun b => ?_
  rw [gA_inv E a b hau]
  rfl

theorem rhsWHaar : RhsWHaar := by
  intro k r z z' μW μW' a a' μsec D
  obtain ⟨μb0, hb0⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  have hW := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 k r z μW D.z_mem D.T_pos D.haarW
  have hW' := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 k r z' μW' D.z'_mem D.T'_pos D.haarW'
  obtain ⟨C, hC, hI⟩ := Formalism.FourierDecayAlt.P.rank_one_integration_formula k r z z' μsec μb0 μW μW' D.k_pos D.z_mem D.z'_mem
    D.T_pos D.T'_pos D.sec hb0 hW hW'
  refine ⟨C⁻¹ • μb0, isHaarOn_smul (skHaar_of_cs hb0) (inv_pos.2 hC), fun φ hφ => ?_⟩
  rw [lintegral_smul_measure, hI φ hφ]
  unfold rhsW
  simp_rw [prod_to_iter D.z_mem D.T_pos D.z'_mem D.T'_pos hW hW' _ hφ]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hC.ne', ENNReal.coe_one, one_mul]

theorem mBase_mem {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (hsec : IsSection k r z z' μsec) :
    mBase k r z z' μsec ∈ Formalism.FourierDecayAlt.B2.UWb k r := by
  have hlt : Tz k r z * Tz k r z' < Complex.normSq (zeta0 k r z z') := by
    have hp : 0 < Tz k r z * Tz k r z' := mul_pos hT hT'
    unfold zeta0
    rw [Complex.normSq_ofReal]
    have hs := Real.mul_self_sqrt hp.le
    have e : (2 * Real.sqrt (Tz k r z * Tz k r z')) * (2 * Real.sqrt (Tz k r z * Tz k r z')) =
        4 * (Real.sqrt (Tz k r z * Tz k r z') * Real.sqrt (Tz k r z * Tz k r z')) := by ring
    rw [e, hs]
    linarith
  exact (Formalism.FourierDecayAlt.P.unipotent_weyl_properties k r).1 ▸ ⟨_, (hsec.2 _ hlt).1, rfl⟩

theorem gaugeShiftW : GaugeShiftW := by
  intro k r z z' μb μW μW' a a' μsec D hμb ρ hρ
  have hg : MeasurableSet (bBall k r ρ) := measurableSet_expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) ρ hρ
  have hmem : (mBase k r z z' μsec)⁻¹ ∈ Formalism.FourierDecayAlt.B2.UWb k r :=
    (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r).inv_mem _ (mBase_mem D.T_pos D.T'_pos D.sec)
  have hl : Measurable (lmulM (k := k) (r := r) (mBase k r z z' μsec)⁻¹) := by
    have : Continuous (lmulM (k := k) (r := r) (mBase k r z z' μsec)⁻¹) := by
      show Continuous fun x : Mt k r =>
        ((mBase k r z z' μsec)⁻¹ * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      exact continuous_const.matrix_mul continuous_id
    exact this.measurable
  have e : mBall k r z z' μsec ρ = lmulM (mBase k r z z' μsec)⁻¹ ⁻¹' bBall k r ρ := rfl
  refine ⟨e ▸ hl hg, ?_⟩
  rw [e, ← Measure.map_apply hl hg, hμb.2.2.2 _ hmem]

theorem wbDataEx : WbDataEx := by
  intro k r hk
  set z : Fin (2 * r + k + 1) → ℂ := Formalism.L2.SG.Pf.WFL.zBv k r 1 with hz
  have hzW : inWb k r z := Formalism.L2.SG.Pf.WFL.inWb_zB 1
  have hzT : Tz k r z = 1 := Formalism.L2.SG.Pf.WFL.Tz_zB zero_le_one
  have hT : 0 < Tz k r z := by rw [hzT]; exact one_pos
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hzW hT
  have hcpt := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hzW hT
  have hfin : μ Set.univ < ⊤ := by
    have h1 : μ Set.univ ≤ μ (UWset k r z : Set (Mt k r)) + μ (UWset k r z : Set (Mt k r))ᶜ := by
      have := measure_union_le (μ := μ) (UWset k r z : Set (Mt k r)) (UWset k r z : Set (Mt k r))ᶜ
      rwa [Set.union_compl_self] at this
    have h2 : μ (UWset k r z : Set (Mt k r))ᶜ = 0 := hμ.conc
    have h3 : μ (UWset k r z : Set (Mt k r)) < ⊤ := hμ.finite_compact _ hcpt
    rw [h2, add_zero] at h1
    exact lt_of_le_of_lt h1 h3
  have h0 : μ Set.univ ≠ 0 := fun h => hμ.ne_zero (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨μsec, hsec⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k r z z hk hzW hzW hT hT
  have ha : 0 < (μ Set.univ).toReal := ENNReal.toReal_pos h0 hfin.ne
  have hm : μ Set.univ = ENNReal.ofReal (μ Set.univ).toReal := (ENNReal.ofReal_toReal hfin.ne).symm
  exact ⟨z, z, μ, μ, _, _, μsec, ⟨hk, hzW, hzW, hT, hT, skHaar_of_cs hμ, skHaar_of_cs hμ, ha, ha, hm, hm, hsec⟩⟩

end Formalism.L2.SG.Pf.GE
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LintegralMulRightOfMap
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

namespace JL

def RightInvS : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ μ : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μ →
    ∀ s ∈ SLoc ε e z, μ.map (fun x => x * s) = μ

theorem frameLoc_swap {n r k : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' : ℝ}
    (hF : FrameLoc ε k e z z' T T') : FrameLoc ε k e z' z T' T :=
  ⟨hF.dim, hF.k_pos, hF.sig, hF.e_li, hF.ee, hF.ez', hF.ez, hF.zz', hF.zz, hF.T'_pos, hF.T_pos⟩

theorem lintegral_mul_right_of_map {n : ℕ} {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε))
    (t : Formalism.REAL.UJ ε) (hμ : μ.map (fun x => x * t) = μ) (F : Formalism.REAL.UJ ε → ℝ≥0∞) :
    ∫⁻ x, F (x * t) ∂μ = ∫⁻ x, F x ∂μ := by
  have hE : MeasurableEmbedding (fun x : Formalism.REAL.UJ ε => x * t) :=
    (MeasurableEquiv.mulRight t).measurableEmbedding
  calc ∫⁻ x, F (x * t) ∂μ = ∫⁻ x, F x ∂(μ.map (fun x => x * t)) := (hE.lintegral_map F).symm
    _ = ∫⁻ x, F x ∂μ := by rw [hμ]

theorem inner_dc {n : ℕ} {ε : Fin n → Bool} (μS μS' : Measure (Formalism.REAL.UJ ε))
    (s₁ s₁' g : Formalism.REAL.UJ ε) (h₁ : μS.map (fun x => x * s₁) = μS)
    (h₁' : μS'.map (fun x => x * s₁') = μS') (φ : Formalism.REAL.UJ ε → ℝ≥0∞) :
    ∫⁻ s, ∫⁻ s', φ (s * (s₁ * g * s₁'⁻¹) * s'⁻¹) ∂μS' ∂μS = ∫⁻ s, ∫⁻ s', φ (s * g * s'⁻¹) ∂μS' ∂μS := by
  have key : ∀ s s' : Formalism.REAL.UJ ε,
      φ (s * (s₁ * g * s₁'⁻¹) * s'⁻¹) = φ ((s * s₁) * g * (s' * s₁')⁻¹) := by
    intro s s'
    congr 1
    group
  have inner : ∀ x : Formalism.REAL.UJ ε,
      ∫⁻ s', φ (x * g * (s' * s₁')⁻¹) ∂μS' = ∫⁻ s', φ (x * g * s'⁻¹) ∂μS' := fun x =>
    lintegral_mul_right_of_map μS' s₁' h₁' (fun y => φ (x * g * y⁻¹))
  simp_rw [key, inner]
  exact lintegral_mul_right_of_map μS s₁ h₁ (fun x => ∫⁻ s', φ (x * g * s'⁻¹) ∂μS')

theorem measurableSet_goodLoc (r : ℕ) (T T' : ℝ) : MeasurableSet (GoodLoc (r := r) T T') := by
  have hD : ∀ l, Continuous fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l := by
    intro l
    by_cases h : l ≤ r + 1
    · simp only [Dl, dif_pos h]
      exact (continuous_id.matrix_diagonal.matrix_submatrix _ _).matrix_det
    · simp only [Dl, dif_neg h]
      exact continuous_const
  have hG : Continuous fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c) := by
    simp only [Gv]
    exact ((hD (r + 1)).norm.pow 2).sub (continuous_const.mul ((hD r).norm.pow 2))
  have h0 : MeasurableSet {c : Fin (r + 1) → ℂ | ∀ l, c l ≠ 0} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun l => (measurable_pi_apply l) (measurableSet_singleton 0).compl
  unfold GoodLoc
  rw [Set.ofPred_and]
  exact h0.inter (measurableSet_lt measurable_const hG.measurable)

end JL

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfJ
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open PI.ScalarPairDr.W (mem_orth hT_swap orth_orth fvec_castSucc fvec_last mem_orth_Xplus hT_smul_left)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scal

variable {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}

theorem span_left_le (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule.span D.host.E (Set.range F.fl.fvec) ≤
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₁.fl.fvec)) :=
  Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩)

theorem span_right_le (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule.span D.host.E (Set.range F₁.fl.fvec) ≤
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₁.fl.fvec)) :=
  Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩)

theorem Xsp_le_span (F : LFlag (D.sp.Y 0) D.R.rS T) :
    Xsp F ≤ Submodule.span D.host.E (Set.range F.fl.fvec) := by
  rw [Xsp, FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a.castSucc, fvec_castSucc _ _⟩

theorem Xsp_eq_Xs (F : LFlag (D.sp.Y 0) D.R.rS T) : Xsp F = Xs (S := VS D) F.fl.fvec := (Xs_fvec F.fl).symm

theorem z_mem_span (F : LFlag (D.sp.Y 0) D.R.rS T) :
    F.fl.z ∈ Submodule.span D.host.E (Set.range F.fl.fvec) :=
  Submodule.subset_span ⟨Fin.last _, fvec_last _⟩

theorem Gom'_mem (u v : Fin (D.R.rS + 1) → (VS D).V) : Gom' u v ∈ Submodule.span D.host.E (Set.range v) :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem Gom_mem (u v : Fin (D.R.rS + 1) → (VS D).V) : Gom u v ∈ Submodule.span D.host.E (Set.range u) :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem scal_dir (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T')
    (hz : F.zt = F.fl.z) (hz₁ : F₁.zt = F₁.fl.z) (hz₂ : F₂.zt = F₂.fl.z) (hT0 : T ≠ 0)
    (hU2 : UUE Λ F F₂ = Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₂.fl.fvec)))
    (htr : ∀ y ∈ UUE Λ F F₂, y ∈ orth (VS D) (Xplus F) → y ∈ UUE Λ F F₁)
    (hsc : ∀ y, y ∈ Ylift Λ F F₁ → y ∈ Ylift Λ F F₂ → ∀ α α', SgRel F F₂ y 0 α α' → SgRel F F₁ y 0 α α')
    (hind : LinearIndependent D.host.E F₁.fl.fvec)
    (hD1 : GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) ≠ 0) :
    (∃ x ∈ Xsp F, GDl F.fl.fvec F₂.fl.fvec (D.R.rS + 1) • Gom' F.fl.fvec F₁.fl.fvec =
      GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) • (Gom' F.fl.fvec F₂.fl.fvec - x)) ∧
    GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) * GDl F.fl.fvec F₂.fl.fvec D.R.rS =
      GDl F.fl.fvec F₂.fl.fvec (D.R.rS + 1) * GDl F.fl.fvec F₁.fl.fvec D.R.rS := by
  set f := F.fl.fvec with hf
  set f1 := F₁.fl.fvec with hf1
  set f2 := F₂.fl.fvec with hf2
  set D1 := GDl f f1 (D.R.rS + 1) with hD1def
  set D2 := GDl f f2 (D.R.rS + 1) with hD2def
  set R1 := GDl f f1 D.R.rS with hR1def
  set R2 := GDl f f2 D.R.rS with hR2def
  set om1 := Gom' f f1 with hom1
  set om2 := Gom' f f2 with hom2
  have hfl : f (Fin.last _) = F.fl.z := fvec_last _
  have hfc : ∀ a : Fin D.R.rS, f a.castSucc = F.fl.e a := fun a => fvec_castSucc _ a
  have p1 : ∀ a, (VS D).hT (f a) om1 = if a = Fin.last _ then D1 else 0 := om'_pair f f1
  have p2 : ∀ a, (VS D).hT (f a) om2 = if a = Fin.last _ then D2 else 0 := om'_pair f f2
  have hzz : (VS D).hT F.fl.z F.fl.z = -T := F.fl.z_norm
  set u2 := om2 + (D2 / T) • F.fl.z with hu2
  have hu2U : u2 ∈ UUE Λ F F₂ := by
    rw [hU2]
    exact Submodule.add_mem _ (span_right_le F F₂ (Gom'_mem f f2))
      (Submodule.smul_mem _ _ (span_left_le F F₂ (z_mem_span F)))
  have hu2o : u2 ∈ orth (VS D) (Xplus F) := by
    rw [Xplus, mem_orth_Xplus]
    refine ⟨fun a => ?_, ?_⟩
    · have h1 := p2 a.castSucc
      rw [if_neg (Fin.castSucc_ne_last a), hfc] at h1
      rw [hu2, map_add (f := _), map_smul, h1, F.fl.z_orth a, smul_zero, add_zero]
    · have h1 := p2 (Fin.last _)
      rw [if_pos rfl, hfl] at h1
      rw [hu2, map_add (f := _), map_smul, h1, hzz, smul_eq_mul]
      field_simp
      ring
  have hu2U1 := htr u2 hu2U hu2o
  have hx2 : om2 - R2 • F₂.fl.z ∈ Xsp F₂ := by
    rw [Xsp_eq_Xs, ← fvec_last F₂.fl]
    exact om'_decomp f f2
  have hsg : SgRel F F₂ u2 0 (D2 / T) R2 :=
    ⟨0, Submodule.zero_mem _, om2 - R2 • F₂.fl.z, hx2, by rw [hz, hz₂, hu2]; abel⟩
  obtain ⟨x, hx, x1, hx1, heq⟩ := hsc u2 (Submodule.mem_inf.2 ⟨hu2U1, hu2o⟩)
    (Submodule.mem_inf.2 ⟨hu2U, hu2o⟩) _ _ hsg
  rw [hz, hz₁, hu2, sub_zero] at heq
  have hp : R2 • F₁.fl.z + x1 = om2 - x := by
    have : om2 - x = (om2 + (D2 / T) • F.fl.z) - (D2 / T) • F.fl.z - x := by abel
    rw [this, heq]
    abel
  have hpspan : om2 - x ∈ Submodule.span D.host.E (Set.range f1) := by
    rw [← hp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (z_mem_span F₁)) (Xsp_le_span F₁ hx1)
  have hxX : x ∈ F.fl.X := hx
  have hq0 : D1 • (om2 - x) - D2 • om1 = 0 := by
    refine lemB f f1 hD1 (Submodule.sub_mem _ (Submodule.smul_mem _ _ hpspan)
      (Submodule.smul_mem _ _ (Gom'_mem f f1))) fun a => ?_
    rw [map_sub, map_smul, map_smul, map_sub, p1, p2, smul_eq_mul, smul_eq_mul]
    induction a using Fin.lastCases with
    | last =>
      rw [if_pos rfl, if_pos rfl, hfl, hT_z_X F.fl hxX]
      ring
    | cast a =>
      rw [if_neg (Fin.castSucc_ne_last a), if_neg (Fin.castSucc_ne_last a), hfc,
        hT_X_X F.fl (Submodule.subset_span ⟨a, rfl⟩) hxX]
      ring
  refine ⟨⟨x, hx, (sub_eq_zero.1 hq0).symm⟩, ?_⟩
  have hy1 : om1 - R1 • f1 (Fin.last _) ∈ Xs (S := VS D) f1 := om'_decomp f f1
  have hx1' : x1 ∈ Xs (S := VS D) f1 := by rw [← Xsp_eq_Xs]; exact hx1
  have hlast1 : f1 (Fin.last _) = F₁.fl.z := fvec_last _
  have e : (D1 * R2 - D2 * R1) • f1 (Fin.last _) =
      D2 • (om1 - R1 • f1 (Fin.last _)) - D1 • x1 + (D1 • (om2 - x) - D2 • om1) := by
    rw [← hp, hlast1]
    module
  rw [hq0, add_zero] at e
  have hmem : (D1 * R2 - D2 * R1) • f1 (Fin.last _) ∈ Xs (S := VS D) f1 := by
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hy1) (Submodule.smul_mem _ _ hx1')
  have hc := lemC f1 hind hmem
  linear_combination hc

end Scal

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

