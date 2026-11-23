module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianSumFrames
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.L2.SG.RealObj.RootCoordinateFrames

theorem nxt_eq {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (a : Fin r) : nxt e z a = fam e z a.succ := by
  unfold nxt fam
  split_ifs with h
  · have hs : a.succ = Fin.castSucc ⟨a.1 + 1, h⟩ := Fin.ext (by simp)
    rw [hs, Fin.snoc_castSucc]
  · have hs : a.succ = Fin.last r := Fin.ext (by simp; omega)
    rw [hs, Fin.snoc_last]

theorem hJ_sum_left {n m : ℕ} (ε : Fin n → Bool) (c : Fin m → ℂ) (v : Fin m → Fin n → ℂ) (w : Fin n → ℂ) :
    hJ ε (∑ i, c i • v i) w = ∑ i, star (c i) * hJ ε (v i) w := by
  unfold hJ
  rw [star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, smul_dotProduct, smul_eq_mul]

private theorem hJ_fintype_sum_smul_right {n : ℕ} {ι : Type} [Fintype ι] (ε : Fin n → Bool) (x : Fin n → ℂ)
    (Q : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ c, Q c • y c) = ∑ c, Q c * hJ ε x (y c) := by
  unfold hJ
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem RootCoordFrame_holds : RootCoordFrame := by
  intro n r ε e f z hfe hfz g P hP a
  unfold rootCoord
  rw [nxt_eq, hP, hJ_fintype_sum_smul_right]
  rw [Finset.sum_eq_single a.castSucc]
  · rw [show fam e z a.castSucc = e a from by unfold fam; exact Fin.snoc_castSucc _ _ _, hfe, if_pos rfl, mul_one]
  · intro c _ hc
    refine Fin.lastCases ?_ (fun b hb => ?_) c hc
    · intro _
      rw [show fam e z (Fin.last r) = z from by unfold fam; exact Fin.snoc_last _ _, hfz, mul_zero]
    · rw [show fam e z b.castSucc = e b from by unfold fam; exact Fin.snoc_castSucc _ _ _, hfe]
      have hab : a ≠ b := fun h => hb (by rw [h])
      rw [if_neg hab, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ZhatNAct_holds : ZhatNAct := by
  intro n r ε f f' s si s' g P P' hsi hinv hP hP'
  have hs : s * si = 1 := mul_eq_one_comm.mp hsi
  ext a b
  have h1 : (si * g * s') *ᵥ f' b = si *ᵥ (g *ᵥ (s' *ᵥ f' b)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h2 : hJ ε (f a) (si *ᵥ (g *ᵥ (s' *ᵥ f' b))) = hJ ε (s *ᵥ f a) (g *ᵥ (s' *ᵥ f' b)) := by
    rw [← hinv (f a) (si *ᵥ _), Matrix.mulVec_mulVec, hs, Matrix.one_mulVec]
  show hJ ε (f a) ((si * g * s') *ᵥ f' b) = _
  rw [h1, h2, hP a, hP' b, hJ_sum_left, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, hJ_fintype_sum_smul_right, Matrix.mul_apply, Matrix.map_apply,
    Matrix.transpose_apply, Zhat, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem FrameAtV_holds : FrameAtV := by
  intro D X u v
  have hc : ∀ p q : (VS D).V, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (rv X.B.I v (X.crd q)) =
      embS D (X.pl v) ((VS D).hT p q) := fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd (X := X) v p q
  have hs : ∀ p q : (VS D).V, (VS D).hT q p = starRingEnd D.host.E ((VS D).hT p q) := by
    intro p q
    first
    | exact ((VS D).herm.eq p q).symm
    | exact ((VS D).herm p q).symm
  simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, hc]
  refine ⟨fun a b => by rw [X.ee a b, map_zero], fun a b => by rw [X.ff a b, map_zero],
    fun a b => ?_, fun a b => ?_,
    fun a => ⟨by rw [(X.zu_orth u a).1, map_zero], by rw [(X.zu_orth u a).2, map_zero]⟩, ?_, ?_⟩
  · rw [X.ef a b]
    split_ifs <;> simp
  · rw [hs, X.ef b a]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h, map_zero, map_zero]
  · rw [X.zu_norm u, map_neg, map_natCast]
    simp [Tw]
  · unfold Tw
    exact_mod_cast (D.mem u).A.T_prime.ne_zero

end Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHGlue
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Jac

variable {k r : ℕ}

theorem skHaar_of_cs {U : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)}
    (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) : Formalism.MainNotions.S.IsHaarOn U μ :=
  ⟨Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite h, h.ne_zero, h.conc, h.left⟩

def fA (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b m : Mt k r) : Mt k r :=
  fun i j => ((Matrix.of a)⁻¹ * g * Matrix.of m * Matrix.of b) i j

def fB (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b m : Mt k r) : Mt k r :=
  fun i j => (Matrix.of a * g * Matrix.of m * (Matrix.of b)⁻¹) i j

theorem meas_fA (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable fun p : (Mt k r × Mt k r) × Mt k r => fA g p.1.1 p.1.2 p.2 := by
  have e : (fun p : (Mt k r × Mt k r) × Mt k r => fA g p.1.1 p.1.2 p.2) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of
        (fun i j => ((Matrix.of p.1.1)⁻¹) i j : Mt k r) * Matrix.of (g : Mt k r)) i j : Mt k r) *
        Matrix.of p.2) i j : Mt k r) * Matrix.of p.1.2) i j : Mt k r) := by
    funext p; rfl
  rw [e]
  exact mulMt_meas (mulMt_meas (mulMt_meas (invMt_meas (measurable_fst.comp measurable_fst)) measurable_const)
    measurable_snd) (measurable_snd.comp measurable_fst)

theorem meas_fB (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable fun p : (Mt k r × Mt k r) × Mt k r => fB g p.1.1 p.1.2 p.2 := by
  have e : (fun p : (Mt k r × Mt k r) × Mt k r => fB g p.1.1 p.1.2 p.2) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => (Matrix.of p.1.1 * Matrix.of (g : Mt k r)) i j : Mt k r) *
        Matrix.of p.2) i j : Mt k r) * Matrix.of (fun i j => ((Matrix.of p.1.2)⁻¹) i j : Mt k r)) i j : Mt k r) := by
    funext p; rfl
  rw [e]
  exact mulMt_meas (mulMt_meas (mulMt_meas (measurable_fst.comp measurable_fst) measurable_const) measurable_snd)
    (invMt_meas (measurable_snd.comp measurable_fst))

theorem meas_fA_slice (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a0 : Mt k r) {f : Mt k r → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun p : Mt k r × Mt k r => f (fA g a0 p.1 p.2) := by
  let P : Mt k r × Mt k r → Mt k r := fun p =>
    ((Matrix.of a0)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
  have hP : Continuous P := by
    show Continuous fun p : Mt k r × Mt k r =>
      ((Matrix.of a0)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    fun_prop
  exact hf.comp hP.measurable

theorem meas_fB_slice (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a0 : Mt k r) {f : Mt k r → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun p : Mt k r × Mt k r => f (fB g a0 p.1 p.2) :=
  hf.comp (meas_PQinv (fun p : Mt k r × Mt k r => Matrix.of a0 * g * Matrix.of p.2) (fun p => Matrix.of p.1)
    (by fun_prop) (by fun_prop))

theorem fA_inv (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b m : Mt k r)
    (ha : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det) :
    fA g (Formalism.FourierDecayAlt.B2.invM a) (Formalism.FourierDecayAlt.B2.invM b) m = fB g a b m := by
  have h1 : ((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ = Matrix.of a :=
    Matrix.nonsing_inv_nonsing_inv _ ha
  show (fun i j => (((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ * g * Matrix.of m *
      (Matrix.of b)⁻¹) i j : Mt k r) = fun i j => (Matrix.of a * g * Matrix.of m * (Matrix.of b)⁻¹) i j
  rw [h1]

theorem itgSwap : ItgSwap := by
  intro k r νN νb hN hb g f hf
  have sN := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hN
  have sb := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hb
  have hinv : νN.map Formalism.FourierDecayAlt.B2.invM = νN :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (Nset k r) νN (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN
  have hA := hf.comp (meas_fA (k := k) (r := r) g)
  have hB := hf.comp (meas_fB (k := k) (r := r) g)
  have e0 : (fun p : (Mt k r × Mt k r) × Mt k r => f ((Matrix.of p.1.1)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1.2)) =
      fun p => f (fA g p.1.1 p.1.2 p.2) := by funext p; rfl
  rw [e0, lintegral_prod (fun p : (Mt k r × Mt k r) × Mt k r => f (fA g p.1.1 p.1.2 p.2)) hA.aemeasurable]
  rw [lintegral_prod (fun q : Mt k r × Mt k r => ∫⁻ m, f (fA g q.1 q.2 m) ∂νb)
    (hA.lintegral_prod_right' (ν := νb)).aemeasurable]

  have key : ∀ F : Mt k r → ℝ≥0∞, Measurable F → ∫⁻ a, F a ∂νN = ∫⁻ a, F (Formalism.FourierDecayAlt.B2.invM a) ∂νN := by
    intro F hF
    conv_lhs => rw [← hinv]
    exact lintegral_map hF Formalism.FourierDecayAlt.P.B2x1.invM_meas
  have hF : Measurable fun a : Mt k r => ∫⁻ b, ∫⁻ m, f (fA g a b m) ∂νb ∂νN :=
    (hA.lintegral_prod_right' (ν := νb)).lintegral_prod_right' (ν := νN)
  refine (key _ hF).trans ?_
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ a ∂νN, (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Nset k r :=
    ae_iff.2 hN.conc
  filter_upwards [hae] with a ha
  have hau : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det := unit_of_UH ha.1
  have hG : Measurable fun b : Mt k r => ∫⁻ m, f (fA g (Formalism.FourierDecayAlt.B2.invM a) b m) ∂νb := by
    exact (meas_fA_slice g (Formalism.FourierDecayAlt.B2.invM a) hf).lintegral_prod_right'
  refine (key _ hG).trans ?_
  have e1 : ∀ b m : Mt k r, f (fA g (Formalism.FourierDecayAlt.B2.invM a) (Formalism.FourierDecayAlt.B2.invM b) m) = f (fB g a b m) :=
    fun b m => by rw [fA_inv g a b m hau]
  simp_rw [e1]
  refine lintegral_lintegral_swap ?_
  exact (meas_fB_slice g a hf).aemeasurable

end Formalism.L2.SG.Pf.BH

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH

theorem rhsHaar : RhsHaar := by
  intro k r μb hμb
  obtain ⟨νG, hG⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨νN, hN⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  obtain ⟨νb, hb⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  obtain ⟨C, hC, hI⟩ := Formalism.FourierDecayAlt.P.iterated_integration_formula k r νG νN νb hG hN hb
  obtain ⟨cb, cb0, cbt, hμB⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) hb hμb.1
  obtain ⟨cN, cN0, cNt, hμN⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hN
    (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top)
  set D : ℝ≥0∞ := cN * cb * cN with hD
  have hD0 : D ≠ 0 := by simp [hD, cN0, cb0]
  have hDt : D ≠ ∞ := by simp [hD, ENNReal.mul_eq_top, cNt, cbt]
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  set E : ℝ≥0∞ := D / (C : ℝ≥0∞) with hE
  have hEt : E ≠ ∞ := ENNReal.div_ne_top hDt hC0
  have hE0 : E ≠ 0 := ENNReal.div_ne_zero.2 ⟨hD0, ENNReal.coe_ne_top⟩
  refine ⟨E.toNNReal • νG, isHaarOn_smul (skHaar_of_cs hG) (ENNReal.toNNReal_pos hE0 hEt), fun φ hφ => ?_⟩
  have hR : rhs k r μb φ = D * ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
      ∫⁻ n, ∫⁻ m, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j)
        ∂νN ∂νb ∂νN := by
    unfold rhs
    rw [← lintegral_const_mul' _ _ hDt]
    refine lintegral_congr fun c => ?_
    rw [hμN, hμB]
    simp_rw [lintegral_smul_measure, smul_eq_mul, lintegral_const_mul' _ _ cNt, lintegral_const_mul' _ _ cbt]
    simp_rw [lintegral_const_mul' _ _ cNt]
    rw [hD]
    ring
  rw [hR, lintegral_smul_measure, hI φ hφ]
  simp_rw [← itgSwap k r νN νb hN hb _ φ hφ]
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_toNNReal hEt, hE, ← mul_assoc, ENNReal.div_mul_cancel hC0 ENNReal.coe_ne_top]

end Formalism.L2.SG.Pf.GE

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

variable {k r : ℕ}

theorem ball_eq_iUnion {E : Type*} [NormedAddCommGroup E] (ρ : ℝ) (hρ : 0 < ρ) :
    Metric.ball (0 : E) ρ = ⋃ n : ℕ, Metric.closedBall (0 : E) (ρ - ρ / (n + 2)) := by
  ext x
  simp only [Metric.mem_ball, Set.mem_iUnion, Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt (ρ / (ρ - ‖x‖))
    refine ⟨n, ?_⟩
    have h1 : 0 < ρ - ‖x‖ := by linarith
    have h2 : ρ / (ρ - ‖x‖) < (n : ℝ) + 2 := by linarith
    have h3 : ρ / ((n : ℝ) + 2) < ρ - ‖x‖ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ h1] at h2
      linarith
    linarith
  · rintro ⟨n, hn⟩
    have : 0 < ρ / ((n : ℝ) + 2) := by positivity
    linarith

theorem measurableSet_expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) (hρ : 0 < ρ) :
    MeasurableSet (expBall (k := k) (r := r) S ρ) := by
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) S
  unfold expBall
  rw [ball_eq_iUnion ρ hρ, Set.image_iUnion]
  refine MeasurableSet.iUnion fun n => ?_
  exact ((isCompact_closedBall _ _).image hE).isClosed.measurableSet

theorem long_weyl_element_mem : w0B k r ∈ UH (Hpk k r) :=
  Formalism.QuantumDeterminants.bigCellMem k r 1 1 (fun a => one_ne_zero) (by simp)

theorem gaugeShift : GaugeShift := by
  intro k r μ hμ ρ hρ
  have hg : MeasurableSet (gBall k r ρ) := measurableSet_expBall (k := k) (r := r) (UH (Hpk k r)) ρ hρ
  have hl : Measurable (lmulM (k := k) (r := r) (w0B k r)) := by
    have : Continuous (lmulM (k := k) (r := r) (w0B k r)) := by
      show Continuous fun x : Mt k r =>
        (w0B k r * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      exact continuous_const.matrix_mul continuous_id
    exact this.measurable
  have e : wBall k r ρ = lmulM (w0B k r) ⁻¹' gBall k r ρ := rfl
  refine ⟨e ▸ hl hg, ?_⟩
  rw [e, ← Measure.map_apply hl hg, hμ.2.2.2 _ long_weyl_element_mem]

end Formalism.L2.SG.Pf.BH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

variable {n r : ℕ}

def SLoc (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {g | InS e z (uMat g)}

def IsHaarS {ε : Fin n → Bool} (S : Set (Formalism.REAL.UJ ε)) (μ : Measure (Formalism.REAL.UJ ε)) : Prop :=
  IsHaarLoc S μ ∧ IsFiniteMeasureOnCompacts μ

structure FrameLoc (ε : Fin n → Bool) (k : ℕ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ) : Prop where
  dim : n = 2 * r + 1 + k
  k_pos : 1 ≤ k
  sig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1
  e_li : LinearIndependent ℂ e
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  ez' : ∀ a, hJ ε (e a) z' = 0
  zz : hJ ε z z = -(T : ℂ)
  zz' : hJ ε z' z' = -(T' : ℂ)
  T_pos : 0 < T
  T'_pos : 0 < T'

def ZLoc (ε : Fin n → Bool) (sc : ℝ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (g : Formalism.REAL.UJ ε) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Zhat ε (famSc sc e z) (famSc sc e z') (uMat g)

def GoodLoc (T T' : ℝ) : Set (Fin (r + 1) → ℂ) :=
  {c | (∀ l, c l ≠ 0) ∧ 0 < Gv T T' (Matrix.diagonal c)}

def wtLoc (k : ℕ) (T T' : ℝ) (c : Fin (r + 1) → ℂ) : ℝ :=
  Gv T T' (Matrix.diagonal c) ^ (k - 1) * JacV (Matrix.diagonal c)

def dcLoc : Measure (Fin (r + 1) → ℂ) :=
  Measure.pi fun _ => (2 : ℝ≥0∞) • (volume : Measure ℂ)

def IsSecLoc (ε : Fin n → Bool) (sc : ℝ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ)
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) : Prop :=
  ∀ c ∈ GoodLoc (r := r) T T', ZLoc ε sc e z z' (h c) = Matrix.diagonal c

def DisintLoc (ε : Fin n → Bool) (k : ℕ) (T T' : ℝ) (μS μS' : Measure (Formalism.REAL.UJ ε))
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (C : ℝ) : Prop :=
  ∀ φ : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable φ →
    ∫⁻ x, φ x ∂(Formalism.REAL.muG ε) =
      ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (C * wtLoc k T T' c) *
        ∫⁻ s, ∫⁻ s', φ (s * h c * s'⁻¹) ∂μS' ∂μS ∂(dcLoc (r := r))

def JacLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
    ∀ h, IsSecLoc ε sc e z z' T T' h → ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

def DiagDCLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ c ∈ GoodLoc (r := r) T T', ∀ g g' : Formalism.REAL.UJ ε,
      ZLoc ε sc e z z' g = Matrix.diagonal c → ZLoc ε sc e z z' g' = Matrix.diagonal c →
      ∃ s ∈ SLoc ε e z, ∃ s' ∈ SLoc ε e z', g' = s * g * s'⁻¹

def SecMeasLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc → ∃ h, Measurable h ∧ IsSecLoc ε sc e z z' T T' h

def NLoc (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {g | InN ε e z (uMat g)}

def HLoc (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {g | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ p a = p a) ∧ uMat g *ᵥ z = z}

def UnimodLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ μ : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μ →
    ∀ s ∈ SLoc ε e z, μ.map (fun x => x * s) = μ

def NHLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' → (∀ a b, hJ ε (e a) (p b) = if a = b then 1 else 0) → (∀ a b, hJ ε (p a) (p b) = 0) →
    (∀ b, hJ ε z (p b) = 0) →
    ∀ μN μH : Measure (Formalism.REAL.UJ ε), IsHaarS (NLoc ε e z) μN → IsHaarS (HLoc ε e p z) μH →
    IsHaarS (SLoc ε e z) ((μN.prod μH).map (fun q => q.1 * q.2))

def P5 : Prop := JacLoc → DiagDCLoc → SecMeasLoc → UnimodLoc → NHLoc → StepReal → HaarDisintegrationReal

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsPt
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermDef

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem atPt_uniq {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (P : LFlag S r T' → Prop) (t : TermQ Λ F P)
    (w w' : Point E (r + 1)) (h : AtPt Λ F P t w) (h' : AtPt Λ F P t w') : w = w' := by
  obtain ⟨F₁, ⟨h₁, e₁⟩, -, c₁⟩ := h
  obtain ⟨F₂, ⟨h₂, e₂⟩, -, c₂⟩ := h'
  have hq : Quot.mk (Rel Λ F P) ⟨F₁, h₁⟩ = Quot.mk (Rel Λ F P) ⟨F₂, h₂⟩ := e₁.trans e₂.symm
  have hg := Quot.eqvGen_exact hq
  have inv : ∀ x y : Carrier P, Relation.EqvGen (Rel Λ F P) x y → ∀ v : Point E (r + 1),
      (IsInCell (ZhatOM (ZhatL F x.1)) v ↔ IsInCell (ZhatOM (ZhatL F y.1)) v) := by
    intro x y hxy
    induction hxy with
    | rel x y hr => exact Formalism.L2.SG.Pf.cell_function_holds Λ F P x y hr
    | refl x => exact fun v => Iff.rfl
    | symm x y _ ih => exact fun v => (ih v).symm
    | trans x y z _ _ ih₁ ih₂ => exact fun v => (ih₁ v).trans (ih₂ v)
  exact Formalism.L2.SG.PtCell.isInCell_uniq ((inv _ _ hg w).1 c₁) c₂

variable {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)

theorem ptUniq_holds : PtUniq X Y u u' := fun t w w' h h' => atPt_uniq _ _ _ t.cls w w' h h'

end Formalism.L2.SG.RowsAbsX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SpanPreservation
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.RealObj.SpanPreservation

open Formalism.L2.SG.HidaSetting

theorem span_pres {n r : ℕ} (e : Fin r → Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) {y : Fin n → ℂ} (hy : y ∈ spanLt e r) :
    g *ᵥ y ∈ spanLt e r := by
  have hmono : ∀ a : Fin r, spanLt e a.1 ≤ spanLt e r := fun a =>
    Submodule.span_mono (Set.image_mono fun b (hb : b.1 < a.1) => lt_trans hb a.2)
  have hgen : ∀ a : Fin r, g *ᵥ e a ∈ spanLt e r := by
    intro a
    have e1 : g *ᵥ e a = e a + (g - 1) *ᵥ e a := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨a, a.2, rfl⟩) (hmono a (hg a))
  unfold spanLt at hy
  induction hy using Submodule.span_induction with
  | mem w hw => obtain ⟨b, -, rfl⟩ := hw; exact hgen b
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ ha

theorem inN_inv {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g gi : Matrix (Fin n) (Fin n) ℂ)
    (h1 : gi * g = 1) (hg : InN ε e z g) : InN ε e z gi := by
  have hS : InS e z gi := Formalism.L2.SG.RealObj.InfCut.inS_inv e z g gi h1 hg.1
  refine ⟨hS, fun y hy => ?_⟩
  have key : (gi - 1) *ᵥ y = -(gi *ᵥ ((g - 1) *ᵥ y)) := by
    simp [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1]
  rw [key]
  exact Submodule.neg_mem _ (span_pres e gi hS.1 (hg.2 y hy))

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ninfU_inv (u : D.what₂.Word) {s : X.B.I.Ginf} (hs : s ∈ X.NinfU u) : s⁻¹ ∈ X.NinfU u := fun v =>
  inN_inv _ _ _ (uMat (s v)) (uMat (s⁻¹ v)) (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (s v)) (hs v)

end Formalism.L2.SG.RealObj.SpanPreservation
end
end

