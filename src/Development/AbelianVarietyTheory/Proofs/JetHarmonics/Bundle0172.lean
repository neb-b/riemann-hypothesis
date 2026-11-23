module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.HermitianCurvature.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorAestronglyMeasurable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0146
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0106
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AemeasurableBesselNormIntegrandBigCell
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory


open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P in
theorem bigCell_density_eq {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ) (hd : ∀ a, c a ≠ 0) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      if Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) then
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
            ((fun j => c j.castSucc), c (Fin.last P.r)) *
          ‖B7.hsL (B7.JM p.T.base F (1, 1) ((fun j => c j.castSucc), c (Fin.last P.r)))‖ ^ 2
      else 0 := by
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
  have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hd _
  rw [TBBx2.Tri.Ew_top p F hl]
  split_ifs with hlt
  · have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      show 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := CutBP.nPt_bigPt P.k P.r _ _ c hlt.le
    have hq : ((fun j => c j.castSucc), c (Fin.last P.r)) ∈ B7.Q0 p.T.base := ⟨hc, hlt⟩
    rw [CutBP.hsVec_norm_V_bigPt p F c hd hG, hn, Real.mul_self_sqrt (CutBP.bcWeight_nonneg0 _ _ _ _ _),
      B7.JM_eq p.T.base F (1, 1) hq, bessel_function_trivial_index P.k P.r Wp Wq p.T.base F, B7.hsL_apply]
    rfl
  · have hV : p.V F (TBB.bigPt P.r c) = 0 := by
      show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = 0
      unfold D.vecV
      rw [dite_eq_right]
      rintro ⟨-, hG⟩
      exact hlt (Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG)
    rw [hV, TBBx2.Tri.hsVec_zero]
    simp


open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P in
theorem bigCell_density_aemeasurable :
    ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
      (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ContinuousOn F (B.GV P.k P.r) →
      AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c)) := by
  intro P Wp Wq _ _ _ _ _ _ p F hF
  have hq : Measurable fun c : Fin (P.r + 1) → ℂ =>
      (((fun j => c j.castSucc), c (Fin.last P.r)) : (Fin P.r → ℂ) × ℂ) := by fun_prop
  have hJ : StronglyMeasurable fun q : (Fin P.r → ℂ) × ℂ => B7.JM p.T.base F (1, 1) q :=
    (B7.sm_JM p.T.base hF).comp_measurable measurable_prodMk_left
  have hN : Measurable fun q : (Fin P.r → ℂ) × ℂ => ‖B7.hsL (B7.JM p.T.base F (1, 1) q)‖ :=
    ((B7.hsL (Wp := Wp) (Wq := Wq)).continuous.comp_stronglyMeasurable hJ).norm.measurable
  have hm : Measurable fun c : Fin (P.r + 1) → ℂ =>
      if Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) then
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
            ((fun j => c j.castSucc), c (Fin.last P.r)) *
          ‖B7.hsL (B7.JM p.T.base F (1, 1) ((fun j => c j.castSucc), c (Fin.last P.r)))‖ ^ 2
      else 0 := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_const
        (Complex.continuous_normSq.measurable.comp (measurable_pi_apply _))
    · exact ((B7.measurable_bcWeight _ _).comp hq).mul ((hN.comp hq).pow_const 2)
  have hae : ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ a, c a ≠ 0 := by
    rw [ae_all_iff]
    intro a
    exact Measure.ae_eval_ne (fun _ => (volume : Measure ℂ)) a 0
  refine (ENNReal.measurable_ofReal.comp hm).aemeasurable.congr ?_
  filter_upwards [hae] with c hc
  rw [bigCell_density_eq p F c hc]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficient
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem aesm_pi_of_finite {α ι E : Type} [MeasurableSpace α] {μ : Measure α} [Finite ι] [NormedAddCommGroup E]
    (f : α → ι → E) (hf : ∀ i, AEStronglyMeasurable (fun a => f a i) μ) : AEStronglyMeasurable f μ := by
  classical
  have := Fintype.ofFinite ι
  have e : f = fun a => ∑ i, (Pi.single i (f a i) : ι → E) := by
    funext a; rw [Finset.univ_sum_single]
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (continuous_single (A := fun _ : ι => E) i).comp_aestronglyMeasurable (hf i)

theorem measurable_nPt_bigPt (k r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) = fun c =>
      ∏ i : Fin (r + 1), (if 1 + (i : ℕ) = r + 1 then (‖c (Fin.last r)‖ ^ 2 - TT) ^ (k - 1)
        else ‖c i‖ ^ (2 * (C.Mlev k r (1 + (i : ℕ)) - 2))) := by
    funext c
    unfold TBB.nPt D.ptGG
    rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt, Complex.normSq_eq_norm_sq]
    unfold TBB.bigPt
    rw [Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights]
  rw [e]
  refine Finset.measurable_prod _ fun i _ => ?_
  split_ifs
  · fun_prop
  · exact ((measurable_pi_apply i).norm).pow_const _

theorem measurable_wPt_bigPt (r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c)) = fun c =>
      ‖∏ i, c i‖ ^ 2 / (‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2) := by
    funext c
    show Top.wPt TT r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold Top.wPt D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [e]
  refine Measurable.div ?_ ?_
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ => ‖∏ i, c i‖ ^ 2).measurable
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ =>
      ‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2).measurable

theorem aestronglyMeasurable_tv : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → B.CkOn ⊤ (B.GV P.k P.r) H →
    AEStronglyMeasurable (tv p H w) volume := by
  intro Wp Wq _ _ _ _ _ _ P p Cb H w hD hw hH
  unfold tv
  refine (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable (aesm_pi_of_finite _ fun x => ?_)
  have hV := GlobalTheory.bigCell_vector_aestronglyMeasurable Wp Wq P p _ (GlobalTheory.liftedWord_continuousOn_GPos Wp Wq P p Cb w x.1 H hD hw hH)
  have hc : Continuous fun X : Wq →L[ℂ] Wp => B.hsVec ((p.TP.E x.2).comp X) := by
    unfold B.hsVec
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (p.TP.E x.2).continuous.comp
      (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous
  refine AEStronglyMeasurable.smul (f := fun c : Fin (P.r + 1) → ℂ =>
    ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) x.1 x.2 : ℝ) : ℂ)) ?_ (hc.comp_aestronglyMeasurable hV)
  refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
  refine (measurable_nPt_bigPt _ _ _).sqrt.mul ?_
  unfold Top.dH
  exact (((measurable_wPt_bigPt _ _).pow_const _).mul_const _).sqrt

end GlobalTheory.TopVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSq
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.jN2_eq_normSq_base

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem good_of_weight_ne_zero (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ)
    (hw : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) ≠ 0) :
    (∀ a, c a ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c) := by
  set T := Tz P.k P.r p.T.base.z with hT
  set T' := Tz P.k P.r p.T.base.z' with hT'
  have hk : 2 ≤ P.k := p.hl.2.2
  have hTT : 0 < T * T' := mul_pos p.T.base.T_pos p.T.base.T'_pos
  have hw' := hw
  unfold bcWeight at hw'
  split_ifs at hw' with hle
  · have hprod := left_ne_zero_of_mul hw'
    have hgg := right_ne_zero_of_mul hw'
    have hlt : T * T' < Complex.normSq (c (Fin.last P.r)) := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso; apply hgg; rw [← h, sub_self, zero_pow (by omega)]
    have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := by
      intro a ha
      apply hprod
      refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      dsimp only
      rw [ha, norm_zero, zero_pow]
      unfold Mdim; have := a.isLt; omega
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    refine ⟨hd, ?_⟩
    show 0 < D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
    unfold D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
    have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
      Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
    nlinarith [mul_lt_mul_of_pos_left hlt hp]
  · exact absurd rfl hw'

theorem pt_eq (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
    bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) *
      ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r (fun j => c j.castSucc)
        (p.T.base.μsec (c (Fin.last P.r)))))‖ ^ 2 := by
  by_cases h : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  · obtain ⟨hl, hG⟩ := h
    have hd : ∀ a, c a ≠ 0 := fun a =>
      (hl.1 (1, c a) (by unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨a, rfl⟩)).2
    have hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) := hG
    have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
      Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG'
    rw [TBBx2.Tri.Ew_top p F hl, hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := nPt_bigPt P.k P.r _ _ c hζ.le
    rw [hn, Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _)]
  · have hw : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) = 0 := by
      by_contra hw
      obtain ⟨hd, hG⟩ := good_of_weight_ne_zero p c hw
      exact h ⟨Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd, hG⟩
    rw [TBBx4.ew_zero_of p F h, hw, zero_mul]

theorem besselNormSq_eq_bigCellNormSq : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TBB.jN2 p F = B.normSq p.T.base F := by
  intro P Wp Wq _ _ _ _ _ _ p F
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  unfold B.normSq jNormSq
  rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
  unfold TBB.jN2
  refine lintegral_congr fun c => ?_
  rw [he c, pt_eq p F c]
  rfl

end GlobalTheory.jN2_eq_normSq_base
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorNormEqRadialValueNorm
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem vec_bigPt_eq_radial : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), (∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ x ∈ Q.DomR P.k P.r p.T.base.z p.T.base.z', gR P p.T.base x.1 x.2 = TBB.Gp p (TBB.bigPt P.r c) ∧ dR P p.T.base x.1 x.2 = ‖∏ l, c l‖ ∧ ∃ lam : ℝ, 0 < lam ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'), Top.IsRadOf P p.T.base Φ H → ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ = lam * nv Φ x := by
  intro Wp Wq _ _ _ _ _ _ P p c hc hG
  have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
    Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
  have hc' : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hc _
  have hz := Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ p.T.base.z_mem p.T.base.z'_mem p.T.base.sec hζ
  have hx : ((fun a : Fin P.r => c a.castSucc), NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r))) ∈
      Q.DomR P.k P.r p.T.base.z p.T.base.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR p.T.base.z_mem p.T.base.z'_mem p.T.base.sec
      (q := ((fun a : Fin P.r => c a.castSucc), c (Fin.last P.r))) ⟨hc', hζ⟩
  refine ⟨_, hx, ?_, ?_, ?_⟩
  · show Complex.normSq (∏ a : Fin P.r, c a.castSucc) *
        (Complex.normSq (Q.zetaL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r)
          (NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)))) - Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') =
        D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
    unfold D.ptG
    rw [hz, Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc c, Complex.normSq_mul]
    ring
  · show ‖(∏ a : Fin P.r, c a.castSucc) * Q.zetaL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r)
          (NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)))‖ = _
    rw [hz, Fin.prod_univ_castSucc c]
  · have hpos : 0 < ∏ a : Fin P.r,
        (if a.val < (Fin.last P.r).val then ‖c a.castSucc‖ ^ (Mdim P.k P.r a - 1) else 1 : ℝ) := by
      refine Finset.prod_pos fun a _ => ?_
      split_ifs
      · exact pow_pos (norm_pos_iff.2 (hc' a)) _
      · exact one_pos
    refine ⟨_, inv_pos.2 hpos, fun H Φ hΦ => ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p H c hc hG]
    unfold nv
    rw [hΦ _ hx]
    unfold Q.resG
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hpos.le,
      inv_mul_cancel_left₀ hpos.ne']
    have e : Q.wCell P.k P.r (Fin.last P.r) (fun a : Fin P.r => c a.castSucc) *
        NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)) =
        bigCell P.k P.r (fun a : Fin P.r => c a.castSucc) (p.T.base.μsec (c (Fin.last P.r))) := by
      unfold NF.muZ
      rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization _ _ _ _).1]
    rw [e]

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrableEmptyWordDensityDecayingCoefficients
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

namespace GlobalTheory.HatNF.EmptyWordL2

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem integrable_weight_normSq (hXi : B.XiExists) {k r : ℕ} (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ)
    (hF : ∀ m : ℕ, B.InCC A m F) (hAB : B.AB k r ≤ A) (hT : JF.TransportedAlt k r A 0) :
    Integrable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) := by
  obtain ⟨-, -, -, ⟨C, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.BXiAsm.any_of hXi k r Wp Wq D A hAB
  obtain ⟨c4, hc4⟩ := hF 4
  have hfin := (hB1 F F c4 c4 (hF 5) (hF 5) hc4 hc4).1
  have h := Formalism.FourierDecayAlt.P.jacquet_smooth_coordinates k r Wp Wq D A 0 F hT (hF 0)
  have h2 : ContinuousOn (fun q => B.JF D F (B.gq D q)) (Formalism.FourierDecayAlt.P.B7.Q0 D) := h.continuousOn
  have h3 : ContinuousOn (fun q => B.hsVec (B.JF D F (B.gq D q))) (Formalism.FourierDecayAlt.P.B7.Q0 D) :=
    (LinearMap.continuous_of_finiteDimensional
      (⟨⟨B.hsVec, fun X Y => by ext; simp [B.hsVec]⟩, fun a X => by ext; simp [B.hsVec]⟩ :
        (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp))).comp_continuousOn h2
  have hmeas : AEStronglyMeasurable
      (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) volume :=
    Formalism.FourierDecayAlt.P.JCx2.rb_aesm D _ ((Formalism.FourierDecayAlt.P.JCx2.rb_contOn_bcW D).mul (h3.norm.pow 2)) fun q h => by simp [h]
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun q =>
    mul_nonneg (Formalism.FourierDecayAlt.P.JCx2.rb_bcWeight_nonneg _ _ q) (sq_nonneg _))]
  exact lt_of_le_of_ne le_top hfin

theorem Ew_bigPt_eq_indicator {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (c : Fin (P.r + 1) → ℂ) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      (Formalism.FourierDecayAlt.P.B7.Q0 p.T.base).indicator
        (fun q => bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q *
          ‖B.hsVec (B.JF p.T.base F (B.gq p.T.base q))‖ ^ 2)
        ((fun j => c j.castSucc), c (Fin.last P.r)) := by
  by_cases hq : ((fun j : Fin P.r => c j.castSucc), c (Fin.last P.r)) ∈ Formalism.FourierDecayAlt.P.B7.Q0 p.T.base
  · rw [Set.indicator_of_mem hq]
    obtain ⟨hc, hlt⟩ := hq
    dsimp only at hc hlt
    have hTT : 0 < Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' := mul_pos p.T.base.T_pos p.T.base.T'_pos
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      show 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p F hl, Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt P.k P.r _ _ c hlt.le
    rw [hn, Real.mul_self_sqrt (Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _)]
    rfl
  · rw [Set.indicator_of_notMem hq]
    refine Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p F fun h => hq ⟨fun a => ?_, ?_⟩
    · exact (h.1.1 (1, c a.castSucc) (by
        unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨a.castSucc, rfl⟩)).2
    · exact Formalism.FourierDecayAlt.P.PBM.zeta_big _ c h.2

end

theorem integrable_density_nil_of_xiExists (hXi : B.XiExists) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) := by
  refine ⟨10, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p H A _ hCC hA
  have ha : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  set x : ℝ := (P.r : ℝ) + 1 with hx
  set n : ℝ := 2 * (P.r : ℝ) + P.k + 1 with hn
  have hx1 : 1 ≤ x := by linarith
  have hn1 : 1 ≤ n := by linarith
  have h1 : x ≤ x ^ 4 := le_self_pow₀ hx1 (by norm_num)
  have h2 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have h3 : x * n ^ 2 ≤ x ^ 4 * n ^ 3 := mul_le_mul h1 h2 (by positivity) (by positivity)
  have h4 : 10 * (x * n ^ 2) ≤ A := by nlinarith
  have h5 : n ≤ n ^ 2 := le_self_pow₀ hn1 (by norm_num)
  have h6 : x * n ≤ x * n ^ 2 := mul_le_mul_of_nonneg_left h5 (by linarith)
  have h7 : 1 ≤ x * n := by nlinarith
  have hAB : B.AB P.k P.r ≤ A := by
    unfold B.AB
    rw [← hx]
    have : ((P.k : ℝ) + P.r) * x ≤ n * x := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  have hT : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    rw [← hx, ← hn]
    nlinarith
  have hint := (integrable_weight_normSq hXi p.T.base H A hCC hAB hT).indicator
    (Formalism.FourierDecayAlt.P.B7.isOpen_good_set p.T.base).measurableSet
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  have h8 := (hmp.integrable_comp_emb e.measurableEmbedding).2 hint
  refine h8.congr (Filter.Eventually.of_forall fun c => ?_)
  simp only [Function.comp]
  rw [he c]
  exact (Ew_bigPt_eq_indicator p H c).symm

theorem integrable_density_nil : GlobalTheory.HCXi.BesselXiIntegrable → ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) :=
  fun h => integrable_density_nil_of_xiExists (GlobalTheory.HCXi.xiExists_of_besselXiIntegrable h)

end GlobalTheory.HatNF.EmptyWordL2
end

