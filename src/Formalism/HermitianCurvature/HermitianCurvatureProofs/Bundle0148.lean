module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRMatFrom
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvEig
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0145
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0146
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0025
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCoefficientHasCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRFinFrom
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RRFin

theorem hasDerivAt_rotExp (m : ℂ) :
    HasDerivAt (fun φ : ℝ => Complex.exp (m * (φ : ℂ) * Complex.I)) (m * Complex.I) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul m).mul_const Complex.I).cexp
  simpa using h

end RRFin

open RRMat RRFin in
theorem rotation_finite_from_matrix : GTRRFinFrom := by
  intro hC hS hW Wp Wq _ _ _ _ _ _ P Bs hpl hk2 hsec e he hc n hn Rt s hRt ρ Φ
  have hB := SSTr.radBase P Bs hpl
  have hTT0 : 0 ≤ P.TT := by
    rw [← SSTr.tz_eq P Bs hpl]; exact mul_nonneg hB.2.2.2.1.le hB.2.2.2.2.1.le
  set E : M.Ty P → (Wq →L[ℂ] Wp) := fun σ => e σ 0 with hEdef
  have heE : ∀ σ ζ, e σ ζ = E σ := fun σ ζ => hc σ ζ 0
  have hid : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => w) (Ann P) := contDiff_id.contDiffOn
  have hstar : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => star w) (Ann P) :=
    by
      have h : (fun w : ℂ => star w) = ⇑Complex.conjCLE := by funext w; simp
      rw [h]; exact Complex.conjCLE.contDiff.contDiffOn
  apply Subtype.ext
  funext q
  simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, SetLike.val_smul, Pi.add_apply,
    Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [dzQ_apply P hTT0, dzbQ_apply P hTT0, fnZ_val P hid, fnZ_val P hstar]
  have hcq : q.1.1 ∈ OmX P.r := q.2.1
  have hζq : P.TT < Complex.normSq q.1.2 := q.2.2

  have hsm : ContDiffOn ℝ MA.sm (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) :=
    (trR P Bs e Φ ρ).2
  have hdiff : DifferentiableAt ℝ (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1 :=
    (hsm.differentiableOn (by simp [MA.sm])).differentiableAt ((MA.Qset_open P.r P.TT).mem_nhds q.2)
  have hWa := hW P.r (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1 hdiff

  have hfibq : ∀ φ : ℝ, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
      (NF.muZ P.k P.r Bs.μsec (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))) ∈
        NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) := by
    intro φ
    have hm := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB Φ.1 Φ.2
    have hx : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
      ⟨hcq, by rw [normSq_rot]; exact ann_tz P Bs hpl hζq⟩
    have h2 := hm.2.1 _ hx
    simp only [NF.radR, Set.indicator_of_mem hx] at h2
    exact h2
  have hGy : ∀ φ : ℝ, inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
        (NF.muZ P.k P.r Bs.μsec q.1.2 * zc P.k P.r φ))) =
      Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) * inner ℂ (B.hsVec (E ρ)) (B.hsVec
        ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))))) := by
    intro φ
    have hζe : P.TT < Complex.normSq (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) := by rw [normSq_rot]; exact hζq
    have hexp := (he.2 _ hζe).2.2 _ (hfibq φ)
    simp only [heE] at hexp
    have hM : ∀ σ, inner ℂ (B.hsVec (E ρ)) (B.hsVec (rotA P Bs φ (E σ))) =
        if ρ = σ then Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) else 0 := fun σ => hn φ ρ σ
    rw [rot_eqv hS P Bs hpl hsec Φ q.1.1 hcq q.1.2 hζq φ]
    conv_lhs => rw [hexp]
    rw [rotA_sum, SSTr.hsVec_sum, inner_sum]
    simp only [VLem.hsV_smul, inner_smul_right, hM, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

  have hD : ((q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hB.2.1 hB.2.2.1 hB.2.2.2.2.2.1 (q := q.1) ⟨hcq, ann_tz P Bs hpl hζq⟩
  have hG := hasDerivAt_pair hC P Bs Φ _ hD (E ρ) 1
  simp only [one_mul] at hG
  have hE := hasDerivAt_rotExp (-(n ρ : ℂ))
  have hprod := (hE.mul hG).const_mul ((wR P.k P.TT q.1.2 : ℝ) : ℂ)
  have hpt : ∀ φ : ℝ, MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ) (q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) * (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I) *
        inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
          (NF.muZ P.k P.r Bs.μsec q.1.2 * zc P.k P.r φ)))) := by
    intro φ
    have hmem : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E P.r) ∈ MA.Qset P.r P.TT :=
      ⟨hcq, by rw [normSq_rot]; exact hζq⟩
    unfold MA.ext
    rw [dite_eq_left hmem, SSTr.trR_apply P Bs hpl hk2 e he]
    simp only [rawR]
    rw [wR_rot, heE, hGy φ, ← mul_assoc (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I)), ← Complex.exp_add]
    have h0 : -(n ρ : ℂ) * (φ : ℂ) * Complex.I + (n ρ : ℂ) * (φ : ℂ) * Complex.I = 0 := by ring
    rw [h0, Complex.exp_zero, one_mul]
  have hF := hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall hpt)
  have heq := hWa.unique hF

  have hsum := hRt Φ _ hD
  simp only at hsum
  have hG0 := hGy 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] at hG0 heq
  rw [SSTr.trR_apply P Bs hpl hk2 e he, SSTr.trR_apply P Bs hpl hk2 e he]
  simp only [rawR]
  rw [hG0] at heq
  rw [heE, hsum, VLem.hsV_add, inner_add_right, VLem.hsV_smul, inner_smul_right]
  push_cast
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination -heq

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvEigAP
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem inverse_alpha_positive_holds : RInvAlphaP := by
  intro k r z' w m hz' hw hm M _ _ X
  exact InvEig.usage₅ hz' ((m * w)⁻¹) (InvEigA.inverse_product_block_zero hw hm) (InvEigA.det_inverse_product_block hw hm)
    (InvEigA.zeta_fix hz' hw hm) M X

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGCkExt
section
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckExt_proof : CkExt := by
  intro k r E _ _ F hF hc
  haveI : ProperSpace (B.Mat k r) := FiniteDimensional.proper ℝ _
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_ball (0 : B.Mat k r)
  choose U f' hUo hmem hsm hag using hF
  let V : B.GV k r → Set (B.Mat k r) := fun i => U i.1 i.2 ∩ Metric.ball 0 R
  have hVo : ∀ i, IsOpen (V i) := fun i => (hUo i.1 i.2).inter Metric.isOpen_ball
  have hs : IsClosed (tsupport F ∩ B.GV k r) := (isClosed_tsupport F).inter B5.GV_closed
  have hcov : tsupport F ∩ B.GV k r ⊆ ⋃ i, V i := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx.2⟩, hmem x hx.2, hR hx.1⟩
  obtain ⟨ρ, hρ⟩ := @SmoothPartitionOfUnity.exists_isSubordinate _ (B.Mat k r) _ _ (B.Mat k r) _
    (modelWithCornersSelf ℝ (B.Mat k r)) (B.Mat k r) _ (chartedSpaceSelf _) _ _ _ _ _ hs V hVo hcov
  refine ⟨fun x => ∑ᶠ i, ρ i x • f' i.1 i.2 x, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    refine ρ.contDiffAt_finsum fun i hi => ?_
    have hx : x ∈ U i.1 i.2 := (hρ i hi).1
    exact (hsm i.1 i.2).contDiffAt ((hUo i.1 i.2).mem_nhds hx)
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : B.Mat k r) R) fun x hx => ?_
    have h0 : ∀ i, ρ i x = 0 := fun i => by
      by_contra h
      exact hx (Metric.ball_subset_closedBall (hρ i (subset_tsupport _ h)).2)
    simp [h0]
  · intro g hg
    have key : ∀ i, ρ i g • f' i.1 i.2 g = ρ i g • F g := fun i => by
      by_cases h : ρ i g = 0
      · simp [h]
      · rw [← hag i.1 i.2 g (hρ i (subset_tsupport _ h)).1 hg]
    simp only [key]
    rw [← finsum_smul]
    by_cases hF0 : g ∈ tsupport F
    · rw [ρ.sum_eq_one ⟨hF0, hg⟩, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hF0, smul_zero]

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGParamSmooth
section
open MeasureTheory
open scoped ContDiff Convolution

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

private theorem parameter_smooth_lemma {Pm X W : Type} [NormedAddCommGroup Pm] [NormedSpace ℝ Pm]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (h : Pm → X → W) (s : Set Pm) (K : Set X) (hs : IsOpen s) (hK : IsCompact K)
    (hv : ∀ p ∈ s, ∀ x ∉ K, h p x = 0)
    (hh : ContDiffOn ℝ ∞ (fun q : Pm × X => h q.1 q.2) (s ×ˢ Set.univ)) :
    (∀ p ∈ s, ∀ x ∉ K, (fderiv ℝ (fun q : Pm × X => h q.1 q.2) (p, x)).comp
        (ContinuousLinearMap.inl ℝ Pm X) = 0) ∧
    ContDiffOn ℝ ∞ (fun q : Pm × X => (fderiv ℝ (fun q : Pm × X => h q.1 q.2) (q.1, q.2)).comp
        (ContinuousLinearMap.inl ℝ Pm X)) (s ×ˢ Set.univ) ∧
    ∀ p ∈ s, ∀ x, HasFDerivAt (fun p' => h p' x)
      ((fderiv ℝ (fun q : Pm × X => h q.1 q.2) (p, x)).comp (ContinuousLinearMap.inl ℝ Pm X)) p := by
  have hO : IsOpen (s ×ˢ (Set.univ : Set X)) := hs.prod isOpen_univ
  refine ⟨?_, ?_, ?_⟩
  · intro p hp x hx
    have hU : IsOpen (s ×ˢ Kᶜ) := hs.prod hK.isClosed.isOpen_compl
    have hz : (fun q : Pm × X => h q.1 q.2) =ᶠ[nhds (p, x)] fun _ => 0 := by
      filter_upwards [hU.mem_nhds ⟨hp, hx⟩] with q hq
      exact hv q.1 hq.1 q.2 hq.2
    rw [hz.fderiv_eq]
    simp
  · have h1 : ContDiffOn ℝ ∞ (fun q => fderiv ℝ (fun q : Pm × X => h q.1 q.2) q) (s ×ˢ Set.univ) :=
      hh.fderiv_of_isOpen hO (by simp)
    exact h1.clm_comp contDiffOn_const
  · intro p hp x
    have hd : DifferentiableAt ℝ (fun q : Pm × X => h q.1 q.2) (p, x) :=
      (hh.contDiffAt (hO.mem_nhds ⟨hp, trivial⟩)).differentiableAt (by simp)
    have hl : HasFDerivAt (fun e : Pm => (e, x)) (ContinuousLinearMap.inl ℝ Pm X) p :=
      hasFDerivAt_prodMk_left (𝕜 := ℝ) p x
    exact HasFDerivAt.comp (x := p) hd.hasFDerivAt hl

private theorem parameter_smooth_lemma_2 {Pm X W : Type} [NormedAddCommGroup Pm] [NormedSpace ℝ Pm]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
    [BorelSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (h : Pm → X → W) (D : Pm → X → (Pm →L[ℝ] W)) (s : Set Pm) (K : Set X)
    (hs : IsOpen s) (hK : IsCompact K)
    (hv : ∀ p ∈ s, ∀ x ∉ K, h p x = 0) (hDv : ∀ p ∈ s, ∀ x ∉ K, D p x = 0)
    (hc : ContinuousOn (fun q : Pm × X => h q.1 q.2) (s ×ˢ Set.univ))
    (hDc : ContinuousOn (fun q : Pm × X => D q.1 q.2) (s ×ˢ Set.univ))
    (hD : ∀ p ∈ s, ∀ x, HasFDerivAt (fun p' => h p' x) (D p x) p)
    (p0 : Pm) (hp0 : p0 ∈ s) :
    HasFDerivAt (fun p => ∫ x, h p x ∂μ) (∫ x, D p0 x ∂μ) p0 := by
  have hO : IsOpen (s ×ˢ (Set.univ : Set X)) := hs.prod isOpen_univ
  have hcont : ∀ p ∈ s, Continuous (h p) := fun p hp =>
    hc.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, trivial⟩)
  have hDcont : ∀ p ∈ s, Continuous (D p) := fun p hp =>
    hDc.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, trivial⟩)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hDcont p0 hp0).continuousOn
  have hev : ∀ᶠ p in nhds p0, ∀ x ∈ K, ‖D p x‖ < C + 1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hca : ContinuousAt (fun q : Pm × X => D q.1 q.2) (p0, x) :=
      hDc.continuousAt (hO.mem_nhds ⟨hp0, trivial⟩)
    exact hca.norm.eventually (gt_mem_nhds (lt_of_le_of_lt (hC x hx) (lt_add_one C)))
  have hS : {p | p ∈ s ∧ ∀ x ∈ K, ‖D p x‖ < C + 1} ∈ nhds p0 :=
    Filter.inter_mem (hs.mem_nhds hp0) hev
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := K.indicator fun _ => C + 1) hS
    ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hs.mem_nhds hp0] with p hp
    exact (hcont p hp).aestronglyMeasurable
  · exact (hcont p0 hp0).integrable_of_hasCompactSupport (HasCompactSupport.intro hK (hv p0 hp0))
  · exact (hDcont p0 hp0).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x p hp => ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      exact (hp.2 x hx).le
    · rw [Set.indicator_of_notMem hx, hDv p hp.1 x hx, norm_zero]
  · exact (integrable_indicator_iff hK.isClosed.measurableSet).2
      (integrableOn_const hK.measure_lt_top.ne)
  · exact Filter.Eventually.of_forall fun x p hp => hD p hp.1 x

theorem parameter_smooth : ParamSmooth := by
  intro Pm X W _ _ _ _ _ _ _ _ _ μ _ h s K hs hK hv hh
  have key : ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (g : Pm → X → V),
      (∀ p ∈ s, ∀ x ∉ K, g p x = 0) →
      ContDiffOn ℝ ∞ (fun q : Pm × X => g q.1 q.2) (s ×ˢ Set.univ) →
      ContDiffOn ℝ n (fun p => ∫ x, g p x ∂μ) s := by
    intro n
    induction n with
    | zero =>
      intro V _ _ g hgv hg
      obtain ⟨hDv, hDs, hD⟩ := parameter_smooth_lemma g s K hs hK hgv hg
      have hdiff : DifferentiableOn ℝ (fun p => ∫ x, g p x ∂μ) s := fun p hp =>
        (parameter_smooth_lemma_2 μ g _ s K hs hK hgv hDv hg.continuousOn hDs.continuousOn hD p
          hp).differentiableAt.differentiableWithinAt
      exact contDiffOn_zero.2 hdiff.continuousOn
    | succ n ih =>
      intro V _ _ g hgv hg
      obtain ⟨hDv, hDs, hD⟩ := parameter_smooth_lemma g s K hs hK hgv hg
      have hder := fun p hp =>
        parameter_smooth_lemma_2 μ g _ s K hs hK hgv hDv hg.continuousOn hDs.continuousOn hD p hp
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs]
      refine ⟨fun p hp => (hder p hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact (ih (Pm →L[ℝ] V) (fun p x => (fderiv ℝ (fun q : Pm × X => g q.1 q.2) (p, x)).comp
        (ContinuousLinearMap.inl ℝ Pm X)) hDv hDs).congr fun p hp => (hder p hp).fderiv
  exact contDiffOn_infty.2 fun n => key n W h hv hh

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH_SFG_PtSmooth
section
open MeasureTheory
open scoped ComplexConjugate ContDiff Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PBI Formalism.FourierDecayAlt.P.PBI.Sm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_castM_sfg {k a b : ℕ} (e : a = b) : ContDiff ℝ ∞ (fun g : B.Mat k a => D.castM e g) := by
  subst e
  have h1 : (fun g : B.Mat k a => D.castM rfl g) = fun g => g := by
    funext g
    simp [D.castM]
  rw [h1]
  exact contDiff_id

theorem castM_pt_sfg {k a b : ℕ} (h : a = b) (A M C : B.Mat k a) :
    (D.castM h A)⁻¹ * D.castM h M * D.castM h C = D.castM h (A⁻¹ * M * C) := by
  subst h
  simp [D.castM]

theorem contDiff_radial_embedding {k ρ m : ℕ} (e : ρ + 1 = m) : ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => rn1 e x) := by
  refine contDiff_iff_contDiffAt.2 fun x₀ => ?_
  have hR : ContDiffAt ℝ ∞ (fun x : U.RC k 1 ρ => U.Rn k 1 ρ x) x₀ :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun l => ms_rnC (f := fun y : U.RC k 1 ρ => y) contDiffAt_id i l
  unfold rn1
  exact ((contDiff_castM_sfg e).comp (contDiff_castM_sfg (Nat.add_comm 1 ρ))).contDiffAt.comp x₀ hR

theorem point_smooth : PtSmooth := by
  intro k ρ m e
  constructor
  · have hfun : (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => pt e q.1.1 q.1.2 q.2) =
        fun q => D.castM e (D.castM (Nat.add_comm 1 ρ)
          ((U.Rn k 1 ρ q.2.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => q.1.1) q.1.2 * U.Rn k 1 ρ q.2.2)) := by
      funext q
      unfold pt rn1 mc
      rw [castM_pt_sfg, castM_pt_sfg]
    rw [hfun]
    refine ((contDiff_castM_sfg e).comp (contDiff_castM_sfg (Nat.add_comm 1 ρ))).comp_contDiffOn ?_
    intro q₀ hq₀
    have ht : q₀.1.1 ≠ 0 := hq₀.1
    have hx : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.2.1) q₀ :=
      contDiffAt_fst.comp q₀ contDiffAt_snd
    have hx' : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.2.2) q₀ :=
      contDiffAt_snd.comp q₀ contDiffAt_snd
    have htc : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.1.1) q₀ :=
      contDiffAt_fst.comp q₀ contDiffAt_fst
    have hZ : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) =>
        Matrix.of fun (_ : Fin 1) (_ : Fin 1) => q.1.1) q₀ :=
      ms_ofC (f := fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => fun (_ : Fin 1) (_ : Fin 1) => q.1.1)
        (contDiffAt_pi.2 fun _ => contDiffAt_pi.2 fun _ => htc)
    have hγc : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.1.2) q₀ :=
      contDiffAt_snd.comp q₀ contDiffAt_fst
    have hμ : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.1.2) q₀ := fun i l =>
      contDiffAt_pi.1 (contDiffAt_pi.1 hγc i) l
    have hdet : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => q₀.1.1).det ≠ 0 := by
      rw [Matrix.det_unique]; exact ht
    have hZi : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) =>
        (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => q.1.1)ᴴ⁻¹) q₀ :=
      ms_inv (ms_conjT hZ) (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hdet)
    have hm : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) =>
        U.mMap k 1 ρ (Matrix.of fun _ _ => q.1.1) q.1.2) q₀ := by
      unfold U.mMap
      exact measurable_block_three (ms_const _) (ms_const _) (ms_mul hZi (ms_const _)) (ms_const _) hμ (ms_const _)
        (ms_mul (ms_const _) hZ) (ms_const _) (ms_const _)
    have hall := ms_mul (ms_mul (ms_rnC_inv hx) hm) (ms_rnC hx')
    exact (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun l => hall i l).contDiffWithinAt
  · intro z
    have hg := contDiff_radial_embedding (k := k) e
    have hE : ∀ i l, ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => rn1 e x i l) := fun i l =>
      contDiff_pi.1 (contDiff_pi.1 hg i) l
    have hell : ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => ell k m z (rn1 e x)) := by
      unfold ell
      refine ContDiff.sum fun a _ => ?_
      by_cases h : a.val + 1 < m
      · simp only [dif_pos h]
        exact hE _ _
      · simp only [dif_neg h, Matrix.mulVec, dotProduct]
        exact ContDiff.sum fun b _ => (hE _ _).mul contDiff_const
    unfold psi
    have hre : ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => (((cStd * ell k m z (rn1 e x)).re : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp (contDiff_const.mul hell))
    exact Complex.contDiff_exp.comp (contDiff_const.mul hre)

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntMulOfCpt
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section Wirt

theorem dZ_eq (f : ℂ → ℂ) (c : ℂ) : NF.dZ f c = (1 / 2 : ℂ) * (fderiv ℝ f c 1 - Complex.I * fderiv ℝ f c Complex.I) := rfl

theorem dZ_conj {φ : ℂ → ℂ} {c : ℂ} (h : DifferentiableAt ℝ φ c) :
    NF.dZ (fun w => conj (φ w)) c = conj (NF.dZb φ c) := by
  have hd : HasFDerivAt (fun w => conj (φ w)) ((Complex.conjCLE.toContinuousLinearMap).comp (fderiv ℝ φ c)) c :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp c h.hasFDerivAt
  unfold NF.dZ NF.dZb
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    map_add, map_sub, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

end Wirt

section IBP

end IBP

section Cpt

end Cpt

end Formalism.FourierDecayAlt.P5.HerB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrablePairOfSquareIntegrable
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section L2

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem norm_hs_le (A C : Wq →L[ℂ] Wp) : ‖B.hsInner A C‖ ≤ ‖B.hsInner A A‖ + ‖B.hsInner C C‖ := by
  unfold B.hsInner
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (B.hsVec C) (B.hsVec A)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp only [norm_pow, RCLike.norm_ofReal, Complex.norm_real, abs_norm, norm_norm]
  nlinarith [norm_nonneg (B.hsVec A), norm_nonneg (B.hsVec C), sq_nonneg (‖B.hsVec A‖ - ‖B.hsVec C‖)]

end L2

section Cls

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

end Cls

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Top

end Formalism.FourierDecayAlt.P5.HerB
end
end

