module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0013
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0085
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem isProjVarF_map_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) :
    IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D := by
  classical
  have h := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  exact ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mp h.1, h.2⟩

section Basis

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


end Basis

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionInterpIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology

noncomputable section

namespace BlockResolutionInterpIntegral

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem locDens_interp (d : HSMBlockDatum D K ι Ω) {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA' : IsSmoothHerm A')
    (t : ℝ) (j : Fin d.R.A.n) {y : Fin D → ℂ} (hy : y ∈ (d.R.A.chart j).target) :
    locDens d.R.A (fun _ => blockInterpPot d d.A A' t) j y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
          else AnResBridge.potOf d.R d.A) j y := by
  set x0 := (d.R.A.chart j).symm y with hx0
  set a : (Fin D → ℂ) → ℝ := fun y' => Real.log (d.A.h (d.R.lift x0 ((d.R.A.chart j).symm y'))) with ha
  set b : (Fin D → ℂ) → ℝ := fun y' => Real.log (A'.h (d.R.lift x0 ((d.R.A.chart j).symm y'))) with hb
  have hV : IsOpen ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0) :=
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U x0)
  have hyV : y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0 := ⟨hy, d.R.mem_U x0⟩
  have hsm : ∀ {L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}, IsSmoothHerm L → ∀ᶠ y' in 𝓝 y,
      ContDiffAt ℝ 2 (fun y'' => Real.log (L.h (d.R.lift x0 ((d.R.A.chart j).symm y'')))) y' := by
    intro L hL
    filter_upwards [hV.mem_nhds hyV] with y' hy'
    exact_mod_cast contDiffAt_infty.mp
      ((AnResBridge.contDiffOn_potOf d.R hL x0 j).contDiffAt (hV.mem_nhds hy')) 2
  have hH := gaamix_cxHessian_comb (ψ := fun y' => (1 - t) * a y' + t * b y') (1 - t) t
    (hsm d.semipos.1) (hsm hA') (Filter.EventuallyEq.refl _ _)
  set H₀ := cxHessian a y
  set H₁ := cxHessian b y
  have hL : locDens d.R.A (fun _ => blockInterpPot d d.A A' t) j y =
      ReciprocityTheory.AnForm.maDens (fun _ y' => (1 - t) * a y' + t * b y') y := rfl
  have hR : ∀ i, locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
      else AnResBridge.potOf d.R d.A) j y =
      ReciprocityTheory.AnForm.maDens (fun k => if k.val < i then b else a) y := by
    intro i
    show ReciprocityTheory.AnForm.maDens _ y = _
    congr 1
    funext k y'
    by_cases hk : k.val < i
    · simp only [hk, if_true]; rfl
    · simp only [hk, if_false]; rfl
  have hpure : (fun _ : Fin D => ReciprocityTheory.AnForm.hessC (fun y' => (1 - t) * a y' + t * b y') y) =
      fun _ => (t : ℂ) • H₁ + (1 - (t : ℂ)) • H₀ := by
    funext k
    show cxHessian _ y = _
    rw [hH, add_comm]
    push_cast
    rfl
  have hmix : ∀ i, (fun k : Fin D => ReciprocityTheory.AnForm.hessC (if k.val < i then b else a) y) =
      fun k : Fin D => if k.val < i then H₁ else H₀ := by
    intro i
    funext k
    by_cases hk : k.val < i
    · simp only [hk, if_true]; rfl
    · simp only [hk, if_false]; rfl
  rw [hL]
  simp only [hR]
  unfold ReciprocityTheory.AnForm.maDens
  rw [hpure, ReciprocityTheory.AnForm.A.mdisc_const, ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmix i]
  have e : (D.choose i : ℂ) * (t : ℂ) ^ i * (1 - (t : ℂ)) ^ (D - i) =
      ((D.choose i * t ^ i * (1 - t) ^ (D - i) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  ring

theorem continuous_logRatio (d : HSMBlockDatum D K ι Ω) {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀)
    (hA' : IsSmoothHerm A') :
    Continuous fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x)) := by
  have hA : IsSmoothHerm d.A := d.semipos.1
  have hE : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
      ext z; simp
    rw [e]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hΦ : ContinuousOn (fun z : (Σ k, ι k) → ℂ => Real.log (A'.h z / d.A.h z))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hA'.continuousOn.div hA.continuousOn fun z hz => (d.A.pos z hz).ne').log fun z hz =>
      (div_pos (A'.pos z hz) (d.A.pos z hz)).ne'
  have hdeg' : A'.a = d.A.a := hdeg.trans d.deg.symm
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hU := (d.R.isOpen_U x₀).mem_nhds (d.R.mem_U x₀)
  have hl : ContinuousAt (d.R.lift x₀) x₀ :=
    (continuousOn_pi.2 fun p => AnResBridge.continuousOn_lift d.R x₀ p).continuousAt hU
  have h0 : d.R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (d.R.mem x₀ x₀ (d.R.mem_U x₀)).1
  have h2 : ContinuousAt (fun x => Real.log (A'.h (d.R.lift x₀ x) / d.A.h (d.R.lift x₀ x))) x₀ :=
    (hΦ.continuousAt (hE.mem_nhds h0)).comp hl
  refine h2.congr ?_
  filter_upwards [hU] with x hx
  obtain ⟨c, hc0, he⟩ := d.R.compat x x₀ x ⟨d.R.mem_U x, hx⟩
  show _ = Real.log (A'.h (d.R.lift x x) / d.A.h (d.R.lift x x))
  have hp : (∏ k, ‖c k‖ ^ d.A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc0 k))
  rw [he, A'.smul c _ hc0, d.A.smul c _ hc0, hdeg', mul_div_mul_left _ _ hp]

theorem mInt_interp (d : HSMBlockDatum D K ι Ω) {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀)
    (hA' : IsSmoothHerm A') (t : ℝ) :
    mInt d.R.A (fun _ => blockInterpPot d d.A A' t)
        (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        mInt d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
            else AnResBridge.potOf d.R d.A)
          (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))) := by
  have hg := continuous_logRatio d hdeg hA'
  have hΦ : ∀ (i : ℕ) (k : Fin D), IsPotential d.R.A
      (if k.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A) := by
    intro i k
    split_ifs
    · exact AnResBridge.isPotential_potOf d.R hA'
    · exact AnResBridge.isPotential_potOf d.R d.semipos.1
  unfold mInt
  by_cases hP : Nonempty (ChartPartition d.R.A)
  · simp only [dif_pos hP]
    unfold integralWith
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : ∀ i ∈ Finset.range (D + 1), Integrable (fun y =>
        (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
          (hP.some.χ j ((d.R.A.chart j).symm y) *
            Real.log (A'.h (blockPt d ((d.R.A.chart j).symm y)) / d.A.h (blockPt d ((d.R.A.chart j).symm y))) *
            locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
              else AnResBridge.potOf d.R d.A) j y))
        (volume.restrict (d.R.A.chart j).target) := fun i _ =>
      (integrableOn_weight d.R.A hP.some _ _ (mIntegrableCont d.R.A _ (hΦ i) _ hg) j).const_mul _
    calc _ = ∫ y in (d.R.A.chart j).target, ∑ i ∈ Finset.range (D + 1),
          (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
            (hP.some.χ j ((d.R.A.chart j).symm y) *
              Real.log (A'.h (blockPt d ((d.R.A.chart j).symm y)) /
                d.A.h (blockPt d ((d.R.A.chart j).symm y))) *
              locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
                else AnResBridge.potOf d.R d.A) j y) := by
          refine setIntegral_congr_fun (d.R.A.chart j).open_target.measurableSet fun y hy => ?_
          rw [locDens_interp d hA' t j hy, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [integral_finsetSum _ hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · simp only [dif_neg hP, mul_zero, Finset.sum_const_zero]

theorem proof : BlockResolutionInterpIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' hdeg hA'
  unfold blockMetricInt
  simp only [mInt_interp d hdeg hA']
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_mul_const,
    ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein D i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end BlockResolutionInterpIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtChartUnit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem ClosedPtChartUnit.proof : ClosedPtChartUnit.Statement := by
  classical
  intro S _ K _ ι _ P hP I hI hX f a hf hfP
  have : P.IsPrime := hP.1.1

  have hTP : KH.cellMon S I ≤ P.primeCompl :=
    Submonoid.closure_le.mpr (by rintro _ ⟨k, i, hi, rfl⟩; exact hX k i hi)
  have hPh : NumbersDVR.IsMultiHomogIdeal P := (NumbersDVR.Objects.isMultiHomogIdeal_iff P).mpr hP.1.2.1

  obtain ⟨t, htT, htJ⟩ : ∃ t ∈ KH.cellMon S I, t ∈ P ⊔ Ideal.span {f} := by
    by_contra hno
    push Not at hno
    obtain ⟨p, hp, hJp, hdisj⟩ := Ideal.exists_le_prime_disjoint (P ⊔ Ideal.span {f}) (KH.cellMon S I)
      (Set.disjoint_left.mpr fun x hxJ hxT => hno x hxT hxJ)
    obtain ⟨W, hW, hWh, hWp, hWJ, hWf⟩ := NumbersDVR.exists_multiHomog_core hp
    have hPW : P ≤ W := hWJ P hPh (le_sup_left.trans hJp)
    have hfW : f ∈ W :=
      hWf f a ((NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf)
        (hJp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
    have hrel : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by
      intro k
      obtain ⟨i, hi⟩ := hI k
      refine ⟨i, fun hXW => Set.disjoint_left.mp hdisj (hWp hXW) ?_⟩
      exact Submonoid.subset_closure ⟨k, i, hi, rfl⟩
    have hWP : W = P := hP.2 W ⟨hW, (NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp hWh, hrel⟩ hPW
    exact hfP (hWP ▸ hfW)

  obtain ⟨e, hte'⟩ : ∃ e, NumbersDVR.IsMultiHomog t e := by
    clear htJ
    induction htT using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨k, i, -, rfl⟩ := hx
      exact ⟨_, isWeightedHomogeneous_X S (NumbersDVR.blockWeight ι) ⟨k, i⟩⟩
    | one => exact ⟨0, isWeightedHomogeneous_one S (NumbersDVR.blockWeight ι)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, IsWeightedHomogeneous.mul hc hd⟩
  have hf' : NumbersDVR.IsMultiHomog f a := (NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf
  obtain ⟨p, hpP, r, hr, hpr⟩ := Submodule.mem_sup.mp htJ
  obtain ⟨g₀, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hcomp : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p +
        weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e (g₀ * f) := by
    rw [← hpr, map_add (f := _)]
  have htself : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t = t := by
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hte'), if_pos rfl]
  rw [htself] at hcomp
  have hpe : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p ∈ P := hPh p hpP e
  by_cases hae : a ≤ e
  · refine ⟨t, htT, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (e - a) g₀, e - a, ?_, ?_, ?_⟩
    · rw [add_tsub_cancel_of_le hae]
      exact (NumbersDVR.Objects.isMultiHomog_iff t e).mp hte'
    · exact (NumbersDVR.Objects.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    · rw [NumbersDVR.component_mul_form_of_le hf' hae] at hcomp
      rw [hcomp, add_sub_cancel_right]
      exact hpe
  · rw [NumbersDVR.component_mul_form_of_not_le hf' hae, add_zero] at hcomp
    exact absurd (hcomp ▸ hpe) (hTP htT)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtFibreLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem ClosedPtFibreLift.proof (hG : GradedSubmodules.Statement) (hSES : KH.CechSESStatement)
    (hSky : ClosedPtSkyscraper.Statement) (hKer : LocIdealKer.Statement) : ClosedPtFibreLift.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d _ _ h𝓜 hP hH1 I hI x hx
  have hPh : IsMultiHomogIdeal P := hP.1.2.1
  obtain ⟨h𝓝', h𝓝''⟩ := (hG S K ι M 𝓜 h𝓜).2 P hPh

  have hyd : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ x ∈
      KH.locPart ι (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) (KH.cellMon S I.1) d := by
    obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx
    rw [GenSESStep.locMap_mk]
    exact GenSESStep.mk_mem_locPart _ t a ht ⟨m, hm, rfl⟩

  have hkill : ∀ p ∈ P, ∀ n : M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M), p • n = 0 := by
    intro p hp n
    induction n using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hp Submodule.mem_top

  obtain ⟨z'', hz'', hz''I⟩ := hSky S K ι _ _ P d h𝓝'' hP hkill I hI _ hyd

  have hg : KH.IsMGradedMap S ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) 𝓜
      (P • ⊤ : Submodule (MRingOver S ι) M).subtype := fun _ _ hm => hm
  have hh : KH.IsMGradedMap S ι 𝓜 (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M))
      (P • ⊤ : Submodule (MRingOver S ι) M).mkQ := fun _ m hm => ⟨m, hm, rfl⟩
  obtain ⟨z, hz, hzmap⟩ := (hSES S K ι _ M _ _ 𝓜 _ _ _ h𝓝' h𝓜 h𝓝'' hg hh
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) d 0).2.2.2.2.1 hH1 z'' hz''
  refine ⟨z, hz, ?_⟩
  have hzI : z I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d := Submodule.mem_pi.mp hz.1 I (Set.mem_univ _)

  refine (hKer S K ι M 𝓜 P (KH.cellMon S I.1) d h𝓜 hPh (fun _ ht => GenSESStep.cellMon_homog ht) _
    (sub_mem hx hzI)).2 ?_
  have e : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = z'' I :=
    congrFun hzmap I
  rw [map_sub]
  change _ - GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = 0
  rw [e, hz''I, sub_self]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtSkyscraper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ClosedPtSkyscraper

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cellMon_notMem {P : Ideal (MRingOver S ι)} (hP : P.IsPrime) {J : ∀ k, Finset (ι k)}
    (hJ : ∀ k, ∀ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) {u : MRingOver S ι} (hu : u ∈ KH.cellMon S J) :
    u ∉ P := by
  induction hu using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    exact hJ k i hi
  | one => exact (Ideal.ne_top_iff_one P).mp hP.ne_top
  | mul f f' _ _ hf hf' => exact fun h => (hP.mem_or_mem h).elim hf hf'

theorem loc_eq_zero {N : Type} [AddCommGroup N] [Module (MRingOver S ι) N] {P : Ideal (MRingOver S ι)}
    (hkill : ∀ p ∈ P, ∀ n : N, p • n = 0) {J : ∀ k, Finset (ι k)}
    (hJ : ∃ k, ∃ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∈ P) (x : LocalizedModule (KH.cellMon S J) N) :
    x = 0 := by
  obtain ⟨k, i, hi, hX⟩ := hJ
  induction x using LocalizedModule.induction_on with
  | h n w =>
    rw [← LocalizedModule.zero_mk (1 : KH.cellMon S J), LocalizedModule.mk_eq]
    refine ⟨⟨X ⟨k, i⟩, Submonoid.subset_closure ⟨k, i, hi, rfl⟩⟩, ?_⟩
    simp only [one_smul, smul_zero]
    rw [Submonoid.smul_def]
    exact hkill _ hX n

end ClosedPtSkyscraper

theorem ClosedPtSkyscraper.proof (hU : ClosedPtChartUnit.Statement) : ClosedPtSkyscraper.Statement := by
  classical
  intro S _ K _ _ ι _ _ N _ _ _ _ 𝓝 P d h𝓝 hP hkill I hI y hy
  obtain ⟨m, s, a, hsa, hm, rfl⟩ := GenSESStep.locPart_normal h𝓝 hy
  have hsP : (s : MRingOver S ι) ∉ P := ClosedPtSkyscraper.cellMon_notMem hP.1.1 hI s.2

  have hcong : ∀ p q : MRingOver S ι, p - q ∈ P → ∀ n : N, p • n = q • n := fun p q h n =>
    sub_eq_zero.mp (by rw [← sub_smul]; exact hkill _ h n)

  have hinv : ∀ J : ∀ k, Finset (ι k), (∀ k, (J k).Nonempty) →
      (∀ k, ∀ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
      ∃ t ∈ KH.cellMon S J, ∃ (g : MRingOver S ι) (b : K → ℕ),
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t (a + b) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b ∧ t - g * s ∈ P :=
    fun J hne hJ => hU S K ι P hP J hne hJ s a hsa hsP
  choose t ht g b htb hgb htg using hinv
  let z : KH.CechC S ι N 0 := fun J =>
    if hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P then
      LocalizedModule.mk (g J.1 J.2.1 hJ • m) ⟨t J.1 J.2.1 hJ, ht J.1 J.2.1 hJ⟩
    else 0

  have hagree : ∀ (J : KH.Cell K ι 0) (hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P)
      (u h' t' : MRingOver S ι), u - h' * s ∈ P →
      (u * t' * g J.1 J.2.1 hJ) • m = (h' * t' * t J.1 J.2.1 hJ) • m := by
    intro J hJ u h' t' hu
    refine hcong _ _ ?_ m
    have := sub_mem (P.mul_mem_right (t' * g J.1 J.2.1 hJ) hu) (P.mul_mem_left (h' * t') (htg J.1 J.2.1 hJ))
    convert this using 1
    ring
  refine ⟨z, ⟨Submodule.mem_pi.mpr fun J _ => ?_, LinearMap.mem_ker.mpr (funext fun E => ?_)⟩, ?_⟩
  ·
    by_cases hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P
    · simp only [z, dif_pos hJ]
      refine GenSESStep.mk_mem_locPart _ _ (a + b J.1 J.2.1 hJ) (htb J.1 J.2.1 hJ) ?_
      have e : (d + fun k => ((a + b J.1 J.2.1 hJ) k : ℤ)) =
          (d + fun k => (a k : ℤ)) + fun k => (b J.1 J.2.1 hJ k : ℤ) := by
        funext k
        simp only [Pi.add_apply, Nat.cast_add]
        ring
      rw [e]
      exact h𝓝.2 _ _ _ _ (hgb J.1 J.2.1 hJ) hm
    · simp only [z, dif_neg hJ]
      exact zero_mem _
  ·
    obtain ⟨J₁, J₂, h₁, h₂, σ, -, hD⟩ := GenTwistGenerated.cechD_zero_apply (S := S) (M := N) E
    rw [Pi.zero_apply, hD z]
    by_cases hE : ∀ k, ∀ i ∈ E.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P
    · have hJ₁ : ∀ k, ∀ i ∈ J₁.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P := fun k i hi => hE k i (h₁ k hi)
      have hJ₂ : ∀ k, ∀ i ∈ J₂.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P := fun k i hi => hE k i (h₂ k hi)
      obtain ⟨u, hu, h', -, -, -, huP⟩ := hU S K ι P hP E.1 E.2.1 hE s a hsa hsP
      simp only [z, dif_pos hJ₁, dif_pos hJ₂]
      rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₁),
        GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₂)]
      have heq : LocalizedModule.mk (g J₁.1 J₁.2.1 hJ₁ • m)
            (⟨t J₁.1 J₁.2.1 hJ₁, GenTwistGenerated.cellMon_mono h₁ (ht J₁.1 J₁.2.1 hJ₁)⟩ : KH.cellMon S E.1) =
          LocalizedModule.mk (g J₂.1 J₂.2.1 hJ₂ • m)
            ⟨t J₂.1 J₂.2.1 hJ₂, GenTwistGenerated.cellMon_mono h₂ (ht J₂.1 J₂.2.1 hJ₂)⟩ := by
        refine LocalizedModule.mk_eq.mpr ⟨⟨u, hu⟩, ?_⟩
        simp only [Submonoid.smul_def, smul_smul]
        rw [← mul_assoc, ← mul_assoc, hagree J₁ hJ₁ u h' (t J₂.1 J₂.2.1 hJ₂) huP,
          hagree J₂ hJ₂ u h' (t J₁.1 J₁.2.1 hJ₁) huP]
        congr 1
        ring
      rw [heq, sub_self]
      exact zsmul_zero σ
    · push Not at hE
      exact ClosedPtSkyscraper.loc_eq_zero hkill hE _
  ·
    simp only [z, dif_pos hI]
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_smul]
    exact (hcong _ _ (by rw [mul_comm]; exact htg I.1 I.2.1 hI) m).symm

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

