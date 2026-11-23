module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0019

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ModelProjObjects
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}

def modelU (M : CxModel P e) (x : M.Xc) : Set M.Xc :=
  (M.sections x).choose

def modelLift (M : CxModel P e) (x : M.Xc) : M.Xc → (Σ k, ι k) → ℂ :=
  (M.sections x).choose_spec.2.2.choose

theorem modelU_isOpen (M : CxModel P e) (x : M.Xc) : IsOpen (modelU M x) :=
  (M.sections x).choose_spec.1

theorem mem_modelU (M : CxModel P e) (x : M.Xc) : x ∈ modelU M x :=
  (M.sections x).choose_spec.2.1

theorem modelLift_spec (M : CxModel P e) (x : M.Xc) :
    (∀ y ∈ modelU M x, modelLift M x y ∈ mcPts P ∧ M.proj (modelLift M x y) = y) ∧
      ∀ p, M.atlas.HoloOn (modelU M x) fun y => modelLift M x y p :=
  (M.sections x).choose_spec.2.2.choose_spec

def modelPot (M : CxModel P e) (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) : LocPot M.Xc where
  U := modelU M
  isOpen_U := modelU_isOpen M
  mem_U := mem_modelU M
  φ x y := c * Real.log (L.h (modelLift M x y))

def modelQ (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : M.Xc) : Fin e → ℂ :=
  fun i => Ψ (segre (modelLift M x x)) i.succ / Ψ (segre (modelLift M x x)) 0

def modelCrit (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set M.Xc :=
  {x | Ψ (segre (modelLift M x x)) 0 = 0 ∨ ∃ j, x ∈ (M.atlas.chart j).source ∧
    ¬ (AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) ∧
      LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def modelBad (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (E : Set M.Xc) : Set M.Xc :=
  E ∪ modelCrit M Ψ

theorem modelQ_good_of_notMem (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (E : Set M.Xc) : ∀ x ∉ modelBad M Ψ E, ∀ j, x ∈ (M.atlas.chart j).source →
      AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) ∧
        LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  intro x hx j hj
  by_contra h
  exact hx (Or.inr (Or.inr ⟨j, hj, h⟩))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBoundaryNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem BoundaryNull.proof : BoundaryNull.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D
  classical
  exact BoundaryPtsNull.proof II Ψ K ι Ω E D

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelLogIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.A (coordDiv)

namespace ModelLogIntegrableAlt

theorem volume_coordDiv {D : ℕ} (S : Finset (Fin D)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  refine (measure_biUnion_null_iff S.countable_toSet).2 fun i _ => ?_
  rw [volume_pi]
  exact Measure.pi_eval_preimage_null _ (measure_singleton 0)

theorem target_inter_compl_Yo_subset {D : ℕ} {X : Type*} [TopologicalSpace X]
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X} (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (j : Fin R.N) :
    (R.chart j).target ∩ (R.chart j).symm ⁻¹' R.Yoᶜ ⊆ coordDiv (R.S j) := by
  rintro y ⟨hy, hyY⟩
  have h := R.mem_Yo j _ ((R.chart j).map_target hy)
  rw [(R.chart j).right_inv hy] at h
  by_contra hc
  exact hyY (h.2 hc)

end ModelLogIntegrableAlt


open ModelLogIntegrableAlt in
theorem ModelLogIntegrable.proof (hM : ModelPtsIntegrable.Statement) : ModelLogIntegrable.Statement := by
  intro K _ ι _ P e M R L c N u C C' g hP hL hN hu hbd hg
  let _ : MeasurableSpace M.Xc := borel M.Xc
  have _ : BorelSpace M.Xc := ⟨rfl⟩
  obtain ⟨B, hB⟩ := R.f_bdd
  refine hM K ι P e M R.N R.chart L c N R.Yoᶜ u g hP hL hN R.compat (fun x => ?_)
    (fun j => measure_mono_null (target_inter_compl_Yo_subset R j) (GroundTheory.Heights₂.Heights.LowerBoundFree.ModelLogIntegrableAlt.volume_coordDiv _))
    (fun j Q hQ hQc => ?_) (fun z hz hzN hzE => hg z hz hzN (not_not.mp hzE))
  · obtain ⟨j, hj⟩ := R.cover x
    exact ⟨j, R.toPotentialCharts.mid_subset_source j (R.toPotentialCharts.inner_subset_mid j hj)⟩

  have hQp : Q ⊆ GroundTheory.Heights₂.Heights.LogInt.polydisc (Fin e) 1 := by
    intro y hy
    have hb : ‖y‖ < 1 := by simpa using R.target_subset j (hQ hy)
    intro i _
    simpa using (norm_le_pi_norm y i).trans hb.le
  set G : (Fin e → ℂ) → ℝ := fun y => |C| + |C'| * (Real.exp 1 + B) +
    |C'| * ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| with hGdef
  have hG : IntegrableOn G Q := by
    refine IntegrableOn.mono_set ?_ hQp
    refine ((integrableOn_const (GroundTheory.Heights₂.Heights.LogInt.volume_polydisc_ne_top 1)).add
      (Integrable.const_mul (integrable_finsetSum _ fun i _ =>
        ((GroundTheory.Heights₂.Heights.LogInt.integrableOn_log_norm_coord 1 i).abs.const_mul 2)) _))
  have hmeas : AEStronglyMeasurable (fun y => u ((R.chart j).symm y)) (volume.restrict Q) :=
    (hu.comp_aemeasurable (((R.chart j).continuousOn_symm.mono hQ).aemeasurable
      hQc.isClosed.measurableSet)).aestronglyMeasurable
  refine Integrable.mono' hG hmeas ?_
  filter_upwards [ae_restrict_mem hQc.isClosed.measurableSet,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (GroundTheory.Heights₂.Heights.LowerBoundFree.ModelLogIntegrableAlt.volume_coordDiv (R.S j)))] with y hyQ hyD
  have hyt := hQ hyQ
  have hYo : (R.chart j).symm y ∈ R.Yo := by
    have h := R.mem_Yo j _ ((R.chart j).map_target hyt)
    rw [(R.chart j).right_inv hyt] at h
    exact h.2 hyD
  have h1 := hbd _ hYo
  have hr1 := R.one_le_r _ hYo
  have hrc := R.r_chart j y ⟨hyt, hyD⟩
  set r := R.r ((R.chart j).symm y) with hrdef
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlogr : Real.log r ≤ r := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < r)]
  have hf : R.f j y ≤ B := (le_abs_self _).trans (hB j y hyt)
  have hsum : ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.log_inv, Real.log_pow]
    push_cast
    linarith [neg_abs_le (Real.log ‖y i‖)]
  have hrb : r ≤ Real.exp 1 + B + ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    rw [hrc]; linarith
  have hC : C + C' * Real.log r ≤ |C| + |C'| * r := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C') hlog0
    have := mul_le_mul_of_nonneg_left hlogr (abs_nonneg C')
    linarith [le_abs_self C]
  have hC2 : |C'| * r ≤ |C'| * (Real.exp 1 + B) + |C'| * ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C')
  rw [Real.norm_eq_abs, hGdef]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuSheetLeviNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData)
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem analyticAt_pi_of_eventually_differentiableAt {d m : ℕ} {f : (Fin d → ℂ) → Fin m → ℂ} {y : Fin d → ℂ}
    (h : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ f y') : AnalyticAt ℂ f y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.1 h
  refine AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood d U (fun w => f w i) hUo (fun z hz => ?_) y hyU
  exact (differentiableAt_pi.mp (hU z hz) i).differentiableWithinAt

theorem RegChartData.contDiffAt_u {n : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas n X}
    (R : RegChartData A) (j : Fin R.N) {ξ : Fin n → ℂ} (hξ : ξ ∈ (R.chart j).target \ coordDiv (R.S j)) :
    ContDiffAt ℝ 2 (R.u j) ξ := by
  have hp : (R.chart j).symm ξ ∈ (R.chart j).source := (R.chart j).map_target hξ.1
  have hYo : R.Yo ∈ 𝓝 ((R.chart j).symm ξ) := by
    refine Filter.mem_of_superset (((R.chart j).isOpen_inter_preimage
      (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed (R.S j)).isOpen_compl).mem_nhds ⟨hp, ?_⟩)
      fun x hx => (R.mem_Yo j x hx.1).2 hx.2
    change (R.chart j) ((R.chart j).symm ξ) ∉ coordDiv (R.S j)
    rw [(R.chart j).right_inv hξ.1]
    exact hξ.2
  obtain ⟨i, hi⟩ := A.cover ((R.chart j).symm ξ)
  have hti : (A.chart i) ((R.chart j).symm ξ) ∈ (A.chart i).target := (A.chart i).map_source hi
  have h1 : ContDiffAt ℝ 2 (R.ph ∘ (A.chart i).symm) ((A.chart i) ((R.chart j).symm ξ)) := by
    refine ((R.ph_smooth i).contDiffAt (Filter.inter_mem ((A.chart i).open_target.mem_nhds hti) ?_)).of_le
      (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
    refine (A.chart i).continuousAt_symm hti |>.preimage_mem_nhds ?_
    rw [(A.chart i).left_inv hi]
    exact hYo
  have hτ : AnalyticAt ℂ ((A.chart i) ∘ (R.chart j).symm) ξ := ((R.compat j i).2) ξ ⟨hξ.1, hi⟩
  have h2 : ContDiffAt ℝ 2 (fun ξ' => R.ph ((R.chart j).symm ξ')) ξ := by
    refine (h1.comp ξ hτ.restrictScalars.contDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [(R.chart j).continuousAt_symm hξ.1 |>.preimage_mem_nhds
      ((A.chart i).open_source.mem_nhds hi)] with ξ' h
    simp only [Function.comp_apply, (A.chart i).left_inv h]
  have hq : ContDiffAt ℝ 2 (R.q j) ξ :=
    ((R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds hξ.1)).of_le (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
  exact hq.add h2

theorem LogLogRegularisationSetting.log_h_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {n : ℕ} {M : CxModel P n} {Xo : Set ((Σ k, ι k) → ℂ)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (S : LogLogRegularisationSetting M Xo A)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hY : M.proj z ∈ S.R.Yo) :
    Real.log (A.h z) = S.R.ph (M.proj z) + Real.log (S.ref.h z) := by
  obtain ⟨z', ⟨hz'o, hz'⟩, hp⟩ := S.Yo_sub _ hY
  obtain ⟨c, hc, rfl⟩ := (M.fibre z' hz' _ hz).1 hp
  have hph := S.ph_eq z' ⟨hz'o, hz'⟩ (by rw [hp]; exact hY)
  have hA : A.h (torusSmul c z') = (∏ k, ‖c k‖ ^ A.a k) * A.h z' := A.smul c z' hc
  have hR : S.ref.h (torusSmul c z') = (∏ k, ‖c k‖ ^ A.a k) * S.ref.h z' := by
    rw [← S.ref_deg]; exact S.ref.smul c z' hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  rw [hA, hR, Real.log_mul hpos.ne' (A.pos z' hz'.1).ne', Real.log_mul hpos.ne' (S.ref.pos z' hz'.1).ne', ← hp,
    hph]
  ring

theorem MuSheetLeviNonneg.proof (hH : SheetChartHolo.Statement) (hR : RefAlongSheet.Statement) :
    MuSheetLeviNonneg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X Q _
  filter_upwards [hH K ι (mCoordIdeal D.y) D.n X.M X.S.R Q] with y hy w γ hγ
  obtain ⟨j, hsrc, hYo, hev⟩ := hy w γ hγ
  have hγev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts (mCoordIdeal D.y) :=
    hγ.2.mono fun _ h => ⟨h.1, h.2.1⟩
  obtain ⟨G, hG, hGeq⟩ := hR K ι _ D.n X.M D.Xo (muLine X.H) X.S γ y j hγev hsrc hev
  set g : (Fin D.n → ℂ) → Fin D.n → ℂ := fun y'' => X.S.R.chart j (X.M.proj (γ y'')) with hgdef
  have hg : AnalyticAt ℂ g y := analyticAt_pi_of_eventually_differentiableAt (hev.mono fun _ h => h.2)
  have hgy : g y ∈ (X.S.R.chart j).target \ coordDiv (X.S.R.S j) :=
    ⟨(X.S.R.chart j).map_source hsrc, (X.S.R.mem_Yo j _ hsrc).1 hYo⟩
  have hUo : IsOpen ((X.S.R.chart j).target \ coordDiv (X.S.R.S j)) :=
    (X.S.R.chart j).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have hC2 : ContDiffOn ℝ 2 (X.S.R.u j) ((X.S.R.chart j).target \ coordDiv (X.S.R.S j)) :=
    fun ξ hξ => (RegChartData.contDiffAt_u X.S.R j hξ).contDiffWithinAt
  have hL := ((ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm _ _ _ hUo hC2).1 (X.S.R.u_psh j)).2
  have hgU : ∀ᶠ y' in 𝓝 y, g y' ∈ (X.S.R.chart j).target \ coordDiv (X.S.R.S j) :=
    hg.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgy)
  have heq : (fun y' => phMu X.H (γ y')) =ᶠ[𝓝 y] fun y' => (X.S.R.u j ∘ g) y' + 1 * (G y').re := by
    filter_upwards [hγev, hev, hgU, hGeq] with y' h1 h2 h3 h4
    have hY' : X.M.proj (γ y') ∈ X.S.R.Yo := (X.S.R.mem_Yo j _ h2.1).2 h3.2
    have hl := X.S.log_h_eq h1.2 hY'
    show Real.log ((muLine X.H).h (γ y')) =
      X.S.R.q j (g y') + X.S.R.ph ((X.S.R.chart j).symm (g y')) + 1 * (G y').re
    rw [hl, h4, hgdef]
    simp only [(X.S.R.chart j).left_inv h2.1]
    ring
  have hu2 : ContDiffAt ℝ 2 (X.S.R.u j) (g y) := RegChartData.contDiffAt_u X.S.R j hgy
  have hcomp : ContDiffAt ℝ 2 (X.S.R.u j ∘ g) y := hu2.comp y hg.restrictScalars.contDiffAt
  have hre : ContDiffAt ℝ 2 (fun y' => (G y').re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hG.restrictScalars.contDiffAt
  refine ⟨(hcomp.add (contDiffAt_const.mul hre)).congr_of_eventuallyEq heq, fun v => ?_⟩
  change 0 ≤ levi (fun y' => phMu X.H (γ y')) y v
  rw [ReciprocityTheory.AnForm.levi_congr heq, ReciprocityTheory.AnForm.levi_add_smul 1 hcomp hre,
    ReciprocityTheory.AnForm.levi_re_analytic hG, ReciprocityTheory.AnForm.levi_comp v hg hu2]
  simpa using hL _ hgy _

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace NbarSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smoothAlong_pow {S : Set ((Σ k, ι k) → ℂ)} {f : ((Σ k, ι k) → ℂ) → ℝ} (hf : SmoothAlong S f) (n : ℕ) :
    SmoothAlong S fun z => f z ^ n := by
  intro z hz
  obtain ⟨U, hU, F, hF, hfF⟩ := hf z hz
  exact ⟨U, hU, fun w => F w ^ n, hF.pow n, fun w hw => by show f w ^ n = F w ^ n; rw [hfF w hw]⟩

theorem hermOfFun_h_of_mem {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {a : K → ℤ}
    {F : ((Σ k, ι k) → ℂ) → ℝ}
    (hF : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hpos : 0 < F z) : (hermOfFun ι a F).h z = F z := by
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  set w := orbitRep z with hw
  have hwz : w = torusSmul c⁻¹ z := by
    funext p
    rw [hzc]
    simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]
  have hcinv : ∀ k, c⁻¹ k ≠ 0 := fun k => by simpa using hc k
  have hwP : w ∈ mcPts P := by rw [hwz]; exact mcPts_smul hP c⁻¹ hcinv hz
  have hP' := prod_norm_zpow_pos hc a
  have hFz : F z = (∏ k, ‖c k‖ ^ a k) * F w := by rw [hzc]; exact hF w hwP c hc
  have hRz : refNorm a z = (∏ k, ‖c k‖ ^ a k) * refNorm a w := by rw [hzc]; exact refNorm_smul a c w
  have hFw : 0 < F w := by
    rw [hFz] at hpos
    exact pos_of_mul_pos_right hpos hP'.le
  have hRw := refNorm_pos a hwP.1
  show refNorm a z * Real.exp (Real.log (F w / refNorm a w)) = F z
  rw [Real.exp_log (div_pos hFw hRw), hRz, hFz]
  field_simp

end NbarSmooth


open MuRegSmooth TopNPoly NbarSmooth in
theorem NbarSmooth.proof (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement)
    (hVS : VertFactorSmooth.Statement) : NbarSmooth.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q t hsm
  set P := mCoordIdeal D.y with hPdef
  set a : K → ℤ := (q : ℤ) • muTwDeg X.H B + (p : ℤ) • D.a' with ha
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z => (X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z))) ^ q *
    (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p with hFdef
  have hSB : ∀ p' ∈ D.SB B, p' ∈ D.S := fun p' hp' => (Finset.mem_filter.1 hp').1
  have hMH : IsMultiHomogIdeal P := D.arith.2.1.2.1
  have hpos : ∀ z ∈ mcPts P, 0 < F z := by
    intro z hz
    have h2 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' z := Finset.prod_pos fun p' hp' =>
      VertFactorPos.proof II Ψ K ι Ω E D p' (hSB p' hp') z hz
    exact mul_pos (mul_pos (pow_pos (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _)) q) (pow_pos h2 q))
      (pow_pos (D.A'.pos z hz.1) p)
  have hhom : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts P := mcPts_smul hMH c hc hz
    have hproj : X.M.proj (torusSmul c z) = X.M.proj z := ((X.M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * X.S.ref.h z := by
      have := X.S.ref.smul c z hc
      rw [X.S.ref_deg] at this
      exact this
    have hA : D.A'.h (torusSmul c z) = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h z := by
      have := D.A'.smul c z hc
      rw [D.A'_deg] at this
      exact this
    have hV : ∀ p' ∈ D.SB B, D.vertFactor p' (torusSmul c z) =
        (∏ k, ‖c k‖ ^ D.vdeg p' k) * D.vertFactor p' z :=
      fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).1 z hz c hc
    have hk : ∀ k, ‖c k‖ ^ a k = (‖c k‖ ^ (muTwDeg X.H B) k) ^ q * (‖c k‖ ^ D.a' k) ^ p := by
      intro k
      have hx : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      have hak : a k = (q : ℤ) * (muTwDeg X.H B) k + (p : ℤ) * D.a' k := by
        simp only [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hak, zpow_add₀ hx, zpow_mul', zpow_natCast, zpow_mul', zpow_natCast]
    have hprod : (∏ k, ‖c k‖ ^ a k) = ((∏ k, ‖c k‖ ^ X.H.aMu k) *
        ∏ p' ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p' k) ^ q * (∏ k, ‖c k‖ ^ D.a' k) ^ p := by
      rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
        muTwDeg, prod_norm_zpow_add_sum hc]
    simp only [hFdef]
    rw [hproj, href, hA, Finset.prod_congr rfl hV, Finset.prod_mul_distrib, hprod]
    ring
  have hsmooth : SmoothAlong (mcPts P) F :=
    smoothAlong_mul (smoothAlong_mul
      (smoothAlong_pow (smoothAlong_mul (smoothAlong_of_contDiffOn X.S.ref_smooth)
        (smoothAlong_exp (hP II Ψ K ι Ω E D X.M _ hsm))) q)
      (smoothAlong_pow (smoothAlong_prod _ fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).2) q))
      (smoothAlong_pow (smoothAlong_of_contDiffOn D.A'_pos.1) p)
  obtain ⟨Z, hZa, hZs, hZh⟩ := hE K ι P a F hMH hpos hhom hsmooth
  show IsSmoothHerm (smoothRep P (hermOfFun ι a F))
  exact smoothRep_smooth_of (Z := Z) hZa hZs fun z hz =>
    (hZh z hz).trans (hermOfFun_h_of_mem hMH hhom hz (hpos z hz)).symm

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNVbInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem OmNVbInt.proof (hT : TpCuspIntegrable.Statement) (hS : NbarSmooth.Statement) : OmNVbInt.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q _ _
  filter_upwards [X.S.eventually_chartLevi X.S_tied] with t ht
  exact hT II Ψ K ι Ω E D O Lt X B p q t (hS II Ψ K ι Ω E D O Lt X B p q t ht.1)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StAPrimeChartMargin
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def APrimeChartMargin.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt),
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, ∀ k : Fin X.S.R.N, X.M.proj z ∈ X.S.R.mid k →
      ∀ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v →
        c * ‖v‖ ^ 2 ≤ levi (fun y => Real.log (D.A'.h y)) z w

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StProjHoloLocal
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ProjHoloLocal.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)), ReciprocityTheory.AnForm.M.IsCompatChart M.atlas e →
    ∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ e.source →
      ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧ ∃ F : ((Σ k, ι k) → ℂ) → Fin D.n → ℂ,
        DifferentiableOn ℂ F W ∧
          ∀ z' ∈ W ∩ mcPts (mCoordIdeal D.y), M.proj z' ∈ e.source ∧ e (M.proj z') = F z'

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

