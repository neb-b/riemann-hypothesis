module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelFnMulEqZeroOfIsForm
section
set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem dens_zero : dens (0 : Alt n) = 0 := by simp [dens]

theorem delAt_eq_zero_of_eventually {F : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] fun _ => 0) : delAt F v = 0 := by
  have hS : ∀ S, GlobalTheory.del (fun x => (bas n).repr (F x) S) v = 0 := fun S => by
    have e : (fun x => (bas n).repr (F x) S) =ᶠ[𝓝 v] fun _ => 0 := h.mono fun x hx => by simp [hx]
    rw [GlobalTheory.del_congr e]
    exact GlobalTheory.del_const _ _
  simp [delAt, coefwise, hS]

theorem del_integral {f : V n → ℂ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (u : V n) :
    Integrable (fun v => GlobalTheory.del f v u) ∧ ∫ v, GlobalTheory.del f v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ f y w) := fun w =>
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  have hD : Integrable (fun v => GlobalTheory.del f v u) := by
    simp only [GlobalTheory.del_apply, smul_eq_mul]
    exact ((hint _).sub ((hint _).const_mul _)).const_mul _
  refine ⟨hD, ?_⟩
  simp only [GlobalTheory.del_apply, smul_eq_mul]
  rw [integral_const_mul, integral_sub (hint _) ((hint _).const_mul _), integral_const_mul,
    ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n f hf hc, ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n f hf hc]
  simp

theorem dens_delAt (F : V n → Alt n) (v : V n) : dens (delAt F v) =
    ∑ a, ∑ S, GlobalTheory.del (fun x => (bas n).repr (F x) S) v (coordVec a) *
      ((bas n).repr (dz a * bas n S) Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dens, delAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

theorem integral_dens_delAt {F : V n → Alt n} (hF : ∀ S, ContDiff ℝ 1 fun v => (bas n).repr (F v) S)
    (hc : ∀ S, HasCompactSupport fun v => (bas n).repr (F v) S) :
    Integrable (fun v => dens (delAt F v)) ∧ ∫ v, dens (delAt F v) = 0 := by
  have hi : ∀ a S, Integrable fun v => GlobalTheory.del (fun x => (bas n).repr (F x) S) v (coordVec a) *
      ((bas n).repr (dz a * bas n S) Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ) :=
    fun a S => (del_integral (hF S) (hc S) _).1.mul_const _
  simp only [dens_delAt]
  refine ⟨integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S, ?_⟩
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun S _ => hi a S]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [integral_mul_const, (del_integral (hF S) (hc S) _).2, zero_mul]

end GlobalTheory.CxForm.LocStokes

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem integral_eq_of_vanish {M : Type} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α) (i : A.ι) {K : Set M} (hKm : MeasurableSet K)
    (hKs : K ⊆ (A.e i).source) (h0 : ∀ x : A.Pt, x.pt ∉ K → α x = 0)
    (hI : Integrable fun v => (dens (A.loc α i v)).re) :
    A.integral α = ∫ v, (dens (A.loc α i v)).re := by
  have hl : ∀ j y (hy : y ∈ (A.e j).source), A.loc α j (A.e j y) = α ⟨(j, y), hy⟩ := fun j y hy =>
    A.loc_crd α ⟨(j, y), hy⟩
  have hρ : ∀ (ε : ℤˣ) j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
      ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re) =
      ENNReal.ofReal (‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2) *
        ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α k (A.e k y))).re) := by
    intro ε j k y hj hk
    rw [hl j y hj, hl k y hk, hα.compat ⟨(j, y), hj⟩ ⟨(k, y), hk⟩ rfl, dens_pull,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    simp only [ChartGlue.transDet, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hz : ∀ (ε : ℤˣ) j y, y ∈ (A.e j).source → y ∉ K →
      ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re) = 0 := by
    intro ε j y hy hyK
    rw [hl j y hy, h0 ⟨(j, y), hy⟩ hyK, dens_zero]
    simp
  have hc : ∀ ε : ℤˣ, A.part α ε Kᶜ = 0 := fun ε => by
    have key : A.part α ε ≤ (A.part α ε).restrict K := iSup_le fun j => by
      have e : ChartGlue.chartMeas (A.e j)
          (fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re)) Kᶜ = 0 := by
        rw [ChartGlue.chartMeas_apply _ _ hKm.compl]
        refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
          ((A.e j).open_source.measurableSet.inter hKm.compl) Set.inter_subset_left) ?_
        rintro _ ⟨y, hy, rfl⟩
        simp only [(A.e j).left_inv hy.1]
        exact hz ε j y hy.1 hy.2
      rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
      exact Measure.restrict_mono le_rfl (le_iSup (fun j => ChartGlue.chartMeas (A.e j)
        fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re)) j)
    refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
    rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
  have hv : ∀ v, v ∉ (A.e i) '' K → (dens (A.loc α i v)).re = 0 := fun v hv => by
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dite_eq_left ht, h0 ⟨(i, (A.e i).symm v), (A.e i).map_target ht⟩
        fun h => hv ⟨_, h, (A.e i).right_inv ht⟩, dens_zero, Complex.zero_re]
    · rw [HolAtlas.loc, dite_eq_right ht, dens_zero, Complex.zero_re]
  have hp : ∀ ε : ℤˣ, A.part α ε univ = ∫⁻ v, ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α i v)).re) := fun ε => by
    rw [← measure_add_measure_compl hKm, hc ε, add_zero, HolAtlas.part,
      ChartGlue.glueMeas_apply A.e _ (fun j k => A.holo j k) (hρ ε) i hKm hKs,
      ChartGlue.chartMeas_apply_of_subset _ _ hKm hKs,
      ← lintegral_indicator (ChartGlue.measurableSet_image _ hKm hKs)]
    refine lintegral_congr fun v => ?_
    by_cases hvK : v ∈ (A.e i) '' K
    · obtain ⟨y, hy, rfl⟩ := hvK
      rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hy), (A.e i).left_inv (hKs hy)]
    · rw [Set.indicator_of_notMem hvK, hv v hvK, mul_zero, ENNReal.ofReal_zero]
  rw [HolAtlas.integral, measureReal_def, measureReal_def, hp, hp,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
  simp

end GlobalTheory.CxForm.LocStokes

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem integral_del_fn_mul_eq_zero_of_isForm {M : Type} [TopologicalSpace M] [CompactSpace M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (A : HolAtlas M n) (γ : A.Fld) (χ : M → ℝ)
    (i : A.ι) (hγ : A.IsForm γ) (hχ : A.SmoothOn univ (fun y => (χ y : ℂ))) (hs : tsupport χ ⊆ (A.e i).source)
    (hd : A.IsForm (A.del (A.fn χ * γ))) : A.integral (A.del (A.fn χ * γ)) = 0 := by
  set β : A.Fld := A.fn χ * γ with hβdef
  set K : Set M := tsupport χ with hKdef
  have hKc : IsCompact K := (isClosed_tsupport χ).isCompact
  have hKm : MeasurableSet K := (isClosed_tsupport χ).measurableSet
  have hβ : A.IsForm β := FormMul.isForm_mul A _ _ (A.isForm_fn hχ) hγ
  have hβ0 : ∀ x : A.Pt, x.pt ∉ K → β x = 0 := fun x hx => by
    simp [hβdef, HolAtlas.fn, image_eq_zero_of_notMem_tsupport hx]

  have hβn : ∀ j, ∀ y ∈ (A.e j).source, y ∉ K → A.loc β j =ᶠ[𝓝 (A.e j y)] fun _ => 0 := fun j y hy hyK => by
    filter_upwards [(ChartGlue.isOpen_over (A.e j) (isClosed_tsupport χ).isOpen_compl).mem_nhds
      (ChartGlue.mem_over (A.e j) (S := Kᶜ) hy hyK)] with w hw
    rw [HolAtlas.loc, dite_eq_left hw.1]
    exact hβ0 _ hw.2
  have hd0 : ∀ x : A.Pt, x.pt ∉ K → A.del β x = 0 := fun x hx =>
    delAt_eq_zero_of_eventually (hβn x.1.1 x.pt x.2 hx)

  set F : V n → Alt n := A.loc β i with hFdef
  set AK : Set (V n) := (A.e i) '' K with hAKdef
  have hAK : IsCompact AK := hKc.image_of_continuousOn ((A.e i).continuousOn.mono hs)
  have hAKt : AK ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hs hy)
  have hF0 : ∀ v ∉ AK, F v = 0 := fun v hv => by
    by_cases ht : v ∈ (A.e i).target
    · rw [hFdef, HolAtlas.loc, dite_eq_left ht]
      exact hβ0 _ fun h => hv ⟨_, h, (A.e i).right_inv ht⟩
    · rw [hFdef, HolAtlas.loc, dite_eq_right ht]
  have hFA : ∀ v ∉ AK, F =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hAK.isClosed.isOpen_compl.mem_nhds hv] with w hw
    exact hF0 w hw
  have hFS : ∀ S, ContDiff ℝ 1 fun v => (bas n).repr (F v) S := fun S => contDiff_iff_contDiffAt.2 fun v => by
    by_cases ht : v ∈ (A.e i).target
    · exact ((hβ.smooth i S).contDiffAt ((A.e i).open_target.mem_nhds ht)).of_le (by simp)
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ((hFA v fun h => ht (hAKt h)).mono fun w hw => ?_)
      simp [hw]
  have hFc : ∀ S, HasCompactSupport fun v => (bas n).repr (F v) S := fun S =>
    HasCompactSupport.intro hAK fun v hv => by simp [hF0 v hv]
  have hloc : ∀ v, A.loc (A.del β) i v = delAt F v := fun v => by
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dite_eq_left ht]
      show delAt (A.loc β i) ((A.e i) ((A.e i).symm v)) = _
      rw [(A.e i).right_inv ht]
    · rw [HolAtlas.loc, dite_eq_right ht]
      exact (delAt_eq_zero_of_eventually (hFA v fun h => ht (hAKt h))).symm
  obtain ⟨hI, h0⟩ := integral_dens_delAt hFS hFc
  have hIre : Integrable fun v => (dens (A.loc (A.del β) i v)).re := by
    simp only [hloc]
    exact Complex.reCLM.integrable_comp hI
  rw [integral_eq_of_vanish A hd i hKm hs hd0 hIre]
  simp only [hloc]
  have := Complex.reCLM.integral_comp_comm hI
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

end GlobalTheory.CxForm.LocStokes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalThetaSecondVariableDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section
namespace GlobalTheory.ThetaDiagUnfold

theorem dot_sumElim {R : Type} [CommSemiring R] {κ : Type} [Fintype κ] (a b c d : κ → R) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem integral_thetaSum_schr_diag : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (κ ⊕ κ), ∀ x : κ → AF F,
      ∫ y in 𝓕₁, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) ∂μ =
        (μ.real 𝓕₁ : ℂ) * ∑' η : κ → F, Φ (Sum.elim ((fun i => algebraMap F (AF F) (η i)) + x)
          ((fun i => algebraMap F (AF F) (η i)) + x)) := by
  intro F _ _ ψ hψ κ _
  intro μ hμ 𝓕₁ hF hfin Φ hΦ x
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : Countable F := GlobalTheory.ThetaParsevalInner.countable_numberField F
  haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin
  haveI := hμ
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hψ
  obtain ⟨emb, hemb⟩ : ∃ emb : (κ → F) → (κ → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (κ → F) → (κ → AF F) → ℂ, e = fun ξ y => ψ (emb ξ ⬝ᵥ y) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (κ ⊕ κ → F) → ℂ, a = fun ξ => Φ ((fun i => algebraMap F (AF F) (ξ i)) + Sum.elim x x) :=
    ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : (κ ⊕ κ → F) → (κ → F), d = fun ξ => ξ ∘ Sum.inl - ξ ∘ Sum.inr := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F (Sum.elim x x) hΦ)
    subst ha
    exact h0
  have he_norm : ∀ ξ y, ‖e ξ y‖ = 1 := fun ξ y => by rw [he]; exact hnorm _
  have he_cont : ∀ ξ, Continuous (e ξ) := fun ξ => by
    rw [he]; exact hcont.comp (continuous_const.dotProduct continuous_id)
  have hpt : ∀ y, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) =
      ∑' ξ, a ξ * e (d ξ) y := by
    intro y
    unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
    refine tsum_congr fun ξ => ?_
    have hsplit : (fun i => algebraMap F (AF F) (ξ i)) =
        Sum.elim (emb (ξ ∘ Sum.inl)) (emb (ξ ∘ Sum.inr)) := by
      funext s; cases s <;> simp [hemb]
    have hx0 : Sum.elim x x ⬝ᵥ Sum.elim y (-y) = 0 := by
      rw [dot_sumElim, dotProduct_neg, add_neg_cancel]
    have hdot : (fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ Sum.elim y (-y) = emb (d ξ) ⬝ᵥ y := by
      rw [hsplit, dot_sumElim, dotProduct_neg, hd]
      have : emb (ξ ∘ Sum.inl - ξ ∘ Sum.inr) = emb (ξ ∘ Sum.inl) - emb (ξ ∘ Sum.inr) := by
        rw [hemb]; funext i; simp [map_sub]
      rw [this, sub_dotProduct, sub_eq_add_neg]
    simp only
    rw [hx0, mul_zero, add_zero, hdot, ha, he]
    ring
  have hFint : ∀ ξ : κ ⊕ κ → F, Integrable (fun y => a ξ * e (d ξ) y) (μ.restrict 𝓕₁) := fun ξ =>
    (Integrable.of_bound (he_cont _).aestronglyMeasurable 1 (ae_of_all _ fun y => (he_norm _ _).le)).const_mul _
  have hnormint : ∀ ξ : κ ⊕ κ → F, ∫ y in 𝓕₁, ‖a ξ * e (d ξ) y‖ ∂μ = ‖a ξ‖ * μ.real 𝓕₁ := by
    intro ξ
    simp only [norm_mul, he_norm, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun ξ : κ ⊕ κ → F => ∫ y in 𝓕₁, ‖a ξ * e (d ξ) y‖ ∂μ := by
    simp_rw [hnormint]
    exact hsum.mul_right _
  have horth : ∀ ζ : κ → F, ∫ y in 𝓕₁, e ζ y ∂μ = if ζ = 0 then (μ.real 𝓕₁ : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ y, e 0 y = 1 := fun y => by simp [he, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push_neg at h; exact hζ (funext h)
      haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
        refine Function.Surjective.countable (f := fun ρ : κ → F => (⟨emb ρ, ?_⟩ : GlobalTheory.ThetaParseval.ratVec F κ)) ?_
        · exact (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ρ, by rw [hemb]⟩
        · rintro ⟨r, hr⟩
          obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
          exact ⟨ρ, by subst hemb; rfl⟩
      refine GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist μ (GlobalTheory.ThetaParseval.ratVec F κ) hF (h := e ζ) ?_
        (c := Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0)) (a := ψ s0) ?_ hs0
      · intro r hr y
        obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show emb ζ ⬝ᵥ (fun i => algebraMap F (AF F) (ρ i)) = algebraMap F (AF F) (ζ ⬝ᵥ ρ) by
          subst hemb; simp [dotProduct, map_sum, map_mul], htriv, one_mul]
      · intro y
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  have hFval : ∀ ξ : κ ⊕ κ → F, ∫ y in 𝓕₁, a ξ * e (d ξ) y ∂μ =
      if d ξ = 0 then (μ.real 𝓕₁ : ℂ) * a ξ else 0 := by
    intro ξ
    rw [integral_const_mul, horth]
    split_ifs <;> ring
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
  simp_rw [hFval]
  have hinj : Function.Injective (fun η : κ → F => (Sum.elim η η : κ ⊕ κ → F)) := fun η η' h => by
    funext i; exact congrFun h (Sum.inl i)
  rw [← hinj.tsum_eq, ← tsum_mul_left]
  · refine tsum_congr fun η => ?_
    have hd0 : d (Sum.elim η η) = 0 := by rw [hd]; funext i; simp
    rw [if_pos hd0, ha]
    dsimp only
    congr 2
    funext s; cases s <;> simp
  · intro ξ hξ
    have h0 : d ξ = 0 := by
      by_contra h; exact hξ (if_neg h)
    refine ⟨ξ ∘ Sum.inl, ?_⟩
    funext s
    cases s with
    | inl i => rfl
    | inr i =>
      have := congrFun h0 i
      rw [hd] at this
      simp only [Pi.sub_apply, Function.comp_apply, Pi.zero_apply, sub_eq_zero] at this
      simpa using this

end GlobalTheory.ThetaDiagUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralNeZeroOfCocompact
section
open scoped TensorProduct Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.PeriodicPositiveIntegral

theorem integral_ne_zero_of_cocompact {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (Γ : AddSubgroup G) [Countable Γ] {K : Set G}
    (hK : IsCompact K) (hKc : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K)
    (I : G → ℂ) (hI : Continuous I) (hper : ∀ γ ∈ Γ, ∀ u, I (γ + u) = I u)
    (hnn : ∀ u, 0 ≤ (I u).re) (h0 : 0 < (I 0).re) (ν : Measure G) [ν.IsAddHaarMeasure] (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 ν) (hfin : ν 𝓕 < ⊤) : ∫ u in 𝓕, I u ∂ν ≠ 0 := by
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hI.continuousOn
  have hint : Integrable I (ν.restrict 𝓕) := by
    refine Integrable.of_bound hI.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hper γ hγ w]
    exact hC _ h
  have hcre : Continuous fun u => (I u).re := Complex.continuous_re.comp hI
  have hO : IsOpen (Function.support fun u => (I u).re) := hcre.isOpen_support
  have hpos : ν (Function.support fun u => (I u).re) ≠ 0 := hO.measure_ne_zero ν ⟨0, h0.ne'⟩
  intro hz
  have hre : ∫ u in 𝓕, (I u).re ∂ν = 0 := by
    have := integral_re (𝕜 := ℂ) hint
    rw [hz] at this
    simpa using this
  have hlt : 0 < ∫ u in 𝓕, (I u).re ∂ν := by
    rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint.re,
      Measure.restrict_apply hO.measurableSet, pos_iff_ne_zero]
    intro hm
    refine hpos (h𝓕.measure_zero_of_invariant _ (fun g => ?_) hm)
    ext u
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    show (I (((-g : Γ) : G) + u)).re ≠ 0 ↔ (I u).re ≠ 0
    rw [hper _ (-g).2]
  exact hlt.ne' hre

theorem integral_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ)
    (I : WOF F E nS nT → ℂ), Continuous I → (∀ γ ∈ ratLF F E nS nT, ∀ u, I (γ + u) = I u) →
    (∀ u, 0 ≤ (I u).re) → 0 < (I 0).re →
    ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν → ∫ u in 𝓕, I u ∂ν ≠ 0 := by
  intro F E _ _ _ _ _ nS nT I hI hper hnn h0 ν 𝓕 hν h𝓕
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  exact integral_ne_zero_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc I hI hper hnn h0 ν 𝓕 h𝓕
    (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕)

end GlobalTheory.PeriodicPositiveIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTwistedComparisonAtFixedSection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SectionLattice

theorem mem_pull_chart_iff {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j : (L.pull f).ι) (y : Y) :
    y ∈ (L.pull f).U j ↔ f.base y ∈ L.U (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_chart_of_isLocalRing {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}}
    (L : LB X) (hL : L.IsLB) (e : Spec (CommRingCat.of R) ⟶ X) : ∃ m : L.ι, ⊤ ≤ e ⁻¹ᵁ L.U m := by
  have h : e.base (IsLocalRing.closedPoint R) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine ⟨m, ?_⟩
  have := (IsLocalRing.closedPoint_mem_iff (R := R) (e ⁻¹ᵁ L.U m)).1 hm
  exact this.ge

theorem integralAtSection_of_conj : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (σ : K' ≃+* K') (τ : W →+* W), (∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l) → ∀ (φ : G.left ⟶ G.left) (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → e₀ ≫ φ = spMap τ ≫ e₀ → ∀ (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))) (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ ρ = spMap (σ : K' →+* K') ≫ x → ∀ (M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), (∀ (n : N.ι) (i : ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).ι) (h : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ := by
  intro W K' _ _ _ _ _ _ G σ τ hσ φ e₀ he₀ hφ ρ x hx₁ hx₂ _ M N hM hN w w₁ H
  obtain ⟨m, hm⟩ := exists_chart_of_isLocalRing M hM e₀
  obtain ⟨n, hn⟩ := exists_chart_of_isLocalRing N hN x
  have hi : ⊤ ≤ e₀ ⁻¹ᵁ (M.pull φ).U (fun _ => m) := by
    intro y _
    change e₀.base y ∈ (M.pull φ).U (fun _ => m)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : φ.base (e₀.base y) = e₀.base ((spMap τ).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hφ]
    rw [h1]
    exact hm (TopologicalSpace.Opens.mem_top _)
  have key : ∀ (P : LB G.left) (i : P.ι), ⊤ ≤ e₀ ⁻¹ᵁ P.U i →
      ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) := by
    intro P i hP y hy
    refine ⟨hn hy, ?_⟩
    change x.base y ∈ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : (pullback.fst G.hom (spMap (algebraMap W K'))).base (x.base y) =
        e₀.base ((spMap (algebraMap W K')).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hx₁]
    rw [h1]
    exact hP (TopologicalSpace.Opens.mem_top _)
  have h₁ := key (M.pull φ) (fun _ => m) hi
  have h₂ := key M m hm
  have hw := H n (fun _ _ => m) h₁ h₂
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
      ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)) :=
    ((Units.isUnit _).map _).map _
  obtain ⟨a, ha⟩ := hσ _ hu.ne_zero
  exact ⟨e₀, he₀, x, hx₁, hx₂, fun _ => m, m, n, hi, hm, h₁, h₂, a, hw.trans ha⟩

end GlobalTheory.SectionLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := by
  first | exact @GlobalTheory.VacLn.vacLine_of_derEx | exact GlobalTheory.VacLn.vacLine_of_derEx | (intros; apply GlobalTheory.VacLn.vacLine_of_derEx <;> assumption)
end

