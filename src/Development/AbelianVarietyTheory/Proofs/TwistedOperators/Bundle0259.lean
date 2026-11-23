module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDataAtRealPlaceNegFirstLowEndLtCloud
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffRightConvolutionAlongOneParameterProduct
section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff ComplexConjugate

noncomputable section

namespace GlobalTheory.ConvSmooth

section Param

variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}

theorem hasFDerivAt_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W} (hΘ : ContDiff ℝ ∞ Θ) (t₀ : P) :
    HasFDerivAt (fun t => ∫ y, φ y • Θ (t, c y) ∂ν) (∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t₀ ∂ν) t₀ := by
  have hΘs : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
    ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
      (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
  have hΘ' := hΘs.continuous
  have hK : IsCompact (closedBall t₀ 1 ×ˢ S) := (isCompact_closedBall t₀ 1).prod hS
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ'.continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hΘ.continuous.continuousOn
  have hm : ∀ t, AEStronglyMeasurable (fun y => φ y • Θ (t, c y)) ν := fun t =>
    hφ.1.smul ((hΘ.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (F' := fun t y => φ y • fderiv ℝ (fun s => Θ (s, c y)) t) (bound := fun y => ‖φ y‖ * C) (ball_mem_nhds t₀ one_pos)
    (.of_forall hm) ?_ ?_ ?_ (hφ.norm.mul_const C) ?_
  · refine Integrable.mono' (hφ.norm.mul_const C₀) (hm t₀) ?_
    filter_upwards [hcS] with y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC₀ _ ⟨mem_closedBall_self zero_le_one, hy⟩) (norm_nonneg _)
  · exact hφ.1.smul ((hΘ'.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  · filter_upwards [hcS] with y hy t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (t, c y) ⟨ball_subset_closedBall ht, hy⟩) (norm_nonneg _)
  · refine .of_forall fun y t _ => ?_
    have hd : ContDiff ℝ ∞ fun s => Θ (s, c y) := hΘ.comp (contDiff_id.prodMk contDiff_const)
    exact ((hd.differentiable (by simp)) t).hasFDerivAt.const_smul (φ y)

theorem contDiff_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W} (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ fun t => ∫ y, φ y • Θ (t, c y) ∂ν := by
  rw [contDiff_infty]
  intro n
  induction n generalizing W with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t =>
      (hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t).continuousAt)
  | succ n ih =>
    have hΘ' : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
      ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
        (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨fun t => ∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t ∂ν,
      ih hΘ', fun t => hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t⟩

end Param

section Group

open GlobalTheory.AdelicU GlobalTheory.Orb NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {u : P → GAd σ J} {ν μ : Measure (GAd σ J)} {φ : GAd σ J → ℂ} {K : Set (GAd σ J)}


omit [NumberField E] [FiniteDimensional ℝ P] in
theorem infFin_mul_smoothFam (hu : IsSmoothRealFam u) {a : GInf σ J → ℂ} {b : GFin σ J → ℂ}
    {Φ : (∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℂ) → ℂ} (e : ∀ x, a x = Φ (infCoord σ J x))
    (z : GAd σ J) (t : P) :
    infFin σ J a b (z * u t) = Φ (fun w τ i j => ∑ k, infCoord σ J (projInf σ J z) w τ i k *
      archMat σ J τ (projArch σ J w (u t)) k j) * b (projFin σ J z) := by
  simp only [infFin, map_mul, hu.1, mul_one, e, infCoord_mul]

theorem integrable_conj_mul_of_mem (hφ : Integrable φ ν) {h : GAd σ J → ℂ}
    (hh : h ∈ CcAd σ J) (g : GAd σ J) (x : GAd σ J) :
    Integrable (fun y => conj (h (y⁻¹ * g * x)) * φ y) ν := by
  obtain ⟨h1, h2⟩ := continuous_of_mem_ccAd hh
  obtain ⟨M, hM⟩ := h1.bounded_above_of_compact_support h2
  refine Integrable.mono' (hφ.norm.const_mul M) ?_ (.of_forall fun y => ?_)
  · have hc : Continuous fun y : GAd σ J => conj (h (y⁻¹ * g * x)) :=
      Complex.continuous_conj.comp (h1.comp ((continuous_inv.mul continuous_const).mul continuous_const))
    exact hc.aestronglyMeasurable.mul hφ.1
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)

theorem contDiff_integral_of_compact (hu : IsSmoothRealFam u) (hKc : IsCompact K) (hK : ∀ᵐ y ∂ν, y ∈ K)
    (hφ : Integrable φ ν) {h : GAd σ J → ℂ} (hh : h ∈ CcAd σ J) (g : GAd σ J) :
    ContDiff ℝ ∞ fun t => ∫ y, conj (h (y⁻¹ * g * u t)) * φ y ∂ν := by
  induction hh using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨-, Φ, hΦ, e⟩, b, hb, rfl⟩ := hf
    have hcc : Continuous fun y : GAd σ J => infCoord σ J (projInf σ J (y⁻¹ * g)) :=
      (continuous_infCoord σ J).comp ((continuous_projInf σ J).comp (continuous_inv.mul continuous_const))
    obtain ⟨M, hM⟩ := hb.1.continuous.bounded_above_of_compact_support hb.2
    have hφ' : Integrable (fun y => conj (b (projFin σ J (y⁻¹ * g))) * φ y) ν := by
      refine Integrable.mono' (hφ.norm.const_mul M) ?_ (.of_forall fun y => ?_)
      · exact (Complex.continuous_conj.comp (hb.1.continuous.comp ((continuous_projFin σ J).comp
          (continuous_inv.mul continuous_const)))).aestronglyMeasurable.mul hφ.1
      · rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    have hΘ : ContDiff ℝ ∞ fun p : P × (∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℂ) =>
        conj (Φ (fun w τ i j => ∑ k, p.2 w τ i k * archMat σ J τ (projArch σ J w (u p.1)) k j)) :=
      Complex.conjCLE.contDiff.comp (hΦ.comp (contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i =>
        contDiff_pi.2 fun j => ContDiff.sum fun k _ =>
          (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_snd w) τ) i) k).mul
            ((hu.2 w τ k j).comp contDiff_fst)))
    have key := GlobalTheory.ConvSmooth.contDiff_integral_smul_param hcc.aestronglyMeasurable (hKc.image hcc)
      (hK.mono fun y hy => mem_image_of_mem _ hy) hφ' hΘ
    convert key using 1
    funext t
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [infFin_mul_smoothFam hu e, map_mul]
    ring
  | zero => simp only [Pi.zero_apply, map_zero, zero_mul, integral_zero]; exact contDiff_const
  | add f f' hf hf' h h' =>
    have e : (fun t => ∫ y, conj ((f + f') (y⁻¹ * g * u t)) * φ y ∂ν) =
        fun t => (∫ y, conj (f (y⁻¹ * g * u t)) * φ y ∂ν) + ∫ y, conj (f' (y⁻¹ * g * u t)) * φ y ∂ν :=
      funext fun t => by
        simp only [Pi.add_apply, map_add (f := _), add_mul]
        exact integral_add (integrable_conj_mul_of_mem hφ hf g _) (integrable_conj_mul_of_mem hφ hf' g _)
    rw [e]
    exact h.add h'
  | smul a f _ h =>
    have e : (fun t => ∫ y, conj ((a • f) (y⁻¹ * g * u t)) * φ y ∂ν) =
        fun t => conj a * ∫ y, conj (f (y⁻¹ * g * u t)) * φ y ∂ν :=
      funext fun t => by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun y => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        ring
    rw [e]
    exact contDiff_const.mul h

theorem contDiff_integral_conj_mul (hu : IsSmoothRealFam u) (hcu : Continuous u) (hφ : LocallyIntegrable φ μ)
    {h : GAd σ J → ℂ} (hh : h ∈ CcAd σ J) (g : GAd σ J) :
    ContDiff ℝ ∞ fun t => ∫ y, conj (h (y⁻¹ * g * u t)) * φ y ∂μ := by
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  obtain ⟨-, hs⟩ := continuous_of_mem_ccAd hh
  set K := (fun p : P × GAd σ J => g * u p.1 * p.2⁻¹) '' (closedBall t₀ 1 ×ˢ tsupport h) with hKdef
  have hKc : IsCompact K := ((isCompact_closedBall t₀ 1).prod hs.isCompact).image (by fun_prop)
  have key := contDiff_integral_of_compact (ν := μ.restrict K) hu hKc (ae_restrict_mem hKc.measurableSet)
    (hφ.integrableOn_isCompact hKc) hh g
  refine key.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds t₀ one_pos] with t ht
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
  have : y⁻¹ * g * u t ∉ tsupport h := fun hm =>
    hy ⟨(t, y⁻¹ * g * u t), ⟨ball_subset_closedBall ht, hm⟩, by simp [mul_assoc]⟩
  simp [image_eq_zero_of_notMem_tsupport this]

end Group

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta NumberField
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem continuous_ofFn_prod {G Q : Type} [Monoid G] [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace Q]
    {k : ℕ} {v : Fin k → Q → G} (hv : ∀ i, Continuous (v i)) :
    Continuous fun t => (List.ofFn fun i => v i t).prod := by
  induction k with
  | zero => simpa using continuous_const
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hv 0).mul (ih fun i => hv i.succ)

theorem contDiff_convR_lift_oneP : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g : GA D V, ContDiff ℝ ∞ fun t : Fin k → ℝ => GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  intro D V μ _ _ θ hθ f hf F k τs Xs hX g
  have hu := GlobalTheory.Orb.isSmoothRealFam_prod fun i =>
    (GlobalTheory.Orb.isSmoothRealFam_oneP hθ (hX i)).1.comp (contDiff_apply ℝ (fun _ => ℝ) i)
  have hcu := continuous_ofFn_prod (v := fun i (t : Fin k → ℝ) => oneP θ V (τs i) (Xs i) (t i)) fun i =>
    (GlobalTheory.Orb.isSmoothRealFam_oneP hθ (hX i)).2.1.comp (continuous_apply i)
  have hφ : LocallyIntegrable (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) μ :=
    locallyIntegrable_iff.2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
  have key := contDiff_integral_conj_mul hu hcu hφ (GlobalTheory.Orb.starFn_mem_ccAd hf) g
  convert key using 1
  funext t
  rw [GlobalTheory.AutomorphicL2Unitary.convR_eq]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp [GlobalTheory.AutomorphicL2Unitary.starFn, mul_assoc]

end Record

end GlobalTheory.ConvSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittTowerRestrictionWeilCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerRestrictChar

theorem continuous_char : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → Continuous c := by
  intro D V V' W r C B hs ψ χS χT χS' χT' ω ω' hω hω' μ 𝓨 hμ c hc
  have hg4 : SecondCountableTopology (GA D W) := by
    obtain ⟨h1, h2, h3⟩ := Formalism.IndefR.Eqv.G5.af_facts D.host.F
    exact (Formalism.IndefR.Eqv.G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig W.gram).2.2.2.1
  have hres := _root_.GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hω.std μ 𝓨 hμ
  obtain ⟨f₀, hf₀, hne⟩ := hres.2
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  set g := GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f₀ with hgdef
  have hg : IsThetaFunO ψ V' W g := (hres.1 f₀ hf₀).2.1
  have hcont1 : Continuous fun h : GA D W => (((1 : GA D V), h) : GA D V × GA D W) :=
    continuous_const.prodMk continuous_id
  have hcont1' : Continuous fun h : GA D W => (((1 : GA D V'), h) : GA D V' × GA D W) :=
    continuous_const.prodMk continuous_id
  suffices hC : Continuous fun h => (c h : ℂ) from continuous_induced_rng.2 hC
  rw [continuous_iff_continuousAt]
  intro h₀

  have hne₀ : ω' (1, h₀) g ≠ 0 := by
    intro h0
    apply hne
    have hinv : ω' (1, h₀⁻¹) * ω' (1, h₀) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, inv_mul_cancel, Prod.mk_one_one, map_one]
    have := congrArg (fun T : Module.End ℂ (WO V' W → ℂ) => T g) hinv
    simp only [Module.End.mul_apply, h0, map_zero, Module.End.one_apply] at this
    exact this.symm
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne₀

  set Dn : GA D W → ℂ := fun h => ω' (1, h) g x with hDn
  have hDc : Continuous Dn := (hω'.om_cont g hg x).comp hcont1'
  have hD0 : Dn h₀ ≠ 0 := hx

  set Nu : GA D W → ℂ := fun h => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f₀) x with hNu
  have hNc : ContinuousAt Nu h₀ := by
    haveI : SecondCountableTopology (GA D W) := hg4
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds h₀
    obtain ⟨c₀, hc₀⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ V W χS χT ω hω f₀ hf₀
      ({(1 : GA D V)} ×ˢ K) (isCompact_singleton.prod hK)
    refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => c₀) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun h =>
        ((hres.1 _ (hω.om_pres _ _ hf₀)).1 x).aestronglyMeasurable
    · filter_upwards [hKn] with h hh
      exact Filter.Eventually.of_forall fun y =>
        hc₀ ((1 : GA D V), h) ⟨rfl, hh⟩ _
    · exact integrable_const c₀
    · exact Filter.Eventually.of_forall fun y =>
        ((hω.om_cont f₀ hf₀ _).comp hcont1).continuousAt

  have hq : ∀ h, Nu h = (c h : ℂ) * Dn h := fun h => by
    have := congrFun (hc h f₀ hf₀) x
    simpa [hNu, hDn, hgdef] using this
  have hev : ∀ᶠ h in nhds h₀, Dn h ≠ 0 := hDc.continuousAt.eventually_ne hD0
  have hdiv : ContinuousAt (fun h => Nu h / Dn h) h₀ := hNc.div hDc.continuousAt hD0
  refine hdiv.congr ?_
  filter_upwards [hev] with h hh
  rw [hq h, mul_div_assoc, div_self hh, mul_one]

end GlobalTheory.TowerRestrictChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsAddBlockArrow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.GridParD

open GlobalTheory.SignedHC Finset

theorem pairPar_X : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i < D.R.m → j ≤ D.R.m →
    PairPar (GlobalTheory.SignedHC.flip (parV D (i + 1) j τ)) (parV D i j τ) (att (cen D τ (D.R.m - i)) (rkV D (i + 1) j))
      (att (cen D τ (D.R.m - i)) (rkV D i j)) := by
  intro D hS i j τ hi hj
  have hnear := grid_nearMid D τ
  have hB1 := gridDataAtRealPlace_neg_firstLowEnd_lt_cloud D τ
  have hbe := grid_hbe D τ
  have heb := grid_heb D τ
  have hbb := grid_hbb D τ hS
  have hga := grid_hga D τ
  have hN0 : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 := by positivity
  have hs2 : ((grid D τ).s : ℚ) + 2 ≤ (grid D τ).ga := by linarith
  have hsOdd := odd_sLen D
  have hle := entries_parD_le (grid D τ) hi hj hnear hB1 hbe hs2
  have hgap : ∀ i', GapOver ((grid D τ).parD i' j) (2 * (bigN D : ℚ) ^ 3) := fun i' =>
    gapOver_parD (grid D τ) i' j hN0 hnear hB1 heb hbb hga
  have hlt : ∀ x ∈ (grid D τ).parD i j, x.1 + ((sLen D : ℚ) + 1) / 2 ≤ (cen D τ (D.R.m - i) : ℚ) := fun x hx =>
    hle x.1 (fst_mem_entries hx)
  have hs0 : (0 : ℚ) ≤ sLen D := by positivity
  set c : ℚ := (cen D τ (D.R.m - i) : ℚ) with hc
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδdef
  set δ' : ℚ := if Odd (i + 1 + j) then -(1 / 2) else 0 with hδ'def
  have e1 : Odd (i + 1 + j) ↔ ¬ Odd (i + j) := by
    rw [show i + 1 + j = (i + j) + 1 by ring]; exact Nat.odd_add_one
  have hδ : att c (rkV D (i + 1) j) = c + δ := by
    by_cases h : Odd (i + j)
    · simp [att, odd_rkV_iff, e1, h, hδdef, sub_eq_add_neg]
    · simp [att, odd_rkV_iff, e1, h, hδdef]
  have hδ' : att c (rkV D i j) = c + δ' := by
    by_cases h : Odd (i + j)
    · simp [att, odd_rkV_iff, e1, h, hδ'def]
    · simp [att, odd_rkV_iff, e1, h, hδ'def, sub_eq_add_neg]
  have key : partner (sLen D) false (c + δ) (c + δ') (shift δ ((grid D τ).parD i j)) =
      flip (shift δ' ((grid D τ).parD (i + 1) j)) := by
    rw [parD_succ _ hi]
    ext y
    simp only [partner, Finset.mem_union, Finset.mem_image, mem_flip, mem_shift, mem_plus]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩)
      · have := hlt _ hx
        left
        rw [if_pos (by simp only at this; linarith)]
        simp only [Bool.not_not]
        convert hx using 2
        ring
      · right
        refine ⟨?_, rfl⟩
        show z - δ' ∈ TPar.block c (sLen D)
        exact sub_mem_block.2 (by simpa [add_comm] using hz)
    · rintro (h | ⟨h1, h2⟩)
      · left
        refine ⟨(y.1 - δ' + δ, !y.2), by simpa using h, ?_⟩
        have := hlt _ h
        rw [if_pos (by simp only at this ⊢; linarith)]
        ext
        · simp only; ring
        · simp
      · right
        refine ⟨y.1, ?_, ?_⟩
        · have : y.1 - δ' ∈ TPar.block c (sLen D) := h1
          simpa [add_comm] using sub_mem_block.1 this
        · ext
          · rfl
          · simpa using h2
  refine ⟨sLen D, flip (shift δ' ((grid D τ).parD (i + 1) j)), shift δ ((grid D τ).parD i j), ?_, rfl, Or.inr ?_⟩
  · exact flip_dualPar _
  · rw [hδ, hδ', ← key]
    have hX : ((grid D τ).parD i j).Nonempty :=
      ⟨((grid D τ).v 2, true), GridData.mem_parD.2 (Or.inl ⟨GridData.mem_cloud.2 ⟨2, le_rfl, (grid D τ).two_le_k, rfl⟩, rfl⟩)⟩
    have hinj : Function.Injective fun x : ℚ × Bool => (x.1 + δ, x.2) := by
      intro a b e
      simp only [Prod.mk.injEq, add_left_inj] at e
      exact Prod.ext e.1 e.2
    have hcard : (shift δ ((grid D τ).parD i j)).card + sLen D ≤ bigN D := by
      rw [shift, card_image_of_injective _ hinj]
      have h1 := card_parD_le (grid D τ) (i := i) (j := j) hi.le
      have h2 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
      have h3 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
      have hr : D.R.r + 1 = D.R.k + D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
      change _ ≤ D.R.r + j * D.R.t + i * sLen D at h1
      unfold bigN
      nlinarith
    have hN : 1800 < bigN D := by
      have := hS.1
      have hr : D.R.r + 1 = D.R.k + D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
      unfold bigN
      nlinarith
    refine _root_.GlobalTheory.PairLift.FromSigned.thetaPar_partner (sLen D) false (c + δ) (c + δ') _ (bigN D) (by unfold sLen; omega) (hX.image _)
      (GapOver.isRegular hN0 (gapOver_shift δ (hgap i))) ?_ ?_ hcard hN (gapOver_shift δ (hgap i))
      (by rw [key]; exact gapOver_flip (gapOver_shift δ' (hgap (i + 1))))
    · intro x hx
      obtain ⟨sg, hsg⟩ := mem_entries.1 hx
      have h := mem_shift.1 hsg
      obtain ⟨z, hz⟩ := int_of_mem_entries_parD (grid D τ) D.R.t_odd hsOdd (fst_mem_entries h)
      obtain ⟨w, hw⟩ := hsOdd
      simp only at hz
      refine ⟨z - cen D τ (D.R.m - i) - (w + 1), ?_⟩
      rw [hw]
      push_cast
      linarith
    · intro x hx
      obtain ⟨sg, hsg⟩ := mem_entries.1 hx
      have h := hlt _ (mem_shift.1 hsg)
      simp only at h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith

end GlobalTheory.GridParD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionPreservesCuspidal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspConv

theorem isCuspFun_convR_lift : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ,
    F ∈ GlobalTheory.Cusp.L2cusp V μ → IsCuspFun V (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) := by
  intro D V μ _ _ f hf F hF
  obtain ⟨hc, hs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have h := (GlobalTheory.CuspAE.mem_L2cusp_iff_isCuspAE D V μ F).1 hF
  have hl := (GlobalTheory.AutomorphicL2Unitary.leftInv_lift (Γ := GQ V) F).convR (μ := μ) f
  refine GlobalTheory.Cusp.isCuspFun_of_forall_flag hl fun 𝔉 h𝔉 => funext fun x => ?_
  refine (GlobalTheory.CuspAE.constTermOn_convR (GlobalTheory.Cusp.cocompact_flag D V 𝔉) (GlobalTheory.AutomorphicL2Unitary.leftInv_lift _)
    ((Lp.stronglyMeasurable F).comp_measurable GlobalTheory.AutomorphicL2Unitary.measurable_mk) (GlobalTheory.CuspAE.locallyIntegrable_lift F)
    hc hs x).trans ?_
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [(measurePreserving_mul_left μ x).quasiMeasurePreserving.ae (h 𝔉 h𝔉)] with y hy
  exact mul_eq_zero_of_right _ hy

end GlobalTheory.CuspConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionRightInvariantOpen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConvLevel

theorem ccGA_leftInv {D : D7} {V : HSp D} {f : GA D V → ℂ} (hf : f ∈ GlobalTheory.Orb.CcGA V) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ y, f (k * y) = f y := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, -, b, hb, rfl⟩ := hf
    obtain ⟨K, hK, hb'⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨K.comap (GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram),
      hK.preimage (GlobalTheory.AdelicU.continuous_projFin _ _), fun k hk hk' y => ?_⟩
    have h1 : GlobalTheory.AdelicU.projInf D.sp.cm.sig V.gram k = 1 := GlobalTheory.AdelicU.mem_finPts.1 hk'
    simp only [GlobalTheory.Orb.infFin, map_mul, h1, one_mul]
    rw [(hb' _ hk _).1]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add f f' _ _ h h' =>
    obtain ⟨U, hU, e⟩ := h
    obtain ⟨U', hU', e'⟩ := h'
    exact ⟨U ⊓ U', hU.inter hU', fun k hk hk' y => by
      simp only [Pi.add_apply, e k hk.1 hk' y, e' k hk.2 hk' y]⟩
  | smul c f _ h =>
    obtain ⟨U, hU, e⟩ := h
    exact ⟨U, hU, fun k hk hk' y => by simp only [Pi.smul_apply, e k hk hk' y]⟩

theorem convR_level : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, ∀ k ∈ U, k ∈ GfC V → ∀ g, GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * k) = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g := by
  intro D V μ _ _ f hf
  obtain ⟨U, hU, e⟩ := ccGA_leftInv hf
  refine ⟨U, hU, fun F k hk hk' g => ?_⟩
  rw [GlobalTheory.AutomorphicL2Unitary.convR_eq, GlobalTheory.AutomorphicL2Unitary.convR_eq]
  congr 1
  funext y
  rw [mul_inv_rev, mul_assoc, e _ (U.inv_mem hk) ((GfC V).inv_mem hk')]

end GlobalTheory.ConvLevel
end

