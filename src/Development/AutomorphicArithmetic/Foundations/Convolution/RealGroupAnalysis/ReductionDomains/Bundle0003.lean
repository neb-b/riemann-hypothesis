module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtOne

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BorHaar
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.borHaar :
    ∀ (F : Type) [Field F] [NumberField F], ∃ μS : Measure (M.Bor F), μS.IsHaarMeasure ∧ ∀ (f : G1 F → ℝ≥0∞), Measurable f → ∫⁻ s, f s ∂μS = ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
  intro F _ _
  obtain ⟨hcl, e, he⟩ := M.borHomeo F
  have hcont : Continuous fun a : IdeleGroup F => (ab a)⁻¹ ^ 2 :=
    (M.continuous_ab.inv₀ fun a => (M.ab_pos a).ne').pow 2
  have hwm : Measurable (M.wt : IdeleGroup F → ℝ≥0∞) := M.measurable_wt
  have hw0 : ∀ a : IdeleGroup F, M.wt a ≠ 0 := fun a => by
    have : 0 < (ab a)⁻¹ ^ 2 := pow_pos (inv_pos.2 (M.ab_pos a)) 2
    exact (ENNReal.ofReal_pos.2 this).ne'
  set ν : Measure (IdeleGroup F) := (ideleMeasure F).withDensity M.wt with hν
  haveI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hcont
  haveI : ν.IsOpenPosMeasure :=
    (withDensity_absolutelyContinuous' hwm.aemeasurable (ae_of_all _ hw0)).isOpenPosMeasure
  haveI : SFinite ν := by rw [hν]; infer_instance
  set ρ : Measure (IdeleGroup F × A F) := ν.prod (adeleMeasure F) with hρ
  have hint : ∀ f : G1 F → ℝ≥0∞, Measurable f → ∫⁻ s, f s ∂(ρ.map e) =
      ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
    intro f hf
    have hc : Continuous fun p : IdeleGroup F × A F => nU p.2 * mD p.1 :=
      (M.continuous_nU.comp continuous_snd).mul (M.continuous_mD.comp continuous_fst)
    have hfm : Measurable fun p : IdeleGroup F × A F => f (nU p.2 * mD p.1) := hf.comp hc.measurable
    rw [show ∫⁻ s, f s ∂(ρ.map e) = ∫⁻ p, f (e p) ∂ρ from
      lintegral_map (f := fun s : M.Bor F => f s) (hf.comp measurable_subtype_coe) e.continuous.measurable]
    simp only [he]
    rw [hρ, lintegral_prod _ hfm.aemeasurable, hν,
      lintegral_withDensity_eq_lintegral_mul _ hwm hfm.lintegral_prod_right']
    refine lintegral_congr fun a => ?_
    have hne : M.wt a ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [Pi.mul_apply, lintegral_mul_const' _ _ hne, mul_comm]
  refine ⟨ρ.map e, ?_, hint⟩
  haveI : IsFiniteMeasureOnCompacts (ρ.map e) := ⟨fun K hK => by
    rw [e.measurableEmbedding.map_apply]
    exact ((e.isCompact_preimage).2 hK).measure_lt_top⟩
  haveI : (ρ.map e).IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  haveI : (ρ.map e).IsMulLeftInvariant := ⟨fun g => by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs]
    have hS : MeasurableSet (Subtype.val '' s : Set (G1 F)) := hcl.measurableSet.subtype_image hs
    set f : G1 F → ℝ≥0∞ := (Subtype.val '' s : Set (G1 F)).indicator 1 with hfdef
    have hf : Measurable f := measurable_one.indicator hS
    have hval : ∀ x : M.Bor F, f x = s.indicator 1 x := fun x => by
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, hfdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hx)]; rfl
      · rw [Set.indicator_of_notMem hx, hfdef, Set.indicator_of_notMem]
        rintro ⟨y, hy, hyx⟩
        exact hx (Subtype.ext hyx ▸ hy)
    have h1 : (ρ.map e) s = ∫⁻ x, f x ∂(ρ.map e) := by
      simp only [hval]; rw [lintegral_indicator_one hs]
    have h2 : (ρ.map e) ((fun x => g * x) ⁻¹' s) = ∫⁻ x, (fun y => f (g.1 * y)) x ∂(ρ.map e) := by
      have hs' : MeasurableSet ((fun x => g * x) ⁻¹' s) := measurable_const_mul g hs
      rw [← lintegral_indicator_one hs']
      refine lintegral_congr fun x => ?_
      have := hval (g * x)
      simpa [Set.indicator] using this.symm
    obtain ⟨p, rfl⟩ := e.surjective g
    rw [h1, h2, hint (fun y => f ((e p : G1 F) * y)) (hf.comp (measurable_const_mul _)), hint f hf]
    simp only [he]
    exact M.borLeft F f hf p.2 p.1⟩
  exact {}
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CosetSum
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.cosetSum :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (σ) (β u : G1 F → ℝ≥0∞), M.RowSec (F := F) σ → M.NWt β → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = ∫⁻ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ := by
  intro F _ _ M₀ σ β u hσ hβ hu hinv
  have hc := (UpperTheory.ConvolutionTheory.R2.M.rowCosets F).2 σ hσ
  haveI := M₀.haar
  let e : ({r : Fin 2 → F // r ≠ 0} × F) → Gam F := fun p =>
    ⟨nU (rt p.2) * ratS F (σ p.1), (Gam F).mul_mem (M.nU_rt_mem _) ⟨_, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro p q h
      obtain ⟨p0, _, hp⟩ := hc (e p)
      exact (hp p rfl).trans (hp q (congrArg Subtype.val h)).symm
    · intro γ
      obtain ⟨p, hp, _⟩ := hc γ
      exact ⟨p, Subtype.ext hp.symm⟩
  have key : ∀ g : G1 F, ∑' γ : Gam F, u (γ • g) * β (γ • g) = ∑' r, u (ratS F (σ r) * g) := by
    intro g
    rw [← (Equiv.ofBijective e he).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun r => ?_
    have h1 : ∀ ξ : F, u ((Equiv.ofBijective e he (r, ξ)) • g) * β ((Equiv.ofBijective e he (r, ξ)) • g)
        = u (ratS F (σ r) * g) * β (nU (rt ξ) * (ratS F (σ r) * g)) := by
      intro ξ
      have h2 : (Equiv.ofBijective e he (r, ξ)) • g = nU (rt ξ) * (ratS F (σ r) * g) := by
        change (nU (rt ξ) * ratS F (σ r)) * g = _
        rw [mul_assoc]
      rw [h2, hinv]
    simp_rw [h1]
    rw [ENNReal.tsum_mul_left, hβ.2, mul_one]
  have hmeas : ∀ γ : Gam F, Measurable fun g : G1 F => u (γ • g) * β (γ • g) := fun γ =>
    (hu.mul hβ.1).comp (measurable_const_smul γ)
  rw [M₀.fund.lintegral_eq_tsum'', ← lintegral_tsum fun γ => (hmeas γ).aemeasurable]
  exact lintegral_congr key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.DiagInvVal
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem diag_val (F : Type) [Field F] [NumberField F] (t : Fˣ) :
    ((IdeleGroup.diagonal F t : (A F)ˣ) : A F) = rt (t : F) := rfl

private theorem diag_inv_val (F : Type) [Field F] [NumberField F] (t : Fˣ) :
    (((IdeleGroup.diagonal F t : (A F)ˣ)⁻¹ : (A F)ˣ) : A F) = rt ((t : F)⁻¹) := by
  rw [← map_inv, ← Units.val_inv_eq_inv_val]
  rfl

private def cR {F : Type} [Field F] (t : Fˣ) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![g 0 0, g 0 1 * (t : F)⁻¹; (t : F) * g 1 0, g 1 1], by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    have ht : (t : F) ≠ 0 := t.ne_zero
    have : g 0 1 * (t : F)⁻¹ * ((t : F) * g 1 0) = g 0 1 * g 1 0 := by field_simp
    rw [this]
    exact h⟩

private theorem cD_ratS {F : Type} [Field F] [NumberField F] (t : Fˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    cD (IdeleGroup.diagonal F t) (ratS F g) = ratS F (cR t g) := by
  refine Subtype.ext ?_
  rw [M.val_ratS]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cD, cR, M.val_ratS, diag_inv_val, diag_val, rt, map_mul]

private theorem cD_mem {F : Type} [Field F] [NumberField F] (t : Fˣ) {x : G1 F} (hx : x ∈ Gam F) :
    cD (IdeleGroup.diagonal F t) x ∈ Gam F := by
  obtain ⟨g, rfl⟩ := hx
  exact ⟨cR t g, (cD_ratS t g).symm⟩

theorem UpperTheory.ConvolutionTheory.R2.M.dConj :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (u : G1 F → ℂ), (∀ γ g, u (ratS F γ * g) = u g) → ∀ t : Fˣ, (IntegrableOn (fun g => u (cD (IdeleGroup.diagonal F t) g)) M₀.D M₀.μ ↔ IntegrableOn u M₀.D M₀.μ) ∧ ∫ g in M₀.D, u (cD (IdeleGroup.diagonal F t) g) ∂M₀.μ = ∫ g in M₀.D, u g ∂M₀.μ := by
  intro F _ _ M₀ u hu t
  haveI := M₀.haar
  set T : (A F)ˣ := IdeleGroup.diagonal F t with hT
  have hTi : T⁻¹ = IdeleGroup.diagonal F t⁻¹ := by rw [hT, map_inv]
  let e : G1 F ≃ₜ G1 F :=
    { toFun := cD T
      invFun := cD T⁻¹
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      continuous_toFun := M.continuous_cD T
      continuous_invFun := M.continuous_cD T⁻¹ }
  let eG : Gam F ≃ Gam F :=
    { toFun := fun γ => ⟨cD T⁻¹ γ.1, by rw [hTi]; exact cD_mem t⁻¹ γ.2⟩
      invFun := fun γ => ⟨cD T γ.1, cD_mem t γ.2⟩
      left_inv := fun γ => Subtype.ext (by
        show cD T (cD T⁻¹ γ.1) = γ.1
        rw [M.cD_cD, mul_inv_cancel, M.cD_one])
      right_inv := fun γ => Subtype.ext (by
        show cD T⁻¹ (cD T γ.1) = γ.1
        rw [M.cD_cD, inv_mul_cancel, M.cD_one]) }
  have hmp : MeasurePreserving (cD T) M₀.μ M₀.μ := M.cdMeas F M₀ T
  have hmpi : MeasurePreserving (cD T⁻¹) M₀.μ M₀.μ := M.cdMeas F M₀ T⁻¹
  have hemb : MeasurableEmbedding (cD T : G1 F → G1 F) := e.measurableEmbedding
  have hD' : IsFundamentalDomain (Gam F) (cD T '' M₀.D) M₀.μ :=
    M₀.fund.image_of_equiv e.toEquiv hmpi.quasiMeasurePreserving eG (fun γ x => by
      show cD T (cD T⁻¹ γ.1 * x) = γ.1 * cD T x
      rw [M.cD_mul, M.cD_cD, mul_inv_cancel, M.cD_one])
  have hpre : cD T ⁻¹' (cD T '' M₀.D) = M₀.D := Set.preimage_image_eq _ e.injective
  have hinv : ∀ (γ : Gam F) (x : G1 F), u (γ • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    exact hu γ x
  constructor
  · have h1 := hmp.integrableOn_comp_preimage hemb (f := u) (s := cD T '' M₀.D)
    rw [hpre] at h1
    exact h1.trans (hD'.integrableOn_iff M₀.fund hinv)
  · have h1 := hmp.setIntegral_preimage_emb hemb u (cD T '' M₀.D)
    rw [hpre] at h1
    exact h1.trans (hD'.setIntegral_eq M₀.fund hinv)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.kkCpt :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], KK F = (M.Ks F : Set (G1 F)) ∧ IsCompact (KK F) := by
  intro F _ _ _
  have h1 : KK F = (M.Ks F : Set (G1 F)) := by
    ext g
    change (InfOrth g ∧ ∀ v, IntAt v g) ↔ gl g ∈ Reduction.maxCompact (K := F) (n := 2)
    rw [Reduction.mem_maxCompact, UpperTheory.ConvolutionTheory.R2.M.kkInf F g]
    exact and_congr_right fun _ => forall_congr' fun v => UpperTheory.ConvolutionTheory.R2.M.kkFin F g v
  refine ⟨h1, ?_⟩
  have hC := Reduction.isCompact_maxCompact (K := F) (n := 2)
  have hD := hC.image (Units.continuous_val)
  have h2 := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hD
  have h3 : KK F = (fun g : G1 F => g.1) ⁻¹' (Units.val '' (Reduction.maxCompact (K := F) (n := 2) : Set (GL (Fin 2) (A F)))) := by
    rw [h1]
    ext g
    constructor
    · intro hg
      exact ⟨gl g, hg, rfl⟩
    · rintro ⟨u, hu, huv⟩
      have : u = gl g := Units.ext huv
      subst this
      exact hu
  rw [h3]
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.LintegralUnipotentQuotientCompDiagonalConj
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.lintegral_unipotent_quotient_comp_diagonal_conj :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (u : G1 F → ℝ≥0∞), Measurable u → (∀ b g, u (nU b * g) = u g) → ∀ t, (M.J0 M₀ fun g => u (cD t g)) = ENNReal.ofReal (ab t)⁻¹ * M.J0 M₀ u := by
  intro F _ _ M₀ u hu hN t
  obtain ⟨β, hβ⟩ := M.wtEx F
  have h1 := M.wtOne F β hβ
  have hcm : ∀ s : (A F)ˣ, Measurable (cD s : G1 F → G1 F) := fun s => (M.continuous_cD s).measurable
  have hβ' : Measurable fun g => β (cD t⁻¹ g) := hβ.1.comp (hcm _)
  have hu' : Measurable fun g => u (cD t g) := hu.comp (hcm _)
  have hN' : ∀ b g, u (cD t (nU b * g)) = u (cD t g) := by
    intro b g
    rw [M.cD_mul, M.cD_nU, hN]
  have hc : ∀ g, ∫⁻ b, β (cD t⁻¹ (nU b * g)) ∂(adeleMeasure F) = ENNReal.ofReal (ab t)⁻¹ := by
    intro g
    have hf : Measurable fun b : A F => β (nU b * cD t⁻¹ g) :=
      hβ.1.comp ((M.continuous_nU.mul continuous_const).measurable)
    have hs : Measurable fun x : A F => (t : IdeleGroup F) • x := by
      have : Continuous fun x : A F => (t : IdeleGroup F) • x := by
        simp only [Units.smul_def, smul_eq_mul]
        exact continuous_const.mul continuous_id
      exact this.measurable
    have e := lintegral_map (μ := adeleMeasure F) hf hs
    rw [map_smul_adeleMeasure, lintegral_smul_measure, h1] at e
    have e2 : ∀ b : A F, β (cD t⁻¹ (nU b * g)) = β (nU ((t : IdeleGroup F) • b) * cD t⁻¹ g) := by
      intro b
      rw [M.cD_mul, M.cD_nU, inv_inv, Units.smul_def, smul_eq_mul, mul_comm b]
    simp_rw [e2]
    rw [← e, smul_eq_mul, mul_one]
    rfl
  have a1 := M.wtA F M₀ β (fun g => u (cD t g)) 1 hβ.1 h1 hu' hN'
  have a2 := M.wtA F M₀ (fun g => β (cD t⁻¹ g)) u _ hβ' hc hu hN
  have a3 := (M.cdMeas F M₀ t).lintegral_comp
    (f := fun h => u h * β (cD t⁻¹ h)) (hu.mul hβ')
  have e3 : ∀ g, β (cD t⁻¹ (cD t g)) = β g := by
    intro g
    rw [M.cD_cD, inv_mul_cancel, M.cD_one]
  simp only [e3] at a3
  rw [one_mul] at a1
  rw [← a1, a3, a2]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.LintegralUnipotentQuotientRightInvariant
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.lintegral_unipotent_quotient_right_invariant :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (u : G1 F → ℝ≥0∞), Measurable u → (∀ b g, u (nU b * g) = u g) → ∀ g₀, (M.J0 M₀ fun g => u (g * g₀)) = M.J0 M₀ u := by
  intro F _ _ M₀ u hu hinv g₀
  obtain ⟨β, hβ⟩ := UpperTheory.ConvolutionTheory.R2.M.wtEx F
  haveI := M₀.right
  have hone := UpperTheory.ConvolutionTheory.R2.M.wtOne F β hβ
  have hm : ∀ h : G1 F, Measurable fun g : G1 F => g * h := fun h => measurable_mul_const h
  have h1 := UpperTheory.ConvolutionTheory.R2.M.wtA F M₀ β (fun g => u (g * g₀)) 1 hβ.1 hone (hu.comp (hm g₀))
    (fun b g => by rw [mul_assoc, hinv])
  have h2 := UpperTheory.ConvolutionTheory.R2.M.wtA F M₀ (fun g => β (g * g₀⁻¹)) u 1 (hβ.1.comp (hm g₀⁻¹))
    (fun g => by simpa only [mul_assoc] using hone (g * g₀⁻¹)) hu hinv
  have h3 := lintegral_mul_right_eq_self (μ := M₀.μ) (fun g => u g * β (g * g₀⁻¹)) g₀
  simp only [mul_inv_cancel_right] at h3
  rw [one_mul] at h1 h2
  rw [← h1, ← h2, h3]
end

