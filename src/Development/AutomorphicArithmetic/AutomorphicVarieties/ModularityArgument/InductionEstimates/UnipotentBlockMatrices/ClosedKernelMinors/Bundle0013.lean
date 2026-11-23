module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistUnitary
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.IsHilbertSchmidtOfAeEqDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LintegralInvUniqueHaar
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem lintegral_inv_unique_haar {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (U : Subgroup G) (ν ν' : Measure G) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : ∀ᵐ k ∂ν, k ∈ U) (h' : ∀ᵐ k ∂ν', k ∈ U) (hi : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν)
    (hi' : ∀ k ∈ U, MeasurePreserving (k * ·) ν' ν') (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y ∂ν' = ∫⁻ x, F x⁻¹ ∂ν := by
  have e1 : ∫⁻ x, ∫⁻ y, F (x⁻¹ * y) ∂ν' ∂ν = ∫⁻ y, F y ∂ν' := by
    rw [lintegral_congr_ae (g := fun _ => ∫⁻ y, F y ∂ν')]
    · simp
    · filter_upwards [h] with x hx
      exact (hi' _ (U.inv_mem hx)).lintegral_comp hF
  have e2 : ∫⁻ y, ∫⁻ x, F (x⁻¹ * y) ∂ν ∂ν' = ∫⁻ x, F x⁻¹ ∂ν := by
    rw [lintegral_congr_ae (g := fun _ => ∫⁻ x, F x⁻¹ ∂ν)]
    · simp
    · filter_upwards [h'] with y hy
      have := (hi _ (U.inv_mem hy)).lintegral_comp (f := fun x => F x⁻¹) (hF.comp measurable_inv)
      simpa [mul_inv_rev] using this
  rw [← e1, ← e2]
  exact lintegral_lintegral_swap (hF.comp (measurable_fst.inv.mul measurable_snd)).aemeasurable

private theorem nu_pres {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (e : G1 K n ≃ₜ* G1 K n)
    (he : ∀ k, e k ∈ D.U ↔ k ∈ D.U) : MeasurePreserving e D.ν D.ν := by
  have := D.prob
  have hm : Measurable e := e.continuous.measurable
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have : IsProbabilityMeasure (D.ν.map e) := inferInstance
  have hp : MeasurePreserving e D.ν (D.ν.map e) := ⟨hm, rfl⟩
  have hs : ∀ᵐ k ∂(D.ν.map e), k ∈ D.U := by
    rw [hemb.ae_map_iff]
    filter_upwards [D.supp] with k hk using (he k).2 hk
  have hi : ∀ k ∈ D.U, MeasurePreserving (k * ·) (D.ν.map e) (D.ν.map e) := by
    intro k hk
    have hk' : e.symm k ∈ D.U := (he _).1 (by simpa using hk)
    refine ⟨measurable_const_mul k, ?_⟩
    rw [Measure.map_map (measurable_const_mul k) hm]
    conv_rhs => rw [← (D.inv _ hk').map_eq, Measure.map_map hm (measurable_const_mul _)]
    congr 1
    funext x
    simp
  refine ⟨hm, Measure.ext_of_lintegral _ fun F hF => ?_⟩
  rw [lintegral_inv_unique_haar D.U D.ν _ D.supp hs D.inv hi F hF, lintegral_inv_unique_haar D.U D.ν _ D.supp D.supp D.inv D.inv F hF]

private theorem fix_tw {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    (D : TypeDat K n) (θ : Twist μ) (hs : Stable D θ) (f : G1 K n → ℂ) (hf : D.Fix f) :
    D.Fix fun x => f (θ.e.symm x) := by
  intro g
  have hemb : MeasurableEmbedding θ.e := θ.e.toHomeomorph.measurableEmbedding
  rw [← (nu_pres D θ.e hs.1).integral_comp hemb]
  refine Eq.trans (integral_congr_ae ?_) (hf (θ.e.symm g))
  filter_upwards [D.supp] with k hk
  simp [hs.2 k hk]

private theorem reps_uniq {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {v w : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) (hw : Reps μ w φ) : v = w := by
  refine Lp.ext ?_
  have h : ∀ᵐ y ∂μ, (v : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) = (w : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) := by
    filter_upwards [hv, hw] with y a b using a.trans b.symm
  have hm : MeasurableSet {y | (v : RightCosetSpace (Gam K n) → ℂ) y = (w : RightCosetSpace (Gam K n) → ℂ) y} :=
    measurableSet_eq_fun (Lp.stronglyMeasurable v).measurable (Lp.stronglyMeasurable w).measurable
  exact (ae_map_iff (measurable_mk (Gam K n)).aemeasurable hm).2 (ae_restrict_of_ae h)

private theorem reps_tw {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    (θ : Twist μ) {v : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) : Reps μ (θ.U v) fun x => φ (θ.e.symm x) := by
  have hp : MeasurePreserving θ.e.symm μ μ := θ.pres.symm θ.e.toHomeomorph.toMeasurableEquiv
  have h1 := hp.quasiMeasurePreserving.ae hv
  have h2 := QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (θ.U_spec v)
  filter_upwards [h1, h2] with y a b
  rw [b, ← a]
  congr 1
  obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Gam K n)).1 (Quotient.out_eq (mk (Gam K n) y))
  rw [← hγ]
  have : θ.e.symm (γ • y) = θ.e.symm γ * θ.e.symm y := map_mul _ _ _
  rw [this]
  exact mk_mul_of_mem ((θ.mem_gam _).1 (by simp)) _

private theorem th_tw {K : Type} [Field K] [NumberField K] (e : G1 K (2 + 2) ≃ₜ* G1 K (2 + 2))
    (hG : ∀ g, e g ∈ Gam K (2 + 2) ↔ g ∈ Gam K (2 + 2)) (hP : ∀ γ, e γ ∈ PK K ↔ γ ∈ PK K)
    (F : G1 K (2 + 2) → ℂ) (hF : ∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) (g : G1 K (2 + 2)) :
    th (fun x => F (e.symm x)) g = th F (e.symm g) := by
  have hm : ∀ γ : Gam K (2 + 2), (γ : G1 K (2 + 2)) ∈ PK K ↔ γ ∈ ParΓ K 2 2 := fun γ =>
    Subgroup.mem_map_iff_mem (f := (Gam K (2 + 2)).subtype) Subtype.val_injective
  let ε : Gam K (2 + 2) ≃ Gam K (2 + 2) := e.toEquiv.subtypeEquiv fun a => (hG a).symm
  have hε : ∀ a, ((ε a : Gam K (2 + 2)) : G1 K (2 + 2)) = e a := fun a => rfl
  let Q : Cos K ≃ Cos K := Quotient.congr ε fun a b => by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, ← hm, ← hm, ← hP]
    simp [hε]
  unfold th
  rw [← finsum_comp_equiv Q]
  refine finsum_congr fun q => ?_
  have h1 : Q q = Quotient.mk _ (ε q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have h2 : (QuotientGroup.rightRel (ParΓ K 2 2)) (ε q.out) (Q q).out := by
    refine Quotient.exact ?_
    rw [Quotient.out_eq, h1]
  rw [QuotientGroup.rightRel_apply, ← hm] at h2
  have h3 := (hP (e.symm _)).1 (by rw [e.apply_symm_apply]; exact h2)
  rw [← hF _ h3 (_ * e.symm g)]
  congr 1
  simp [hε, mul_assoc]

private theorem sec_tw {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure]
    {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} (i₁ : CuspIrr μ₂ τ₁) (i₂ : CuspIrr μ₂ τ₂)
    {D : TypeDat K (2 + 2)} {σ : K ≃+* K} {θ : Twist μ} {θ₂ : Twist μ₂} (h : UpperTheory.ConvolutionTheory.K.IsGal σ θ)
    (h₂ : UpperTheory.ConvolutionTheory.K.IsGal σ θ₂) (hs : Stable D θ) (m₁ : τ₁.map (θ₂.U : L2 μ₂ →ₗ[ℂ] L2 μ₂) = τ₂)
    (m₂ : τ₂.map (θ₂.U : L2 μ₂ →ₗ[ℂ] L2 μ₂) = τ₁) (f : G1 K (2 + 2) → ℂ) (hf : IsSec τ₁ τ₂ f ∧ D.Fix f) :
    IsSec τ₂ τ₁ (fun x => f (θ.e.symm x)) ∧ D.Fix fun x => f (θ.e.symm x) := by
  have hx := fix_tw D θ hs f hf.2
  obtain ⟨g1, g2, -⟩ := galLaws μ μ₂ σ θ θ₂ h h₂
  have g3 : ∀ a b t, θ.e.symm (lv a b t) = lv (θ₂.e.symm a) (θ₂.e.symm b) t := fun a b t => by
    apply θ.e.injective
    simp [g1]
  obtain ⟨c, ⟨C, hC⟩, hn, hr, hl⟩ := (secCrit μ₂ τ₁ τ₂ D i₁ i₂ f hf.2).1 hf.1
  refine ⟨(secCrit μ₂ τ₂ τ₁ D i₂ i₁ _ hx).2 ⟨c.comp θ.e.symm.continuous, ⟨C, fun g => hC _⟩, fun X g => ?_, fun t g => ?_,
    fun g => ⟨fun b => ?_, fun a => ?_⟩⟩, hx⟩
  · obtain ⟨Y, hY⟩ := (g2 X).2
    simp only [map_mul, hY, hn]
  · simp only [map_mul, g3, map_one, hr]
  · obtain ⟨v, hv, hv'⟩ := (hl (θ.e.symm g)).1 (θ₂.e.symm b)
    refine ⟨θ₂.U v, m₁ ▸ Submodule.mem_map_of_mem hv, ?_⟩
    simpa only [map_mul, g3] using reps_tw θ₂ hv'
  · obtain ⟨v, hv, hv'⟩ := (hl (θ.e.symm g)).2 (θ₂.e.symm a)
    refine ⟨θ₂.U v, m₂ ▸ Submodule.mem_map_of_mem hv, ?_⟩
    simpa only [map_mul, g3] using reps_tw θ₂ hv'

private theorem lin_tw {K : Type} [Field K] [NumberField K] {μ : Measure (G1 K (2 + 2))}
    {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ ρ₁ ρ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d d' : ℕ} (A : Line μ τ₁ τ₂ D d)
    (A' : Line μ ρ₁ ρ₂ D d') (e : G1 K (2 + 2) ≃ G1 K (2 + 2))
    (h : ∀ f, IsSec τ₁ τ₂ f ∧ D.Fix f → IsSec ρ₁ ρ₂ (fun x => f (e x)) ∧ D.Fix fun x => f (e x)) :
    ∃ s : Eu d →ₗ[ℂ] Eu d', Function.Injective s ∧ ∀ v, A'.sec (s v) = fun x => A.sec v (e x) := by
  obtain ⟨r, hr⟩ := A'.sec.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 A'.inj)
  have key : ∀ v, A'.sec ((r ∘ₗ LinearMap.funLeft ℂ ℂ e ∘ₗ A.sec) v) = fun x => A.sec v (e x) := fun v => by
    obtain ⟨w, hw⟩ := (A'.onto _).2 (h _ ((A.onto _).1 ⟨v, rfl⟩))
    have : (r ∘ₗ LinearMap.funLeft ℂ ℂ e ∘ₗ A.sec) v = r (A'.sec w) := by rw [hw]; rfl
    rw [this, ← hw]
    exact congrArg _ (LinearMap.congr_fun hr w)
  refine ⟨_, fun v w hvw => A.inj (funext fun x => ?_), key⟩
  have := congrFun ((key v).symm.trans ((congrArg A'.sec hvw).trans (key w))) (e.symm x)
  simpa using this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.convU :
    ConvUC := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' σ θ θ₂ h h₂ hs m₁ m₂
  obtain ⟨s, hsi, hsec⟩ := lin_tw A A' θ.e.symm.toEquiv (sec_tw hp.irr₁ hp.irr₂ h h₂ hs m₁ m₂)
  obtain ⟨s', hsi', -⟩ := lin_tw A' A θ.e.symm.toEquiv (sec_tw hp.irr₂ hp.irr₁ h h₂ hs m₂ m₁)
  have hd : Module.finrank ℂ (Eu d) = Module.finrank ℂ (Eu d') :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hsi) (LinearMap.finrank_le_finrank_of_injective hsi')
  obtain ⟨-, -, -, gP, gH⟩ := galLaws μ μ₂ σ θ θ₂ h h₂
  obtain ⟨U, hU, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary K _ μ θ
  let S : L (Eu d) →L[ℂ] L (Eu d') := (LinearMap.toContinuousLinearMap s).compLpL 2 volume
  have hS : ∀ u, ∀ᵐ x : ℝ, S u x = s (u x) := fun u => (LinearMap.toContinuousLinearMap s).coeFn_compLpL u
  have hcomm : θ.U ∘L A.J.toContinuousLinearMap = A'.J.toContinuousLinearMap ∘L S := by
    refine ContinuousLinearMap.ext_on (denseCc d).1 ?_
    rintro u ⟨β, v, hβ, hβc, hu⟩
    have hv := (A.onto _).1 ⟨v, rfl⟩
    have hb := (bfFun _ β (secFun μ₂ τ₁ τ₂ D hp.irr₁ hp.irr₂ _ hv.1 hv.2) hβ hβc).1.rat
    have r1 := reps_tw θ (A.spec β v u hβ hβc hu)
    have r2 := A'.spec β (s v) (S u) hβ hβc (by
      filter_upwards [hS u, hu] with x a b
      rw [a, b, map_smul])
    refine reps_uniq r1 ?_
    have : theta β (A'.sec (s v)) = fun x => theta β (A.sec v) (θ.e.symm x) := by
      funext x
      rw [theta_eq, theta_eq, ← th_tw θ.e θ.mem_gam gP _ hb, hsec]
      congr 1
      funext y
      have : HP 2 2 (θ.e.symm y) = HP 2 2 y := by simpa using (gH (θ.e.symm y)).symm
      simp only [bf, this]
      rfl
    rw [← this]
    exact r2
  have hc : ∀ (u : L (Eu d)) (v : L (Eu d')), (∀ᵐ x : ℝ, v x = s (u x)) → θ.U (A.J u) = A'.J v := fun u v huv => by
    have : v = S u := Lp.ext (by filter_upwards [huv, hS u] with x a b using a.trans b.symm)
    rw [this]
    exact congrArg (fun T : L (Eu d) →L[ℂ] L2 μ => T u) hcomm
  have hn : ∀ v, ‖s v‖ = ‖v‖ := fun v => by
    have hI : (volume : Measure ℝ) (Icc 0 1) ≠ ∞ := by simp
    have := hc (indicatorConstLp 2 measurableSet_Icc hI v) (indicatorConstLp 2 measurableSet_Icc hI (s v)) (by
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Icc) (hμs := hI) (c := v),
        indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Icc) (hμs := hI) (c := s v)] with x a b
      rw [a, b]
      by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [hx])
    have h2 := congrArg norm this
    rw [← hU] at h2
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map,
      LinearIsometry.norm_map] at h2
    rw [norm_indicatorConstLp (by simp) (by simp), norm_indicatorConstLp (by simp) (by simp)] at h2
    simpa using h2.symm
  exact ⟨LinearIsometry.toLinearIsometryEquiv ⟨s, hn⟩ hd, fun v x => congrFun (hsec v) x, hc⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TChiSec
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

set_option synthInstance.maxHeartbeats 400000

private theorem exists_rep {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (φ : G1 K n → ℂ) (hc : Continuous φ) (hi : ∀ γ ∈ Gam K n, ∀ g, φ (γ * g) = φ g) (C : ℝ) (hC : ∀ g, ‖φ g‖ ≤ C) :
    ∃ v : L2 μ, Reps μ v φ := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  let f : RightCosetSpace (Gam K n) → ℂ := fun x => φ x.out
  have hf : ∀ g, f (mk (Gam K n) g) = φ g := fun g => by
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Gam K n) (g := (mk (Gam K n) g).out) (h := g)).1 (Quotient.out_eq _)
    change φ _ = _
    rw [← hγ]
    exact hi γ γ.2 g
  have hfc : Continuous f := by
    rw [(isOpenQuotientMap_mk (Gam K n)).isQuotientMap.continuous_iff]
    have : f ∘ mk (Gam K n) = φ := funext hf
    rwa [this]
  have hm : MemLp f 2 (quotientMeasure (Gam K n) μ) :=
    MemLp.of_bound hfc.aestronglyMeasurable C (Eventually.of_forall fun x => hC _)
  refine ⟨hm.toLp f, ?_⟩
  have h1 := hm.coeFn_toLp
  have h2 : ∀ᵐ y ∂μ.restrict (fundamentalDomain (Gam K n)), (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y) :=
    ae_of_ae_map (measurable_mk (Gam K n)).aemeasurable h1
  have hF := isFundamentalDomain_fundamentalDomain (Gam K n) μ
  have h3 : μ {y | ¬ (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y)} = 0 := by
    refine hF.measure_zero_of_invariant _ (fun γ => ?_) ?_
    · ext y
      simp [Set.mem_smul_set_iff_inv_smul_mem]
    · rw [ae_restrict_iff' (measurableSet_fundamentalDomain (Gam K n)), ae_iff] at h2
      refine measure_mono_null (fun y hy => ?_) h2
      exact fun h => hy.1 (h hy.2)
  have h4 : ∀ᵐ y ∂μ, (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y) := ae_iff.2 h3
  filter_upwards [h4] with y hy
  rw [hy, hf]

private theorem orth {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} (u : L2 μ) {w : L2 μ}
    {ψ : G1 K n → ℂ} (hw : Reps μ w ψ) :
    ∫ m, conj ((u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) m)) * ψ m ∂fd μ = ⟪u, w⟫_ℂ := by
  rw [L2.inner_def, integral_quotientMeasure]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hw] with y h2
  rw [h2, RCLike.inner_apply, mul_comm]

private theorem contInt {Y G : Type} [TopologicalSpace Y] [FirstCountableTopology Y] [LocallyCompactSpace Y]
    [TopologicalSpace G] [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G)
    [IsLocallyFiniteMeasure μ] {w : G → ℂ} (hw : Continuous w) (hwc : HasCompactSupport w) {Φ : Y × G → ℂ}
    (hΦ : Continuous Φ) : Continuous fun y => ∫ g, w g * Φ (y, g) ∂μ := by
  have := continuous_parametric_integral_of_continuous (μ := μ) (f := fun y g => w g * Φ (y, g))
    ((hw.comp continuous_snd).mul hΦ) hwc.isCompact
  refine this.congr fun y => setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_
  rw [image_eq_zero_of_notMem_tsupport hg, zero_mul]

private theorem slice_int {K : Type} [Field K] [NumberField K] {n N : ℕ} (μ : Measure (G1 K N)) [μ.IsHaarMeasure]
    (μ₂ : Measure (G1 K n)) [μ₂.IsHaarMeasure] (τ : Submodule ℂ (L2 μ₂)) (hτ : IsClosed (τ : Set (L2 μ₂)))
    {w : G1 K N → ℂ} (hw : Continuous w) (hwc : HasCompactSupport w) {Φ : G1 K n × G1 K N → ℂ} (hΦ : Continuous Φ)
    {C : ℝ} (hC : ∀ p, ‖Φ p‖ ≤ C) (hi : ∀ γ ∈ Gam K n, ∀ m g, Φ (γ * m, g) = Φ (m, g))
    (hr : ∀ g, ∃ v ∈ τ, Reps μ₂ v fun m => Φ (m, g)) : ∃ v ∈ τ, Reps μ₂ v fun m => ∫ g, w g * Φ (m, g) ∂μ := by
  have hwi : Integrable w μ := hw.integrable_of_hasCompactSupport hwc
  obtain ⟨v, hv⟩ := exists_rep μ₂ (fun m => ∫ g, w g * Φ (m, g) ∂μ) (contInt μ hw hwc hΦ)
    (fun γ hγ m => by simp only [hi γ hγ]) (∫ g, ‖w g‖ * C ∂μ) fun m =>
      norm_integral_le_of_norm_le (hwi.norm.mul_const C) (Eventually.of_forall fun g => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  refine ⟨v, ?_, hv⟩
  haveI := hτ.completeSpace_coe
  rw [← τ.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro u hu
  haveI := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ₂
  have hu1 : Integrable (fun m => (u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) m)) (fd μ₂) :=
    ((Lp.memLp u).integrable one_le_two).comp_measurable (measurable_mk _)
  have hu2 : Integrable (fun m => conj ((u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) m))) (fd μ₂) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hu1
  haveI : BorelSpace (G1 K n × G1 K N) := Prod.borelSpace
  have hI : Integrable (fun p : G1 K n × G1 K N =>
      conj ((u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) p.1)) * w p.2 * Φ p) ((fd μ₂).prod μ) :=
    (hu2.mul_prod hwi).mul_bdd hΦ.aestronglyMeasurable (Eventually.of_forall hC)
  rw [← orth u hv]
  simp only [← integral_const_mul, ← mul_assoc]
  rw [integral_integral_swap (f := fun m g => conj ((u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) m)) * w g * Φ (m, g)) hI]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun g => ?_)
  obtain ⟨v', hv', h⟩ := hr g
  have := orth u h
  rw [Submodule.inner_left_of_mem_orthogonal hv' hu] at this
  simp only [mul_comm _ (w g), mul_assoc, integral_const_mul, this, mul_zero, Pi.zero_apply]

private theorem fix_int {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [IsFiniteMeasure ν]
    {U : Set G} (hU : IsCompact U) (hν : ∀ᵐ k ∂ν, k ∈ U) {e a Θ : G → ℂ} (he : Continuous e) (ha : Continuous a)
    (hac : HasCompactSupport a) (hΘ : Continuous Θ) (h : ∀ g, ∫ k, e k * a (k⁻¹ * g) ∂ν = a g) :
    ∫ k, e k * ∫ g, a g * Θ (k * g) ∂μ ∂ν = ∫ g, a g * Θ g ∂μ := by
  have e1 : ∀ k, e k * ∫ g, a g * Θ (k * g) ∂μ = ∫ g, e k * a (k⁻¹ * g) * Θ g ∂μ := fun k => by
    rw [← integral_const_mul, ← integral_mul_left_eq_self _ k⁻¹]
    simp only [mul_inv_cancel_left, mul_assoc]
  have hc : Continuous fun p : G × G => e p.1 * a (p.1⁻¹ * p.2) * Θ p.2 := by fun_prop
  have hI : Integrable (fun p : G × G => e p.1 * a (p.1⁻¹ * p.2) * Θ p.2) (ν.prod μ) := by
    refine (hc.continuousOn.integrableOn_compact (hU.prod (hU.mul hac.isCompact))).integrable_of_ae_notMem_eq_zero ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν] with p hp hn
    have : a (p.1⁻¹ * p.2) = 0 := by_contra fun h0 =>
      hn ⟨hp, p.1, hp, _, subset_tsupport _ h0, mul_inv_cancel_left _ _⟩
    rw [this, mul_zero, zero_mul]
  simp only [e1]
  rw [integral_integral_swap (f := fun k g => e k * a (k⁻¹ * g) * Θ g) hI]
  simp only [integral_mul_const, h]

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.tChiSec :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ → ∀ (a : CC K (2 + 2)) (χ : ℝ → ℂ) (f : G1 K (2 + 2) → ℂ),
      D.Hecke a → Continuous χ → IsSec τ₁ τ₂ f → D.Fix f → IsSec τ₁ τ₂ (tChi μ a χ f) ∧ D.Fix (tChi μ a χ f) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ D h₁ h₂ a χ f ha hχ hf hD
  obtain ⟨hH1, hH2, -, hHc, hH5⟩ := hpSpec (K := K)
  obtain ⟨-, hmul, -, hlv, -⟩ := blkLaws (K := K)
  obtain ⟨hU, hUK, -⟩ := typeFin D
  obtain ⟨hfc, ⟨C, hC⟩, hfu, hfr, hfs⟩ := (secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hD).1 hf
  have hS := secFun μ₂ τ₁ τ₂ D h₁ h₂ f hf hD
  let ψ : ℝ → ℂ := fun s => χ s * Complex.exp (2 * (s : ℂ))
  have hψ : Continuous ψ := by
    simp only [ψ]
    fun_prop
  have hT : ∀ x, tChi μ a χ f x = ∫ g, a g * (ψ (HH (x * g) - HH x) * f (x * g)) ∂μ := fun x => by
    simp only [tChi, ψ, mul_assoc]
  have hlv0 : ∀ m₁ m₂ t y, HH (lv m₁ m₂ t * y) = t + HH (y : G1 K (2 + 2)) := fun m₁ m₂ t y => by
    have := hH1 0 m₁ m₂ t y
    rwa [show (nn 0 : G1 K (2 + 2)) = 1 from unipOne_zero 2, one_mul] at this
  have hfix : D.Fix (tChi μ a χ f) := fun x => by
    haveI := D.prob
    rw [hT x, ← fix_int μ D.ν hU D.supp D.cont (a := fun g => a g) a.continuous a.hasCompactSupport
      (Θ := fun g => ψ (HH (x * g) - HH x) * f (x * g))
      ((hψ.comp ((hHc.comp (continuous_const.mul continuous_id)).sub continuous_const)).mul
        (hfc.comp (continuous_const.mul continuous_id))) fun g => (ha g).1]
    refine integral_congr_ae ?_
    filter_upwards [D.supp] with k hk
    rw [hT, (hH2 k (hUK hk)).2]
    simp only [mul_assoc]
  have hsl : ∀ m₁ m₂ x, tChi μ a χ f (lv m₁ m₂ 0 * x) =
      ∫ g, (a g * ψ (HH (x * g) - HH x)) * f (lv m₁ m₂ 0 * (x * g)) ∂μ := fun m₁ m₂ x => by
    simp only [hT, mul_assoc, hlv0, zero_add]
  have hw : ∀ x, Continuous fun g => a g * ψ (HH (x * g) - HH x) := fun x =>
    a.continuous.mul (hψ.comp ((hHc.comp (continuous_const.mul continuous_id)).sub continuous_const))
  refine ⟨(secCrit μ₂ τ₁ τ₂ D h₁ h₂ _ hfix).2 ⟨?_, ?_, fun X x => ?_, fun t x => ?_, fun x => ⟨fun m₂ => ?_, fun m₁ => ?_⟩⟩,
    hfix⟩
  · refine (contInt μ (w := fun g => a g) a.continuous a.hasCompactSupport (Φ := fun p : G1 K (2 + 2) × G1 K (2 + 2) =>
      ψ (HH (p.1 * p.2) - HH p.1) * f (p.1 * p.2)) ?_).congr fun x => (hT x).symm
    exact (hψ.comp ((hHc.comp continuous_mul).sub (hHc.comp continuous_fst))).mul (hfc.comp continuous_mul)
  · obtain ⟨R, hR⟩ := hH5 _ a.hasCompactSupport.isCompact
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hψ.continuousOn
    refine ⟨∫ g, ‖a g‖ * (M * C) ∂μ, fun x => ?_⟩
    rw [hT]
    refine norm_integral_le_of_norm_le
      ((a.continuous.integrable_of_hasCompactSupport a.hasCompactSupport).norm.mul_const _) (Eventually.of_forall fun g => ?_)
    by_cases h0 : a g = 0
    · simp [h0]
    · have h1 := hM _ (abs_le.1 (hR x g (subset_tsupport _ h0)))
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul h1 (hC _) (norm_nonneg _) ((norm_nonneg _).trans h1)) (norm_nonneg _)
  · have h0 : ∀ y, HH (nn X * y) = HH y := fun y => by
      have := hH1 X 1 1 0 y
      rwa [(blkLaws (K := K)).2.2.1, mul_one, zero_add] at this
    simp only [hT, mul_assoc, h0, hfu]
  · simp only [hT, mul_assoc, hlv0, hfr, add_sub_add_left_eq_sub]
  · simp only [hsl]
    refine slice_int μ μ₂ τ₁ h₁.closed (hw x) a.hasCompactSupport.mul_right
      (Φ := fun p => f (lv p.1 m₂ 0 * (x * p.2))) ?_ (fun _ => hC _) (fun γ hγ m g => ?_) fun g => (hfs (x * g)).1 m₂
    · have : Continuous fun p : G1 K 2 × G1 K (2 + 2) => (p.1, m₂, (0 : ℝ)) := by fun_prop
      exact hfc.comp ((hlv.comp this).mul (continuous_const.mul continuous_snd))
    · have e : lv (γ * m) m₂ 0 = lv γ 1 0 * lv m m₂ 0 := by rw [hmul, one_mul, add_zero]
      have := hS.rat (lv γ 1 0) (((pkLaws (K := K)).2.1 _).2 ⟨0, ⟨γ, hγ⟩, 1, by
        change lv γ 1 0 = nn 0 * lv γ 1 0
        rw [show (nn 0 : G1 K (2 + 2)) = 1 from unipOne_zero 2, one_mul]⟩)
      simp only [e, mul_assoc, this]
  · simp only [hsl]
    refine slice_int μ μ₂ τ₂ h₂.closed (hw x) a.hasCompactSupport.mul_right
      (Φ := fun p => f (lv m₁ p.1 0 * (x * p.2))) ?_ (fun _ => hC _) (fun γ hγ m g => ?_) fun g => (hfs (x * g)).2 m₁
    · have : Continuous fun p : G1 K 2 × G1 K (2 + 2) => (m₁, p.1, (0 : ℝ)) := by fun_prop
      exact hfc.comp ((hlv.comp this).mul (continuous_const.mul continuous_snd))
    · have e : lv m₁ (γ * m) 0 = lv 1 γ 0 * lv m₁ m 0 := by rw [hmul, one_mul, add_zero]
      have := hS.rat (lv 1 γ 0) (((pkLaws (K := K)).2.1 _).2 ⟨0, 1, ⟨γ, hγ⟩, by
        change lv 1 γ 0 = nn 0 * lv 1 γ 0
        rw [show (nn 0 : G1 K (2 + 2)) = 1 from unipOne_zero 2, one_mul]⟩)
      simp only [e, mul_assoc, this]
end

