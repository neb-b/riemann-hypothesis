module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0057
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaust
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanSelfdualMeasureDiscriminantScaled
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem real_coord_eq_re {F : Type} [Field F] [NumberField F]
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (hh : IsHomeomorph e)
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) (x : Ainf F) (w : InfinitePlace F) :
    e x w = (InfinitePlace.Completion.extensionEmbedding w (x w)).re := by
  have hf : Continuous fun y : Ainf F => e y w := (continuous_apply w).comp hh.continuous
  have hg : Continuous fun y : Ainf F =>
      (InfinitePlace.Completion.extensionEmbedding w (y w)).re :=
    Complex.continuous_re.comp
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w))
  have key := (InfiniteAdeleRing.denseRange_algebraMap (K := F)).equalizer hf hg (by
    funext k
    simp only [Function.comp_apply]
    rw [he, GroundTheory.Global.extensionEmbedding_algebraMap_apply, ← hρ, Complex.ofReal_re])
  exact congrFun key x

theorem psiInf_std_mul {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (hh : IsHomeomorph e)
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) (s t : Ainf F) :
    psiInf F (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F)) (s * t) =
      Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (e s ⬝ᵥ e t) : ℝ) : ℂ)) := by
  have htr : GroundTheory.Global.infiniteTrace F (s * t) = e s ⬝ᵥ e t := by
    rw [GroundTheory.Global.infiniteTrace_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [(hF.isReal w).mult_eq_one, Nat.cast_one, one_mul,
      ← real_coord_eq_re ρ e hρ hh he, map_mul, Pi.mul_apply]
  have h1 : GroundTheory.Global.adelicChar F (pairA F (s * t) 0) =
      Real.fourierChar (-GroundTheory.Global.infiniteTrace F (s * t)) :=
    GroundTheory.Global.adelicChar_infinite (K := F) (s * t)
  show ((GroundTheory.Global.adelicChar F (pairA F (s * t) 0) : Circle) : ℂ) = _
  rw [h1, htr, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem selfDual_psiInf_std (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (laminf : Measure (Ainf F)) (hl : IsStdInf laminf) :
    SelfDual (Real.toNNReal (Real.sqrt |(discr F : ℝ)|) • laminf)
      (fun s t => psiInf F (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F)) (s * t)) := by
  obtain ⟨ρ, e, hρ, hh, he, -, hm⟩ := real_iso F hF
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  let e' : Ainf F ≃ₜ+ (InfinitePlace F → ℝ) :=
    { e.toAddEquiv with
      continuous_toFun := hh.continuous
      continuous_invFun :=
        (e.toEquiv.toHomeomorphOfContinuousOpen hh.continuous hh.isOpenMap).symm.continuous }
  have hcoe : ∀ x, e' x = e x := fun _ => rfl
  set c : ℝ := Real.sqrt |(discr F : ℝ)| with hc
  have hc0 : 0 < c := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
    exact Real.sqrt_pos.mpr (abs_pos.mpr this)
  have hmap : (Real.toNNReal c • laminf).map e' = (volume : Measure (InfinitePlace F → ℝ)) := by
    have h1 : laminf.map e' = ENNReal.ofReal c⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := hm laminf hl
    have h2 : ((Real.toNNReal c : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal c⁻¹ = 1 := by
      rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hc0.le,
        ← ENNReal.ofReal_mul hc0.le, mul_inv_cancel₀ hc0.ne', ENNReal.ofReal_one]
    rw [Measure.map_smul, h1, ENNReal.smul_def, smul_smul, h2, one_smul]
    exact e'.continuous.measurable.aemeasurable
  have hsd := selfDual_real_coord (InfinitePlace F) (-1) (Or.inr rfl)
  rw [← hmap] at hsd
  have := (selfDual_transport (Ainf F) (InfinitePlace F → ℝ) e' (Real.toNNReal c • laminf)
    (fun x y => Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℂ)))).mpr hsd
  convert this using 3 with s t
  exact psiInf_std_mul hF ρ e hρ hh he s t

end GlobalTheory.CompanionTheory.SW
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DiscriminantDifferentProductFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix nonZeroDivisors

namespace GlobalTheory.CompanionTheory.SW.SelfDual

theorem differentExp_finite (F : Type) [Field F] [NumberField F] :
    {v : HeightOneSpectrum (𝓞 F) | GroundTheory.Global.differentExp v ≠ 0}.Finite := by
  unfold GroundTheory.Global.differentExp
  exact Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)

private theorem differentIdeal_int_ne_zero (F : Type) [Field F] [NumberField F] :
    differentIdeal ℤ (𝓞 F) ≠ 0 := by
  intro h
  have h1 := absNorm_differentIdeal F (𝓞 F)
  rw [h, map_zero] at h1
  exact discr_ne_zero F (Int.natAbs_eq_zero.1 h1.symm)

private theorem differentExp_eq_count_differentIdeal (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    GroundTheory.Global.differentExp v =
      ((Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors : ℤ) := by
  unfold GroundTheory.Global.differentExp
  exact FractionalIdeal.count_coe F v (differentIdeal_int_ne_zero F)

private theorem prod_absNorm_pow_count_differentIdeal_eq_natAbs_discr (F : Type) [Field F] [NumberField F] :
    ∏ v ∈ (differentExp_finite F).toFinset, Ideal.absNorm v.asIdeal ^
      ((Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors) =
      (discr F).natAbs := by
  have hprod := Ideal.finprod_heightOneSpectrum_factorization (differentIdeal_int_ne_zero F)
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := (differentExp_finite F).toFinset) ?_] at hprod
  · have hN := congrArg Ideal.absNorm hprod
    rw [map_prod, absNorm_differentIdeal F (𝓞 F)] at hN
    rw [← hN]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [HeightOneSpectrum.maxPowDividing, map_pow]
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq, differentExp_eq_count_differentIdeal]
    intro h0
    apply hv
    have h0' : (Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors = 0 := by
      exact_mod_cast h0
    rw [HeightOneSpectrum.maxPowDividing, h0', pow_zero]

theorem sqrt_discr_mul_finprod_different (F : Type) [Field F] [NumberField F] :
    (∀ᶠ v in Filter.cofinite, (Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ≥0) ^ (((-GroundTheory.Global.differentExp v : ℤ) : ℝ) / 2) = 1) ∧ Real.toNNReal (Real.sqrt |(discr F : ℝ)|) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (((-GroundTheory.Global.differentExp v : ℤ) : ℝ) / 2) = 1 := by
  refine ⟨?_, ?_⟩
  · filter_upwards [FractionalIdeal.finite_factors (K := F)
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)] with v hv
    have hv' : GroundTheory.Global.differentExp v = 0 := hv
    rw [hv']
    simp
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := (differentExp_finite F).toFinset) ?_]
    · have hterm : ∀ v : HeightOneSpectrum (𝓞 F),
          (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (((-GroundTheory.Global.differentExp v : ℤ) : ℝ) / 2) =
            ((Ideal.absNorm v.asIdeal : ℝ≥0) ^
              ((Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors)) ^
                (-(1 / 2 : ℝ)) := by
        intro v
        rw [differentExp_eq_count_differentIdeal, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
        congr 1
        push_cast
        ring
      rw [Finset.prod_congr rfl (fun v _ => hterm v), NNReal.finsetProd_rpow]
      have h := congrArg (fun n : ℕ => (n : ℝ≥0)) (prod_absNorm_pow_count_differentIdeal_eq_natAbs_discr F)
      simp only [Nat.cast_prod, Nat.cast_pow] at h
      rw [h]
      have ha0 : ((discr F).natAbs : ℝ≥0) ≠ 0 := by
        exact_mod_cast Int.natAbs_ne_zero.2 (discr_ne_zero F)
      have ha : (((discr F).natAbs : ℝ≥0) : ℝ) = |(discr F : ℝ)| := by
        rw [NNReal.coe_natCast, Nat.cast_natAbs, Int.cast_abs]
      rw [← ha, ← Real.coe_sqrt, Real.toNNReal_coe, NNReal.sqrt_eq_rpow, ← NNReal.rpow_add ha0]
      norm_num
    · intro v hv
      rw [Function.mem_mulSupport] at hv
      rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      intro h0
      exact hv (by rw [h0]; simp)

end GlobalTheory.CompanionTheory.SW.SelfDual
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaCountCompactFinite
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CntFin

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
  {μ : Measure (HA (AF F) σ J)} {𝓕 : Set (HA (AF F) σ J)}

theorem cntI_mono_fun {S : Set (Fin n → Fin M → E)}
    {Φ Ψ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞} (h : ∀ Y, Φ Y ≤ Ψ Y) :
    cntI σ J μ 𝓕 S Φ ≤ cntI σ J μ 𝓕 S Ψ :=
  lintegral_mono fun _ => ENNReal.tsum_le_tsum fun _ => h _

theorem cntI_le_of_contrib {S S' : Set (Fin n → Fin M → E)}
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞}
    (h : ∀ (g : HA (AF F) σ J) (X : Fin n → Fin M → E), X ∈ S →
      Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ≠ 0 → X ∈ S') :
    cntI σ J μ 𝓕 S Φ ≤ cntI σ J μ 𝓕 S' Φ := by
  refine lintegral_mono fun g => ?_
  rw [tsum_subtype S (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))),
    tsum_subtype S' (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)))]
  refine ENNReal.tsum_le_tsum fun X => ?_
  by_cases hX : X ∈ S
  · by_cases h0 : Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) = 0
    · simp [Set.indicator, h0]
    · simp [Set.indicator, hX, h g X hX h0]
  · simp [Set.indicator, hX]

theorem cntI_union_le [Countable E] {S S' : Set (Fin n → Fin M → E)}
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞}
    (hm : ∀ X : Fin n → Fin M → E,
      Measurable fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) :
    cntI σ J μ 𝓕 (S ∪ S') Φ ≤ cntI σ J μ 𝓕 S Φ + cntI σ J μ 𝓕 S' Φ := by
  unfold cntI
  rw [← lintegral_add_left (Measurable.tsum fun X : S => hm X)]
  exact lintegral_mono fun g => ENNReal.tsum_union_le
    (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) S S'

end SlopeTestRemainingChoices

theorem cntI_nonzero_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M →
    ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 →
    ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω →
      cntI σ J μ 𝓕 {X | X ≠ 0} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM μ 𝓕 hH hFD Ω hΩ
  classical
  obtain ⟨⟨hAlc, hAsc, hAt2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hAlc
  haveI := hAsc
  haveI := hAt2
  obtain ⟨hTG, -, -, -, hBor, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM M J hJ (AF F)
  haveI := hTG
  haveI := hBor
  obtain ⟨-, -, -, hKt2, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := hKt2
  haveI : Countable E :=
    ((Module.finBasis ℚ E).equivFun.toEquiv).injective.countable
  haveI : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hcl : IsClosed Ω := hΩ.isClosed
  set Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞ := Set.indicator Ω (fun _ => (1 : ℝ≥0∞)) with hΦ

  have hm : ∀ X : Fin 1 → Fin M → E,
      Measurable fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) := by
    intro X
    have hc : Continuous fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X) :=
      (hact 1).1.comp (continuous_inv.prodMk continuous_const)
    have hs : MeasurableSet ((fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ⁻¹' Ω) :=
      (hcl.preimage hc).measurableSet
    have he : (fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) =
        Set.indicator ((fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ⁻¹' Ω)
          (fun _ => (1 : ℝ≥0∞)) := by
      funext g
      by_cases hg : actW (AF F) σ J g⁻¹ (ratTup (AF F) X) ∈ Ω <;> simp [hΦ, Set.indicator, hg]
    rw [he]
    exact measurable_const.indicator hs

  have hzero : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} Φ < ⊤ := by
    obtain ⟨-, hbox, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.BoxF.box_facts F E σ hCM _ (Module.finBasis F E) 1 M
    obtain ⟨N, r, hN, hr, hsub⟩ := hbox Ω hΩ
    obtain ⟨C, hC⟩ := _root_.GlobalTheory.CompanionTheory.SW.mean_isotropic_box F E σ hCM M J hJ hM μ 𝓕 hH hFD _ (Module.finBasis F E) N hN
    refine lt_of_le_of_lt (le_trans (cntI_mono_fun fun Y => ?_) (hC r hr)) ENNReal.ofReal_lt_top
    exact Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le) Y

  have hlen : ∀ t : F, t ≠ 0 →
      cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E t} Φ < ⊤ := by
    intro t ht
    exact _root_.GlobalTheory.CompanionTheory.SW.CountGen.finite_count F E σ hCM M J hJ
      (fun M' _ J' hJ' => GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M' J' hJ') t ht μ 𝓕 hH hFD Ω hΩ

  have hfinset : ∀ T : Finset F, (∀ t ∈ T, t ≠ 0) →
      cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
        ∃ t ∈ T, gramE σ J X = fun _ _ => algebraMap F E t} Φ < ⊤ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      simpa using hzero
    | insert a T _ ih =>
      intro hT
      have hsub : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
          ∃ t ∈ insert a T, gramE σ J X = fun _ _ => algebraMap F E t} Φ ≤
          cntI σ J μ 𝓕 ({X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E a} ∪
            {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
              ∃ t ∈ T, gramE σ J X = fun _ _ => algebraMap F E t}) Φ := by
        refine cntI_le_of_contrib fun g X hX _ => ?_
        rcases hX with hX | ⟨t, ht, hX⟩
        · exact Or.inr (Or.inl hX)
        · rcases Finset.mem_insert.1 ht with rfl | ht'
          · exact Or.inl hX
          · exact Or.inr (Or.inr ⟨t, ht', hX⟩)
      refine lt_of_le_of_lt (hsub.trans (cntI_union_le hm)) (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
      · exact hlen a (hT a (Finset.mem_insert_self a T))
      · exact ih fun t ht => hT t (Finset.mem_insert_of_mem ht)
  obtain ⟨hlenQ, hgram, hfin⟩ := _root_.GlobalTheory.CompanionTheory.SW.FinQ.gram_rational_finite F E σ hCM M J hJ
  refine lt_of_le_of_lt ?_ (hfinset ((hfin Ω hΩ).toFinset.erase 0)
    fun t ht => (Finset.mem_erase.1 ht).1)
  refine cntI_le_of_contrib fun g X hX hne => ?_
  have hY : actW (AF F) σ J g⁻¹ (ratTup (AF F) X) ∈ Ω := by
    by_contra hY
    exact hne (by simp [hΦ, Set.indicator, hY])
  obtain ⟨t, ht⟩ := hlenQ X
  by_cases h0 : t = 0
  · refine Or.inl ⟨hX, ?_⟩
    rw [ht, h0]
    funext a b
    simp
  · refine Or.inr ⟨t, Finset.mem_erase.2 ⟨h0, ?_⟩, ht⟩
    refine (Set.Finite.mem_toFinset _).2 ⟨_, hY, ?_⟩
    rw [((hact 1).2.2.2 g⁻¹ (ratTup (AF F) X)), hgram 1 X, ht]
    funext a b
    rfl

end GlobalTheory.CompanionTheory.SW.CntFin
end

