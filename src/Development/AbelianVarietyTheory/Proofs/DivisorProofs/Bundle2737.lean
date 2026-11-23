module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernel
section
noncomputable section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKWeil

theorem cone_zero (F : Type) [Field F] [NumberField F] (n d : ℕ) (c : ℝ) :
    ∫⁻ t in GlobalTheory.SiegelSet.cone 0 c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  have e : ∀ t : Fin 0 → ℝ, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) = 1 := fun t => by
    simp [GlobalTheory.SiegelSet.modulus]
  simp only [e, setLIntegral_const, one_mul]
  refine (measure_mono (Set.subset_univ _)).trans_lt ?_
  rw [MeasureTheory.volume_pi, Measure.pi_univ]
  simp

theorem mul_le_max_mul {C H₁ H P : ℝ} (h0 : 0 ≤ H₁) (h1 : H₁ ≤ H) (hP : 0 ≤ P) : C * H₁ * P ≤ max C 0 * H * P := by
  refine mul_le_mul_of_nonneg_right ?_ hP
  calc C * H₁ ≤ max C 0 * H₁ := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max C 0 * H := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
theorem one_le_ht {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (h : UA σ J) : (1 : ℝ) ≤ ht h := by
  have := GlobalTheory.AdelicU.one_le_heightGL (F := F) h.1
  exact_mod_cast this


open scoped Classical in
theorem weilConv (hKP : KP) : WeilConv := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP hdim
  have hb := _root_.GlobalTheory.ThKBasic.thetaBasic hKP.base F E σ B n d X W M χX χW om r s r' s' hP
  have hcm := hP.base.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hJ' : IsHermND σ ((1 : E) • X.J.map σ) := by
    rw [one_smul]; exact GlobalTheory.UnitaryVol.isHermND_map hσ hP.herm
  let e : UA σ X.J ≃* GAd σ ((1 : E) • X.J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ (one_ne_zero : (1 : E) ≠ 0))
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ X.J) := ⟨by
    have h3 : (fun p : UA σ X.J × UA σ X.J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  haveI := hP.good.haar
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ X.J
  haveI : MeasurableMul (UA σ X.J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  have hH : (M.μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map M.μ e he he'
  obtain ⟨r₀, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame hcm hJ'
  obtain ⟨hr₀, hs₀⟩ := _root_.GlobalTheory.WittFrameSig.wittFrame_le_signature F E σ B n X r s hP.base hP.herm r₀ Xf Yf hW
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hKP.siegelSetUnitary F E σ hcm n ((1 : E) • X.J.map σ) hJ' r₀ Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas _ hH
  have hSm : MeasurableSet (GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K) := hcl.measurableSet
  have hS' : MeasurableSet (e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K) :=
    hSm.preimage he.measurable
  have hScov : ∀ g : UA σ X.J, ∃ γ ∈ ratU σ X.J,
      γ * g ∈ e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K := fun g => by
    obtain ⟨γ, hγ, s', hs', hgs⟩ := hcov (e g)
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hr : e.symm γ ∈ ratU σ X.J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
    refine ⟨(e.symm γ)⁻¹, inv_mem hr, ?_⟩
    show e ((e.symm γ)⁻¹ * g) ∈ GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, hgs, inv_mul_cancel_left]
    exact hs'
  have hI : ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
    rcases Nat.eq_zero_or_pos r₀ with h0 | h0
    · subst h0
      exact cone_zero F n d c
    · exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top F n r₀ d hc (by omega)
  set I := ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) with hIdef
  have key : ∀ (θ0 : UA σ X.J → ℂ) (A : ℝ), Continuous θ0 → (∀ γ ∈ ratU σ X.J, ∀ g, θ0 (γ * g) = θ0 g) →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ k ∈ K, ‖θ0 (e.symm (p * a * k))‖ ≤ A * ∏ i, t i ^ (Module.finrank ℚ F * d)) →
      IntegrableOn θ0 M.dom M.μ ∧ ∫ g in M.dom, ‖θ0 g‖ ∂M.μ ≤ (C₁ : ℝ) * max A 0 * I.toReal := by
    intro θ0 A hθc hθi hθb
    have hA : 0 ≤ max A 0 := le_max_right _ _
    have hle : ∫⁻ g in M.dom, ‖θ0 g‖ₑ ∂M.μ ≤ C₁ * (ENNReal.ofReal (max A 0) * I) := by
      calc ∫⁻ g in M.dom, ‖θ0 g‖ₑ ∂M.μ
          ≤ ∫⁻ g in e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K, ‖θ0 g‖ₑ ∂M.μ :=
            GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (ratU σ X.J) M.μ hP.good.dom hS' hScov
              hθc.enorm.measurable (fun γ hγ g => by rw [hθi γ hγ g])
        _ = ∫⁻ x in GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K, ‖θ0 (e.symm x)‖ₑ ∂(M.μ.map e) := by
            rw [setLIntegral_map (f := fun x => ‖θ0 (e.symm x)‖ₑ) hSm (hθc.comp he').enorm.measurable he.measurable]
            simp only [MulEquiv.symm_apply_apply]
        _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c, ENNReal.ofReal (max A 0 * ∏ i, t i ^ (Module.finrank ℚ F * d)) *
              ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) := by
            refine hC₁ (fun x => ‖θ0 (e.symm x)‖ₑ) _ (by fun_prop) fun q hq t ht a ha k hk => ?_
            have ht0 : ∀ i, 0 < t i := ht.1
            have hP0 : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
              Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal
              ((hθb q hq t ht a ha k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hP0))
        _ = C₁ * (ENNReal.ofReal (max A 0) * I) := by
            rw [hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hA, mul_assoc]
    refine ⟨⟨hθc.aestronglyMeasurable, hle.trans_lt (by finiteness)⟩, ?_⟩
    rw [integral_norm_eq_lintegral_enorm hθc.aestronglyMeasurable]
    refine (ENNReal.toReal_mono (by finiteness) hle).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.coe_toReal]
    ring

  have pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) := fun x Φ hΦ =>
    (IsUWeilPair.isUSplitting hP.weil).pres x Φ hΦ
  have thAdd : ∀ Φ ∈ schA F (Fin n × Fin d), ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ g h,
      theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := fun Φ hΦ Ψ hΨ g h => by
    simp only [theta, map_add (f := _)]
    exact thetaSum_add F (pres _ Φ hΦ) (pres _ Ψ hΨ)
  have thSmul : ∀ (a : ℂ) Φ g h, theta om (a • Φ) g h = a * theta om Φ g h := fun a Φ g h => by
    simp only [theta, map_smul]
    exact thetaSum_smul F a _
  have contθ : ∀ Φ ∈ schA F (Fin n × Fin d), ∀ h, Continuous fun g => theta om Φ g h := fun Φ hΦ h =>
    (hb.1 Φ hΦ).1.comp (continuous_id.prodMk continuous_const)
  have invθ : ∀ Φ ∈ schA F (Fin n × Fin d), ∀ h, ∀ γ ∈ ratU σ X.J, ∀ g, theta om Φ (γ * g) h = theta om Φ g h :=
    fun Φ hΦ h γ hγ g => by
      have := (hb.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) g h
      rwa [one_mul] at this
  have hPr : ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) := fun t ht =>
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  have boundA : ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (N : ℕ) (C : ℝ), ∀ h, ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ k ∈ K,
      ‖theta om Φ (e.symm (p * a * k)) h‖ ≤ C * (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      obtain ⟨N, C, T, hT⟩ :=
        _root_.GlobalTheory.SiegelTheta.theta_le_seminorm_height_torus F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj g hg
      exact ⟨N, C * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f, fun h p hp t htc a ha k hk => hT f h _ p hp t htc a ha k hk rfl⟩
    | zero => exact ⟨0, 0, fun h p _ t _ a _ k _ => by simp [theta, thetaSum]⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨N₁, C₁', h₁⟩ := ihx
      obtain ⟨N₂, C₂', h₂⟩ := ihy
      refine ⟨max N₁ N₂, max C₁' 0 + max C₂' 0, fun h p hp t htc a ha k hk => ?_⟩
      have e1 : (1 : ℝ) ≤ ht h := one_le_ht h
      have a1 : (ht h : ℝ) ^ N₁ ≤ (ht h : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ e1 (le_max_left _ _)
      have a2 : (ht h : ℝ) ^ N₂ ≤ (ht h : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ e1 (le_max_right _ _)
      have b1 := mul_le_max_mul (C := C₁') (by positivity) a1 (hPr t htc)
      have b2 := mul_le_max_mul (C := C₂') (by positivity) a2 (hPr t htc)
      rw [thAdd x hx y hy]
      calc _ ≤ ‖theta om x (e.symm (p * a * k)) h‖ + ‖theta om y (e.symm (p * a * k)) h‖ := norm_add_le _ _
        _ ≤ _ := add_le_add ((h₁ h p hp t htc a ha k hk).trans b1) ((h₂ h p hp t htc a ha k hk).trans b2)
        _ = _ := by ring
    | smul z x hx ih =>
      obtain ⟨N, C, h₁⟩ := ih
      refine ⟨N, ‖z‖ * C, fun h p hp t htc a ha k hk => ?_⟩
      rw [thSmul, norm_mul]
      calc ‖z‖ * ‖theta om x (e.symm (p * a * k)) h‖
          ≤ ‖z‖ * (C * (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d)) :=
            mul_le_mul_of_nonneg_left (h₁ h p hp t htc a ha k hk) (norm_nonneg _)
        _ = _ := by ring
  have hIr : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  refine ⟨fun Φ hΦ => ?_, fun φ hφ h => ?_⟩
  · obtain ⟨N, C, hC⟩ := boundA Φ hΦ
    have hk := fun h => key (fun g => theta om Φ g h) (C * (ht h : ℝ) ^ N) (contθ Φ hΦ h) (invθ Φ hΦ h)
      (fun p hp t htc a ha k hk => hC h p hp t htc a ha k hk)
    refine ⟨fun h => (hk h).1, (C₁ : ℝ) * max C 0 * I.toReal, N, fun h => (hk h).2.trans (le_of_eq ?_)⟩
    have hH : (0 : ℝ) ≤ (ht h : ℝ) ^ N := by positivity
    rw [← zero_mul ((ht h : ℝ) ^ N), ← max_mul_of_nonneg _ _ hH]
    ring_nf
  · obtain ⟨N, C, T, hT⟩ :=
      _root_.GlobalTheory.SiegelTheta.theta_le_seminorm_height_torus F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj φ hφ
    have memA : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
      Submodule.subset_span ⟨f, φ, hφ, rfl⟩
    have hint := fun f : SInf F (Fin n × Fin d) => key (fun g => theta om (pureA F f φ) g h)
      (C * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) (contθ _ (memA f) h) (invθ _ (memA f) h)
      (fun p hp t htc a ha k hk => hT f h _ p hp t htc a ha k hk rfl)
    have pAdd : ∀ f₁ f₂ : SInf F (Fin n × Fin d), pureA F (⇑(f₁ + f₂)) φ = pureA F f₁ φ + pureA F f₂ φ :=
      fun f₁ f₂ => funext fun x => by simp [pureA, add_mul]
    have pSmul : ∀ (z : ℂ) (f₁ : SInf F (Fin n × Fin d)), pureA F (⇑(z • f₁)) φ = z • pureA F f₁ φ :=
      fun z f₁ => funext fun x => by simp [pureA, mul_assoc]
    let L : SInf F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
      { toFun := fun f => M.I om (pureA F f φ) h
        map_add' := fun f₁ f₂ => by
          simp only [Model.I, pAdd, thAdd _ (memA f₁) _ (memA f₂)]
          exact integral_add (hint f₁).1 (hint f₂).1
        map_smul' := fun z f₁ => by
          simp only [Model.I, pSmul, thSmul, RingHom.id_apply, smul_eq_mul]
          exact integral_const_mul z _ }
    show Continuous L
    have hH : (0 : ℝ) ≤ (ht h : ℝ) ^ N := by positivity
    refine WithSeminorms.continuous_normedSpace_rng ℂ (schwartz_withSeminorms ℂ _ ℂ) L
      ⟨T, ⟨(C₁ : ℝ) * max C 0 * (ht h : ℝ) ^ N * I.toReal, by positivity⟩, fun f => ?_⟩
    have hq : 0 ≤ (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f := apply_nonneg _ _
    show ‖M.I om (pureA F f φ) h‖ ≤ _
    refine (norm_integral_le_integral_norm _).trans ((hint f).2.trans (le_of_eq ?_))
    show _ = ((C₁ : ℝ) * max C 0 * (ht h : ℝ) ^ N * I.toReal) * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f
    rw [show C * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N =
      C * ((T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) by ring,
      ← zero_mul ((T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N),
      ← max_mul_of_nonneg _ _ (mul_nonneg hq hH)]
    ring_nf

end GlobalTheory.ThKWeil

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEisensteinSiegelConvergence
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec)

namespace GlobalTheory.WeilEisConv

theorem weilEisensteinSiegelConvergence : GlobalTheory.Published.WeilEisensteinSiegelConvergence := by
  intro D n V hn hV ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.StdUnn.SchDatum.exists_datum D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ g : G D n, (ω g Φ).1 0 = swSec A V omh μ 𝓕 f (κ.symm g) := by
    intro g
    have h := hT (κ.symm g) f hf Φ hfΦ.symm
    have e : κ (κ.symm g) = g := κ.apply_symm_apply g
    rw [e] at h
    exact (congrFun h 0).trans (mixS_dblDec_zero A V ψ₀ μ 𝓕 _ 0)
  obtain ⟨a, ha⟩ := exists_isMaj A
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  obtain ⟨C, hC, h₁⟩ := GlobalTheory.SWAbsGrowth.norm_swSec_le hW hμ hf a ha
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hs : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hc.2.2.2, hc.2.2.2, star_star])
  have hP := GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ' hsk κ hκ
  have hG := GlobalTheory.StdUnn.chart_mem_GF_iff D A μ' hsk κ hκ
  have hb : (A.rank : ℝ) < (V.rank : ℝ) / 2 := by
    have : (2 * n : ℝ) < V.rank := by exact_mod_cast hV
    change (n : ℝ) < _
    linarith
  have hsum : Summable fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) =>
      (hgt A a (κ.symm (Subtype.val (q.out : GF D n))) : ℝ) ^ ((V.rank : ℝ) / 2) := by
    refine GlobalTheory.Eis.Conv.summable_hgt hc hs (GlobalTheory.Doubling.gram_hdbl A) (GlobalTheory.Doubling.isHermND_gram A)
      (GlobalTheory.Doubling.isCompact_Khat A a) hI (γ := fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) => κ.symm (Subtype.val (q.out : GF D n)))
      (fun q => (hG _).2 (by rw [MulEquiv.apply_symm_apply]; exact q.out.2)) (fun q q' h => ?_) hb
    have h' := (hP _).1 h
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    rw [← q.out_eq, ← q'.out_eq]
    exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨q'.out * q.out⁻¹, h'⟩, inv_mul_cancel_right _ _⟩
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hsum.mul_left C)
  simp only [GlobalTheory.Eis.term, mul_one]
  rw [key]
  exact h₁ _

end GlobalTheory.WeilEisConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsOfHeckeLbPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.BiextPairing

open GlobalTheory.UPel.HT

theorem lbIso_lbPow_hecke {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) (k : ℕ) :
    LBIso (lbPow P k) ((Hecke.lbPow P k).pull (𝟙 X)) := by
  have hQ : (Hecke.lbPow P k).IsLB := LB.isLB_linComb hP _ _
  have h₁ : LBIso (lbPow P k) (Hecke.lbPow P k) := by
    unfold Hecke.lbPow lbPow
    apply (GlobalTheory.PrimNorm.lbIso_iff hP _ _ _ _).2
    simp
  exact h₁.trans (LB.isLB_linComb hP _ _) hQ (pull_isLB hQ _) (GlobalTheory.DescendedPrincipal.lbIso_pull_id hQ).symm

theorem weilIs_of_hecke_lbPow {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {P : LB A.left} (hP : P.IsLB) (k : ℕ) {T : Over S} {X Y : T ⟶ A} {u : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A (Hecke.lbPow P k) 1 X Y u) : Out.WeilIs A P k X Y u := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hQ : (Hecke.lbPow P k).IsLB := LB.isLB_linComb hP _ _
  have := (GlobalTheory.weilIs_along_hom hG S A A (𝟙 _) P (Hecke.lbPow P k) k 1 T X Y u u hA hA hP hQ inferInstance
    (lbIso_lbPow_hecke hP k) (by simpa using h)).1
  simpa using this

end GlobalTheory.BiextPairing

namespace GlobalTheory.BiextPairing

open GlobalTheory.UPel.HT

end GlobalTheory.BiextPairing
end
end

