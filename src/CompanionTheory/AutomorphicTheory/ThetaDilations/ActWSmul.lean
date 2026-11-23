module

public import CompanionTheory.AutomorphicTheory.ThetaDilations.ContinuousPm
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0054
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0055
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0025

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

theorem actW_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (a : R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J h (a • X) = a • actW R σ J h X := funext fun i => Matrix.mulVec_smul _ a (X i)

set_option maxHeartbeats 1000000 in
theorem nu : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∃ (P : Subgroup (HA (AF F) σ (hypJ J))) (ν : Measure (HA (AF F) σ (hypJ J))) (S : ℤ → Set (HA (AF F) σ (hypJ J))) (ω : Set (AF F ⊗[F] E)ˣ) (Kc : ℝ≥0∞), (∀ h, h ∈ P ↔ ∃ a : (AF F ⊗[F] E)ˣ, actW (AF F) σ _ h (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ SFinite ν ∧ (∀ p ∈ P, ν.map (fun g => p * g) = ν) ∧ (∀ U ∈ 𝓝 (1 : HA (AF F) σ (hypJ J)), ν U ≠ 0) ∧ IsCompact ω ∧ Kc < ⊤ ∧ (∀ j, MeasurableSet (S j)) ∧ (∀ j : ℤ, ν (S j) ≤ Kc * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ))))) ∧ (∀ j : ℤ, ∀ p ∈ S j, p ∈ P ∧ ∃ c ∈ ω, actW (AF F) σ _ p (eOne _ (M + 1)) = ((τ (Multiplicative.ofAdd (j : ℝ)) * c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ ∀ᵐ p ∂ν, ∃ γ ∈ P, HA.mat (AF F) σ (hypJ J) γ ∈ HFin (AF F) σ (hypJ J) ∧ ∃ j, γ * p ∈ S j := by
  intro F E _ _ _ _ _ σ hcm M J hJ hfin τ hτ
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB 1 M
  have : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm M J hJ (AF F)
  obtain ⟨_, _, _, _, _, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm _ _ (_root_.GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND F E σ hcm M J hJ).1 (AF F)
  obtain ⟨-, a1, a2, -⟩ := hact 1
  letI : MeasurableSpace (AF F ⊗[F] E)ˣ := borel _
  have : BorelSpace (AF F ⊗[F] E)ˣ := ⟨rfl⟩
  have : SecondCountableTopology (AF F ⊗[F] E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : SecondCountableTopology (AF F ⊗[F] E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  obtain ⟨nn, ι, mm, c, hΨ, cn, ci, cm, cc, n0, nmul, -, hin, hmn, hmi, hline, hdec, rn, ri, rm⟩ :=
    par F E σ hcm M J hJ
  obtain ⟨⟨μ₁, hμ₁⟩, hex⟩ := _root_.GlobalTheory.CompanionTheory.SW.haar_fundamental_exist F E σ hcm M J hJ
  obtain ⟨-, ⟨𝓕, h𝓕m, h𝓕, hcov⟩, -⟩ := hex μ₁ hμ₁
  have : μ₁.IsHaarMeasure := hμ₁
  set μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E) := Measure.addHaar with hμW
  set μA : Measure (AF F) := Measure.addHaar with hμA
  set μT : Measure (AF F ⊗[F] E)ˣ := Measure.haar with hμT
  obtain ⟨χ, χc, χ1, χ2⟩ := _root_.GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi F E σ hcm τ hτ M μW μA inferInstance inferInstance
  obtain ⟨ω, hω, hid⟩ := _root_.GlobalTheory.CompanionTheory.SW.Fujisaki.units_decomp F E σ hcm τ hτ
  obtain ⟨⟨CW, hCW, hW⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.CocW.main F E σ hcm 1 M
  obtain ⟨⟨CA, hCA, hA⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact F
  obtain ⟨B, hBd⟩ := (hω.image χc).bddAbove
  set m := (μW.prod μA).prod (μ₁.prod (μT.withDensity fun s => (χ s : ℝ≥0∞))) with hm
  have hemb := hΨ.measurableEmbedding
  have hχm : Measurable fun s => (χ s : ℝ≥0∞) := (ENNReal.continuous_coe.comp χc).measurable
  let P : Subgroup (HA (AF F) σ (hypJ J)) :=
    { carrier := {h | ∃ a : (AF F ⊗[F] E)ˣ, actW (AF F) σ _ h (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1)}
      one_mem' := ⟨1, by rw [a1, Units.val_one, one_smul]⟩
      mul_mem' := by
        rintro g h ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨b * a, by rw [a2, hb, actW_smul, ha, Units.val_mul, mul_smul]⟩
      inv_mem' := by
        rintro g ⟨a, ha⟩
        refine ⟨a⁻¹, ?_⟩
        have := congrArg (fun X => ((a⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • actW (AF F) σ _ g⁻¹ X) ha
        simp only [← a2, inv_mul_cancel, a1, actW_smul, smul_smul, Units.inv_mul, one_smul] at this
        exact this.symm }
  have hωj : ∀ j : ℤ, IsCompact ((fun x => τ (Multiplicative.ofAdd (j : ℝ)) * x) '' ω) := fun j =>
    hω.image (continuous_const.mul continuous_id)
  refine ⟨P, m.map fun z => nn z.1 * ι z.2.1 * mm z.2.2,
    fun j => (fun z => nn z.1 * ι z.2.1 * mm z.2.2) '' ((CW ×ˢ CA) ×ˢ (𝓕 ×ˢ
      ((fun x => τ (Multiplicative.ofAdd (j : ℝ)) * x) '' ω))), ω, μW CW * μA CA * (μ₁ 𝓕 * (B * μT ω)),
    fun _ => Iff.rfl, inferInstance, ?_, fun U hU h0 => ?_, hω, ?_, fun j => ?_, fun j => ?_, ?_, ?_⟩
  · rintro g ⟨a, ha⟩
    obtain ⟨p, u, rfl⟩ := hdec g a ha
    refine _root_.GlobalTheory.CompanionTheory.Adelic.tripleProduct_map_leftInvariant _ _ _ _ (μW.prod μA) μ₁ μT nn ι mm χ cn.measurable ci.measurable cm.measurable
      χc.measurable (fun p => ⟨fun x => (p.1 + x.1, p.2 + x.2 + c p.1 x.1), ?_, fun x => nmul _ _ _ _⟩)
      (fun u => ⟨Prod.map (actW (AF F) σ J u) id, ?_, fun x => hin u _ _⟩)
      (fun t => ⟨_, ?_, χ1 t, fun x => hmn t _ _⟩) hmi p u a
    · refine (measurePreserving_add_left μW p.1).skew_product (g := fun w y => p.2 + y + c p.1 w) ?_
        (ae_of_all _ fun w => ?_)
      · exact ((continuous_const.add continuous_snd).add (cc.comp (continuous_const.prodMk continuous_fst))).measurable
      · simpa only [add_right_comm p.2] using map_add_left_eq_self μA (p.2 + c p.1 w)
    · obtain ⟨-, -, -, -, -, hact'⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm M J hJ (AF F)
      exact MeasurePreserving.prod ⟨((hact' 1).1.comp (continuous_const.prodMk continuous_id)).measurable,
        _root_.GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq F E σ hcm M J hJ μW inferInstance u⟩ (MeasurePreserving.id μA)
    · exact Continuous.measurable (by fun_prop)
  · have : (μT.withDensity fun s => (χ s : ℝ≥0∞)).IsOpenPosMeasure :=
      (withDensity_absolutelyContinuous' hχm.aemeasurable (ae_of_all _ fun s => by
        have : χ s * χ s⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        exact_mod_cast left_ne_zero_of_mul_eq_one this)).isOpenPosMeasure
    have h1 := measure_mono_null interior_subset h0
    rw [hemb.map_apply] at h1
    refine (isOpen_interior.preimage hΨ.continuous).measure_ne_zero m ⟨((0, 0), 1, 1), ?_⟩ h1
    show nn (0, 0) * ι 1 * mm 1 ∈ interior U
    rw [n0, map_one, map_one, one_mul, one_mul]
    exact mem_interior_iff_mem_nhds.2 hU
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hCW.measure_lt_top hCA.measure_lt_top)
      (ENNReal.mul_lt_top ((hfin.2 μ₁ hμ₁).2 𝓕 h𝓕) (ENNReal.mul_lt_top ENNReal.coe_lt_top hω.measure_lt_top))
  · exact hemb.measurableSet_image.2
      ((hCW.measurableSet.prod hCA.measurableSet).prod (h𝓕m.prod (hωj j).measurableSet))
  · rw [hemb.map_apply, hemb.injective.preimage_image, hm, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
      withDensity_apply _ (hωj j).measurableSet, mul_assoc (μW CW * μA CA), mul_assoc (μ₁ 𝓕), ← χ2,
      ENNReal.ofReal_coe_nnreal]
    gcongr
    calc _ ≤ ∫⁻ _ in (fun x => τ (Multiplicative.ofAdd (j : ℝ)) * x) '' ω,
          ((χ (τ (Multiplicative.ofAdd (j : ℝ))) * B : ℝ≥0) : ℝ≥0∞) ∂μT := by
          refine setLIntegral_mono' (hωj j).measurableSet ?_
          rintro _ ⟨x, hx, rfl⟩
          rw [map_mul]
          exact_mod_cast mul_le_mul_right (hBd ⟨x, hx, rfl⟩) _
      _ = _ := by
          rw [setLIntegral_const, Set.image_mul_left, measure_preimage_mul, ENNReal.coe_mul]; ring
  · rintro j _ ⟨⟨p, u, _⟩, ⟨-, -, x, hx, rfl⟩, rfl⟩
    exact ⟨⟨_, hline p u _⟩, x, hx, hline p u _⟩
  · refine hemb.ae_map_iff.2 (ae_of_all _ fun ⟨⟨w, t⟩, u, a⟩ => ?_)
    obtain ⟨l, a', x, j, hl, hx, rfl⟩ := hid a
    obtain ⟨γ, hγ, hγu⟩ := hcov u
    obtain ⟨w₁, t₁, e1⟩ : ∃ w₁ t₁, mm a'⁻¹ * nn (w, t) = nn (w₁, t₁) * mm a'⁻¹ := ⟨_, _, hmn _ _ _⟩
    obtain ⟨X, hX⟩ := hW (actW (AF F) σ J γ w₁)
    obtain ⟨r, hr⟩ := hA (t₁ + c (ratTup (AF F) (-X)) (actW (AF F) σ J γ w₁))
    refine ⟨nn (ratTup (AF F) (-X), algebraMap F (AF F) (-r)) * ι γ * mm a'⁻¹, ⟨_, hline _ _ _⟩,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (rn _ _) (ri _ hγ)) (rm l⁻¹ _ (Units.inv_eq_of_mul_eq_one_right
        (by rw [hl, ← map_mul, Units.mul_inv, map_one]))), j,
      ((ratTup (AF F) (-X) + actW (AF F) σ J γ w₁, algebraMap F (AF F) (-r) + t₁ +
        c (ratTup (AF F) (-X)) (actW (AF F) σ J γ w₁)), γ * u, τ (Multiplicative.ofAdd (j : ℝ)) * x),
      ⟨⟨?_, ?_⟩, hγu, x, hx, rfl⟩, ?_⟩
    · have e : ratTup (F := F) (AF F) (-X) = -ratTup (AF F) X := funext fun a => funext fun i => map_neg _ _
      rwa [e, neg_add_eq_sub]
    · rwa [map_neg, add_assoc, neg_add_eq_sub]
    · show nn _ * ι (γ * u) * mm _ = _ * (nn (w, t) * ι u * mm _)
      rw [← nmul, map_mul ι, mul_assoc a', map_mul mm a']
      simp only [← mul_assoc]
      rw [mul_assoc _ (mm a'⁻¹) (nn (w, t)), e1, ← mul_assoc, mul_assoc _ (ι γ) (nn (w₁, t₁)), hin, ← mul_assoc,
        mul_assoc _ (mm a'⁻¹) (ι u), hmi, ← mul_assoc, mul_assoc _ (mm a'⁻¹) (mm a'), ← map_mul mm, inv_mul_cancel,
        map_one, mul_one]

end CompanionTheory.PlacePermOperatorBicommutantSpan
