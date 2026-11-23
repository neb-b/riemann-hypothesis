module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.FormalDegreeBessel.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedIwasawaIntegralSmallBallAsymptotics
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem lintegral_triple_eq {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ₁ : Measure α) (μ₂ : Measure β) (μ₃ : Measure γ) [SFinite μ₂] [SFinite μ₃]
    (δ : β → ENNReal) (hδ : Measurable δ) (P : α × β × γ → ENNReal) (hP : Measurable P) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, P (u, m, k) ∂μ₃ ∂μ₂ ∂μ₁ = ∫⁻ x, δ x.2.1 * P x ∂(μ₁.prod (μ₂.prod μ₃)) := by
  symm
  rw [lintegral_prod (fun x => δ x.2.1 * P x)
    (show Measurable fun x : α × β × γ => δ x.2.1 * P x from (hδ.comp measurable_snd.fst).mul hP).aemeasurable]
  refine lintegral_congr fun u => ?_
  rw [lintegral_prod (fun y => δ y.1 * P (u, y))
    (show Measurable fun y : β × γ => δ y.1 * P (u, y) from
      (hδ.comp measurable_fst).mul (hP.comp measurable_prodMk_left)).aemeasurable]
  refine lintegral_congr fun m => ?_
  exact lintegral_const_mul (δ m)
    (show Measurable fun k : γ => P (u, m, k) from hP.comp (measurable_prodMk_left.comp measurable_prodMk_left))

theorem IsCut.sigmaFinite {n d : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)}
    {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsCut ε S E) {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : IsGaugeSub S d μ) : SigmaFinite μ := by
  obtain ⟨A, hA, hON, hspan, rfl⟩ := h
  exact (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hON hspan μ hμ).1

theorem localised_iwasawa_asymptotics : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsON EL → (∀ v, gau EN EM EK EL v = 0 → v = 0) → volume {v | gau EN EM EK EL v ≤ 1} ≠ ⊤ → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub (flagN ε W) dN μN → IsGaugeSub (flagM ε W) dM μM → IsGaugeSub (maxK ε) dK μK → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → Filter.Tendsto (fun r : ℝ => (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) * (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  intro n ε a j W hW dN dM dK dL EN EM EK EL hN hM hK hL hgau hvol μN μM μK hμN hμM hμK
  have := hN.sigmaFinite hμN
  have := hM.sigmaFinite hμM
  have := hK.sigmaFinite hμK
  obtain ⟨C, hC, hCη⟩ := _root_.GlobalTheory.IwSand.gau_sandwich n ε _ _ _ dN dM dK dL EN EM EK EL hN hM hK hL hgau
  obtain ⟨t₀, ht₀, hasym⟩ :=
    _root_.GlobalTheory.IwConstBox.prod_gauge_body n ε _ _ _ dN dM dK dL EN EM EK EL hN hM hK hgau μN μM μK hμN hμM hμK
  obtain ⟨t₁, ht₁, h₁⟩ := hCη 1 one_pos
  obtain ⟨ts, hts, hts0, hts1⟩ : ∃ ts : ℝ, 0 < ts ∧ ts ≤ t₀ ∧ ts ≤ t₁ :=
    ⟨min t₀ t₁, lt_min ht₀ ht₁, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨ρ₀, hρ₀, hball⟩ := _root_.GlobalTheory.IwNear.near n ε a j W hW ts hts
  obtain ⟨hdltm, -, hdlt⟩ := GlobalTheory.T.leviFactorInverseModulus_properties n ε a j W

  have hae : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.1 ∈ flagN ε W ∧ x.2.1 ∈ flagM ε W ∧ x.2.2 ∈ maxK ε := by
    have h1 : (μN.prod (μM.prod μK)) ((flagN ε W)ᶜ ×ˢ Set.univ) = 0 := by
      rw [Measure.prod_prod, hμN.1, zero_mul]
    have h2 : (μN.prod (μM.prod μK)) (Set.univ ×ˢ ((flagM ε W)ᶜ ×ˢ Set.univ)) = 0 := by
      rw [Measure.prod_prod, Measure.prod_prod, hμM.1, zero_mul, mul_zero]
    have h3 : (μN.prod (μM.prod μK)) (Set.univ ×ˢ (Set.univ ×ˢ (maxK ε)ᶜ)) = 0 := by
      rw [Measure.prod_prod, Measure.prod_prod, hμK.1, mul_zero, mul_zero]
    have e1 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.1 ∈ flagN ε W := by
      rw [ae_iff]
      exact measure_mono_null (fun x hx => Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩) h1
    have e2 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.2.1 ∈ flagM ε W := by
      rw [ae_iff]
      exact measure_mono_null
        (fun x hx => Set.mem_prod.2 ⟨Set.mem_univ _, Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩⟩) h2
    have e3 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.2.2 ∈ maxK ε := by
      rw [ae_iff]
      exact measure_mono_null
        (fun x hx => Set.mem_prod.2 ⟨Set.mem_univ _, Set.mem_prod.2 ⟨Set.mem_univ _, hx⟩⟩) h3
    filter_upwards [e1, e2, e3] with x hx1 hx2 hx3
    exact ⟨hx1, hx2, hx3⟩
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρρ₀ => ?_⟩
  have hPmeas : ∀ r : ℝ, Measurable fun x : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε × Formalism.REAL.UJ ε =>
      (hsBall ε r).indicator (1 : Formalism.REAL.UJ ε → ENNReal) (x.1 * x.2.1 * x.2.2) *
        (slab ε EL ρ r).indicator 1 x.2.2 := by
    intro r
    exact ((measurable_one.indicator (measurableSet_hsBall ε r)).comp
      ((measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd)).mul
      ((measurable_one.indicator (measurableSet_slab ε EL ρ r)).comp measurable_snd.snd)

  have hF : ∀ r : ℝ, (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) *
      (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) =
      ∫⁻ x, dlt j W x.2.1 * ((hsBall ε r).indicator 1 (x.1 * x.2.1 * x.2.2) *
        (slab ε EL ρ r).indicator 1 x.2.2) ∂(μN.prod (μM.prod μK)) := fun r =>
    GlobalTheory.IwConst.lintegral_triple_eq μN μM μK (dlt j W) hdltm _ (hPmeas r)
  have hc := continuous_nrm_uMat ε
  apply GlobalTheory.T.tendsto_small_ball_density_of_squeeze _ (dN + (dM + dK)) _ hvol
  intro η hη
  obtain ⟨t₂, ht₂, h₂⟩ := hCη η hη
  obtain ⟨t₃, ht₃, h₃⟩ := hdlt η hη
  obtain ⟨t, ht, htts, htρ, htt₂, htt₃⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ts ∧ t ≤ ρ ∧ t ≤ t₂ ∧ t ≤ t₃ :=
    ⟨min (min ts ρ) (min t₂ t₃), lt_min (lt_min hts hρ) (lt_min ht₂ ht₃),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hBmeas : ∀ s : ℝ, MeasurableSet {x : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε × Formalism.REAL.UJ ε |
      (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧
        gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ s} := by
    intro s
    refine measurableSet_setOfPred.2
      (((measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_fst) measurable_const)).and
      ((measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_snd.fst) measurable_const)).and
        (measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_snd.snd) measurable_const)))).and
      (measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const)))
    exact (continuous_gau EN EM EK EL).measurable.comp
      (((continuous_crd_uMat ε EN).measurable.comp measurable_fst).prodMk
        (((continuous_crd_uMat ε EM).measurable.comp measurable_snd.fst).prodMk
          ((continuous_crd_uMat ε EK).measurable.comp measurable_snd.snd)))
  refine ⟨fun s => (μN.prod (μM.prod μK)) {x |
      (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧
        gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ s},
    hasym t ht (htts.trans hts0), ?_⟩
  have hr₁ : 0 < min ρ₀ (t / (2 * C)) := lt_min hρ₀ (div_pos ht (by positivity))
  filter_upwards [Ioo_mem_nhdsGT hr₁] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hrρ₀ : r ≤ ρ₀ := (lt_of_lt_of_le hr1 (min_le_left _ _)).le
  have hrC : 2 * C * r < t := by
    have h := lt_of_lt_of_le hr1 (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    linarith
  have hη1 : (0 : ℝ) < 1 + η := by linarith
  rw [hF r]
  constructor
  ·
    rw [← lintegral_indicator_one (hBmeas _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with x hx
    obtain ⟨hxN, hxM, hxK⟩ := hx
    rw [Set.indicator_apply]
    split_ifs with hB
    · obtain ⟨⟨hu, hm, hk⟩, hγ⟩ := hB
      obtain ⟨-, hσγ, -, -, -⟩ := h₂ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu htt₂)
        (lt_of_lt_of_le hm htt₂) (lt_of_lt_of_le hk htt₂) _ _ rfl rfl
      have hσ : max (nrm (uMat (x.1 * x.2.1 * x.2.2) - 1)) (len (crd EL (uMat x.2.2 - 1))) ≤ r := by
        refine hσγ.trans ?_
        calc (1 + η) * gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
              crd EK (uMat x.2.2 - 1)) ≤ (1 + η) * (r / (1 + η)) :=
              mul_le_mul_of_nonneg_left hγ hη1.le
          _ = r := by field_simp
      have hmem1 : x.1 * x.2.1 * x.2.2 ∈ hsBall ε r :=
        ((le_max_left _ _).trans hσ : nrm (uMat (x.1 * x.2.1 * x.2.2) - 1) ≤ r)
      have hmem2 : x.2.2 ∈ slab ε EL ρ r :=
        (⟨lt_of_lt_of_le hk htρ, (le_max_right _ _).trans hσ⟩ :
          nrm (uMat x.2.2 - 1) < ρ ∧ len (crd EL (uMat x.2.2 - 1)) ≤ r)
      rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2]
      simp only [Pi.one_apply, mul_one]
      exact (h₃ x.2.1 hxM (lt_of_lt_of_le hm htt₃)).2
    · exact bot_le
  ·
    rw [← lintegral_indicator_one (hBmeas _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with x hx
    obtain ⟨hxN, hxM, hxK⟩ := hx
    by_cases hA : x.1 * x.2.1 * x.2.2 ∈ hsBall ε r
    swap
    · simp [Set.indicator_apply, hA]
    by_cases hS : x.2.2 ∈ slab ε EL ρ r
    swap
    · simp [Set.indicator_apply, hS]
    rw [Set.indicator_of_mem hA, Set.indicator_of_mem hS]
    simp only [Pi.one_apply, mul_one]
    have hA' : nrm (uMat (x.1 * x.2.1 * x.2.2) - 1) ≤ r := hA
    obtain ⟨hkρ, hL⟩ := (hS : nrm (uMat x.2.2 - 1) < ρ ∧ len (crd EL (uMat x.2.2 - 1)) ≤ r)
    obtain ⟨hu1, hm1, hk1⟩ :=
      hball x.1 hxN x.2.1 hxM x.2.2 (hA'.trans hrρ₀) (lt_of_lt_of_le hkρ hρρ₀)
    have hσ : max (nrm (uMat (x.1 * x.2.1 * x.2.2) - 1)) (len (crd EL (uMat x.2.2 - 1))) ≤ r :=
      max_le hA' hL
    obtain ⟨hγ1, -, hCu, hCm, hCk⟩ := h₁ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu1 hts1)
      (lt_of_lt_of_le hm1 hts1) (lt_of_lt_of_le hk1 hts1) _ _ rfl rfl
    have hγ2 : gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
        crd EK (uMat x.2.2 - 1)) ≤ 2 * r := by
      have := mul_le_mul_of_nonneg_left hσ (by norm_num : (0 : ℝ) ≤ 1 + 1)
      linarith
    have hCγ := mul_le_mul_of_nonneg_left hγ2 hC.le
    have hu : nrm (uMat x.1 - 1) < t := by linarith
    have hm : nrm (uMat x.2.1 - 1) < t := by linarith
    have hk : nrm (uMat x.2.2 - 1) < t := by linarith
    obtain ⟨hγη, -, -, -, -⟩ := h₂ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu htt₂)
      (lt_of_lt_of_le hm htt₂) (lt_of_lt_of_le hk htt₂) _ _ rfl rfl
    have hγ : gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
        crd EK (uMat x.2.2 - 1)) ≤ (1 + η) * r :=
      hγη.trans (mul_le_mul_of_nonneg_left hσ hη1.le)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [if_pos ⟨⟨hu, hm, hk⟩, hγ⟩, Pi.one_apply, mul_one]
    exact (h₃ x.2.1 hxM (lt_of_lt_of_le hm htt₃)).1

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTypeVectorsSpanFixedLatticeVectorModLevel
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.SpanMoved

theorem natSmul_mem (I : AutInst) (T : Submodule (IntAf I.F I.E) (VA I)) (n : ℕ) {t : VA I} (ht : t ∈ T) :
    (n : I.E ⊗[I.F] Af I.F) • t ∈ T := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem ht n

def satG (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) :
    Submodule (IntAf I.F I.E) (VA I) where
  carrier := {x | ∃ N : ℕ, Nat.Coprime N g ∧ (N : I.E ⊗[I.F] Af I.F) • x ∈ T}
  zero_mem' := ⟨1, Nat.coprime_one_left g, by simp⟩
  add_mem' := by
    rintro x y ⟨N, hN, hx⟩ ⟨M, hM, hy⟩
    refine ⟨N * M, Nat.coprime_mul_iff_left.2 ⟨hN, hM⟩, ?_⟩
    have e : ((N * M : ℕ) : I.E ⊗[I.F] Af I.F) • (x + y) =
        (M : I.E ⊗[I.F] Af I.F) • ((N : I.E ⊗[I.F] Af I.F) • x) +
          (N : I.E ⊗[I.F] Af I.F) • ((M : I.E ⊗[I.F] Af I.F) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (M : I.E ⊗[I.F] Af I.F)]
    rw [e]
    exact add_mem (natSmul_mem I T M hx) (natSmul_mem I T N hy)
  smul_mem' := by
    rintro r x ⟨N, hN, hx⟩
    refine ⟨N, hN, ?_⟩
    have e : (N : I.E ⊗[I.F] Af I.F) • (r • x) = r • ((N : I.E ⊗[I.F] Af I.F) • x) :=
      smul_comm _ _ _
    rw [e]
    exact T.smul_mem r hx

theorem mem_of_coprime_smul (I : AutInst) (g n : ℕ) (hn : Nat.Coprime n g)
    (T : Submodule (IntAf I.F I.E) (VA I)) (hT : mL I g ≤ T) {v : VA I} (hv : v ∈ I.Lf)
    (hnv : (n : I.E ⊗[I.F] Af I.F) • v ∈ T) : v ∈ T := by
  have hg : (g : ℤ) • v ∈ T := by
    have h : (g : I.E ⊗[I.F] Af I.F) • v ∈ mL I g := Submodule.subset_span ⟨v, hv, rfl⟩
    rw [Nat.cast_smul_eq_nsmul] at h
    rw [natCast_zsmul]
    exact hT h
  have hn' : (n : ℤ) • v ∈ T := by
    rw [Nat.cast_smul_eq_nsmul] at hnv
    rw [natCast_zsmul]
    exact hnv

  have key : v = Nat.gcdA n g • ((n : ℤ) • v) + Nat.gcdB n g • ((g : ℤ) • v) := by
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (Nat.gcdA n g), mul_comm (Nat.gcdB n g),
      ← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hn, Nat.cast_one, one_smul]
  rw [key]
  exact add_mem (zsmul_mem hn' _) (zsmul_mem hg _)

private theorem mem_satG_iff_exists_coprime_smul_mem (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) (x : VA I) :
    x ∈ satG I g T ↔ ∃ N : ℕ, Nat.Coprime N g ∧ (N : I.E ⊗[I.F] Af I.F) • x ∈ T := Iff.rfl

private theorem mem_satG_of_mem (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) {x : VA I}
    (hx : x ∈ T) : x ∈ satG I g T :=
  (mem_satG_iff_exists_coprime_smul_mem I g T x).2 ⟨1, Nat.coprime_one_left g, by rw [Nat.cast_one, one_smul]; exact hx⟩

private theorem map_mem_mL_of_preserves_Lf (I : AutInst) (g : ℕ) (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I)
    (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf) {x : VA I} (hx : x ∈ mL I g) : φ x ∈ mL I g := by
  have h : mL I g ≤ (mL I g).comap (φ.restrictScalars (IntAf I.F I.E)) := by
    conv_lhs => unfold mL
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show φ ((g : I.E ⊗[I.F] Af I.F) • y) ∈ mL I g
    rw [φ.map_smul]
    exact Submodule.subset_span ⟨φ y, hφ y hy, rfl⟩
  exact h hx

theorem map_mem_satG (I : AutInst) (g : ℕ)
    (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I) (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf) (S S' : Set (VA I))
    (hS : ∀ s ∈ S, φ s ∈ satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g))
    {w : VA I} (hw : InMod I g S w) :
    φ w ∈ satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g) := by
  have hle : Submodule.span (IntAf I.F I.E) S ⊔ mL I g ≤
      (satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g)).comap (φ.restrictScalars (IntAf I.F I.E)) := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro s hs
      exact hS s hs
    · intro x hx
      exact mem_satG_of_mem I g _ (Submodule.mem_sup_right (map_mem_mL_of_preserves_Lf I g φ hφ hx))
  exact hle hw

theorem map_inAt (I : AutInst) (g : ℕ)
    (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I) (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf)
    (T : Submodule (IntAf I.F I.E) (VA I)) (hT : mL I g ≤ T) {d : VA I} (hd : InAt I g g d) :
    φ d ∈ satG I g T := by
  obtain ⟨N, hN, hNd⟩ := hd
  refine (mem_satG_iff_exists_coprime_smul_mem I g T _).2 ⟨N, hN, ?_⟩
  rw [← φ.map_smul]
  exact hT (map_mem_mL_of_preserves_Lf I g φ hφ hNd)

theorem span_moved : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] → (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) → (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) → p (incl X.B.I (X.zR u)) = 0 → ∀ v ∈ X.B.I.Lf, p v = v → InMod X.B.I X.B.g (Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) ∪ Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))) v := by
  intro D X u c p hc hpL hef hzR v hv hpv
  have hcg : Nat.Coprime c X.B.g := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hc, Nat.gcd_one_left]
  let V := X.B.I.fmat (X.xu u)

  let ψ : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I :=
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (p ∘ₗ Matrix.mulVecLin V)
  have hψ : ∀ y, ψ y = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (V *ᵥ y) := fun y => rfl
  have hVVi : ∀ y, V *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec]
    simp [V, Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv]
  have hK : ∀ y, y ∈ X.B.I.Lf ↔ V *ᵥ y ∈ X.B.I.Lf := X.xu_K u
  have hViL : ∀ y ∈ X.B.I.Lf, X.B.I.fmat (X.xu u)⁻¹ *ᵥ y ∈ X.B.I.Lf := fun y hy =>
    (hK _).2 (by rw [hVVi]; exact hy)
  have hψL : ∀ y ∈ X.B.I.Lf, ψ y ∈ X.B.I.Lf := fun y hy => by
    rw [hψ]
    exact hpL _ ((hK y).1 hy)
  let S' : Set (VA X.B.I) :=
    Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) ∪
      Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))
  let T := Submodule.span (IntAf X.B.I.F X.B.I.E) S' ⊔ mL X.B.I X.B.g
  have hT : mL X.B.I X.B.g ≤ T := le_sup_right

  have hS : ∀ s ∈ Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd,
      ψ s ∈ satG X.B.I X.B.g T := by
    rintro s ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | hs) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    ·
      have hfix : V *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := (X.xu_fix u a).1
      have h0 : ψ (incl X.B.I (X.eR a)) = 0 := by rw [hψ, hfix, (hef a).1, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.e0 a - incl X.B.I (X.eR a)) := (X.basisApprox a).1
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rwa [map_sub, h0, sub_zero] at h
    ·
      have hfix : V *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := (X.xu_fix u a).2
      have h0 : ψ (incl X.B.I (X.fR a)) = 0 := by rw [hψ, hfix, (hef a).2, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.f0 a - incl X.B.I (X.fR a)) := (X.basisApprox a).2
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rwa [map_sub, h0, sub_zero] at h
    ·
      rw [Set.mem_singleton_iff] at hs
      subst hs
      have h0 : ψ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) = 0 := by
        rw [hψ, hVVi, hzR, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) :=
        X.xu_z u
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rw [map_sub, h0, zero_sub] at h
      simpa using neg_mem h
    · exact mem_satG_of_mem X.B.I X.B.g T
        (Submodule.mem_sup_left (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
    · exact mem_satG_of_mem X.B.I X.B.g T
        (Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))

  have hmap := map_mem_satG X.B.I X.B.g ψ hψL _ S' hS (X.latticeSpan _ (hViL v hv))
  obtain ⟨N, hN, hNv⟩ := (mem_satG_iff_exists_coprime_smul_mem _ _ _ _).1 hmap
  rw [hψ, hVVi, hpv, smul_smul, ← Nat.cast_mul] at hNv
  exact mem_of_coprime_smul X.B.I X.B.g (N * c) (Nat.Coprime.mul_left hN hcg) T hT hv hNv

end GlobalTheory.St.G.SpanMoved
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopMinorAndGramNumberLeMajorantLengths
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YBound

open GlobalTheory.Amp.GramFlag (eucl_eq)

theorem det_upper {r : ℕ} (x : UT r → ℂ) : (upper x).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [upper]
  · intro a b h
    have h' : b < a := h
    simp [upper, not_lt.2 h'.le, h'.ne']

theorem det_change {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) {j : ℕ} (y : Fin j → V₁) (y' : Fin j → V₂) (U U' : Matrix (Fin j) (Fin j) ℂ)
    (hU : U.det = 1) (hU' : U'.det = 1) :
    (Matrix.of fun a b => B (∑ c, U c a • y c) (∑ c, U' c b • y' c)).det =
      (Matrix.of fun a b => B (y a) (y' b)).det := by
  have e : (Matrix.of fun a b => B (∑ c, U c a • y c) (∑ c, U' c b • y' c)) =
      Uᵀ * (Matrix.of fun a b => B (y a) (y' b)) * (U'ᴴ)ᵀ := by
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.of_apply, Matrix.mul_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, Matrix.transpose_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    first
      | (refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; simp; ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; simp; ring)
  rw [e]
  simp [Matrix.det_mul, Matrix.det_conjTranspose, hU, hU']

theorem prod_le_pow' {n : ℕ} (f : Fin n → ℝ) (R : ℝ) (h0 : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ R) :
    ∏ i, f i ≤ R ^ n := by
  calc _ ≤ ∏ _a : Fin n, R := Finset.prod_le_prod₀ (fun i _ => h0 i) fun i _ => h i
    _ = _ := by simp

def formE {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) →ₗ⋆[ℂ] ℂ :=
  (innerₛₗ ℂ).flip ∘ₗ Matrix.toEuclideanLin H

theorem formE_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    formE H (WithLp.toLp 2 v) (WithLp.toLp 2 w) = herm H v w := by
  show ⟪(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)), WithLp.toLp 2 (H *ᵥ v)⟫_ℂ = _
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, herm]

theorem formE_le {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ * H = 1) (v w : EuclideanSpace ℂ (Fin n)) :
    ‖formE H v w‖ ≤ ‖v‖ * ‖w‖ := by
  have h1 : ‖Matrix.toEuclideanLin H v‖ = ‖v‖ := by
    have : ⟪Matrix.toEuclideanLin H v, Matrix.toEuclideanLin H v⟫_ℂ = ⟪v, v⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      congr 1
      ext i
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hH]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), this, ← norm_eq_sqrt_re_inner]
  show ‖⟪w, Matrix.toEuclideanLin H v⟫_ℂ‖ ≤ _
  rw [mul_comm, ← h1]
  exact norm_inner_le_norm _ _

theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have h : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem gramProj_le {n r : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin r → Fin n → ℂ)
    (U : Matrix (Fin r) (Fin r) ℂ) (hU : U.det = 1) (R : ℝ) (hR : ∀ a, eucl (∑ b, U b a • v b) ≤ R) :
    gramProj P v ≤ R ^ r := by
  have h := (Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.gramHadamard (EuclideanSpace ℂ (Fin n)) r
    (fun a => ∑ b, U b a • P.starProjection (WithLp.toLp 2 (v b)))).2 R (fun a => by
      refine le_trans ?_ (hR a)
      rw [eucl_eq, WithLp.toLp_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← map_smul, ← map_sum, WithLp.toLp_smul]
      exact P.norm_starProjection_apply_le _)
  have e : ∀ w : Fin r → EuclideanSpace ℂ (Fin n), (Matrix.gram ℂ w).det =
      (Matrix.of fun a b => (innerₛₗ ℂ).flip (w a) (w b)).det := by
    intro w
    rw [← Matrix.det_transpose]
    rfl
  unfold gramProj
  rw [e, det_change _ _ _ U U hU hU, ← e] at h
  exact h

theorem dr_y_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), TwoFl k r z z' γ → ∀ x ∈ GG k r, Dr k r z z' γ ≤ Sg k r z' x ^ r * Sg k r z (γ * x) ^ r ∧ 0 ≤ Yv k r z z' γ x ∧ Yv k r z z' γ x ≤ Sg k r z (γ * x) ^ r / Dr k r z z' γ := by
  intro k r z z' γ hT x hx
  obtain ⟨hz, hz', -, -, hg, -, -⟩ := hT
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hG := uHGroup _ _ hH
  have hgx : γ * x ∈ GG k r := hG.2.1 _ hg _ hx
  obtain ⟨u', hu', -⟩ := GramFlag.gramSchmidt_lengths k r z' x hx
  obtain ⟨u, hu, -⟩ := GramFlag.gramSchmidt_lengths k r z _ hgx
  have h1 : ∀ a, eucl (∑ b, upper u b a • ((γ * x)⁻¹ *ᵥ bvec (eI k r b))) ≤ Sg k r z (γ * x) := fun a => by
    rw [(hu a).1]; exact (((LInv.lengths_basic k r z hz).2.2 _).2.1 _).2
  have h2 : ∀ a, eucl (∑ b, upper u' b a • (x⁻¹ *ᵥ bvec (eI k r b))) ≤ Sg k r z' x := fun a => by
    rw [(hu' a).1]; exact (((LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2
  have hD0 : 0 ≤ Dr k r z z' γ := norm_nonneg _
  refine ⟨?_, div_nonneg (Real.sqrt_nonneg _) hD0, ?_⟩
  · have h := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.wedgeHadamard _ _ (formE (Hpk k r))
      (formE_le _ (by rw [(hpkFacts k r).1, (hpkFacts k r).2.1])) r
      (fun a => ∑ b, upper u' b a • WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r b)))
      (fun a => ∑ b, upper u b a • WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r b)))
    rw [det_change _ _ _ _ _ (det_upper u') (det_upper u)] at h
    have e : Dmin k r z z' γ ⟨r, by omega⟩ = (Matrix.of fun a b : Fin r => formE (Hpk k r)
        (WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r a))) (WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r b)))).det := by
      unfold Dmin
      rw [← Matrix.det_transpose]
      congr 1
      ext a b
      have ha := a.2
      have hb := b.2
      simp only at ha hb
      simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Formalism.QuantumDeterminants.Zhat, fvec, Matrix.of_apply, formE_apply]
      rw [dite_eq_left (by simpa using ha), dite_eq_left (by simpa using hb),
        ← herm_mulVec (hG.2.2 _ hgx).2, Matrix.mulVec_mulVec, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_mul_cancel_right _ _ (hG.2.2 _ hg).1]
      rfl
    unfold Dr
    rw [e]
    refine h.trans (mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_)
    · refine prod_le_pow' _ _ (fun _ => norm_nonneg _) fun a => le_trans (le_of_eq ?_) (h2 a)
      rw [eucl_eq, WithLp.toLp_sum]; rfl
    · refine prod_le_pow' _ _ (fun _ => norm_nonneg _) fun a => le_trans (le_of_eq ?_) (h1 a)
      rw [eucl_eq, WithLp.toLp_sum]; rfl
    · exact pow_nonneg (zero_le_one.trans ((LInv.lengths_basic k r z' hz').2.2 _).1) _
  · unfold Yv
    refine div_le_div_of_nonneg_right ?_ hD0
    refine gramProj_le _ _ (upper u) (det_upper u) _ fun a => ?_
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_inv_rev] using h1 a

end GlobalTheory.Amp.YBound
end
end

