module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0008
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAtlasMeasureEtalePullbackLebesgue
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.EtaleMeasure

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

def rho (A : WeightedAtlas n Y ι La) (U : Set Y) (z : Y → V n) (x : U) : ℝ≥0∞ :=
  ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹

theorem rho_measurable (A : WeightedAtlas n Y ι La) {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) : Measurable (rho A U z) := by
  have hfr := _root_.GlobalTheory.OTY.jdet_isFrameOn_kap n Y ι La A U z hE
  have hc : ContinuousOn (A.nsq A.kap (jdet A z)) U := api_nsq_contOn A hE.isOpen hfr.1
  have hc' : Continuous (fun x : U => A.nsq A.kap (jdet A z) x) := hc.restrict
  exact ENNReal.measurable_ofReal.comp hc'.measurable.inv

theorem mu_piece (A : WeightedAtlas n Y ι La) {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n (fun y : U => z y) e) (i : ι) (B : Set U)
    (hB : MeasurableSet B) (hBs : B ⊆ e.source) (hBi : ∀ m ∈ B, (m : Y) ∈ (A.chart i).source) :
    A.mu.comap Subtype.val B = ∫⁻ m in B, rho A U z m ∂vol n (fun y : U => z y) := by
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hemb := MeasurableEmbedding.subtype_coe hUm
  have hz : IsLocalHomeomorph (fun y : U => z y) := _root_.GlobalTheory.OTY.etale_isLocalHomeomorph n Y ι La A U z hE
  have hfr := _root_.GlobalTheory.OTY.jdet_isFrameOn_kap n Y ι La A U z hE
  have hρ : Measurable (rho A U z) := rho_measurable A hE
  rw [hemb.comap_apply]
  have hBY : MeasurableSet (Subtype.val '' B : Set Y) := hemb.measurableSet_image.2 hB
  rw [A.mu_chart i _ hBY (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)]
  have hBimg : MeasurableSet (e '' B) := by
    have := measurableSet_image_of_chart n (fun y : U => z y) e he B hB hBs
    rwa [Set.image_congr fun m hm => he (hBs hm)] at this
  have hR : ∫⁻ m in B, rho A U z m ∂vol n (fun y : U => z y) =
      ∫⁻ w in e '' B, rho A U z (e.symm w) := by
    rw [← lintegral_indicator hB, lintegral_vol_chart n _ hz e he _ (hρ.indicator hB)
      (fun m hm => Set.indicator_of_notMem (fun h => hm (hBs h)) _)]
    have hsub : e '' B ⊆ e.target := fun _ ⟨m, hm, hmw⟩ => hmw ▸ e.map_source (hBs hm)
    rw [← Set.inter_eq_left.2 hsub, ← Measure.restrict_restrict hBimg, ← lintegral_indicator hBimg]
    refine setLIntegral_congr_fun e.open_target.measurableSet fun w hw => ?_
    by_cases h : e.symm w ∈ B
    · have hw' : w ∈ e '' B := ⟨e.symm w, h, e.right_inv hw⟩
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem hw']
    · have hw' : w ∉ e '' B := by
        rintro ⟨m, hm, rfl⟩
        exact h (by rw [e.left_inv (hBs hm)]; exact hm)
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem hw']
  set F : V n → V n := z ∘ (A.chart i).symm with hFdef
  set S := A.chart i '' (Subtype.val '' B)
  have hS : MeasurableSet S :=
    measurableSet_image_of_chart n (A.chart i) (A.chart i) (fun _ _ => rfl) _ hBY
      (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)
  have hOo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hSO : S ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨(A.chart i).map_source (hBi m hm), ?_⟩
    show (A.chart i).symm (A.chart i m) ∈ U
    rw [(A.chart i).left_inv (hBi m hm)]; exact m.2
  have hFm : ∀ m ∈ B, F (A.chart i m) = e m := fun m hm => by
    simp only [hFdef, Function.comp_apply, (A.chart i).left_inv (hBi m hm)]
    exact he (hBs hm)
  have himg : e '' B = F '' S := by
    rw [Set.image_image, Set.image_image]
    exact (Set.image_congr fun m hm => hFm m hm).symm
  have hinj : Set.InjOn F S := by
    rintro _ ⟨_, ⟨m1, hm1, rfl⟩, rfl⟩ _ ⟨_, ⟨m2, hm2, rfl⟩, rfl⟩ h
    rw [hFm m1 hm1, hFm m2 hm2] at h
    rw [e.injOn (hBs hm1) (hBs hm2) h]
  have hder : ∀ v ∈ S, HasFDerivWithinAt F
      ((fderiv ℂ F v).restrictScalars ℝ) S v := fun v hv =>
    ((((hE.holo i).differentiableAt (hOo.mem_nhds (hSO hv))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  rw [hR, himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hder hinj]
  refine setLIntegral_congr_fun hS ?_
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  have hmi := hBi m hm
  have hne : jdet A z i m ≠ 0 := hE.det_ne i m m.2 hmi
  have hns := api_nsq_eq A hfr.1 hmi m.2
  have hjd : (fderiv ℂ F (A.chart i m)).det = jdet A z i m := rfl
  simp only
  rw [hFm m hm, e.left_inv (hBs hm), (A.chart i).left_inv hmi, rho, ← hns,
    ← ENNReal.ofReal_mul (abs_nonneg _), fc_det_real, hjd]
  congr 1
  have h2 : 0 < ‖jdet A z i m‖ ^ 2 := by positivity
  rw [mul_inv, Real.exp_neg, inv_inv]
  field_simp

end

end GlobalTheory.EtaleMeasure

namespace GlobalTheory.EtaleMeasure

theorem lintegral_mu_etale : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ≥0∞, Measurable φ → ∫⁻ y in U, φ y ∂A.mu = ∫⁻ x : U, φ x * ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹ ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE φ hφ
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hz : IsLocalHomeomorph (fun y : U => z y) := _root_.GlobalTheory.OTY.etale_isLocalHomeomorph n Y ι La A U z hE
  have hρ : Measurable (rho A U z) := rho_measurable A hE
  have hmeas : A.mu.comap Subtype.val = (vol n (fun y : U => z y)).withDensity (rho A U z) := by
    choose e he hxe using fun x : U => exists_chart n _ hz x
    let W : U → Set U := fun x =>
      (e x).source ∩ Subtype.val ⁻¹' (A.chart (A.pick x)).source
    have hWo : ∀ x, IsOpen (W x) := fun x =>
      (e x).open_source.inter ((A.chart _).open_source.preimage continuous_subtype_val)
    obtain ⟨T, hTc, hTW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
    have huniv : ⋃ t : T, W t = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      have hx : x ∈ ⋃ i ∈ T, W i := hTW ▸ Set.mem_iUnion.2 ⟨x, hxe x, A.mem_pick _⟩
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, hxt⟩
    haveI := hTc.to_subtype
    refine Measure.ext_of_iUnion_eq_univ huniv fun t => ?_
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
      withDensity_apply _ (hB.inter (hWo t).measurableSet)]
    exact mu_piece A hE (e t) (he t) (A.pick (t : Y)) (B ∩ W t)
      (hB.inter (hWo t).measurableSet) (fun m hm => hm.2.1) (fun m hm => hm.2.2)
  rw [← lintegral_subtype_comap hUm, hmeas]
  exact (lintegral_withDensity_eq_lintegral_mul _ hρ (hφ.comp measurable_subtype_coe)).trans
    (lintegral_congr fun x => mul_comm _ _)

end GlobalTheory.EtaleMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnOfOnWithCanonical
section
open NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree

namespace GlobalTheory.BigOn

theorem canonical_error_real {ι J : Type} [Fintype J] (T : Finset ι) (I F err err0 J0 : ι → J → ℝ)
    (e c l : ι → ℝ) (D E E' : ℝ) (hD : 0 < D) (he : ∀ w, 0 < e w) (hl : ∀ w, 0 ≤ l w) (hE : 2 * E ≤ E')
    (hJ : ∀ w ∈ T, ∀ j, 0 ≤ J0 w j)
    (h0 : ∀ w j, err0 w j =
      max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) / (e w * (Fintype.card J : ℝ)))
    (h1 : ∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err w j) + c w) * D)
    (h2 : ∀ w ∈ T, ∀ j, 0 ≤ err w j)
    (h3 : ∀ j, ∑ w ∈ T, l w * (e w * err w j + e w * J0 w j) ≤ E) :
    (∀ w ∈ T, ∑ j, I w j ≤ (∑ j, (2 * (e w * F w j) + e w * err0 w j) + c w) * D) ∧
    (∀ w ∈ T, ∀ j, 0 ≤ err0 w j) ∧
    ∀ j, ∑ w ∈ T, l w * (e w * err0 w j + e w * J0 w j) ≤ E' := by
  refine ⟨fun w hw => ?_, fun w _ j => ?_, fun j => ?_⟩
  · rcases isEmpty_or_nonempty J with hJe | hJn
    · simpa using h1 w hw
    · have hn : (0 : ℝ) < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
      have hew := he w
      have hs : ∑ j, e w * err0 w j =
          max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) := by
        simp only [h0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      rw [Finset.sum_add_distrib, hs, ← div_le_iff₀ hD]
      have := le_max_right 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w)
      linarith
  · rw [h0]
    exact div_nonneg (le_max_left _ _) (mul_nonneg (he w).le (Nat.cast_nonneg _))
  · have hn : (0 : ℝ) < (Fintype.card J : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨j⟩)
    have hA : ∀ w ∈ T, (Fintype.card J : ℝ) * (l w * (e w * err0 w j)) ≤ ∑ j', l w * (e w * err w j') := by
      intro w hw
      have hew := he w
      have hs : (Fintype.card J : ℝ) * (l w * (e w * err0 w j)) =
          l w * max 0 ((∑ j', I w j') / D - ∑ j', 2 * (e w * F w j') - c w) := by
        rw [h0]; field_simp
      rw [hs, ← Finset.mul_sum _ _ (l w)]
      refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) (hl w)
      · exact Finset.sum_nonneg fun j' _ => mul_nonneg hew.le (h2 w hw j')
      · have h := h1 w hw
        rw [Finset.sum_add_distrib, ← div_le_iff₀ hD] at h
        linarith
    have hB : ∀ j', ∑ w ∈ T, l w * (e w * err w j') ≤ E := fun j' =>
      le_trans (Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg (he w).le (hJ w hw j'))) (hl w)) (h3 j')
    have hC : ∑ w ∈ T, l w * (e w * J0 w j) ≤ E :=
      le_trans (Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg (he w).le (h2 w hw j))) (hl w)) (h3 j)
    have hF : (Fintype.card J : ℝ) * ∑ w ∈ T, l w * (e w * err0 w j) ≤ (Fintype.card J : ℝ) * E := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum hA) ?_
      rw [Finset.sum_comm]
      refine le_trans (Finset.sum_le_sum fun j' _ => hB j') ?_
      simp
    have hG := le_of_mul_le_mul_left hF hn
    simp only [mul_add, Finset.sum_add_distrib]
    linarith

theorem on_of_onWith_canonical :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (Z : IndefScale Bs) (C C' CH CH' : ℝ) (err : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ), 0 < S.D → 0 ≤ Z.E1u → 2 * C ≤ C' → (∀ w ∈ S.Tw, ∀ j, 0 ≤ Z.J0 (S.μ w) w j) → (∀ w j, S.err0 w j = max 0 ((∑ j', ((S.Iw j' (S.μ w) w : ℝ) + (S.Iw j' (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ))) / (S.D : ℝ) - ∑ j', 2 * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * Z.F0 w j') - (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) / ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (Fintype.card Bs.J : ℝ))) → ONwith S (Z.num C CH) err → S.ON (Z.num C' CH') := by
  intro K _ _ _ Bs Df S Z C C' CH CH' err hD hE hC hJ h0 h
  rw [on_iff_with]
  obtain ⟨h1, h2, h3⟩ := h
  exact canonical_error_real S.Tw
    (fun w j => (S.Iw j (S.μ w) w : ℝ) + (S.Iw j (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ)) Z.F0 err S.err0
    (fun w j => Z.J0 (S.μ w) w j) (fun w => (Formalism.EigenvalueLevelCeiling.ramw w : ℝ))
    (fun w => (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) (fun w => Formalism.DivisionValues.lw w) (S.D : ℝ)
    (C * Z.E1u) (C' * Z.E1u) (by exact_mod_cast hD) (fun w => ramw_pos w) (fun w => (lw_pos w).le)
    (by nlinarith [mul_le_mul_of_nonneg_right hC hE]) hJ h0 h1 h2 h3

end GlobalTheory.BigOn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEqZeroOfSuccLe
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem prod_eq_zero_of_succ_le {I : Type} {D : Type} [CommRing D] (N : ℕ) (t : I → D)
    (h : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (k : ℕ) (hk : N + 1 ≤ k) (s : Fin k → I) :
    ∏ a, t (s a) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Fin.prod_univ_add, h (fun a => s (Fin.castAdd j a)), zero_mul]

theorem taylor_eq_of_le : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (N' : ℕ), N ≤ N' → ∀ f : (I → ℂ) → ℂ, GlobalTheory.PeriodFamily.taylor N' t f = GlobalTheory.PeriodFamily.taylor N t f := by
  intro I _ _ D _ _ N t h N' hN f
  induction N', hN using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [← ih]
    unfold taylor
    rw [Finset.sum_range_succ _ (n + 1)]
    simp [prod_eq_zero_of_succ_le N t h (n + 1) (by omega)]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveTensorOfFibreProjective
section
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem isNilpotent_matrix_of_entries_mem {R : Type*} [CommRing R] {n : ℕ} (I : Ideal R) (N : ℕ)
    (hN : I ^ N = ⊥) (M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, M i j ∈ I) : IsNilpotent M := by
  have key : ∀ j : ℕ, ∀ a b, (M ^ j) a b ∈ I ^ j := by
    intro j
    induction j with
    | zero => intro a b; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ j ih =>
      intro a b
      rw [pow_succ M, Matrix.mul_apply, pow_succ I]
      exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_mul (ih a c) (hM c b)
  refine ⟨N, ?_⟩
  ext a b
  have := key N a b
  rw [hN, Ideal.mem_bot] at this
  simpa using this

theorem le_pow_smul_of_le_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (K : Submodule R M) (hK : K ≤ I • K) (j : ℕ) : K ≤ (I ^ j) • K := by
  induction j with
  | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  | succ j ih =>
    rw [pow_succ', Submodule.mul_smul]
    exact hK.trans (Submodule.smul_mono le_rfl ih)

end GlobalTheory.HTSummand

namespace GlobalTheory.HTSummand

theorem projective_tensor_of_fibre_projective :
    ∀ (C k B : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Field k] [CommRing B] (σ : C →+* k),
      Function.Surjective σ → ∀ (H V : Type 1) [AddCommGroup H] [Module C H] [AddCommGroup V] [Module k V]
      (ρ : B →+* Module.End C H) (ρ' : B →+* Module.End k V) (f : H →ₛₗ[σ] V), Module.Finite C H →
      Module.Projective C H → Function.Surjective f →
      (∀ h, f h = 0 → h ∈ RingHom.ker σ • (⊤ : Submodule C H)) → (∀ x h, f (ρ x h) = ρ' x (f h)) →
      (letI := GlobalTheory.HTSummand.tensorModOf ρ'; Module.Projective (k ⊗[ℤ] B) V) →
      letI := GlobalTheory.HTSummand.tensorModOf ρ; Module.Projective (C ⊗[ℤ] B) H := by
  intro C k B _ _ _ _ _ σ hσ H V _ _ _ _ ρ ρ' f hfin hproj hf hker hcomm hV
  letI mH : Module (C ⊗[ℤ] B) H := tensorModOf ρ
  letI mV : Module (k ⊗[ℤ] B) V := tensorModOf ρ'

  set m : Ideal C := RingHom.ker σ with hm_def
  have hmtop : m ≠ ⊤ := by
    intro h
    have : (1 : C) ∈ m := h ▸ Submodule.mem_top
    rw [hm_def, RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  have hmjac : m ≤ (⊥ : Ideal C).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hmtop
  obtain ⟨N, hN⟩ : ∃ N : ℕ, m ^ N = ⊥ := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    exact ⟨N, le_bot_iff.1 ((Ideal.pow_right_mono hmjac N).trans (le_of_eq hN))⟩

  let τa := Algebra.TensorProduct.map σ.toIntAlgHom (AlgHom.id ℤ B)
  let τ : C ⊗[ℤ] B →+* k ⊗[ℤ] B := τa.toRingHom
  have hτ : Function.Surjective τ :=
    Algebra.TensorProduct.map_surjective σ.toIntAlgHom (AlgHom.id ℤ B) hσ Function.surjective_id
  have hτtmul : ∀ (c : C) (b : B), τ (c ⊗ₜ b) = σ c ⊗ₜ b := fun _ _ => rfl
  have hkerτ : RingHom.ker τ ≤ Ideal.map (algebraMap C (C ⊗[ℤ] B)) m := by
    have h1 : RingHom.ker τ = Ideal.map Algebra.TensorProduct.includeLeft m :=
      Algebra.TensorProduct.rTensor_ker σ.toIntAlgHom hσ
    rw [h1]
    exact Ideal.map_le_iff_le_comap.2 fun c hc => Ideal.mem_map_of_mem (algebraMap C (C ⊗[ℤ] B)) hc
  have hJm : ∀ x ∈ RingHom.ker τ, x ∈ (m • ⊤ : Submodule C (C ⊗[ℤ] B)) := by
    intro x hx
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    exact hkerτ hx
  have hJN : (RingHom.ker τ) ^ N = ⊥ := by
    refine le_bot_iff.1 ((Ideal.pow_right_mono hkerτ N).trans ?_)
    rw [← Ideal.map_pow, hN, Ideal.map_bot]

  haveI tC : IsScalarTower C (C ⊗[ℤ] B) H := IsScalarTower.of_algebraMap_smul fun c h => by
    show ((c ⊗ₜ[ℤ] (1 : B) : C ⊗[ℤ] B)) • h = c • h
    rw [tensorModOf_tmul, map_one]
    rfl
  letI mRV : Module (C ⊗[ℤ] B) V := Module.compHom V τ
  let fR : H →ₗ[C ⊗[ℤ] B] V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r h => by
        show f (r • h) = τ r • f h
        induction r using TensorProduct.induction_on with
        | zero => rw [zero_smul, map_zero, map_zero, zero_smul]
        | tmul c b =>
          rw [hτtmul, tensorModOf_tmul, tensorModOf_tmul, f.map_smulₛₗ, hcomm]
        | add x y hx hy => rw [add_smul, map_add (f := _), hx, hy, map_add (f := _), add_smul] }
  have hfR : Function.Surjective fR := hf
  haveI : Module.Finite (C ⊗[ℤ] B) H := Module.Finite.of_restrictScalars_finite C (C ⊗[ℤ] B) H
  haveI : Module.Finite (C ⊗[ℤ] B) V := Module.Finite.of_surjective fR hfR
  haveI finSV : Module.Finite (k ⊗[ℤ] B) V := by
    letI : Algebra (C ⊗[ℤ] B) (k ⊗[ℤ] B) := τ.toAlgebra
    haveI : IsScalarTower (C ⊗[ℤ] B) (k ⊗[ℤ] B) V := IsScalarTower.of_algebraMap_smul fun r v => rfl
    exact Module.Finite.of_restrictScalars_finite (C ⊗[ℤ] B) (k ⊗[ℤ] B) V

  obtain ⟨n, pb, hpb⟩ := Module.Finite.exists_fin' (k ⊗[ℤ] B) V
  obtain ⟨sb, hsb⟩ := Module.projective_lifting_property pb LinearMap.id hpb
  have hps : ∀ v, pb (sb v) = v := fun v => LinearMap.congr_fun hsb v
  set eb : Matrix (Fin n) (Fin n) (k ⊗[ℤ] B) := LinearMap.toMatrix' (sb ∘ₗ pb) with heb
  have heb_idem : IsIdempotentElem eb := by
    show eb * eb = eb
    rw [heb, ← LinearMap.toMatrix'_comp]
    congr 1
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, hps]
  have heb_apply : ∀ y, eb.mulVec y = sb (pb y) := fun y => by
    rw [heb, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  obtain ⟨E, hE, hEeb⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (τ.mapMatrix :
      Matrix (Fin n) (Fin n) (C ⊗[ℤ] B) →+* Matrix (Fin n) (Fin n) (k ⊗[ℤ] B))
    (fun x hx => by
      refine isNilpotent_matrix_of_entries_mem (RingHom.ker τ) N hJN x fun i j => ?_
      rw [RingHom.mem_ker] at hx ⊢
      exact congrFun (congrFun hx i) j)
    eb ⟨eb.map (Function.surjInv hτ), by ext i j; simp [Function.surjInv_eq hτ]⟩ heb_idem
  have hEE : ∀ w, E.mulVec (E.mulVec w) = E.mulVec w := fun w => by
    rw [Matrix.mulVec_mulVec, hE.eq]
  have hτE : ∀ w : Fin n → C ⊗[ℤ] B, (fun i => τ (E.mulVec w i)) = sb (pb (fun i => τ (w i))) := by
    intro w
    rw [← heb_apply, ← hEeb]
    funext i
    exact RingHom.map_mulVec τ E w i

  set Q : Submodule (C ⊗[ℤ] B) (Fin n → C ⊗[ℤ] B) := LinearMap.range (Matrix.toLin' E) with hQ
  have hQE : ∀ q : Q, E.mulVec (q : Fin n → C ⊗[ℤ] B) = q := by
    rintro ⟨q, w, rfl⟩
    show E.mulVec (Matrix.toLin' E w) = Matrix.toLin' E w
    rw [Matrix.toLin'_apply, hEE]
  let sQ : (Fin n → C ⊗[ℤ] B) →ₗ[C ⊗[ℤ] B] Q :=
    (Matrix.toLin' E).codRestrict Q fun w => LinearMap.mem_range_self _ w
  have hsQ : ∀ q : Q, sQ q = q := fun q => Subtype.ext (by
    show Matrix.toLin' E (q : Fin n → C ⊗[ℤ] B) = q
    rw [Matrix.toLin'_apply, hQE])
  haveI hQproj : Module.Projective (C ⊗[ℤ] B) Q :=
    Module.Projective.of_split Q.subtype sQ (LinearMap.ext hsQ)
  let φ : Q →ₗ[C ⊗[ℤ] B] V :=
    { toFun := fun q => pb (fun i => τ ((q : Fin n → C ⊗[ℤ] B) i))
      map_add' := fun x y => by
        rw [← map_add (f := _)]
        congr 1
        funext i
        simp
      map_smul' := fun r x => by
        show pb _ = τ r • pb _
        rw [← map_smul]
        congr 1
        funext i
        simp }
  have hφ : Function.Surjective φ := by
    intro v
    let w : Fin n → C ⊗[ℤ] B := fun i => Function.surjInv hτ (sb v i)
    refine ⟨⟨Matrix.toLin' E w, LinearMap.mem_range_self _ w⟩, ?_⟩
    show pb (fun i => τ (Matrix.toLin' E w i)) = v
    rw [Matrix.toLin'_apply, hτE]
    have : (fun i => τ (w i)) = sb v := funext fun i => Function.surjInv_eq hτ _
    rw [this, hps, hps]
  obtain ⟨g, hg⟩ := Module.projective_lifting_property fR φ hfR
  have hgφ : ∀ q, f (g q) = φ q := fun q => LinearMap.congr_fun hg q

  have hgs : Function.Surjective g := by
    have hle : (⊤ : Submodule C H) ≤ (LinearMap.range g).restrictScalars C ⊔ m • ⊤ := by
      intro h _
      obtain ⟨q, hq⟩ := hφ (f h)
      have h0 : f (h - g q) = 0 := by rw [map_sub, hgφ, hq, sub_self]
      have : h = g q + (h - g q) := by abel
      rw [this]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self g q) (hker _ h0)
    have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hmjac hle
    intro h
    exact htop Submodule.mem_top

  let g' : Q →ₗ[C] H := g.restrictScalars C
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g' LinearMap.id hgs
  have hgs' : ∀ h, g' (s h) = h := fun h => LinearMap.congr_fun hs h
  let P : Q →ₗ[C] Q := LinearMap.id - s ∘ₗ g'
  have hPK : ∀ x, P x ∈ LinearMap.ker g' := fun x => by
    rw [LinearMap.mem_ker]
    show g' (x - s (g' x)) = 0
    rw [map_sub, hgs', sub_self]
  have hKm : ∀ x ∈ LinearMap.ker g', x ∈ (m • ⊤ : Submodule C Q) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hφx : φ x = 0 := by rw [← hgφ]; exact (congrArg f hx).trans (map_zero f)
    have hτx : (fun i => τ ((x : Fin n → C ⊗[ℤ] B) i)) = 0 := by
      have h1 := hτE x
      rw [hQE x] at h1
      rw [h1]
      have : pb (fun i => τ ((x : Fin n → C ⊗[ℤ] B) i)) = 0 := hφx
      rw [this, map_zero]
    have hx1 : (x : Fin n → C ⊗[ℤ] B) ∈ (m • ⊤ : Submodule C (Fin n → C ⊗[ℤ] B)) := by
      rw [← Finset.univ_sum_single (x : Fin n → C ⊗[ℤ] B)]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hi : (x : Fin n → C ⊗[ℤ] B) i ∈ (m • ⊤ : Submodule C (C ⊗[ℤ] B)) :=
        hJm _ (RingHom.mem_ker.2 (congrFun hτx i))
      have := Submodule.mem_map_of_mem (f := LinearMap.single C (fun _ : Fin n => C ⊗[ℤ] B) i) hi
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have := Submodule.mem_map_of_mem (f := sQ.restrictScalars C) hx1
    rw [Submodule.map_smul''] at this
    have hx' : sQ.restrictScalars C x = x := hsQ x
    rw [hx'] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hK : LinearMap.ker g' ≤ m • LinearMap.ker g' := by
    intro x hx
    have hPx : P x = x := by
      show x - s (g' x) = x
      rw [LinearMap.mem_ker.1 hx, map_zero, sub_zero]
    have := Submodule.mem_map_of_mem (f := P) (hKm x hx)
    rw [Submodule.map_smul'', hPx] at this
    exact Submodule.smul_mono le_rfl (fun y hy => by
      obtain ⟨z, _, rfl⟩ := hy
      exact hPK z) this
  have hK0 : LinearMap.ker g' = ⊥ := by
    have := le_pow_smul_of_le_smul m _ hK N
    rw [hN, Submodule.bot_smul] at this
    exact le_bot_iff.1 this
  have hgi : Function.Injective g := by
    have h' : Function.Injective g' := LinearMap.ker_eq_bot.1 hK0
    exact h'
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective g ⟨hgi, hgs⟩)

end GlobalTheory.HTSummand
end
end

