module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalityPreservedInClosure
section
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.HolDict.ZClosed

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem exists_bound_orbit (Γ : Subgroup G) [DiscreteTopology Γ] {K : Set G} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ x : G, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) ≤ N := by
  classical
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have hKK : IsCompact (K * K⁻¹) := hK.mul hK.inv
  have hfin : (((↑) : Γ → G) ⁻¹' (K * K⁻¹)).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKK).finite_of_discrete
  refine ⟨hfin.toFinset.card, fun x => ?_⟩
  by_cases h : ∃ γ₀ : Γ, γ₀⁻¹ • x ∈ K
  · obtain ⟨γ₀, h₀⟩ := h
    have hs : ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) =
        ∑ γ ∈ hfin.toFinset.image (fun δ => γ₀ * δ⁻¹), K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) := by
      refine tsum_eq_sum fun γ hγ => Set.indicator_of_notMem (fun hx => hγ ?_) _
      refine Finset.mem_image.2 ⟨γ⁻¹ * γ₀, ?_, by group⟩
      rw [Set.Finite.mem_toFinset]
      refine ⟨_, hx, _, Set.inv_mem_inv.2 h₀, ?_⟩
      simp only [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hs]
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun γ _ =>
      Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)) ?_
    simp only [nsmul_eq_mul, mul_one, Nat.cast_le]
    exact Finset.card_image_le
  · push_neg at h
    simp only [Set.indicator_of_notMem (h _), tsum_zero, zero_le]

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

theorem exists_lintegral_le (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {K : Set G} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ f : G → ℝ≥0∞, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      ∫⁻ x in K, f x ∂μ ≤ N * ∫⁻ x in 𝓕, f x ∂μ := by
  obtain ⟨N, hN⟩ := exists_bound_orbit Γ hK
  refine ⟨N, fun f hf hinv => ?_⟩
  have hKm := hK.measurableSet
  rw [← lintegral_indicator hKm, h𝓕.lintegral_eq_tsum', ← lintegral_tsum, ← lintegral_const_mul _ hf]
  · refine lintegral_mono fun x => ?_
    have : ∀ γ : Γ, K.indicator f (γ⁻¹ • x) = K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) * f x := by
      intro γ
      by_cases h : γ⁻¹ • x ∈ K
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
        exact hinv _ (γ⁻¹).2 x
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    simp only [this]
    rw [ENNReal.tsum_mul_right]
    exact mul_le_mul_left (hN x) _
  · intro γ
    exact ((hf.indicator hKm).comp (measurable_const_mul ((γ⁻¹ : Γ) : G))).aemeasurable

theorem lintegral_average_le (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] {X : Type} [MeasurableSpace X]
    (m : Measure X) [IsFiniteMeasure m] {j : X → G} (hj : Measurable j) {K Ω : Set G}
    (hΩ : IsCompact Ω) (hm : ∀ᵐ z ∂m, j z ∈ K) {h : G → ℂ} (hh : Continuous h) :
    ∫⁻ g in Ω, ‖∫ z, h (j z * g) ∂m‖ₑ ∂μ ≤ m Set.univ * ∫⁻ x in K * Ω, ‖h x‖ₑ ∂μ := by
  have hmeas : Measurable fun p : G × X => ‖h (j p.2 * p.1)‖ₑ :=
    hh.enorm.measurable.comp ((hj.comp measurable_snd).mul measurable_fst)
  calc _ ≤ ∫⁻ g in Ω, ∫⁻ z, ‖h (j z * g)‖ₑ ∂m ∂μ := lintegral_mono fun g => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ z, ∫⁻ g in Ω, ‖h (j z * g)‖ₑ ∂μ ∂m := lintegral_lintegral_swap hmeas.aemeasurable
    _ ≤ ∫⁻ _z, ∫⁻ x in K * Ω, ‖h x‖ₑ ∂μ ∂m := by
        refine lintegral_mono_ae (hm.mono fun z hz => ?_)
        have e := (measurePreserving_mul_left μ (j z)).setLIntegral_comp_emb
          (MeasurableEquiv.mulLeft (j z)).measurableEmbedding (fun x => ‖h x‖ₑ) Ω
        refine (le_of_eq e).trans (lintegral_mono_set ?_)
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨_, hz, _, hg, rfl⟩
    _ = _ := by rw [lintegral_const, mul_comm]

theorem average_eq_zero_of_mem_closure [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) {Q : Type} [MeasurableSpace Q] {π : G → Q} (hπ : Measurable π)
    (ρ : G → Lp ℂ 2 ((μ.restrict 𝓕).map π) → Lp ℂ 2 ((μ.restrict 𝓕).map π))
    (hρ : ∀ g F, ∀ᵐ x ∂μ, ρ g F (π x) = F (π (x * g)))
    {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]
    {j : X → G} (hj : Continuous j) {s : Set X} (hs : IsCompact s) (hm : ∀ᵐ z ∂m, z ∈ s)
    {φ ψ : G → ℂ} {F₀ F : Lp ℂ 2 ((μ.restrict 𝓕).map π)}
    (hφ : Continuous φ) (hφΓ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (hφ0 : ∀ g, ∫ z, φ (j z * g) ∂m = 0)
    (hF₀ : ∀ᵐ x ∂μ, F₀ (π x) = φ x)
    (hψ : Continuous ψ) (hψΓ : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (hF : ∀ᵐ x ∂μ, F (π x) = ψ x)
    (hcl : F ∈ closure (Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀} : Set (Lp ℂ 2 ((μ.restrict 𝓕).map π))))
    (g₀ : G) : ∫ z, ψ (j z * g₀) ∂m = 0 := by
  have hms : m.restrict s = m := Measure.restrict_eq_self_of_ae_mem hm
  have hint : ∀ h : G → ℂ, Continuous h → ∀ g, Integrable (fun z => h (j z * g)) m := by
    intro h hh g
    rw [← hms]
    exact (hh.comp (hj.mul continuous_const)).continuousOn.integrableOn_compact hs
  have hspan : ∀ H ∈ Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀}, ∃ h : G → ℂ, Continuous h ∧
      (∀ γ ∈ Γ, ∀ g, h (γ * g) = h g) ∧ (∀ g, ∫ z, h (j z * g) ∂m = 0) ∧ ∀ᵐ x ∂μ.restrict 𝓕, H (π x) = h x := by
    intro H hH
    induction hH using Submodule.span_induction with
    | mem H hH =>
      obtain ⟨u, rfl⟩ := hH
      refine ⟨fun x => φ (x * u), hφ.comp (continuous_id.mul continuous_const), fun γ hγ g => ?_, fun g => ?_,
        ae_restrict_of_ae ?_⟩
      · simp only [mul_assoc, hφΓ γ hγ]
      · simp only [mul_assoc, hφ0]
      · filter_upwards [hρ u F₀, (measurePreserving_mul_right μ u).quasiMeasurePreserving.ae hF₀] with x h1 h2
        rw [h1, h2]
    | zero =>
      refine ⟨0, continuous_const, fun _ _ _ => rfl, fun g => by simp, ?_⟩
      exact ae_of_ae_map hπ.aemeasurable (Lp.coeFn_zero ℂ 2 _)
    | add H H' _ _ h1 h2 =>
      obtain ⟨h, hc, hi, h0, ha⟩ := h1
      obtain ⟨h', hc', hi', h0', ha'⟩ := h2
      refine ⟨h + h', hc.add hc', fun γ hγ g => by simp only [Pi.add_apply, hi γ hγ, hi' γ hγ], fun g => ?_, ?_⟩
      · simp only [Pi.add_apply]
        rw [integral_add (hint h hc g) (hint h' hc' g), h0, h0', add_zero]
      · filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_add H H'), ha, ha'] with x e1 e2 e3
        rw [e1, Pi.add_apply, Pi.add_apply, e2, e3]
    | smul a H _ h1 =>
      obtain ⟨h, hc, hi, h0, ha⟩ := h1
      refine ⟨a • h, hc.const_smul a, fun γ hγ g => by simp only [Pi.smul_apply, hi γ hγ], fun g => ?_, ?_⟩
      · simp only [Pi.smul_apply]
        rw [integral_smul, h0, smul_zero]
      · filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_smul a H), ha] with x e1 e2
        rw [e1, Pi.smul_apply, Pi.smul_apply, e2]
  obtain ⟨Ω, hΩ, hg₀⟩ := exists_compact_mem_nhds g₀
  have hK : IsCompact (j '' s) := hs.image hj
  obtain ⟨N, hN⟩ := exists_lintegral_le Γ μ h𝓕 (hK.mul hΩ)
  set c : ℝ≥0∞ := m Set.univ * (N * μ 𝓕 ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)) with hc
  have hc' : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_)
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hfin
    norm_num
  have hbd : ∀ H ∈ (Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀} : Set (Lp ℂ 2 ((μ.restrict 𝓕).map π))),
      ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - H‖ₑ := by
    intro H hH
    obtain ⟨h, hh, hi, h0, ha⟩ := hspan H hH
    have hd : Continuous (ψ - h) := hψ.sub hh
    have e1 : ∀ g, ∫ z, ψ (j z * g) ∂m = ∫ z, (ψ - h) (j z * g) ∂m := by
      intro g
      simp only [Pi.sub_apply]
      rw [integral_sub (hint ψ hψ g) (hint h hh g), h0, sub_zero]
    simp only [e1]
    refine (lintegral_average_le μ m hj.measurable hΩ (K := j '' s)
      (hm.mono fun z hz => Set.mem_image_of_mem j hz) hd).trans ?_
    rw [hc, mul_assoc, mul_assoc]
    refine mul_le_mul_right ((hN _ hd.enorm.measurable fun γ hγ g => ?_).trans (mul_le_mul_right ?_ _)) _
    · simp only [Pi.sub_apply, hψΓ γ hγ, hi γ hγ]
    · rw [← eLpNorm_one_eq_lintegral_enorm]
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (q := 2) one_le_two hd.aestronglyMeasurable).trans ?_
      rw [Measure.restrict_apply_univ, mul_comm, Lp.enorm_def,
        eLpNorm_map_measure (Lp.aestronglyMeasurable _) hπ.aemeasurable]
      refine le_of_eq (congrArg _ (eLpNorm_congr_ae ?_))
      filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_sub F H), ha, ae_restrict_of_ae hF] with x e1 e2 e3
      rw [Function.comp_apply, e1, Pi.sub_apply, Pi.sub_apply, e2, e3]
      exact hd.aestronglyMeasurable
  have hz : ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ = 0 := by
    have hcont : Continuous fun H : Lp ℂ 2 ((μ.restrict 𝓕).map π) => c * ‖F - H‖ₑ :=
      (ENNReal.continuous_const_mul hc').comp (continuous_const.sub continuous_id).enorm
    have : ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - F‖ₑ :=
      closure_minimal (t := {H | ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - H‖ₑ}) hbd
        (isClosed_le continuous_const hcont) hcl
    simpa using this
  have hC : Continuous fun g => ∫ z, ψ (j z * g) ∂m := by
    have := continuous_parametric_integral_of_continuous (μ := m) (f := fun g z => ψ (j z * g))
      (hψ.comp ((hj.comp continuous_snd).mul continuous_fst)) hs
    rwa [hms] at this
  rw [lintegral_eq_zero_iff hC.enorm.measurable] at hz
  have hz' : (fun g => ∫ z, ψ (j z * g) ∂m) =ᵐ[μ.restrict (interior Ω)] fun _ => 0 := by
    refine ae_restrict_of_ae_restrict_of_subset interior_subset (hz.mono fun g hg => ?_)
    simpa using hg
  exact Measure.eqOn_open_of_ae_eq hz' isOpen_interior hC.continuousOn continuousOn_const
    (mem_interior_iff_mem_nhds.2 hg₀)

end Abstract

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem zcusp_of_mem_closure : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (φ ψ : GA D V → ℂ) F₀ F, IsAutFun V φ → ZCusp V φ → Repr V μ 𝓕 F₀ φ → IsAutFun V ψ → Repr V μ 𝓕 F ψ → F ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set (Lp ℂ 2 (nuQ V μ 𝓕))) → ZCusp V ψ := by
  intro D θ V hθ μ 𝓕 ρ hP hρ φ ψ F₀ F hφ hφ0 hF₀ hψ hF hcl ξ hξ ν 𝓖 hν h𝓖 g
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨ν₀, 𝓖₀, hν₀, h𝓖₀, hc⟩ := (_root_.GlobalTheory.TransvMeasure.transvection_measure D θ V hθ ξ hξ).1
  have hZ : IsClosed (ZI V ξ : Set (GA D V)) := (_root_.GlobalTheory.HolDict.TransvGroup.transvection_group D θ V hθ ξ hξ).2.1
  haveI : LocallyCompactSpace (ZI V ξ) := hZ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Countable ((GQ V).subgroupOf (ZI V ξ)) :=
    Function.Injective.countable (f := fun x : (GQ V).subgroupOf (ZI V ξ) => (⟨x.1.1, x.2⟩ : GQ V))
      fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : GQ V => (t : GA D V)) h))
  haveI : SecondCountableTopology (ZI V ξ) := TopologicalSpace.Subtype.secondCountableTopology (ZI V ξ : Set (GA D V))
  have h₁ : IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓖₀ ν :=
    h𝓖₀.mono (Measure.absolutelyContinuous_isHaarMeasure ν ν₀)
  haveI := hP.haar
  haveI := hP.right
  haveI : IsFiniteMeasure (ν.restrict 𝓖₀) :=
    isFiniteMeasure_restrict.2 ((measure_mono subset_closure).trans_lt hc.measure_lt_top).ne
  rw [h𝓖.setIntegral_eq h₁ (f := fun z : ZI V ξ => ψ ((z : GA D V) * g)) fun γ z => by
    have := hψ.left γ.1.1 γ.2 (z.1 * g)
    rw [← mul_assoc] at this
    exact this]
  exact average_eq_zero_of_mem_closure (GQ V) μ hP.fd hP.fin (π := autMk V) measurable_quotient_mk'' (fun u H => ρ u H)
    hρ.val (ν.restrict 𝓖₀) continuous_subtype_val hc
    ((ae_restrict_mem₀ h₁.nullMeasurableSet).mono fun z hz => subset_closure hz)
    hφ.cont hφ.left (hφ0 ξ hξ ν 𝓖₀ hν h₁) hF₀ hψ.cont hψ.left hF hcl g

end GlobalTheory.HolDict.ZClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairTermEqCentraliserOrbitSum
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.TermPair

theorem finsum_dc_translate {H : Type} [Group H] (A B K : Subgroup H) (u : H)
    (hAB : B = A.map (MulAut.conj u).toMonoidHom) (S₁ S₂ : H → ℂ)
    (hS₂ : ∀ b ∈ B, ∀ k ∈ K, ∀ h, S₂ (b * h * k) = S₂ h) (h12 : ∀ h, S₁ h = S₂ (u * h)) :
    ∑ᶠ q : DoubleCoset.Quotient (A : Set H) (K : Set H), S₁ (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (B : Set H) (K : Set H), S₂ (Quotient.out q) := by
  have memB : ∀ a, a ∈ A → u * a * u⁻¹ ∈ B := fun a ha => by
    rw [hAB]; exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  have memA : ∀ b, b ∈ B → u⁻¹ * b * u ∈ A := fun b hb => by
    rw [hAB] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    simpa [MulAut.conj_apply, mul_assoc] using ha
  let e : DoubleCoset.Quotient (A : Set H) (K : Set H) ≃ DoubleCoset.Quotient (B : Set H) (K : Set H) :=
    { toFun := Quotient.map' (u * ·) (fun x y hxy => by
        obtain ⟨a, ha, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hxy
        exact DoubleCoset.rel_iff.2 ⟨u * a * u⁻¹, memB a ha, k, hk, by group⟩)
      invFun := Quotient.map' (u⁻¹ * ·) (fun x y hxy => by
        obtain ⟨b, hb, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hxy
        exact DoubleCoset.rel_iff.2 ⟨u⁻¹ * b * u, memA b hb, k, hk, by group⟩)
      left_inv := fun q => by
        induction q using Quotient.inductionOn' with
        | h x =>
          simp only [Quotient.map'_mk'', inv_mul_cancel_left, mul_inv_cancel_left]
          rfl
      right_inv := fun q => by
        induction q using Quotient.inductionOn' with
        | h x =>
          simp only [Quotient.map'_mk'', inv_mul_cancel_left, mul_inv_cancel_left]
          rfl }
  have hF : ∀ x y : H, DoubleCoset.mk B K x = DoubleCoset.mk B K y → S₂ x = S₂ y := fun x y hxy => by
    obtain ⟨b, hb, k, hk, rfl⟩ := (@DoubleCoset.eq _ _ B K x y).1 hxy
    exact (hS₂ b hb k hk x).symm
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  rw [h12]
  apply hF
  rw [DoubleCoset.out_eq']
  conv_rhs => rw [← DoubleCoset.out_eq' q]
  rfl

theorem card_eq_of_conj {Γ : Type} [Group Γ] (S T : Subgroup Γ) (v : Γ) (h : ∀ w, w ∈ T ↔ v⁻¹ * w * v ∈ S) :
    Nat.card T = Nat.card S :=
  Nat.card_congr
    { toFun := fun w => ⟨v⁻¹ * w * v, (h w).1 w.2⟩
      invFun := fun w => ⟨v * w * v⁻¹, (h _).2 (by simpa [mul_assoc] using w.2)⟩
      left_inv := fun w => by ext; simp [mul_assoc]
      right_inv := fun w => by ext; simp [mul_assoc] }

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair

theorem mem_map_conj {H : Type} [Group H] (K : Subgroup H) (a x : H) :
    x ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ K := by
  rw [Subgroup.mem_map_equiv]; simp [MulAut.conj_symm_apply]

theorem conj_mem_iff {H : Type} [Group H] (K : Subgroup H) (a h k y : H) (hk : k ∈ K) :
    (a * h * k)⁻¹ * y * (a * h * k) ∈ K ↔ h⁻¹ * (a⁻¹ * y * a) * h ∈ K := by
  have e : (a * h * k)⁻¹ * y * (a * h * k) = k⁻¹ * (h⁻¹ * (a⁻¹ * y * a) * h) * k := by group
  rw [e, K.mul_mem_cancel_right hk, K.mul_mem_cancel_left (K.inv_mem hk)]

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem cent_le_grp (P : DPair G) : P.cent ≤ GlobalTheory.LKCx.grp G P.β := fun y hy =>
  ⟨hy.2, DFormPos.sim_pos p G (DForm.ofDPair P) y.1 y.2 hy.2⟩

theorem centralizer_eq (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β) :
    Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} =
      (Subgroup.inclusion (cent_le_grp P)).range := by
  ext v
  rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_range]
  constructor
  · intro h
    have h' := congrArg (fun w : GlobalTheory.LKCx.grp G P.β => (w : G.Cˣ × ℚˣ).1) h
    simp only [Subgroup.coe_mul, Prod.fst_mul] at h'
    exact ⟨⟨v, h', v.2.1⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    apply Subtype.ext
    exact Prod.ext w.2.1 (mul_comm _ _)

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair
variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem termAt_eq (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ)
    (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G 1)
    (hδ : IsNrm G 1 P.atP δ z) :
    P.termAt Kf f 1 K' f' x t hx δ z =
      centSum (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f'
        ⟨(P.γ, P.c), hm⟩ := by
  have hδ' : δ = z⁻¹ * inclG G 1 P.atP * z := by simpa [IsNrm, nrmG] using hδ
  have hle := cent_le_grp P
  have e1 : ∀ w, GlobalTheory.LKCx.toAfF G P.β x t hx (Subgroup.inclusion hle w) = P.toAf x t hx w := fun w => rfl
  have e2 : ∀ w, P.toQr 1 z w = z⁻¹ * GlobalTheory.LKCx.toP1 G P.β (Subgroup.inclusion hle w) * z := fun w => by
    simp [DPair.toQr, GlobalTheory.LKCx.toP1, carry, MulAut.conj_apply]
  have eg : Subgroup.inclusion hle P.self = ⟨(P.γ, P.c), hm⟩ := rfl
  have hj2g : GlobalTheory.LKCx.toP1 G P.β ⟨(P.γ, P.c), hm⟩ = inclG G 1 P.atP := rfl
  have hC := centralizer_eq P hm
  unfold DPair.termAt pointSum centSum
  refine finsum_dc_translate ((P.toAf x t hx).prod (P.toQr 1 z)).range
    ((Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)}).map
      ((GlobalTheory.LKCx.toAfF G P.β x t hx).prod (GlobalTheory.LKCx.toP1 G P.β))) (Kf.prod K') ((1 : G.GAf), z) ?_
    (fun h => ((Nat.card (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h) : ℕ) : ℂ)⁻¹ *
      (f (h.1⁻¹ * (P.toAf x t hx) P.self * h.1) * f' (h.2⁻¹ * δ * (sigG G 1) h.2)))
    (fun h => ((Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' h ⊓
      Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) : ℕ) : ℂ)⁻¹ *
      term (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) 1 f f' h
        ⟨(P.γ, P.c), hm⟩) ?_ ?_
  · rw [hC, MonoidHom.map_range, MonoidHom.map_range]
    refine congrArg MonoidHom.range (MonoidHom.ext fun w => ?_)
    refine Prod.ext ?_ ?_
    · simp [MulAut.conj_apply, e1]
    · simp [MulAut.conj_apply, e2]
      group
  · rintro b hb k hk h
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
    have hvc : v * (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) = (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * v := Subgroup.mem_centralizer_singleton_iff.1 hv
    have hvg : v⁻¹ * (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * v = (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) := by
      rw [mul_assoc, ← hvc, inv_mul_cancel_left]
    have hcard : Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((GlobalTheory.LKCx.toAfF G P.β x t hx).prod (GlobalTheory.LKCx.toP1 G P.β)) v * h * k) ⊓
        Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) =
        Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' h ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) := by
      refine card_eq_of_conj _ _ v fun w => ?_
      simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, mem_map_conj, MonoidHom.prod_apply, Prod.fst_mul,
        Prod.snd_mul]
      rw [conj_mem_iff _ _ _ _ _ hk1, conj_mem_iff _ _ _ _ _ hk2, map_mul, map_mul, map_mul, map_mul, map_inv,
        map_inv]
      have hCv : w ∈ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} ↔ v⁻¹ * w * v ∈ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} := by
        rw [Subgroup.mul_mem_cancel_right _ hv, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hv)]
      rw [hCv]
    have ef : ∀ a y : G.GAf, f ((a * h.1 * k.1)⁻¹ * y * (a * h.1 * k.1)) = f (h.1⁻¹ * (a⁻¹ * y * a) * h.1) :=
      fun a y => by
        rw [← hf k.1 hk1 (h.1⁻¹ * (a⁻¹ * y * a) * h.1)]; congr 1; group
    have ef' : ∀ a y : Gr G 1, f' ((a * h.2 * k.2)⁻¹ * y * (a * h.2 * k.2)) =
        f' (h.2⁻¹ * (a⁻¹ * y * a) * h.2) := fun a y => by
      rw [← hf' k.2 hk2 (h.2⁻¹ * (a⁻¹ * y * a) * h.2)]; congr 1; group
    have g1 : ((GlobalTheory.LKCx.toAfF G P.β x t hx) v)⁻¹ * (GlobalTheory.LKCx.toAfF G P.β x t hx) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * (GlobalTheory.LKCx.toAfF G P.β x t hx) v = (GlobalTheory.LKCx.toAfF G P.β x t hx) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) := by
      rw [← map_inv, ← map_mul, ← map_mul, hvg]
    have g2 : ((GlobalTheory.LKCx.toP1 G P.β) v)⁻¹ * ((GlobalTheory.LKCx.toP1 G P.β) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * 1) * (GlobalTheory.LKCx.toP1 G P.β) v = (GlobalTheory.LKCx.toP1 G P.β) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * 1 := by
      rw [mul_one, ← map_inv, ← map_mul, ← map_mul, hvg]
    beta_reduce
    rw [hcard]
    simp only [term, MonoidHom.prod_apply, Prod.fst_mul, Prod.snd_mul, MonoidHom.id_apply]
    rw [ef, ef', g1, g2]
  · intro h
    have hmem : ∀ w, Subgroup.inclusion hle w ∈ stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ↔
        w ∈ stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h := fun w => by
      simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, mem_map_conj, Prod.fst_mul, Prod.snd_mul, one_mul, e1, e2]
      have e3 : (z * h.2)⁻¹ * (GlobalTheory.LKCx.toP1 G P.β) (Subgroup.inclusion hle w) * (z * h.2) =
          h.2⁻¹ * (z⁻¹ * (GlobalTheory.LKCx.toP1 G P.β) (Subgroup.inclusion hle w) * z) * h.2 := by group
      rw [e3]
    have hsub : stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} =
        (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h).map (Subgroup.inclusion hle) := by
      rw [hC]
      ext v
      simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map]
      constructor
      · rintro ⟨hv, w, rfl⟩
        exact ⟨w, (hmem w).1 hv, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(hmem w).2 hw, w, rfl⟩
    have hcard : Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} :
        Subgroup _) = Nat.card (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h) := by
      rw [hsub]; exact Subgroup.card_map_of_injective (Subgroup.inclusion_injective hle)
    beta_reduce
    rw [hcard]
    simp only [term, Prod.fst_mul, Prod.snd_mul, MonoidHom.id_apply, one_mul, mul_one, GlobalTheory.LKCx.sigG_one]
    rw [← e1 P.self, eg, hδ', ← hj2g]
    congr 3
    group

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair

theorem term_eq_centSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : GlobalTheory.LKDef.DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      P.term L.K.toSubgroup f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' ⟨(P.γ, P.c), hm⟩ := by
  intro p _ G P hm L f hf K' f' hf'
  have hex : ∃ dz : Gr G 1 × Gr G 1, IsNrm G 1 P.atP dz.1 dz.2 :=
    ⟨(inclG G 1 P.atP, 1), by simp [IsNrm, nrmG]⟩
  unfold DPair.term
  rw [dite_eq_left hex]
  exact termAt_eq P hm _ f (fun k hk g => by simpa using hf.2.2.1 k hk g) K' f'
    (fun k hk g => by simpa [GlobalTheory.LKCx.sigG_one] using hf'.2.2.1 k hk g) _ _ _ _ _ hex.choose_spec

end GlobalTheory.LKDef.TermPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.LowIrr

def zR (P Q R S : ℕ) : Fin R × Fin (P + Q) → Ln P Q R S := fun w => (finSumFinEquiv.symm w.2, .inl w.1)

def yS (P Q R S : ℕ) : Fin S × Fin (P + Q) → Ln P Q R S := fun w => (finSumFinEquiv.symm w.2, .inr w.1)

def kap (P Q k k' : ℕ) : Fin (P + Q) → ℂ := fun i => if (i : ℕ) < P then (k : ℂ) else -(k' : ℂ)

theorem zR_inj (P Q R S : ℕ) : Function.Injective (zR P Q R S) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ e
  simp only [zR, Prod.mk.injEq, Sum.inl.injEq, EmbeddingLike.apply_eq_iff_eq] at e
  rw [e.1, e.2]

theorem yS_inj (P Q R S : ℕ) : Function.Injective (yS P Q R S) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ e
  simp only [yS, Prod.mk.injEq, Sum.inr.injEq, EmbeddingLike.apply_eq_iff_eq] at e
  rw [e.1, e.2]

theorem zR_ne_yS (P Q R S : ℕ) (u w) : zR P Q R S u ≠ yS P Q R S w := by
  simp [zR, yS]

theorem zR_or_yS (P Q R S : ℕ) (s : Ln P Q R S) :
    (∃ u, zR P Q R S u = s) ∨ ∃ w, yS P Q R S w = s := by
  obtain ⟨a, c | d⟩ := s
  · exact Or.inl ⟨(c, finSumFinEquiv a), by simp [zR]⟩
  · exact Or.inr ⟨(d, finSumFinEquiv a), by simp [yS]⟩

theorem fockF_rowOp {σ I J : Type} [DecidableEq σ] [Fintype J] (z : I × J → σ) (c d : I)
    (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (GlobalTheory.Capelli.rowOp ℂ z c d f) g = Formalism.REAL.fockF f (GlobalTheory.Capelli.rowOp ℂ z d c g) := by
  rw [GlobalTheory.Capelli.rowOp_apply, GlobalTheory.Capelli.rowOp_apply, Formalism.REAL.fischerInner_sum_left, Formalism.REAL.fischerInner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Formalism.REAL.fischerInner_X_mul_left, Formalism.REAL.fischerInner_pderiv_left]

theorem eab_isKC_inl {R S : ℕ} (c d : Fin R) : IsKC (Eab (.inl c) (.inl d) : Mat R S) := by
  intro a b h
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact absurd trivial h
  · rfl

theorem eab_isKC_inr {R S : ℕ} (c d : Fin S) : IsKC (Eab (.inr c) (.inr d) : Mat R S) := by
  intro a b h
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact absurd trivial h
  · rfl

end GlobalTheory.LowIrr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistAcyclicSpectrumPolynomialOfIsAlgClosedStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistAcyclic_spectrum_polynomial_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K], IsUnit (q : K) → Acyc q (sp (Polynomial K)) := by
  first | (exact @GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed) | (exact GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed) | (intros; apply GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed  <;> assumption)
end

