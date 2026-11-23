module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralHaarEqCompactSubgroupTransversal
section
open MeasureTheory

namespace GlobalTheory.Twist

theorem lintegral_haar_eq_transversal (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace E] (μ mK : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
    [IsProbabilityMeasure mK] (lam : Measure E) [SFinite lam] (K : Set G) (e : E → G)
    (he : Measurable e) (hK : mK Kᶜ = 0)
    (hinv : ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK) (hlam : lam ≠ 0)
    (hfin : ∀ C : Set G, IsCompact C → lam {B | ∃ k ∈ K, k * e B ∈ C} < ⊤)
    (hact : ∀ g : G, ∃ ψ : E → E, Measurable ψ ∧ Measure.map ψ lam = lam ∧
      ∀ B, ∃ κ ∈ K, e B * g = κ * e (ψ B)) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂μ = ENNReal.ofReal c * ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
  have hm : Measurable (fun z : E × G => z.2 * e z.1) :=
    measurable_snd.mul (he.comp measurable_fst)
  set ν : Measure G := Measure.map (fun z : E × G => z.2 * e z.1) (lam.prod mK) with hν
  have hint : ∀ f : G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂ν = ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
    intro f hf
    rw [hν, lintegral_map hf hm]
    exact lintegral_prod (fun z : E × G => f (z.2 * e z.1)) (hf.comp hm).aemeasurable
  have hH : ∀ f : G → ENNReal, Measurable f →
      Measurable (fun B => ∫⁻ k, f (k * e B) ∂mK) := by
    intro f hf
    exact Measurable.lintegral_prod_right' (f := fun z : E × G => f (z.2 * e z.1)) (hf.comp hm)
  have hR : ν.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨ψ, hψ, hψl, hψe⟩ := hact g
    refine Measure.ext_of_lintegral _ (fun f hf => ?_)
    have hg : Measurable (fun x : G => x * g) := measurable_mul_const g
    rw [lintegral_map hf hg, hint (fun x => f (x * g)) (hf.comp hg), hint f hf]
    have h1 : ∀ B, ∫⁻ k, f (k * e B * g) ∂mK = ∫⁻ k, f (k * e (ψ B)) ∂mK := by
      intro B
      obtain ⟨κ, hκ, hk⟩ := hψe B
      have h2 := lintegral_map (μ := mK) (f := fun x => f (x * e (ψ B))) (g := fun x => x * κ)
        (hf.comp (measurable_mul_const _)) (measurable_mul_const κ)
      rw [hinv κ hκ] at h2
      rw [h2]
      simp only [mul_assoc, hk]
    simp only [h1]
    have h3 := lintegral_map (μ := lam) (hH f hf) hψ
    rw [hψl] at h3
    exact h3.symm
  have hF : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun C hC => ?_⟩
    have hCm : MeasurableSet C := hC.measurableSet
    have h1 := hint (C.indicator 1) (measurable_one.indicator hCm)
    rw [lintegral_indicator_one hCm] at h1
    rw [h1]
    set S := {B | ∃ k ∈ K, k * e B ∈ C} with hS
    refine lt_of_le_of_lt ?_ (hfin C hC)
    rw [← measure_toMeasurable, ← lintegral_indicator_one (measurableSet_toMeasurable _ _)]
    refine lintegral_mono (fun B => ?_)
    by_cases hB : B ∈ toMeasurable lam S
    · rw [Set.indicator_of_mem hB]
      calc ∫⁻ k, C.indicator (1 : G → ENNReal) (k * e B) ∂mK ≤ ∫⁻ _k, 1 ∂mK :=
            lintegral_mono (fun k => Set.indicator_le_self' (fun _ _ => zero_le_one) _)
        _ = 1 := by simp
    · rw [Set.indicator_of_notMem hB]
      have hB' : B ∉ S := fun h => hB (subset_toMeasurable _ _ h)
      have hae : ∀ᵐ k ∂mK, k ∈ K := hK
      have : ∫⁻ k, C.indicator (1 : G → ENNReal) (k * e B) ∂mK = ∫⁻ _k, 0 ∂mK := by
        refine lintegral_congr_ae (hae.mono fun k hk => ?_)
        exact Set.indicator_of_notMem (fun h => hB' ⟨k, hk, h⟩) _
      simp [this]
  have hν0 : ν ≠ 0 := by
    intro h
    have h1 := hint (fun _ => 1) measurable_const
    rw [h] at h1
    simp at h1
    exact hlam (Measure.measure_univ_eq_zero.mp h1.symm)
  have hmul := Measure.isMulLeftInvariant_eq_smul ν.inv μ
  set c := Measure.haarScalarFactor ν.inv μ with hc
  have hνc : ν = c • μ := by
    have : ν.inv.inv = (c • μ).inv := by rw [← hmul]
    rw [Measure.inv_inv] at this
    rw [this]
    change Measure.map _ (c • μ) = _
    rw [Measure.map_smul (c := c) (f := Inv.inv)
      (measurable_inv.aemeasurable : AEMeasurable Inv.inv μ), Measure.map_inv_eq_self μ]
  have hc0 : c ≠ 0 := by
    intro h
    apply hν0
    rw [hνc, h, zero_smul]
  refine ⟨((c⁻¹ : NNReal) : ℝ), by exact_mod_cast inv_pos.mpr (pos_iff_ne_zero.mpr hc0), fun f hf => ?_⟩
  rw [← hint f hf, hνc, lintegral_smul_measure, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul,
    ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0]
  simp

end GlobalTheory.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralUnfoldingLeOfTranslateCover
section
open MeasureTheory

namespace GlobalTheory

theorem unfolding_cover_bound (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H]
    (μ : Measure H) [μ.IsMulLeftInvariant] (ι : H →* G) (hι : Function.Injective ι)
    (Γ : Subgroup G) [Countable Γ] (Kc : Set H)
    (hK : ∀ h, ∃ δ ∈ Γ.comap ι, δ * h ∈ Kc) (F : G → ENNReal)
    (hF : ∀ γ : G, Measurable fun h => F (γ * ι h)) :
    ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ
      ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ := by
  classical
  haveI hcH : Countable (Γ.comap ι) := by
    have : Function.Injective (fun δ : Γ.comap ι => (⟨ι δ, δ.2⟩ : Γ)) := by
      intro a b hab
      apply Subtype.ext
      apply hι
      simpa using congrArg Subtype.val hab
    exact this.countable
  have step : ∀ g : G, ∫⁻ h, F (g * ι h) ∂μ
      ≤ ∑' δ : Γ.comap ι, ∫⁻ k in Kc, F (g * ι ((δ:H)⁻¹) * ι k) ∂μ := by
    intro g
    have hcov : (Set.univ : Set H) = ⋃ δ : Γ.comap ι, (fun h => (δ:H) * h) ⁻¹' Kc := by
      ext h
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_preimage, true_iff]
      obtain ⟨δ, hδ, hδK⟩ := hK h
      exact ⟨⟨δ, hδ⟩, hδK⟩
    calc ∫⁻ h, F (g * ι h) ∂μ
        = ∫⁻ h in ⋃ δ : Γ.comap ι, (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ := by
          rw [← hcov, Measure.restrict_univ]
      _ ≤ ∑' δ : Γ.comap ι, ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ :=
          lintegral_iUnion_le _ _
      _ = ∑' δ : Γ.comap ι, ∫⁻ k in Kc, F (g * ι ((δ:H)⁻¹) * ι k) ∂μ := by
          congr 1; funext δ
          set e := MeasurableEquiv.mulLeft ((δ:H)⁻¹) with he
          have hmap : μ.map e = μ := by
            rw [MeasurableEquiv.coe_mulLeft]; exact map_mul_left_eq_self μ _
          have hpre : e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc) = Kc := by
            ext k; simp [e]
          calc ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂μ
              = ∫⁻ h in (fun h => (δ:H) * h) ⁻¹' Kc, F (g * ι h) ∂(μ.map e) := by rw [hmap]
            _ = ∫⁻ h, F (g * ι h) ∂((μ.restrict (e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc))).map e) := by
                rw [e.restrict_map]
            _ = ∫⁻ k, F (g * ι (e k)) ∂(μ.restrict (e ⁻¹' ((fun h => (δ:H) * h) ⁻¹' Kc))) :=
                lintegral_map_equiv _ _
            _ = _ := by rw [hpre]; simp [e, mul_assoc]
  haveI : Countable (Γ ⧸ ι.range.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  let φ : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι → Γ := fun p =>
    (p.1.out : Γ) * ⟨ι ((p.2 : H)⁻¹), by simpa using Γ.inv_mem p.2.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨q₁, δ₁⟩ ⟨q₂, δ₂⟩ h
    have hv := congrArg Subtype.val h
    simp only [φ, Subgroup.coe_mul] at hv
    have hq : q₁ = q₂ := by
      rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      refine ⟨(δ₁:H)⁻¹ * (δ₂:H), ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((q₁.out : Γ) : G)⁻¹ * ((q₂.out : Γ) : G)
          = ((q₁.out : Γ) : G)⁻¹ * (((q₂.out : Γ) : G) * ι ((δ₂:H)⁻¹)) * ι (δ₂:H) by
            rw [map_inv]; group, ← hv]
      simp only [map_mul, map_inv]; group
    subst hq
    have h2 : ι ((δ₁:H)⁻¹) = ι ((δ₂:H)⁻¹) := mul_left_cancel hv
    have h3 : (δ₁:H)⁻¹ = (δ₂:H)⁻¹ := hι h2
    simp only [Prod.mk.injEq, true_and]
    exact Subtype.ext (inv_injective h3)
  calc ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ
      ≤ ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∑' δ : Γ.comap ι,
          ∫⁻ k in Kc, F (((φ (q, δ)) : G) * ι k) ∂μ := by
        refine ENNReal.tsum_le_tsum fun q => ?_
        exact step _
    _ = ∑' p, ∫⁻ k in Kc, F ((φ p : G) * ι k) ∂μ := ENNReal.tsum_prod.symm
    _ = ∫⁻ k in Kc, ∑' p, F ((φ p : G) * ι k) ∂μ :=
        (lintegral_tsum fun p => (hF _).aemeasurable).symm
    _ ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ :=
        lintegral_mono fun k => ENNReal.tsum_comp_le_tsum_of_injective hφ (fun γ : Γ => F (γ * ι k))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MainThm
section
open MeasureTheory DoubleCoset

namespace GlobalTheory.TwistedOperatorMainTheorem

theorem main_thm : ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (m : MeasureTheory.Measure G) [MeasureTheory.Measure.IsHaarMeasure m] (J : Subgroup G), IsOpen (↑J : Set G) → IsCompact (↑J : Set G) → ∀ (ι : Type) [Countable ι] (x : ι → G), Pairwise (Function.onFun Disjoint fun (i : ι) ↦ DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) → ∀ (F : G → ℂ), (∀ (g j : G), j ∈ J → ∀ j' ∈ J, F (j * g * j') = F g) → (∀ (g : G), F g ≠ (0 : ℂ) → ∃ (i : ι), g ∈ DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) → (Summable fun (i : ι) ↦ MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) * ‖F (x i)‖) → MeasureTheory.Integrable F m ∧ HasSum (fun (i : ι) ↦ (↑(MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G))) : ℂ) * F (x i)) (∫ (g : G), F g ∂m) ∧ HasSum (fun (c : DoubleCoset.Quotient (↑J : Set G) (↑J : Set G)) ↦ (↑(MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (Quotient.out c) (↑J : Set G) (↑J : Set G))) : ℂ) * F (Quotient.out c)) (∫ (g : G), F g ∂m) := by
  intro G _ _ _ _ _ m _ J hJo hJc ι _ x hdisj F hF hsupp hsum

  have hmeas : ∀ a : G, MeasurableSet (doubleCoset a (J : Set G) J) := fun a =>
    (IsOpen.mul_left hJo).measurableSet
  have hfin : ∀ a : G, m (doubleCoset a (J : Set G) J) < ⊤ := fun a =>
    ((hJc.mul isCompact_singleton).mul hJc).measure_lt_top

  have hconst : ∀ a g, g ∈ doubleCoset a (J : Set G) J → F g = F a := by
    intro a g hg
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_doubleCoset.1 hg
    exact hF a u hu w hw
  have hint : ∀ i, ∫ g in doubleCoset (x i) (J : Set G) J, F g ∂m =
      (m.real (doubleCoset (x i) (J : Set G) J) : ℂ) * F (x i) := by
    intro i
    rw [setIntegral_congr_fun (hmeas _) (fun g hg => hconst (x i) g hg), setIntegral_const, Complex.real_smul]
  have hnorm : ∀ i, ∫ g in doubleCoset (x i) (J : Set G) J, ‖F g‖ ∂m =
      m.real (doubleCoset (x i) (J : Set G) J) * ‖F (x i)‖ := by
    intro i
    rw [setIntegral_congr_fun (hmeas _) (fun g hg => by rw [hconst (x i) g hg]), setIntegral_const, smul_eq_mul]
  have hon : ∀ i, IntegrableOn F (doubleCoset (x i) (J : Set G) J) m := fun i =>
    (integrableOn_const (hfin (x i)).ne).congr_fun (fun g hg => (hconst (x i) g hg).symm) (hmeas _)

  have hU : IntegrableOn F (⋃ i, doubleCoset (x i) (J : Set G) J) m :=
    integrableOn_iUnion_of_summable_integral_norm hon (by simpa only [hnorm] using hsum)
  have hout : ∀ g, g ∉ ⋃ i, doubleCoset (x i) (J : Set G) J → F g = 0 := by
    intro g hg
    by_contra h
    obtain ⟨i, hi⟩ := hsupp g h
    exact hg (Set.mem_iUnion.2 ⟨i, hi⟩)
  have hsumI : HasSum (fun i => (m.real (doubleCoset (x i) (J : Set G) J) : ℂ) * F (x i)) (∫ g, F g ∂m) := by
    have h := hasSum_integral_iUnion (fun i => hmeas (x i)) hdisj hU
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at h
    simp only [hint] at h
    exact h
  refine ⟨hU.integrable_of_forall_notMem_eq_zero hout, hsumI, ?_⟩

  have hinj : Function.Injective (fun i => DoubleCoset.mk J J (x i)) := by
    intro i j hij
    by_contra hne
    have hj : x j ∈ doubleCoset (x i) (J : Set G) J := by
      obtain ⟨u, hu, w, hw, e⟩ := (@DoubleCoset.eq _ _ J J (x i) (x j)).1 hij
      exact mem_doubleCoset.2 ⟨u, hu, w, hw, e⟩
    exact Set.disjoint_left.1 (hdisj hne) hj (mem_doubleCoset_self J J (x j))
  have hcls : ∀ i, Quotient.out (DoubleCoset.mk J J (x i)) ∈ doubleCoset (x i) (J : Set G) J := by
    intro i
    obtain ⟨u, hu, w, hw, e⟩ := DoubleCoset.mk_out_eq_mul J J (x i)
    exact mem_doubleCoset.2 ⟨u, hu, w, hw, e⟩
  have hzero : ∀ c ∉ Set.range (fun i => DoubleCoset.mk J J (x i)),
      (m.real (doubleCoset (Quotient.out c) (J : Set G) J) : ℂ) * F (Quotient.out c) = 0 := by
    intro c hc
    by_contra h
    obtain ⟨i, hi⟩ := hsupp _ (right_ne_zero_of_mul h)
    refine hc ⟨i, ?_⟩
    show DoubleCoset.mk J J (x i) = c
    rw [← DoubleCoset.out_eq' c]
    exact (DoubleCoset.mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hi)).symm
  refine (hinj.hasSum_iff hzero).1 ?_
  convert hsumI using 1
  funext i
  show (m.real (doubleCoset (Quotient.out (DoubleCoset.mk J J (x i))) (J : Set G) J) : ℂ) *
      F (Quotient.out (DoubleCoset.mk J J (x i))) = _
  rw [doubleCoset_eq_of_mem (hcls i), hconst (x i) _ (hcls i)]

end GlobalTheory.TwistedOperatorMainTheorem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanFundamentalDomainOfLe
section
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem mean_fundamentalDomain_of_le : ∀ (g : ℕ) (Λ Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd D₁ : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℝ), Countable Λ₁ → Λ ≤ Λ₁ → IsAddFundamentalDomain Λ Fd volume → IsAddFundamentalDomain Λ₁ D₁ volume → volume Fd ≠ ⊤ → (∀ a ∈ Λ₁, ∀ z, f (z + a) = f z) → (∫ z in D₁, f z) / (volume D₁).toReal = 1 → IntegrableOn f Fd volume ∧ (∫ z in Fd, f z) / (volume Fd).toReal = 1 := by
  intro g Λ Λ₁ Fd D₁ f hc hle hFd hD₁ hfin hper hmean
  have hb : (volume D₁).toReal ≠ 0 := by
    intro h; rw [h, div_zero] at hmean; exact zero_ne_one hmean
  have hab : ∫ z in D₁, f z = (volume D₁).toReal := (div_eq_one_iff_eq hb).1 hmean
  have hint : IntegrableOn f D₁ volume := by
    by_contra h
    rw [integral_undef h] at hab; exact hb hab.symm
  have hD0 : volume D₁ ≠ 0 := fun h => hb (by simp [h])
  have hinv₁ : ∀ (γ : Λ₁) (x : Fin g → ℂ), f (γ +ᵥ x) = f x := fun γ x => by
    show f ((γ : Fin g → ℂ) + x) = f x
    rw [add_comm]; exact hper _ γ.2 x
  have hinv : ∀ (l : Λ) (x : Fin g → ℂ), f (l +ᵥ x) = f x := fun l x => by
    show f ((l : Fin g → ℂ) + x) = f x
    rw [add_comm]; exact hper _ (hle l.2) x
  let Q := Λ₁ ⧸ Λ.addSubgroupOf Λ₁
  haveI : Countable Λ := (AddSubgroup.inclusion_injective hle).countable
  haveI : Countable Q := (QuotientAddGroup.mk_surjective (s := Λ.addSubgroupOf Λ₁)).countable
  let rep : Q → Λ₁ := fun q => q.out
  have hrep : ∀ q : Q, (QuotientAddGroup.mk (rep q) : Q) = q := fun q => QuotientAddGroup.out_eq' q
  have hrepinj : Function.Injective rep := fun q q' h => by rw [← hrep q, ← hrep q', h]
  let s : Q → Set (Fin g → ℂ) := fun q => ((rep q : Λ₁) : Fin g → ℂ) +ᵥ D₁
  have hs : ∀ q, IsAddFundamentalDomain Λ₁ (s q) volume := fun q => hD₁.vadd_of_comm _
  have hsd : Pairwise (Function.onFun (AEDisjoint volume) s) := fun q q' hne => hD₁.aedisjoint (hrepinj.ne hne)
  let E := ⋃ q, s q
  have key : ∀ (l : Λ) (q : Q), l +ᵥ s q =
      ((⟨(l : Fin g → ℂ) + rep q, Λ₁.add_mem (hle l.2) (rep q).2⟩ : Λ₁) +ᵥ D₁) := by
    intro l q; ext x
    simp only [s, Set.mem_vadd_set]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      show ((l : Fin g → ℂ) + rep q) + z = (l : Fin g → ℂ) + ((rep q : Fin g → ℂ) + z)
      abel
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(rep q : Fin g → ℂ) +ᵥ z, ⟨z, hz, rfl⟩, ?_⟩
      show (l : Fin g → ℂ) + ((rep q : Fin g → ℂ) + z) = ((l : Fin g → ℂ) + rep q) + z
      abel
  have hE : IsAddFundamentalDomain Λ E volume := by
    refine ⟨NullMeasurableSet.iUnion fun q => (hs q).nullMeasurableSet, ?_, ?_⟩
    · filter_upwards [hD₁.ae_covers] with x ⟨γ, hγ⟩
      have h1 : (QuotientAddGroup.mk (-γ) : Q) = QuotientAddGroup.mk (rep (QuotientAddGroup.mk (-γ))) :=
        (hrep _).symm
      rw [QuotientAddGroup.eq, neg_neg, AddSubgroup.mem_addSubgroupOf] at h1
      refine ⟨⟨_, h1⟩, Set.mem_iUnion.2 ⟨QuotientAddGroup.mk (-γ), ?_⟩⟩
      refine Set.mem_vadd_set.2 ⟨γ +ᵥ x, hγ, ?_⟩
      show (rep (QuotientAddGroup.mk (-γ)) : Fin g → ℂ) + ((γ : Fin g → ℂ) + x) =
        ((γ + rep (QuotientAddGroup.mk (-γ)) : Λ₁) : Fin g → ℂ) + x
      push_cast; abel
    · intro l l' hne
      simp only [Function.onFun, E, Set.vadd_set_iUnion]
      rw [AEDisjoint.iUnion_left_iff]; intro q
      rw [AEDisjoint.iUnion_right_iff]; intro q'
      rw [key, key]
      apply hD₁.aedisjoint
      intro heq
      have hv : (l : Fin g → ℂ) + rep q = l' + rep q' := congrArg Subtype.val heq
      have hqq : q = q' := by
        rw [← hrep q, ← hrep q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        have : ((-rep q + rep q' : Λ₁) : Fin g → ℂ) = (l : Fin g → ℂ) - l' := by
          push_cast
          calc -(rep q : Fin g → ℂ) + rep q' = -(rep q : Fin g → ℂ) + rep q' + ((l : Fin g → ℂ) + rep q - (l' + rep q')) := by
                rw [hv, sub_self, add_zero]
            _ = (l : Fin g → ℂ) - l' := by abel
        rw [this]; exact Λ.sub_mem l.2 l'.2
      subst hqq
      exact hne (Subtype.ext (add_right_cancel hv))
  have hvol : ∀ q, volume (s q) = volume D₁ := fun q => (hs q).measure_eq hD₁
  have hvolE : volume E = ∑' _ : Q, volume D₁ := by
    show volume (⋃ q, s q) = _
    rw [measure_iUnion₀ hsd fun q => (hs q).nullMeasurableSet]
    simp only [hvol]
  have hEFd : volume E = volume Fd := hE.measure_eq hFd
  haveI : Finite Q := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    exact hfin (by rw [← hEFd, hvolE]; exact ENNReal.tsum_const_eq_top_of_ne_zero hD0)
  haveI := Fintype.ofFinite Q
  have hn : (Fintype.card Q : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hintE : IntegrableOn f E volume :=
    integrableOn_finite_iUnion.2 fun q => ((hs q).integrableOn_iff hD₁ hinv₁).2 hint
  have hsi : ∀ q, ∫ z in s q, f z = ∫ z in D₁, f z := fun q => (hs q).setIntegral_eq hD₁ hinv₁
  have hIE : ∫ z in E, f z = Fintype.card Q * ∫ z in D₁, f z := by
    show ∫ z in ⋃ q, s q, f z = _
    rw [integral_iUnion_ae (fun q => (hs q).nullMeasurableSet) hsd hintE, tsum_fintype]
    simp only [hsi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨(hFd.integrableOn_iff hE hinv).2 hintE, ?_⟩
  rw [hFd.setIntegral_eq hE hinv, ← hEFd, hIE, hvolE, tsum_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, hab]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanPeriodicIndepOfCovolumeOne
section
open MeasureTheory

namespace GlobalTheory


open MeasureTheory in
theorem _root_.GlobalTheory.mean_periodic_indep_of_covolume_one :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (μ μ' : Measure G) (𝓕 𝓕' : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → μ'.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕' μ' → μ' 𝓕' = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ∫ x in 𝓕', Φ x ∂μ' := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov μ μ' 𝓕 𝓕' hμ h𝓕 h𝓕1 hμ' h𝓕' h𝓕'1 Φ hΦ hper
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖Φ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hK.image hΦ.norm).bddAbove
    refine ⟨M, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hcov x
    rw [← hper γ hγ x]
    exact hM ⟨_, hx, rfl⟩
  have hint : IntegrableOn Φ 𝓕 μ :=
    Measure.integrableOn_of_bounded (by rw [h𝓕1]; exact ENNReal.one_ne_top)
      hΦ.aestronglyMeasurable (M := M) (Filter.Eventually.of_forall hM)
  refine ⟨hint, ?_⟩
  have hsm := Measure.isAddLeftInvariant_eq_smul μ' μ
  have hc0 : μ'.addHaarScalarFactor μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hsm
    rw [hsm] at h𝓕'1
    simp at h𝓕'1
  have hac : μ ≪ μ' := by
    intro s hs
    rw [hsm, Measure.smul_apply] at hs
    simpa [hc0] using hs
  have h𝓕'μ : IsAddFundamentalDomain Γ 𝓕' μ := h𝓕'.mono hac
  have hc1 : μ'.addHaarScalarFactor μ = 1 := by
    have e := h𝓕'1
    rw [hsm, Measure.smul_apply, h𝓕'μ.measure_eq h𝓕, h𝓕1] at e
    simpa using e
  have hμμ' : μ' = μ := by rw [hsm, hc1, one_smul]
  rw [hμμ']
  exact h𝓕.setIntegral_eq h𝓕'μ (fun g x => hper g g.2 x)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureOfForallDualVanish
section
namespace GlobalTheory

open Complex

theorem mem_closure_of_forall_dual_vanish :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by
  intro E _ _ _ _ p hp Z x h
  haveI := hp.continuousSMul
  haveI : LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
  by_contra hx
  rw [← Z.topologicalClosure_coe] at hx
  obtain ⟨f, u, hfx, hf⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ)
    ((Z.topologicalClosure.restrictScalars ℝ).convex) Z.isClosed_topologicalClosure hx
  simp only [RCLike.re_to_complex] at hfx hf
  have hre : ∀ w ∈ Z, (f w).re = 0 := by
    intro w hw
    by_contra hne
    set t : ℝ := (u - 1) / (f w).re
    have hmem : ((t : ℂ) • w) ∈ Z.topologicalClosure :=
      Z.le_topologicalClosure (Z.smul_mem _ hw)
    have h1 := hf _ hmem
    rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul] at h1
    have : t * (f w).re = u - 1 := by
      simp only [t]; field_simp
    linarith
  have hvan : ∀ z ∈ Z, f z = 0 := by
    intro z hz
    have h1 := hre z hz
    have h2 := hre (Complex.I • z) (Z.smul_mem _ hz)
    rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at h2
    apply Complex.ext
    · simpa using h1
    · simp at h2; simpa using h2
  have h0 := hf 0 (Z.topologicalClosure.zero_mem)
  have hfx0 := h f hvan
  rw [map_zero] at h0
  rw [hfx0] at hfx
  simp at h0 hfx
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NatCastMemOfPrimeDvdAbsNorm
section
namespace GlobalTheory.NatCastMemOfPrimeDvdNorm

open NumberField IsDedekindDomain

theorem natCast_mem_of_prime_dvd_absNorm {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (RingOfIntegers K)) {q : ℕ} (hq : Nat.Prime q)
    (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : RingOfIntegers K) ∈ w.asIdeal := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (RingOfIntegers K ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have hc : q ∣ Nat.card (RingOfIntegers K ⧸ w.asIdeal) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hc
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : (q : RingOfIntegers K ⧸ w.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]
    exact addOrderOf_nsmul_eq_zero x
  have h2 : (q : RingOfIntegers K ⧸ w.asIdeal) = 0 := (mul_eq_zero.mp h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

end GlobalTheory.NatCastMemOfPrimeDvdNorm
end

