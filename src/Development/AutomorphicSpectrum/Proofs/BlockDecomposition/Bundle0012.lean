module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierOneParameterIntegral
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.OneParamFourier

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace A] [BorelSpace A]

theorem integral_translate_mul_char (lam : Measure A) [lam.IsAddHaarMeasure] (H : A → ℂ)
    (χ : AddChar A ℂ) (a : A) :
    ∫ b, H (b + a) * χ b ∂lam = χ (-a) * ∫ b, H b * χ b ∂lam := by
  have h := integral_add_right_eq_self (μ := lam) (fun b => H b * χ (b + -a)) a
  simp only [add_neg_cancel_right] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [AddChar.map_add_eq_mul]
  ring

theorem integrable_mul_char {lam : Measure A} {H : A → ℂ} (hH : Integrable H lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) :
    Integrable (fun b => H b * χ b) lam := by
  refine hH.mono (hH.aestronglyMeasurable.mul hχ.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun b => ?_)
  simp [hn]

theorem integrable_uncurry_translate (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam]
    (c : ℝ →+ A) (hc : Continuous c) {G : A → ℂ} (hG : Continuous G) (hGi : Integrable G lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (K : ℂ) (s : ℝ) :
    Integrable (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b)
      ((volume.restrict (Set.uIoc 0 s)).prod lam) := by
  have hcont : Continuous (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) := by
    unfold Function.uncurry
    fun_prop
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) s)) := by
    unfold Set.uIoc
    infer_instance
  refine (integrable_prod_iff hcont.aestronglyMeasurable).2 ⟨ae_of_all _ fun u => ?_, ?_⟩
  · have h1 : Integrable (fun b => G (b + c u)) lam := hGi.comp_add_right (c u)
    have h2 := integrable_mul_char (h1.const_mul K) hχ hn
    simpa [Function.uncurry, mul_assoc] using h2
  · have hconst : ∀ u : ℝ, ∫ b, ‖Function.uncurry (fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) (u, b)‖ ∂lam
        = ‖K‖ * ∫ b, ‖G b‖ ∂lam := by
      intro u
      have h := integral_add_right_eq_self (μ := lam) (fun b => ‖G b‖) (c u)
      rw [← h, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp [Function.uncurry, hn]
    simp_rw [hconst]
    exact integrable_const _

theorem integral_mul_char_eq_of_hasDerivAt (A : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A)
    [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A) (hc : Continuous c) (F G : A → ℂ)
    (hF : Continuous F) (hG : Continuous G) (hFi : Integrable F lam) (hGi : Integrable G lam)
    (χ : AddChar A ℂ) (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (f : ℝ)
    (hf : ∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ))))
    (hd : ∀ (b : A) (s : ℝ),
      HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) :
    ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by
  set K : ℂ := 2 * Real.pi * Complex.I with hK
  have hK0 : K ≠ 0 := by
    simp [hK, Real.pi_ne_zero, Complex.I_ne_zero]
  set e : ℝ → ℂ := fun u => Complex.exp (K * ((u * f : ℝ) : ℂ)) with he
  have hχe : ∀ s : ℝ, χ (-(c s)) = e s := by
    intro s
    rw [← map_neg, hf, he]
    simp only
    congr 1
    push_cast
    ring
  set Fh : ℂ := ∫ b, F b * χ b ∂lam with hFh
  set Gh : ℂ := ∫ b, G b * χ b ∂lam with hGh
  have hec : Continuous e := by
    rw [he]
    fun_prop
  have key : ∀ s : ℝ, (e s - 1) * Fh = K * Gh * ∫ u in (0 : ℝ)..s, e u := by
    intro s
    have hftc : ∀ b : A, F (b + c s) - F b = ∫ u in (0 : ℝ)..s, K * G (b + c u) := by
      intro b
      have hcu : Continuous fun u : ℝ => K * G (b + c u) := by fun_prop
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
        (f := fun t : ℝ => F (b + c t)) (f' := fun u => K * G (b + c u))
        (fun x _ => hd b x) (hcu.intervalIntegrable _ _)
      simpa using this.symm
    have hswap := intervalIntegral_integral_swap
      (integrable_uncurry_translate lam c hc hG hGi hχ hn K s)
    have h1 : ∫ b, F (b + c s) * χ b ∂lam = e s * Fh := by
      rw [integral_translate_mul_char, hχe]
    have hi1 : Integrable (fun b => F (b + c s) * χ b) lam :=
      integrable_mul_char (hFi.comp_add_right (c s)) hχ hn
    have hi2 : Integrable (fun b => F b * χ b) lam := integrable_mul_char hFi hχ hn
    have h2 : (e s - 1) * Fh = ∫ b, (∫ u in (0 : ℝ)..s, K * G (b + c u) * χ b) ∂lam := by
      have : (e s - 1) * Fh = ∫ b, (F (b + c s) * χ b - F b * χ b) ∂lam := by
        rw [integral_sub hi1 hi2, h1]
        ring
      rw [this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [intervalIntegral.integral_mul_const, ← hftc b]
      ring
    rw [h2, ← hswap, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    beta_reduce
    have h3 : ∫ b, K * G (b + c u) * χ b ∂lam = K * ∫ b, G (b + c u) * χ b ∂lam := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      ring
    rw [h3, integral_translate_mul_char, hχe]
    ring
  have hL : HasDerivAt (fun s : ℝ => (e s - 1) * Fh) (K * f * Fh) 0 := by
    have h0 : HasDerivAt (fun u : ℝ => K * ((u * f : ℝ) : ℂ)) (K * f) 0 := by
      have : HasDerivAt (fun u : ℝ => ((u : ℂ))) 1 0 := Complex.ofRealCLM.hasDerivAt
      simpa [mul_assoc] using (this.mul_const (f : ℂ)).const_mul K
    have := ((h0.cexp).sub_const 1).mul_const Fh
    simpa [he] using this
  have hR : HasDerivAt (fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u) (K * Gh) 0 := by
    have := (hec.integral_hasStrictDerivAt 0 0).hasDerivAt.const_mul (K * Gh)
    simpa [he] using this
  have hEq : (fun s : ℝ => (e s - 1) * Fh) = fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u :=
    funext key
  rw [hEq] at hL
  have := hL.unique hR
  have h4 : K * (f * Fh) = K * Gh := by
    rw [← mul_assoc]
    exact this
  exact (mul_left_cancel₀ hK0 h4).symm

end GlobalTheory.CompanionTheory.OneParamFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
section
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.UnfoldAbs

theorem hasSum_integral_of_norm_bound {A Z : Type} [MeasurableSpace A] (μ : Measure A)
    [IsFiniteMeasure μ] [Countable Z] (G : Z → A → ℂ)
    (hm : ∀ q, AEStronglyMeasurable (G q) μ) (M : ℝ)
    (hb : ∀ b, Summable (fun q => ‖G q b‖) ∧ ∑' q, ‖G q b‖ ≤ M) :
    HasSum (fun q => ∫ b, G q b ∂μ) (∫ b, ∑' q, G q b ∂μ) := by
  have hbd : ∀ q b, ‖G q b‖ ≤ M := fun q b =>
    ((hb b).1.le_tsum q (fun _ _ => norm_nonneg _)).trans (hb b).2
  have hint : ∀ q, Integrable (G q) μ := fun q =>
    Integrable.of_bound (hm q) M (ae_of_all _ (hbd q))
  refine hasSum_integral_of_summable_integral_norm hint ?_
  refine summable_of_sum_le (c := ∫ _, M ∂μ)
    (fun q => integral_nonneg fun _ => norm_nonneg _) ?_
  intro s
  rw [← MeasureTheory.integral_finsetSum s (fun q _ => (hint q).norm)]
  exact integral_mono (MeasureTheory.integrable_finsetSum _ fun q _ => (hint q).norm) (integrable_const _)
    (fun b => ((hb b).1.sum_le_tsum s (fun _ _ => norm_nonneg _)).trans (hb b).2)

theorem setIntegral_eq_zero_of_translate {A : Type} [AddCommGroup A] [MeasurableSpace A]
    [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A)
    [Countable Λ] (𝓖 : Set A) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (Ψ : A → ℂ) (ν : A) (z : ℂ)
    (hz : z ≠ 1) (hΛ : ∀ (l : Λ) b, Ψ ((l : A) + b) = Ψ b) (hν : ∀ b, Ψ (ν + b) = z * Ψ b) :
    ∫ b in 𝓖, Ψ b ∂lam = 0 := by
  have h2 : IsAddFundamentalDomain Λ (ν +ᵥ 𝓖) lam := h𝓖.vadd_of_comm ν
  have e1 : ∫ b in 𝓖, Ψ b ∂lam = ∫ b in (ν +ᵥ 𝓖), Ψ b ∂lam :=
    h𝓖.setIntegral_eq h2 (fun g x => hΛ g x)
  have hpre : (fun x => ν + x) ⁻¹' (ν +ᵥ 𝓖) = 𝓖 := by
    ext x
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have e2 : ∫ b in (ν +ᵥ 𝓖), Ψ b ∂lam = ∫ b in 𝓖, Ψ (ν + b) ∂lam := by
    have := (measurePreserving_add_left lam ν).setIntegral_preimage_emb
      (MeasurableEquiv.addLeft ν).measurableEmbedding Ψ (ν +ᵥ 𝓖)
    rw [hpre] at this
    exact this.symm
  have e3 : ∫ b in 𝓖, Ψ (ν + b) ∂lam = z * ∫ b in 𝓖, Ψ b ∂lam := by
    simp_rw [hν]
    exact integral_const_mul _ _
  have e4 : (1 - z) * ∫ b in 𝓖, Ψ b ∂lam = 0 := by
    have : ∫ b in 𝓖, Ψ b ∂lam = z * ∫ b in 𝓖, Ψ b ∂lam := by rw [← e3, ← e2, ← e1]
    linear_combination this
  exact (mul_eq_zero.mp e4).resolve_left (sub_ne_zero.mpr (Ne.symm hz))

theorem integrable_of_lattice_bound {A : Type} [AddCommGroup A] [MeasurableSpace A]
    [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A)
    [Countable Λ] (𝓖 : Set A) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (h1 : lam 𝓖 = 1)
    (F0 : A → ℂ) (hm : AEStronglyMeasurable F0 lam) (M : ℝ)
    (hb : ∀ b, Summable (fun l : Λ => ‖F0 ((l : A) + b)‖) ∧ ∑' l : Λ, ‖F0 ((l : A) + b)‖ ≤ M) :
    Integrable F0 lam := by
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have e : ∫⁻ b, ‖F0 b‖ₑ ∂lam = ∑' l : Λ, ∫⁻ b in 𝓖, ‖F0 ((l : A) + b)‖ₑ ∂lam :=
    h𝓖.lintegral_eq_tsum'' _
  have hmeas : ∀ l : Λ, AEMeasurable (fun b => ‖F0 ((l : A) + b)‖ₑ) (lam.restrict 𝓖) := fun l =>
    ((hm.comp_measurePreserving (measurePreserving_add_left lam (l : A))).enorm).restrict
  rw [e, ← lintegral_tsum hmeas]
  calc ∫⁻ b in 𝓖, ∑' l : Λ, ‖F0 ((l : A) + b)‖ₑ ∂lam
      ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal M ∂lam := by
        refine lintegral_mono (fun b => ?_)
        simp_rw [← ofReal_norm_eq_enorm]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hb b).1]
        exact ENNReal.ofReal_le_ofReal (hb b).2
    _ < ⊤ := by simp [h1]

theorem unfold_abs : ∀ {A X Y : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A)
    (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] (c : X → Y) (y0 : Y)
    (F : X → A → ℂ) (F0 : A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam)
    (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1)
    (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1) (M : ℝ)
    (_ : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ M) (τ : Λ → X ≃ X)
    (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q)
    (e : Λ → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e)
    (_ : ∀ (l : Λ) b, F (e l) b = F0 ((l : A) + b))
    (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b),
    Integrable F0 lam ∧ ∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam = ∫ b, F0 b * ch b ∂lam := by
  intro A X Y _ _ _ lam _ Λ _ 𝓖 h𝓖 h1 _ c y0 F F0 ch hF hch hnorm hmul hΛ M hb τ hτ hcτ e he hfib
    hF0 hν
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by simp [h1]⟩

  have hsub : ∀ {Z : Type} (j : Z → X), Function.Injective j → ∀ b,
      Summable (fun z => ‖F (j z) b‖) ∧ ∑' z, ‖F (j z) b‖ ≤ M := by
    intro Z j hj b
    refine ⟨(hb b).1.comp_injective hj, ?_⟩
    exact (tsum_comp_le_tsum_of_inj (hb b).1 (fun _ => norm_nonneg _) hj).trans (hb b).2
  have key : ∀ {Z : Type} [Countable Z] (j : Z → X), Function.Injective j →
      HasSum (fun z => ∫ b in 𝓖, F (j z) b * ch b ∂lam)
        (∫ b in 𝓖, (∑' z, F (j z) b) * ch b ∂lam) := by
    intro Z _ j hj
    have := hasSum_integral_of_norm_bound (lam.restrict 𝓖) (fun z b => F (j z) b * ch b)
      (fun z => ((hF (j z)).mul hch).restrict) M (fun b => by
        simpa [hnorm] using hsub j hj b)
    simpa only [tsum_mul_right] using this

  have hF0e : F0 = F (e 0) := by
    funext b
    have := hF0 0 b
    simpa using this.symm
  have hint0 : Integrable F0 lam := by
    refine integrable_of_lattice_bound lam Λ 𝓖 h𝓖 h1 F0 (hF0e ▸ hF (e 0)) M (fun b => ?_)
    simpa only [hF0] using hsub e he b
  refine ⟨hint0, ?_⟩

  have hT := key (Z := X) id Function.injective_id
  simp only [id] at hT
  have hsig := (Equiv.sigmaFiberEquiv c).hasSum_iff.mpr hT
  have hg : HasSum (fun y => ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam)
      (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) :=
    hsig.sigma (fun y => key (Z := {x // c x = y}) Subtype.val Subtype.val_injective)

  have hzero : ∀ y, y ≠ y0 → ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam = 0 := by
    intro y hy
    obtain ⟨ν, hν1, hνq⟩ := hν y hy
    refine setIntegral_eq_zero_of_translate lam Λ 𝓖 h𝓖 _ ν (ch ν) hν1 (fun l b => ?_) (fun b => ?_)
    · have hs : ∑' z : {x // c x = y}, F z ((l : A) + b) = ∑' z : {x // c x = y}, F z b := by
        calc ∑' z : {x // c x = y}, F z ((l : A) + b)
            = ∑' z : {x // c x = y}, F (τ l z) b := tsum_congr fun z => hτ l z b
          _ = ∑' z : {x // c x = y}, F z b :=
            ((τ l).subtypeEquiv (p := fun x => c x = y) (q := fun x => c x = y)
              (fun a => by rw [hcτ])).tsum_eq (fun z : {x // c x = y} => F z b)
      rw [hs, hmul, hΛ, one_mul]
    · have hs : ∑' z : {x // c x = y}, F z (ν + b) = ∑' z : {x // c x = y}, F z b :=
        tsum_congr fun z => hνq z z.2 b
      rw [hs, hmul]
      ring
  have hT' := hg.unique (hasSum_single y0 (fun y hy => hzero y hy))
  rw [hT']

  let ee : Λ ≃ {x // c x = y0} := Equiv.ofBijective
    (fun l => ⟨e l, (hfib _).2 ⟨l, rfl⟩⟩)
    ⟨fun a b h => he (congrArg Subtype.val h), fun q => by
      obtain ⟨l, hl⟩ := (hfib q).1 q.2
      exact ⟨l, Subtype.ext hl⟩⟩
  have hsum : ∀ b, ∑' z : {x // c x = y0}, F z b = ∑' l : Λ, F (e l) b := fun b =>
    (ee.tsum_eq (fun z => F z b)).symm
  simp_rw [hsum]
  rw [← (key e he).tsum_eq]
  have hint1 : Integrable (fun b => F0 b * ch b) lam :=
    hint0.mono (hint0.aestronglyMeasurable.mul hch) (ae_of_all _ fun b => by simp [hnorm])
  rw [h𝓖.integral_eq_tsum'' _ hint1]
  refine tsum_congr fun l => ?_
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  change F (e l) b * ch b = F0 ((l : A) + b) * ch ((l : A) + b)
  rw [hF0, hmul, hΛ, one_mul]

end GlobalTheory.CompanionTheory.UnfoldAbs
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCountBound
section
open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Growth

theorem lintegral_le_mul_of_encard_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (M : Set G) (hM : MeasurableSet M) (f : G → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (n : ℕ)
    (hn : ∀ x, Set.encard {γ : Γ | (γ : G) * x ∈ M} ≤ n) :
    ∫⁻ x in M, f x ∂μ ≤ n * ∫⁻ x in 𝓕, f x ∂μ := by
  have hmul : ∀ γ : Γ, Measurable fun x : G => (γ : G) * x := fun γ => measurable_const_mul _
  have hterm : ∀ (γ : Γ) (x : G), M.indicator f (γ • x) =
      f x * (M.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) := by
    intro γ x
    rw [Subgroup.smul_def, smul_eq_mul]
    by_cases hx : (γ : G) * x ∈ M
    · simp [Set.indicator_of_mem hx, hinv γ γ.2 x]
    · simp [Set.indicator_of_notMem hx]
  have hcount : ∀ x : G, ∑' γ : Γ, M.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) ≤ n := by
    intro x
    have h1 : (fun γ : Γ => M.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) =
        ({γ : Γ | (γ : G) * x ∈ M}).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext γ
      by_cases hx : (γ : G) * x ∈ M
      · simp [Set.indicator, hx]
      · simp [Set.indicator, hx]
    rw [h1, ← tsum_subtype, ENNReal.tsum_set_one]
    calc _ ≤ (((n : ℕ∞)) : ℝ≥0∞) := ENat.toENNReal_le.2 (hn x)
      _ = n := by simp
  calc ∫⁻ x in M, f x ∂μ = ∫⁻ x, M.indicator f x ∂μ := (lintegral_indicator hM f).symm
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, M.indicator f (γ • x) ∂μ := h𝓕.lintegral_eq_tsum'' _
    _ = ∫⁻ x in 𝓕, ∑' γ : Γ, M.indicator f (γ • x) ∂μ := by
        rw [lintegral_tsum]
        intro γ
        exact ((hf.indicator hM).comp (hmul γ)).aemeasurable
    _ ≤ ∫⁻ x in 𝓕, n * f x ∂μ := by
        refine lintegral_mono fun x => ?_
        simp only [hterm]
        rw [ENNReal.tsum_mul_left, mul_comm]
        exact mul_le_mul_left (hcount x) _
    _ = n * ∫⁻ x in 𝓕, f x ∂μ := by
        rw [lintegral_const_mul _ hf]

end GlobalTheory.CompanionTheory.Growth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSubgroupRelIndexMul
section
open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.HaarIndex

theorem measure_eq_relIndex_mul : ∀ (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G), H ≤ K →
    MeasurableSet (H : Set G) → H.relIndex K ≠ 0 →
    μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  intro G _ _ _ μ _ H K hHK hH hn
  classical
  set H' := H.addSubgroupOf K
  have hidx : H.relIndex K = H'.index := rfl
  have : H'.FiniteIndex := ⟨by rw [← hidx]; exact hn⟩
  have : Finite (K ⧸ H') := inferInstance
  letI := Fintype.ofFinite (K ⧸ H')
  let o : K ⧸ H' → G := fun q => ((Quotient.out q : K) : G)
  let S : K ⧸ H' → Set G := fun q => (fun x => -o q + x) ⁻¹' (H : Set G)
  have hS : ∀ q, MeasurableSet (S q) := fun q => (measurable_const_add (-o q)) hH
  have hcover : (K : Set G) = ⋃ q, S q := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨((⟨x, hx⟩ : K) : K ⧸ H'), ?_⟩
      have h1 := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' ((⟨x, hx⟩ : K) : K ⧸ H'))
      rw [AddSubgroup.mem_addSubgroupOf] at h1
      simpa [S, o] using h1
    · rintro ⟨q, hq⟩
      have hq' : -o q + x ∈ H := hq
      have hoK : o q ∈ K := (Quotient.out q).2
      have hx : x = o q + (-o q + x) := (add_neg_cancel_left (o q) x).symm
      rw [hx]
      exact K.add_mem hoK (hHK hq')
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro q r hqr
    rw [Function.onFun, Set.disjoint_left]
    intro x hxq hxr
    apply hqr
    have hq' : -o q + x ∈ H := hxq
    have hr' : -o r + x ∈ H := hxr
    have h2 : -o q + o r ∈ H := by
      have := H.add_mem hq' (H.neg_mem hr')
      simpa [neg_add_rev, add_assoc] using this
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' r]
    apply QuotientAddGroup.eq.mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    simpa [o] using h2
  have hμ : ∀ q, μ (S q) = μ (H : Set G) := fun q => MeasureTheory.measure_preimage_add μ (-o q) _
  rw [hcover, MeasureTheory.measure_iUnion hdisj hS, tsum_fintype]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]

end GlobalTheory.CompanionTheory.HaarIndex
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtOfContinuousHom
section
namespace GlobalTheory.CompanionTheory.CharDeriv

theorem hasDerivAt_of_continuous_hom :
    ∀ (χ : ℝ → ℂ), Continuous χ → χ 0 = 1 → (∀ s t, χ (s + t) = χ s * χ t) →
      ∃ c : ℂ, ∀ t, HasDerivAt χ (c * χ t) t := by
  intro χ hc h0 hadd
  have hP : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) (χ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  obtain ⟨δ, hI⟩ : ∃ δ : ℝ, (∫ s in (0 : ℝ)..δ, χ s) ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) = fun _ => (0 : ℂ) := funext h
    have h1 := hP 0
    rw [hz] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at h2
    exact one_ne_zero h2
  have key : ∀ t : ℝ, χ t = ((∫ s in (0 : ℝ)..(t + δ), χ s) - ∫ s in (0 : ℝ)..t, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s) := by
    intro t
    rw [eq_div_iff hI, ← intervalIntegral.integral_const_mul]
    have h1 : (∫ s in (0 : ℝ)..δ, χ t * χ s) = ∫ u in t..(t + δ), χ u := by
      have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := δ) (fun u => χ u) t
      rw [add_zero] at h2
      rw [← h2]
      exact intervalIntegral.integral_congr fun s _ => (hadd t s).symm
    rw [h1]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  refine ⟨(χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s), fun t => ?_⟩
  have hD : HasDerivAt (fun y : ℝ => ((∫ s in (0 : ℝ)..(y + δ), χ s) - ∫ s in (0 : ℝ)..y, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s)) ((χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s)) t := by
    have h3 : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..(y + δ), χ s) (χ (t + δ)) t := by
      simpa using (hP (t + δ)).comp_add_const t δ
    exact (h3.sub (hP t)).div_const _
  have hval : (χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s) * χ t =
      (χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s) := by
    rw [hadd t δ]
    ring
  rw [hval]
  exact hD.congr_of_eventuallyEq (Filter.Eventually.of_forall key)

end GlobalTheory.CompanionTheory.CharDeriv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalOpenStabilizer
section
namespace GlobalTheory.CompanionTheory.Smooth

def linearFormStabiliser {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) : Subgroup G where
  carrier := {g : G | l ∘ₗ ρ g = l}
  mul_mem' := by
    intro a b ha hb
    have ha' : l ∘ₗ ρ a = l := ha
    have hb' : l ∘ₗ ρ b = l := hb
    show l ∘ₗ ρ (a * b) = l
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha', hb']
  one_mem' := by
    show l ∘ₗ ρ 1 = l
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    have ha' : l ∘ₗ ρ a = l := ha
    show l ∘ₗ ρ a⁻¹ = l
    conv_lhs => rw [← ha']
    rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem isOpen_linearForm_stabiliser {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (l : Module.Dual ℂ V)
    (hl : ∀ x ∈ K, l ∘ₗ ρ x = l) : IsOpen {g : G | l ∘ₗ ρ g = l} :=
  Subgroup.isOpen_mono (H₁ := K) (H₂ := linearFormStabiliser ρ l) (fun x hx => hl x hx) hK

end GlobalTheory.CompanionTheory.Smooth
end

