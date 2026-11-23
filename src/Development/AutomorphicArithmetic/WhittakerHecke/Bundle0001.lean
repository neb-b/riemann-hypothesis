module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.EqZeroAtOneOfFourierIntegralEqZero
section
open MeasureTheory FourierTransform

theorem UpperTheory.eq_zero_at_one_of_fourierIntegral_eq_zero :
    ∀ (G : ℝ → ℂ), MeasureTheory.Integrable G → ContinuousAt G 1 →
        (∀ u : ℝ, ∫ y : ℝ, G y * Complex.exp (2 * Real.pi * Complex.I * ((y * u : ℝ) : ℂ)) = 0) → G 1 = 0 := by
  intro G hG hc h
  have hF : 𝓕 G = 0 := by
    funext w
    have h1 := h (-w)
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [Pi.zero_apply]
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hint : Integrable (𝓕 G) := by rw [hF]; exact integrable_zero _ _ _
  have key := hG.fourierInv_fourier_eq hint hc
  rw [← key, hF]
  simp [Real.fourierInv_eq']
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.EqZeroOfOrthogonalEvenHomogeneousTrig
section
open Complex MeasureTheory

private lemma UpperTheory.fourier_vanishing_homogeneous (F : ℝ → ℂ) (hc : Continuous F) (hp : ∀ t, F (t + Real.pi) = F t)
    (h : ∀ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous (2 * e) →
      ∫ t in (0 : ℝ)..2 * Real.pi,
        MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p * F t = 0)
    (s : ℂ) (hs : s = 1 ∨ s = -1) (k : ℕ) :
    ∫ t in (0 : ℝ)..2 * Real.pi, cexp (s * (2 * k) * (t * I)) * F t = 0 := by
  have hhom : ((MvPolynomial.X 1 + MvPolynomial.C (s * I) * MvPolynomial.X 0 :
      MvPolynomial (Fin 2) ℂ) ^ (2 * k)).IsHomogeneous (2 * k) := by
    have h1 : (MvPolynomial.X 1 + MvPolynomial.C (s * I) * MvPolynomial.X 0 :
        MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
      (MvPolynomial.isHomogeneous_X ℂ 1).add (MvPolynomial.isHomogeneous_C_mul_X _ _)
    simpa using h1.pow (2 * k)
  have := h k _ hhom
  rw [← this]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have he : cexp (s * (t * I)) = (Real.cos t : ℂ) + s * I * (Real.sin t : ℂ) := by
    rcases hs with rfl | rfl
    · rw [one_mul, exp_mul_I]; push_cast; ring
    · have : (-1 : ℂ) * (t * I) = ((-t : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]
      push_cast; ring
  have hpow : cexp (s * (2 * k) * (t * I)) = cexp (s * (t * I)) ^ (2 * k) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  simp only [map_pow, map_add (f := _), map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [hpow, he]

theorem UpperTheory.eq_zero_of_orthogonal_even_homogeneous_trig :
    ∀ (F : ℝ → ℂ), Continuous F → (∀ t, F (t + Real.pi) = F t) →
        (∀ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous (2 * e) →
          ∫ t in (0 : ℝ)..2 * Real.pi, MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p * F t = 0) →
        ∀ t, F t = 0 := by
  intro F hc hp h
  haveI : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩
  have hper : Function.Periodic F Real.pi := hp
  let f : C(AddCircle Real.pi, ℂ) :=
    ⟨hper.lift, (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hc⟩
  have hfx : ∀ x : ℝ, f (x : AddCircle Real.pi) = F x := fun x => hper.lift_coe x

  have hint : ∀ n : ℤ, ∫ t in (0 : ℝ)..Real.pi, cexp ((-(2 * n : ℂ)) * (t * I)) * F t = 0 := by
    intro n
    have hG : Function.Periodic (fun t : ℝ => cexp ((-(2 * n : ℂ)) * (t * I)) * F t) Real.pi := by
      intro t
      have h1 : cexp ((-(2 * n : ℂ)) * (((t + Real.pi : ℝ) : ℂ) * I)) =
          cexp ((-(2 * n : ℂ)) * (t * I)) := by
        have : (-(2 * n : ℂ)) * (((t + Real.pi : ℝ) : ℂ) * I) =
            (-(2 * n : ℂ)) * (t * I) + ((-n : ℤ) : ℂ) * (2 * Real.pi * I) := by
          push_cast; ring
        rw [this, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
      simp only [h1, hp]
    have hcont : Continuous (fun t : ℝ => cexp ((-(2 * n : ℂ)) * (t * I)) * F t) := by
      fun_prop
    have hsplit : ∫ t in (0 : ℝ)..2 * Real.pi, cexp ((-(2 * n : ℂ)) * (t * I)) * F t =
        2 * ∫ t in (0 : ℝ)..Real.pi, cexp ((-(2 * n : ℂ)) * (t * I)) * F t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable 0 Real.pi) (hcont.intervalIntegrable Real.pi (2 * Real.pi))]
      have := hG.intervalIntegral_add_eq Real.pi 0
      rw [show Real.pi + Real.pi = 2 * Real.pi by ring, zero_add] at this
      rw [this]; ring
    have hz : ∫ t in (0 : ℝ)..2 * Real.pi, cexp ((-(2 * n : ℂ)) * (t * I)) * F t = 0 := by
      rcases le_total 0 n with hn | hn
      · have := UpperTheory.fourier_vanishing_homogeneous F hc hp h (-1) (Or.inr rfl) n.toNat
        have e : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hn)
        rw [e] at this
        rw [← this]
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [neg_mul, one_mul]
      · have := UpperTheory.fourier_vanishing_homogeneous F hc hp h 1 (Or.inl rfl) (-n).toNat
        have e : (((-n).toNat : ℕ) : ℂ) = -(n : ℂ) := by
          have h2 : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (neg_nonneg.2 hn)
          rw [← Int.cast_natCast, h2, Int.cast_neg]
        rw [e] at this
        rw [← this]
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [one_mul, mul_neg]
    rw [hz] at hsplit
    exact (mul_eq_zero.1 hsplit.symm).resolve_left two_ne_zero
  have hF : ∀ n : ℤ, fourierCoeff f n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
    have e : ∀ x : ℝ, fourier (-n) (x : AddCircle Real.pi) • f (x : AddCircle Real.pi) =
        cexp ((-(2 * n : ℂ)) * (x * I)) * F x := by
      intro x
      have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
      rw [fourier_coe_apply, smul_eq_mul, hfx]
      congr 2
      push_cast
      field_simp
    simp only [e]
    rw [hint n, smul_zero]
  have hsum : Summable (fourierCoeff f) := by
    rw [show fourierCoeff f = 0 from funext hF]
    exact summable_zero
  intro t
  have hs := has_pointwise_sum_fourier_series_of_summable hsum (t : AddCircle Real.pi)
  simp only [hF, zero_smul] at hs
  rw [← hfx]
  exact hs.unique hasSum_zero
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IntegrableAndContinuousMellinIntegralOfRapidDeca
section
open MeasureTheory Set

private lemma integrable_weight {a : ℝ} (ha : -1 < a) {r : ℕ} (hr : a + 1 < r) :
    Integrable fun y : ℝ => ((1 + |y|) ^ r)⁻¹ * |y| ^ a := by
  set f : ℝ → ℝ := fun x => ((1 + x) ^ r)⁻¹ * x ^ a with hf
  have hmeas : Measurable f := by
    rw [hf]; fun_prop
  have h : IntegrableOn f (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
    refine IntegrableOn.union ?_ ?_
    · have h1 : IntegrableOn (fun x : ℝ => x ^ a) (Ioc 0 1) := by
        have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) ha
        rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
      refine Integrable.mono' h1 hmeas.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 < x := hx.1
      have hp : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le _
      have hq : ((1 + x) ^ r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
      rw [Real.norm_of_nonneg (by rw [hf]; positivity)]
      calc f x ≤ 1 * x ^ a := mul_le_mul_of_nonneg_right hq hp
        _ = x ^ a := one_mul _
    · have h1 : IntegrableOn (fun x : ℝ => x ^ (a - r)) (Ioi 1) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
      refine Integrable.mono' h1 hmeas.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1 : ℝ) < x := hx
      have hx0 : 0 < x := lt_trans one_pos hx1
      have hp : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le _
      have hq : ((1 + x) ^ r)⁻¹ ≤ (x ^ r)⁻¹ := by
        gcongr
        linarith
      rw [Real.norm_of_nonneg (by rw [hf]; positivity), Real.rpow_sub hx0, Real.rpow_natCast,
        div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right hq hp
  have hG : Integrable ((Ioi (0 : ℝ)).indicator f) :=
    (integrable_indicator_iff measurableSet_Ioi).2 h
  have hsum := hG.add hG.comp_neg
  refine hsum.congr ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with y hy
  have hy0 : y ≠ 0 := hy
  rcases lt_or_gt_of_ne hy0 with h0 | h0
  · have h1 : y ∉ Ioi (0 : ℝ) := by simp [h0.le]
    have h2 : -y ∈ Ioi (0 : ℝ) := by simpa using h0
    simp only [Pi.add_apply, indicator_of_notMem h1, indicator_of_mem h2, zero_add, abs_of_neg h0,
      hf]
  · have h1 : y ∈ Ioi (0 : ℝ) := h0
    have h2 : -y ∉ Ioi (0 : ℝ) := by simp [h0.le]
    simp only [Pi.add_apply, indicator_of_mem h1, indicator_of_notMem h2, add_zero, abs_of_pos h0,
      hf]

private lemma continuousOn_weight (k : ℕ) (z : ℂ) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ z) ({0}ᶜ : Set ℝ) := by
  refine ContinuousOn.mul (by fun_prop) ?_
  intro y hy
  have hy0 : 0 < |y| := abs_pos.2 hy
  have h1 : ((|y| : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hy0
  have h2 : ContinuousAt (fun y : ℝ => ((|y| : ℝ) : ℂ)) y := by fun_prop
  exact (ContinuousAt.comp (f := fun y : ℝ => ((|y| : ℝ) : ℂ)) (g := fun w : ℂ => w ^ z)
    (continuousAt_cpow_const h1) h2).continuousWithinAt

theorem UpperTheory.integrable_and_continuous_mellinIntegral_of_rapidDecay :
    ∀ (W : ℝ → ℝ → ℂ) (c : ℝ → ℂ) (k : ℕ) (s : ℂ),
        ContinuousOn (fun p : ℝ × ℝ => W p.1 p.2) (({0}ᶜ : Set ℝ) ×ˢ Set.univ) →
        ContinuousOn c ({0}ᶜ : Set ℝ) → (∀ y, ‖c y‖ = 1) →
        (∀ r : ℕ, ∃ B : ℝ, ∀ y t, y ≠ 0 → ‖W y t‖ ≤ B * ((1 + |y|) ^ r)⁻¹) →
        1 - (k : ℝ) < s.re →
        (∀ t, MeasureTheory.Integrable fun y : ℝ => W y t * c y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)) ∧
        Continuous fun t => ∫ y : ℝ, W y t * c y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2) := by
  intro W c k s hW hc hc1 hdec hs
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = k + s.re - 2 := ⟨_, rfl⟩
  have ha : -1 < a := by rw [hadef]; linarith
  obtain ⟨r, hr⟩ := exists_nat_gt (a + 1)
  obtain ⟨B, hB⟩ := hdec r
  have hae : ∀ᵐ y : ℝ, y ∈ ({0}ᶜ : Set ℝ) := compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))
  have hint : Integrable fun y : ℝ => |B| * (((1 + |y|) ^ r)⁻¹ * |y| ^ a) :=
    (integrable_weight ha hr).const_mul _
  have hnorm : ∀ t, ∀ᵐ y : ℝ,
      ‖W y t * c y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)‖
        ≤ |B| * (((1 + |y|) ^ r)⁻¹ * |y| ^ a) := by
    intro t
    filter_upwards [hae] with y hy
    have hy0 : 0 < |y| := abs_pos.2 hy
    have hw : ‖(y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)‖ = |y| ^ a := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hy0, hadef, ← Real.rpow_natCast,
        ← Real.rpow_add hy0]
      congr 1
      simp only [Complex.sub_re, Complex.re_ofNat]
      ring
    have hp : 0 ≤ |y| ^ a := Real.rpow_nonneg hy0.le _
    have hinv : 0 ≤ ((1 + |y|) ^ r)⁻¹ := by positivity
    rw [mul_assoc, norm_mul, norm_mul, hc1, mul_one, hw]
    calc ‖W y t‖ * |y| ^ a ≤ (B * ((1 + |y|) ^ r)⁻¹) * |y| ^ a :=
          mul_le_mul_of_nonneg_right (hB y t hy) hp
      _ ≤ (|B| * ((1 + |y|) ^ r)⁻¹) * |y| ^ a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self B) hinv) hp
      _ = |B| * (((1 + |y|) ^ r)⁻¹ * |y| ^ a) := by ring
  have hmeas : ∀ t, AEStronglyMeasurable
      (fun y : ℝ => W y t * c y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)) volume := by
    intro t
    have h1 : ContinuousOn (fun y : ℝ => W y t) ({0}ᶜ : Set ℝ) :=
      ContinuousOn.comp (g := fun p : ℝ × ℝ => W p.1 p.2) (f := fun y : ℝ => (y, t)) hW
        (by fun_prop) (fun y hy => ⟨hy, trivial⟩)
    have h2 : ContinuousOn
        (fun y : ℝ => W y t * c y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)) ({0}ᶜ : Set ℝ) := by
      refine ((h1.mul hc).mul (continuousOn_weight k (s - 2))).congr ?_
      intro y _
      simp only [Pi.mul_apply, mul_assoc]
    have h3 := h2.aestronglyMeasurable (μ := volume) isOpen_compl_singleton.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at h3
  refine ⟨fun t => Integrable.mono' hint (hmeas t) (hnorm t), ?_⟩
  refine continuous_of_dominated hmeas hnorm hint ?_
  filter_upwards [hae] with y hy
  have h1 : Continuous fun t : ℝ => W y t :=
    hW.comp_continuous (f := fun t : ℝ => (y, t)) (by fun_prop) (fun t => ⟨hy, trivial⟩)
  exact ((h1.mul continuous_const).mul continuous_const).mul continuous_const
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IsAffineOpenImagePullbackOpenImmersionChart
section
open CategoryTheory Limits AlgebraicGeometry TensorProduct

private lemma chart_open {X W E : Scheme.{0}} (π : W ⟶ X) (N : X.Opens) (hN : IsAffineOpen N)
    {S C T : CommRingCat.{0}} (φ : S ⟶ Γ(X, N)) (τ : E ⟶ Spec S)
    (q : (π ⁻¹ᵁ N).toScheme ⟶ E)
    (hq : IsPullback q (π ∣_ N) τ (hN.isoSpec.hom ≫ Spec.map φ))
    (χ : S ⟶ C) (c : Spec C ⟶ E) [IsOpenImmersion c] (hc : c ≫ τ = Spec.map χ)
    (l : Γ(X, N) ⟶ T) (r : C ⟶ T) (hpo : IsPushout φ χ l r) :
    ∃ (ι' : Spec T ⟶ (π ⁻¹ᵁ N).toScheme) (_ : IsOpenImmersion ι'),
      ι'.opensRange = q ⁻¹ᵁ c.opensRange ∧ ι' ≫ q = Spec.map r ≫ c ∧
      ι' ≫ (π ∣_ N) = Spec.map l ≫ hN.isoSpec.inv := by
  have L := IsPullback.of_hasPullback q c
  have big := L.paste_horiz hq.flip
  rw [hc] at big
  have hS := isPullback_SpecMap_of_isPushout φ χ l r hpo
  have sq : IsPullback hN.isoSpec.inv (Spec.map φ) (hN.isoSpec.hom ≫ Spec.map φ) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hS' := hS.paste_horiz sq
  rw [Category.comp_id] at hS'
  let e := IsPullback.isoIsPullback _ _ hS' big
  refine ⟨e.hom ≫ pullback.fst q c, inferInstance, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc,
      IsPullback.isoIsPullback_hom_snd]
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_fst]

private lemma chart_ring {X W : Scheme.{0}} (π : W ⟶ X) (N : X.Opens) (hN : IsAffineOpen N)
    {S C T : CommRingCat.{0}} (φ : S ⟶ Γ(X, N)) (χ : S ⟶ C)
    (l : Γ(X, N) ⟶ T) (r : C ⟶ T) (hpo : IsPushout φ χ l r)
    (ι : Spec T ⟶ W) [IsOpenImmersion ι] (hι : ι ≫ π = Spec.map l ≫ hN.fromSpec)
    (V : W.Opens) (hV : V = ι ''ᵁ ⊤) (hle : V ≤ π ⁻¹ᵁ N) :
    ∃ ρ : C ⟶ Γ(W, V), IsPushout φ χ (π.appLE N V hle) ρ ∧
      ∀ f : C, ι ''ᵁ (PrimeSpectrum.basicOpen (r.hom f)) = W.basicOpen (ρ.hom f) := by
  subst hV
  have hVa : IsAffineOpen (ι ''ᵁ ⊤) := (isAffineOpen_top (Spec T)).image_of_isOpenImmersion ι
  let θ : Γ(W, ι ''ᵁ ⊤) ≅ T := ι.appIso ⊤ ≪≫ Scheme.ΓSpecIso T
  have key1 : Spec.map θ.hom ≫ hVa.fromSpec = ι := by
    have h0 := IsAffineOpen.SpecMap_appLE_fromSpec ι hVa (isAffineOpen_top (Spec T))
      (ι.preimage_image_eq ⊤).ge
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h0
    simp only [θ, Iso.trans_hom, Spec.map_comp, Category.assoc, Scheme.Hom.appIso_hom']
    rw [h0, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  have key2 : π.appLE N (ι ''ᵁ ⊤) hle ≫ θ.hom = l := by
    apply Spec.map_injective
    rw [← cancel_mono hN.fromSpec, Spec.map_comp, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec π hN hVa hle, ← Category.assoc, key1, hι]
  refine ⟨r ≫ θ.inv, ?_, ?_⟩
  · refine hpo.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) θ.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [← key2]
      simp
    · simp
  · intro f
    rw [← basicOpen_eq_of_affine, Scheme.image_basicOpen]
    rfl

theorem UpperTheory.isAffineOpen_image_pullback_openImmersion_chart :
    ∀ {S C : Type} [CommRing S] [CommRing C] {X W E : Scheme.{0}} (π : W ⟶ X) (N : X.Opens)
        (hN : IsAffineOpen N) (φ : S →+* Γ(X, N)) (τ : E ⟶ Spec (CommRingCat.of S))
        (q : (π ⁻¹ᵁ N).toScheme ⟶ E)
        (_ : IsPullback q (π ∣_ N) τ (hN.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ)))
        (χ : S →+* C) (c : Spec (CommRingCat.of C) ⟶ E) [IsOpenImmersion c]
        (_ : c ≫ τ = Spec.map (CommRingCat.ofHom χ)),
        IsAffineOpen ((π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange)) ∧
        ∃ (hle : (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange) ≤ π ⁻¹ᵁ N)
          (ρ : C →+* Γ(W, (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange))),
          IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom χ) (Scheme.Hom.appLE π N _ hle) (CommRingCat.ofHom ρ) ∧
          ∀ (O : E.Opens) (f : C), c ⁻¹ᵁ O = PrimeSpectrum.basicOpen f →
            (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange) ⊓ (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ O) = W.basicOpen (ρ f) := by
  intro S C _ _ X W E π N hN φ τ q hq χ c _ hc
  obtain ⟨ι', _, hr, hq', hπ'⟩ := chart_open π N hN (CommRingCat.ofHom φ) τ q hq (CommRingCat.ofHom χ) c hc
    (pushout.inl (CommRingCat.ofHom φ) (CommRingCat.ofHom χ))
    (pushout.inr (CommRingCat.ofHom φ) (CommRingCat.ofHom χ)) (IsPushout.of_hasPushout _ _)
  have hι : (ι' ≫ (π ⁻¹ᵁ N).ι) ≫ π =
      Spec.map (pushout.inl (CommRingCat.ofHom φ) (CommRingCat.ofHom χ)) ≫ hN.fromSpec := by
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hπ', Category.assoc]
    rfl
  have hV : (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange) = (ι' ≫ (π ⁻¹ᵁ N).ι) ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp, hr]
  have hle : (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange) ≤ π ⁻¹ᵁ N := (π ⁻¹ᵁ N).ι_image_le _
  obtain ⟨ρ, hpo, hb⟩ := chart_ring π N hN (CommRingCat.ofHom φ) (CommRingCat.ofHom χ) _ _
    (IsPushout.of_hasPushout _ _) (ι' ≫ (π ⁻¹ᵁ N).ι) hι _ hV hle
  refine ⟨?_, hle, ρ.hom, ?_, ?_⟩
  · rw [hV]
    exact (isAffineOpen_top _).image_of_isOpenImmersion _
  · simpa using hpo
  · intro O f hO
    have hbo : (PrimeSpectrum.basicOpen ((pushout.inr (CommRingCat.ofHom φ) (CommRingCat.ofHom χ)).hom f) :
        (Spec _).Opens) = ι' ⁻¹ᵁ q ⁻¹ᵁ O := by
      rw [← Scheme.Hom.comp_preimage, hq', Scheme.Hom.comp_preimage, hO]
      ext x
      exact Iff.rfl
    rw [← hb f, hbo]
    have hinj := (π ⁻¹ᵁ N).ι.isOpenEmbedding.injective
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_image, Scheme.Hom.coe_image, Scheme.Hom.coe_image, ← hr,
      ← Set.image_inter hinj, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
    congr 1
    rw [← Scheme.Hom.coe_image, Scheme.Hom.image_preimage_eq_opensRange_inf]
    rfl
end

