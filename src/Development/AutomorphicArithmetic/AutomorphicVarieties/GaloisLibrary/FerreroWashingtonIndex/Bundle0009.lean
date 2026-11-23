module

public import GroundTheory.GlobalFields.HasseNorm
public import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
public import GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.LocFin
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem ideal_step {R : Type} [CommRing R] [IsDedekindDomain R] (c : R ≃+* R) (P I : Ideal R) (a : R)
    (hP : P ≠ 0) (hI : I ≠ 0) (ha : a ≠ 0) (hc : P.map c = P) (h : I * I.map c = Ideal.span {a}) :
    ∃ b t : R, b * c b = a * t ∧ ∀ w : Ideal R, w.IsPrime → P ≤ w → t ∉ w := by
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_sup_span_eq (I := I * P) (J := I) Ideal.mul_le_left (mul_ne_zero hI hP)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {b} := Ideal.dvd_iff_le.2 (hb ▸ le_sup_right)
  have h1 : P ⊔ J = ⊤ := by
    rw [hJ, ← Ideal.mul_sup] at hb
    have := mul_left_cancel₀ hI (hb.trans (mul_one I).symm)
    rwa [Ideal.one_eq_top] at this
  have h2 : P ⊔ J.map c = ⊤ := by
    have := congrArg (Ideal.map c) h1
    rwa [Ideal.map_sup, hc, Ideal.map_top] at this
  have h3 : Ideal.span {b * c b} = Ideal.span {a} * (J * J.map c) := by
    have := congrArg (Ideal.map c) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_mul] at this
    rw [← Ideal.span_singleton_mul_span_singleton, hJ, this, ← h]; ring
  have h4 : b * c b ∈ Ideal.span {a} :=
    (Ideal.span_singleton_le_iff_mem _).1 (h3 ▸ Ideal.mul_le_left)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 h4
  refine ⟨b, t, ht, fun w hw hPw htw => ?_⟩
  rw [ht, ← Ideal.span_singleton_mul_span_singleton] at h3
  have h5 := mul_left_cancel₀ (by simpa using ha) h3
  have h6 : J * J.map c ≤ w := h5 ▸ (Ideal.span_singleton_le_iff_mem _).2 htw
  rcases hw.mul_le.1 h6 with h7 | h7
  · exact hw.ne_top (top_le_iff.1 (h1 ▸ sup_le hPw h7))
  · exact hw.ne_top (top_le_iff.1 (h2 ▸ sup_le hPw h7))

private theorem norm_cm (K : Type) [Field K] [NumberField K] [IsCMField K] (b : K) :
    algebraMap (maximalRealSubfield K) K (Algebra.norm (maximalRealSubfield K) b) = b * IsCMField.complexConj K b := by
  classical
  have hcard : Fintype.card (K ≃ₐ[maximalRealSubfield K] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.card_top, ← IsCMField.zpowers_complexConj_eq_top, Nat.card_zpowers,
      IsCMField.orderOf_complexConj]
  have hne := (IsCMField.complexConj_ne_one K).symm
  have huniv : (Finset.univ : Finset (K ≃ₐ[maximalRealSubfield K] K)) = {1, IsCMField.complexConj K} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, hcard])).symm
  rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne]
  rfl

theorem UpperTheory.V.FW.locFin :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : (maximalRealSubfield K)ˣ) (a : 𝓞 K) (I : (Ideal (𝓞 K))⁰), UnrFin K → (a : K) = algebraMap (maximalRealSubfield K) K x → (I * idMap (cE K) I).1 = Ideal.span {a} → ∀ v, GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) x) ∈ (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
  intro K _ _ _ x a I hunr hax hI v
  have haK : (a : K) ≠ 0 := by rw [hax]; simp
  have ha : a ≠ 0 := fun h => haK (by rw [h]; rfl)
  obtain ⟨w⟩ := GroundTheory.Global.nonempty_placesOver K v
  have hw : w.1.asIdeal.LiesOver v.asIdeal := inferInstance
  have hP : v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  have hc : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K))).map (RingOfIntegers.mapRingEquiv (cE K)) =
      v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) := by
    have : ((RingOfIntegers.mapRingEquiv (cE K) : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K).comp (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) = algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) := by
      ext y
      exact (IsCMField.complexConj K).commutes (y : maximalRealSubfield K)
    rw [← Ideal.map_coe, Ideal.map_map, this]
  obtain ⟨b, t, hbt, ht⟩ := ideal_step (RingOfIntegers.mapRingEquiv (cE K)) _ I.1 a hP (nonZeroDivisors.ne_zero I.2) ha hc hI
  have htw : t ∉ w.1.asIdeal := ht _ w.1.isPrime (Ideal.map_le_iff_le_comap.2 hw.over.le)
  have ht0 : t ≠ 0 := fun h => htw (h ▸ zero_mem _)
  have hb0 : (b : K) ≠ 0 := by
    intro h
    have : b = 0 := by simpa using h
    rw [this, zero_mul] at hbt
    exact mul_ne_zero ha ht0 hbt.symm
  set n : (maximalRealSubfield K)ˣ := Units.map (Algebra.norm (maximalRealSubfield K)) (Units.mk0 (b : K) hb0) with hn
  have hy : algebraMap (maximalRealSubfield K) K ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K) = (t : K) := by
    have h1 : algebraMap (maximalRealSubfield K) K n = (a : K) * t :=
      (norm_cm K b).trans (congrArg (fun z : 𝓞 K => (z : K)) hbt)
    rw [Units.val_mul, map_mul, h1, Units.val_inv_eq_inv_val, map_inv₀, ← hax]
    field_simp
  have hv : v.valuation (maximalRealSubfield K) ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K) = 1 := by
    have h1 := HeightOneSpectrum.valuation_liesOver K v w.1 ((n * x⁻¹ : (maximalRealSubfield K)ˣ) : maximalRealSubfield K)
    rw [hy, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) w.1).2 htw] at h1
    apply (pow_eq_one_iff.1 h1).resolve_right
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.1.asIdeal v.ne_bot]
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ v.ne_bot
  have h1 : GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) n) ∈
      (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
    rw [hn, ← GroundTheory.Global.ideleNorm_diagonal, GroundTheory.Global.IdeleNorm.finiteProj_ideleNorm]
    exact ⟨_, rfl⟩
  have h2 : GroundTheory.Global.IdeleGroup.finiteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) (n * x⁻¹)) ∈
      (GroundTheory.Global.IdeleNorm.finiteLocalNorm K v).range := by
    refine Subgroup.map_le_range _ (GroundTheory.Global.IdeleNorm.integerUnitsOver K v) ?_
    rw [GroundTheory.Global.IdeleNorm.map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w (hunr w.1)]
    refine HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2 ?_
    rw [GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans hv
  have h3 := mul_mem (inv_mem h2) h1
  rwa [← map_inv, ← map_inv, ← map_mul, ← map_mul, mul_inv_rev, inv_inv, inv_mul_cancel_right] at h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.LocInf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.locInf :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : (maximalRealSubfield K)ˣ), (∀ φ : K →+* ℂ, 0 < (φ (algebraMap (maximalRealSubfield K) K x)).re) → ∀ v, GroundTheory.Global.IdeleGroup.infiniteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) x) ∈ (GroundTheory.Global.IdeleNorm.infiniteLocalNorm K v).range := by
  intro K _ _ _ x hx v
  classical
  obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (k := maximalRealSubfield K) (K := K) v
  set u := W.comap (algebraMap (maximalRealSubfield K) K) with hu_def
  have hWu : W.LiesOver u := { under_eq := rfl }
  have hu : u.IsReal := IsTotallyReal.isReal u
  have hpos : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hu
      (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K)) := by
    have h0 : InfinitePlace.Completion.ringEquivRealOfIsReal hu
        (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K)) =
        InfinitePlace.embedding_of_isReal hu (x : maximalRealSubfield K) := by
      change InfinitePlace.Completion.extensionEmbeddingOfIsReal hu _ = _
      rw [InfinitePlace.Completion.algebraMap_apply]
      exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hu _
    rw [h0]
    have h1 := InfinitePlace.embedding_of_isReal_apply hu (x : maximalRealSubfield K)
    have h3 := hx W.embedding
    rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq W u with h2 | h2
    · have h4 := congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2
      simp only [RingHom.coe_comp, Function.comp_apply] at h4
      rw [h4, ← h1] at h3
      rwa [Complex.ofReal_re] at h3
    · have h4 := congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2
      simp only [RingHom.coe_comp, Function.comp_apply, ComplexEmbedding.conjugate_coe_eq,
        Complex.conj_re] at h4
      rw [h4, ← h1] at h3
      rwa [Complex.ofReal_re] at h3
  letI : Algebra u.Completion W.Completion := AbsoluteValue.Completion.algebraOfLiesOver u.1 W.1
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hu with he
  set a := algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K) with ha
  set d := Module.finrank u.Completion W.Completion with hd_def
  have hd : 0 < d := by
    rcases W.isUnramified_or_isRamified (maximalRealSubfield K) with h | h
    · rw [hd_def, h.finrank_eq_one u]; norm_num
    · rw [hd_def, h.finrank_eq_two u]; norm_num
  set r : u.Completion := e.symm (e a ^ ((d : ℝ)⁻¹)) with hr_def
  have hr : r ^ d = a := by
    apply e.injective
    rw [map_pow, hr_def, RingEquiv.apply_symm_apply, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
      inv_mul_cancel₀ (by exact_mod_cast hd.ne'), Real.rpow_one]
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact (map_ne_zero _).mpr x.ne_zero
  have hr0 : algebraMap u.Completion W.Completion r ≠ 0 := by
    rw [map_ne_zero]
    rintro h0
    rw [h0, zero_pow hd.ne'] at hr
    exact ha0 hr.symm
  let w0 : ↑(InfinitePlace.placesOver K u) := ⟨W, hWu⟩
  refine ⟨Pi.mulSingle w0 (Units.mk0 _ hr0), ?_⟩
  apply Units.ext
  simp only [GroundTheory.Global.IdeleNorm.infiniteLocalNorm, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Fintype.prod_eq_single w0 (fun w hw => by rw [Pi.mulSingle_eq_of_ne hw, map_one]),
    Pi.mulSingle_eq_same, Units.coe_map, Units.val_mk0]
  rw [GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal]
  rw [← InfinitePlace.Completion.algebraMap_apply]
  change Algebra.norm u.Completion (algebraMap u.Completion W.Completion r) = a
  rw [Algebra.norm_algebraMap, ← hd_def, hr]
end

