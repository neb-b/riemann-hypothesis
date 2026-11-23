module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0040
public import Formalism.LatticeTheta.ThetaShiftInversion

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalPowersAtPlacesIndexLe
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain in
private theorem exists_valuation_natCast_eq_exp_neg_and_dvd {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : 0 < p) :
    ∃ e : ℕ, HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-(e : ℤ)) ∧
      v.asIdeal ^ e ∣ Ideal.span {(p : 𝓞 F)} := by
  have hval : HeightOneSpectrum.valuation F v (p : F) = v.intValuation (p : 𝓞 F) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    simp
  have hne : v.intValuation (p : 𝓞 F) ≠ 0 :=
    v.intValuation_ne_zero _ (by exact_mod_cast hp.ne')
  have hle : v.intValuation (p : 𝓞 F) ≤ 1 := v.intValuation_le_one _
  set a := v.intValuation (p : 𝓞 F) with ha
  have hlog : WithZero.log a ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hne, WithZero.exp_zero]
    exact hle
  refine ⟨(-WithZero.log a).toNat, ?_, ?_⟩
  · rw [hval, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd, Int.toNat_of_nonneg (by omega), neg_neg,
      WithZero.exp_log hne]

open NumberField IsDedekindDomain in
private theorem powSub_eq_comap_pows_units_map {F L : Type} [Field F] [Field L] {p : ℕ} (hp : 0 < p)
    (φ : F →+* L) :
    _root_.GlobalTheory.CNorm.powSub p φ =
      (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)).comap (Units.map φ.toMonoidHom) := by
  ext x
  rw [_root_.GlobalTheory.CNorm.mem_powSub, Subgroup.mem_comap]
  unfold _root_.GlobalTheory.CNorm.pows
  simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, powMonoidHom_apply]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne'] at hr
      exact (map_ne_zero φ).2 x.ne_zero hr.symm
    exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr)⟩
  · rintro ⟨y, hy⟩
    refine ⟨(y : L), ?_⟩
    have := congrArg Units.val hy
    simpa using this

open NumberField IsDedekindDomain in
private theorem powSub_index_ne_zero_and_le_pIdx {F L : Type} [Field F] [Field L] {p : ℕ} (hp : 0 < p)
    (φ : F →+* L) (h : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) ≠ 0) :
    (_root_.GlobalTheory.CNorm.powSub p φ).index ≠ 0 ∧
      (_root_.GlobalTheory.CNorm.powSub p φ).index ≤ _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) := by
  have hdef : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) = (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)).index := by
    unfold _root_.GlobalTheory.CNorm.pIdx
    exact Subgroup.relIndex_top_right _
  rw [hdef] at h ⊢
  rw [powSub_eq_comap_pows_units_map hp, Subgroup.index_comap]
  have hd := Subgroup.relIndex_dvd_index_of_normal (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ))
    (Units.map φ.toMonoidHom).range
  exact ⟨ne_zero_of_dvd_ne_zero h hd, Nat.le_of_dvd (Nat.pos_of_ne_zero h) hd⟩

open NumberField IsDedekindDomain in
private theorem pTor_units_le {L : Type} [Field L] {p : ℕ} (hp : 0 < p) :
    _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup Lˣ) ≤ p := by
  unfold _root_.GlobalTheory.CNorm.pTor
  classical
  have hinj : Function.Injective (fun x : {x : Lˣ // x ∈ (⊤ : Subgroup Lˣ) ∧ x ^ p = 1} =>
      (⟨(x.1 : L), by
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hp, ← Units.val_pow_eq_pow_val, x.2.2,
          Units.val_one]⟩ : (Polynomial.nthRoots p (1 : L)).toFinset)) := by
    intro x y hxy
    exact Subtype.ext (Units.ext (congrArg Subtype.val hxy))
  calc Nat.card {x : Lˣ // x ∈ (⊤ : Subgroup Lˣ) ∧ x ^ p = 1}
      ≤ Nat.card (Polynomial.nthRoots p (1 : L)).toFinset := Nat.card_le_card_of_injective _ hinj
    _ = (Polynomial.nthRoots p (1 : L)).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ (Polynomial.nthRoots p (1 : L)).card := Multiset.toFinset_card_le _
    _ ≤ p := Polynomial.card_nthRoots p 1

open NumberField IsDedekindDomain in
private theorem prod_absNorm_pow_le_pow_finrank {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {p : ℕ} (hp : 0 < p) (e : HeightOneSpectrum (𝓞 F) → ℕ)
    (he : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(p : 𝓞 F)}) :
    ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ p ^ Module.finrank ℚ F := by
  have hdvd : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(p : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ he
    intro v _ w _ hvw
    have hne : v.asIdeal ≠ w.asIdeal := fun h => hvw (HeightOneSpectrum.ext h)
    exact (Ideal.isCoprime_iff_sup_eq.mpr
      (Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal hne)).pow
  have hnorm : Ideal.absNorm (Ideal.span {(p : 𝓞 F)}) = p ^ Module.finrank ℚ F := by
    rw [Ideal.absNorm_span_singleton]
    have : (p : 𝓞 F) = algebraMap ℤ (𝓞 F) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp
  have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
  rw [hnorm, map_prod] at h
  simp only [map_pow] at h
  exact Nat.le_of_dvd (pow_pos hp _) h


open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
theorem _root_.GlobalTheory.CNorm.index_finPow_le : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F]
    [_root_.NumberField.IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F))), 0 < p →
    (_root_.GlobalTheory.CNorm.finPow p F S).index ≠ 0 ∧
      (_root_.GlobalTheory.CNorm.finPow p F S).index ≤
        p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
  intro p F _ _ _ S hp
  choose! e he hdiv using fun v : HeightOneSpectrum (𝓞 F) => exists_valuation_natCast_eq_exp_neg_and_dvd v hp
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧
        (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≤
          p * Ideal.absNorm v.asIdeal ^ e v * p := by
    intro v
    obtain ⟨ht, hrel⟩ :=
      _root_.GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion p F v (e v) (v.adicCompletion F) hp (he v)
    rw [Module.finrank_self, pow_one] at hrel
    have hN : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have hne : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup (v.adicCompletion F)ˣ) ≠ 0 := by
      rw [hrel]
      exact mul_ne_zero (mul_ne_zero hp.ne' (pow_ne_zero _ hN)) ht
    obtain ⟨h1, h2⟩ := powSub_index_ne_zero_and_le_pIdx hp (algebraMap F (v.adicCompletion F)) hne
    refine ⟨h1, h2.trans ?_⟩
    rw [hrel]
    exact Nat.mul_le_mul_left _ (pTor_units_le hp)
  have hinf : _root_.GlobalTheory.CNorm.finPow p F S =
      ⨅ v : S, _root_.GlobalTheory.CNorm.powSub p
        (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) := by
    unfold _root_.GlobalTheory.CNorm.finPow
    rw [iInf_subtype']
  rw [hinf]
  refine ⟨Subgroup.index_iInf_ne_zero fun v => (hloc v).1, (Subgroup.index_iInf_le _).trans ?_⟩
  calc ∏ v : S, (_root_.GlobalTheory.CNorm.powSub p
          (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))).index
      ≤ ∏ v : S, (p * Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v * p) :=
        Finset.prod_le_prod' fun v _ => (hloc v).2
    _ = p ^ (2 * S.card) * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v := by
        rw [Finset.prod_coe_sort S (fun v => p * Ideal.absNorm v.asIdeal ^ e v * p)]
        simp only [Finset.prod_mul_distrib, Finset.prod_const]
        ring
    _ ≤ p ^ (2 * S.card) * p ^ Module.finrank ℚ F :=
        Nat.mul_le_mul_left _ (prod_absNorm_pow_le_pow_finrank S hp e fun v _ => hdiv v)
    _ = p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
        rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
          IsTotallyComplex.nrRealPlaces_eq_zero, ← pow_add]
        ring_nf

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ZlatticeTsumDilateSubIntegralLeRapid
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open scoped FourierTransform RealInnerProductSpace SchwartzMap

namespace GlobalTheory

theorem fourier_comp_smul_of_pos {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (f : V → ℂ) {t : ℝ} (ht : 0 < t)
    (w : V) :
    (𝓕 (fun x => f (t • x)) : V → ℂ) w
      = (((t ^ Module.finrank ℝ V)⁻¹ : ℝ) : ℂ) * (𝓕 f : V → ℂ) (t⁻¹ • w) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  have h := Measure.integral_comp_smul (volume : Measure V)
    (fun u : V => cexp (((-2 * Real.pi * ⟪u, t⁻¹ • w⟫ : ℝ) : ℂ) * I) • f u) t
  rw [abs_of_pos (by positivity), Complex.real_smul] at h
  rw [← h]
  congr 1
  ext v
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc t, mul_inv_cancel₀ ht.ne', one_mul]

theorem latticeSum_dilate_sub_integral_le (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (A : ℕ) :
    ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 →
      ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x) /
        ((ZLattice.covolume L * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  obtain ⟨hD, -⟩ := Formalism.H.dualIsLattice V L
  set d := Module.finrank ℝ V with hd
  set k := A + d + Module.finrank ℤ (Formalism.H.dual L) + 1 with hk
  set F : 𝓢(V, ℂ) := hc.toSchwartzMap hf with hF
  have hFf : (F : V → ℂ) = f := rfl
  obtain ⟨C, hC0, hC⟩ := (𝓕 F : 𝓢(V, ℂ)).decay k 0
  have hs := ZLattice.summable_norm_pow_inv (Formalism.H.dual L) k (by omega)
  have hcov : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  refine ⟨(ZLattice.covolume L)⁻¹ * (C * ∑' y : Formalism.H.dual L, ‖y‖⁻¹ ^ k), ?_⟩
  intro x₀ t ht ht1
  have hft : ContDiff ℝ ∞ (fun x : V => f (t • x)) := hf.comp (contDiff_const_smul t)
  have hct : HasCompactSupport (fun x : V => f (t • x)) :=
    hc.comp_homeomorph (Homeomorph.smulOfNeZero t ht.ne')
  obtain ⟨G, hG⟩ : ∃ G : 𝓢(V, ℂ), (G : V → ℂ) = fun x : V => f (t • x) :=
    ⟨hct.toSchwartzMap hft, rfl⟩
  obtain ⟨h1, h2⟩ := Formalism.H.poissonSchwartz V L G x₀
  rw [hG] at h1 h2
  rw [h2.tsum_eq, h1.tsum_eq_add_tsum_ite 0]
  have h0 : (𝓕 (fun x : V => f (t • x)) : V → ℂ) ((0 : Formalism.H.dual L) : V) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪((0 : Formalism.H.dual L) : V), x₀⟫ : ℝ))
      = (((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x := by
    rw [fourier_comp_smul_of_pos f ht, Real.fourier_eq']
    simp [hd]
  rw [h0, mul_add]
  have h3 : ∀ S : ℂ, (ZLattice.covolume L : ℂ)⁻¹ * ((((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x) + S -
      (∫ x, f x) / ((ZLattice.covolume L * t ^ d : ℝ) : ℂ) = S := by
    intro S
    push_cast
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [h3, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcov.le,
    mul_assoc (ZLattice.covolume L volume)⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hcov.le)
  rw [← tsum_mul_left, ← tsum_mul_right]
  refine tsum_of_norm_bounded (((hs.mul_left C).mul_right (t ^ A)).hasSum) ?_
  intro y
  split_ifs with hy
  · rw [norm_zero]; positivity
  have hn : 0 < ‖(y : V)‖ := norm_pos_iff.2 (fun h => hy (Subtype.ext h))
  have he : ‖Complex.exp (2 * Real.pi * Complex.I * (⟪(y : V), x₀⟫ : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [norm_mul, he, mul_one, fourier_comp_smul_of_pos f ht, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have h4 := hC (t⁻¹ • (y : V))
  rw [norm_iteratedFDeriv_zero, _root_.norm_smul, Real.norm_of_nonneg (by positivity),
    SchwartzMap.fourier_coe, hFf] at h4
  change _ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ A
  have h5 : ‖(𝓕 f : V → ℂ) (t⁻¹ • (y : V))‖ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ k := by
    rw [mul_comm, ← le_div_iff₀ (by positivity)] at h4
    refine h4.trans_eq ?_
    rw [mul_pow, inv_pow, inv_pow]
    field_simp
  have h6 : t ^ k ≤ t ^ (A + d) := pow_le_pow_of_le_one ht.le ht1 (by omega)
  calc (t ^ d)⁻¹ * ‖(𝓕 f : V → ℂ) (t⁻¹ • (y : V))‖
      ≤ (t ^ d)⁻¹ * (C * ‖(y : V)‖⁻¹ ^ k * t ^ (A + d)) := by
        refine mul_le_mul_of_nonneg_left (h5.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by rw [pow_add t A d]; field_simp

end GlobalTheory
end

