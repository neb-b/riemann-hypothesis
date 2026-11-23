module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.NT
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize.RayDegree

section General

variable {R : Type} [CommRing R] [IsDedekindDomain R] {m : Ideal R}

theorem isCoprime_span {a : R} (ha : a - 1 ∈ m) : IsCoprime (Ideal.span {a}) m :=
  Ideal.isCoprime_iff_exists.mpr ⟨a, Ideal.mem_span_singleton_self a, -(a - 1), m.neg_mem ha, by ring⟩

theorem exists_mem_sub_one {I : Ideal R} (hI0 : I ≠ ⊥) (h : IsCoprime I m) : ∃ a ∈ I, a ≠ 0 ∧ a - 1 ∈ m := by
  by_cases ht : m = ⊤
  · obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    exact ⟨a, haI, ha0, by simp [ht]⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp h
  have h1 : a - 1 ∈ m := by
    have : a - 1 = -b := by rw [← hab]; ring
    rw [this]
    exact m.neg_mem hb
  refine ⟨a, ha, ?_, h1⟩
  rintro rfl
  apply ht
  rw [Ideal.eq_top_iff_one]
  simpa using m.neg_mem h1

theorem exists_good {I J : Ideal R} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) (hI : IsCoprime I m) (hJ : IsCoprime J m)
    {x y : R} (hy : y ≠ 0) (h : Ideal.span {x} * I = Ideal.span {y} * J) :
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ m ∧ IsCoprime (Ideal.span {b}) m ∧
      Ideal.span {a} * I = Ideal.span {b} * J := by
  obtain ⟨a, haJ, ha0, ha⟩ := exists_mem_sub_one hJ0 hJ
  have h1 : y * a ∈ Ideal.span {x} * I := by
    rw [h]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self y) haJ
  obtain ⟨b, -, hb⟩ := Ideal.mem_span_singleton_mul.mp h1
  have h2 : Ideal.span {a} * I = Ideal.span {b} * J := by
    have hy' : (Ideal.span {y} : Ideal R) ≠ 0 := by simpa using hy
    apply mul_left_cancel₀ hy'
    rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, ← hb, mul_left_comm, ← h, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, mul_comm b x]
  refine ⟨a, b, ha0, ?_, ha, ?_, h2⟩
  · rintro rfl
    simp [ha0, hI0] at h2
  · have := (isCoprime_span ha).mul_left hI
    rw [h2] at this
    exact this.of_mul_left_left

end General

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {𝔮 : Ideal (𝓞 K)}

theorem emb_ne_zero (φ : K →+* ℝ) {a : 𝓞 K} (ha : a ≠ 0) : φ (a : K) ≠ 0 := by
  simpa using ha

theorem heckeIdeal_eq_of_ray (hR : IsRay L 𝔮) {I J : Ideal (𝓞 K)} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥)
    (hI : IsCoprime I 𝔮) (hJ : IsCoprime J 𝔮) {α β : 𝓞 K} (hp : RayPair 𝔮 α β)
    (h : I * Ideal.span {β} = J * Ideal.span {α}) (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    heckeIdeal L χ I = heckeIdeal L χ J := by
  obtain ⟨a, haJ, ha0, ha⟩ := exists_mem_sub_one hJ0 hJ
  have ha2 : a * a - 1 ∈ 𝔮 := by
    have : a * a - 1 = (a + 1) * (a - 1) := by ring
    rw [this]; exact 𝔮.mul_mem_left _ ha
  obtain ⟨M, hM⟩ : J ∣ Ideal.span {a * a} := Ideal.dvd_span_singleton.mpr (J.mul_mem_left _ haJ)
  have hM' : IsCoprime M 𝔮 := by
    have := isCoprime_span ha2
    rw [hM] at this
    exact this.of_mul_left_right
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    simp [ha0] at hM
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  have e1 : heckeIdeal L χ (J * M) = 1 := by
    refine (hR.2.2 _ (mul_ne_zero hJ0 hM0) (hJ.mul_left hM')).2 ⟨a * a, 1, ⟨mul_ne_zero ha0 ha0, one_ne_zero,
      isCoprime_span ha2, isCoprime_span (by simp), ha2, fun φ => ?_⟩, by simp [hM]⟩ χ
    have := mul_self_pos.2 (emb_ne_zero φ ha0)
    simpa using this
  have e2 : heckeIdeal L χ (I * M) = 1 := by
    refine (hR.2.2 _ (mul_ne_zero hI0 hM0) (hI.mul_left hM')).2 ⟨a * a * α, β,
      ⟨mul_ne_zero (mul_ne_zero ha0 ha0) h1, h2, ?_, h4, ?_, fun φ => ?_⟩, ?_⟩ χ
    · rw [← Ideal.span_singleton_mul_span_singleton]
      exact (isCoprime_span ha2).mul_left h3
    · have : a * a * α - β = α * (a * a - 1) + (α - β) := by ring
      rw [this]
      exact 𝔮.add_mem (𝔮.mul_mem_left _ ha2) h5
    · have := mul_pos (mul_self_pos.2 (emb_ne_zero φ ha0)) (h6 φ)
      simpa [mul_assoc] using this
    · rw [mul_right_comm, h, mul_right_comm, ← hM, Ideal.span_singleton_mul_span_singleton]
  rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hJ0 hM0] at e1
  rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hI0 hM0] at e2
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one e1) (e2.trans e1.symm)

theorem exists_ideal [IsGalois K L] (hR : IsRay L 𝔮) (σ : L ≃ₐ[K] L) :
    ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧ ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ) := by
  let S : Submonoid (L ≃ₐ[K] L) :=
    { carrier := {σ | ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧
        ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ)}
      one_mem' := ⟨1, one_ne_zero, isCoprime_one_left, fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩
      mul_mem' := by
        rintro x y ⟨I, hI0, hI, hx⟩ ⟨J, hJ0, hJ, hy⟩
        refine ⟨I * J, mul_ne_zero hI0 hJ0, hI.mul_left hJ, fun χ => ?_⟩
        rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hI0 hJ0, hx, hy]; simp }
  have hσ : σ ∈ Subgroup.closure
      {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ GlobalTheory.NT.IsFrob L 𝔭 σ} := by
    rw [hR.2.1]; trivial
  change σ ∈ S
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, hx⟩ := hx
    refine ⟨v.asIdeal, v.ne_bot, ?_, fun χ => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hv (Ideal.dvd_iff_le.2 (le_sup_right.trans (v.isMaximal.eq_of_le hne le_sup_left).ge))
    · rw [GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hR.1 v hv) hx]
  | one => exact S.one_mem
  | mul x y _ _ hx hy => exact S.mul_mem hx hy
  | inv x _ hx =>
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [this]
    exact S.pow_mem hx _

theorem finrank_le : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → IsRay L 𝔮 →
    Module.finrank K L ≤ classNumber K * Ideal.absNorm 𝔮 * 2 ^ Fintype.card (K →+* ℝ) := by
  intro K L _ _ _ _ _ _ 𝔮 h𝔮 hR
  classical
  choose s hs0 hs hsx using exists_ideal hR
  let cl : (L ≃ₐ[K] L) → ClassGroup (𝓞 K) := fun x =>
    ClassGroup.mk0 ⟨s x, mem_nonZeroDivisors_of_ne_zero (hs0 x)⟩
  have key : ∀ x, ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ 𝔮 ∧ IsCoprime (Ideal.span {b}) 𝔮 ∧
      Ideal.span {a} * s x = Ideal.span {b} * s (Function.invFun cl (cl x)) := by
    intro x
    have h : cl x = cl (Function.invFun cl (cl x)) := (Function.invFun_eq ⟨x, rfl⟩).symm
    obtain ⟨a, b, -, hb, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
    exact exists_good (hs0 x) (hs0 _) (hs x) (hs _) hb hxy
  choose a b ha0 hb0 ha hb hab using key
  let F : (L ≃ₐ[K] L) → (ClassGroup (𝓞 K) × (𝓞 K ⧸ 𝔮)) × ((K →+* ℝ) → Prop) := fun x =>
    ((cl x, Ideal.Quotient.mk 𝔮 (b x)), fun φ => 0 < φ (a x : K) * φ (b x : K))
  have hF : Function.Injective F := by
    intro x y hxy
    obtain ⟨h12, h3⟩ := Prod.mk.inj hxy
    obtain ⟨h1, h2⟩ := Prod.mk.inj h12
    rw [Ideal.Quotient.eq] at h2
    have hp : RayPair 𝔮 (b x * a y) (a x * b y) := by
      refine ⟨mul_ne_zero (hb0 x) (ha0 y), mul_ne_zero (ha0 x) (hb0 y), ?_, ?_, ?_, fun φ => ?_⟩
      · rw [← Ideal.span_singleton_mul_span_singleton]
        exact (hb x).mul_left (isCoprime_span (ha y))
      · rw [← Ideal.span_singleton_mul_span_singleton]
        exact (isCoprime_span (ha x)).mul_left (hb y)
      · have : b x * a y - a x * b y = b x * (a y - 1) - b y * (a x - 1) + (b x - b y) := by ring
        rw [this]
        exact 𝔮.add_mem (𝔮.sub_mem (𝔮.mul_mem_left _ (ha y)) (𝔮.mul_mem_left _ (ha x))) h2
      · have h4 : 0 < φ (a x : K) * φ (b x : K) ↔ 0 < φ (a y : K) * φ (b y : K) := (congrFun h3 φ).to_iff
        have h5 := mul_ne_zero (emb_ne_zero φ (ha0 x)) (emb_ne_zero φ (hb0 x))
        have h6 := mul_ne_zero (emb_ne_zero φ (ha0 y)) (emb_ne_zero φ (hb0 y))
        have h7 : 0 < (φ (a x : K) * φ (b x : K)) * (φ (a y : K) * φ (b y : K)) := by
          by_cases h : 0 < φ (a x : K) * φ (b x : K)
          · exact mul_pos h (h4.1 h)
          · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 h) h5)
              (lt_of_le_of_ne (not_lt.1 fun h' => h (h4.2 h')) h6)
        convert h7 using 1
        push_cast
        simp only [map_mul]
        ring
    have he : s x * Ideal.span {a x * b y} = s y * Ideal.span {b x * a y} := by
      have e1 := hab x
      have e2 := hab y
      rw [← h1] at e2
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
        ← mul_assoc, mul_comm (s x), e1, mul_comm (s y), mul_assoc _ _ (s y), e2]
      ring
    have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, χ x = χ y := fun χ => by
      apply Units.ext
      rw [← hsx, ← hsx]
      exact heckeIdeal_eq_of_ray hR (hs0 x) (hs0 y) (hs x) (hs y) hp he χ
    by_contra hne
    letI : CommGroup (L ≃ₐ[K] L) := IsMulCommutative.instCommGroup
    obtain ⟨χ, h⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) ℂ
      (a := x * y⁻¹) (by rwa [ne_eq, mul_inv_eq_one])
    apply h
    rw [map_mul, map_inv, hχ χ, mul_inv_cancel]
  haveI : Finite (𝓞 K ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 h𝔮
  rw [← IsGalois.card_aut_eq_finrank]
  refine (Nat.card_le_card_of_injective F hF).trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_prod, Ideal.absNorm_apply, Submodule.cardQuot_apply, classNumber,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := _ → Prop)]
  simp

end GlobalTheory.FieldSize.RayDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MapDifferentLeDifferentSupIntermediateField
section
set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.DiffBaseChange

theorem sum_emb_mul_dual {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ E) (σ τ : E →ₐ[ℚ] ℂ) [Decidable (σ = τ)] :
    ∑ i, σ (b i) * τ (b.traceDual i) = if σ = τ then 1 else 0 := by
  classical
  have hli := Fintype.linearIndependent_iff.1 (linearIndependent_algHom_toLinearMap ℚ E ℂ)
    (fun σ : E →ₐ[ℚ] ℂ => (∑ i, σ (b i) * τ (b.traceDual i)) - if σ = τ then 1 else 0) ?_ σ
  · convert sub_eq_zero.1 hli
  · ext x
    have h1 : τ x = ∑ i, (∑ σ : E →ₐ[ℚ] ℂ, σ (x * b i)) * τ (b.traceDual i) := by
      conv_lhs => rw [← b.traceDual.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, τ.commutes, b.traceDual_repr_apply, Algebra.traceForm_apply,
        ← trace_eq_sum_embeddings ℂ]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      smul_eq_mul, LinearMap.zero_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h1, sub_eq_zero]
    simp only [Finset.sum_mul, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem eq_sum_trace_mul_dual {F E L : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra F L] (j : E →+* L) (u : L →+* ℂ)
    (hgen : ∀ ρ : L →+* ℂ, (∀ x : F, ρ (algebraMap F L x) = u (algebraMap F L x)) →
      (∀ x : E, ρ (j x) = u (j x)) → ρ = u)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (y : L) :
    y = ∑ i, algebraMap F L (Algebra.trace F L (y * j (b i))) * j (b.traceDual i) := by
  classical
  letI : Algebra L ℂ := u.toAlgebra
  letI : Algebra F ℂ := (u.comp (algebraMap F L)).toAlgebra
  haveI : IsScalarTower F L ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply u.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have h1 : ∀ i, u (algebraMap F L (Algebra.trace F L (y * j (b i))) * j (b.traceDual i)) =
      ∑ ρ : L →ₐ[F] ℂ, ρ y * (ρ (j (b i)) * u (j (b.traceDual i))) := by
    intro i
    have := trace_eq_sum_embeddings (K := F) ℂ (x := y * j (b i))
    rw [map_mul]
    change algebraMap F ℂ _ * _ = _
    rw [this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => by rw [map_mul, mul_assoc]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ ρ : L →ₐ[F] ℂ, ∑ i, ρ y * (ρ (j (b i)) * u (j (b.traceDual i))) =
      if ρ = IsScalarTower.toAlgHom F L ℂ then u y else 0 := by
    intro ρ
    rw [← Finset.mul_sum]
    have := sum_emb_mul_dual b ((ρ : L →+* ℂ).comp j).toRatAlgHom (u.comp j).toRatAlgHom
    simp only [RingHom.toRatAlgHom_apply, RingHom.comp_apply, RingHom.coe_coe] at this
    rw [this]
    by_cases h : ρ = IsScalarTower.toAlgHom F L ℂ
    · subst h
      rw [if_pos rfl, if_pos (by rfl), mul_one]
      rfl
    · rw [if_neg h, if_neg, mul_zero]
      intro h'
      apply h
      have := hgen (ρ : L →+* ℂ) (fun x => ρ.commutes x) (fun x => DFunLike.congr_fun h' x)
      ext x
      exact DFunLike.congr_fun this x
  simp [h2]

theorem map_different_le {F E L : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra F L] (j : E →+* L) (u : L →+* ℂ)
    (hgen : ∀ ρ : L →+* ℂ, (∀ x : F, ρ (algebraMap F L x) = u (algebraMap F L x)) →
      (∀ x : E, ρ (j x) = u (j x)) → ρ = u) :
    (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom j) ≤ differentIdeal (𝓞 F) (𝓞 L) := by
  classical
  rw [Ideal.map_le_iff_le_comap]
  intro δ hδ
  rw [Ideal.mem_comap]
  have h1 : algebraMap (𝓞 E) E δ ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) :=
    (IsLocalization.mem_coeSubmodule _ _).2 ⟨δ, hδ, rfl⟩
  rw [coeSubmodule_differentIdeal ℤ ℚ (𝓞 E), Submodule.mem_div_iff_forall_mul_mem] at h1
  have hb : ∀ i, (integralBasis E).traceDual i ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    intro i
    rw [← Submodule.restrictScalars_mem ℤ, Submodule.traceDual_span_of_basis ℤ _ (integralBasis E)]
    · exact Submodule.subset_span ⟨i, rfl⟩
    · ext x
      rw [mem_span_integralBasis, Submodule.restrictScalars_mem, Submodule.mem_one]
      rfl
  suffices h : algebraMap (𝓞 L) L (RingOfIntegers.mapRingHom j δ) ∈
      IsLocalization.coeSubmodule L (differentIdeal (𝓞 F) (𝓞 L)) by
    obtain ⟨y, hy, hyx⟩ := (IsLocalization.mem_coeSubmodule _ _).1 h
    obtain rfl := IsFractionRing.injective (𝓞 L) L hyx
    exact hy
  rw [coeSubmodule_differentIdeal (𝓞 F) F (𝓞 L), Submodule.mem_div_iff_forall_mul_mem]
  intro y hy
  rw [eq_sum_trace_mul_dual (F := F) j u hgen (integralBasis E) y, Finset.mul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (h1 _ (hb i))
  obtain ⟨t, ht⟩ := Submodule.mem_traceDual.1 hy (j (integralBasis E i))
    (Submodule.mem_one.2 ⟨RingOfIntegers.mapRingHom j (RingOfIntegers.basis E i), by
      rw [integralBasis_apply]; rfl⟩)
  rw [Algebra.traceForm_apply] at ht
  refine Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 L) t * RingOfIntegers.mapRingHom j c, ?_⟩
  have e1 : ∀ z : 𝓞 E, algebraMap (𝓞 L) L (RingOfIntegers.mapRingHom j z) = j (algebraMap (𝓞 E) E z) := fun _ => rfl
  rw [map_mul, e1, e1, hc, map_mul, ← ht, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  ring

theorem map_different_le_sup (F F' : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField ↥(F ⊔ F')] :
    letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
    (differentIdeal ℤ (𝓞 F')).map
      (RingOfIntegers.mapRingHom (IntermediateField.inclusion (le_sup_right : F' ≤ F ⊔ F')).toRingHom) ≤
      differentIdeal (𝓞 F) (𝓞 ↥(F ⊔ F')) := by
  letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  refine map_different_le (F := F) _ (F ⊔ F').val.toRingHom fun ρ h1 h2 => ?_
  ext ⟨x, hx⟩
  change ρ ⟨x, hx⟩ = x
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact h1 ⟨x, hx⟩
    · exact h2 ⟨x, hx⟩
  | algebraMap q => exact h1 (algebraMap ℚ F q)
  | add x y hx hy ihx ihy => exact (map_add ρ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [ihx, ihy])
  | inv x hx ih => exact (map_inv₀ ρ ⟨x, hx⟩).trans (by rw [ih])
  | mul x y hx hy ihx ihy => exact (map_mul ρ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [ihx, ihy])

end GlobalTheory.DiffBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulFinrankMemDifferentIdeal
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize Pointwise
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.DifferentBound

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem algebraMap_intTrace_eq_sum (x : 𝓞 L) :
    algebraMap (𝓞 K) (𝓞 L) (Algebra.intTrace (𝓞 K) (𝓞 L) x) = ∑ σ : L ≃ₐ[K] L, σ • x := by
  apply FaithfulSMul.algebraMap_injective (𝓞 L) L
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K L,
    Algebra.algebraMap_intTrace (L := L), trace_eq_sum_automorphisms, map_sum]
  rfl

theorem not_dvd_of_inertia (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥)
    (h : ∀ σ : L ≃ₐ[K] L, (∀ x : 𝓞 L, σ • x - x ∈ P) → σ = 1) :
    ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  have hp : P.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP
  have := Ideal.IsPrime.isMaximal inferInstance hP
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under (𝓞 K)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (L ≃ₐ[K] L)] at hcard
  have hb : P.inertia (L ≃ₐ[K] L) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    exact h σ hσ
  rw [hb, Subgroup.card_bot] at hcard
  rw [not_dvd_differentIdeal_iff]
  exact Ideal.ramificationIdx_eq_one_iff.1 hcard.symm

theorem not_pow_dvd (n : ℕ) (hn : 0 < n) (P Q : Ideal (𝓞 L)) [hP : P.IsMaximal] (m : ℕ) (hnP : (n : 𝓞 L) ∈ P)
    (hPQ : P ⊔ Q = ⊤) (h : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} = P ^ m * Q) :
    ¬ P ^ m ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  classical
  have hco : IsCoprime (P ^ m) Q := (Ideal.isCoprime_iff_sup_eq.2 hPQ).pow_left
  obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.1
    ((Ideal.eq_top_iff_one _).1 (Ideal.isCoprime_iff_sup_eq.1 hco))
  refine not_dvd_differentIdeal_of_intTrace_not_mem (𝓞 K)
    (p := Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 K)}) (P ^ m) Q ?_ x hx ?_
  · rw [Ideal.map_span, Set.image_singleton, map_natCast, h]
  intro htr
  have hle : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} ≤ P ^ m := h ▸ Ideal.mul_le_left
  have h1 : ∑ σ : L ≃ₐ[K] L, σ • x ∈ P ^ m := by
    rw [← algebraMap_intTrace_eq_sum]
    apply hle
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) htr
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  set S := MulAction.stabilizer (L ≃ₐ[K] L) P
  have h2 : ∀ σ : L ≃ₐ[K] L, σ • x - (if σ ∈ S then 1 else 0) ∈ P ^ m := by
    intro σ
    split_ifs with hσ
    · have h3 : σ • a ∈ σ • P ^ m := Ideal.smul_mem_pointwise_smul σ a _ ha
      rw [smul_pow', MulAction.mem_stabilizer_iff.1 hσ] at h3
      have h4 : σ • x - 1 = -(σ • a) := by
        rw [← smul_one σ, ← hax, smul_add]; ring
      rw [h4]
      exact neg_mem h3
    · rw [sub_zero]
      have h3 : σ • x ∈ σ • Q := Ideal.smul_mem_pointwise_smul σ x _ hx
      have h4 : σ • Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} =
          Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} := by
        rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton, map_natCast]
      have h5 : P ^ m ∣ (σ • P) ^ m * σ • Q := by
        rw [← smul_pow', ← smul_mul', ← h, h4]
        exact Ideal.dvd_iff_le.2 hle
      have hM : (σ • P).IsMaximal := by
        rw [Ideal.pointwise_smul_def]
        exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ)
      have h6 : IsCoprime P (σ • P) :=
        Ideal.isCoprime_iff_sup_eq.2 (hP.coprime_of_ne hM fun e => hσ (MulAction.mem_stabilizer_iff.2 e.symm))
      exact Ideal.dvd_iff_le.1 ((h6.pow).dvd_of_dvd_mul_left h5) h3
  have h7 : ((Nat.card S : ℕ) : 𝓞 L) ∈ P ^ m := by
    have h8 := sub_mem h1 (Ideal.sum_mem _ fun σ (_ : σ ∈ Finset.univ) => h2 σ)
    rw [Finset.sum_sub_distrib, sub_sub_cancel, Finset.sum_boole] at h8
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h9 : ((Module.finrank K L : ℕ) : 𝓞 L) ∈ P ^ m := by
    obtain ⟨c, hc⟩ := S.card_subgroup_dvd_card
    rw [← IsGalois.card_aut_eq_finrank, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h7
  have h10 : P ^ m * P ∣ P ^ m * Q := by
    rw [← h, Ideal.dvd_span_singleton, Nat.cast_mul, mul_comm (n : 𝓞 L)]
    exact Ideal.mul_mem_mul h9 hnP
  have h0 : P ^ m ≠ 0 := by
    intro e
    rw [e, zero_mul, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at h
    exact (Nat.mul_pos hn Module.finrank_pos).ne' h
  have h11 := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left h0).1 h10)
  exact hP.ne_top (by rw [← hPQ, sup_eq_left.2 h11])


omit K L in
theorem natCast_mul_finrank_mem_differentIdeal :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (n : ℕ), 0 < n →
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∉ 𝔭.asIdeal → GlobalTheory.NT.UnramIn L 𝔭) →
      ((n * Module.finrank K L : ℕ) : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  intro K L _ _ _ _ _ _ n hn hu
  classical
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := differentIdeal_ne_bot
  have hI : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Nat.mul_pos hn Module.finrank_pos).ne'
  rw [← Ideal.dvd_span_singleton, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD0]
  intro P hP
  have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have hPm := hPp.isMaximal hP0
  by_cases hnP : (n : 𝓞 L) ∈ P
  · obtain ⟨Q, hPQ, h⟩ := Ideal.eq_prime_pow_mul_coprime hI P
    have h1 := not_pow_dvd K L n hn P Q _ hnP hPQ h
    exact (emultiplicity_lt_iff_not_dvd.2 h1).le.trans (le_emultiplicity_of_pow_dvd ⟨Q, h⟩)
  · have hp : P.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0
    have h1 := hu ⟨P.under (𝓞 K), inferInstance, hp⟩ (fun e => hnP (by simpa using Ideal.mem_comap.1 e))
    have h2 := not_dvd_of_inertia K L P hP0 fun σ hσ => h1 σ ⟨P, hPp, ⟨rfl⟩, hσ⟩
    rw [emultiplicity_eq_zero.2 h2]
    exact zero_le

end GlobalTheory.DifferentBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SzFieldRangeEmbedding
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

theorem sz_fieldRange_embedding (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) :
    Sz φ.toRatAlgHom.fieldRange (Real.log (Module.finrank ℚ K))
      (Real.log |((discr K : ℤ) : ℝ)| / Module.finrank ℚ K) := by
  let e : K ≃ₐ[ℚ] φ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField φ.toRatAlgHom
  have hfd : FiniteDimensional ℚ φ.toRatAlgHom.fieldRange := e.toLinearEquiv.finiteDimensional
  refine ⟨hfd, ?_⟩
  let _ : NumberField φ.toRatAlgHom.fieldRange := NumberField.mk
  have h1 : Module.finrank ℚ φ.toRatAlgHom.fieldRange = Module.finrank ℚ K := e.toLinearEquiv.finrank_eq.symm
  have h2 : discr φ.toRatAlgHom.fieldRange = discr K := (NumberField.discr_eq_discr_of_algEquiv K e).symm
  rw [h1, h2]
  exact ⟨le_rfl, le_rfl⟩

end GlobalTheory.FieldSize
end

