module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.LineR

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.AbsNormInvMulDifferent
section
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise

theorem absNorm_galois_smul' (E : Type) [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (𝔟 : Ideal (𝓞 E)) :
    Ideal.absNorm (c • 𝔟) = Ideal.absNorm 𝔟 := by
  classical
  rw [Ideal.pointwise_smul_def]
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv 𝔟 _ (MulSemiringAction.toRingEquiv _ (𝓞 E) c) rfl).toEquiv).symm

theorem absNorm_inv_mul_different (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
    [Algebra K E] (c : E ≃ₐ[ℚ] E) (𝔟 : Ideal (𝓞 E))
    (h : differentIdeal (𝓞 K) (𝓞 E) = 𝔟 * (c • 𝔟)) :
    FractionalIdeal.absNorm (((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ *
        ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ^ 2 =
      (Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) : ℚ) := by
  have hD : differentIdeal (𝓞 K) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hb : 𝔟 ≠ ⊥ := by
    rintro rfl
    exact hD (by rw [h]; exact Submodule.bot_mul _)
  have hcoe : ∀ J : Ideal (𝓞 E), FractionalIdeal.absNorm
      ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) = (Ideal.absNorm J : ℚ) := fun J =>
    FractionalIdeal.coeIdeal_absNorm J
  have hB : ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  rw [h, FractionalIdeal.coeIdeal_mul, ← mul_assoc, inv_mul_cancel₀ hB, one_mul, hcoe, map_mul,
    absNorm_galois_smul' E c 𝔟]
  push_cast
  ring

theorem natAbs_discr_eq (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
    [Algebra K E] (d : ℕ) (hdK : NumberField.discr K = -(d : ℤ)) :
    (NumberField.discr E).natAbs =
      Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) * d ^ Module.finrank K E := by
  rw [← absNorm_differentIdeal E (𝓞 E),
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 E), map_mul,
    Ideal.absNorm_algebraMap, absNorm_differentIdeal K (𝓞 K), hdK,
    ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E]
  simp

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.LiftMOneExt
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem liftM_val_ext {M : IntermediateField ℚ ℂ} {x : ℂ} (h : x ∈ M) : ((liftM M x : M) : ℂ) = x := by
  simp [liftM, h]

theorem liftM_mul_ext {E : Type} [Field E] (M : IntermediateField ℚ ℂ) (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M)
    (a b : E) : liftM M (σ (a * b)) = liftM M (σ a) * liftM M (σ b) := by
  apply Subtype.ext
  rw [liftM_val_ext (hσ (a * b)), IntermediateField.coe_mul, liftM_val_ext (hσ a),
    liftM_val_ext (hσ b), map_mul]

theorem liftM_add_ext {E : Type} [Field E] (M : IntermediateField ℚ ℂ) (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M)
    (a b : E) : liftM M (σ (a + b)) = liftM M (σ a) + liftM M (σ b) := by
  apply Subtype.ext
  rw [liftM_val_ext (hσ (a + b)), IntermediateField.coe_add, liftM_val_ext (hσ a),
    liftM_val_ext (hσ b), map_add]

theorem liftM_one_ext {E : Type} [Field E] (M : IntermediateField ℚ ℂ) (σ : E →+* ℂ) :
    liftM M (σ 1) = 1 := by
  apply Subtype.ext
  rw [map_one, liftM_val_ext (one_mem M), IntermediateField.coe_one]

theorem liftM_int_ext {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (e : 𝓞 E) :
    liftM M (σ (algebraMap (𝓞 E) E e)) ∈ (algebraMap (𝓞 M) M).range := by
  have h1 : IsIntegral ℤ (σ (algebraMap (𝓞 E) E e)) :=
    (RingOfIntegers.isIntegral_coe e).map σ.toIntAlgHom
  have hx : IsIntegral ℤ (liftM M (σ (algebraMap (𝓞 E) E e))) := by
    rw [← isIntegral_algHom_iff (algebraMap M ℂ).toIntAlgHom (algebraMap M ℂ).injective]
    change IsIntegral ℤ ((liftM M (σ (algebraMap (𝓞 E) E e)) : M) : ℂ)
    rwa [liftM_val_ext (hσ _)]
  exact ⟨⟨_, hx⟩, rfl⟩

theorem mem_imI_iff {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (x : M) :
    x ∈ imI M σ J ↔
      ∀ b ∈ ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E), x * liftM M (σ b) ∈ (algebraMap (𝓞 M) M).range := by
  have hJJ : (1 : E) ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one]
    exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have hint : ∀ z ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E), liftM M (σ z) ∈ (algebraMap (𝓞 M) M).range := by
    intro z hz
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one] at hz
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hz
    exact liftM_int_ext M σ hσ y
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro b hb
      rw [← liftM_mul_ext M σ hσ]
      exact hint _ (Submodule.mul_mem_mul ha hb)
    | zero =>
      intro b _
      rw [zero_mul]
      exact zero_mem _
    | add y z _ _ hy hz =>
      intro b hb
      rw [add_mul]
      exact add_mem (hy b hb) (hz b hb)
    | smul r y _ hy =>
      intro b hb
      rw [smul_mul_assoc, Algebra.smul_def]
      exact mul_mem (RingHom.mem_range_self _ r) (hy b hb)
  · intro hx
    have key : ∀ z ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
        Submodule (𝓞 E) E), x * liftM M (σ z) ∈ imI M σ J := by
      intro z hz
      induction hz using Submodule.mul_induction_on' with
      | mem_mul_mem a ha b hb =>
        obtain ⟨r, hr⟩ := hx b hb
        rw [liftM_mul_ext M σ hσ, mul_comm (liftM M (σ a)), ← mul_assoc, ← hr, ← Algebra.smul_def]
        exact Submodule.smul_mem _ r (Submodule.subset_span ⟨a, ha, rfl⟩)
      | add y _ z _ hy hz =>
        rw [liftM_add_ext M σ hσ, mul_add]
        exact add_mem hy hz
    have := key 1 hJJ
    rwa [liftM_one_ext, mul_one] at this

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.MapMulLeftDenSpanImageEqMapNum
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

private lemma algebraMap_ringOfIntegers_tower {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (x : 𝓞 E) : algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) x) = algebraMap E F (algebraMap (𝓞 E) E x) := rfl

theorem map_mulLeft_den_span_image_eq_map_num {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    Submodule.map (LinearMap.mulLeft (𝓞 F) ((algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E) : 𝓞 F) : F))
        (Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))) =
      Submodule.map (Algebra.linearMap (𝓞 F) F) (J.num.map (algebraMap (𝓞 E) (𝓞 F))) := by
  have hden := FractionalIdeal.den_mul_self_eq_num J
  rw [Submodule.map_span, Ideal.map, Ideal.span, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    have h1 : J.den • j ∈ J.den • (J : Submodule (𝓞 E) E) :=
      Submodule.smul_mem_pointwise_smul j _ _ hj
    rw [hden] at h1
    obtain ⟨n, hn, hnj⟩ := Submodule.mem_map.mp h1
    refine ⟨algebraMap (𝓞 E) (𝓞 F) n, ⟨n, hn, rfl⟩, ?_⟩
    show algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) n) =
      algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E)) * algebraMap E F j
    rw [algebraMap_ringOfIntegers_tower, algebraMap_ringOfIntegers_tower, ← map_mul]
    congr 1
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    have h1 : algebraMap (𝓞 E) E n ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) J.num :=
      Submodule.mem_map_of_mem hn
    rw [← hden] at h1
    obtain ⟨j, hj, hjn⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    refine ⟨algebraMap E F j, ⟨j, hj, rfl⟩, ?_⟩
    show algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E)) * algebraMap E F j =
      algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) n)
    rw [algebraMap_ringOfIntegers_tower, algebraMap_ringOfIntegers_tower, ← map_mul, ← Algebra.smul_def]
    exact congrArg (algebraMap E F) hjn

theorem index_image_ideal {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (s : F)
    (hs : s ∈ Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))) :
    ((((Submodule.span (𝓞 F) {s}).toAddSubgroup.addSubgroupOf
        (Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))).toAddSubgroup).index : ℕ) : ℚ) *
        (Ideal.absNorm J.num : ℚ) ^ Module.finrank E F =
      |Algebra.norm ℚ s| * |Algebra.norm ℚ ((J.den : 𝓞 E) : E)| ^ Module.finrank E F := by
  set A := Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E)) with hA
  set c : 𝓞 F := algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E) with hcdef
  have hc : (c : F) = algebraMap E F ((J.den : 𝓞 E) : E) := rfl
  have hden0 : ((J.den : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.coe_ne_zero J.den
    exact_mod_cast this
  have hc0 : (c : F) ≠ 0 := by rw [hc]; exact (map_ne_zero _).mpr hden0
  set f := LinearMap.mulLeft (𝓞 F) (c : F) with hf
  have hfinj : Function.Injective f := fun x y h => mul_left_cancel₀ hc0 h
  set I2 : Ideal (𝓞 F) := J.num.map (algebraMap (𝓞 E) (𝓞 F)) with hI2
  have hmapA : Submodule.map f A = Submodule.map (Algebra.linearMap (𝓞 F) F) I2 := map_mulLeft_den_span_image_eq_map_num J
  have hcs : (c : F) * s ∈ Submodule.map (Algebra.linearMap (𝓞 F) F) I2 := by
    rw [← hmapA]; exact ⟨s, hs, rfl⟩
  obtain ⟨t, ht, hts⟩ := hcs
  simp only [Algebra.linearMap_apply] at hts
  have hmaps : Submodule.map f (Submodule.span (𝓞 F) {s}) =
      Submodule.map (Algebra.linearMap (𝓞 F) F) (Ideal.span {t}) := by
    rw [Ideal.span, Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton]
    simp only [Algebra.linearMap_apply, hts]
    rfl
  have hginj : Function.Injective (Algebra.linearMap (𝓞 F) F) := RingOfIntegers.coe_injective
  have hrel : (((Submodule.span (𝓞 F) {s}).toAddSubgroup.addSubgroupOf A.toAddSubgroup).index) =
      (Ideal.span {t}).toAddSubgroup.relIndex I2.toAddSubgroup := by
    change (Submodule.span (𝓞 F) {s}).toAddSubgroup.relIndex A.toAddSubgroup = _
    have h1 := AddSubgroup.relIndex_map_map_of_injective (f := (f : F →+ F))
      (Submodule.span (𝓞 F) {s}).toAddSubgroup A.toAddSubgroup hfinj
    rw [← h1, ← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hmaps, hmapA,
      Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective
      (f := ((Algebra.linearMap (𝓞 F) F) : 𝓞 F →+ F)) _ _ hginj
  have hle : (Ideal.span {t}).toAddSubgroup ≤ I2.toAddSubgroup := by
    intro x hx
    exact (Ideal.span_singleton_le_iff_mem _).mpr ht hx
  have hmul := AddSubgroup.relIndex_mul_index hle
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, Ideal.absNorm_span_singleton, hI2,
    Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 F) F] at hmul
  rw [hrel]
  have hnt : ((Algebra.norm ℤ t : ℤ) : ℚ) = Algebra.norm ℚ s * (Algebra.norm ℚ ((J.den : 𝓞 E) : E)) ^ Module.finrank E F := by
    rw [Algebra.coe_norm_int, show ((t : F)) = (c : F) * s from hts, map_mul, hc, mul_comm]
    congr 1
    rw [← Algebra.norm_norm (S := E), Algebra.norm_algebraMap, map_pow]
  have hq := congrArg (fun n : ℕ => (n : ℚ)) hmul
  simp only [Nat.cast_mul, Nat.cast_pow] at hq
  rw [hq, Nat.cast_natAbs, Int.cast_abs, hnt, abs_mul, abs_pow]

theorem index_imI_ext {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (s : F)
    (hs : s ∈ Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))) :
    ((((Submodule.span (𝓞 F) {s}).toAddSubgroup.addSubgroupOf
        (Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))).toAddSubgroup).index : ℕ) : ℚ) ^
        Module.finrank ℚ E * (FractionalIdeal.absNorm J : ℚ) ^ Module.finrank ℚ F =
      |Algebra.norm ℚ s| ^ Module.finrank ℚ E := by
  have haux := index_image_ideal J s hs
  have hJ : (FractionalIdeal.absNorm J : ℚ) =
      (Ideal.absNorm J.num : ℚ) / |Algebra.norm ℚ ((J.den : 𝓞 E) : E)| := by
    rw [FractionalIdeal.absNorm_eq, Int.cast_abs, Algebra.coe_norm_int]
  have hD : |Algebra.norm ℚ ((J.den : 𝓞 E) : E)| ≠ 0 := by
    refine abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ?_)
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr (nonZeroDivisors.coe_ne_zero J.den)
  have hf : Module.finrank ℚ F = Module.finrank ℚ E * Module.finrank E F :=
    (Module.finrank_mul_finrank ℚ E F).symm
  rw [hJ, hf, div_pow, ← mul_div_assoc, div_eq_iff (pow_ne_zero _ hD),
    mul_comm (Module.finrank ℚ E) (Module.finrank E F), pow_mul, pow_mul, ← mul_pow, ← mul_pow, haux]

theorem index_imI {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (s : M) (hs0 : s ≠ 0)
    (hs : s ∈ imI M σ J) :
    ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (imI M σ J).toAddSubgroup).index : ℕ) : ℝ) ^ Module.finrank ℚ E *
      ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ Module.finrank ℚ M =
      |((Algebra.norm ℚ s : ℚ) : ℝ)| ^ Module.finrank ℚ E := by
  letI : Algebra E M := (σ.codRestrict M hσ).toAlgebra
  have hlift : ∀ a, algebraMap E M a = liftM M (σ a) := fun a =>
    Subtype.ext (by rw [show ((liftM M (σ a) : M) : ℂ) = σ a by simp [liftM, hσ a]]; rfl)
  have hI : imI M σ J = Submodule.span (𝓞 M) (algebraMap E M '' (J : Set E)) := by
    unfold imI
    congr 1
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, hlift a⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, hlift a⟩
  rw [hI] at hs ⊢
  have h := index_imI_ext (E := E) (F := M) J s hs
  exact_mod_cast h

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.SumEmbDualBasisComplex
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem liftM_coe_of_mem (M : IntermediateField ℚ ℂ) {x : ℂ} (h : x ∈ M) : ((liftM M x : M) : ℂ) = x := by
  rw [liftM, dite_eq_left h]

theorem sum_emb_eq_trace_complex (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (ι : Type) [Fintype ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (a : E) :
    ∑ i, emb i a = φ₀ (Algebra.trace K E a) := by
  letI : Algebra K ℂ := φ₀.toAlgebra
  haveI : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ K E
  let f : ι → (E →ₐ[K] ℂ) := fun i => { emb i with commutes' := fun y => hres i y }
  have hfinj : Function.Injective f := fun i j h => hinj (RingHom.ext fun x => AlgHom.congr_fun h x)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, by rw [hcard, AlgHom.card K E ℂ]⟩
  have htr := trace_eq_sum_embeddings ℂ (K := K) (L := E) (x := a)
  calc ∑ i, emb i a = ∑ i, f i a := rfl
    _ = ∑ σ : E →ₐ[K] ℂ, σ a := hbij.sum_comp (fun σ => σ a)
    _ = φ₀ (Algebra.trace K E a) := htr.symm

theorem sum_emb_eq_trace (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (a : E) :
    ∑ i, liftM M (emb i a) = liftM M (φ₀ (Algebra.trace K E a)) := by
  have hsum := sum_emb_eq_trace_complex K E φ₀ ι emb hinj hres hcard a
  have hmem : φ₀ (Algebra.trace K E a) ∈ M := hsum ▸ M.sum_mem (fun i _ => hM i a)
  apply Subtype.ext
  rw [IntermediateField.coe_sum, liftM_coe_of_mem M hmem, ← hsum]
  exact Finset.sum_congr rfl fun i _ => liftM_coe_of_mem M (hM i a)

theorem sum_emb_dualBasis_complex (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) {κ : Type} [Fintype κ] [DecidableEq κ] (e : Module.Basis κ K E)
    (i k : ι) :
    ∑ j, emb i (e j) * emb k ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e j) =
      if i = k then 1 else 0 := by
  have hexp : ∀ x, emb k x = ∑ i', emb i' x * ∑ j, emb i' (e j) * emb k (((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e) j) := by
    intro x
    conv_lhs => rw [← ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul,
      hres, ← sum_emb_eq_trace_complex K E φ₀ ι emb hinj hres hcard, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ => by ring
  have hLI : LinearIndependent ℂ (fun i => ((emb i : E →+* ℂ) : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun i => (emb i).toMonoidHom)
      (fun i j h => hinj (RingHom.ext fun x => DFunLike.congr_fun h x))
  rw [Fintype.linearIndependent_iff] at hLI
  have h := hLI (fun i' => (∑ j, emb i' (e j) * emb k (((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e) j)) - if i' = k then 1 else 0) (by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
      Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, hexp x]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _) i
  rwa [sub_eq_zero] at h

theorem sum_emb_dualBasis (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) {κ : Type} [Fintype κ] [DecidableEq κ] (e : Module.Basis κ K E)
    (i k : ι) :
    ∑ j, liftM M (emb i (e j)) *
        liftM M (emb k ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e j)) =
      if i = k then 1 else 0 := by
  have hc := sum_emb_dualBasis_complex K E φ₀ ι emb hinj hres hcard e i k
  apply Subtype.ext
  rw [IntermediateField.coe_sum]
  simp only [IntermediateField.coe_mul, liftM_coe_of_mem M (hM _ _)]
  rw [hc]
  split_ifs <;> simp

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

