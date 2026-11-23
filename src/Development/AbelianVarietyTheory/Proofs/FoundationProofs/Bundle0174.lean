module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisorDescentModUnramifiedGaloisSubmodule
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0169
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.PetAdjQuot
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0156

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerDivisorDescendsFunctionField
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KummerCob

theorem descent_abstract (A K E Ω : Type) [CommRing A] [IsDedekindDomain A] [Field K] [CharZero K] [Algebra A K]
    [IsFractionRing A K] [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E] [Algebra A E]
    [IsScalarTower A K E] [Field Ω] [Algebra E Ω] (N : ℕ) (hN : 0 < N) (hNu : IsUnit (N : A))
    (s : Finset E) (hs : IntermediateField.adjoin K (s : Set E) = ⊤)
    (hsu : ∀ x ∈ s, ∃ u : Aˣ, x ^ N = algebraMap A E u)
    (hcl : ∀ c : ClassGroup A, ∃ d, c = d ^ N) (w : E) (hw : w ≠ 0)
    (hσ : ∀ σ : E ≃ₐ[K] E, ∃ u : E, u ≠ 0 ∧ σ w = w * u ^ N) :
    ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, (∀ x : A, algebraMap E Ω (algebraMap A E x) ∈ B) →
      ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / algebraMap K E f / c ^ N)) = 1 := by
  haveI : IsDedekindDomain (integralClosure A E) := integralClosure.isDedekindDomain A K E
  haveI : IsFractionRing (integralClosure A E) E := integralClosure.isFractionRing_of_finite_extension K E
  obtain ⟨f, J, hf, hJ⟩ := _root_.GlobalTheory.DivisorDescent.descent_submodule A (integralClosure A E) K E N hN
    (_root_.GlobalTheory.kummer_not_map_comap_le_sq A K E N hNu s hs hsu) hcl w hw hσ
  refine ⟨f, hf, fun B hB => ?_⟩
  refine _root_.GlobalTheory.valuation_eq_one_of_pow_eq_span E Ω (integralClosure A E).toSubring B J N hN ?_ _ ?_ hJ
  · intro x
    show algebraMap E Ω (x : E) ∈ B
    obtain ⟨p, hp, hpx⟩ : IsIntegral A (x : E) := x.2
    let φ : A →+* B := ((algebraMap E Ω).comp (algebraMap A E)).codRestrict B.toSubring hB
    have hint : IsIntegral B (algebraMap E Ω x) := by
      refine ⟨p.map φ, hp.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      have h := congrArg (algebraMap E Ω) hpx
      rw [Polynomial.hom_eval₂, map_zero] at h
      exact h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hy]
    exact y.2
  · exact div_ne_zero hw ((_root_.map_ne_zero _).mpr hf)

theorem isGalois_adjoin_pair (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hζK : ζ ∈ Set.range (algebraMap K Ω))
    (a b : K) (α β : Ω) (ha : a ≠ 0) (hb : b ≠ 0) (hα : α ^ N = algebraMap K Ω a) (hβ : β ^ N = algebraMap K Ω b) :
    IsGalois K (IntermediateField.adjoin K {α, β}) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have key : ∀ (c : K) (γ x : Ω), c ≠ 0 → γ ^ N = algebraMap K Ω c → γ ∈ IntermediateField.adjoin K {α, β} →
      x ^ N = algebraMap K Ω c → x ∈ IntermediateField.adjoin K {α, β} := by
    intro c γ x hc hγ hm hx
    have hc' : algebraMap K Ω c ≠ 0 := (_root_.map_ne_zero _).mpr hc
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      rw [zero_pow hN.ne'] at hγ
      exact hc' hγ.symm
    have h1 : (x / γ) ^ N = 1 := by rw [div_pow, hx, hγ, div_self hc']
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h1
    obtain ⟨z, rfl⟩ := hζK
    have : x = algebraMap K Ω z ^ i * γ := by rw [hi, div_mul_cancel₀ _ hγ0]
    rw [this]
    exact mul_mem (pow_mem (IntermediateField.algebraMap_mem _ z) i) hm
  let p : K[X] := (X ^ N - C a) * (X ^ N - C b)
  have hp0 : p ≠ 0 := mul_ne_zero (X_pow_sub_C_ne_zero hN a) (X_pow_sub_C_ne_zero hN b)
  have hroot : ∀ x : Ω, x ∈ p.rootSet Ω ↔ x ^ N = algebraMap K Ω a ∨ x ^ N = algebraMap K Ω b := by
    intro x
    rw [mem_rootSet_of_ne hp0]
    simp [p, sub_eq_zero]
  have heq : IntermediateField.adjoin K {α, β} = IntermediateField.adjoin K (p.rootSet Ω) := by
    apply le_antisymm
    · apply IntermediateField.adjoin.mono
      rintro x (rfl | rfl)
      · exact (hroot _).mpr (Or.inl hα)
      · exact (hroot _).mpr (Or.inr hβ)
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases (hroot x).mp hx with h | h
      · exact key a α x ha hα (IntermediateField.subset_adjoin _ _ (by simp)) h
      · exact key b β x hb hβ (IntermediateField.subset_adjoin _ _ (by simp)) h
  rw [heq]
  haveI := IntermediateField.adjoin_rootSet_isSplittingField (K := K) (L := Ω) (p := p) (IsAlgClosed.splits _)
  haveI : Normal K (IntermediateField.adjoin K (p.rootSet Ω)) := Normal.of_isSplittingField p
  exact ⟨⟩

theorem adjoin_pair_eq_top (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (α β : Ω)
    (α' β' : IntermediateField.adjoin K {α, β}) (hα : (α' : Ω) = α) (hβ : (β' : Ω) = β) :
    IntermediateField.adjoin K ({α', β'} : Set (IntermediateField.adjoin K {α, β})) = ⊤ := by
  apply IntermediateField.map_injective (IntermediateField.adjoin K {α, β}).val
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
    Set.image_pair]
  simp [hα, hβ]

theorem divisor_descends : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ : Ω, θ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} →
      (∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N) →
      ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        ∃ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 ∧ B.valuation (θ ^ N / (algebraMap K Ω f * c ^ N)) = 1 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ hθ hw hs
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  haveI := isGalois_adjoin_pair K Ω N ζ hN hζ (zeta_mem_range k K Ω N ζ hN hζ) a b α β ha0 hb0 hα hβ
  haveI : FiniteDimensional K (IntermediateField.adjoin K {α, β}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  have hNu : IsUnit (N : FunctionField.ringOfIntegers k K) := by
    have h1 : IsUnit (N : k) := (Nat.cast_ne_zero.mpr hN.ne').isUnit
    have h2 := h1.map ((algebraMap k[X] (FunctionField.ringOfIntegers k K)).comp C)
    rwa [map_natCast] at h2
  let α' : IntermediateField.adjoin K {α, β} := ⟨α, IntermediateField.subset_adjoin _ _ (by simp)⟩
  let β' : IntermediateField.adjoin K {α, β} := ⟨β, IntermediateField.subset_adjoin _ _ (by simp)⟩
  obtain ⟨f, hf, hB⟩ := descent_abstract (FunctionField.ringOfIntegers k K) K (IntermediateField.adjoin K {α, β}) Ω
    N hN hNu {α', β'} (by rw [Finset.coe_pair]; exact adjoin_pair_eq_top K Ω α β α' β' rfl rfl)
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, ha'⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩,
          Subtype.ext hα⟩
      · rw [Finset.mem_singleton.mp hx]
        exact ⟨⟨⟨b, hb⟩, ⟨b⁻¹, hb'⟩, Subtype.ext (mul_inv_cancel₀ hb0), Subtype.ext (inv_mul_cancel₀ hb0)⟩,
          Subtype.ext hβ⟩)
    (_root_.GlobalTheory.classGroup_ringOfIntegers_divisible k K N hN) ⟨θ ^ N, hw⟩ (fun h => pow_ne_zero N hθ (congrArg Subtype.val h))
    (by
      intro σ
      obtain ⟨u, hu, hu0, h⟩ := hs (σ.liftNormal Ω)
      refine ⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h), Subtype.ext ?_⟩
      exact (σ.liftNormal_commutes Ω ⟨θ ^ N, hw⟩).symm.trans h)
  refine ⟨f, hf, fun B hO => ?_⟩
  obtain ⟨c, hc, hv⟩ := hB B fun x => hO x.1 x.2
  refine ⟨c, c.2, fun h => hc (Subtype.ext h), ?_⟩
  rw [div_div, map_div₀, map_mul, map_pow] at hv
  exact hv

end GlobalTheory.KummerCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSelfPosGamma1InterGammaStatement
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_self_pos_gamma1InterGamma0 : ∀ (N l : ℕ) (k : ℤ), 0 < N → 0 < l → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, f ≠ 0 → 0 < (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑f).re ∧ (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑f).im = 0 := by
  first | exact @GlobalTheory.Hk.pet_self_pos | exact GlobalTheory.Hk.pet_self_pos | (intros; apply GlobalTheory.Hk.pet_self_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSesquilinearHermitian
section
noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_finiteIndex' (N l : ℕ) (hN : 0 < N) (hl : 0 < l) : (lev N l).FiniteIndex := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

theorem pet_eq_quotInt (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) :
    pet Γ k f g = UpperTheory.V.Lit.KT.quotInt Γ (petersson k f g) := rfl

theorem pet_sesq : ∀ (N l : ℕ) (k : ℤ), 0 < N → 0 < l → ∀ (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (c : ℂ), GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f (⇑g + c • ⇑h) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g + c * GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑h ∧ GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑g ⇑f = (starRingEnd ℂ) (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g) := by
  intro N l k hN hl f g h c
  haveI := lev_finiteIndex' N l hN hl
  haveI : Fintype (SL(2, ℤ) ⧸ lev N l) := Fintype.ofFinite _
  refine ⟨?_, ?_⟩
  · have e : petersson k ⇑f (⇑g + c • ⇑h) = fun z => petersson k f g z + c * petersson k f h z := by
      funext z
      simp only [petersson, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨B, hB⟩ := CuspFormClass.petersson_bounded_left k _ f g
    obtain ⟨B', hB'⟩ := CuspFormClass.petersson_bounded_left k _ f h
    have hc := petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous g)
    have hc' := petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous h)
    have hb'' : ∀ z, ‖c * petersson k f h z‖ ≤ ‖c‖ * B' := fun z => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB' z) (norm_nonneg _)
    rw [pet_eq_quotInt, pet_eq_quotInt, pet_eq_quotInt, e,
      UpperTheory.V.Lit.KT.quotInt_add (ψ := fun z => c * petersson k f h z) _ hc hB (continuous_const.mul hc') hb'', UpperTheory.V.Lit.KT.quotInt_mul]
  · simp only [pet, finsum_eq_sum_of_fintype]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← integral_conj]
    congr 1
    funext z
    exact petersson_symm _ _ _ _

end GlobalTheory.Hk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumQExpansion
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.LatQ

theorem hat_bounded (L : ℕ) (φ : ZMod L → ℂ) : ∃ C : ℝ, ∀ x, ‖hat φ x‖ ≤ C := by
  refine ⟨∑ y ∈ Finset.range L, ‖φ (y : ZMod L)‖, fun x => ?_⟩
  unfold hat
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_mul]
  have : ‖cexp (2 * π * Complex.I * ((y : ℂ) * (x : ℂ)) / (L : ℂ))‖ = 1 := by
    have h : (2 * π * Complex.I * ((y : ℂ) * (x : ℂ)) / (L : ℂ)) = ((2 * π * y * x / L : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  rw [this, mul_one]

theorem trm_zero_eq (j : ℕ) (w : ℂ) : trm j 0 w = (w ^ j)⁻¹ := by
  simp [trm]

theorem trm_neg (j : ℕ) (w : ℂ) : trm j 0 (-w) = (-1) ^ j * trm j 0 w := by
  rw [trm_zero_eq, trm_zero_eq, neg_pow, mul_inv, ← inv_pow, inv_neg, inv_one]

theorem trm_tendsto (j : ℕ) (hj : 1 ≤ j) (z : ℂ) :
    Tendsto (fun d : ℤ => trm j 0 (z + d)) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun d : ℤ => |(d : ℝ)|) cofinite atTop :=
    (tendsto_norm_cocompact_atTop.comp Int.tendsto_coe_cofinite)
  have h2 : Tendsto (fun d : ℤ => ‖z + d‖) cofinite atTop := by
    refine tendsto_atTop_mono (fun d => ?_) (tendsto_atTop_add_const_right _ (-‖z‖) h1)
    have := norm_sub_norm_le ((d : ℂ)) (-z)
    simp only [Complex.norm_intCast, norm_neg, sub_neg_eq_add] at this
    linarith [show ‖(d : ℂ) + z‖ = ‖z + d‖ by rw [add_comm]]
  have h3 : Tendsto (fun d : ℤ => ‖z + d‖ ^ j) cofinite atTop :=
    (tendsto_pow_atTop (by omega)).comp h2
  refine h3.inv_tendsto_atTop.congr (fun d => ?_)
  simp [trm_zero_eq, norm_inv, norm_pow]

theorem sum_range_eq_univ (L : ℕ) (hL : 0 < L) (φ : ZMod L → ℂ) (f : ℕ → ZMod L)
    (hf : Set.InjOn f (Finset.range L)) :
    haveI : NeZero L := ⟨hL.ne'⟩;
    ∑ r ∈ Finset.range L, φ (f r) = ∑ y, φ y := by
  haveI : NeZero L := ⟨hL.ne'⟩
  rw [← Finset.sum_image (fun x hx y hy h => hf hx hy h)]
  congr 1
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn hf, Finset.card_range, ZMod.card]

theorem kills (L : ℕ) (hL : 0 < L) (φ : ZMod L → ℂ) (d : ℤ) :
    ∑ r ∈ Finset.range L, φ ((d - r : ℤ) : ZMod L) = hat φ 0 := by
  have h1 : hat φ 0 = ∑ y ∈ Finset.range L, φ (y : ZMod L) := by simp [hat]
  rw [h1, sum_range_eq_univ L hL φ, sum_range_eq_univ L hL φ]
  · intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact this
  · intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    have h2 : (d - (b : ℤ)) - (d - (a : ℤ)) = (a : ℤ) - b := by ring
    rw [h2] at h
    have h3 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega

theorem phi_bounded (L : ℕ) (hL : 0 < L) (φ : ZMod L → ℂ) : ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C := by
  haveI : NeZero L := ⟨hL.ne'⟩
  exact ⟨∑ y, ‖φ y‖, fun y => Finset.single_le_sum (f := fun y => ‖φ y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)⟩

theorem latF_mul (L : ℕ) (hL : 0 < L) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (k d : ℤ) :
    latF L b φ (k * L, d) = b k * φ (d : ZMod L) := by
  have : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  simp [latF, Int.mul_ediv_cancel _ this]

theorem latF_ndvd (L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (x : ℤ × ℤ) (h : ¬ (L : ℤ) ∣ x.1) :
    latF L b φ x = 0 := by
  simp [latF, h]

theorem row_summable (j L : ℕ) (hj : 1 ≤ j) (hL : 0 < L) (A : ℤ → ℂ) (hA : ∃ C : ℝ, ∀ d, ‖A d‖ ≤ C) (τ : ℍ) (c : ℤ) :
    Summable fun d : ℤ => A d * dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (c, d) := by
  obtain ⟨C, hC⟩ := hA
  have hs := (_root_.GlobalTheory.LatSumZ.latsum_summable j L (0, 1) τ hj hL).prod_factor c
  refine (hs.mul_left C).of_norm_bounded (fun d => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC d) (norm_nonneg _)

theorem row_lim (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hj : 1 ≤ j) (hL : 0 < L) (h0 : hat φ 0 = 0)
    (τ : ℍ) (k : ℤ) :
    Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, b k * φ (d : ZMod L) * trm j 0 (((k * L : ℤ) : ℂ) * τ + d))
      atTop (𝓝 (∑' d : ℤ, latF L b φ (k * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k * L, d))) := by
  simp_rw [latF_mul L hL b φ k]
  obtain ⟨C, hC⟩ := phi_bounded L hL φ
  have hA : ∃ C : ℝ, ∀ d : ℤ, ‖b k * φ (d : ZMod L)‖ ≤ C :=
    ⟨‖b k‖ * C, fun d => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)⟩
  have hK : ∀ d : ℤ, ∑ r ∈ Finset.range L, b k * φ (((d - r : ℤ)) : ZMod L) = 0 := by
    intro d; rw [← Finset.mul_sum, kills L hL φ d, h0, mul_zero]
  exact GlobalTheory.RowLim.rowlim L (fun d => b k * φ (d : ZMod L)) (fun d => trm j 0 (((k * L : ℤ) : ℂ) * τ + d))
    (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k * L) hL hA hK (fun d => rfl)
    (trm_tendsto j hj _) (row_summable j L hj hL _ hA τ _)

theorem lip_all (j L : ℕ) (φ : ZMod L → ℂ) (z : ℂ) (hj : 1 ≤ j) (hL : 0 < L) (hz : 0 < z.im) (h0 : hat φ 0 = 0) :
    Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm j 0 (z + d)) atTop
      (𝓝 ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial *
        ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (j - 1) * hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
  · convert _root_.GlobalTheory.EisM.LipOne.lipschitz_one L φ z hL hz h0 using 2
    simp
  · exact _root_.GlobalTheory.EisM.lipschitz_periodic j L φ z hj2 hL hz

theorem row_pos (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hj : 1 ≤ j) (hL : 0 < L) (h0 : hat φ 0 = 0)
    (τ : ℍ) (n : ℕ) :
    ∑' d : ℤ, latF L b φ (((n + 1 : ℕ) : ℤ) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (((n + 1 : ℕ) : ℤ) * L, d) =
      (-2 * π * Complex.I / L) ^ j / (j - 1).factorial *
        (b (n + 1 : ℕ) * ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (j - 1) * hat φ (m + 1 : ℕ) *
          cexp (2 * π * Complex.I * (m + 1 : ℕ) * ((n + 1 : ℕ) * τ))) := by
  have hlim := row_lim j L b φ hj hL h0 τ ((n + 1 : ℕ) : ℤ)
  have hz : 0 < ((((((n + 1 : ℕ) : ℤ) * L : ℤ)) : ℂ) * (τ : ℂ)).im := by
    have : (((((n + 1 : ℕ) : ℤ) * L : ℤ)) : ℂ) = (((n + 1 : ℕ) * L : ℕ) : ℝ) := by push_cast; ring
    rw [this, Complex.im_ofReal_mul]
    exact mul_pos (by exact_mod_cast Nat.mul_pos (Nat.succ_pos n) hL) τ.im_pos
  have h2 := (lip_all j L φ _ hj hL hz h0).const_mul (b ((n + 1 : ℕ) : ℤ))
  have h3 : (fun R : ℕ => b ((n + 1 : ℕ) : ℤ) * ∑ d ∈ Finset.Icc (-(R : ℤ)) R,
      φ (d : ZMod L) * trm j 0 (((((n + 1 : ℕ) : ℤ) * L : ℤ) : ℂ) * τ + d)) =
      (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R,
        b ((n + 1 : ℕ) : ℤ) * φ (d : ZMod L) * trm j 0 (((((n + 1 : ℕ) : ℤ) * L : ℤ) : ℂ) * τ + d)) := by
    funext R; rw [Finset.mul_sum]; simp_rw [mul_assoc]
  rw [h3] at h2
  rw [tendsto_nhds_unique hlim h2]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have h4 : ∀ m : ℕ, cexp (2 * π * Complex.I * ((m + 1 : ℕ) : ℂ) * ((((((n + 1 : ℕ) : ℤ) * L : ℤ)) : ℂ) * τ) / L) =
      cexp (2 * π * Complex.I * ((m + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) * τ)) := by
    intro m; congr 1; push_cast; field_simp
  simp_rw [h4]
  ring

theorem row_neg (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hj : 1 ≤ j) (hL : 0 < L) (h0 : hat φ 0 = 0)
    (hpar : ∀ x y : ℤ, b (-x) * φ (-(y : ZMod L)) = (-1) ^ j * (b x * φ y)) (τ : ℍ) (k : ℤ) :
    ∑' d : ℤ, latF L b φ ((-k) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) ((-k) * L, d) =
    ∑' d : ℤ, latF L b φ (k * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k * L, d) := by
  refine tendsto_nhds_unique (row_lim j L b φ hj hL h0 τ (-k)) ?_
  refine (row_lim j L b φ hj hL h0 τ k).congr (fun R => ?_)
  refine Finset.sum_nbij' (fun d => -d) (fun d => -d) ?_ ?_ ?_ ?_ ?_
  · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
  · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
  · intro d _; simp
  · intro d _; simp
  · intro d _
    have e1 : (((-k) * L : ℤ) : ℂ) * τ + ((-d : ℤ) : ℂ) = -(((k * L : ℤ) : ℂ) * τ + (d : ℂ)) := by push_cast; ring
    have e2 := hpar k d
    rw [e1, trm_neg, show ((-d : ℤ) : ZMod L) = -(d : ZMod L) by push_cast; rfl]
    have : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-((-1 : ℂ) ^ j * trm j 0 (((k * L : ℤ) : ℂ) * τ + (d : ℂ)))) * e2 -
      (b k * φ (d : ZMod L) * trm j 0 (((k * L : ℤ) : ℂ) * τ + (d : ℂ))) * this

theorem row_zero_indep (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (τ τ' : ℍ) :
    ∑' d : ℤ, latF L b φ ((0 : ℤ) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) ((0 : ℤ) * L, d) =
    ∑' d : ℤ, latF L b φ ((0 : ℤ) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ' + y.2)) ((0 : ℤ) * L, d) := by
  congr 1; funext d; congr 1
  simp [dif]

theorem latF_bounded (L : ℕ) (hL : 0 < L) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hb : ∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) :
    ∃ C : ℝ, ∀ x, ‖latF L b φ x‖ ≤ C := by
  obtain ⟨Cb, hCb⟩ := hb
  obtain ⟨Cφ, hCφ⟩ := phi_bounded L hL φ
  have hb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 0)
  have hφ0 : 0 ≤ Cφ := (norm_nonneg _).trans (hCφ 0)
  refine ⟨Cb * Cφ, fun x => ?_⟩
  unfold latF; split_ifs
  · rw [norm_mul]; exact mul_le_mul (hCb _) (hCφ _) (norm_nonneg _) hb0
  · simp only [norm_zero]; positivity

theorem tsum_rows (L : ℕ) (hL : 0 < L) (F : ℤ → ℂ) (κ S : ℂ) (T : ℕ → ℂ) (hFs : Summable F)
    (hz : ∀ k, ¬ (L : ℤ) ∣ k → F k = 0) (hneg : ∀ k : ℤ, F ((-k) * L) = F (k * L))
    (hpos : ∀ n : ℕ, F (((n + 1 : ℕ) : ℤ) * L) = κ * T n) (hT : HasSum T S) :
    ∑' k, F k = F ((0 : ℤ) * L) + 2 * κ * S := by
  have hinj : Function.Injective (fun n : ℤ => n * (L : ℤ)) :=
    fun x y h => mul_right_cancel₀ (by exact_mod_cast hL.ne' : (L : ℤ) ≠ 0) h
  have hsupp : Function.support F ⊆ Set.range (fun n : ℤ => n * (L : ℤ)) := by
    intro k hk
    by_contra hn
    exact hk (hz k fun ⟨n, hn'⟩ => hn ⟨n, by rw [hn', mul_comm]⟩)
  rw [← hinj.tsum_eq hsupp]
  have hg : Summable fun n : ℤ => F (n * L) := hFs.comp_injective hinj
  have hsucc : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := fun x y h => by simpa using h
  have hnsucc : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := fun x y h => by simpa using h
  rw [tsum_of_add_one_of_neg_add_one (f := fun n : ℤ => F (n * L)) (hg.comp_injective hsucc) (hg.comp_injective hnsucc)]
  have hpos' : ∀ n : ℕ, F (((n : ℤ) + 1) * L) = κ * T n := fun n => by rw [← hpos n, Nat.cast_succ]
  simp only [hneg, hpos', tsum_mul_left, hT.tsum_eq]
  ring

theorem lat_qexp : ∀ (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ), 1 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) →
    hat φ 0 = 0 → (∀ x y : ℤ, b (-x) * φ (-(y : ZMod L)) = (-1) ^ j * (b x * φ y)) →
    ∃ c : ℂ, PolyB (eis j c (hat φ) b) ∧ ∀ τ : ℍ, lat j 0 L (0, 1) (latF L b φ) τ =
      2 * (-2 * π * Complex.I / L) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  intro j L b φ hj hL hb h0 hpar
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hκ : ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial : ℂ) ≠ 0 := by
    refine div_ne_zero (pow_ne_zero _ (div_ne_zero ?_ hL')) (by exact_mod_cast (Nat.factorial_pos _).ne')
    refine mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  generalize hκdef : ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial : ℂ) = κ at hκ
  obtain ⟨K, hK⟩ : ∃ K : ℂ, ∀ τ : ℍ, ∑' d : ℤ, latF L b φ ((0 : ℤ) * L, d) *
      dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) ((0 : ℤ) * L, d) = K :=
    ⟨_, fun τ => row_zero_indep j L b φ τ UpperHalfPlane.I⟩
  refine ⟨K / (2 * κ), (_root_.GlobalTheory.EisM.eis_qseries j _ (hat φ) b (hat_bounded L φ) hb).1, fun τ => ?_⟩
  have hq := (_root_.GlobalTheory.EisM.eis_qseries j (K / (2 * κ)) (hat φ) b (hat_bounded L φ) hb).2.2 τ
  obtain ⟨CΦ, hCΦ⟩ := latF_bounded L hL b φ hb
  have hs : Summable fun x : ℤ × ℤ => latF L b φ x *
      dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) x := by
    refine ((_root_.GlobalTheory.LatSumZ.latsum_summable j L (0, 1) τ hj hL).mul_left CΦ).of_norm_bounded (fun x => ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hCΦ x) (norm_nonneg _)
  have hrows := tsum_rows L hL (fun k => ∑' d : ℤ, latF L b φ (k, d) *
      dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k, d)) κ _ _ hs.prod
    (fun k hk => by simp only [latF_ndvd L b φ (k, _) hk, zero_mul, tsum_zero])
    (fun k => row_neg j L b φ hj hL h0 hpar τ k)
    (fun n => by rw [← hκdef]; exact row_pos j L b φ hj hL h0 τ n) hq
  have e : (2 * (-2 * π * Complex.I / L) ^ j / (j - 1).factorial : ℂ) = 2 * κ := by rw [← hκdef]; ring
  rw [e, lat, hs.tsum_prod, hrows]
  beta_reduce
  rw [hK τ]
  field_simp
  ring

end GlobalTheory.LatQ

end
end

