module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0083
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn
public import Formalism.LocalRingCardinality.DataKerI

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped nonZeroDivisors

namespace GlobalTheory.Mem

theorem span_image_eq_coeSubmodule_map {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) (𝔞 : Ideal (𝓞 E)) :
    Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, x = f (a : E)} =
      IsLocalization.coeSubmodule K (𝔞.map (RingOfIntegers.mapRingHom f)) := by
  rw [Ideal.map, IsLocalization.coeSubmodule_span, Set.image_image]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

noncomputable def extendIdealHom {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) : Ideal (𝓞 E) →* Submodule (𝓞 K) K where
  toFun 𝔞 := IsLocalization.coeSubmodule K (𝔞.map (RingOfIntegers.mapRingHom f))
  map_one' := by
    rw [Ideal.one_eq_top, Ideal.map_top, IsLocalization.coeSubmodule_top]
  map_mul' a b := by rw [Ideal.map_mul, IsLocalization.coeSubmodule_mul]

theorem extendIdealHom_span {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) (a : 𝓞 E) :
    extendIdealHom f (Ideal.span {a}) = Submodule.span (𝓞 K) {f (a : E)} := by
  show IsLocalization.coeSubmodule K ((Ideal.span {a}).map (RingOfIntegers.mapRingHom f)) = _
  rw [Ideal.map_span, IsLocalization.coeSubmodule_span, Set.image_singleton, Set.image_singleton]
  rfl

theorem extendIdealHom_fg {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) (𝔞 : Ideal (𝓞 E)) : (extendIdealHom f 𝔞).FG :=
  Submodule.FG.map _ (IsNoetherian.noetherian _)

theorem span_singleton_prod_pow {R K ι : Type} [CommRing R] [CommRing K] [Algebra R K]
    (s : Finset ι) (x : ι → K) (r : ι → ℕ) :
    ∏ i ∈ s, Submodule.span R {x i} ^ r i = Submodule.span R {∏ i ∈ s, x i ^ r i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Submodule.one_eq_span]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, Submodule.span_pow, Set.singleton_pow,
      Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem fg_prod_pow {R K ι : Type} [CommRing R] [CommRing K] [Algebra R K]
    (s : Finset ι) (I : ι → Submodule R K) (r : ι → ℕ) (h : ∀ i, (I i).FG) :
    (∏ i ∈ s, I i ^ r i).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact ((h i).pow _).mul ih

theorem exists_rep_pow_classNumber (E : Type) [Field E] [NumberField E] (c : ClassGroup (𝓞 E)) :
    ∃ (𝔠 : (Ideal (𝓞 E))⁰) (γ : 𝓞 E), ClassGroup.mk0 𝔠 = c ∧ γ ≠ 0 ∧
      (𝔠 : Ideal (𝓞 E)) ^ Fintype.card (ClassGroup (𝓞 E)) = Ideal.span {γ} := by
  obtain ⟨𝔠, h𝔠⟩ := ClassGroup.mk0_surjective c
  have h1 : ClassGroup.mk0 (𝔠 ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 := (ClassGroup.mk0_eq_one_iff (𝔠 ^ Fintype.card (ClassGroup (𝓞 E))).2).1 h1
  obtain ⟨γ, hγ⟩ := h2
  have hγ' : (𝔠 : Ideal (𝓞 E)) ^ Fintype.card (ClassGroup (𝓞 E)) = Ideal.span {γ} := hγ
  refine ⟨𝔠, γ, h𝔠, ?_, hγ'⟩
  rintro rfl
  rw [Ideal.span_singleton_zero] at hγ'
  exact pow_ne_zero _ (nonZeroDivisors.ne_zero 𝔠.2) hγ'

theorem exists_finset_typeNorm_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], (∀ z ∈ S, z ∈ K) → (∀ (τ : E →+* ℂ) x, τ x ∈ K) → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : K, β ≠ 0 ∧ Submodule.span (𝓞 K) {β} = ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧ ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  intro E _ _ _ _ r n hr
  classical
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : 0 < h := Fintype.card_pos
  choose 𝔠 γ h𝔠 hγ0 hγ using exists_rep_pow_classNumber E
  have hex : ∀ c, ∃ z : ℂ, z ^ h = ∏ τ : E →+* ℂ, τ (γ c : E) ^ r τ := fun c =>
    IsAlgClosed.exists_pow_nat_eq _ hpos
  choose b hb using hex
  refine ⟨Finset.univ.image b, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hz
    refine IsAlgebraic.of_pow hpos ?_
    rw [hb]
    refine IsIntegral.isAlgebraic (IsIntegral.prod _ fun τ _ => IsIntegral.pow ?_ _)
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) (γ c : E)).map τ.toRatAlgHom
  intro K _ hS hK 𝔞 h𝔞
  have : NumberField K := NumberField.mk
  let f : (E →+* ℂ) → (E →+* K) := fun τ => τ.codRestrict K (hK τ)
  let N : 𝓞 E → K := fun a => ∏ τ : E →+* ℂ, f τ (a : E) ^ r τ
  have hN0 : ∀ a, a ≠ 0 → N a ≠ 0 := fun a ha =>
    Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (by
      rw [map_ne_zero]; exact_mod_cast ha)
  have hNabs : ∀ (a : 𝓞 E) (σ : K →+* ℂ),
      ‖σ (N a)‖ ^ 2 = (Ideal.absNorm (Ideal.span {a}) : ℝ) ^ n := by
    intro a σ
    have := norm_typeNorm_sq_eq E r n hr K hK (a : E) σ
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]
    rw [← Algebra.coe_norm_int] at this
    rw [Rat.cast_intCast] at this
    exact this
  let Φ : Ideal (𝓞 E) → Submodule (𝓞 K) K := fun I => ∏ τ : E →+* ℂ, extendIdealHom (f τ) I ^ r τ
  have hΦmul : ∀ I J, Φ (I * J) = Φ I * Φ J := by
    intro I J
    simp only [Φ, map_mul, mul_pow, Finset.prod_mul_distrib]
  have hΦpow : ∀ I, Φ (I ^ h) = Φ I ^ h := by
    intro I
    simp only [Φ, map_pow, ← Finset.prod_pow, ← pow_mul, mul_comm]
  have hΦspan : ∀ a, Φ (Ideal.span {a}) = Submodule.span (𝓞 K) {N a} := by
    intro a
    simp only [Φ, N, extendIdealHom_span, span_singleton_prod_pow]
  have hgoal : ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ
      = Φ 𝔞 := by
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine Eq.trans ?_ (span_image_eq_coeSubmodule_map (f τ) 𝔞)
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
    rfl
  rw [hgoal]
  let 𝔞' : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  set c := ClassGroup.mk0 𝔞' with hc
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hc.symm.trans (h𝔠 c).symm)
  have hxy' : Ideal.span {x} * 𝔞 = Ideal.span {y} * (𝔠 c : Ideal (𝓞 E)) := hxy
  let βc : K := ⟨b c, hS _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  have hβc : βc ^ h = N (γ c) := by
    apply Subtype.ext
    simp only [βc, N, SubmonoidClass.coe_pow, IntermediateField.coe_prod, hb]
    rfl
  have hβc0 : βc ≠ 0 := by
    intro h0
    rw [h0, zero_pow hpos.ne'] at hβc
    exact hN0 _ (hγ0 c) hβc.symm
  have hΦc : Φ (𝔠 c) = Submodule.span (𝓞 K) {βc} := by
    refine GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ βc h hpos hβc0
      (fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _) ?_
    rw [← hΦpow, hγ, hΦspan, hβc]
  have hcabs : ∀ σ : K →+* ℂ, ‖σ βc‖ ^ 2 = (Ideal.absNorm (𝔠 c : Ideal (𝓞 E)) : ℝ) ^ n := by
    intro σ
    have := hNabs (γ c) σ
    rw [← hγ, ← hβc, map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at this
    exact (pow_left_inj₀ (by positivity) (by positivity) hpos.ne').1 this
  refine ⟨(N x)⁻¹ * (N y * βc), mul_ne_zero (inv_ne_zero (hN0 x hx)) (mul_ne_zero (hN0 y hy) hβc0),
    ?_, ?_⟩
  · have h1 := congrArg Φ hxy'
    rw [hΦmul, hΦmul, hΦspan, hΦspan, hΦc] at h1
    rw [← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton, ← Submodule.span_mul_span,
      ← Submodule.span_mul_span, ← h1, ← mul_assoc, Submodule.span_mul_span,
      Set.singleton_mul_singleton, inv_mul_cancel₀ (hN0 x hx), ← Submodule.one_eq_span, one_mul]
  · intro σ
    have h1 := congrArg (fun I => (Ideal.absNorm I : ℝ) ^ n) hxy'
    simp only [map_mul, Nat.cast_mul, mul_pow] at h1
    rw [← hNabs x σ, ← hNabs y σ, ← hcabs σ] at h1
    have h2 : ‖σ (N x)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]; exact hN0 x hx
    rw [map_mul, map_mul, map_inv₀, norm_mul, norm_mul, norm_inv, mul_pow, mul_pow, ← h1]
    field_simp

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowJoint
section
open NumberField IsDedekindDomain

namespace GlobalTheory.TameJoint

theorem exists_pow_joint : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ)
    (γ : Formalism.ConjugateSelfDual.G E Ω) (π : Ω) (w : E),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → Formalism.BasicNotions.TameGenAt A γ →
    (∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → φ τ = 1) → φ γ ^ L = 1 →
    π ≠ 0 → π ^ L = algebraMap E Ω w →
    ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π = (γ π / π) ^ b * π := by
  intro E Ω _ _ _ _ _ M _ φ P A L γ π w hA hker hL hγ hw hγL hπ he σ hσ
  have hL0 : L ≠ 0 := by rintro rfl; exact hL (by simp)
  have hn : 0 < L := Nat.pos_of_ne_zero hL0
  have hLA : ¬ A.valuation (L : Ω) < 1 := by
    intro h
    apply hL
    rw [← hA]
    simpa using h
  set ζ := γ π / π with hζ
  have hζn : ζ ^ L = 1 := by
    rw [hζ, div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
    rw [← he]; exact pow_ne_zero _ hπ
  have hred : ∀ {N : Type} [Monoid N] (x : N), x ^ L = 1 → ∀ a : ℕ, x ^ a = x ^ (a % L) := by
    intro N _ x hx a
    conv_lhs => rw [← Nat.div_add_mod a L, pow_add, pow_mul, hx, one_pow, one_mul]
  have hvζ : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ L = 1 := by rw [← map_pow, hζn, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with hl | he' | hg
    · exact absurd hp (pow_lt_one₀ zero_le' hl hL0).ne
    · exact he'
    · exact absurd hp (one_lt_pow₀ hg hL0).ne'

  have hfixζ : ∀ τ ∈ ReciprocityTheory.Gal.Ine (F := E) A, τ ζ = ζ := by
    intro τ hτ
    refine GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA ?_ hζn (hτ.2 ζ hvζ.le)
    rw [← map_pow, hζn, map_one]

  have hfixπ : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → τ π = π := by
    intro τ hτ
    have h1 : (τ π / π) ^ L = 1 := by
      rw [div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
      rw [← he]; exact pow_ne_zero _ hπ
    have h2 := GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA h1 (one_pow L) (hτ π hπ)
    rwa [div_eq_one_iff_eq hπ] at h2

  have hopenH : ∀ (H : Subgroup (Formalism.ConjugateSelfDual.G E Ω)), IsOpen (H : Set (Formalism.ConjugateSelfDual.G E Ω)) →
      ∀ U : Set (Formalism.ConjugateSelfDual.G E Ω), (∀ τ ∈ U, ∀ g ∈ H, τ * g ∈ U) → IsOpen U := by
    intro H hH U hU
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    rw [← map_mul_left_nhds_one τ]
    exact Filter.mem_map.2 (Filter.mem_of_superset (hH.mem_nhds (one_mem _)) fun g hg => hU τ hτ g hg)
  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  haveI : FiniteDimensional E (IntermediateField.adjoin E {π}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hHo : IsOpen ((IntermediateField.adjoin E {π}).fixingSubgroup : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hloc : ∀ c : Ω, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | τ π = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopenH _ hHo _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg π
      (IntermediateField.mem_adjoin_simple_self E π)]
  have hfib : ∀ c : M, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | φ τ = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopenH _ hker _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [map_mul, (MonoidHom.mem_ker).1 hg, mul_one]
  let T : Set (Formalism.ConjugateSelfDual.G E Ω) := ⋃ a ∈ Finset.range L, {τ | φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π}
  have hTc : IsClosed T := by
    refine isClosed_biUnion_finset fun a _ => ?_
    exact (hfib _).inter (hloc _)
  let Q : Formalism.ConjugateSelfDual.G E Ω → Prop := fun τ =>
    τ ∈ ReciprocityTheory.Gal.Ine (F := E) A ∧ ∃ a : ℕ, φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π
  have hQ : ∀ τ ∈ Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), Q τ := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, 1, (pow_one _).symm, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ]⟩
      · exact ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hx, 0, by rw [hw x hx, pow_zero],
          by rw [hfixπ x hx, pow_zero, one_mul]⟩
    | one => exact ⟨one_mem _, 0, by rw [map_one, pow_zero], by rw [pow_zero, one_mul]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      obtain ⟨hyI, b, hb, hbπ⟩ := ihy
      refine ⟨mul_mem hxI hyI, a + b, by rw [map_mul, ha, hb, pow_add], ?_⟩
      rw [AlgEquiv.mul_apply, hbπ, map_mul, map_pow, hfixζ x hxI, haπ, pow_add]
      ring
    | inv x _ ihx =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      have hiI : x⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A := inv_mem hxI
      have hex : a * (L - 1) + a = a * L := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      refine ⟨hiI, a * (L - 1), ?_, ?_⟩
      · rw [map_inv, ha]
        symm
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_add, hex, pow_mul', hγL, one_pow]
      · have hxx : (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) (x π) = π := by
          rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
        have h1 : π = ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
          have h2 := congrArg (fun y => (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) y) haπ
          rw [hxx, map_mul, map_pow, hfixζ _ hiI] at h2
          exact h2
        calc (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π = ζ ^ (a * (L - 1) + a) * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
              rw [hex, pow_mul', hζn, one_pow, one_mul]
          _ = ζ ^ (a * (L - 1)) * (ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π) := by ring
          _ = ζ ^ (a * (L - 1)) * π := by rw [← h1]
  have hST : ((Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
        Set (Formalism.ConjugateSelfDual.G E Ω)) ⊆ T := by
    intro τ hτ
    obtain ⟨-, a, ha, haπ⟩ := hQ τ hτ
    refine Set.mem_biUnion (x := a % L) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hn))) ?_
    exact ⟨by rw [ha, hred _ hγL a], by rw [haπ, hred _ hζn a]⟩
  have hσT : σ ∈ T := closure_minimal hST hTc (hγ.2 hσ)
  simp only [T, Set.mem_iUnion] at hσT
  obtain ⟨a, -, h⟩ := hσT
  exact ⟨a, h⟩

end GlobalTheory.TameJoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterOfPolynomialOfCuspidalLabel
section
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.SerCmp.LabConv

theorem isCuspOf_of_hasCuspLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : Formalism.L2.NT.IsGenSys L.gen), t = L.teich → ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → GlobalTheory.GLq.IsCusp (fun x => V.character x) → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht L.gen hζ) V P → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) := by
  intro g _ L t ht hζ htL d V P hd hcusp hlab
  subst htL
  obtain ⟨hm, hi, hX, hdeg, hval⟩ := hlab
  rw [Fintype.card_fin] at hdeg
  have hPl : GlobalTheory.GLq.IsPrimeLab d P := ⟨hm, hi, Formalism.L2.NT.coeff_zero_ne_of_monic_irr hm hi hX, hdeg⟩
  refine ⟨hPl, hcusp, ?_⟩
  intro x hx y hy z hz
  have hd0 : 0 < d := hd
  have hcpl : GlobalTheory.GLq.IsPrimeLab d (y : GlobalTheory.GLq.Mt g d).charpoly := by
    refine ⟨Matrix.charpoly_monic _, hy, ?_, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]⟩
    intro h0
    have hdet := Matrix.det_eq_sign_charpoly_coeff (y : GlobalTheory.GLq.Mt g d)
    rw [h0, mul_zero] at hdet
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit y) |>.ne_zero hdet
  have hz1 : z ^ (g ^ d - 1) = 1 := GlobalTheory.GLq.LabelUnique.pow_sub_one_eq_one hcpl hz
  have hx1 : x ^ (g ^ d - 1) = 1 := GlobalTheory.GLq.LabelUnique.pow_sub_one_eq_one hPl hx
  have hprim : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := by
    rw [← L.gen_order d hd0]; exact IsPrimitiveRoot.orderOf _
  haveI : NeZero (g ^ d - 1) := ⟨by
    have := Nat.one_lt_pow hd0.ne' (Fact.out : g.Prime).one_lt
    omega⟩
  obtain ⟨m, -, hmz⟩ := hprim.eq_pow_of_pow_eq_one hz1
  have hax : aeval x P = 0 := GlobalTheory.GLq.LabelUnique.aeval_eq_zero_of_mem hm.ne_zero hx
  have haz : aeval z (y : GlobalTheory.GLq.Mt g d).charpoly = 0 :=
    GlobalTheory.GLq.LabelUnique.aeval_eq_zero_of_mem (Matrix.charpoly_monic _).ne_zero hz
  have hmz' : (Formalism.L2.NT.convC L.teich ht L.gen hζ).gen (Fintype.card (Fin d)) ^ m = z := by
    rw [Fintype.card_fin]; exact hmz
  have e := hval x hax y hy z haz m hmz'
  simp only [Fintype.card_fin, ZMod.card] at e
  have htx : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx1, map_one]
  show LinearMap.trace ℂ V (V.ρ y) = _
  rw [e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hmz, ← pow_mul, GlobalTheory.GLq.LabelUnique.thetaOf_gen_pow L d hd0 x htx]
  rfl

end GlobalTheory.SerCmp.LabConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamV
section
open Formalism.BasicNotions

namespace GlobalTheory.PadicPlaceExt

theorem exists_lam {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [NumberField L] (e : L →+* ℂ) (φ : L →+* ℂ_[p]) :
    ∃ lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p], ∀ z : L, φ z = lamV lam (e z) := by
  have hmem : ∀ z : L, e z ∈ algebraicClosure ℚ ℂ := fun z =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom e.toRatAlgHom)
  let e' : L →+* algebraicClosure ℚ ℂ := e.codRestrict (algebraicClosure ℚ ℂ) hmem
  let : Algebra L (algebraicClosure ℚ ℂ) := e'.toAlgebra
  let : Algebra L ℂ_[p] := φ.toAlgebra
  have : IsScalarTower ℚ L (algebraicClosure ℚ ℂ) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic L (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  let f : algebraicClosure ℚ ℂ →ₐ[L] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.toRingHom, fun z => ?_⟩
  rw [lamV, dite_eq_left (hmem z)]
  exact (f.commutes z).symm

end GlobalTheory.PadicPlaceExt
end

