module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerUnitsFiniteModPowersAtLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0144
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationUniqueOnLthRootLevelFields
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.UniqRoot

theorem exists_finite_field {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (A : Set E) (hfin : A.Finite)
    (hA : ∀ a ∈ A, IsAlgebraic (IntermediateField.adjoin F {t}) a) :
    ∃ (L : IntermediateField F E) (ht : t ∈ L), A ⊆ L ∧
      FiniteDimensional (IntermediateField.adjoin F {(⟨t, ht⟩ : L)}) L := by
  let K₀ : IntermediateField F E := IntermediateField.adjoin F {t}
  let L' : IntermediateField K₀ E := IntermediateField.adjoin K₀ A
  haveI : Finite A := hfin
  have hL' : FiniteDimensional K₀ L' := IntermediateField.finiteDimensional_adjoin fun a ha => (hA a ha).isIntegral
  let L : IntermediateField F E := L'.restrictScalars F
  have hK : ∀ x : K₀, (x : E) ∈ L := fun x => L'.algebraMap_mem x
  have ht : t ∈ L := hK ⟨t, IntermediateField.mem_adjoin_simple_self F t⟩
  refine ⟨L, ht, fun a ha => IntermediateField.subset_adjoin K₀ A ha, ?_⟩
  let K' : IntermediateField F L := IntermediateField.adjoin F {(⟨t, ht⟩ : L)}
  have hmap : K'.map L.val = K₀ := by
    simp only [K', K₀, IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ x : K₀, (⟨x, hK x⟩ : L) ∈ K' := by
    intro x
    have hx : (x : E) ∈ K'.map L.val := by rw [hmap]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = ⟨x, hK x⟩ := Subtype.ext hyx
    exact this ▸ hy
  let φ : K₀ →+* K' :=
    { toFun := fun x => ⟨⟨x, hK x⟩, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra K₀ K' := φ.toAlgebra
  letI : Algebra K₀ L := (inferInstance : Algebra K₀ L')
  haveI : Module.Finite K₀ L := hL'
  haveI : IsScalarTower K₀ K' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K₀ K' L

theorem valuation_eq_one_iff' {K : Type} [Field K] (W : ValuationSubring K) (x : K) :
    W.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ W ∧ x⁻¹ ∈ W := by
  rw [← W.valuation_le_one_iff, ← W.valuation_le_one_iff, map_inv₀]
  constructor
  · intro h
    refine ⟨?_, h.le, by rw [h, inv_one]⟩
    rintro rfl
    simp at h
  · rintro ⟨h0, h1, h2⟩
    have hp : 0 < W.valuation x := zero_lt_iff.2 ((map_ne_zero _).2 h0)
    exact le_antisymm h1 ((inv_le_one₀ hp).1 h2)

theorem gauss_comap {F E : Type} [Field F] [Field E] [Algebra F E] {t : E} (L : IntermediateField F E) (ht : t ∈ L)
    {V : ValuationSubring F} {W : ValuationSubring E} (h : Gauss t V W) :
    Gauss (⟨t, ht⟩ : L) V (W.comap (algebraMap L E)) := by
  refine ⟨fun a => ?_, fun P hP hu => ?_⟩
  · rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact h.1 a
  · have h1 := (valuation_eq_one_iff' _ _).1 (h.2 P hP hu)
    have e : algebraMap L E (Polynomial.aeval (⟨t, ht⟩ : L) P) = Polynomial.aeval t P :=
      (Polynomial.aeval_algHom_apply L.val (⟨t, ht⟩ : L) P).symm
    rw [valuation_eq_one_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, e]
    refine ⟨fun h0 => h1.1 ?_, h1.2⟩
    rw [← e, h0, map_zero]

theorem transcendental_j {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    Transcendental Ω X.jK := by
  intro h
  have hd := IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible h.isIntegral)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one Ω X.jK hd
  have h1 := X.j_exp.1
  rw [← hc, AlgHom.commutes] at h1
  simp [HahnSeries.algebraMap_apply', HahnSeries.coeff_single] at h1

theorem gauss_unique_root : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring (AlgebraicClosure X.K), Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₁ → Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₂ → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), f ∈ X.Un l → Lev X M₀ f → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → ∀ x ∈ IntermediateField.adjoin (levF X M₀) {θ}, x ∈ W₁ ↔ x ∈ W₂ := by
  classical
  intro Ω _ _ _ ε X hj l M₀ hl hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have halgΩ : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : @Algebra.IsAlgebraic ℚ Ω _ _ DivisionRing.toRatAlgebra := by
    convert halgΩ
    exact Subsingleton.elim _ _
  obtain ⟨R, hR⟩ := GlobalTheory.KZ.FinLev.finite_mod_powers ε X ε.injective hj M₀ l hM hl.pos
  obtain ⟨T, -, hT⟩ := GlobalTheory.T.exists_finset_span_principalCongruenceLevel_functions ε X hj M₀ hM
  let E := AlgebraicClosure X.K
  let ι : X.K →ₐ[Ω] E := IsScalarTower.toAlgHom Ω X.K E
  let t : E := algebraMap X.K E X.jK
  have hmap : (IntermediateField.adjoin Ω {X.jK}).map ι = IntermediateField.adjoin Ω {t} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ c : IntermediateField.adjoin Ω {X.jK}, ι c ∈ IntermediateField.adjoin Ω {t} :=
    fun c => hmap ▸ ⟨c, c.2, rfl⟩
  have halg : ∀ f : X.K, IsAlgebraic (IntermediateField.adjoin Ω {t}) (algebraMap X.K E f) := by
    intro f
    let φ : IntermediateField.adjoin Ω {X.jK} →+* IntermediateField.adjoin Ω {t} :=
      (ι.toRingHom.comp (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K)).codRestrict
        (IntermediateField.adjoin Ω {t}) hmem
    exact ((X.alg_j f).isIntegral.map_of_comp_eq φ (algebraMap X.K E) (RingHom.ext fun _ => rfl)).isAlgebraic
  let A : Set E := algebraMap X.K E '' (T : Set X.K) ∪
    ⋃ r ∈ (R : Set X.Kˣ), {y : E | y ^ l = algebraMap X.K E (r : X.K)}
  have hAfin : A.Finite := by
    refine (T.finite_toSet.image _).union (R.finite_toSet.biUnion fun r _ => ?_)
    refine (Polynomial.nthRoots l (algebraMap X.K E (r : X.K))).toFinset.finite_toSet.subset fun y hy => ?_
    simpa [Polynomial.mem_nthRoots hl.pos] using hy
  have hAalg : ∀ a ∈ A, IsAlgebraic (IntermediateField.adjoin Ω {t}) a := by
    rintro a (⟨f, -, rfl⟩ | ha)
    · exact halg f
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq] at ha
      obtain ⟨r, -, hr⟩ := ha
      exact IsAlgebraic.of_pow hl.pos (hr ▸ halg r)
  obtain ⟨L, ht, hAL, hfin⟩ := exists_finite_field (F := Ω) t A hAfin hAalg
  have htr : Transcendental Ω (⟨t, ht⟩ : L) := by
    intro h
    have h1 : IsAlgebraic Ω (ι X.jK) := h.algHom L.val
    exact transcendental_j X ((isAlgebraic_algHom_iff ι ι.toRingHom.injective).1 h1)
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.BertiniNoether.gauss_extension_unique_of_gauss (F := Ω) (⟨t, ht⟩ : L) htr hfin
  have hlev : ∀ f : X.K, Lev X M₀ f → algebraMap X.K E f ∈ L := by
    intro f hf
    have hsp := hT f hf
    clear hf
    induction hsp using Submodule.span_induction with
    | mem x hx => exact hAL (Or.inl ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact L.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact L.add_mem hx hy
    | smul c x _ hx =>
      have hc : ι c ∈ L := (IntermediateField.adjoin_simple_le_iff.2 ht) (hmem c)
      have e : algebraMap X.K E (c • x) = ι c * algebraMap X.K E x := by
        rw [IntermediateField.smul_def, smul_eq_mul, map_mul]
        rfl
      rw [e]
      exact L.mul_mem hc hx
  have hlevF : levF X M₀ ≤ L := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hlev f hf
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ θ f hf hfl hθ x hx => ?_⟩
  have hW := hS q hq hqS V hV _ _ (gauss_comap L ht h₁) (gauss_comap L ht h₂)
  obtain ⟨r, hr, g, hg, c, hc, hfe⟩ := hR f hf hfl
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hl.pos
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hl.ne_zero] at hd
    exact hc hd.symm
  let u : E := algebraMap X.K E (g : X.K) * algebraMap Ω E d
  have hu0 : u ≠ 0 := mul_ne_zero ((map_ne_zero _).2 g.ne_zero) ((map_ne_zero _).2 hd0)
  have huL : u ∈ L := L.mul_mem (hlev g hg) (L.algebraMap_mem d)
  have hy : (θ / u) ^ l = algebraMap X.K E (r : X.K) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ hu0), hθ, hfe, mul_pow, ← map_pow, ← map_pow, hd, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_assoc]
  have hθL : θ ∈ L := by
    have h1 : θ / u ∈ L := hAL (Or.inr (Set.mem_biUnion (Finset.mem_coe.2 hr) hy))
    have := L.mul_mem h1 huL
    rwa [div_mul_cancel₀ _ hu0] at this
  have hxL : x ∈ L := by
    have hle : IntermediateField.adjoin (levF X M₀) {θ} ≤ IntermediateField.extendScalars hlevF :=
      IntermediateField.adjoin_simple_le_iff.2 hθL
    exact hle hx
  have := SetLike.ext_iff.1 hW ⟨x, hxL⟩
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at this
  exact this

end GlobalTheory.KZ.ES.UniqRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStable
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem modGrowth_pow_bounds (y : ℝ) (hy : 0 < y) (A : ℕ) :
    max y y⁻¹ ^ A ≤ y ^ A + (y ^ A)⁻¹ ∧ y ^ A + (y ^ A)⁻¹ ≤ 2 * max y y⁻¹ ^ A := by
  rw [← inv_pow]
  have h1 : 0 < y ^ A := pow_pos hy A
  have h2 : 0 < y⁻¹ ^ A := pow_pos (inv_pos.mpr hy) A
  rcases le_total y y⁻¹ with h | h
  · rw [max_eq_right h]
    have : y ^ A ≤ y⁻¹ ^ A := pow_le_pow_left₀ hy.le h A
    constructor <;> linarith
  · rw [max_eq_left h]
    have : y⁻¹ ^ A ≤ y ^ A := pow_le_pow_left₀ (inv_pos.mpr hy).le h A
    constructor <;> linarith

theorem one_le_max_inv (y : ℝ) (hy : 0 < y) : 1 ≤ max y y⁻¹ := by
  rcases le_total 1 y with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hy).mpr h)

theorem mod_of_bound (F : ℍ → ℂ) (C : ℝ) (A : ℕ) (h : ∀ τ : ℍ, ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A) :
    Mod F := by
  refine ⟨max C 0, A, fun τ => ?_⟩
  obtain ⟨b1, _⟩ := modGrowth_pow_bounds τ.im τ.im_pos A
  have hM : 0 ≤ max τ.im τ.im⁻¹ ^ A :=
    pow_nonneg (le_trans zero_le_one (one_le_max_inv _ τ.im_pos)) A
  calc ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A := h τ
    _ ≤ max C 0 * max τ.im τ.im⁻¹ ^ A := mul_le_mul_of_nonneg_right (le_max_left _ _) hM
    _ ≤ _ := mul_le_mul_of_nonneg_left b1 (le_max_right _ _)

theorem bound_of_mod (F : ℍ → ℂ) (hF : Mod F) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ τ : ℍ, ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A := by
  obtain ⟨C, A, h⟩ := hF
  refine ⟨2 * max C 0, A, by positivity, fun τ => ?_⟩
  obtain ⟨_, b2⟩ := modGrowth_pow_bounds τ.im τ.im_pos A
  have hh : 0 ≤ τ.im ^ A + (τ.im ^ A)⁻¹ :=
    add_nonneg (pow_pos τ.im_pos A).le (inv_pos.mpr (pow_pos τ.im_pos A)).le
  calc ‖F τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) := h τ
    _ ≤ max C 0 * (τ.im ^ A + (τ.im ^ A)⁻¹) := mul_le_mul_of_nonneg_right (le_max_left _ _) hh
    _ ≤ max C 0 * (2 * max τ.im τ.im⁻¹ ^ A) := mul_le_mul_of_nonneg_left b2 (le_max_right _ _)
    _ = _ := by ring

theorem mod_add (F G : ℍ → ℂ) (hF : Mod F) (hG : Mod G) : Mod (fun τ => F τ + G τ) := by
  obtain ⟨C, A, hC, h1⟩ := bound_of_mod F hF
  obtain ⟨D, B, hD, h2⟩ := bound_of_mod G hG
  refine mod_of_bound _ (C + D) (A + B) fun τ => ?_
  have hM := one_le_max_inv _ τ.im_pos
  have eA : max τ.im τ.im⁻¹ ^ A ≤ max τ.im τ.im⁻¹ ^ (A + B) := pow_le_pow_right₀ hM (Nat.le_add_right A B)
  have eB : max τ.im τ.im⁻¹ ^ B ≤ max τ.im τ.im⁻¹ ^ (A + B) := pow_le_pow_right₀ hM (Nat.le_add_left B A)
  calc ‖F τ + G τ‖ ≤ ‖F τ‖ + ‖G τ‖ := norm_add_le _ _
    _ ≤ C * max τ.im τ.im⁻¹ ^ A + D * max τ.im τ.im⁻¹ ^ B := add_le_add (h1 τ) (h2 τ)
    _ ≤ C * max τ.im τ.im⁻¹ ^ (A + B) + D * max τ.im τ.im⁻¹ ^ (A + B) :=
        add_le_add (mul_le_mul_of_nonneg_left eA hC) (mul_le_mul_of_nonneg_left eB hD)
    _ = _ := by ring

theorem mod_mul (F G : ℍ → ℂ) (hF : Mod F) (hG : Mod G) : Mod (fun τ => F τ * G τ) := by
  obtain ⟨C, A, hC, h1⟩ := bound_of_mod F hF
  obtain ⟨D, B, hD, h2⟩ := bound_of_mod G hG
  refine mod_of_bound _ (C * D) (A + B) fun τ => ?_
  have hM := le_trans zero_le_one (one_le_max_inv _ τ.im_pos)
  calc ‖F τ * G τ‖ = ‖F τ‖ * ‖G τ‖ := norm_mul _ _
    _ ≤ (C * max τ.im τ.im⁻¹ ^ A) * (D * max τ.im τ.im⁻¹ ^ B) :=
        mul_le_mul (h1 τ) (h2 τ) (norm_nonneg _) (mul_nonneg hC (pow_nonneg hM A))
    _ = _ := by ring

theorem mod_const (c : ℂ) : Mod fun _ => c :=
  mod_of_bound _ ‖c‖ 0 fun τ => by simp

theorem im_slz_arg (δ : M2) (hc : δ 1 0 = 0) (τ : ℍ) :
    (((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)))).im
      = (δ 0 0 : ℝ) / (δ 1 1 : ℝ) * τ.im := by
  rw [hc]
  simp [Complex.div_im]
  rcases eq_or_ne ((δ 1 1 : ℤ) : ℝ) 0 with h | h
  · simp [h]
  · field_simp

theorem max_inv_mul_le (r y : ℝ) (hr : 0 < r) (hy : 0 < y) :
    max (r * y) (r * y)⁻¹ ≤ max r r⁻¹ * max y y⁻¹ := by
  have h1 := one_le_max_inv r hr
  have h2 := one_le_max_inv y hy
  rw [mul_inv]
  apply max_le
  · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) hy.le (by linarith)
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (inv_pos.mpr hy).le (by linarith)

theorem mod_slz (F : ℍ → ℂ) (k : ℕ) (δ : M2) (hdet : 0 < δ.det) (hc : δ 1 0 = 0) (hF : Mod F) :
    Mod (slz k δ F) := by
  obtain ⟨C, A, hC0, hC⟩ := bound_of_mod F hF
  have hdet' : δ.det = δ 0 0 * δ 1 1 := by rw [Matrix.det_fin_two, hc]; ring
  have had : (0 : ℝ) < (δ 0 0 : ℝ) * (δ 1 1 : ℝ) := by
    have : (0 : ℤ) < δ 0 0 * δ 1 1 := hdet' ▸ hdet
    exact_mod_cast this
  have hd : (δ 1 1 : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at had; exact lt_irrefl _ had
  have hrpos : (0 : ℝ) < (δ 0 0 : ℝ) / (δ 1 1 : ℝ) := by
    have : (δ 0 0 : ℝ) / (δ 1 1 : ℝ) = (δ 0 0 : ℝ) * δ 1 1 / ((δ 1 1 : ℝ) ^ 2) := by
      field_simp
    rw [this]; exact div_pos had (by positivity)
  set r : ℝ := (δ 0 0 : ℝ) / (δ 1 1 : ℝ) with hr
  set K : ℝ := ‖((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹‖ with hK
  set R : ℝ := max r r⁻¹ with hR
  have hR1 : 1 ≤ R := one_le_max_inv r hrpos
  refine mod_of_bound _ (K * (C * R ^ A)) A fun τ => ?_
  have him := im_slz_arg δ hc τ
  rw [← hr] at him
  have hz : 0 < (((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)))).im := by
    rw [him]; exact mul_pos hrpos τ.im_pos
  set w : ℍ := ofComplex ((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ))) with hw
  have hwim : w.im = r * τ.im := by
    rw [hw, ofComplex_apply_of_im_pos hz]; exact him
  have hMw : max w.im w.im⁻¹ ^ A ≤ R ^ A * max τ.im τ.im⁻¹ ^ A := by
    rw [← mul_pow, hwim]
    exact pow_le_pow_left₀ (le_trans zero_le_one (one_le_max_inv _ (mul_pos hrpos τ.im_pos)))
      (max_inv_mul_le r τ.im hrpos τ.im_pos) A
  have hslz : slz k δ F τ = (((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹) * F w := by
    rw [slz, hw]; simp [hc]
  rw [hslz, norm_mul, ← hK]
  have hK0 : 0 ≤ K := norm_nonneg _
  calc K * ‖F w‖ ≤ K * (C * max w.im w.im⁻¹ ^ A) := mul_le_mul_of_nonneg_left (hC w) hK0
    _ ≤ K * (C * (R ^ A * max τ.im τ.im⁻¹ ^ A)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMw hC0) hK0
    _ = _ := by ring

theorem mod_algebra : (∀ F G : ℍ → ℂ, Mod F → Mod G → Mod (fun τ => F τ + G τ) ∧ Mod (fun τ => F τ * G τ)) ∧ (∀ c : ℂ, Mod fun _ => c) ∧ (∀ (F : ℍ → ℂ) (k : ℕ) (δ : M2), 0 < δ.det → δ 1 0 = 0 → Mod F → Mod (slz k δ F)) :=
  ⟨fun F G hF hG => ⟨mod_add F G hF hG, mod_mul F G hF hG⟩, mod_const,
    fun F k δ hdet hc hF => mod_slz F k δ hdet hc hF⟩

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthQExpansionOfCoeffPolynomialGrow
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma pow_succ_le_factorial_mul_choose (n A : ℕ) :
    ((n : ℝ) + 1) ^ A ≤ (A.factorial : ℝ) * ((n + A).choose A : ℕ) := by
  have h := Nat.pow_succ_le_ascFactorial (n + 1) A
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at h
  exact_mod_cast h

lemma norm_qterm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-2 * π * τ.im) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma one_sub_exp_inv_le (y : ℝ) (hy : 0 < y) :
    (1 - Real.exp (-2 * π * y))⁻¹ ≤ 1 + y⁻¹ := by
  set t := 2 * π * y with ht
  have htpos : 0 < t := by positivity
  have hty : y ≤ t := by
    have : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    nlinarith
  have h1 : Real.exp (-t) ≤ (1 + t)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp t])
  have h2 : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have : t / (1 + t) = 1 - (1 + t)⁻¹ := by field_simp; ring
    linarith
  have h3 : (1 - Real.exp (-t))⁻¹ ≤ (t / (1 + t))⁻¹ := inv_anti₀ (by positivity) h2
  have h4 : (t / (1 + t))⁻¹ = 1 + t⁻¹ := by field_simp; ring
  have h5 : t⁻¹ ≤ y⁻¹ := inv_anti₀ hy hty
  have : -2 * π * y = -t := by rw [ht]; ring
  rw [this]
  linarith

lemma one_add_inv_pow_le (y : ℝ) (hy : 0 < y) (B : ℕ) :
    (1 + y⁻¹) ^ B ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
  rcases le_or_gt 1 y with h | h
  · have : 1 + y⁻¹ ≤ 2 * y := by
      have : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
      linarith
    calc (1 + y⁻¹) ^ B ≤ (2 * y) ^ B := pow_le_pow_left₀ (by positivity) this B
      _ = 2 ^ B * y ^ B := mul_pow _ _ _
      _ ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
        have : 0 ≤ (y ^ B)⁻¹ := by positivity
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) B]
  · have : 1 + y⁻¹ ≤ 2 * y⁻¹ := by
      have : 1 ≤ y⁻¹ := one_le_inv₀ hy |>.mpr h.le
      linarith
    calc (1 + y⁻¹) ^ B ≤ (2 * y⁻¹) ^ B := pow_le_pow_left₀ (by positivity) this B
      _ = 2 ^ B * (y ^ B)⁻¹ := by rw [mul_pow, inv_pow]
      _ ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
        have : 0 ≤ y ^ B := by positivity
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) B]

theorem mod_qs_of_polyB : ∀ a : ℕ → ℂ, PolyB a → Mod (qs a) := by
  intro a ⟨C, A, hC⟩
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp at this
    exact le_trans (norm_nonneg _) this
  refine ⟨C * A.factorial * 2 ^ (A + 1), A + 1, fun τ => ?_⟩
  set y := τ.im
  have hy : 0 < y := τ.im_pos
  set r := Real.exp (-2 * π * y) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    have := Real.pi_pos
    calc r < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0.le]
  have hS := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) A hrn
  have hbound : ∀ n : ℕ, ‖a n * cexp (2 * π * Complex.I * n * τ)‖ ≤
      (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) := by
    intro n
    rw [norm_mul, norm_qterm]
    have h1 := hC n
    have h2 := pow_succ_le_factorial_mul_choose n A
    calc ‖a n‖ * r ^ n ≤ C * ((n : ℝ) + 1) ^ A * r ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ C * ((A.factorial : ℝ) * ((n + A).choose A : ℕ)) * r ^ n := by
          gcongr
      _ = (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) := by ring
  have hsum2 : HasSum (fun n : ℕ => (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n))
      ((C * A.factorial) * (1 / (1 - r) ^ (A + 1))) := hS.mul_left _
  have hsumm : Summable (fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hsum2.summable
  have key : ‖qs a τ‖ ≤ (C * A.factorial) * (1 / (1 - r) ^ (A + 1)) := by
    unfold qs
    calc ‖∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * τ)‖
        ≤ ∑' n : ℕ, ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := norm_tsum_le_tsum_norm hsumm
      _ ≤ ∑' n : ℕ, (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) :=
          hsumm.tsum_le_tsum hbound hsum2.summable
      _ = _ := hsum2.tsum_eq
  have hinv : 1 / (1 - r) ^ (A + 1) ≤ 2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹) := by
    rw [one_div, ← inv_pow]
    calc ((1 - r)⁻¹) ^ (A + 1) ≤ (1 + y⁻¹) ^ (A + 1) :=
          pow_le_pow_left₀ (by have : 0 < 1 - r := by linarith
                               positivity) (one_sub_exp_inv_le y hy) _
      _ ≤ _ := one_add_inv_pow_le y hy _
  calc ‖qs a τ‖ ≤ (C * A.factorial) * (1 / (1 - r) ^ (A + 1)) := key
    _ ≤ (C * A.factorial) * (2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = C * A.factorial * 2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹) := by ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeStableCongruenceConjDiamondMatrix
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory.KZ.StabHecke

theorem congruenceCondition_conj_diamond : ∀ (N l d : ℕ) (σ : SL(2, ℤ)) (r : Matrix (Fin 2) (Fin 2) ℤ), IsDiam N l d σ → PP N l r →
    PP N l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  intro N l d σ r hσ hr
  obtain ⟨h1, h2, -, h4⟩ := diam_facts hσ
  obtain ⟨r1, r2, r3, r4⟩ := hr
  have e00 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 =
      r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (r 0 0) * h4
  have e10 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
      σ 1 0 * (σ 1 1 * r 0 0 - σ 1 0 * r 0 1 - σ 1 1 * r 1 1) + σ 1 1 * σ 1 1 * r 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00, show r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 - 1 =
        (r 0 0 - 1) + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 by ring]
    exact dvd_add (dvd_add r1 (dvd_mul_of_dvd_left h1 _)) (dvd_mul_of_dvd_right r2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right r2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_right r3 _)
  · rw [e00]
    obtain ⟨s, hs⟩ := h2
    obtain ⟨t, ht⟩ := r3
    have e : r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 =
        r 0 0 + (l : ℤ) * (s * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * t) := by
      rw [hs, ht]; ring
    rw [e]
    exact r4.add_mul_left_left _

end GlobalTheory.KZ.StabHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmallTracesSubgroupGaloisTowerTopStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallTraces_subgroup_galois_towerTop : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (H : Subgroup (Gal p Ω)), H ≤ ⨅ n, Gn T n → ∀ (S : Finset Ω) (j : ℕ), 1 ≤ j → ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt (p := p) y ∧ (∀ g ∈ E, g ∈ H) ∧ (∀ h ∈ H, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧ ∑ g ∈ E, g y = T.ζ j - 1 := by
  first | exact @GlobalTheory.K5.small_traces_subgroup | exact GlobalTheory.K5.small_traces_subgroup | (intros; apply GlobalTheory.K5.small_traces_subgroup <;> assumption)
end

