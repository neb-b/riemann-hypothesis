module

public import Mathlib
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0013
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle0005
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0014
public import GroundTheory.GlobalFields.ComplexMultiplication.InseparableFrobenius

@[expose] public section

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityClass
section
open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

theorem image_mul_image_mul (c d : ℂ) (S : Set ℂ) :
    (c * ·) '' ((d * ·) '' S) = ((c * d) * ·) '' S := by
  rw [Set.image_image]
  congr 1
  funext x
  ring

theorem eq_image_mul_inv {c : ℂ} (hc : c ≠ 0) {A B : Set ℂ} (h : B = (c * ·) '' A) :
    A = (c⁻¹ * ·) '' B := by
  rw [h, image_mul_image_mul, inv_mul_cancel₀ hc]
  simp only [one_mul, Set.image_id']

theorem image_ringEquiv_image_mul (σ : ℂ ≃+* ℂ) (c : ℂ) (S : Set ℂ) :
    σ '' ((c * ·) '' S) = (σ c * ·) '' (σ '' S) := by
  rw [Set.image_image, Set.image_image]
  simp only [map_mul]

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ)

theorem image_idealLattice (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k)
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    σ '' (idealLattice σ₀ I : Set ℂ) = idealLattice σ₀ I := by
  ext z
  simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (hσ x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨σ₀ x, ⟨x, hx, rfl⟩, hσ x⟩

variable (hK : finrank ℚ K = 2) [_root_.NumberField.IsTotallyComplex K]
include hK

theorem latticeHom_eq_idealLattice (L L' : PeriodPair) (hL : periodLatticeEnd L = cmRingOfEmbedding σ₀)
    (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h : L'.lattice = idealLattice σ₀ ↑𝔟 * L.lattice) :
    (latticeHom L L' : Set ℂ) = idealLattice σ₀ ↑𝔟 := by
  obtain ⟨I, c, hc, hI⟩ := exists_idealLattice_of_latticeEnd_eq σ₀ hK L hL
  have hI' := idealLattice_mul_homothetic σ₀ (I : FractionalIdeal (𝓞 K)⁰ K) ↑𝔟 hI
  rw [← h] at hI'
  have hmem' : ∀ z, z ∈ L'.lattice ↔ ∃ x ∈ ((𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I), c * σ₀ x = z := by
    intro z
    rw [← SetLike.mem_coe, hI']
    simp only [Set.mem_image, SetLike.mem_coe, mem_idealLattice]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨σ₀ x, ⟨x, hx, rfl⟩, rfl⟩
  have hmemL : ∀ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K), c * σ₀ x ∈ L.lattice := by
    intro x hx
    rw [← SetLike.mem_coe, hI]
    exact ⟨σ₀ x, (mem_idealLattice σ₀).2 ⟨x, hx, rfl⟩, rfl⟩
  ext α
  simp only [SetLike.mem_coe, mem_latticeHom]
  constructor
  · intro hα
    have hI0 : ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥ := by
      rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
      exact I.ne_zero
    obtain ⟨i₀, hi₀, hi₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    obtain ⟨k₀, -, hk₀⟩ := (hmem' _).1 (hα _ (hmemL i₀ hi₀))
    have hσi₀ : σ₀ i₀ ≠ 0 := (map_ne_zero σ₀).2 hi₀0
    have hy : σ₀ (k₀ / i₀) = α := by
      rw [map_div₀, div_eq_iff hσi₀]
      exact mul_left_cancel₀ hc (by rw [hk₀]; ring)
    set y := k₀ / i₀
    have hyI : ∀ i ∈ (I : FractionalIdeal (𝓞 K)⁰ K), y * i ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I := by
      intro i hi
      obtain ⟨k, hk, hke⟩ := (hmem' _).1 (hα _ (hmemL i hi))
      have : σ₀ k = σ₀ (y * i) := by
        rw [map_mul, hy]
        exact mul_left_cancel₀ hc (by rw [hke]; ring)
      rwa [← σ₀.injective this]
    have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (I : FractionalIdeal (𝓞 K)⁰ K) ≤
        (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * I := by
      rw [FractionalIdeal.mul_le]
      intro a ha b hb
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 K)⁰).1 ha
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r (hyI b hb)
    have hle' := mul_le_mul_left hle ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
    rw [mul_assoc, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one,
      mul_one] at hle'
    exact (mem_idealLattice σ₀).2
      ⟨y, hle' (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ y), hy⟩
  · intro hα l hl
    rw [h]
    exact Submodule.mul_mem_mul hα hl

theorem homConstSet_of_smul {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll = E'.toEll) :
    ∃ c : ℂ, c ≠ 0 ∧
      (homConstSet E.curve E'.curve : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
  obtain ⟨L, C, hL, hC, hE⟩ := E.exists_lattice σ₀ hK
  obtain ⟨L', hL'lat, hL'⟩ := exists_lattice_mul σ₀ hK L hL 𝔞
  have h1 := classGroup_smul_ellOf σ₀ hK L L' hL hL' 𝔞 hL'lat
  have h2 : E'.toEll = (CMCurve.ofLattice σ₀ L' hL').toEll := by
    rw [← h, ← hE]
    exact h1
  obtain ⟨C', hC'⟩ := (CMCurve.toEll_eq_iff _ _).1 h2
  have hC'' : C' • E'.curve = weierstrassCurve L' := hC'
  obtain ⟨d, hd, hset⟩ := homConstSet_vc C C' hC hC''
  rw [homConstSet_weierstrassCurve, latticeHom_eq_idealLattice σ₀ hK L L' hL 𝔞⁻¹ hL'lat] at hset
  exact ⟨d⁻¹, inv_ne_zero hd, eq_image_mul_inv hd hset⟩

theorem smul_toEll_of_homConstSet {E E' : CMCurve K} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {c : ℂ}
    (hc : c ≠ 0)
    (h : (homConstSet E.curve E'.curve : Set ℂ) = (c * ·) '' idealLattice σ₀ ↑𝔞⁻¹) :
    (ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll = E'.toEll := by
  obtain ⟨b, hb, -⟩ := existsUnique_smul_eq σ₀ hK E.toEll E'.toEll
  obtain ⟨J, rfl⟩ := classGroup_mk_surjective hK b
  obtain ⟨d, hd, h'⟩ := homConstSet_of_smul σ₀ hK hb
  have e : (idealLattice σ₀ ↑J⁻¹ : Set ℂ) = ((d⁻¹ * c) * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by
    rw [eq_image_mul_inv hd h', h, image_mul_image_mul]
  have hcls := (classGroup_mk_eq_iff σ₀ hK 𝔞⁻¹ J⁻¹).2 ⟨d⁻¹ * c, mul_ne_zero (inv_ne_zero hd) hc, e⟩
  rw [map_inv, map_inv, inv_inj] at hcls
  rw [hcls]
  exact hb

theorem ELL.map_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (a : ClassGroup (𝓞 K))
    (x : ELL K) :
    ELL.map σ ((ellMulAction σ₀ hK).smul a x) = (ellMulAction σ₀ hK).smul a (ELL.map σ x) := by
  obtain ⟨𝔞, rfl⟩ := classGroup_mk_surjective hK a
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  obtain ⟨E', hE'⟩ := ELL.exists_eq ((ellMulAction σ₀ hK).smul (ClassGroup.mk K 𝔞) E.toEll)
  rw [← hE', ELL.map_toEll, ELL.map_toEll]
  obtain ⟨c, hc, h⟩ := homConstSet_of_smul σ₀ hK hE'.symm
  refine (smul_toEll_of_homConstSet σ₀ hK (c := σ c) ((map_ne_zero σ).2 hc) ?_).symm
  calc (homConstSet (E.map σ).curve (E'.map σ).curve : Set ℂ)
      = σ '' homConstSet E.curve E'.curve := homConstSet_map (E := E.curve) (E' := E'.curve) σ
    _ = σ '' ((c * ·) '' idealLattice σ₀ ↑𝔞⁻¹) := by rw [h]
    _ = (σ c * ·) '' (σ '' idealLattice σ₀ ↑𝔞⁻¹) := image_ringEquiv_image_mul σ c _
    _ = (σ c * ·) '' idealLattice σ₀ ↑𝔞⁻¹ := by rw [image_idealLattice σ₀ σ hσ]

theorem ellMulAction_one_smul (x : ELL K) : (ellMulAction σ₀ hK).smul 1 x = x := by
  rw [ellMulAction_smul, one_mul, Equiv.apply_symm_apply]

theorem ellMulAction_mul_smul (a b : ClassGroup (𝓞 K)) (x : ELL K) :
    (ellMulAction σ₀ hK).smul (a * b) x =
      (ellMulAction σ₀ hK).smul a ((ellMulAction σ₀ hK).smul b x) := by
  rw [ellMulAction_smul, ellMulAction_smul, ellMulAction_smul, Equiv.symm_apply_apply, mul_assoc]

def galClass (σ : ℂ ≃+* ℂ) : ClassGroup (𝓞 K) :=
  (ellEquiv σ₀ hK).symm (ELL.map σ (ellEquiv σ₀ hK 1))

theorem ELL.map_eq_galClass_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    ELL.map σ x = (ellMulAction σ₀ hK).smul (galClass σ₀ hK σ) x := by
  have hx : x = (ellMulAction σ₀ hK).smul ((ellEquiv σ₀ hK).symm x) (ellEquiv σ₀ hK 1) := by
    rw [ellMulAction_smul, Equiv.symm_apply_apply, mul_one, Equiv.apply_symm_apply]
  rw [hx, ELL.map_smul σ₀ hK σ hσ]
  simp only [ellMulAction_smul, Equiv.symm_apply_apply, mul_one]
  exact congrArg (ellEquiv σ₀ hK) (mul_comm _ _)

theorem apply_j_eq_j_galClass_smul (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    σ (ELL.j x) = ELL.j ((ellMulAction σ₀ hK).smul (galClass σ₀ hK σ) x) := by
  rw [← ELL.j_map, ELL.map_eq_galClass_smul σ₀ hK σ hσ]

theorem galClass_one : galClass σ₀ hK 1 = 1 := by
  rw [galClass, ELL.map_one, Equiv.symm_apply_apply]

theorem galClass_mul (σ τ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k)
    (hτ : ∀ k : K, τ (σ₀ k) = σ₀ k) :
    galClass σ₀ hK (σ * τ) = galClass σ₀ hK σ * galClass σ₀ hK τ := by
  rw [galClass, ELL.map_mul, ELL.map_eq_galClass_smul σ₀ hK τ hτ,
    ELL.map_eq_galClass_smul σ₀ hK σ hσ, ← ellMulAction_mul_smul]
  simp only [ellMulAction_smul, Equiv.symm_apply_apply, mul_one]

theorem galClass_eq_one_iff (σ : ℂ ≃+* ℂ) (hσ : ∀ k : K, σ (σ₀ k) = σ₀ k) (x : ELL K) :
    galClass σ₀ hK σ = 1 ↔ σ (ELL.j x) = ELL.j x := by
  rw [apply_j_eq_j_galClass_smul σ₀ hK σ hσ]
  constructor
  · intro h
    rw [h, ellMulAction_one_smul]
  · intro h
    exact (ell_smul_eq_self_iff σ₀ hK _ x).1 (ELL.j_injective h)

end Elliptic
end GroundTheory.Global
end
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

theorem pow_eq_one_of_scale {F : Type*} [Field F] {E : WeierstrassCurve F} [E.IsElliptic]
    (hE : IsShortForm E) {u : F} (h4 : E.a₄ = u ^ 4 * E.a₄) (h6 : E.a₆ = u ^ 6 * E.a₆) :
    u ^ automorphismOrder E = 1 ∧ u ^ 12 = 1 := by
  by_cases hu : u = 0
  · subst hu
    rcases hE.a₄_ne_zero_or_a₆_ne_zero with h | h
    · exact absurd (by simpa using h4) h
    · exact absurd (by simpa using h6) h
  have hn : u ^ automorphismOrder E = 1 := by
    have := (scale_conditions_iff hE u⁻¹).mp ⟨by rw [inv_inv]; exact h4.symm,
      by rw [inv_inv]; exact h6.symm⟩
    rwa [inv_pow, inv_eq_one] at this
  refine ⟨hn, ?_⟩
  unfold automorphismOrder at hn
  split_ifs at hn
  · rw [show 12 = 4 * 3 by rfl, pow_mul, hn, one_pow]
  · rw [show 12 = 6 * 2 by rfl, pow_mul, hn, one_pow]
  · rw [show 12 = 2 * 6 by rfl, pow_mul, hn, one_pow]

section AlgClosed

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]


omit [IsAlgClosed F] [A.IsElliptic] [B.IsElliptic] in
theorem vcPoint_constPoint (C : VariableChange F) (hC : C • A = B) (R : A.toAffine.Point) :
    vcPoint (C.baseChange A.toAffine.FunctionField) (Elliptic.baseChange_smul_eq C _ hC)
        (constPoint A R) = constMap B A.toAffine.FunctionField (vcPoint C hC R) := by
  cases R with
  | zero => rfl
  | some x y h =>
    obtain ⟨h', e⟩ := constPoint_some A h
    rw [e, vcPoint_some, vcPoint_some]
    show Point.some _ _ _ = Point.some _ _ _
    rw [Point.some.injEq]
    exact ⟨(map_vcX C (algebraMap F _) x).symm, (map_vcY C (algebraMap F _) x y).symm⟩

theorem pointMap_eq_vcPoint (C : VariableChange F) (hC : C • A = B) (ψ : Isogeny A B)
    (hψ : ψ.1 = vcPoint (C.baseChange A.toAffine.FunctionField)
      (Elliptic.baseChange_smul_eq C _ hC) (genericPoint A)) (R : A.toAffine.Point) :
    ψ.pointMap R = vcPoint C hC R := by
  apply Isogeny.pointMap_eq_of_map_translate
  rw [hψ, Elliptic.map_vcPoint C (translate A R) hC, map_translate_genericPoint, vcPoint_add,
    vcPoint_constPoint]

theorem pointMap_some_of_scale (hA : IsShortForm A) (hB : IsShortForm B) (u : Fˣ)
    (h4 : B.a₄ = (u : F) ^ 4 * A.a₄) (h6 : B.a₆ = (u : F) ^ 6 * A.a₆) (ψ : Isogeny A B)
    (hx : ψ.x = algebraMap F A.toAffine.FunctionField ((u : F) ^ 2) * genX A)
    (hy : ψ.y = algebraMap F A.toAffine.FunctionField ((u : F) ^ 3) * genY A)
    {x y : F} (h : A.toAffine.Nonsingular x y) :
    ∃ h' : B.toAffine.Nonsingular ((u : F) ^ 2 * x) ((u : F) ^ 3 * y),
      ψ.pointMap (.some x y h) = .some _ _ h' := by
  let C : VariableChange F := ⟨u⁻¹, 0, 0, 0⟩
  have hC : C • A = B := by
    ext
    · simp [C, variableChange_a₁, hA.a₁_eq, hB.a₁_eq]
    · simp [C, variableChange_a₂, hA.a₁_eq, hA.a₂_eq, hB.a₂_eq]
    · simp [C, variableChange_a₃, hA.a₁_eq, hA.a₃_eq, hB.a₃_eq]
    · simp [C, variableChange_a₄, hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, h4]
    · simp [C, variableChange_a₆, hA.a₁_eq, hA.a₂_eq, hA.a₃_eq, h6]
  have hψ : ψ.1 = vcPoint (C.baseChange A.toAffine.FunctionField)
      (Elliptic.baseChange_smul_eq C _ hC) (genericPoint A) := by
    rw [ψ.val_eq_some_x_y]
    simp only [GroundTheory.Arith.Abelian.genericPoint, vcPoint_some, Point.some.injEq]
    constructor
    · rw [hx]
      simp [C, vcX, VariableChange.baseChange, VariableChange.map]
    · rw [hy]
      simp [C, vcY, VariableChange.baseChange, VariableChange.map]
  have ex : vcX C x = (u : F) ^ 2 * x := by simp [C, vcX]
  have ey : vcY C x y = (u : F) ^ 3 * y := by simp [C, vcY]
  have hN : B.toAffine.Nonsingular (vcX C x) (vcY C x y) := hC ▸ (nonsingular_vc C A x y).2 h
  rw [ex, ey] at hN
  refine ⟨hN, ?_⟩
  rw [pointMap_eq_vcPoint C hC ψ hψ, vcPoint_some, Point.some.injEq]
  exact ⟨ex, ey⟩

end AlgClosed

section BaseChange

variable {F : Type u} [Field F] {A B : WeierstrassCurve F} [A.IsElliptic] [B.IsElliptic]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] [DecidableEq Ω]

theorem pointMap_isogBaseChange_some_of_degree_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hA : IsShortForm A) (hB : IsShortForm B) (ψ : Isogeny A B) (h : ψ.degree = 1) :
    ∃ u : Fˣ, B.a₄ = (u : F) ^ 4 * A.a₄ ∧ B.a₆ = (u : F) ^ 6 * A.a₆ ∧
      ∀ (x y : Ω) (hxy : (A.baseChange Ω).toAffine.Nonsingular x y),
        ∃ h' : (B.baseChange Ω).toAffine.Nonsingular
            (algebraMap F Ω (u : F) ^ 2 * x) (algebraMap F Ω (u : F) ^ 3 * y),
          (isogBaseChange (F' := Ω) ψ).pointMap (.some x y hxy) = .some _ _ h' := by
  obtain ⟨u, hx, hy, h4, h6⟩ := exists_scale_of_degree_eq_one h2 h3 hA hB ψ h
  refine ⟨u, h4, h6, fun x y hxy => ?_⟩
  let v : Ωˣ := Units.map (algebraMap F Ω) u
  have hv : (v : Ω) = algebraMap F Ω (u : F) := rfl
  have h4' : (B.baseChange Ω).a₄ = (v : Ω) ^ 4 * (A.baseChange Ω).a₄ := by
    show algebraMap F Ω B.a₄ = _ * algebraMap F Ω A.a₄
    rw [h4, hv, map_mul, map_pow]
  have h6' : (B.baseChange Ω).a₆ = (v : Ω) ^ 6 * (A.baseChange Ω).a₆ := by
    show algebraMap F Ω B.a₆ = _ * algebraMap F Ω A.a₆
    rw [h6, hv, map_mul, map_pow]
  have hx' : (isogBaseChange (F' := Ω) ψ).x =
      algebraMap Ω (A.baseChange Ω).toAffine.FunctionField ((v : Ω) ^ 2) *
        genX (A.baseChange Ω) := by
    rw [isogBaseChange_alt, hx, map_mul, AlgHom.commutes, bcEmb_genX, hv, ← map_pow,
      ← IsScalarTower.algebraMap_apply]
  have hy' : (isogBaseChange (F' := Ω) ψ).y =
      algebraMap Ω (A.baseChange Ω).toAffine.FunctionField ((v : Ω) ^ 3) *
        genY (A.baseChange Ω) := by
    rw [isogBaseChange_y, hy, map_mul, AlgHom.commutes, bcEmb_genY, hv, ← map_pow,
      ← IsScalarTower.algebraMap_apply]
  exact pointMap_some_of_scale (hA.baseChange Ω) (hB.baseChange Ω) v h4' h6' _ hx' hy' hxy

end BaseChange

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremPointHom
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

section OverF

variable {F : Type u} [Field F] [DecidableEq F] (Ω : Type u) [Field Ω] [Algebra F Ω]
  [DecidableEq Ω] [PerfectField F] [IsAlgClosed Ω]

omit [DecidableEq F] [PerfectField F] in
theorem app_eq_of_eq {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] (φ : Isogeny E E')
    {L : Type*} [Field L] [Algebra F L] [DecidableEq L] {P P' : (E.baseChange L).toAffine.Point}
    (h : P = P') (hP : IsGenPt E P) (hP' : IsGenPt E P') : φ.app P hP = φ.app P' hP' := by
  subst h
  rfl

theorem pointHomOver_comp {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
    [E''.IsElliptic] (ψ : Isogeny E' E'') (φ : Isogeny E E') (R : E.toAffine.Point) :
    pointHomOver Ω (ψ.comp φ) R = pointHomOver Ω ψ (pointHomOver Ω φ R) := by
  apply constMap_injective E'' E.toAffine.FunctionField
  set R' := pointHomOver Ω φ R
  have hX' := isGenPt_genericPoint_add_constMap E' R'
  have e0 := app_genericPoint_add_constMap Ω φ R
  have h1 := app_genericPoint_add_constMap Ω (ψ.comp φ) R

  have e : φ.1 + constMap E' E.toAffine.FunctionField R' =
      Point.map φ.comap (genericPoint E' + constMap E' E'.toAffine.FunctionField R') := by
    rw [map_add (f := _), Isogeny.map_comap_genericPoint, map_constMap]
  have hY : IsGenPt E' (φ.1 + constMap E' E.toAffine.FunctionField R') := by
    rw [e]
    exact isGenPt_map E' φ.comap hX'
  have h2 : ψ.app (φ.1 + constMap E' E.toAffine.FunctionField R') hY =
      Point.map φ.comap (ψ.1 + constMap E'' E'.toAffine.FunctionField (pointHomOver Ω ψ R')) := by
    rw [← app_genericPoint_add_constMap Ω ψ R', Isogeny.map_app]
    exact app_eq_of_eq ψ e _ _
  rw [Isogeny.app_comp, app_eq_of_eq ψ e0 _ hY, h2, map_add (f := _), map_constMap, ← Isogeny.comp_val,
    add_right_inj] at h1
  exact h1.symm

theorem pointHomOver_congr {E E' E₁ E₁' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
    [E₁.IsElliptic] [E₁'.IsElliptic] (φ : Isogeny E E') (hE : E = E₁) (hE' : E' = E₁')
    (R : E.toAffine.Point) :
    pointHomOver Ω (φ.congr hE hE') (pointCongr hE R) = pointCongr hE' (pointHomOver Ω φ R) := by
  subst hE hE'
  rw [Isogeny.congr_rfl]
  rfl

end OverF

section Frobenius

variable {F : Type u} [Field F] [DecidableEq F] (Ω : Type u) [Field Ω] [Algebra F Ω]
  [DecidableEq Ω] [PerfectField F] [IsAlgClosed Ω] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [Fact p.Prime] [CharP F p]

omit [PerfectField F] [E.IsElliptic] in
theorem frobeniusPoint_constMap {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (R : E.toAffine.Point) :
    frobeniusPoint E p L (constMap E L R) =
      constMap (frobeniusTwist E p) L (pointMapRing (frobenius F p) E R) := by
  rcases R with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := pointMapRing_some (frobenius F p) E h
    rw [e]
    show Point.some _ _ _ = Point.some _ _ _
    simp only [Algebra.ofId_apply, frobenius_def, map_pow]

theorem pointHomOver_frobeniusIsogeny (R : E.toAffine.Point) :
    pointHomOver Ω (frobeniusIsogeny E p) R = pointMapRing (frobenius F p) E R := by
  have : CharP E.toAffine.FunctionField p :=
    charP_of_injective_algebraMap (algebraMap F E.toAffine.FunctionField).injective p
  apply constMap_injective (frobeniusTwist E p) E.toAffine.FunctionField
  have hX := isGenPt_genericPoint_add_constMap E R
  have h1 := app_genericPoint_add_constMap Ω (frobeniusIsogeny E p) R
  rw [frobeniusIsogeny_app, frobeniusPoint_add, frobeniusPoint_constMap] at h1
  have h2 : frobeniusPoint E p E.toAffine.FunctionField (genericPoint E) = (frobeniusIsogeny E p).1 :=
    rfl
  rw [h2, add_right_inj] at h1
  exact h1.symm

end Frobenius

end

end GroundTheory.Global
end

