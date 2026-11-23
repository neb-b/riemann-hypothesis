module

public import Mathlib
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0015
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionDifferential
public import GroundTheory.GlobalFields.ComplexMultiplication.IsogenyDegreeOne
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0002

@[expose] public section

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityGalois
section
open NumberField Module WeierstrassCurve IntermediateField
open scoped nonZeroDivisors

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

section Extend

variable {K : Type*} [Field K] [Algebra K ℂ]

theorem exists_algEquiv_extend_adjoin {α : ℂ} (hα : IsAlgebraic K α) (φ : K⟮α⟯ →ₐ[K] ℂ) :
    ∃ σ : ℂ ≃ₐ[K] ℂ, ∀ z : K⟮α⟯, σ z = φ z := by
  have hint := hα.isIntegral
  have hroot : Polynomial.aeval (φ (AdjoinSimple.gen K α)) (minpoly K α) = 0 := by
    rw [Polynomial.aeval_algHom_apply, aeval_gen_minpoly, map_zero]
  have heq : minpoly K α = minpoly K (φ (AdjoinSimple.gen K α)) :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hroot (minpoly.monic hint)
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_minpoly_eq hα heq
  refine ⟨σ, fun z ↦ ?_⟩
  have e : (σ.toAlgHom.comp (K⟮α⟯).val) = φ := by
    apply adjoin_algHom_ext
    rintro x rfl
    exact hσ
  exact DFunLike.congr_fun e z

end Extend

variable {K : Type*} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]
include hK

def galClassHom : (ℂ ≃ₐ[K] ℂ) →* ClassGroup (𝓞 K) where
  toFun σ := galClass (algebraMap K ℂ) hK σ.toRingEquiv
  map_one' := galClass_one (algebraMap K ℂ) hK
  map_mul' σ τ := galClass_mul (algebraMap K ℂ) hK σ.toRingEquiv τ.toRingEquiv
    (fun k ↦ σ.commutes k) (fun k ↦ τ.commutes k)

theorem galClassHom_apply_j (σ : ℂ ≃ₐ[K] ℂ) (x : ELL K) :
    σ (ELL.j x) = ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassHom hK σ) x) :=
  apply_j_eq_j_galClass_smul (algebraMap K ℂ) hK σ.toRingEquiv (fun k ↦ σ.commutes k) x

theorem galClassHom_eq_one_iff (σ : ℂ ≃ₐ[K] ℂ) (x : ELL K) :
    galClassHom hK σ = 1 ↔ σ (ELL.j x) = ELL.j x :=
  galClass_eq_one_iff (algebraMap K ℂ) hK σ.toRingEquiv (fun k ↦ σ.commutes k) x

theorem ELL.isAlgebraic_j_over (x : ELL K) : IsAlgebraic K (ELL.j x) := by
  have : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact IsAlgebraic.extendScalars (algebraMap ℚ K).injective (ELL.isAlgebraic_j hK x)

theorem ELL.j_mem_adjoin (x y : ELL K) : ELL.j y ∈ K⟮ELL.j x⟯ := by
  have key : ∀ ρ : ℂ ≃ₐ[K⟮ELL.j x⟯] ℂ, ρ (ELL.j y) = ELL.j y := by
    intro ρ
    have h1 : (ρ.restrictScalars K) (ELL.j x) = ELL.j x :=
      ρ.commutes (AdjoinSimple.gen K (ELL.j x))
    rw [← galClassHom_eq_one_iff hK] at h1
    have h2 := galClassHom_apply_j hK (ρ.restrictScalars K) y
    rw [h1, ellMulAction_one_smul] at h2
    exact h2
  obtain ⟨w, hw⟩ := IntermediateField.mem_bot.1
    ((mem_bot_iff_forall_algEquiv_apply_eq (F := K⟮ELL.j x⟯)).2 key)
  rw [← hw]
  exact w.2

section Field

variable (M : IntermediateField K ℂ) (hM : ∀ y : ELL K, ELL.j y ∈ M)
include hM

omit [NumberField K] hK [_root_.NumberField.IsTotallyComplex K] in
theorem adjoin_j_le (x : ELL K) : K⟮ELL.j x⟯ ≤ M :=
  adjoin_simple_le_iff.2 (hM x)

def extendOf (τ : M ≃ₐ[K] M) : ℂ ≃ₐ[K] ℂ :=
  (exists_algEquiv_extend_adjoin (ELL.isAlgebraic_j_over hK (ellEquiv (algebraMap K ℂ) hK 1))
    (M.val.comp (τ.toAlgHom.comp (inclusion (adjoin_j_le M hM _))))).choose

def galClassOfFun (τ : M ≃ₐ[K] M) : ClassGroup (𝓞 K) :=
  galClassHom hK (extendOf hK M hM τ)

theorem galClassOfFun_apply_j (τ : M ≃ₐ[K] M) (y : ELL K) :
    (τ ⟨ELL.j y, hM y⟩ : ℂ) =
      ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassOfFun hK M hM τ) y) := by
  set x₀ := ellEquiv (algebraMap K ℂ) hK 1
  have hy : ELL.j y ∈ K⟮ELL.j x₀⟯ := ELL.j_mem_adjoin hK x₀ y
  have spec := (exists_algEquiv_extend_adjoin (ELL.isAlgebraic_j_over hK x₀)
    (M.val.comp (τ.toAlgHom.comp (inclusion (adjoin_j_le M hM x₀))))).choose_spec ⟨_, hy⟩
  rw [galClassOfFun, ← galClassHom_apply_j]
  exact spec.symm

theorem galClassOfFun_unique (τ : M ≃ₐ[K] M) (a : ClassGroup (𝓞 K)) (y : ELL K)
    (h : (τ ⟨ELL.j y, hM y⟩ : ℂ) = ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul a y)) :
    galClassOfFun hK M hM τ = a := by
  rw [galClassOfFun_apply_j hK M hM] at h
  exact (existsUnique_smul_eq (algebraMap K ℂ) hK y _).unique (ELL.j_injective h) rfl

def galClassOf : (M ≃ₐ[K] M) →* ClassGroup (𝓞 K) where
  toFun := galClassOfFun hK M hM
  map_one' := by
    apply galClassOfFun_unique hK M hM 1 1 (ellEquiv (algebraMap K ℂ) hK 1)
    rw [ellMulAction_one_smul]
    rfl
  map_mul' τ₁ τ₂ := by
    set y := ellEquiv (algebraMap K ℂ) hK 1
    apply galClassOfFun_unique hK M hM _ _ y
    have h2 : τ₂ ⟨ELL.j y, hM y⟩ = ⟨ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul
        (galClassOfFun hK M hM τ₂) y), hM _⟩ :=
      Subtype.ext (galClassOfFun_apply_j hK M hM τ₂ y)
    rw [ellMulAction_mul_smul, ← galClassOfFun_apply_j hK M hM τ₁, ← h2]
    rfl

theorem galClassOf_apply_j (τ : M ≃ₐ[K] M) (y : ELL K) :
    (τ ⟨ELL.j y, hM y⟩ : ℂ) =
      ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul (galClassOf hK M hM τ) y) :=
  galClassOfFun_apply_j hK M hM τ y

end Field

section Adjoin

variable (x : ELL K)

end Adjoin

end Elliptic
end GroundTheory.Global
end
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open Polynomial NumberField IsDedekindDomain IsLocalRing

section Generic

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (f : R →+* S)

theorem isPrimitiveRoot_map_of_natCast_ne_zero {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hn : (n : S) ≠ 0) : IsPrimitiveRoot (f ζ) n := by
  have : NeZero (n : S) := ⟨hn⟩
  have : NeZero (n : R) := ⟨fun h => hn (by rw [← map_natCast f n, h, map_zero])⟩
  have hr : eval ζ (cyclotomic n R) = 0 := isRoot_cyclotomic_iff.mpr hζ
  apply isRoot_cyclotomic_iff.mp
  show eval (f ζ) (cyclotomic n S) = 0
  rw [← map_cyclotomic n f, eval_map, eval₂_hom, hr, map_zero]

theorem eq_of_map_eq_of_pow_eq_one {ζ : R} {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (hn : (n : S) ≠ 0) {η η' : R} (hη : η ^ n = 1) (hη' : η' ^ n = 1) (h : f η = f η') :
    η = η' := by
  have hf := isPrimitiveRoot_map_of_natCast_ne_zero f hζ hn
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  obtain ⟨k, hk, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη'
  rw [map_pow, map_pow] at h
  rw [hf.pow_inj hj hk h]

theorem existsUnique_pow_eq_one_of_isPrimitiveRoot {ζ : R} {n : ℕ} [NeZero n]
    (hζ : IsPrimitiveRoot ζ n) (hn : (n : S) ≠ 0) {w : S} (hw : w ^ n = 1) :
    ∃! η : R, η ^ n = 1 ∧ f η = w := by
  have hf := isPrimitiveRoot_map_of_natCast_ne_zero f hζ hn
  obtain ⟨i, -, e⟩ := hf.eq_pow_of_pow_eq_one hw
  have hi : (ζ ^ i) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨ζ ^ i, ⟨hi, by rw [map_pow, e]⟩, ?_⟩
  rintro η ⟨hη, hfη⟩
  exact eq_of_map_eq_of_pow_eq_one f hζ hn hη hi (by rw [hfη, map_pow, e])

end Generic

theorem two_ne_zero_and_three_ne_zero_of_five_le_ringChar {k : Type*} [Field k]
    (h : 5 ≤ ringChar k) : (2 : k) ≠ 0 ∧ (3 : k) ≠ 0 := by
  refine ⟨fun h2 => ?_, fun h3 => ?_⟩
  · have := Nat.le_of_dvd (by norm_num) ((ringChar.spec k 2).mp (by exact_mod_cast h2))
    omega
  · have := Nat.le_of_dvd (by norm_num) ((ringChar.spec k 3).mp (by exact_mod_cast h3))
    omega

section NumberField

variable {L : Type*} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

end NumberField

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesLocal
section
namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian

universe u

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (F : Type u) [Field F] [Algebra 𝒪 F] [IsFractionRing 𝒪 F] {W W' : WeierstrassCurve 𝒪}
  [W.IsElliptic] [W'.IsElliptic]

theorem invConst_reduceIsogeny_eq_zero (φ : Isogeny (W.baseChange F) (W'.baseChange F)) {c : 𝒪}
    (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    invConst (reduceIsogeny F W W' φ) = 0 := by
  obtain ⟨c', h1, h2⟩ := exists_invConst_reduceIsogeny F W W' φ
  have e : c' = c := IsFractionRing.injective 𝒪 F (h1.trans hφ.symm)
  rw [← h2, e]
  exact (residue_eq_zero_iff c).2 hc

theorem isogenyPullback_reduceIsogeny_eq_zero (φ : Isogeny (W.baseChange F) (W'.baseChange F))
    {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    isogenyPullback (reduceIsogeny F W W' φ) (invariantDifferential (W'.map (residue 𝒪))) = 0 := by
  rw [isogenyPullback_eq_invConst_smul, invConst_reduceIsogeny_eq_zero F φ hc hφ, zero_smul]

variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField 𝒪) p] [PerfectRing (ResidueField 𝒪) p]

theorem reduceIsogeny_eq_comp_frobeniusIsogeny (φ : Isogeny (W.baseChange F) (W'.baseChange F))
    (hdeg : φ.degree = p) {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    ∃ ψ : Isogeny (frobeniusTwist (W.map (residue 𝒪)) p) (W'.map (residue 𝒪)),
      reduceIsogeny F W W' φ = ψ.comp (frobeniusIsogeny (W.map (residue 𝒪)) p) ∧
      ψ.degree = 1 ∧ Function.Bijective ψ.comap ∧
      (dualOver ψ).comp ψ = mulIsogeny _ 1 one_ne_zero ∧
      ψ.comp (dualOver ψ) = mulIsogeny _ 1 one_ne_zero :=
  exists_isomorphism_of_degree_eq p _ (isogenyPullback_reduceIsogeny_eq_zero F φ hc hφ)
    (by rw [degree_reduceIsogeny, hdeg])

theorem residue_j_eq_pow (φ : Isogeny (W.baseChange F) (W'.baseChange F)) (hdeg : φ.degree = p)
    {c : 𝒪} (hc : c ∈ maximalIdeal 𝒪) (hφ : algebraMap 𝒪 F c = invConst φ) :
    residue 𝒪 W'.j = residue 𝒪 W.j ^ p := by
  rw [← j_map_residue, ← j_map_residue]
  exact j_eq_pow_of_isogenyPullback_eq_zero p _ (isogenyPullback_reduceIsogeny_eq_zero F φ hc hφ)
    (by rw [degree_reduceIsogeny, hdeg])

end

end GroundTheory.Global
end

