module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
section
namespace GlobalTheory.BaseRing

section
open Polynomial

theorem aeval_derivative_mul_mem_adjoin (A K : Type*) {L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsDomain A] [IsFractionRing A K]
    [IsIntegrallyClosed A] [FiniteDimensional K L] [Algebra.IsSeparable K L] {x : L}
    (hx : Algebra.adjoin K {x} = ⊤) (hAx : IsIntegral A x) (f : A[X]) (hf : aeval x f = 0)
    {z : L} (hz : IsIntegral A z) : aeval x (derivative f) * z ∈ Algebra.adjoin A {x} := by
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : Module.IsTorsionFree A L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hinj
  have h1 : z ∈ (Algebra.traceForm K L).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin A {x})) := by
    intro y hy
    have hy' : IsIntegral A y :=
      (show Algebra.adjoin A {x} ≤ integralClosure A L from
        Algebra.adjoin_le (Set.singleton_subset_iff.mpr hAx)) hy
    have := Algebra.isIntegral_trace (L := K) (hz.mul hy')
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
    rw [Algebra.traceForm_apply, ← ha]
    exact Submodule.mem_one.mpr ⟨a, rfl⟩
  rw [traceForm_dualSubmodule_adjoin A K hx hAx] at h1
  have hne : aeval x (derivative (minpoly K x)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  rw [Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hne), inv_inv,
    minpoly.isIntegrallyClosed_eq_field_fractions' K hAx, derivative_map,
    aeval_map_algebraMap] at h1
  obtain ⟨g, hg⟩ := minpoly.isIntegrallyClosed_dvd hAx hf
  have : aeval x (derivative f) * z = aeval x g * (aeval x (derivative (minpoly A x)) * z) := by
    rw [hg, derivative_mul]
    simp only [map_add (f := _), map_mul, minpoly.aeval]
    ring
  rw [this]
  exact Subalgebra.mul_mem _ (aeval_mem_adjoin_singleton _ _) h1


open IntermediateField in
theorem natCast_mul_mem_of_isIntegral (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (T : Subring ℂ) (hT : ∀ w ∈ K, IsIntegral ℤ w → w ∈ T) {ζ : ℂ} {n : ℕ} (hn : 0 < n)
    (hζ : ζ ^ n = 1) (hζT : ζ ∈ T) {z : ℂ} (hzK : z ∈ K⟮ζ⟯) (hz : IsIntegral ℤ z) :
    (n : ℂ) * z ∈ T := by
  have : NumberField K := {}
  let A := integralClosure ℤ K
  have : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension ℚ K
  have : IsIntegrallyClosed A := integralClosure.isIntegrallyClosedOfFiniteExtension ℚ
  have hζi : IsIntegral ℤ ζ := IsIntegral.of_pow hn (hζ ▸ isIntegral_one)
  have hζK : IsIntegral K ζ := hζi.tower_top
  have : FiniteDimensional K K⟮ζ⟯ := adjoin.finiteDimensional hζK
  let x : K⟮ζ⟯ := AdjoinSimple.gen K ζ
  have hx : Algebra.adjoin K {x} = ⊤ := (adjoin.powerBasis hζK).adjoin_gen_eq_top
  have hint : ∀ y : K⟮ζ⟯, IsIntegral ℤ (y : ℂ) → IsIntegral A y := fun y hy =>
    ((isIntegral_algHom_iff (K⟮ζ⟯.val.restrictScalars ℤ) Subtype.val_injective).mp hy).tower_top
  have hxn : x ^ n = 1 := Subtype.ext hζ
  have h := aeval_derivative_mul_mem_adjoin A K hx (hint x hζi) (X ^ n - 1) (by simp [hxn])
    (hint ⟨z, hzK⟩ hz)
  have hsub : ∀ y ∈ Algebra.adjoin A {x}, (y : ℂ) ∈ T := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hζT
    | algebraMap a =>
      exact hT _ a.1.2 ((isIntegral_algHom_iff (K.val.restrictScalars ℤ) Subtype.val_injective).mpr a.2)
    | add a b _ _ ha hb => exact T.add_mem ha hb
    | mul a b _ _ ha hb => exact T.mul_mem ha hb
  have h2 := T.mul_mem hζT (hsub _ h)
  convert h2 using 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hxc : (x : ℂ) = ζ := rfl
  set_option synthInstance.maxHeartbeats 200000 in
    simp [derivative_X_pow, hxc]
  linear_combination (-(m + 1 : ℂ) * z) * hζ


open IntermediateField in
theorem mem_of_isIntegral_quadratic {d : ℕ} (hd : d.Prime) (hd4 : d % 4 = 3) {r : ℂ}
    (hr : r ^ 2 = -(d : ℂ)) (T : Subring ℂ) (hT : (1 + r) / 2 ∈ T) {z : ℂ} (hzK : z ∈ ℚ⟮r⟯)
    (hz : IsIntegral ℤ z) : z ∈ T := by
  first
  | exact @_root_.GlobalTheory.RationalIntegralCoordinates.main
  | exact _root_.GlobalTheory.RationalIntegralCoordinates.main
  | (apply _root_.GlobalTheory.RationalIntegralCoordinates.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RationalIntegralCoordinates.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RationalIntegralCoordinates.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RationalIntegralCoordinates.main ..)

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem zeta_pow_self {n : ℕ} (hn : 0 < n) : zeta n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one

theorem isIntegral_sqrt_discriminant (H : Host E) : IsIntegral ℤ H.rt0 :=
  IsIntegral.of_pow two_pos (H.sqrt_neg_disc_sq ▸ (isIntegral_natCast H.d).neg)

theorem isIntegral_half_one_add_sqrt (H : Host E) : IsIntegral ℤ ((1 + H.rt0) / 2) := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, H.d + 1 = 4 * c := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hc' : (H.d : ℂ) + 1 = 4 * c := by exact_mod_cast hc
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩
  simp
  linear_combination (1 / 4 : ℂ) * H.sqrt_neg_disc_sq - (1 / 4 : ℂ) * hc'

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · exact (isIntegral_sqrt_discriminant H).tower_top
  · exact IsIntegral.of_pow l.A_pos (zeta_pow_self l.A_pos ▸ isIntegral_one)

theorem RZ_le_KA (l : Level H) (S : ℕ) : RZ H S l.A ≤ (KA l).toSubalgebra.toSubring := by
  refine Subring.closure_le.mpr ?_
  have h1 : H.rt0 ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
  rintro x (rfl | rfl | rfl)
  · exact show _ ∈ KA l from div_mem (add_mem (one_mem (KA l)) h1) (ofNat_mem (KA l) 2)
  · exact show _ ∈ KA l from inv_mem (natCast_mem (KA l) S)
  · exact IntermediateField.subset_adjoin ℚ {H.rt0, zeta l.A} (by simp)


open IntermediateField in
theorem mem_RZ_of_isIntegral (l : Level H) {S e : ℕ} (hS : 0 < S) (hA : l.A ∣ S ^ e) {z : ℂ}
    (hzK : z ∈ KA l) (hz : IsIntegral ℤ z) : z ∈ RZ H S l.A := by
  have : FiniteDimensional ℚ ℚ⟮H.rt0⟯ := adjoin.finiteDimensional (isIntegral_sqrt_discriminant H).tower_top
  have h := natCast_mul_mem_of_isIntegral ℚ⟮H.rt0⟯ (RZ H S l.A)
    (fun w hw hw' => mem_of_isIntegral_quadratic H.d_prime (by have := H.d_mod; omega) H.sqrt_neg_disc_sq _
      (Subring.subset_closure (by simp)) hw hw') l.A_pos (zeta_pow_self l.A_pos)
    (Subring.subset_closure (by simp)) (z := z)
    ((mem_restrictScalars ℚ).mp ((adjoin_simple_adjoin_simple ℚ H.rt0 (zeta l.A)).ge hzK)) hz
  obtain ⟨c, hc⟩ := hA
  have hc' : (S : ℂ) ^ e = l.A * c := by exact_mod_cast hc
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hi : (S : ℂ)⁻¹ ∈ RZ H S l.A := Subring.subset_closure (by simp)
  have : z = (S : ℂ)⁻¹ ^ e * (c * (l.A * z)) := by
    have h1 : (S : ℂ)⁻¹ ^ e * S ^ e = 1 := by rw [← mul_pow, inv_mul_cancel₀ hS', one_pow]
    rw [hc'] at h1
    linear_combination (-z) * h1
  rw [this]
  exact mul_mem (pow_mem hi e) (mul_mem (natCast_mem _ c) h)

theorem exists_pow_mul_isIntegral (H : Host E) {S A : ℕ} (hS : 0 < S) (hA : 0 < A) {z : ℂ}
    (hz : z ∈ RZ H S A) : ∃ k : ℕ, IsIntegral ℤ ((S : ℂ) ^ k * z) := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hp : ∀ k : ℕ, IsIntegral ℤ ((S : ℂ) ^ k) := fun k => (isIntegral_natCast S).pow k
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simpa using isIntegral_half_one_add_sqrt H⟩
    · exact ⟨1, by simpa [hS'] using isIntegral_one⟩
    · exact ⟨0, by simpa using IsIntegral.of_pow hA (zeta_pow_self hA ▸ isIntegral_one)⟩
  | zero => exact ⟨0, by simpa using isIntegral_zero⟩
  | one => exact ⟨0, by simpa using isIntegral_one⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have e : (S : ℂ) ^ (a + b) * (x + y) = S ^ b * (S ^ a * x) + S ^ a * (S ^ b * y) := by ring
    exact ⟨a + b, e ▸ ((hp b).mul ha).add ((hp a).mul hb)⟩
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by simpa using ha.neg⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have e : (S : ℂ) ^ (a + b) * (x * y) = (S ^ a * x) * (S ^ b * y) := by ring
    exact ⟨a + b, e ▸ ha.mul hb⟩

theorem finiteType_RZ (H : Host E) (S A : ℕ) : Algebra.FiniteType ℤ (RZ H S A) := by
  classical
  have h : (Algebra.adjoin ℤ {(1 + H.rt0) / 2, (S : ℂ)⁻¹, zeta A}).FG :=
    Subalgebra.fg_def.mpr ⟨_, Set.toFinite _, rfl⟩
  have h2 := (Subalgebra.fg_iff_finiteType _).mp h
  have h3 : (Algebra.adjoin ℤ {(1 + H.rt0) / 2, (S : ℂ)⁻¹, zeta A}).toSubring = RZ H S A := by
    rw [Algebra.adjoin_int]; rfl
  exact h2.equiv (RingEquiv.subringCongr h3).toIntAlgEquiv

theorem isDedekindDomain_RZ (l : Level H) {S e : ℕ} (hS : 0 < S) (hA : l.A ∣ S ^ e) :
    IsDedekindDomain (RZ H S l.A) := by
  have := finiteDimensional_KA l
  have : NumberField (KA l) := {}
  have hint : ∀ y : KA l, IsIntegral ℤ (y : ℂ) ↔ IsIntegral ℤ y := fun y =>
    isIntegral_algHom_iff ((KA l).val.restrictScalars ℤ) Subtype.val_injective
  let φ : 𝓞 (KA l) →+* RZ H S l.A :=
    ((KA l).val.toRingHom.comp (algebraMap (𝓞 (KA l)) (KA l))).codRestrict _ fun a =>
      mem_RZ_of_isIntegral l hS hA (a : KA l).2 ((hint _).mpr a.isIntegral_coe)
  have hφ : ∀ a, (φ a : ℂ) = ((a : KA l) : ℂ) := fun _ => rfl
  letI : Algebra (𝓞 (KA l)) (RZ H S l.A) := φ.toAlgebra
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hi : (S : ℂ)⁻¹ ∈ RZ H S l.A := Subring.subset_closure (by simp)
  have : IsLocalization (Submonoid.powers (S : 𝓞 (KA l))) (RZ H S l.A) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, k, rfl⟩
      simp only [map_pow, map_natCast]
      refine IsUnit.pow k (IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext ?_))
      simp [hS']
    · intro z
      obtain ⟨k, hk⟩ := exists_pow_mul_isIntegral H hS l.A_pos z.2
      have hm : (S : ℂ) ^ k * z ∈ KA l :=
        mul_mem (pow_mem (natCast_mem _ S) k) (RZ_le_KA l S z.2)
      refine ⟨(⟨⟨_, hm⟩, (hint _).mp hk⟩, ⟨_, k, rfl⟩), Subtype.ext ?_⟩
      simp only [map_pow, map_natCast]
      push_cast
      exact mul_comm _ _
    · intro x y h
      refine ⟨1, ?_⟩
      have : x = y := RingOfIntegers.ext (Subtype.ext (by
        rw [← hφ, ← hφ]; exact congrArg Subtype.val h))
      rw [this]
  exact IsLocalization.isDedekindDomain (𝓞 (KA l))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.mpr hS.ne' : (S : 𝓞 (KA l)) ≠ 0)) _

theorem isDedFrac_RZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (S e : ℕ), 0 < S → l.A ∣ S ^ e → (∃ β : RZ H S l.A →+* KA l, IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β) ∧ Algebra.FiniteType ℤ (RZ H S l.A) ∧ ∀ β : RZ H S l.A →+* KA l, IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → IsDedFrac β := by
  intro E _ _ _ H l S e hS hA
  refine ⟨⟨Subring.inclusion (RZ_le_KA l S), fun _ => rfl⟩, finiteType_RZ H S l.A, fun β hβ => ?_⟩
  refine ⟨⟨inferInstance, isDedekindDomain_RZ l hS hA⟩, inferInstance, ?_⟩
  letI := β.toAlgebra
  have hβ' : ∀ x, ((algebraMap (RZ H S l.A) (KA l) x : KA l) : ℂ) = x := hβ
  have hinj : Function.Injective (algebraMap (RZ H S l.A) (KA l)) := fun x y h =>
    Subtype.ext (by rw [← hβ' x, ← hβ' y, h])
  have := finiteDimensional_KA l
  have : NumberField (KA l) := {}
  have hint : ∀ y : KA l, IsIntegral ℤ (y : ℂ) ↔ IsIntegral ℤ y := fun y =>
    isIntegral_algHom_iff ((KA l).val.restrictScalars ℤ) Subtype.val_injective
  have hmem : ∀ a : 𝓞 (KA l), ((a : KA l) : ℂ) ∈ RZ H S l.A := fun a =>
    mem_RZ_of_isIntegral l hS hA (a : KA l).2 ((hint _).mpr a.isIntegral_coe)
  have : FaithfulSMul (RZ H S l.A) (KA l) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 (KA l)) z
  refine ⟨⟨_, hmem a⟩, ⟨_, hmem b⟩, ?_⟩
  congr 1 <;> exact Subtype.ext (by rw [hβ'])

end GlobalTheory.BaseRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.EpsThick

theorem existsUnique_of_isPushout {R : Type} [CommRing R] {A A' : CommRingCat.{0}} (s : R →+* A) (p : A ⟶ A')
    (s' : DualNumber R →+* A')
    (H : IsPushout (CommRingCat.ofHom s) (CommRingCat.ofHom (algebraMap R (DualNumber R))) p
      (CommRingCat.ofHom s')) :
    Function.Bijective fun ab : A × A => p.hom ab.1 + s' DualNumber.eps * p.hom ab.2 := by
  let _ : Algebra R A := s.toAlgebra
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra (DualNumber R) A' := s'.toAlgebra
  let _ : Algebra R A' := (s'.comp (algebraMap R (DualNumber R))).toAlgebra
  have : IsScalarTower R (DualNumber R) A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout R (DualNumber R) A A' := (CommRingCat.isPushout_iff_isPushout.mp H).symm
  let e : DualNumber R ⊗[R] A ≃+ A' := h.out.equiv.toAddEquiv
  have he : ∀ c v, e (c ⊗ₜ v) = s' c * p.hom v :=
    fun c v => (h.out.equiv_tmul c v).trans (Algebra.smul_def _ _)
  have key : ∀ ab : A × A, p.hom ab.1 + s' DualNumber.eps * p.hom ab.2 =
      e ((1 : DualNumber R) ⊗ₜ ab.1 + (DualNumber.eps : DualNumber R) ⊗ₜ ab.2) := fun ab => by
    rw [map_add (f := _), he, he, map_one, _root_.one_mul]
  simp only [key]
  refine e.bijective.comp (f := fun ab : A × A =>
    ((1 : DualNumber R) ⊗ₜ[R] ab.1 + (DualNumber.eps : DualNumber R) ⊗ₜ[R] ab.2)) ⟨fun x y hxy => ?_, fun t => ?_⟩
  · have h1 := congrArg ((TensorProduct.lid R A).toLinearMap ∘ₗ
      ((TrivSqZeroExt.fstHom R R R).toLinearMap).rTensor A) hxy
    have h2 := congrArg ((TensorProduct.lid R A).toLinearMap ∘ₗ
      (TrivSqZeroExt.sndHom R R).rTensor A) hxy
    ext
    · simpa using h1
    · simpa using h2
  · induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c v =>
      refine ⟨(c.fst • v, c.snd • v), ?_⟩
      dsimp only
      rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
      congr 1
      ext <;> simp
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      refine ⟨a + b, ?_⟩
      simp only [Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add]
      abel

variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {π : Y' ⟶ Sp (DualNumber R)} {ρ : Y' ⟶ Y}

def comb (π : Y' ⟶ Sp (DualNumber R)) (ρ : Y' ⟶ Y) (O : Y.Opens) (ab : Γ(Y, O) × Γ(Y, O)) : Γ(Y', ρ ⁻¹ᵁ O) :=
  (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2

theorem comb_bijective_of_isAffineOpen (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R))))
    {U : Y.Opens} (hU : IsAffineOpen U) : Function.Bijective (comb π ρ U) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine existsUnique_of_isPushout
    ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appLE ⊤ U (fun _ _ => trivial)).hom (ρ.app U)
    ((Scheme.ΓSpecIso (.of (DualNumber R))).inv ≫ π.appLE ⊤ (ρ ⁻¹ᵁ U) (fun _ _ => trivial)).hom ?_
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber R))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · simp

theorem res_comb {U O : Y.Opens} (h : U ≤ O) (ab : Γ(Y, O) × Γ(Y, O)) :
    (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom (comb π ρ O ab) =
      comb π ρ U ((Y.presheaf.map (homOfLE h).op).hom ab.1, (Y.presheaf.map (homOfLE h).op).hom ab.2) := by
  have h1 : ∀ a, (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom ((ρ.app O).hom a) =
      (ρ.app U).hom ((Y.presheaf.map (homOfLE h).op).hom a) := fun a =>
    (congrArg (fun φ => φ.hom a) (ρ.naturality (homOfLE h).op)).symm
  have h2 : (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom (constFn π _ DualNumber.eps) =
      constFn π (ρ ⁻¹ᵁ U) DualNumber.eps := by
    exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of (DualNumber R))).inv.hom DualNumber.eps))
      (π.appLE_map (U := ⊤) (V := ρ ⁻¹ᵁ O) le_top (homOfLE (ρ.preimage_mono h)).op)
  simp only [comb, map_add (f := _), map_mul, h1, h2]

theorem le_iSup_affine (O : Y.Opens) :
    O ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, U.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩

theorem comb_injective (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) (O : Y.Opens) :
    Function.Injective (comb π ρ O) := by
  intro x y hxy
  have key : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE U.2.2).op).hom x.1, (Y.presheaf.map (homOfLE U.2.2).op).hom x.2) =
      ((Y.presheaf.map (homOfLE U.2.2).op).hom y.1, (Y.presheaf.map (homOfLE U.2.2).op).hom y.2) := fun U => by
    apply (comb_bijective_of_isAffineOpen H U.2.1).1
    rw [← res_comb, ← res_comb, hxy]
  ext
  · exact Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) _ _
      fun U => congrArg Prod.fst (key U)
  · exact Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) _ _
      fun U => congrArg Prod.snd (key U)

theorem comb_surjective (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) (O : Y.Opens) :
    Function.Surjective (comb π ρ O) := by
  intro F
  choose s hs using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} =>
    (comb_bijective_of_isAffineOpen H U.2.1).2 ((Y'.presheaf.map (homOfLE (ρ.preimage_mono U.2.2)).op).hom F)
  have key : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (s U).1,
        (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (s U).2) =
      ((Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (s V).1,
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (s V).2) := fun U V => by
    apply comb_injective H
    rw [← res_comb, ← res_comb, hs, hs, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (s U).1) fun U V => congrArg Prod.fst (key U V)
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (s U).2) fun U V => congrArg Prod.snd (key U V)
  refine ⟨(a, b), ?_⟩
  refine Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _
    (fun U => homOfLE (ρ.preimage_mono U.2.2)) ?_ _ _ fun U => ?_
  · rw [← Scheme.Hom.preimage_iSup]
    exact ρ.preimage_mono (le_iSup_affine O)
  · refine (res_comb U.2.2 (a, b)).trans (Eq.trans ?_ (hs U))
    exact congrArg _ (Prod.ext (ha U) (hb U))

theorem isPullback_special (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) {j : Y ⟶ Y'}
    (h₁ : j ≫ ρ = 𝟙 Y) (h₂ : j ≫ π = q ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom) :
    IsPullback j q π (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  refine (IsPullback.of_bot ?_ h₂.symm H.flip).flip
  have : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  rw [h₁, this]
  exact IsPullback.of_vert_isIso ⟨by simp⟩

theorem surjective_spMap_fst : Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  refine ⟨fun x => ?_⟩
  have h : x ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)]
    intro z hz
    have hz' : z.fst = 0 := hz
    refine x.isPrime.mem_of_pow_mem 2 ?_
    have : z ^ 2 = 0 := by
      ext <;> simp [pow_two, hz']
    rw [this]
    exact zero_mem _
  exact h

theorem thickening_functions : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  intro Y Y' q π ρ j H h₁ h₂
  have P := isPullback_special H h₁ h₂
  refine ⟨fun O => ?_, P, fun O F => ?_⟩
  · have hj : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) P.flip surjective_spMap_fst
    ext x
    obtain ⟨y, rfl⟩ := hj.surj x
    have : ρ (j y) = y := by rw [← Scheme.Hom.comp_apply, h₁]; rfl
    change j (ρ (j y)) ∈ O ↔ j y ∈ O
    rw [this]
  · obtain ⟨ab, hab⟩ := comb_surjective H O F
    exact ⟨ab, hab.symm, fun y hy => comb_injective H O (hy.symm.trans hab.symm)⟩

end GlobalTheory.EpsThick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfLineSubsetDiscrete
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem eq_zero_of_line_subset_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (v : Fin g → ℂ) (hv : ∀ t : ℂ, t • v ∈ Λ) : v = 0 := by
  by_contra h
  have hc : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hinj : Function.Injective (fun t : ℂ => (⟨t • v, hv t⟩ : Λ)) := by
    intro s t hst
    exact smul_left_injective ℂ h (congrArg Subtype.val hst)
  have : Countable ℂ := hinj.countable
  have : Countable ℝ := Complex.ofReal_injective.countable
  exact not_countable this

theorem linear_eq_of_ex_eq {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
    (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, u.ex (F z) = u.ex (F' z)) : F = F' := by
  have hd := u.discrete
  have hm : ∀ z, F z - F' z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h1 := u.ex_add (F z - F' z) (F' z)
    rw [sub_add_cancel, h z] at h1
    exact (mul_eq_right.mp h1.symm)
  refine LinearMap.ext fun z => sub_eq_zero.mp (eq_zero_of_line_subset_discrete u.Λ _ fun t => ?_)
  have := hm (t • z)
  rwa [map_smul, map_smul, ← smul_sub] at this

theorem exists_linear_lift_action : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → (∀ (f : P₀.A ⟶ P₀.A) (F F' : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f) → F = F') ∧ ∀ (O : Type) [CommRing O] (act : OAct O P₀.A), ∃ F : O →+* Module.End ℂ (Fin P₀.g → ℂ), ∀ a z, u.ex (F a z) = u.ex z ≫ act.act a := by
  intro P₀ u Hm χ hu
  refine ⟨fun f F F' h h' => linear_eq_of_ex_eq u F F' fun z => (h z).trans (h' z).symm, ?_⟩
  intro O _ act
  choose F hF using fun a => hu.endo (act.act a) (act.hom a)
  have hone : F 1 = (1 : Module.End ℂ (Fin P₀.g → ℂ)) :=
    linear_eq_of_ex_eq u _ _ fun z => by rw [hF, act.one, Category.comp_id]; rfl
  have hmul : ∀ a b, F (a * b) = (F a : Module.End ℂ (Fin P₀.g → ℂ)) * F b := fun a b =>
    linear_eq_of_ex_eq u _ _ fun z => by
      rw [hF, mul_comm a b, act.mul, Module.End.mul_apply, hF, hF, Category.assoc]
  have hadd : ∀ a b, F (a + b) = F a + F b := fun a b =>
    linear_eq_of_ex_eq u _ _ fun z => by
      rw [hF, act.add, LinearMap.add_apply, u.ex_add, hF, hF, MonObj.comp_mul]
  exact ⟨RingHom.mk' ⟨⟨F, hone⟩, hmul⟩ hadd, hF⟩

end GlobalTheory.KS
end

