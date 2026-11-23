module

public import Mathlib

@[expose] public section

open scoped TensorProduct Pointwise

namespace GlobalTheory

section Ring

variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]

instance isInvariant_fixedSubring : Algebra.IsInvariant (FixedPoints.subring A G) A G :=
  ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩

theorem finite_of_isInvariant [Finite G] (R B : Type*) [CommRing R] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra B A] [IsScalarTower R B A] [Algebra.IsInvariant B A G]
    [Algebra.FiniteType R A] : Module.Finite B A := by
  haveI := Algebra.IsInvariant.isIntegral B A G
  haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType R B A
  exact Algebra.IsIntegral.finite

theorem finiteType_of_isInvariant [Finite G] (R B : Type*) [CommRing R] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra B A] [IsScalarTower R B A] [FaithfulSMul B A]
    [Algebra.IsInvariant B A G] [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Algebra.FiniteType R B :=
  haveI := finite_of_isInvariant A G R B
  ⟨fg_of_fg_of_fg R B A Algebra.FiniteType.out Module.Finite.fg_top
    (FaithfulSMul.algebraMap_injective B A)⟩

theorem exists_orbit_eq_primesOver_of_isInvariant [Finite G] (B : Type*) [CommRing B]
    [Algebra B A] [FaithfulSMul B A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    (P : Ideal B) [P.IsPrime] :
    ∃ Q : Ideal A, Q.IsPrime ∧ Q.LiesOver P ∧ MulAction.orbit G Q = P.primesOver A := by
  haveI := Algebra.IsInvariant.isIntegral B A G
  obtain ⟨⟨Q, hQ, hQP⟩⟩ := Ideal.nonempty_primesOver (S := A) P
  exact ⟨Q, hQ, hQP, Algebra.IsInvariant.orbit_eq_primesOver B A G P Q⟩

end Ring

section FlatModule

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M']

theorem isBaseChange_of_forall_eq [Module.Flat R S] {ι : Type*} [Finite ι]
    {P P' : ι → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    [∀ i, AddCommGroup (P' i)] [∀ i, Module R (P' i)] [∀ i, Module S (P' i)]
    [∀ i, IsScalarTower R S (P' i)]
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] [Module S N']
    [IsScalarTower R S N']
    (φ ψ : ∀ i, M →ₗ[R] P i) (φ' ψ' : ∀ i, M' →ₗ[S] P' i)
    (f : M →ₗ[R] M') (hf : IsBaseChange S f) (h : ∀ i, P i →ₗ[R] P' i)
    (hh : ∀ i, IsBaseChange S (h i))
    (hφ : ∀ i x, h i (φ i x) = φ' i (f x)) (hψ : ∀ i x, h i (ψ i x) = ψ' i (f x))
    (j : N →ₗ[R] M) (hj : Function.Injective j)
    (hj' : ∀ x, x ∈ Set.range j ↔ ∀ i, φ i x = ψ i x)
    (j' : N' →ₗ[S] M') (hj₁ : Function.Injective j')
    (hj₁' : ∀ x, x ∈ Set.range j' ↔ ∀ i, φ' i x = ψ' i x)
    (k : N →ₗ[R] N') (hk : ∀ x, j' (k x) = f (j x)) : IsBaseChange S k := by
  refine IsBaseChange.of_left_exact S k f (.pi fun i ↦ h i ∘ₗ .proj i) (f := j) (f' := j')
    (g := .pi fun i ↦ φ i - ψ i) (g' := .pi fun i ↦ φ' i - ψ' i) ?_ ?_ hf
    (IsBaseChange.pi h hh) ?_ hj ?_ hj₁
  · ext x; simp [hk]
  · ext x i; simp [hφ, hψ]
  · intro x; rw [hj']; simp [funext_iff, sub_eq_zero]
  · intro x; rw [hj₁']; simp [funext_iff, sub_eq_zero]

variable {G : Type*} [Group G]



end FlatModule

section FlatRing

variable (G : Type*) [Group G]

section
variable {R S A A' : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing A']
  [Algebra R S] [Algebra R A] [Algebra R A'] [Algebra S A'] [IsScalarTower R S A']
  [MulSemiringAction G A] [SMulCommClass G R A] [MulSemiringAction G A'] [SMulCommClass G S A']


variable (S) in
def fixedSubalgebraMap (f : A →ₐ[R] A') (hf : ∀ (g : G) a, f (g • a) = g • f a) :
    FixedPoints.subalgebra R A G →ₐ[R] FixedPoints.subalgebra S A' G where
  toFun x := ⟨f x, fun g ↦ by rw [← hf, x.2 g]⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f _ _)
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f _ _)
  commutes' r := Subtype.ext (f.commutes r)

theorem isBaseChange_fixedSubalgebraMap [Finite G] [Module.Flat R S] (f : A →ₐ[R] A')
    (hb : IsBaseChange S f.toLinearMap) (hf : ∀ (g : G) a, f (g • a) = g • f a) :
    IsBaseChange S (fixedSubalgebraMap G (S := S) f hf).toLinearMap :=
  isBaseChange_of_forall_eq S (ι := G) (fun g ↦ (MulSemiringAction.toAlgHom R A g).toLinearMap)
    (fun _ ↦ .id) (fun g ↦ (MulSemiringAction.toAlgHom S A' g).toLinearMap) (fun _ ↦ .id)
    f.toLinearMap hb (fun _ ↦ f.toLinearMap) (fun _ ↦ hb) hf (fun _ _ ↦ rfl)
    (FixedPoints.subalgebra R A G).val.toLinearMap Subtype.val_injective
    (fun x ↦ ⟨by rintro ⟨y, rfl⟩; exact y.2, fun h ↦ ⟨⟨x, h⟩, rfl⟩⟩)
    (FixedPoints.subalgebra S A' G).val.toLinearMap Subtype.val_injective
    (fun x ↦ ⟨by rintro ⟨y, rfl⟩; exact y.2, fun h ↦ ⟨⟨x, h⟩, rfl⟩⟩) _ (fun _ ↦ rfl)

theorem isInvariant_of_isBaseChange [Finite G] [Module.Flat R S] [Algebra.IsInvariant R A G]
    (f : A →ₐ[R] A') (hb : IsBaseChange S f.toLinearMap)
    (hf : ∀ (g : G) a, f (g • a) = g • f a) : Algebra.IsInvariant S A' G := by
  refine ⟨fun y hy ↦ ?_⟩
  have key : ∀ z : FixedPoints.subalgebra S A' G, ∃ s, algebraMap S A' s = z := by
    intro z
    induction z using (isBaseChange_fixedSubalgebraMap G f hb hf).inductionOn with
    | tmul m =>
      obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := G) (m : A) m.2
      refine ⟨algebraMap R S r, ?_⟩
      change _ = f m
      rw [← hr, f.commutes, ← IsScalarTower.algebraMap_apply]
    | smul s n hn =>
      obtain ⟨t, ht⟩ := hn
      exact ⟨s * t, by rw [map_mul, ht, ← Algebra.smul_def]; rfl⟩
    | add a b ha hb =>
      obtain ⟨t, ht⟩ := ha
      obtain ⟨u, hu⟩ := hb
      exact ⟨t + u, by rw [map_add (f := _), ht, hu]; rfl⟩
  exact key ⟨y, hy⟩


omit [MulSemiringAction G A] [SMulCommClass G R A] [MulSemiringAction G A']
  [SMulCommClass G S A'] in
theorem faithfulSMul_of_isBaseChange [Module.Flat R S] [FaithfulSMul R A]
    (f : A →ₐ[R] A') (hb : IsBaseChange S f.toLinearMap) : FaithfulSMul S A' := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := S) (Algebra.linearMap R A)
    (FaithfulSMul.algebraMap_injective R A)
  have : ⇑(algebraMap S A') =
      hb.equiv ∘ (Algebra.linearMap R A).lTensor S ∘ (TensorProduct.rid R S).symm := by
    ext s
    simp [IsBaseChange.equiv_tmul, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact hb.equiv.injective.comp (h.comp (TensorProduct.rid R S).symm.injective)

end

section
variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

end

section
variable {A : Type*} [CommRing A] [MulSemiringAction G A]

variable {B : Type*} [CommRing B] [Algebra B A] [SMulCommClass G B A]

end

end FlatRing

section Generator

variable {A : Type*} [CommRing A]

variable {M : Type*} [AddCommGroup M] [Module A M]

theorem dual_apply_smul_comm [Module.Invertible A M] (f : Module.Dual A M) (x y : M) :
    f x • y = f y • x := by
  have := congrArg (fun z ↦ TensorProduct.lid A M (f.rTensor M z))
    (Module.Invertible.tmul_comm (R := A) (m₁ := x) (m₂ := y))
  simpa using this

theorem exists_sum_dual_apply_eq_one (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Invertible A M] : ∃ s : Finset (Module.Dual A M × M), ∑ p ∈ s, p.1 p.2 = 1 := by
  obtain ⟨s, hs⟩ := ((Module.Invertible.linearEquiv A M).symm 1).exists_finset
  refine ⟨s, Eq.symm ?_⟩
  simpa [LinearEquiv.symm_apply_eq, Module.Invertible.linearEquiv] using hs

theorem free_of_invertible_of_finite_maximalSpectrum (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] [Finite (MaximalSpectrum A)] [Module.Invertible A M] : Module.Free A M :=
  Module.free_of_flat_of_finrank_eq _ _ 1
    fun _ ↦ let _ := @Ideal.Quotient.field A _; Module.Invertible.finrank_eq_one ..

theorem exists_bijective_toSpanSingleton_of_finite_maximalSpectrum (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] [Finite (MaximalSpectrum A)] [Module.Invertible A M] :
    ∃ e : M, Function.Bijective (LinearMap.toSpanSingleton A M e) := by
  obtain ⟨φ⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (free_of_invertible_of_finite_maximalSpectrum A M)
  refine ⟨φ.symm 1, ?_⟩
  have : LinearMap.toSpanSingleton A M (φ.symm 1) = φ.symm.toLinearMap := by ext; simp
  rw [this]
  exact φ.symm.bijective

theorem bijective_toSpanSingleton_of_isBaseChange [Module.Invertible A M] (f : Module.Dual A M)
    (e : M) {A' M' : Type*} [CommRing A'] [Algebra A A'] [AddCommGroup M'] [Module A M']
    [Module A' M'] [IsScalarTower A A' M'] (l : M →ₗ[A] M') (hl : IsBaseChange A' l)
    (hu : IsUnit (algebraMap A A' (f e))) :
    Function.Bijective (LinearMap.toSpanSingleton A' M' (l e)) := by
  haveI : Module.Invertible A' M' := .congr hl.equiv
  refine Module.Invertible.bijective_of_surjective fun y ↦ ?_
  induction y using hl.inductionOn with
  | tmul m =>
    obtain ⟨u, hu⟩ := hu
    refine ⟨↑u⁻¹ * algebraMap A A' (f m), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, mul_smul, algebraMap_smul, ← map_smul,
      dual_apply_smul_comm, map_smul, ← algebraMap_smul A' (f e), ← hu, smul_smul, Units.inv_mul,
      one_smul]
  | smul s n hn =>
    obtain ⟨a, rfl⟩ := hn
    exact ⟨s • a, map_smul _ _ _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

end Generator

section Semilinear

variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]

section
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]

theorem smulCommClass_of_smulDistribClass (B : Type*) [CommRing B] [Algebra B A]
    [SMulCommClass G B A] [Module B M] [IsScalarTower B A M] : SMulCommClass G B M :=
  ⟨fun g b x ↦ by
    rw [← algebraMap_smul A b, smul_distrib_smul, smul_algebraMap, algebraMap_smul]⟩

instance smulCommClass_fixedSubring : SMulCommClass G (FixedPoints.subring A G) M :=
  smulCommClass_of_smulDistribClass A M _

variable {A M}

variable (B : Type*) [CommRing B] [Algebra B A] [FaithfulSMul B A] [SMulCommClass G B A]
  [Algebra.IsInvariant B A G] [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]

end

section
variable (G) {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
  [∀ i, DistribMulAction G (M i)] [∀ i, SMulDistribClass G A (M i)]

end

section
variable {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] {ι : Type*}




variable [SMulDistribClass G A M]

variable {A}

end

end Semilinear

universe u v

end GlobalTheory
