module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
section
open WeierstrassCurve WeierstrassCurve.Projective

namespace GlobalTheory.AddLaw

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

def Proportional (T U : Fin 3 → R) : Prop :=
  ∀ i j, T i * U j = T j * U i

lemma Proportional.symm {T U : Fin 3 → R} (h : Proportional T U) : Proportional U T :=
  fun i j => by linear_combination h j i

lemma proportional_negY (W : Projective R) {X N Z X' N' Z' : R} (hxz : X * Z' = Z * X')
    (hnz : N * Z' = Z * N') (hxn : X * N' = N * X') :
    Proportional ![X, W.negY ![X, N, Z], Z] ![X', W.negY ![X', N', Z'], Z'] := by
  have hxy : X * W.negY ![X', N', Z'] = W.negY ![X, N, Z] * X' := by
    simp only [negY_eq]; linear_combination -hxn - W.a₃ * hxz
  have hyz : W.negY ![X, N, Z] * Z' = Z * W.negY ![X', N', Z'] := by
    simp only [negY_eq]; linear_combination -hnz - W.a₁ * hxz
  intro i j
  fin_cases i <;> fin_cases j
  exacts [rfl, hxy, hxz, hxy.symm, rfl, hyz, hxz.symm, hyz.symm, rfl]

variable {W : Projective R}

lemma diagXYZ_X (P Q : Fin 3 → R) : diagXYZ W P Q 0 = diagX W P Q := rfl

lemma diagXYZ_Y (P Q : Fin 3 → R) : diagXYZ W P Q 1 = diagY W P Q := rfl

lemma diagXYZ_Z (P Q : Fin 3 → R) : diagXYZ W P Q 2 = diagZ W P Q := rfl

lemma diagXYZ_self {P : Fin 3 → R} (hP : W.Equation P) : diagXYZ W P P = W.dblXYZ P := by
  rw [diagXYZ, diagY, diagX_self hP, negDiagY_self hP, diagZ_self hP, dblXYZ, dblY]

lemma diagY_smul (P Q : Fin 3 → R) (u v : R) :
    diagY W (u • P) (v • Q) = (u * v) ^ 2 * diagY W P Q := by
  simp only [diagY, negY_eq, diagX_smul, negDiagY_smul, diagZ_smul]
  ring1

lemma diagXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    diagXYZ W (u • P) (v • Q) = (u * v) ^ 2 • diagXYZ W P Q := by
  rw [diagXYZ, diagX_smul, diagY_smul, diagZ_smul, smul_fin3, diagXYZ_X, diagXYZ_Y, diagXYZ_Z]

lemma map_diagY (f : R →+* S) (P Q : Fin 3 → R) :
    diagY (W.map f) (f ∘ P) (f ∘ Q) = f (diagY W P Q) := by
  simp only [diagY, negY_eq, map_diagX, map_negDiagY, map_diagZ]
  simp only [map_neg, map_sub, map_mul, WeierstrassCurve.map]

lemma map_diagXYZ (f : R →+* S) (P Q : Fin 3 → R) :
    diagXYZ (W.map f) (f ∘ P) (f ∘ Q) = f ∘ diagXYZ W P Q := by
  simp only [diagXYZ, map_diagX, map_diagY, map_diagZ, comp_fin3]

lemma proportional_diagXYZ_addXYZ {P Q : Fin 3 → R} (hP : W.Equation P) (hQ : W.Equation Q) :
    Proportional (diagXYZ W P Q) (W.addXYZ P Q) :=
  proportional_negY W (diagX_mul_addZ hP hQ) (negDiagY_mul_addZ hP hQ) (diagX_mul_negAddY hP hQ)







end Ring

section Field

variable {F : Type*} [Field F] {W : Projective F}

lemma ne_zero_of_nonsingular {P : Fin 3 → F} (hP : W.Nonsingular P) : P ≠ 0 := by
  rintro rfl
  exact Y_ne_zero_of_Z_eq_zero hP rfl rfl

lemma nonsingular_iff_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) (P : Fin 3 → F) :
    W.Nonsingular P ↔ W.Equation P ∧ P ≠ 0 := by
  refine ⟨fun h => ⟨h.left, ne_zero_of_nonsingular h⟩, fun ⟨h, h0⟩ => ?_⟩
  by_cases hz : P 2 = 0
  · have hx := X_eq_zero_of_Z_eq_zero h hz
    have hy : P 1 ≠ 0 := fun hy => h0 <| by
      ext i; fin_cases i
      exacts [hx, hy, hz]
    refine (nonsingular_of_Z_eq_zero hz).mpr ⟨h, Or.inr ?_⟩
    simpa [hx] using hy
  · exact (nonsingular_of_Z_ne_zero hz).mpr <|
      (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp <| (equation_of_Z_ne_zero hz).mp h

lemma equiv_of_proportional {T U : Fin 3 → F} (h : Proportional T U) (hT : T ≠ 0) (hU : U ≠ 0) :
    T ≈ U := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hU
  replace hj : U j ≠ 0 := hj
  have e : (T j / U j) • U = T := by
    ext i
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, div_eq_iff hj, h i j]
  have hu : T j / U j ≠ 0 := fun h0 => hT <| by rw [← e, h0, zero_smul]
  exact ⟨Units.mk0 _ hu, e⟩


lemma addXYZ_ne_zero_iff {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.addXYZ P Q ≠ 0 ↔ ¬P ≈ Q := by
  refine ⟨fun h ⟨u, e⟩ => h ?_, fun h => ?_⟩
  · have := addXYZ_smul (W' := W) Q Q u 1
    rw [one_smul, addXYZ_self] at this
    rw [← show (u : F) • Q = P from e, this]
    ext i
    fin_cases i <;> simp
  · rw [← add_of_not_equiv h]
    exact ne_zero_of_nonsingular <| nonsingular_add hP hQ

lemma diagXYZ_equiv_add_of_equiv {P Q : Fin 3 → F} (hP : W.Equation P) (h : P ≈ Q) :
    diagXYZ W P Q ≈ W.add P Q := by
  rw [add_of_equiv h, ← diagXYZ_self hP]
  obtain ⟨u, e⟩ := Setoid.symm h
  have := diagXYZ_smul (W := W) P P 1 u
  rw [one_smul, one_mul] at this
  rw [← show (u : F) • P = Q from e, this]
  exact smul_equiv _ (u.isUnit.pow 2)

lemma diagXYZ_ne_zero_of_equiv {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : P ≈ Q) : diagXYZ W P Q ≠ 0 :=
  ne_zero_of_nonsingular <| (nonsingular_of_equiv <| diagXYZ_equiv_add_of_equiv hP.left h).mpr <|
    nonsingular_add hP hQ

theorem addXYZ_ne_zero_or_diagXYZ_ne_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : W.addXYZ P Q ≠ 0 ∨ diagXYZ W P Q ≠ 0 := by
  by_cases h : P ≈ Q
  · exact Or.inr <| diagXYZ_ne_zero_of_equiv hP hQ h
  · exact Or.inl <| (addXYZ_ne_zero_iff hP hQ).mpr h

lemma addXYZ_equiv_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : W.addXYZ P Q ≠ 0) : W.addXYZ P Q ≈ W.add P Q := by
  rw [add_of_not_equiv <| (addXYZ_ne_zero_iff hP hQ).mp h]

lemma diagXYZ_equiv_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : diagXYZ W P Q ≠ 0) : diagXYZ W P Q ≈ W.add P Q := by
  by_cases e : P ≈ Q
  · exact diagXYZ_equiv_add_of_equiv hP.left e
  · rw [add_of_not_equiv e]
    exact equiv_of_proportional (proportional_diagXYZ_addXYZ hP.left hQ.left) h <|
      (addXYZ_ne_zero_iff hP hQ).mpr e

lemma equiv_add_of_proportional {P Q T : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h₁ : Proportional T (W.addXYZ P Q)) (h₂ : Proportional T (diagXYZ W P Q)) (hT : T ≠ 0) :
    T ≈ W.add P Q := by
  rcases addXYZ_ne_zero_or_diagXYZ_ne_zero hP hQ with h | h
  · exact Setoid.trans (equiv_of_proportional h₁ hT h) (addXYZ_equiv_add hP hQ h)
  · exact Setoid.trans (equiv_of_proportional h₂ hT h) (diagXYZ_equiv_add hP hQ h)

variable [DecidableEq F]

end Field

end GlobalTheory.AddLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
section
open TensorProduct

namespace GlobalTheory.ReducedAlg

theorem eq_zero_of_forall_lTensor_eq_zero {k : Type*} [Field k] {C M : Type*} [AddCommGroup C]
    [Module k C] [AddCommGroup M] [Module k M] {ι : Sort*} {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)] (φ : ∀ i, M →ₗ[k] N i)
    (hφ : ∀ m, (∀ i, φ i m = 0) → m = 0) (z : C ⊗[k] M)
    (hz : ∀ i, (φ i).lTensor C z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis k C
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext j
  rw [Finsupp.coe_zero, Pi.zero_apply]
  have nat : ∀ (i : ι) (w : C ⊗[k] M),
      φ i (TensorProduct.equivFinsuppOfBasisLeft b w j) =
        TensorProduct.equivFinsuppOfBasisLeft b ((φ i).lTensor C w) j := by
    intro i w
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  apply hφ
  intro i
  rw [nat, hz i, map_zero, Finsupp.coe_zero, Pi.zero_apply]

theorem isReduced_tensor_of_forall_prime {k : Type*} [Field k] (C A : Type*) [CommRing C]
    [Algebra k C] [CommRing A] [Algebra k A] [IsReduced A]
    (h : ∀ (p : Ideal A) [p.IsPrime], IsReduced (C ⊗[k] (A ⧸ p))) : IsReduced (C ⊗[k] A) := by
  classical
  refine ⟨fun x hx => ?_⟩
  refine eq_zero_of_forall_lTensor_eq_zero
    (fun p : {p : Ideal A // p.IsPrime} => (Ideal.Quotient.mkₐ k p.1).toLinearMap) ?_ x ?_
  · intro a ha
    have hmem : a ∈ nilradical A := by
      rw [nilradical_eq_sInf, Submodule.mem_sInf]
      intro J hJ
      have h1 := ha ⟨J, hJ⟩
      simpa [Ideal.Quotient.eq_zero_iff_mem] using h1
    exact IsReduced.eq_zero a (mem_nilradical.1 hmem)
  · intro p
    have := p.2
    have := h p.1
    have hF : ∀ w : C ⊗[k] A,
        Algebra.TensorProduct.map (AlgHom.id k C) (Ideal.Quotient.mkₐ k p.1) w =
          (Ideal.Quotient.mkₐ k p.1).toLinearMap.lTensor C w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c a => simp
      | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
    rw [← hF]
    exact IsReduced.eq_zero _
      (hx.map (Algebra.TensorProduct.map (AlgHom.id k C) (Ideal.Quotient.mkₐ k p.1)))

theorem isReduced_field_tensor_domain {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsDomain A] [Algebra.FiniteType k A] :
    IsReduced (K ⊗[k] A) := by
  classical
  have hfp : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus k A := by
    show Algebra.FormallySmooth k (Localization.AtPrime (⊥ : Ideal A))
    have hS : (⊥ : Ideal A).primeCompl = nonZeroDivisors A := by
      ext x
      simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
    have hloc : IsLocalization (nonZeroDivisors A) (Localization.AtPrime (⊥ : Ideal A)) :=
      hS ▸ (inferInstance : IsLocalization (⊥ : Ideal A).primeCompl (Localization.AtPrime (⊥ : Ideal A)))
    have e1 : Algebra.EssFiniteType A (FractionRing A) := .of_isLocalization _ (nonZeroDivisors A)
    have e2 : Algebra.EssFiniteType k (FractionRing A) := .comp k A _
    exact (Algebra.FormallySmooth.iff_of_equiv ((IsLocalization.algEquiv (nonZeroDivisors A)
      (FractionRing A) (Localization.AtPrime (⊥ : Ideal A))).restrictScalars k)).1 inferInstance
  obtain ⟨v, ⟨f, rfl⟩, hv, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hgen Algebra.isOpen_smoothLocus
  have hf0 : f ≠ 0 := by
    have := (PrimeSpectrum.mem_basicOpen f _).1 hv
    simpa using this
  have hsm : Algebra.Smooth k (Localization.Away f) :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.1 hsub
  have hred : IsReduced (K ⊗[k] Localization.Away f) :=
    GlobalTheory.isReduced_of_smooth_of_isIntegrallyClosed K _
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k K) (IsScalarTower.toAlgHom k A (Localization.Away f)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ hinj)

theorem isReduced_field_tensor {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsReduced A] :
    IsReduced (K ⊗[k] A) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).2 hB⟩
  refine isReduced_tensor_of_forall_prime K B (fun p _ => ?_)
  have : Algebra.FiniteType k (B ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p)
      (Ideal.Quotient.mkₐ_surjective k p)
  exact isReduced_field_tensor_domain K (B ⧸ p)

theorem isReduced_tensor {k : Type*} [Field k] [PerfectField k] (A B : Type*)
    [CommRing A] [Algebra k A] [IsReduced A] [CommRing B] [Algebra k B] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  refine isReduced_tensor_of_forall_prime A B (fun p _ => ?_)
  have : IsReduced (FractionRing (B ⧸ p) ⊗[k] A) := isReduced_field_tensor (FractionRing (B ⧸ p)) A
  have : IsReduced (A ⊗[k] FractionRing (B ⧸ p)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k A (FractionRing (B ⧸ p)))
      (Algebra.TensorProduct.comm k A (FractionRing (B ⧸ p))).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k (B ⧸ p) (FractionRing (B ⧸ p))))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective (B ⧸ p) _))

universe u

end GlobalTheory.ReducedAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsApplyEqZeroAndEqOne
section
namespace GlobalTheory.AffinePoints

open Topology Filter Set Polynomial

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

theorem exists_comap_eq_of_isIntegral {K A B : Type*} [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (φ : A →ₐ[K] B) (hφ : φ.toRingHom.IsIntegral)
    (p : A →ₐ[K] K) (hp : ∀ a, φ a = 0 → p a = 0) : ∃ q : B →ₐ[K] K, comap φ q = p := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  have hsurj : Function.Surjective p := fun c => ⟨algebraMap K A c, by simp⟩
  haveI : (RingHom.ker p).IsMaximal := RingHom.ker_isMaximal_of_surjective p hsurj
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) (RingHom.ker p) hp
  have hcomp : ∀ a, Ideal.Quotient.mk Q (φ a) = algebraMap K (B ⧸ Q) (p a) := by
    intro a
    have : a - algebraMap K A (p a) ∈ Q.comap (algebraMap A B) := by
      rw [← Ideal.under_def, hQp]
      simp [RingHom.mem_ker]
    have h2 : φ (a - algebraMap K A (p a)) ∈ Q := this
    rw [map_sub, AlgHom.commutes] at h2
    exact Ideal.Quotient.eq.2 h2
  haveI : Algebra.IsIntegral K (B ⧸ Q) := ⟨fun x => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨h, hm, hb⟩ := hφ b
    refine ⟨h.map p.toRingHom, hm.map _, ?_⟩
    have : (algebraMap K (B ⧸ Q)).comp p.toRingHom = (Ideal.Quotient.mk Q).comp φ.toRingHom := by
      ext a; exact (hcomp a).symm
    rw [eval₂_map, this, ← hom_eval₂, hb, map_zero]⟩
  let e : K ≃ₐ[K] (B ⧸ Q) := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ Q))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K Q), ?_⟩
  ext a
  change e.symm (Ideal.Quotient.mk Q (φ a)) = p a
  rw [hcomp, AlgEquiv.commutes]; rfl

theorem finite_fiber_comap {R A B K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [Field K] [Algebra R K] (φ : A →ₐ[R] B) (hφ : φ.Finite) (p : A →ₐ[R] K) :
    ((comap φ : (B →ₐ[R] K) → (A →ₐ[R] K)) ⁻¹' {p}).Finite := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Algebra A K := p.toRingHom.toAlgebra
  haveI : Module.Finite A B := hφ
  let F : ((comap φ : (B →ₐ[R] K) → (A →ₐ[R] K)) ⁻¹' {p}) → (B →ₐ[A] K) := fun q =>
    { q.1.toRingHom with commutes' := fun a => DFunLike.congr_fun q.2 a }
  refine Set.finite_coe_iff.1 (Finite.of_injective F fun q q' h => ?_)
  ext b
  exact DFunLike.congr_fun h b

theorem norm_le_of_isRoot_monic {h : ℂ[X]} (hm : h.Monic) {t : ℂ} (ht : h.IsRoot t) :
    ‖t‖ ≤ ∑ i ∈ Finset.range h.natDegree, ‖h.coeff i‖ + 1 := by
  have h1 := ht.norm_lt_cauchyBound hm.ne_zero
  have h2 : h.cauchyBound ≤ ∑ i ∈ Finset.range h.natDegree, ‖h.coeff i‖₊ + 1 := by
    simp only [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, add_le_add_iff_right]
    exact Finset.sup_le fun i hi =>
      Finset.single_le_sum (f := fun i => ‖h.coeff i‖₊) (fun _ _ => zero_le) hi
  have h3 := h1.le.trans h2
  simpa [NNReal.coe_sum] using NNReal.coe_le_coe.2 h3

theorem isProperMap_comap (φ : A →ₐ[ℂ] B) (hφ : φ.toRingHom.IsIntegral) :
    IsProperMap (comap φ : (B →ₐ[ℂ] ℂ) → (A →ₐ[ℂ] ℂ)) := by
  refine isProperMap_iff_ultrafilter_of_t2.2 ⟨continuous_comap φ, fun 𝒰 p hp => ?_⟩
  have hlim : ∀ b : B, ∃ t : ℂ, Tendsto (fun q : B →ₐ[ℂ] ℂ => q b) 𝒰 (𝓝 t) := by
    intro b
    obtain ⟨h, hm, hb⟩ := hφ b
    let M : (A →ₐ[ℂ] ℂ) → ℝ := fun r => ∑ i ∈ Finset.range h.natDegree, ‖r (h.coeff i)‖ + 1
    have hM : Continuous M :=
      (continuous_finsetSum _ fun i _ => (continuous_eval _).norm).add continuous_const
    have hbd : ∀ q : B →ₐ[ℂ] ℂ, ‖q b‖ ≤ M (comap φ q) := by
      intro q
      have hr : (h.map (comap φ q).toRingHom).IsRoot (q b) := by
        have : (comap φ q).toRingHom = q.toRingHom.comp φ.toRingHom := rfl
        rw [IsRoot, eval_map, this]
        change eval₂ _ (q.toRingHom b) h = 0
        rw [← hom_eval₂, hb, map_zero]
      have := norm_le_of_isRoot_monic (hm.map _) hr
      simpa [hm.natDegree_map, M] using this
    have hev : ∀ᶠ q in (𝒰 : Filter (B →ₐ[ℂ] ℂ)), q b ∈ Metric.closedBall (0 : ℂ) (M p + 1) := by
      filter_upwards [((hM.tendsto p).comp hp).eventually (gt_mem_nhds (lt_add_one (M p)))]
        with q hq
      exact mem_closedBall_zero_iff.2 ((hbd q).trans hq.le)
    obtain ⟨t, -, ht⟩ := (isCompact_closedBall (0 : ℂ) (M p + 1)).ultrafilter_le_nhds
      (𝒰.map fun q : B →ₐ[ℂ] ℂ => q b) (le_principal_iff.2 hev)
    exact ⟨t, ht⟩
  choose u hu using hlim
  have hu' : Tendsto (fun q : B →ₐ[ℂ] ℂ => (q : B → ℂ)) 𝒰 (𝓝 u) := tendsto_pi_nhds.2 hu
  obtain ⟨q, hq⟩ := (isClosedEmbedding_coe (R := ℂ) (A := B) (C := ℂ)).isClosed_range.mem_of_tendsto
    hu' (Eventually.of_forall fun q => ⟨q, rfl⟩)
  refine ⟨q, ?_⟩
  rw [← tendsto_id', tendsto_nhds_iff]
  intro b
  rw [show q b = u b from congrFun hq b]
  exact hu b

theorem exists_isRoot_norm_lt {h : ℂ[X]} (hm : h.Monic) {ε : ℝ} (hε : 0 ≤ ε)
    (h0 : ‖h.coeff 0‖ < ε ^ h.natDegree) : ∃ t, h.IsRoot t ∧ ‖t‖ < ε := by
  first
  | exact @_root_.GlobalTheory.RootNormBound.exists_root_norm_lt
  | exact _root_.GlobalTheory.RootNormBound.exists_root_norm_lt
  | (apply _root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootNormBound.exists_root_norm_lt ..)

theorem exists_apply_eq_zero_and_eq_one {K : Type*} [Field K] [Algebra K A] (p : A →ₐ[K] K)
    {S : Set (A →ₐ[K] K)} (hS : S.Finite) (hp : p ∉ S) :
    ∃ a : A, p a = 0 ∧ ∀ q ∈ S, q a = 1 := by
  classical
  have : ∀ q ∈ S, ∃ e : A, p e = 1 ∧ q e = 0 := by
    intro q hq
    obtain ⟨b, hb⟩ : ∃ b, p b ≠ q b := by
      by_contra h
      push Not at h
      exact hp (by rwa [AlgHom.ext h])
    refine ⟨(p b - q b)⁻¹ • (b - algebraMap K A (q b)), ?_, by simp⟩
    simp [inv_mul_cancel₀ (sub_ne_zero.2 hb)]
  choose! e he using this
  refine ⟨1 - ∏ q ∈ hS.toFinset, e q, ?_, fun q hq => ?_⟩
  · rw [map_sub, map_one, map_prod, Finset.prod_eq_one fun q hq => (he q (by simpa using hq)).1,
      sub_self]
  · rw [map_sub, map_one, map_prod, Finset.prod_eq_zero (i := q) (by simpa using hq) (he q hq).2,
      sub_zero]

theorem isOpenMap_comap [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] (φ : A →ₐ[ℂ] B)
    (hφ : φ.Finite) (hinj : Function.Injective φ) :
    IsOpenMap (comap φ : (B →ₐ[ℂ] ℂ) → (A →ₐ[ℂ] ℂ)) := by
  have hint : φ.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hφ
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨p, hpU, rfl⟩
  obtain ⟨a, hpa, ha⟩ := exists_apply_eq_zero_and_eq_one p
    ((finite_fiber_comap φ hφ (comap φ p)).diff (t := U)) (fun h => h.2 hpU)
  have hai : IsIntegral A a := hint a
  have hm := minpoly.monic hai
  have hK : IsClosed (comap φ '' (Uᶜ ∩ {q : B →ₐ[ℂ] ℂ | ‖q a‖ ≤ 1 / 2})) :=
    (isProperMap_comap φ hint).isClosedMap _ (hU.isClosed_compl.inter
      (isClosed_le (continuous_eval a).norm continuous_const))
  have hW : IsOpen {r : A →ₐ[ℂ] ℂ |
      ‖r ((minpoly A a).coeff 0)‖ < (1 / 2) ^ (minpoly A a).natDegree} :=
    isOpen_lt (continuous_eval _).norm continuous_const
  refine mem_of_superset ((hK.isOpen_compl.inter hW).mem_nhds ⟨?_, ?_⟩) ?_
  · rintro ⟨q, ⟨hqU, hqa⟩, hq⟩
    rw [mem_setOf_eq, ha q ⟨hq, hqU⟩] at hqa
    norm_num at hqa
  · have h1 : p (φ ((minpoly A a).coeff 0)) = 0 := by
      have h2 : p.toRingHom (eval₂ φ.toRingHom a (minpoly A a)) = 0 := by
        rw [show eval₂ φ.toRingHom a (minpoly A a) = 0 from minpoly.aeval A a, map_zero]
      rw [hom_eval₂, show p.toRingHom a = 0 from hpa, eval₂_at_zero] at h2
      exact h2
    rw [mem_setOf_eq, comap_apply, h1, norm_zero]
    positivity
  · rintro r ⟨hrK, hrW⟩
    obtain ⟨t, ht, htn⟩ := exists_isRoot_norm_lt (h := (minpoly A a).map r.toRingHom) (hm.map _)
      (ε := 1 / 2) (by norm_num) (by simpa [hm.natDegree_map] using hrW)
    let χ : A[X] →ₐ[ℂ] B := (aeval a).restrictScalars ℂ
    have hχ : χ.toRingHom.IsIntegral := by
      refine RingHom.IsIntegral.tower_top (C : A →+* A[X]) χ.toRingHom ?_
      convert hint
      ext x
      simp [χ, RingHom.algebraMap_toAlgebra]
    obtain ⟨q, hq⟩ := exists_comap_eq_of_isIntegral χ hχ (aevalTower r t) fun f hf => by
      obtain ⟨k, rfl⟩ := minpoly.isIntegrallyClosed_dvd hai (p := f) hf
      have : aevalTower r t (minpoly A a) = 0 := by
        rw [IsRoot, eval_map] at ht
        exact ht
      rw [map_mul, this, zero_mul]
    have hqr : comap φ q = r := by
      ext x
      simpa [χ, RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun hq (C x)
    have hqa : q a = t := by simpa [χ] using DFunLike.congr_fun hq X
    refine ⟨q, ?_, hqr⟩
    by_contra hqU
    exact hrK ⟨q, ⟨hqU, by rw [mem_setOf_eq, hqa]; exact htn.le⟩, hqr⟩

end GlobalTheory.AffinePoints
end

