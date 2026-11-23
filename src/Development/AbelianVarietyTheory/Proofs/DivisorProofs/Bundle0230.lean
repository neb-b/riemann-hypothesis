module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardExponentTuplesModEqOneOfPrimeNotDvd
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import GroundTheory.LocalFields.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Formalism.LatticeTheta.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaMatrixOfFinitePadicAlgebraOfLocal
section
open scoped TensorProduct
open Function

namespace GlobalTheory.AzumayaMatrixReduction

theorem of_local : (∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A)) →
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro hloc ℓ _ A _ _ _ Λ _ _ _ _ n hn
  obtain ⟨ι, _, I, hlocI, hcop, hbot⟩ := GlobalTheory.T.exists_localRing_quotients_coprime_iInf_eq_bot ℓ A
  refine GlobalTheory.T.algEquiv_matrix_glue_crt A Λ ι I hcop hbot n fun i => ?_
  haveI := hlocI i
  haveI : IsAzumaya (A ⧸ I i) ((A ⧸ I i) ⊗[A] Λ) := GlobalTheory.T.azumaya_base_change A (A ⧸ I i) Λ
  haveI : Module.Finite ℤ_[ℓ] (A ⧸ I i) :=
    Module.Finite.of_surjective ((IsScalarTower.toAlgHom ℤ_[ℓ] A (A ⧸ I i)).toLinearMap)
      Ideal.Quotient.mk_surjective
  refine hloc ℓ (A ⧸ I i) ((A ⧸ I i) ⊗[A] Λ) n ?_
  haveI : Nontrivial A := (Ideal.Quotient.mk (I i)).domain_nontrivial
  rw [Module.finrank_baseChange, hn]

end GlobalTheory.AzumayaMatrixReduction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardComapMulFinsumEqFinsumFibresStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_comap_mul_finsum_eq_finsum_fibres : ∀ (G₀ G : Type) [Group G₀] [Group G] [Finite G₀] [Finite G] (ι : G₀ →* G) (H : Subgroup G) (T : G → ℂ), (∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = ι k * p) → (Nat.card (H.comap ι) : ℂ) * ∑ᶠ y, T y = ∑ᶠ k : G₀, ∑ᶠ p : H, T (ι k * p) := by
  first | (exact @GlobalTheory.fibre_count_comap_mul) | (exact GlobalTheory.fibre_count_comap_mul) | (intros; apply GlobalTheory.fibre_count_comap_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardExponentTuplesModEqOneOfPrimeNotDvdStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_exponent_tuples_modEq_one_of_prime_not_dvd : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k → (Finset.univ.filter fun a : Fin l → Fin m => k * ∑ i ∈ Finset.range l, q ^ (m * i) ≡ ∑ j : Fin l, k * q ^ (j : ℕ) * (q ^ l) ^ (a j : ℕ) [MOD (q ^ l) ^ m - 1]).card ≡ 1 [MOD l] := by
  first | (exact @GlobalTheory.ExpCount.count_one_mod) | (exact GlobalTheory.ExpCount.count_one_mod) | (intros; apply GlobalTheory.ExpCount.count_one_mod  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroStalkImageOfGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem charZero_stalk_genPt : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y], CharZero Γ(Y, ⊤) →
    ∀ (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    (letI := GlobalTheory.NormSheafDescent.fieldK π hK
     CharZero (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  intro Y Z π _ hY hK
  haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hL : CharZero Y.functionField :=
    charZero_of_injective_ringHom (f := (Y.germToFunctionField ⊤).hom) (Y.germToFunctionField_injective ⊤)
  have h0 : CharZero (Z.presheaf.stalk (genPt π)) := (π.stalkMap (genericPoint Y)).hom.charZero
  exact h0

end GlobalTheory.NormSheafDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDvdOfAevalEqZero
section
open Polynomial Matrix Formalism.UG

namespace GlobalTheory.SepCharpoly

theorem charpoly_dvd_of_aeval_eq_zero :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (p : R[X]),
      M.charpoly.Separable → aeval M p = 0 → M.charpoly ∣ p := by
  intro R _ _ n M p hs hp
  classical
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  rw [← Polynomial.map_dvd_map f hf M.charpoly_monic, ← Matrix.charpoly_map]
  refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval (M.map f) ?_ (p.map f) ?_
  · rw [Matrix.charpoly_map]; exact hs.map
  · rw [show M.map f = (f.mapMatrix : Matrix (Fin n) (Fin n) R →+* _) M from rfl]
    have := congrArg (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId R K)) hp
    rw [← aeval_algHom_apply, map_zero] at this
    rw [aeval_map_algebraMap]
    exact this

end GlobalTheory.SepCharpoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChevalleyExistsLeSupMaximalIdealPowOfAntitone
section
open IsLocalRing

namespace GlobalTheory.Chevalley

theorem exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion (A : Type) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (F : AdicCompletion (maximalIdeal A) A) (n : ℕ) :
    ∃ a : A, F - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal A) A n F)
  refine ⟨a, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem A,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal A).fg_of_isNoetherianRing,
    LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
  first
  | rw [Submodule.mkQ_apply, Algebra.algebraMap_self, RingHom.id_apply, ← ha, sub_self]
  | simp [← ha]

theorem exists_le_sup_maximalIdeal_pow_of_antitone :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A) (J : Ideal A),
      Antitone K → (∀ e, maximalIdeal A ^ e ≤ K e) →
      (∀ (F : AdicCompletion (maximalIdeal A) A) (a : ℕ → A),
        (∀ n, F - algebraMap A (AdicCompletion (maximalIdeal A) A) (a n) ∈
          maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) →
        (∀ n, a n ∈ K n) → F ∈ J.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) →
      ∀ k : ℕ, ∃ e : ℕ, K e ≤ J ⊔ maximalIdeal A ^ k := by
  intro A _ _ _ K J hK hmK hJ k
  let B := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : Module.Flat A B := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let f := algebraMap A B
  have hmB : ∀ n, maximalIdeal B ^ n = (maximalIdeal A ^ n).map f := fun n ↦ by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_pow]
  let K' : ℕ → Ideal B := fun e ↦ (K e).map f
  have hK' : Antitone K' := fun i j hij ↦ Ideal.map_mono (hK hij)
  have hmK' : ∀ e, maximalIdeal B ^ e ≤ K' e := fun e ↦ by
    rw [hmB]; exact Ideal.map_mono (hmK e)
  let N : Ideal B := ⨅ e, K' e
  have hNK : ∀ e, N ≤ K' e := fun e ↦ iInf_le _ e
  have hNJ : N ≤ J.map f := by
    intro F hF
    choose a ha using exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion A F
    refine hJ F a ha fun n ↦ ?_
    have h1 : f (a n) ∈ K' n := by
      have : f (a n) = F - (F - f (a n)) := by abel
      rw [this]
      exact Submodule.sub_mem _ (hNK n hF) (hmK' n (ha n))
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (K n)]
    exact h1
  let P : ℕ → Submodule B (B ⧸ N) := fun e ↦ Submodule.map (Submodule.mkQ N) (K' e : Submodule B B)
  have hdir : Directed (· ≥ ·) P := fun i j ↦
    ⟨max i j, Submodule.map_mono (hK' (le_max_left i j)), Submodule.map_mono (hK' (le_max_right i j))⟩
  have hbot : (⨅ e, P e) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N x
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [Submodule.mem_iInf] at hx ⊢
    intro e
    have := Submodule.mem_comap.2 (hx e)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 (hNK e)] at this
    exact this
  obtain ⟨e, he⟩ := exists_le_maximalIdeal_pow_smul_of_directed B (B ⧸ N) ℕ P ⟨0⟩ hdir hbot k
  refine ⟨e, ?_⟩
  have hsm : (maximalIdeal B ^ k • (⊤ : Submodule B (B ⧸ N))) =
      Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B) := by
    have hI : (maximalIdeal B ^ k • (⊤ : Submodule B B)) = (maximalIdeal B ^ k : Submodule B B) := by
      rw [smul_eq_mul, Ideal.mul_top]
    rw [← Submodule.range_mkQ N, LinearMap.range_eq_map, ← Submodule.map_smul'', hI]
  have h2 : K' e ≤ maximalIdeal B ^ k ⊔ N := by
    intro y hy
    have h := he (Submodule.mem_map_of_mem (f := Submodule.mkQ N) hy)
    rw [hsm] at h
    have h' : y ∈ Submodule.comap (Submodule.mkQ N)
        (Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B)) := h
    rw [Submodule.comap_map_mkQ] at h'
    rw [sup_comm]; exact h'
  have h3 : K' e ≤ (J ⊔ maximalIdeal A ^ k).map f := by
    rw [Ideal.map_sup, ← hmB]
    exact h2.trans (sup_le le_sup_right (hNJ.trans le_sup_left))
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J ⊔ maximalIdeal A ^ k)]
  exact Ideal.map_le_iff_le_comap.1 h3

end GlobalTheory.Chevalley
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginNoeth

def baseHom (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : R →+* D :=
  (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R))

def closure (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Subring D :=
  letI := (baseHom A R D).toAlgebra
  (integralClosure R D).toSubring

def closureAlg (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Algebra R (closure A R D) :=
  ((baseHom A R D).codRestrict (closure A R D) (fun r => by
    letI := (baseHom A R D).toAlgebra
    exact isIntegral_algebraMap (R := R) (A := D) (x := r))).toAlgebra

def ClosureFiniteEtale (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Prop :=
  letI := closureAlg A R D
  Module.Finite R (closure A R D) ∧ Algebra.Etale R (closure A R D) ∧ Nontrivial (closure A R D)

def Good (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (ρ : R →+* A) : Prop :=
  letI := closureAlg A R D
  (∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
      Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] closure A R D)) ∧
    ∃ s : closure A R D →+* FractionRing A,
      s.comp (algebraMap R (closure A R D)) = (algebraMap A (FractionRing A)).comp ρ

end GlobalTheory.KeyOriginNoeth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffNormFormOfFamilyMemRangeIntegrallyClosed
section
open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace GlobalTheory.NormSheaf.IntegralCoeff

open MvPolynomial
open scoped TensorProduct

theorem leftMulMatrix_sum_tmul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    (x : Fin m → L) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis (MvPolynomial (Fin m) K) (Module.finBasis K L))
      (∑ i, (X i : MvPolynomial (Fin m) K) ⊗ₜ[K] x i) =
    ∑ i, (X i : MvPolynomial (Fin m) K) •
      (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* MvPolynomial (Fin m) K) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext a c
  simp [Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_repr_tmul,
    Algebra.TensorProduct.basis_apply]

theorem isIntegral_det_of_aeval {R' F : Type} [CommRing R'] [Field F] [Algebra R' F] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (g : Polynomial R') (hg : g.Monic)
    (h : Polynomial.aeval M (g.map (algebraMap R' F)) = 0) : IsIntegral R' M.det := by
  have hd := GlobalTheory.CharpolyDvd.matrix_charpoly_dvd_pow M _ h
  rw [← Polynomial.map_pow] at hd
  have hc := Polynomial.isIntegral_coeff_of_dvd (g ^ Fintype.card n) M.charpoly (hg.pow _) M.charpoly_monic hd 0
  rw [Matrix.det_eq_sign_charpoly_coeff]
  exact (isIntegral_one.neg.pow _).mul hc

end GlobalTheory.NormSheaf.IntegralCoeff

namespace GlobalTheory.NormSheaf.IntegralCoeff

open MvPolynomial
open scoped TensorProduct

theorem isIntegral_normForm (A K L : Type) [CommRing A] [Field K] [Field L] [Algebra A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L) (hx : ∀ i, IsIntegral A (x i)) :
    @IsIntegral (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) _ _
      MvPolynomial.algebraMvPolynomial (GlobalTheory.NormSheaf.normForm K L x) := by
  classical
  letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
  set R := MvPolynomial (Fin m) K
  set R' := MvPolynomial (Fin m) A
  let F := FractionRing R
  haveI : IsScalarTower R' R F := inferInstance
  let S := R ⊗[K] L
  letI : Algebra R' S := ((algebraMap R S).comp (algebraMap R' R)).toAlgebra
  let y : S := ∑ i, (X i : R) ⊗ₜ[K] x i
  have hy : IsIntegral R' y := by
    refine IsIntegral.sum _ fun i _ => ?_
    have e : (X i : R) ⊗ₜ[K] x i = algebraMap R' S (X i) * (1 ⊗ₜ[K] x i) := by
      have hX : algebraMap R' R (X i) = X i := MvPolynomial.map_X _ _
      change _ = algebraMap R S (algebraMap R' R (X i)) * _
      rw [hX]
      change _ = ((X i : R) ⊗ₜ[K] (1 : L)) * (1 ⊗ₜ[K] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    refine isIntegral_algebraMap.mul ?_
    refine IsIntegral.map_of_comp_eq (algebraMap A R')
      (Algebra.TensorProduct.includeRight : L →ₐ[K] S).toRingHom ?_ (hx i)
    refine RingHom.ext fun a => ?_
    change (algebraMap R' R (algebraMap A R' a)) ⊗ₜ[K] (1 : L) = (1 : R) ⊗ₜ[K] algebraMap A L a
    have h1 : algebraMap R' R (algebraMap A R' a) = algebraMap K R (algebraMap A K a) := by
      change MvPolynomial.map (algebraMap A K) (C a) = C (algebraMap A K a)
      exact MvPolynomial.map_C _ _
    rw [h1, IsScalarTower.algebraMap_apply A K L, Algebra.algebraMap_eq_smul_one (A := R) (algebraMap A K a),
      Algebra.algebraMap_eq_smul_one (A := L) (algebraMap A K a), TensorProduct.smul_tmul]
  obtain ⟨g, hgm, hgy⟩ := hy
  let bS := Algebra.TensorProduct.basis R (Module.finBasis K L)
  let φ : S →ₐ[R] Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F :=
    (AlgHom.mapMatrix (Algebra.ofId R F)).comp (Algebra.leftMulMatrix bS)
  have hM : φ y = (algebraMap R F).mapMatrix
      (∑ i, (X i : R) • (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* R)) := by
    rw [← leftMulMatrix_sum_tmul K L x]
    rfl
  have h0 : Polynomial.aeval (φ y) (g.map (algebraMap R' F)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hh : (algebraMap F (Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F)).comp (algebraMap R' F)
        = φ.toRingHom.comp (algebraMap R' S) := by
      refine RingHom.ext fun r => ?_
      change algebraMap F _ (algebraMap R' F r) = φ (algebraMap R S (algebraMap R' R r))
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R' R F]
      exact (IsScalarTower.algebraMap_apply R F _ _).symm
    rw [hh]
    have h2 := Polynomial.hom_eval₂ g (algebraMap R' S) φ.toRingHom y
    rw [hgy, map_zero] at h2
    exact h2.symm
  have hdet := isIntegral_det_of_aeval _ g hgm h0
  rw [hM, ← RingHom.map_det] at hdet
  exact (isIntegral_algebraMap_iff ).mp hdet

end GlobalTheory.NormSheaf.IntegralCoeff

namespace GlobalTheory.NormSheaf.IntegralCoeff

theorem coeff_normForm_mem_range : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L), (∀ i, IsIntegral A (x i)) →
    ∀ s, (GlobalTheory.NormSheaf.normForm K L x).coeff s ∈ (algebraMap A K).range := by
  intro A K L _ _ _ _ _ _ _ _ _ _ _ m x hx s
  letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
  have key := isIntegral_normForm A K L x hx
  have hc := MvPolynomial.isIntegral_iff_isIntegral_coeff.mp key s
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hc
  exact ⟨a, ha⟩

end GlobalTheory.NormSheaf.IntegralCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexAutomorphismWeierstrassTorsionQCoeffs
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.CoeffConj

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem vmul_dg_apply_zero_and_one {N : ℕ} (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ) :
    _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) 0 = x 0 ∧
      _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) 1 = (a : ZMod N) * x 1 := by
  simp [_root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem ringEquiv_cG_eq (N : ℕ) (g : ℂ ≃+* ℂ) (k : ℕ) :
    g (_root_.GlobalTheory.WpFam.cG N k) = _root_.GlobalTheory.WpFam.cG N k := by
  unfold _root_.GlobalTheory.WpFam.cG
  split_ifs <;> simp [map_ofNat]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem ringEquiv_cSum_eq_cSum_vmul_dg (N : ℕ) (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ)
    (hg : _root_.GlobalTheory.WpFam.ZetaAct g N a) (e : ℕ) (s : ℂ) (hs : g s = s) (x : Fin 2 → ZMod N)
    (k : ℕ) :
    g (_root_.GlobalTheory.WpFam.cSum N e s x k) =
      _root_.GlobalTheory.WpFam.cSum N e s (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
  obtain ⟨h0, h1⟩ := vmul_dg_apply_zero_and_one x a
  unfold _root_.GlobalTheory.WpFam.ZetaAct at hg
  unfold _root_.GlobalTheory.WpFam.cSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [h0, h1]
  simp only [map_mul, map_pow, map_natCast, map_add (f := _), apply_ite g, map_zero, hs, hg]
  rw [mul_neg, mul_left_comm (a : ZMod N)]


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.CoeffConj.main : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.ZetaAct g N a → ∀ (x : Fin 2 → ZMod N) (k : ℕ), g (_root_.GlobalTheory.WpFam.cB N x k) = _root_.GlobalTheory.WpFam.cB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k ∧ g (_root_.GlobalTheory.WpFam.cD N x k) = _root_.GlobalTheory.WpFam.cD N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k ∧ g (_root_.GlobalTheory.WpFam.cG N k) = _root_.GlobalTheory.WpFam.cG N k ∧ g (_root_.GlobalTheory.WpFam.cP N x k) = _root_.GlobalTheory.WpFam.cP N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
  intro N _ g a hg x k
  obtain ⟨h0, h1⟩ := vmul_dg_apply_zero_and_one x a
  have hζ := hg
  unfold _root_.GlobalTheory.WpFam.ZetaAct at hζ
  have hG := ringEquiv_cG_eq N g k
  have hB : g (_root_.GlobalTheory.WpFam.cB N x k) =
      _root_.GlobalTheory.WpFam.cB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
    unfold _root_.GlobalTheory.WpFam.cB
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [if_true, h0, h1]
      split_ifs
      · simp only [map_div₀, map_pow, map_sub, map_one, hζ]
      · exact map_zero g
    · simp only [hk, if_false]
      exact ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 1 1 (map_one g) x k
  have hD : g (_root_.GlobalTheory.WpFam.cD N x k) =
      _root_.GlobalTheory.WpFam.cD N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
    unfold _root_.GlobalTheory.WpFam.cD
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [if_true, h0, h1]
      split_ifs
      · simp only [map_div₀, map_pow, map_sub, map_add (f := _), map_mul, map_one, hζ]
      · exact map_zero g
    · simp only [hk, if_false]
      exact ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 2 (-1) (by simp) x k
  refine ⟨hB, hD, hG, ?_⟩
  have hzero := (_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x (_root_.GlobalTheory.WpFam.dg a)
  unfold _root_.GlobalTheory.WpFam.cP
  by_cases hx : x = 0
  · rw [if_pos hx, if_pos (hzero.2 hx), map_zero]
  · have hx' : _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) ≠ 0 := fun h => hx (hzero.1 h)
    simp only [hx, hx', if_false, map_sub, hB, hG]

end GlobalTheory.WpFam.CoeffConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIsBigORpowLipschitzProductKernelStatement
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_isBigO_rpow_lipschitzProductKernel : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) → Continuous (Phi k z) ∧ ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := by
  first | exact @GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi | exact GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi | (intros; apply GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicSumNormSqEqOneSingleNonzeroStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_sum_normSq_eq_one_single_nonzero : ∀ (l : ℕ) (ζ : ℂ), l.Prime → IsPrimitiveRoot ζ l → ∀ (I : Type) (S : Finset I) (n : I → ℕ → ℤ), ∑ i ∈ S, (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) * star (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) = 1 → ∃ i₀ ∈ S, ∀ i ∈ S, i ≠ i₀ → ∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a = 0 := by
  first | (exact @GlobalTheory.cyclo_sum_mul_star_eq_one_single) | (exact GlobalTheory.cyclo_sum_mul_star_eq_one_single) | (intros; apply GlobalTheory.cyclo_sum_mul_star_eq_one_single <;> assumption)
end

