module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNatCoeffsDetSumSmulNeZero
section
open scoped Matrix
open Polynomial

namespace GlobalTheory

theorem det_affine_eval {K : Type} [Field K] {m : ℕ} (U V : Matrix (Fin m) (Fin m) K) (t : K) :
    ((X : K[X]) • V.map C + U.map C).det.eval t = (U + t • V).det := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [add_comm]
  ring

theorem exists_nat_det_ne_zero_affine {K : Type} [Field K] [CharZero K] {m : ℕ}
    (U V : Matrix (Fin m) (Fin m) K) (t : K) (h : (U + t • V).det ≠ 0) :
    ∃ k : ℕ, (U + (k : K) • V).det ≠ 0 := by
  classical
  set p : K[X] := ((X : K[X]) • V.map C + U.map C).det
  have hp : p ≠ 0 := by
    intro h0
    apply h
    rw [← det_affine_eval]
    simp [p, h0]
  by_contra hall
  push_neg at hall
  have hsub : Set.range (fun k : ℕ => (k : K)) ⊆ (p.roots.toFinset : Set K) := by
    rintro _ ⟨k, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot, det_affine_eval]
    exact hall k
  have hinf : (Set.range (fun k : ℕ => (k : K))).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  exact hinf ((p.roots.toFinset.finite_toSet).subset hsub)

theorem exists_nat_coeffs_on_finset_det_sum_ne_zero {K : Type} [Field K] [CharZero K] {m n : ℕ}
    (T : Fin n → Matrix (Fin m) (Fin m) K) (s : Finset (Fin n)) :
    ∀ b : Fin n → K, (∑ i, b i • T i).det ≠ 0 →
      ∃ b' : Fin n → K, (∑ i, b' i • T i).det ≠ 0 ∧ ∀ i ∈ s, ∃ k : ℕ, b' i = k := by
  classical
  induction s using Finset.induction_on with
  | empty => intro b hb; exact ⟨b, hb, by simp⟩
  | insert j s hj ih =>
    intro b hb
    obtain ⟨b₁, hb₁, hs⟩ := ih b hb
    have key : ∀ t : K, ∑ i, Function.update b₁ j t i • T i
        = (∑ i, Function.update b₁ j 0 i • T i) + t • T j := by
      intro t
      have h1 := Finset.sum_erase_add (s := Finset.univ) (a := j)
        (f := fun i => Function.update b₁ j t i • T i) (Finset.mem_univ j)
      have h2 := Finset.sum_erase_add (s := Finset.univ) (a := j)
        (f := fun i => Function.update b₁ j 0 i • T i) (Finset.mem_univ j)
      have h3 : ∑ i ∈ Finset.univ.erase j, Function.update b₁ j t i • T i
          = ∑ i ∈ Finset.univ.erase j, Function.update b₁ j 0 i • T i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
          Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [← h1, ← h2, h3]
      simp
    have hb₁' : ((∑ i, Function.update b₁ j 0 i • T i) + b₁ j • T j).det ≠ 0 := by
      rw [← key, Function.update_eq_self]; exact hb₁
    obtain ⟨k, hk⟩ := exists_nat_det_ne_zero_affine _ _ _ hb₁'
    refine ⟨Function.update b₁ j (k : K), by rw [key]; exact hk, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact ⟨k, by simp⟩
    · obtain ⟨k', hk'⟩ := hs i hi'
      refine ⟨k', ?_⟩
      rw [Function.update_of_ne (by rintro rfl; exact hj hi')]
      exact hk'

theorem exists_nat_coeffs_det_ne_zero : ∀ {K : Type} [Field K] [CharZero K] {m n : ℕ}
    (T : Fin n → Matrix (Fin m) (Fin m) K) (b : Fin n → K),
    (∑ i, b i • T i).det ≠ 0 → ∃ a : Fin n → ℕ, (∑ i, (a i : K) • T i).det ≠ 0 := by
  intro K _ _ m n T b hb
  obtain ⟨b', hb', hs⟩ := exists_nat_coeffs_on_finset_det_sum_ne_zero T Finset.univ b hb
  choose a ha using fun i => hs i (Finset.mem_univ i)
  refine ⟨a, ?_⟩
  simp_rw [← ha]; exact hb'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormForm
section
open Polynomial

namespace GlobalTheory.NormFormBound

theorem prod_pow_bound {k σ : Type} [Field k] (s : Finset σ) (m : σ → ℕ) (p : σ → k[X]) (d : ℕ)
    (hp : ∀ i, (p i).natDegree ≤ d) :
    (∏ i ∈ s, p i ^ m i).natDegree ≤ (∑ i ∈ s, m i) * d ∧
      (∏ i ∈ s, p i ^ m i).coeff ((∑ i ∈ s, m i) * d) = ∏ i ∈ s, (p i).coeff d ^ m i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, add_mul]
    have hpa : (p a ^ m a).natDegree ≤ m a * d :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hp a))
    refine ⟨natDegree_mul_le.trans (add_le_add hpa ih1), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hpa ih1, coeff_pow_of_natDegree_le (hp a), ih2, Finset.prod_insert ha]

theorem form_bound {k σ : Type} [Field k] [Infinite k] [Fintype σ] (n : ℕ)
    (F : MvPolynomial σ k[X]) (hF : F.IsHomogeneous n) (h0 : F ≠ 0) :
    ∃ (c : ℕ) (lam : σ → k),
      (∀ (d : ℕ) (p : σ → k[X]), (∀ i, (p i).natDegree ≤ d) →
        (MvPolynomial.eval p F).natDegree ≤ n * d + c) ∧
      ∀ (d : ℕ) (p : σ → k[X]), (∀ i, (p i).natDegree ≤ d) → (∀ i, (p i).coeff d = lam i) →
        (MvPolynomial.eval p F).coeff (n * d + c) ≠ 0 := by
  classical
  set c := F.support.sup (fun m => (F.coeff m).natDegree) with hc
  set G : MvPolynomial σ k := ∑ m ∈ F.support, MvPolynomial.monomial m ((F.coeff m).coeff c) with hG
  have hsumdeg : ∀ m ∈ F.support, ∑ i ∈ m.support, m i = n := by
    intro m hm
    have h := hF (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  have hcle : ∀ m ∈ F.support, (F.coeff m).natDegree ≤ c := fun m hm =>
    Finset.le_sup (f := fun m => (F.coeff m).natDegree) hm
  have hG0 : G ≠ 0 := by
    have hne : F.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
    obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image F.support (fun m => (F.coeff m).natDegree) hne
    have hcm : c = (F.coeff m0).natDegree :=
      le_antisymm (Finset.sup_le fun m hm => hmax m hm) (hcle m0 hm0)
    intro hG'
    have h1 := congrArg (AddMonoidAlgebra.coeff · m0) hG'
    rw [hG, MvPolynomial.coeff_sum, Finset.sum_eq_single m0] at h1
    · rw [MvPolynomial.coeff_monomial, if_pos rfl, hcm, MvPolynomial.coeff_zero] at h1
      exact (MvPolynomial.mem_support_iff.mp hm0) (Polynomial.leadingCoeff_eq_zero.mp h1)
    · intro m _ hm
      rw [MvPolynomial.coeff_monomial, if_neg hm]
    · intro h
      exact absurd hm0 h
  obtain ⟨lam, hlam⟩ : ∃ lam : σ → k, MvPolynomial.eval lam G ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hG0 (MvPolynomial.funext fun x => by simpa using hall x)
  refine ⟨c, lam, ?_, ?_⟩
  · intro d p hp
    rw [MvPolynomial.eval_eq]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    have hdeg := (prod_pow_bound m.support m p d hp).1
    rw [hsumdeg m hm] at hdeg
    refine natDegree_mul_le.trans ?_
    have := hcle m hm
    omega
  · intro d p hp hpl
    rw [MvPolynomial.eval_eq, Polynomial.finsetSum_coeff]
    have hterm : ∀ m ∈ F.support, (F.coeff m * ∏ i ∈ m.support, p i ^ m i).coeff (n * d + c) =
        (F.coeff m).coeff c * ∏ i ∈ m.support, lam i ^ m i := by
      intro m hm
      have hb := prod_pow_bound m.support m p d hp
      rw [hsumdeg m hm] at hb
      rw [add_comm (n * d) c, coeff_mul_add_eq_of_natDegree_le (hcle m hm) hb.1, hb.2]
      simp [hpl]
    rw [Finset.sum_congr rfl hterm]
    have hev : MvPolynomial.eval lam G =
        ∑ m ∈ F.support, (F.coeff m).coeff c * ∏ i ∈ m.support, lam i ^ m i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hG, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.eval_monomial, Finsupp.prod]
    rw [← hev]
    exact hlam

theorem exists_norm_form {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
    (b : Module.Basis (Fin n) R A) :
    ∃ F : MvPolynomial (Fin n) R, F.IsHomogeneous n ∧
      ∀ p : Fin n → R, MvPolynomial.eval p F = Algebra.norm R (∑ i, p i • b i) := by
  classical
  refine ⟨(Matrix.of fun a c => ∑ i, MvPolynomial.C (Algebra.leftMulMatrix b (b i) a c) *
      MvPolynomial.X i).det, ?_, ?_⟩
  · rw [Matrix.det_apply]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    have hC : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n) R) =
        MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
    rw [hC]
    have hent : ∀ a ∈ (Finset.univ : Finset (Fin n)), ((Matrix.of fun a c => ∑ i,
        MvPolynomial.C (Algebra.leftMulMatrix b (b i) a c) * MvPolynomial.X i) (σ a) a).IsHomogeneous 1 := by
      intro a _
      rw [Matrix.of_apply]
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) (Algebra.leftMulMatrix b (b i) (σ a) a)).mul
        (MvPolynomial.isHomogeneous_X R i)
    have hmul := (MvPolynomial.isHomogeneous_C (Fin n) ((Equiv.Perm.sign σ : ℤ) : R)).mul
      (MvPolynomial.IsHomogeneous.prod _ _ (fun _ => 1) hent)
    simpa using hmul
  · intro p
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext a c
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Matrix.sum_apply, mul_comm]

theorem norm_degree (k A : Type) [Field k] [Infinite k] [CommRing A] [IsDomain A]
    [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) :
    ∃ (c : ℕ) (lam : Fin n → k),
      (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).natDegree ≤ d) →
        (Algebra.norm k[X] (∑ i, p i • b i)).natDegree ≤ n * d + c) ∧
      ∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).degree < (d : WithBot ℕ)) →
        ∑ i, (C (lam i) * X ^ d + p i) • b i ≠ 0 ∧
          (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).natDegree = n * d + c := by
  classical
  haveI : Module.Free k[X] A := Module.Free.of_basis b
  haveI : Module.Finite k[X] A := Module.Finite.of_basis b
  obtain ⟨F, hFh, hFev⟩ := exists_norm_form n b
  have hF0 : F ≠ 0 := by
    intro hF
    have h1 := hFev (fun i => b.repr 1 i)
    rw [hF, map_zero, b.sum_repr 1, map_one] at h1
    exact one_ne_zero h1.symm
  obtain ⟨c, lam, hb1, hb2⟩ := form_bound n F hFh hF0
  refine ⟨c, lam, fun d p hp => ?_, fun d p hp => ?_⟩
  · rw [← hFev]
    exact hb1 d p hp
  · have hq1 : ∀ i, (C (lam i) * X ^ d + p i).natDegree ≤ d := fun i =>
      (natDegree_add_le _ _).trans
        (max_le (natDegree_C_mul_X_pow_le _ _) (natDegree_le_of_degree_le (hp i).le))
    have hq2 : ∀ i, (C (lam i) * X ^ d + p i).coeff d = lam i := fun i => by
      rw [coeff_add, coeff_C_mul_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt (hp i), add_zero]
    have hN : (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).coeff (n * d + c) ≠ 0 := by
      rw [← hFev]
      exact hb2 d (fun i => C (lam i) * X ^ d + p i) hq1 hq2
    refine ⟨fun h0 => hN (by rw [h0, Algebra.norm_zero, coeff_zero]), ?_⟩
    apply le_antisymm
    · rw [← hFev]
      exact hb1 d (fun i => C (lam i) * X ^ d + p i) hq1
    · exact le_natDegree_of_ne_zero hN

end GlobalTheory.NormFormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimeNatCastMem
section
namespace GlobalTheory.PrimeNatCastMembership

theorem exists_prime_natCast_mem {A : Type} [inst : CommRing A] (P : Ideal A) (hP : Ideal.IsPrime P)
    (n : ℕ) (hn : n ≠ (0 : ℕ)) (hmem : (↑n : A) ∈ P) :
    ∃ (q : ℕ), Nat.Prime q ∧ (↑q : A) ∈ P := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hmem)) hP.ne_top
    · obtain ⟨q, hq, m, hm⟩ := Nat.exists_prime_and_dvd h1
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hn (by simpa using hm)
      have hlt : m < n := by
        have h2 := hq.two_le
        have h3 := Nat.pos_of_ne_zero hm0
        rw [hm]
        nlinarith
      have hprod : (q : A) * (m : A) ∈ P := by
        rw [← Nat.cast_mul, ← hm]
        exact hmem
      rcases hP.mem_or_mem hprod with h | h
      · exact ⟨q, hq, h⟩
      · exact ih m hlt hm0 h

end GlobalTheory.PrimeNatCastMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSpectralValuationAlgebraicExtension
section
open scoped NNReal TensorProduct

namespace GlobalTheory

open Polynomial

theorem exists_spectralValuation (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (f : AbsoluteValue K ℝ) (hna : IsNonarchimedean f) (hnt : f.IsNontrivial)
    (hc : CompleteSpace (WithAbs f)) :
    ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧
      ∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1 := by
  obtain ⟨a, ha⟩ := hnt.exists_abv_gt_one
  letI : NontriviallyNormedField (WithAbs f) :=
    NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs f a, by
      intro h; rw [WithAbs.toAbs_eq_zero] at h; rw [h, map_zero] at ha; linarith, by
      rw [WithAbs.norm_toAbs_eq]; exact ha.ne'⟩
  haveI : IsUltrametricDist (WithAbs f) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => hna x.ofAbs y.ofAbs
  haveI : IsScalarTower K (WithAbs f) Ω := inferInstance
  haveI : Algebra.IsAlgebraic (WithAbs f) Ω := Algebra.IsAlgebraic.tower_top (K := K) (WithAbs f)
  have hmin : ∀ x : Ω, minpoly (WithAbs f) x = (minpoly K x).map (algebraMap K (WithAbs f)) := by
    intro x
    have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hmap : (minpoly K x).map (algebraMap K (WithAbs f)) =
        Polynomial.mapEquiv (WithAbs.equiv f).symm (minpoly K x) := by
      rw [Polynomial.mapEquiv_apply]; rfl
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · rw [hmap]; exact (MulEquiv.irreducible_iff _).mpr (minpoly.irreducible hx)
    · rw [Polynomial.aeval_map_algebraMap]; exact minpoly.aeval K x
    · exact (minpoly.monic hx).map _
  let v : Valuation Ω ℝ≥0 :=
    { toFun := fun x => ⟨spectralNorm (WithAbs f) Ω x, spectralNorm_nonneg x⟩
      map_zero' := by ext; exact spectralNorm_zero
      map_one' := by ext; exact spectralNorm_one
      map_mul' := fun x y => by
        ext; exact spectralAlgNorm_mul (K := WithAbs f) (L := Ω) x y
      map_add_le_max' := fun x y => by
        show spectralNorm (WithAbs f) Ω (x + y) ≤ max (spectralNorm (WithAbs f) Ω x) (spectralNorm (WithAbs f) Ω y)
        exact isNonarchimedean_spectralNorm x y }
  have hv : ∀ x : Ω, (v x : ℝ) = spectralNorm (WithAbs f) Ω x := fun _ => rfl
  refine ⟨v, fun x => ?_, fun x => ?_⟩
  · rw [hv]
    have : algebraMap K Ω x = algebraMap (WithAbs f) Ω (WithAbs.toAbs f x) := rfl
    rw [this, spectralNorm_extends, WithAbs.norm_toAbs_eq]
  · have hx : IsIntegral (WithAbs f) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [← NNReal.coe_le_coe, NNReal.coe_one, hv]
    show spectralValue (minpoly (WithAbs f) x) ≤ 1 ↔ _
    rw [spectralValue_le_one_iff (minpoly.monic hx), hmin x]
    refine forall_congr' fun i => ?_
    rw [Polynomial.coeff_map, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
section
noncomputable section

namespace GlobalTheory

open TensorProduct

theorem isPrecomplete_of_finite {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t with
  | tmul a m =>
    obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I R a
    refine ⟨r • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, show AdicCompletion.of I R r =
      algebraMap R (AdicCompletion I R) r by simp [AdicCompletion.algebraMap_apply],
      algebraMap_smul, map_smul]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv]⟩

theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  rw [isAdicComplete_iff]
  exact ⟨IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson I), isPrecomplete_of_finite I M⟩

theorem isAdicComplete_map_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (I.map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  exact isAdicComplete_of_finite I S

section Tower

variable {R : Type*} [CommRing R] (I : Ideal R)

end Tower

section Quotient

variable {R : Type*} [CommRing R] (I : Ideal R)

variable [IsNoetherianRing R] [IsAdicComplete I R] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

end Quotient

section Tensor

variable {R : Type*} [CommRing R] (I : Ideal R)

variable [IsNoetherianRing R] [IsAdicComplete I R]

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

end


section

variable {A B : Type*} [Ring A] [Ring B] [Bialgebra R A] [Bialgebra R B]

end

end Tensor

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteQuotientComap
section
open NumberField

namespace GlobalTheory.FiniteQuotientComap

theorem exists_int_mul_mem {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ b : 𝓞 E, (b : E) = (m : E) * a := by

  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (R := ℤ) (Rₘ := ℚ)
    (M := nonZeroDivisors ℤ) a (Algebra.IsIntegral.isIntegral a)
  refine ⟨(m : ℤ), nonZeroDivisors.coe_ne_zero m, (⟨m • a, hm⟩ : 𝓞 E), ?_⟩
  show m • a = _
  rw [Submonoid.smul_def, zsmul_eq_mul]

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨k, hk0, hk⟩ := hz
    refine ⟨m * k, mul_ne_zero hm0 hk0, ?_⟩
    have e1 : (m * k) • y = k • (m • y) := by rw [mul_comm, mul_smul]
    have e2 : (m * k) • z = m • (k • z) := mul_smul m k z
    rw [smul_add, e1, e2]
    exact add_mem (zsmul_mem hm k) (zsmul_mem hk m)
  | smul c y _ hy =>

    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨k, hk0, b, hb⟩ := exists_int_mul_mem c
    refine ⟨k * m, mul_ne_zero hk0 hm0, ?_⟩
    have e : (k * m) • (c • y) = b • (m • y) := by
      ext i
      simp [Algebra.smul_def, hb]
      ring
    rw [e]
    exact L.smul_mem b hm

theorem finite_quotient_comap {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L₀ L : Submodule (𝓞 E) (Fin n → E)) (h₀ : L₀.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := by

  have : Module.Finite (𝓞 E) L₀ := Module.Finite.iff_fg.mpr h₀
  have : Module.Finite ℤ L₀ := Module.Finite.trans (𝓞 E) L₀
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.comap L₀.subtype L) q
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem L (y : Fin n → E) (by rw [hL]; exact Submodule.mem_top)
  refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm0⟩, ?_⟩
  change (m : ℤ) • (Submodule.Quotient.mk y : L₀ ⧸ Submodule.comap L₀.subtype L) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  simpa using hm

end GlobalTheory.FiniteQuotientComap
end

