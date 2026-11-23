module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0001
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGoodRootOfHenselianSepClosedResidue
section
noncomputable section
open IsLocalRing UpperTheory.Et

open Polynomial in
private lemma split_of_units {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) (ζ : A) (hq : q ≠ 0) (h1 : ζ ^ q = 1)
    (hu : ∀ i ∈ Finset.range q, ∀ j ∈ Finset.range q, i ≠ j → IsUnit (ζ ^ i - ζ ^ j)) :
    (X ^ q - 1 : A[X]) = ∏ a ∈ Finset.range q, (X - C (ζ ^ a)) := by
  have hmon : ∀ a ∈ Finset.range q, (X - C (ζ ^ a) : A[X]).Monic := fun a _ => monic_X_sub_C _
  have hdvd : (∏ a ∈ Finset.range q, (X - C (ζ ^ a))) ∣ (X ^ q - 1 : A[X]) := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      exact isCoprime_X_sub_C_of_isUnit_sub (hu i hi j hj hij)
    · intro a _
      rw [dvd_iff_isRoot]
      show eval (ζ ^ a) (X ^ q - 1 : A[X]) = 0
      rw [eval_sub, eval_pow, eval_X, eval_one, ← pow_mul, mul_comm, pow_mul, h1, one_pow, sub_self]
  have hm1 : (X ^ q - 1 : A[X]).Monic := by
    have h := monic_X_pow_sub_C (1 : A) hq
    rwa [map_one] at h
  refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_of_monic _ _ hmon) hm1 hdvd ?_
  rw [natDegree_prod_of_monic _ _ hmon]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  rw [← map_one C, natDegree_X_pow_sub_C _]

theorem UpperTheory.exists_goodRoot_of_henselian_sepClosed_residue :
    ∀ (A : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)] (q : ℕ), IsUnit (q : A) → ∃ ζ : A, GoodRoot q ζ := by
  intro A _ _ _ q hqu
  have hqk : ((q : ResidueField A)) ≠ 0 := by
    rw [← map_natCast (residue A)]
    exact (residue_ne_zero_iff_isUnit _).2 hqu
  haveI : NeZero (q : ResidueField A) := ⟨hqk⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hqk (by simp)
  haveI : NeZero q := ⟨hq0⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ResidueField A) q
  obtain ⟨a0, rfl⟩ := residue_surjective z
  have ha0 : IsUnit a0 := (residue_ne_zero_iff_isUnit _).1 (hz.ne_zero hq0)
  have hmon : (Polynomial.X ^ q - 1 : Polynomial A).Monic := by
    have h := Polynomial.monic_X_pow_sub_C (1 : A) hq0
    rwa [map_one] at h
  obtain ⟨ζ, hroot, hζ⟩ := HenselianLocalRing.is_henselian (Polynomial.X ^ q - 1 : Polynomial A) hmon a0
    (by
      rw [← residue_eq_zero_iff]
      simp [hz.pow_eq_one])
    (by
      simp only [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
        Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_natCast,
        Polynomial.eval_pow, Polynomial.eval_X]
      exact hqu.mul (ha0.pow _))
  have hζq : ζ ^ q = 1 := by
    have h := hroot.eq_zero
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at h
    exact sub_eq_zero.1 h
  have hres : residue A ζ = residue A a0 := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hζ
  have hunits : ∀ i < q, ∀ j < q, i ≠ j → IsUnit (ζ ^ i - ζ ^ j) := by
    intro i hi j hj hij
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_pow, map_pow, hres]
    intro h
    exact hij (hz.pow_inj hi hj (sub_eq_zero.1 h))
  refine ⟨ζ, hζq, ?_, ?_⟩
  · intro a b hab
    exact hunits a.val (ZMod.val_lt a) b.val (ZMod.val_lt b) (fun h => hab (ZMod.val_injective q h))
  · intro S' _ φ x
    have key := split_of_units q ζ hq0 hζq
      (fun i hi j hj hij => hunits i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij)
    have h := congrArg (Polynomial.eval₂ φ x) key
    simpa [Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow, Polynomial.eval₂_C] using h

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicLaurentPolynomialNearRootOfUnity
section
noncomputable section
open IsLocalRing UpperTheory.Et

theorem UpperTheory.exists_monic_laurent_polynomial_near_root_of_unity :
    ∀ (A D : Type) [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Int → ∀ (q : ℕ), 0 < q → ∀ w : D, w ^ q - 1 ∈ mm (⊤ : Subalgebra A D) →
      ∃ (φ : LaurentPolynomial A →ₐ[A] D) (P : Polynomial (LaurentPolynomial A)) (n : ℕ), φ (LaurentPolynomial.T 1) = T.t ∧ φ (LaurentPolynomial.T (-1)) = T.s ∧ P.Monic ∧ P.eval₂ φ.toRingHom w = 0 ∧
        ∀ i, (P - (Polynomial.X ^ q - 1) ^ n).coeff i ∈ (maximalIdeal A).map (algebraMap A (LaurentPolynomial A)) := by
  intro A D _ _ _ _ T hI q hq w hw
  classical
  let τ : Dˣ := ⟨T.t, T.s, T.ts, by rw [mul_comm]; exact T.ts⟩
  let φ0 : LaurentPolynomial A →+* D := LaurentPolynomial.eval₂ (algebraMap A D) τ
  have hcomm : ∀ a : A, φ0 (algebraMap A (LaurentPolynomial A) a) = algebraMap A D a := by
    intro a
    simp [φ0, LaurentPolynomial.algebraMap_apply]
  let φ : LaurentPolynomial A →ₐ[A] D := { φ0 with commutes' := hcomm }
  have ht : φ (LaurentPolynomial.T 1) = T.t := by
    change φ0 _ = _
    simp [φ0, τ]
  have hs : φ (LaurentPolynomial.T (-1)) = T.s := by
    change φ0 _ = _
    simp [φ0, τ, zpow_neg]
  letI : Algebra (LaurentPolynomial A) D := φ.toRingHom.toAlgebra
  have hmap : ∀ r, algebraMap (LaurentPolynomial A) D r = φ r := fun _ => rfl
  have hadj : Algebra.adjoin A {T.t} ≤ φ.range := by
    refine Algebra.adjoin_le ?_
    rintro _ rfl
    exact ⟨_, ht⟩
  have hB : ∀ b ∈ T.B, IsIntegral (LaurentPolynomial A) b := by
    intro b hb
    obtain ⟨p, hpm, hp0⟩ := hI.1 b hb
    have hl : p.map (algebraMap (Algebra.adjoin A {T.t}) D) ∈
        Polynomial.lifts (algebraMap (LaurentPolynomial A) D) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨r, hr⟩ := hadj (p.coeff n).2
      exact ⟨r, hr⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hpm.map _)
    refine ⟨Q, hQm, ?_⟩
    rw [← Polynomial.eval_map, hQ, Polynomial.eval_map]
    exact hp0
  have hint : Algebra.IsIntegral (LaurentPolynomial A) D := by
    refine ⟨fun x => ?_⟩
    obtain ⟨k, hk⟩ := T.locB x
    have hsI : IsIntegral (LaurentPolynomial A) T.s := by
      rw [← hs]
      exact isIntegral_algebraMap
    have : x = T.s ^ k * (T.t ^ k * x) := by
      rw [← mul_assoc, ← mul_pow, mul_comm T.s, T.ts, one_pow, one_mul]
    rw [this]
    exact (hsI.pow k).mul (hB _ hk)
  have hu : w ^ q - 1 ∈ Ideal.map (algebraMap (LaurentPolynomial A) D)
      ((maximalIdeal A).map (algebraMap A (LaurentPolynomial A))) := by
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro a ha d _
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      have : algebraMap A D a = algebraMap (LaurentPolynomial A) D (algebraMap A (LaurentPolynomial A) a) := by
        rw [hmap]
        exact (hcomm a).symm
      rw [this]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
    · intro x y hx hy
      exact Ideal.add_mem _ hx hy
  obtain ⟨Q, hQm, hQ0, hQc⟩ := Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hu
  set I := (maximalIdeal A).map (algebraMap A (LaurentPolynomial A)) with hIdef
  have hmon : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : LaurentPolynomial A) hq.ne'
  have hdeg : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).natDegree ≠ 0 := by
    have := Polynomial.natDegree_X_pow_sub_C (n := q) (1 : LaurentPolynomial A)
    rw [map_one] at this
    rw [this]
    exact hq.ne'
  refine ⟨φ, Q.comp (Polynomial.X ^ q - 1), Q.natDegree, ht, hs, hQm.comp hmon hdeg, ?_, ?_⟩
  · rw [Polynomial.eval₂_comp]
    have : Polynomial.eval₂ φ.toRingHom w (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)) = w ^ q - 1 := by
      simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow]
    rw [this]
    exact hQ0
  · intro i
    have hcoef : ∀ j, (Q - Polynomial.X ^ Q.natDegree).coeff j ∈ I := by
      intro j
      by_cases hj : j = Q.natDegree
      · subst hj
        have : Q.coeff Q.natDegree = 1 := hQm
        simp [this]
      · simpa [Polynomial.coeff_X_pow, hj] using hQc j hj
    have heq : Q.comp (Polynomial.X ^ q - 1) - (Polynomial.X ^ q - 1) ^ Q.natDegree =
        (Q - Polynomial.X ^ Q.natDegree).comp (Polynomial.X ^ q - 1) := by
      simp [Polynomial.sub_comp]
    rw [heq, ← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_comp]
    have : (Q - Polynomial.X ^ Q.natDegree).map (Ideal.Quotient.mk I) = 0 := by
      ext j
      rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact hcoef j
    rw [this]
    simp

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsPolynomialEqMapEvalRootsOfPermInvariant
section
noncomputable section
open Polynomial

theorem UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant :
    ∀ (A : Type) [CommRing A] (N : ℕ) (g : A[X]) (Φ : (MvPolynomial (Fin N) A)[X]), (∀ σ : Equiv.Perm (Fin N), Φ.map (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom = Φ) →
      ∃ p : A[X], p.natDegree ≤ Φ.natDegree ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) → p.map (algebraMap A S) = Φ.map (MvPolynomial.aeval x : MvPolynomial (Fin N) A →ₐ[A] S).toRingHom := by
  intro A _ N g Φ hΦ
  have hsym : ∀ n, (Φ.coeff n).IsSymmetric := by
    intro n σ
    have := congrArg (fun q => q.coeff n) (hΦ σ)
    simpa [Polynomial.coeff_map] using this
  choose a ha using fun n => UpperTheory.exists_eval_roots_symmetric_eq_algebraMap A N g (Φ.coeff n) (hsym n)
  refine ⟨∑ n ∈ Finset.range (Φ.natDegree + 1), monomial n (a n), ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun n hn => ?_)
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
  · intro S _ _ x hx
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hn
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ha n S x hx]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsPowerDecompositionOfRootOfUnity
section
noncomputable section
open IsLocalRing UpperTheory.Et

namespace UpperTheory.LineDecomposition

variable {A D : Type} [CommRing A] [CommRing D] [Algebra A D]

private lemma tsPow (T : TC A D) (i : ℕ) : T.t ^ i * T.s ^ i = 1 := by
  rw [← mul_pow, T.ts, one_pow]

private lemma memS (T : TC A D) {j : ℕ} {x : D} : x ∈ T.S j ↔ x ∈ T.B ∧ T.s ^ j * x ∈ T.C :=
  Iff.rfl

private lemma evB (T : TC A D) (x : D) : ∃ k : ℕ, ∀ m ≥ k, T.t ^ m * x ∈ T.B := by
  obtain ⟨k, hk⟩ := T.locB x
  refine ⟨k, fun m hm => ?_⟩
  have e : T.t ^ m * x = T.t ^ (m - k) * (T.t ^ k * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  rw [e]
  exact T.B.mul_mem (T.B.pow_mem T.tB _) hk

private lemma evC (T : TC A D) (x : D) : ∃ k : ℕ, ∀ m ≥ k, T.s ^ m * x ∈ T.C := by
  obtain ⟨k, hk⟩ := T.locC x
  refine ⟨k, fun m hm => ?_⟩
  have e : T.s ^ m * x = T.s ^ (m - k) * (T.s ^ k * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  rw [e]
  exact T.C.mul_mem (T.C.pow_mem T.sC _) hk

private lemma evCfin (T : TC A D) (F : Finset D) :
    ∃ k : ℕ, ∀ m ≥ k, ∀ z ∈ F, T.s ^ m * z ∈ T.C := by
  choose k hk using fun z => evC T z
  exact ⟨F.sup k, fun m hm z hz => hk z m (le_trans (Finset.le_sup hz) hm)⟩

private def NN (T : TC A D) (X : Finset D) : Submodule A D :=
  Submodule.span A {y | ∃ x ∈ X, ∃ j : ℕ, y = T.s ^ j * x}

private lemma NN_mul (T : TC A D) (X : Finset D) {u : D} (hu : ∀ x ∈ X, u * x ∈ T.C)
    {n : D} (hn : n ∈ NN T X) : u * n ∈ T.C := by
  unfold NN at hn
  induction hn using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, j, rfl⟩ := hy
    have h := T.C.mul_mem (T.C.pow_mem T.sC j) (hu x hx)
    convert h using 1
    ring
  | zero =>
    rw [mul_zero]
    exact T.C.zero_mem
  | add y z _ _ hy hz =>
    rw [mul_add]
    exact T.C.add_mem hy hz
  | smul a y _ hy =>
    rw [mul_smul_comm]
    exact T.C.smul_mem hy a

private lemma split (T : TC A D) (X : Finset D) (hXB : ∀ x ∈ X, x ∈ T.B)
    (hX : ∀ b ∈ T.B, b ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x})
    (y : D) : ∃ b ∈ T.B, ∃ n ∈ NN T X, y = b + n := by
  obtain ⟨k, hk⟩ := T.locB y
  have key : ∀ z ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x},
      T.s ^ k * z ∈ Subalgebra.toSubmodule T.B ⊔ NN T X := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, i, rfl⟩ := hw
      rcases le_or_gt k i with hki | hki
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hki
        apply Submodule.mem_sup_left
        have e : T.s ^ k * (T.t ^ (k + d) * x) = T.t ^ d * x := by
          linear_combination (T.t ^ d * x) * tsPow T k
        rw [e]
        exact T.B.mul_mem (T.B.pow_mem T.tB d) (hXB x hx)
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hki
        apply Submodule.mem_sup_right
        have e : T.s ^ (i + d + 1) * (T.t ^ i * x) = T.s ^ (d + 1) * x := by
          linear_combination (T.s ^ (d + 1) * x) * tsPow T i
        rw [e]
        exact Submodule.subset_span ⟨x, hx, d + 1, rfl⟩
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r ha
  have hy := key _ (hX _ hk)
  have e : T.s ^ k * (T.t ^ k * y) = y := by
    linear_combination y * tsPow T k
  rw [e] at hy
  obtain ⟨b, hb, n, hn, hbn⟩ := Submodule.mem_sup.mp hy
  exact ⟨b, hb, n, hn, hbn.symm⟩

private lemma decomp (T : TC A D) (X : Finset D) (hXB : ∀ x ∈ X, x ∈ T.B)
    (hX : ∀ b ∈ T.B, b ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x})
    {ω η : D} (hηω : η * ω = 1) {m : ℕ} (h1 : ω * T.t ^ m ∈ T.B)
    (h3 : ∀ x ∈ X, ω * T.s ^ m * x ∈ T.C) (h4 : ∀ x ∈ X, η * T.s ^ m * x ∈ T.C) (y : D) :
    ∃ b ∈ T.B, ∃ c' ∈ T.C, ∃ p' : D, y = b + c' + p' ∧ ω * T.t ^ m * p' ∈ T.B ∧
      ω * T.s ^ m * p' ∈ T.C := by
  obtain ⟨b₀, hb₀, n₀, hn₀, hz⟩ := split T X hXB hX (ω * T.t ^ m * y)
  obtain ⟨b₂, hb₂, n₂, hn₂, hq⟩ := split T X hXB hX (η * T.s ^ m * b₀)
  have hts := tsPow T m
  refine ⟨b₂, hb₂, η * T.s ^ m * n₀, NN_mul T X h4 hn₀, n₂, ?_, ?_, NN_mul T X h3 hn₂⟩
  · linear_combination hq + η * T.s ^ m * hz - T.t ^ m * T.s ^ m * y * hηω - y * hts
  · have e : ω * T.t ^ m * n₂ = b₀ - ω * T.t ^ m * b₂ := by
      linear_combination (-(ω * T.t ^ m)) * hq + b₀ * T.t ^ m * T.s ^ m * hηω + b₀ * hts
    rw [e]
    exact T.B.sub_mem hb₀ (T.B.mul_mem h1 hb₂)

end UpperTheory.LineDecomposition

open UpperTheory.LineDecomposition in
theorem UpperTheory.exists_power_decomposition_of_root_of_unity :
    ∀ (A D : Type) [CommRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Fin → ∀ (q : ℕ), IsUnit (q : A) → 0 < q → ∀ ω : D, ω ^ q = 1 → ∃ m₀ : ℕ, ∀ m ≥ m₀, ω * T.t ^ m ∈ T.S (2 * m) ∧
      ∀ σ ∈ T.S (2 * q * m), ∃ a ∈ T.S (q * m), ∃ b ∈ T.S (q * m), ∃ c ∈ T.S (2 * m), σ = a + T.t ^ (q * m) * b - (q : D) * (ω * T.t ^ m) ^ (q - 1) * c := by
  classical
  intro A D _ _ _ T hF q hq hq0 ω hω
  obtain ⟨X, hXB, hX⟩ := hF
  have hηω : ω ^ (q - 1) * ω = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hq0, hω]
  obtain ⟨k₁, hk₁⟩ := evB T ω
  obtain ⟨k₂, hk₂⟩ := evC T ω
  obtain ⟨k₃, hk₃⟩ := evCfin T (X.image (fun x => ω * x))
  obtain ⟨k₄, hk₄⟩ := evCfin T (X.image (fun x => ω ^ (q - 1) * x))
  obtain ⟨r, hr⟩ := hq.exists_left_inv
  refine ⟨max (max k₁ k₂) (max k₃ k₄), fun m hm => ?_⟩
  have hm₁ : k₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm₂ : k₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm₃ : k₃ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm₄ : k₄ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have hB : ω * T.t ^ m ∈ T.B := by
    rw [mul_comm]
    exact hk₁ m hm₁
  have hC : ω * T.s ^ m ∈ T.C := by
    rw [mul_comm]
    exact hk₂ m hm₂
  have h3 : ∀ x ∈ X, ω * T.s ^ m * x ∈ T.C := fun x hx => by
    have h := hk₃ m hm₃ (ω * x) (Finset.mem_image_of_mem _ hx)
    convert h using 1
    ring
  have h4 : ∀ x ∈ X, ω ^ (q - 1) * T.s ^ m * x ∈ T.C := fun x hx => by
    have h := hk₄ m hm₄ (ω ^ (q - 1) * x) (Finset.mem_image_of_mem _ hx)
    convert h using 1
    ring
  have hts := tsPow T m
  have hu : ω * T.t ^ m ∈ T.S (2 * m) := by
    rw [memS]
    refine ⟨hB, ?_⟩
    have e : T.s ^ (2 * m) * (ω * T.t ^ m) = ω * T.s ^ m := by
      rw [two_mul, pow_add]
      linear_combination ω * T.s ^ m * hts
    rw [e]
    exact hC
  refine ⟨hu, fun σ hσ => ?_⟩
  rw [memS] at hσ
  obtain ⟨b₁, hb₁, c₁, hc₁, p₁, hy, hp1, hp2⟩ :=
    decomp T X hXB hX hηω hB h3 h4 (T.s ^ (q * m) * σ)
  have hqm := tsPow T (q * m)
  have hupow : (ω * T.t ^ m) ^ q = T.t ^ (q * m) := by
    rw [mul_pow, hω, one_mul, ← pow_mul, Nat.mul_comm]
  have hspow : (ω * T.s ^ m) ^ q = T.s ^ (q * m) := by
    rw [mul_pow, hω, one_mul, ← pow_mul, Nat.mul_comm]
  have hup : (ω * T.t ^ m) ^ (q - 1) * (ω * T.t ^ m * p₁) = T.t ^ (q * m) * p₁ := by
    rw [← mul_assoc, pow_sub_one_mul hq0.ne', hupow]
  have hsp : (ω * T.s ^ m) ^ (q - 1) * (ω * T.s ^ m * p₁) = T.s ^ (q * m) * p₁ := by
    rw [← mul_assoc, pow_sub_one_mul hq0.ne', hspow]
  have ha : T.t ^ (q * m) * c₁ ∈ T.S (q * m) := by
    rw [memS]
    constructor
    · have ea : T.t ^ (q * m) * c₁ =
          σ - T.t ^ (q * m) * b₁ - (ω * T.t ^ m) ^ (q - 1) * (ω * T.t ^ m * p₁) := by
        rw [hup]
        linear_combination (-T.t ^ (q * m)) * hy + σ * hqm
      rw [ea]
      exact T.B.sub_mem (T.B.sub_mem hσ.1 (T.B.mul_mem (T.B.pow_mem T.tB _) hb₁))
        (T.B.mul_mem (T.B.pow_mem hB _) hp1)
    · have ec : T.s ^ (q * m) * (T.t ^ (q * m) * c₁) = c₁ := by
        linear_combination c₁ * hqm
      rw [ec]
      exact hc₁
  have hb : b₁ ∈ T.S (q * m) := by
    rw [memS]
    refine ⟨hb₁, ?_⟩
    have eb : T.s ^ (q * m) * b₁ =
        T.s ^ (2 * q * m) * σ - T.s ^ (q * m) * c₁ - (ω * T.s ^ m) ^ (q - 1) * (ω * T.s ^ m * p₁) := by
      rw [hsp, show 2 * q * m = q * m + q * m by ring, pow_add]
      linear_combination (-T.s ^ (q * m)) * hy
    rw [eb]
    exact T.C.sub_mem (T.C.sub_mem hσ.2 (T.C.mul_mem (T.C.pow_mem T.sC _) hc₁))
      (T.C.mul_mem (T.C.pow_mem hC _) hp2)
  have hpS : ω * T.t ^ m * p₁ ∈ T.S (2 * m) := by
    rw [memS]
    refine ⟨hp1, ?_⟩
    have e : T.s ^ (2 * m) * (ω * T.t ^ m * p₁) = ω * T.s ^ m * p₁ := by
      rw [two_mul, pow_add]
      linear_combination (ω * T.s ^ m * p₁) * hts
    rw [e]
    exact hp2
  refine ⟨T.t ^ (q * m) * c₁, ha, b₁, hb, -(r • (ω * T.t ^ m * p₁)),
    Submodule.neg_mem _ (Submodule.smul_mem _ r hpS), ?_⟩
  have hrq : algebraMap A D r * (q : D) = 1 := by
    rw [← map_natCast (algebraMap A D), ← map_mul, hr, map_one]
  rw [Algebra.smul_def]
  linear_combination (-(q : D) * algebraMap A D r) * hup - T.t ^ (q * m) * p₁ * hrq +
    T.t ^ (q * m) * hy - σ * hqm

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionLiftOfEtaleOfHenselian
section
noncomputable section
open IsLocalRing UpperTheory.Et

theorem UpperTheory.exists_section_lift_of_etale_of_henselian :
    ∀ (A E : Type) [CommRing A] [HenselianLocalRing A] [CommRing E] [Algebra A E] [Algebra.Etale A E] (π : E →ₐ[A] ResidueField A), ∃ σ : E →ₐ[A] A, ∀ x, residue A (σ x) = π x := by
  intro A E _ _ _ _ _ π
  classical
  let Q : Ideal E := RingHom.ker π
  haveI : Q.IsPrime := RingHom.ker_isPrime π
  obtain ⟨f, hfQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  obtain ⟨P⟩ := hstd.nonempty_standardEtalePresentation
  have hunit : ∀ y : Submonoid.powers f, IsUnit (π y) := by
    rintro ⟨_, n, rfl⟩
    simp only [map_pow]
    exact (isUnit_iff_ne_zero.mpr fun h => hfQ (RingHom.mem_ker.mpr h)).pow n
  let πf : Localization.Away f →ₐ[A] ResidueField A := IsLocalization.liftAlgHom (M := Submonoid.powers f) hunit
  let ι : E →ₐ[A] Localization.Away f := IsScalarTower.toAlgHom A E _
  have hπ : ∀ x, πf (ι x) = π x := fun x => by
    simp [πf, ι]
  let τ : P.Ring →ₐ[A] ResidueField A := πf.comp P.equivRing.symm.toAlgHom
  have hx : P.HasMap (τ P.X) := StandardEtalePair.hasMap_X.map τ
  have key : ∀ b : A, residue A b = τ P.X → ∀ p : Polynomial A, residue A (p.eval b) = Polynomial.aeval (τ P.X) p := by
    intro b hb p
    rw [← hb, ← ResidueField.algebraMap_eq, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (τ P.X)
  have h1 : P.f.eval a₀ ∈ maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, key a₀ ha₀]
    exact hx.1
  have h2 : IsUnit (P.f.derivative.eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key a₀ ha₀]
    exact hx.isUnit_derivative_f.ne_zero
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀ h1 h2
  have hra : residue A a = τ P.X := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at ham
    rw [ham, ha₀]
  have hA : P.HasMap a := by
    refine ⟨by rw [Polynomial.coe_aeval_eq_eval]; exact ha, ?_⟩
    rw [Polynomial.coe_aeval_eq_eval, ← IsLocalRing.residue_ne_zero_iff_isUnit, key a hra]
    exact hx.2.ne_zero
  let ρ : A →ₐ[A] ResidueField A := IsScalarTower.toAlgHom A A (ResidueField A)
  have hρ : ρ.comp (P.lift a hA) = τ := by
    apply StandardEtalePair.hom_ext
    simp [ρ, hra, ResidueField.algebraMap_eq]
  refine ⟨(P.lift a hA).comp (P.equivRing.toAlgHom.comp ι), fun x => ?_⟩
  have := congrArg (fun φ => φ (P.equivRing (ι x))) hρ
  simp only [AlgHom.comp_apply, ρ, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq, τ, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe, AlgEquiv.symm_apply_apply] at this
  simpa [hπ] using this

end
end

