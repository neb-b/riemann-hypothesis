module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHomogeneousDehomogenize
section
open MvPolynomial

namespace GlobalTheory

theorem exists_isHomogeneous_dehomogenize : ∀ {D : ℕ} (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ),
    T₀.totalDegree ≤ q → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧
      ∀ (R : Type) [CommRing R] (a : Fin (D + 1) → R), a 0 = 1 →
        aeval a T = aeval (fun j => a j.succ) T₀ := by
  intro D T₀ q hq
  refine ⟨∑ d ∈ Finset.range (q + 1),
    X 0 ^ (q - d) * rename Fin.succ (homogeneousComponent d T₀), ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro d hd
    have hdq : d ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have h := (isHomogeneous_X_pow (R := ℤ) (0 : Fin (D + 1)) (q - d)).mul
      ((homogeneousComponent_isHomogeneous d T₀).rename_isHomogeneous (f := Fin.succ))
    rwa [Nat.sub_add_cancel hdq] at h
  · intro R _ a ha
    have hsum : ∑ d ∈ Finset.range (q + 1), homogeneousComponent d T₀ = T₀ := by
      conv_rhs => rw [← sum_homogeneousComponent T₀]
      symm
      refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hq)) ?_
      intro x _ hx
      apply homogeneousComponent_eq_zero
      simp only [Finset.mem_range] at hx
      omega
    conv_rhs => rw [← hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    intro d _
    simp only [map_mul, map_pow, aeval_X, ha, one_pow, one_mul, aeval_rename]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalHomAdicCompletionExtend
section
open IsLocalRing

namespace GlobalTheory

theorem exists_isLocalHom_adicCompletion_extend (O : Type) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (V : Type) [CommRing V] [IsLocalRing V]
    [IsAdicComplete (maximalIdeal V) V] (ψ : O →+* V) (hψ : IsLocalHom ψ) :
    ∃ ev₀ : AdicCompletion (maximalIdeal O) O →+* V,
      IsLocalHom ev₀ ∧ ∀ a, ev₀ (algebraMap O _ a) = ψ a := by
  have h1 : maximalIdeal O ≤ (maximalIdeal V).comap ψ :=
    (IsLocalRing.maximalIdeal_comap ψ).ge
  have hn : ∀ n : ℕ, maximalIdeal O ^ n ≤ (maximalIdeal V ^ n).comap ψ := fun n =>
    (Ideal.pow_right_mono h1 n).trans (Ideal.le_comap_pow ψ n)
  let f : (n : ℕ) → AdicCompletion (maximalIdeal O) O →+* V ⧸ maximalIdeal V ^ n := fun n =>
    (Ideal.quotientMap _ ψ (hn n)).comp (AdicCompletion.evalₐ (maximalIdeal O) n : _ →+* _)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal V) hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective _ _ x
    simp only [f, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk,
      Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.eq, ← map_sub]
    apply hn m
    have := c.2 hle
    rw [SModEq.sub_mem] at this
    have h2 := neg_mem this
    simpa using h2
  have hev : ∀ a, IsAdicComplete.liftRingHom (maximalIdeal V) f hf (algebraMap O _ a) = ψ a := by
    intro a
    refine congrFun (IsHausdorff.funext' (maximalIdeal V)
      (f := fun a => IsAdicComplete.liftRingHom (maximalIdeal V) f hf (algebraMap O _ a))
      (g := fun a => ψ a) fun n b => ?_) a
    rw [IsAdicComplete.mk_liftRingHom]
    simp only [f, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
    exact Ideal.quotientMap_mk
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal V) f hf, ?_, hev⟩
  apply ((IsLocalRing.local_hom_tfae _).out 1 3).mpr
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.comp_apply, hev]
  exact h1 ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementIsotropicOrthogonalComplex
section
open scoped ComplexOrder

namespace GlobalTheory

open Matrix

theorem levi_element_cpx : ∀ (n a b : ℕ) (J Q : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → Q.PosDef →
    ∀ (X₁ Y₁ : Matrix (Fin n) (Fin a) ℂ) (Xb Yb : Matrix (Fin n) (Fin b) ℂ),
      X₁.conjTranspose * J * X₁ = 0 → X₁.conjTranspose * J * Xb = 0 → Xb.conjTranspose * J * Xb = 0 →
      X₁.conjTranspose * J * Y₁ = 1 → X₁.conjTranspose * J * Yb = 0 → Yb.conjTranspose * J * Yb = 0 →
      Xb.conjTranspose * J * Yb = 1 →
    ∃ (u₂ : GL (Fin n) ℂ) (A : Matrix (Fin a) (Fin b) ℂ), (u₂.1).conjTranspose * J * u₂.1 = J ∧
      u₂.1 * X₁ = X₁ ∧ u₂.1 * Xb = Xb + X₁ * A ∧ u₂.1 * Yb = Yb ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₁.conjTranspose * J) v = 0 →
        Matrix.mulVec u₂.1 v = v + Matrix.mulVec X₁ (Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v))) ∧
      X₁.conjTranspose * Q * (Xb + X₁ * A) = 0 := by
  intro n a b J Q hJ hQ X₁ Y₁ Xb Yb h11 h1b hbb h1Y h1Yb hYbYb hbYb

  have hYb1 : Ybᴴ * J * X₁ = 0 := by
    have := congrArg conjTranspose h1Yb
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hYbb : Ybᴴ * J * Xb = 1 := by
    have := congrArg conjTranspose hbYb
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hY1 : Y₁ᴴ * J * X₁ = 1 := by
    have := congrArg conjTranspose h1Y
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this

  have hinj : Function.Injective X₁.mulVec := by
    intro x y hxy
    have := congrArg (fun w => (Y₁ᴴ * J) *ᵥ w) hxy
    simp only [mulVec_mulVec] at this
    simpa [hY1] using this
  set G := X₁ᴴ * Q * X₁ with hG
  have hGpd : G.PosDef := hQ.conjTranspose_mul_mul_same hinj
  have hGu : IsUnit G := hGpd.isUnit
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGu
  set A : Matrix (Fin a) (Fin b) ℂ := -(G⁻¹ * (X₁ᴴ * Q * Xb)) with hA
  set T : Matrix (Fin n) (Fin n) ℂ := X₁ * A * Ybᴴ * J - Yb * Aᴴ * X₁ᴴ * J with hT
  have hT2 : T * T = 0 := by
    simp only [hT, sub_mul, mul_sub]
    have e1 : X₁ * A * Ybᴴ * J * (X₁ * A * Ybᴴ * J) = X₁ * A * (Ybᴴ * J * X₁) * A * Ybᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e2 : X₁ * A * Ybᴴ * J * (Yb * Aᴴ * X₁ᴴ * J) = X₁ * A * (Ybᴴ * J * Yb) * Aᴴ * X₁ᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e3 : Yb * Aᴴ * X₁ᴴ * J * (X₁ * A * Ybᴴ * J) = Yb * Aᴴ * (X₁ᴴ * J * X₁) * A * Ybᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e4 : Yb * Aᴴ * X₁ᴴ * J * (Yb * Aᴴ * X₁ᴴ * J) = Yb * Aᴴ * (X₁ᴴ * J * Yb) * Aᴴ * X₁ᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e1, e2, e3, e4, hYb1, hYbYb, h11, h1Yb]
    simp
  have hTJ : Tᴴ * J = -(J * T) := by
    simp only [hT, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hJ, sub_mul, mul_sub,
      Matrix.mul_assoc, neg_sub]
  let u : GL (Fin n) ℂ := ⟨1 + T, 1 - T, by
      rw [mul_sub, mul_one, add_mul, one_mul, hT2]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, hT2]; abel⟩
  refine ⟨u, A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (1 + T)ᴴ * J * (1 + T) = J
    rw [conjTranspose_add, conjTranspose_one, add_mul, one_mul, add_mul, mul_add, mul_add, hTJ]
    simp only [mul_one, neg_mul, Matrix.mul_assoc, hT2, mul_zero, neg_zero, add_zero]
    abel
  · show (1 + T) * X₁ = X₁
    have : T * X₁ = 0 := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * X₁ = X₁ * A * (Ybᴴ * J * X₁) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * X₁ = Yb * Aᴴ * (X₁ᴴ * J * X₁) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYb1, h11]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this, add_zero]
  · show (1 + T) * Xb = Xb + X₁ * A
    have : T * Xb = X₁ * A := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * Xb = X₁ * A * (Ybᴴ * J * Xb) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * Xb = Yb * Aᴴ * (X₁ᴴ * J * Xb) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYbb, h1b]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this]
  · show (1 + T) * Yb = Yb
    have : T * Yb = 0 := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * Yb = X₁ * A * (Ybᴴ * J * Yb) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * Yb = Yb * Aᴴ * (X₁ᴴ * J * Yb) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYbYb, h1Yb]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this, add_zero]
  · intro v hv
    show (1 + T) *ᵥ v = v + X₁ *ᵥ (A *ᵥ ((Ybᴴ * J) *ᵥ v))
    rw [add_mulVec, one_mulVec]
    congr 1
    simp only [hT, sub_mulVec]
    have e1 : (X₁ * A * Ybᴴ * J) *ᵥ v = X₁ *ᵥ (A *ᵥ ((Ybᴴ * J) *ᵥ v)) := by
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    have e2 : (Yb * Aᴴ * X₁ᴴ * J) *ᵥ v = (Yb * Aᴴ) *ᵥ ((X₁ᴴ * J) *ᵥ v) := by
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    rw [e1, e2, hv, mulVec_zero, sub_zero]
  · rw [Matrix.mul_add]
    have : X₁ᴴ * Q * (X₁ * A) = G * A := by rw [hG]; simp only [Matrix.mul_assoc]
    rw [this, hA, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hGdet, Matrix.one_mul]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricPointOfFaithfullyFlatFiniteTy
section
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.GeomPointLift

theorem nonempty_algHom_of_isAlgClosed (K C : Type) [Field K] [IsAlgClosed K] [CommRing C] [Nontrivial C]
    [Algebra K C] [Algebra.FiniteType K C] : Nonempty (C →ₐ[K] K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal C
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (C ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (C ⧸ M)
  exact ⟨(IsAlgClosed.lift : (C ⧸ M) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K M)⟩

theorem exists_lift (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (hff : Module.FaithfullyFlat A B)
    (hft : Algebra.FiniteType A B) (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k) :
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := by
  letI : Algebra A k := φ.toAlgebra
  haveI : Nontrivial (k ⊗[A] B) := Module.FaithfullyFlat.rTensor_nontrivial A B k
  haveI : Algebra.FiniteType k (k ⊗[A] B) := inferInstance
  obtain ⟨f⟩ := nonempty_algHom_of_isAlgClosed k (k ⊗[A] B)
  refine ⟨f.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply A k (k ⊗[A] B), AlgHom.commutes]
  rfl

end GlobalTheory.GeomPointLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentAdaptedToDecreasingChainA
section
open Filter Topology

namespace GlobalTheory

theorem exists_linearIndependent_finCons_of_lt {G : Type} [AddCommGroup G] {m k : ℕ}
    (e : Fin m → G) (he : LinearIndependent ℤ e) (f : Fin k → G) (hf : LinearIndependent ℤ f)
    (hmk : m < k) : ∃ j, LinearIndependent ℤ (Fin.cons (f j) e : Fin m.succ → G) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hc : ∀ j, ∃ c : ℤ, c ≠ 0 ∧ c • f j ∈ Submodule.span ℤ (Set.range e) := by
    intro j
    by_contra h
    push_neg at h
    apply hcon j
    refine LinearIndependent.finCons' (f j) e he fun c y hy hxy => ?_
    by_contra hc0
    apply h c hc0
    have : c • f j = -y := eq_neg_of_add_eq_zero_left hxy
    rw [this]
    exact Submodule.neg_mem _ hy
  choose c hc0 hcs using hc
  have hg : LinearIndependent ℤ (fun j => c j • f j) := by
    rw [Fintype.linearIndependent_iff] at hf ⊢
    intro a ha j
    have := hf (fun j => a j * c j) (by simpa [mul_smul] using ha) j
    exact (mul_eq_zero.mp this).resolve_right (hc0 j)
  have hle := linearIndependent_le_span_aux' (fun j => c j • f j) hg (Set.range e)
    (by rintro _ ⟨j, rfl⟩; exact hcs j)
  have h2 : Fintype.card (Set.range e) = m := by
    rw [Set.card_range_of_injective he.injective, Fintype.card_fin]
  rw [h2, Fintype.card_fin] at hle
  omega

theorem exists_linearIndependent_extend_with_levels {G : Type} [AddCommGroup G] (S : ℕ → Set G) {k : ℕ} (f : Fin k → G)
    (hf : LinearIndependent ℤ f) (hfS : ∀ j, f j ∈ S 0) (m : ℕ) (e : Fin m → G) (n : Fin m → ℕ)
    (he : LinearIndependent ℤ e) (heS : ∀ j, e j ∈ S (n j)) :
    ∀ k', m ≤ k' → k' ≤ k → ∃ (e2 : Fin k' → G) (n2 : Fin k' → ℕ), LinearIndependent ℤ e2 ∧
      (∀ j, e2 j ∈ S (n2 j)) ∧ ∑ j, n2 j = ∑ j, n j := by
  intro k' hm
  induction k', hm using Nat.le_induction with
  | base => intro _; exact ⟨e, n, he, heS, rfl⟩
  | succ k' hmk ih =>
    intro hk
    obtain ⟨e2, n2, h1, h2, h3⟩ := ih (by omega)
    obtain ⟨j, hj⟩ := exists_linearIndependent_finCons_of_lt e2 h1 f hf (by omega)
    refine ⟨Fin.cons (f j) e2, Fin.cons 0 n2, hj, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hfS j
      · simpa using h2 i
    · rw [Fin.sum_cons, zero_add, h3]

theorem exists_linearIndependent_adapted_to_decreasing_chain : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G]
    (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ),
    (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) →
    (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ),
      LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧
      ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  intro G _ _ S hS N
  induction N generalizing S with
  | zero =>
    intro r hr _
    obtain ⟨e, he, heS⟩ := hr 0
    exact ⟨e, fun _ => 0, he, heS, by simp⟩
  | succ N ih =>
    intro r hr hrd
    obtain ⟨e', n', he', heS', hsum⟩ := ih (fun i => S (i + 1)) (fun i => hS (i + 1))
      (fun i => r (i + 1)) (fun i => hr (i + 1)) (fun i => hrd (i + 1))
    obtain ⟨f, hf, hfS⟩ := hr 0
    obtain ⟨e, n, he, heS, hn⟩ := exists_linearIndependent_extend_with_levels S f hf hfS (r (0 + 1)) e' (fun j => n' j + 1) he'
      heS' (r 0) (hrd 0) le_rfl
    refine ⟨e, n, he, heS, ?_⟩
    rw [Finset.sum_range_succ']
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hsum hn ⊢
    omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentIteratesOfLinearIndepende
section
open scoped Matrix
open Polynomial

namespace GlobalTheory.CyclicVector

theorem exists_linearIndependent_iterates_of_linearIndependent_pow {K : Type} [Field K] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) K)
    (hg : LinearIndependent K (fun i : Fin r => g ^ (i : ℕ))) :
    ∃ v : Fin r → K, LinearIndependent K (fun i : Fin r => (g ^ (i : ℕ)) *ᵥ v) := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval' (Matrix.toLin' g))
  set v := (Module.AEval'.of (Matrix.toLin' g)).symm x with hv
  refine ⟨v, ?_⟩
  rw [Fintype.linearIndependent_iff] at hg ⊢
  intro c hc
  let q : K[X] := ∑ j : Fin r, monomial (j : ℕ) (c j)
  have haq : aeval g q = ∑ j : Fin r, c j • g ^ (j : ℕ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [q, map_sum, aeval_monomial, Algebra.smul_def]
  have ha : ∀ p : K[X], aeval (Matrix.toLin' g) p = Matrix.toLin' (aeval g p) := fun p =>
    (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin r)) g p)
  have hqv : aeval g q *ᵥ v = 0 := by
    rw [haq, Matrix.sum_mulVec]
    have hs : ∀ j : Fin r, (c j • g ^ (j : ℕ)) *ᵥ v = c j • (g ^ (j : ℕ) *ᵥ v) := fun j => by
      ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    simpa [hs] using hc
  have hmem : q ∈ Module.annihilator K[X] (Module.AEval' (Matrix.toLin' g)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    apply (Module.AEval'.of (Matrix.toLin' g)).symm.injective
    rw [Module.AEval.of_symm_smul, map_zero, ha]
    exact hqv
  have hq : aeval g q = 0 := by
    apply Matrix.toLin'.injective
    rw [map_zero, ← ha]
    refine LinearMap.ext fun u => ?_
    have := Module.mem_annihilator.1 hmem (Module.AEval'.of (Matrix.toLin' g) u)
    have h2 := congrArg (Module.AEval'.of (Matrix.toLin' g)).symm this
    rw [Module.AEval.of_symm_smul, map_zero] at h2
    simpa using h2
  exact hg c (haq ▸ hq)

end GlobalTheory.CyclicVector
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtend
section
set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace GlobalTheory.LocalCompletion

theorem exists_localHom_adicCompletion_extend :
    ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R],
      IsAdicComplete (maximalIdeal R) R → ∀ (φ : A →+* R), IsLocalHom φ →
      ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R,
        IsLocalHom ψ ∧ ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  intro A R _ _ _ _ _ hR φ hφ
  let I : Ideal A := maximalIdeal A
  let J : Ideal R := maximalIdeal R
  have hmap : I.map φ ≤ J := ((IsLocalRing.local_hom_tfae φ).out 1 3).1 hφ
  have hle : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap φ := fun n => by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hmap n
  let g : ∀ n : ℕ, AdicCompletion I A →+* R ⧸ J ^ n := fun n =>
    (Ideal.quotientMap (J ^ n) φ (hle n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)
  have hg : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (g n) = g m := by
    intro m n h
    refine RingHom.ext fun x => ?_
    obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I A x
    simp only [g, RingHom.comp_apply, RingHom.coe_coe]
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, ← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl
  let e : R ≃ₐ[R] AdicCompletion J R := AdicCompletion.ofAlgEquiv J
  let ψ : AdicCompletion I A →+* R := (e.symm : AdicCompletion J R →+* R).comp (AdicCompletion.liftRingHom J g hg)
  have hψ : ψ.comp (algebraMap A (AdicCompletion I A)) = φ := by
    refine RingHom.ext fun b => e.injective ?_
    refine AdicCompletion.ext_evalₐ fun n => ?_
    simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.apply_symm_apply]
    rw [AdicCompletion.evalₐ_liftRingHom]
    change Ideal.quotientMap (J ^ n) φ (hle n) (AdicCompletion.evalₐ I n (algebraMap A _ b)) = _
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    rw [show e (φ b) = algebraMap R (AdicCompletion J R) (φ b) from e.commutes (φ b),
      AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    rfl
  refine ⟨ψ, ?_, hψ⟩
  refine ((IsLocalRing.local_hom_tfae ψ).out 1 3).2 ?_
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hψ]
  exact hmap

end GlobalTheory.LocalCompletion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLower
section
namespace GlobalTheory.LowerTriangularEntryBound

theorem exists_lower {n : ℕ} (f : (Fin n → ℂ) → ℝ) (hc : Continuous f)
    (hh : ∀ (t : ℝ) (x : Fin n → ℂ), f (t • x) = t ^ (2 : ℕ) * f x)
    (hp : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < f x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℂ, c * ‖x‖ ^ 2 ≤ f x := by
  have hf0 : f 0 = 0 := by simpa using hh 0 0
  have hscale : ∀ x : Fin n → ℂ, x ≠ 0 → f x = ‖x‖ ^ 2 * f (‖x‖⁻¹ • x) := by
    intro x hx
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hx' : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    conv_lhs => rw [hx']
    exact hh _ _
  have hunit : ∀ x : Fin n → ℂ, x ≠ 0 → ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  by_cases hS : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_isMinOn hS hc.continuousOn
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    refine ⟨f u, hp u hu0, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp [hf0]
    · have hle : f u ≤ f (‖x‖⁻¹ • x) := isMinOn_iff.mp hmin _ (hunit x hx)
      rw [hscale x hx]
      calc f u * ‖x‖ ^ 2 ≤ f (‖x‖⁻¹ • x) * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = ‖x‖ ^ 2 * f (‖x‖⁻¹ • x) := mul_comm _ _
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp [hf0]
    · exact absurd ⟨_, hunit x hx⟩ hS

theorem entry_bound {n : ℕ} (f : (Fin n → ℂ) → ℝ) (hc : Continuous f)
    (hh : ∀ (t : ℝ) (x : Fin n → ℂ), f (t • x) = t ^ (2 : ℕ) * f x)
    (hp : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < f x) :
    ∃ K : ℝ, ∀ (A : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 ≤ s →
      (∀ x : Fin n → ℂ, f (Matrix.mulVec A x) = s * f x) →
      ∀ a b : Fin n, ‖A a b‖ ≤ K * √s := by
  obtain ⟨c, hc0, hlow⟩ := exists_lower f hc hh hp
  set C : ℝ := ∑ j : Fin n, |f (Pi.single j (1 : ℂ))| with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨√(C / c), fun A s hs hA a b => ?_⟩
  have hfb : f (Pi.single b (1 : ℂ)) ≤ C :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j : Fin n => |f (Pi.single j (1 : ℂ))|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ b))
  have hcol : (Matrix.mulVec A (Pi.single b (1 : ℂ))) a = A a b := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h2 : ‖A a b‖ ≤ ‖Matrix.mulVec A (Pi.single b (1 : ℂ))‖ := by
    rw [← hcol]
    exact norm_le_pi_norm _ a
  have h2' : ‖A a b‖ ^ 2 ≤ ‖Matrix.mulVec A (Pi.single b (1 : ℂ))‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h3 : c * ‖Matrix.mulVec A (Pi.single b (1 : ℂ))‖ ^ 2 ≤ s * C :=
    calc c * ‖Matrix.mulVec A (Pi.single b (1 : ℂ))‖ ^ 2 ≤ f (Matrix.mulVec A (Pi.single b (1 : ℂ))) := hlow _
      _ = s * f (Pi.single b (1 : ℂ)) := hA _
      _ ≤ s * C := mul_le_mul_of_nonneg_left hfb hs
  have h4 : ‖A a b‖ ^ 2 ≤ C / c * s := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    nlinarith [mul_le_mul_of_nonneg_left h2' hc0.le, h3]
  calc ‖A a b‖ = √(‖A a b‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(C / c * s) := Real.sqrt_le_sqrt h4
    _ = √(C / c) * √s := Real.sqrt_mul (div_nonneg hC hc0.le) s

end GlobalTheory.LowerTriangularEntryBound
end

