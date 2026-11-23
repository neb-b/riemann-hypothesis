module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatricesIntertwiningOfSemilinear
section
open Matrix

namespace GlobalTheory

theorem exists_matrices_intertwining_of_semilinear : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l) (I M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∃ (n : ℕ) (σ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (e : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] V), (∀ p, σ p = 0 → ∀ x : M, p • x = 0) ∧ Function.Injective e ∧ (∀ c, e c ∈ Submodule.span (PadicAlgCl l) (Set.range j)) ∧ ∀ i c, Tq i (e c) = e ((σ (MvPolynomial.X i)).map emb *ᵥ c) := by
  intro l _ O _ _ _ emb I M _ _ _ _ hfin htf V _ _ j Tq hli hX
  have : NoZeroSMulDivisors O M := ⟨fun {c x} h => htf c x h⟩
  have : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let n := Module.finrank O M
  let b : Module.Basis (Fin n) O M := Module.finBasis O M
  let σ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lsmul O O M)
  let e : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] V :=
    ∑ a, (LinearMap.proj a : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] PadicAlgCl l).smulRight (j (b a))
  have he : ∀ c, e c = ∑ a, c a • j (b a) := by
    intro c
    simp [e, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hσ : ∀ p a, p • b a = ∑ k, σ p k a • b k := by
    intro p a
    conv_lhs => rw [← b.sum_repr (p • b a)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp [σ, LinearMap.toMatrixAlgEquiv_apply]
  refine ⟨n, σ, e, ?_, ?_, ?_, ?_⟩
  · intro p hp x
    have h1 : (Algebra.lsmul O O M) p = 0 := by
      apply (LinearMap.toMatrixAlgEquiv b).injective
      simpa [σ] using hp
    simpa using LinearMap.congr_fun h1 x
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hl := Fintype.linearIndependent_iff.mp (hli n b b.linearIndependent) c (by rw [← he]; exact hc)
    funext a
    exact hl a
  · intro c
    rw [he]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b a, rfl⟩)
  · intro i c
    have key : ∀ a, Tq i (j (b a)) = ∑ k, emb (σ (MvPolynomial.X i) k a) • j (b k) := by
      intro a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hX, hσ, map_sum]
      simp [LinearMap.map_smulₛₗ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he, he, map_sum]
    simp_rw [LinearMap.map_smul, key, Finset.smul_sum, smul_smul]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixRangeEq
section
namespace GlobalTheory.MatrixRangeExistence

theorem exists_matrix_range_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n : ℕ) (ϖ : O) (N : Submodule O (Fin n → O)) (hϖ : ϖ ≠ 0)
    (hN : ∀ y : Fin n → O, (fun a : Fin n => ϖ * y a) ∈ N) :
    ∃ A : Matrix (Fin n) (Fin n) O,
      (∀ x : Fin n → O, x ∈ N ↔ ∃ u : Fin n → O, Matrix.mulVec A u = x) ∧ Matrix.det A ≠ 0 := by
  classical
  let f : (Fin n → O) →ₗ[O] N :=
    LinearMap.codRestrict N (ϖ • LinearMap.id) (fun y => hN y)
  have hf : Function.Injective f := by
    intro y z h
    have h' : ϖ • y = ϖ • z := congrArg Subtype.val h
    funext a
    exact mul_left_cancel₀ hϖ (congrFun h' a)
  have h1 : n ≤ Module.finrank O N := by
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
  have h2 : Module.finrank O N ≤ n := by
    have := Submodule.finrank_le N
    simpa using this
  let b : Module.Basis (Fin n) O N := Module.finBasisOfFinrankEq O N (le_antisymm h2 h1)
  let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => (b j : Fin n → O) i
  have hA : ∀ u : Fin n → O, Matrix.mulVec A u = ((∑ j, u j • b j : N) : Fin n → O) := by
    intro u
    funext i
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have key : ∀ x : Fin n → O, x ∈ N ↔ ∃ u : Fin n → O, Matrix.mulVec A u = x := by
    intro x
    constructor
    · intro hx
      refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_⟩
      rw [hA, b.sum_repr ⟨x, hx⟩]
    · rintro ⟨u, rfl⟩
      rw [hA]
      exact Subtype.property _
  refine ⟨A, key, ?_⟩
  have hcol : ∀ j : Fin n, ∃ u : Fin n → O,
      Matrix.mulVec A u = fun a => ϖ * (Pi.single j (1 : O) : Fin n → O) a :=
    fun j => (key _).1 (hN _)
  choose U hU using hcol
  have hmul : A * (Matrix.of fun i j => U j i) = ϖ • (1 : Matrix (Fin n) (Fin n) O) := by
    ext i j
    have := congrFun (hU j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp [Matrix.mul_apply, this, Matrix.one_apply, Pi.single_apply]
  intro h0
  have := congrArg Matrix.det hmul
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hϖ this.symm

end GlobalTheory.MatrixRangeExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixSqrtNearOneUltrametric
section
open Matrix Filter Topology

namespace GlobalTheory.MatSqrtNearOne

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] {n : ℕ}

theorem norm_mul_le_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_apply_le_norm A) (norm_apply_le_norm B)
    (norm_nonneg _) (norm_nonneg _)

theorem norm_add_le_max_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A + B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [Matrix.norm_le_iff (le_max_of_le_left (norm_nonneg _))]
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (norm_apply_le_norm A) (norm_apply_le_norm B))

theorem norm_sub_le_max_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A - B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [sub_eq_add_neg, ← norm_neg B]
  exact norm_add_le_max_ultra A (-B)

noncomputable def iter (u : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => 0
  | k + 1 => u - iter u k * iter u k

theorem commute_iter {u a : Matrix (Fin n) (Fin n) K} (h : Commute a u) :
    ∀ k, Commute a (iter u k)
  | 0 => Commute.zero_right a
  | k + 1 => h.sub_right ((commute_iter h k).mul_right (commute_iter h k))

theorem norm_iter_le {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) : ∀ k, ‖iter u k‖ ≤ ‖u‖ := by
  intro k
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [iter]
    refine (norm_sub_le_max_ultra _ _).trans (max_le le_rfl ?_)
    calc ‖iter u k * iter u k‖ ≤ ‖iter u k‖ * ‖iter u k‖ := norm_mul_le_ultra _ _
      _ ≤ ‖u‖ * 1 := mul_le_mul ih (ih.trans hc.le) (norm_nonneg _) (norm_nonneg _)
      _ = ‖u‖ := mul_one _

theorem matrix_sub_mul_self_sub_eq_neg_mul_of_commute (u a b : Matrix (Fin n) (Fin n) K) (h : Commute a b) :
    (u - b * b) - (u - a * a) = -((b - a) * (a + b)) := by
  rw [sub_mul, mul_add, mul_add, ← h.eq]
  abel

theorem norm_iter_diff_le {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) :
    ∀ k, ‖iter u (k + 1) - iter u k‖ ≤ ‖u‖ * ‖u‖ ^ k := by
  intro k
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    have hcomm : Commute (iter u k) (iter u (k + 1)) :=
      commute_iter (commute_iter (Commute.refl u) k).symm (k + 1)
    have hstep : iter u (k + 1 + 1) - iter u (k + 1) =
        (u - iter u (k + 1) * iter u (k + 1)) - (u - iter u k * iter u k) :=
      congrArg₂ (· - ·) (iter.eq_2 u (k + 1)) (iter.eq_2 u k)
    rw [hstep, matrix_sub_mul_self_sub_eq_neg_mul_of_commute u _ _ hcomm, norm_neg]
    have hab : ‖iter u k + iter u (k + 1)‖ ≤ ‖u‖ :=
      (norm_add_le_max_ultra _ _).trans (max_le (norm_iter_le hc k) (norm_iter_le hc (k + 1)))
    calc ‖(iter u (k + 1) - iter u k) * (iter u k + iter u (k + 1))‖
        ≤ ‖iter u (k + 1) - iter u k‖ * ‖iter u k + iter u (k + 1)‖ := norm_mul_le_ultra _ _
      _ ≤ (‖u‖ * ‖u‖ ^ k) * ‖u‖ :=
          mul_le_mul ih hab (norm_nonneg _) (by positivity)
      _ = ‖u‖ * ‖u‖ ^ (k + 1) := by ring

theorem tau_add (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A + B).map σ)ᵀ = (A.map σ)ᵀ + (B.map σ)ᵀ := by
  ext i j; simp

theorem tau_sub (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A - B).map σ)ᵀ = (A.map σ)ᵀ - (B.map σ)ᵀ := by
  ext i j; simp

theorem tau_mul (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := by
  rw [Matrix.map_mul, transpose_mul]

theorem tau_one (σ : K →+* K) : ((1 : Matrix (Fin n) (Fin n) K).map σ)ᵀ = 1 := by
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one]

theorem tau_smul (σ : K →+* K) (c : K) (A : Matrix (Fin n) (Fin n) K) :
    ((c • A).map σ)ᵀ = σ c • (A.map σ)ᵀ := by
  ext i j; simp

theorem exists_sqrt [CompleteSpace K] [CharZero K] (σ : K →+* K) (hσ : Continuous σ)
    (s : Matrix (Fin n) (Fin n) K)
    (hs : ∀ i j, ‖s i j - (1 : Matrix (Fin n) (Fin n) K) i j‖ < ‖(4 : K)‖) :
    ∃ r : Matrix (Fin n) (Fin n) K, r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K,
      a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  have h4 : (4 : K) ≠ 0 := by norm_num
  have h4p : 0 < ‖(4 : K)‖ := norm_pos_iff.2 h4
  set u : Matrix (Fin n) (Fin n) K := (4 : K)⁻¹ • (s - 1) with hu
  have hs1 : ‖s - 1‖ < ‖(4 : K)‖ := (Matrix.norm_lt_iff h4p).2 fun i j => by simpa using hs i j
  have hc : ‖u‖ < 1 := by
    rw [hu, norm_smul, norm_inv, inv_mul_lt_iff₀ h4p, mul_one]
    exact hs1
  have hcs : CauchySeq (iter u) := cauchySeq_of_le_geometric ‖u‖ ‖u‖ hc fun k => by
    rw [dist_eq_norm, norm_sub_rev]; exact norm_iter_diff_le hc k
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcs
  have hfix : y + y * y = u := by
    have h1 : Tendsto (fun k => iter u (k + 1)) atTop (𝓝 y) := hy.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k => iter u (k + 1)) atTop (𝓝 (u - y * y)) :=
      tendsto_const_nhds.sub (hy.mul hy)
    exact eq_sub_iff_add_eq.1 (tendsto_nhds_unique h1 h2)
  refine ⟨1 + (2 : K) • y, ?_, ?_, ?_⟩
  · calc (1 + (2 : K) • y) * (1 + (2 : K) • y) = 1 + (4 : K) • (y + y * y) := by
          rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm]
          module
      _ = s := by rw [hfix, hu, smul_inv_smul₀ h4]; abel
  · intro a ha
    have hau : Commute a u := ((Commute.sub_right ha (Commute.one_right a))).smul_right _
    have hay : a * y = y * a :=
      tendsto_nhds_unique (hy.const_mul a)
        ((hy.mul_const a).congr fun k => (commute_iter hau k).eq.symm)
    exact ((Commute.one_right a).add_right ((show Commute a y from hay).smul_right (2 : K))).eq
  · intro hsσ
    have hτu : (u.map σ)ᵀ = u := by
      rw [hu, tau_smul, tau_sub, tau_one, hsσ, map_inv₀, map_ofNat]
    have hτiter : ∀ k, ((iter u k).map σ)ᵀ = iter u k := by
      intro k
      induction k with
      | zero => ext i j; simp [iter]
      | succ k ih =>
        show ((u - iter u k * iter u k).map σ)ᵀ = u - iter u k * iter u k
        rw [tau_sub, tau_mul, ih, hτu]
    have hτc : Continuous fun M : Matrix (Fin n) (Fin n) K => (M.map σ)ᵀ :=
      (continuous_id.matrix_map hσ).matrix_transpose
    have hτy : (y.map σ)ᵀ = y :=
      tendsto_nhds_unique ((hτc.tendsto y).comp hy) (hy.congr fun k => (hτiter k).symm)
    rw [tau_add, tau_one, tau_smul, hτy, map_ofNat]

end GlobalTheory.MatSqrtNearOne

namespace GlobalTheory

theorem matrix_sqrt_near_one_ultrametric :
    ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] (n : ℕ) (σ : K →+* K), Continuous σ →
      ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) K), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) K,
        r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K, a * s = s * a → a * r = r * a) ∧
        ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  intro K _ _ _ _ n σ hσ
  have h4 : (4 : K) ≠ 0 := by norm_num
  refine ⟨{s | ∀ i j, ‖s i j - (1 : Matrix (Fin n) (Fin n) K) i j‖ < ‖(4 : K)‖}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ (by simp [h4])
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((continuous_id.matrix_elem i j).sub continuous_const).norm continuous_const
  · intro s hs
    exact MatSqrtNearOne.exists_sqrt σ hσ s hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalPrimeCharNotMemFiniteTypeInt
section
namespace GlobalTheory

theorem isJacobsonRing_integers : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_bot]
    by_contra h0
    have h1 := Ideal.mem_jacobson_bot.1 hx x
    have h2 : 0 < x * x := mul_self_pos.2 h0
    rcases Int.isUnit_iff.1 h1 with h3 | h3 <;> omega
  · have := Ring.DimensionLEOne.maximalOfPrime h hP
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem closedPt_of_finiteType_int : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by
  intro R _ _ _ f hf
  haveI := isJacobsonRing_integers
  let S := Localization.Away f
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  haveI : Nontrivial S := hinj.nontrivial
  haveI : Algebra.FiniteType R S := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) S
  haveI : Algebra.FiniteType ℤ S := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  obtain ⟨n, hn⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ n) := Ideal.Quotient.field n
  haveI : Algebra.FiniteType ℤ (S ⧸ n) := inferInstance
  haveI hfin := finite_of_finite_type_of_isJacobsonRing ℤ (S ⧸ n)
  have hZ : (algebraMap ℤ (S ⧸ n)).IsIntegral := fun x => IsIntegral.of_finite ℤ x
  let ψ : R →+* S ⧸ n := (Ideal.Quotient.mk n).comp (algebraMap R S)
  have hcomp : ψ.comp (Int.castRingHom R) = algebraMap ℤ (S ⧸ n) := RingHom.ext_int _ _
  have hψ : ψ.IsIntegral := RingHom.IsIntegral.tower_top (Int.castRingHom R) ψ (hcomp ▸ hZ)
  haveI hbot : (⊥ : Ideal (S ⧸ n)).IsMaximal := Ideal.bot_isMaximal
  let M : Ideal R := (⊥ : Ideal (S ⧸ n)).comap ψ
  have hM : M.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ψ hψ ⊥
  refine ⟨M, hM, ?_, ?_⟩
  · intro hfM
    have h0 : ψ f = 0 := by simpa [M] using hfM
    have hu : IsUnit (algebraMap R S f) := IsLocalization.Away.algebraMap_isUnit f
    have hu' : IsUnit (ψ f) := hu.map (Ideal.Quotient.mk n)
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  · have hMZ : (M.comap (Int.castRingHom R)).IsMaximal := by
      have : M.comap (Int.castRingHom R) = (⊥ : Ideal (S ⧸ n)).comap (algebraMap ℤ (S ⧸ n)) := by
        rw [← hcomp, ← Ideal.comap_comap]
      rw [this]
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hZ ⊥
    obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (M.comap (Int.castRingHom R))
    change _ = Ideal.span {a} at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at ha
      exact Ring.ne_bot_of_isMaximal_of_not_isField hMZ Int.not_isField ha
    have hpr : Prime a := by
      rw [← Ideal.span_singleton_prime ha0, ← ha]
      exact hMZ.isPrime
    refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.1 hpr, ?_⟩
    have hmem : (a.natAbs : ℤ) ∈ M.comap (Int.castRingHom R) := by
      rw [ha, Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    have h2 := Ideal.mem_comap.1 hmem
    simpa only [eq_intCast, Int.cast_natCast] using h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalSubfieldMissingElemExpOne
section
open TensorProduct

namespace GlobalTheory

open Polynomial

theorem cfmax_finrank (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p]
    (L : Subfield K) (z : K) (hz : z ∉ L) (hzp : z ^ p ∈ L) :
    IsIntegral L z ∧ Module.finrank L (IntermediateField.adjoin L ({z} : Set K)) = p := by
  have hirr : Irreducible (X ^ p - C (⟨z ^ p, hzp⟩ : L)) := by
    apply X_pow_sub_C_irreducible_of_prime hp.out
    intro b hb
    apply hz
    have hb' : (b : K) ^ p = z ^ p := by
      have := congrArg (fun t : L => (t : K)) hb
      simpa using this
    have h0 : ((b : K) - z) ^ p = 0 := by
      rw [sub_pow_char, hb', sub_self]
    have : (b : K) = z := sub_eq_zero.mp ((pow_eq_zero_iff hp.out.ne_zero).mp h0)
    rw [← this]; exact b.2
  have hmonic : (X ^ p - C (⟨z ^ p, hzp⟩ : L)).Monic := monic_X_pow_sub_C _ hp.out.ne_zero
  have haeval : aeval z (X ^ p - C (⟨z ^ p, hzp⟩ : L)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    exact sub_self _
  have hint : IsIntegral L z := ⟨_, hmonic, by rw [← aeval_def]; exact haeval⟩
  refine ⟨hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, ← minpoly.eq_of_irreducible_of_monic hirr haeval hmonic,
    natDegree_X_pow_sub_C _]

theorem cfmax_main : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (F : Subfield K), (∀ y : K, y ^ p ∈ F) → ∀ f : K, f ∉ F → ∃ L : Subfield K, F ≤ L ∧ f ∉ L ∧ IntermediateField.adjoin L ({f} : Set K) = ⊤ := by
  intro p _ K _ _ F hF f hf
  have hch : ∀ c ⊆ {L : Subfield K | F ≤ L ∧ f ∉ L}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {L : Subfield K | F ≤ L ∧ f ∉ L}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    refine ⟨sSup c, ⟨(hc hy).1.trans (le_sSup hy), ?_⟩, fun z hz => le_sSup hz⟩
    rw [Subfield.mem_sSup_of_directedOn ⟨y, hy⟩ hchain.directedOn]
    rintro ⟨s, hs, hfs⟩
    exact (hc hs).2 hfs
  obtain ⟨L, -, hmax⟩ := zorn_le_nonempty₀ {L : Subfield K | F ≤ L ∧ f ∉ L} hch F ⟨le_rfl, hf⟩
  refine ⟨L, hmax.prop.1, hmax.prop.2, ?_⟩
  have hpow : ∀ y : K, y ^ p ∈ L := fun y => hmax.prop.1 (hF y)
  rw [eq_top_iff]
  intro y _
  by_cases hy : y ∈ L
  · exact IntermediateField.algebraMap_mem _ (⟨y, hy⟩ : L)
  · obtain ⟨hiy, hdy⟩ := cfmax_finrank p K L y hy (hpow y)
    obtain ⟨_, hdf⟩ := cfmax_finrank p K L f hmax.prop.2 (hpow f)
    have hfy : f ∈ IntermediateField.adjoin L ({y} : Set K) := by
      by_contra hfy
      have hLM : L ≤ (IntermediateField.adjoin L ({y} : Set K)).toSubfield := fun x hx =>
        (IntermediateField.adjoin L ({y} : Set K)).algebraMap_mem (⟨x, hx⟩ : L)
      have hM : (IntermediateField.adjoin L ({y} : Set K)).toSubfield ∈
          {L : Subfield K | F ≤ L ∧ f ∉ L} := ⟨hmax.prop.1.trans hLM, hfy⟩
      exact hy (hmax.le_of_ge hM hLM (IntermediateField.mem_adjoin_simple_self L y))
    have hle : IntermediateField.adjoin L ({f} : Set K) ≤ IntermediateField.adjoin L ({y} : Set K) :=
      IntermediateField.adjoin_simple_le_iff.mpr hfy
    haveI : FiniteDimensional L (IntermediateField.adjoin L ({y} : Set K)) :=
      IntermediateField.adjoin.finiteDimensional hiy
    have heq := IntermediateField.eq_of_le_of_finrank_eq hle (hdf.trans hdy.symm)
    rw [heq]
    exact IntermediateField.mem_adjoin_simple_self L y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMulEqOfTraceEq
section
namespace GlobalTheory.TraceEqualFinrank

open Module

theorem trace_eq_finrank_range {g : ℕ} (P : Matrix (Fin g) (Fin g) ℂ) (hP : IsIdempotentElem P) :
    Matrix.trace P = (finrank ℂ (LinearMap.range (Matrix.toLin' P)) : ℂ) := by
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP.eq]
  have hproj := (LinearMap.isProj_range_iff_isIdempotentElem (Matrix.toLin' P)).mpr he
  rw [← Matrix.trace_toLin'_eq, hproj.trace]

theorem exists_mul_mul_eq_of_trace_eq {g : ℕ} (P P' : Matrix (Fin g) (Fin g) ℂ)
    (hP : IsIdempotentElem P) (hP' : IsIdempotentElem P')
    (h : Matrix.trace P = Matrix.trace P') :
    ∃ (X : Matrix (Fin g) (Fin g) ℂ) (Y : Matrix (Fin g) (Fin g) ℂ), Y * P' * X = P := by
  have hrk : finrank ℂ (LinearMap.range (Matrix.toLin' P')) =
      finrank ℂ (LinearMap.range (Matrix.toLin' P)) := by
    have h2 := (trace_eq_finrank_range P' hP').symm.trans (h.symm.trans (trace_eq_finrank_range P hP))
    exact_mod_cast h2
  let e := LinearEquiv.ofFinrankEq _ _ hrk
  have hid' : ∀ w ∈ LinearMap.range (Matrix.toLin' P'), Matrix.toLin' P' w = w := by
    rintro w ⟨u, rfl⟩
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hP'.eq]
  let Xl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (LinearMap.range (Matrix.toLin' P')).subtype ∘ₗ
    e.symm.toLinearMap ∘ₗ (Matrix.toLin' P).rangeRestrict
  let Yl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (LinearMap.range (Matrix.toLin' P)).subtype ∘ₗ
    e.toLinearMap ∘ₗ (Matrix.toLin' P').rangeRestrict
  refine ⟨LinearMap.toMatrix' Xl, LinearMap.toMatrix' Yl, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  have hw := (e.symm ((Matrix.toLin' P).rangeRestrict v)).2
  have h1 : (Matrix.toLin' P').rangeRestrict
      (Matrix.toLin' P' ((e.symm ((Matrix.toLin' P).rangeRestrict v) : Fin g → ℂ))) =
      e.symm ((Matrix.toLin' P).rangeRestrict v) := by
    apply Subtype.ext
    change Matrix.toLin' P' (Matrix.toLin' P' _) = _
    rw [hid' _ hw, hid' _ hw]
  change ((e ((Matrix.toLin' P').rangeRestrict
      (Matrix.toLin' P' ((e.symm ((Matrix.toLin' P).rangeRestrict v) : Fin g → ℂ)))) :
      LinearMap.range (Matrix.toLin' P)) : Fin g → ℂ) = Matrix.toLin' P v
  rw [h1, LinearEquiv.apply_symm_apply]
  rfl

end GlobalTheory.TraceEqualFinrank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstAndFinite
section
namespace GlobalTheory.EtC

def firstAndFinite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A) :
    Subalgebra R (PiTensorProduct R (fun _ : Fin (k + 1) => A)) :=
  Algebra.adjoin R (Set.range (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) 0) ∪
    ⋃ i : Fin (k + 1), (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) i) '' (F : Set A))

def firstIncl (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A) :
    A →ₐ[R] firstAndFinite R A k F :=
  (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) 0).codRestrict _
    (fun a => Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩))

end GlobalTheory.EtC
end

