module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointInjectiveSurjectiveAndPositiveScalar
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem adjoint_injective_surjective_and_positive_scalar :
    ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (A : E →ₗ[ℂ] F),
      (Function.Injective (LinearMap.adjoint A) → Function.Surjective A) ∧
      (∀ (U : Submodule ℂ F) (l : ℂ), l ≠ 0 →
        (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = l * ⟪x, y⟫_ℂ) →
        ∃ l' : ℝ, 0 < l' ∧
          (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = (l' : ℂ) * ⟪x, y⟫_ℂ) ∧
          ∀ x ∈ U, A (LinearMap.adjoint A x) = (l' : ℂ) • x) := by
  intro E F _ _ _ _ _ _ A
  constructor
  · intro hinj
    have hbot : (LinearMap.range A)ᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      have h0 : LinearMap.adjoint A v = 0 := by
        apply ext_inner_right ℂ
        intro e
        rw [LinearMap.adjoint_inner_left, inner_zero_left]
        exact (Submodule.mem_orthogonal' _ _).mp hv (A e) ⟨e, rfl⟩
      exact hinj (h0.trans (map_zero _).symm)
    have htop : LinearMap.range A = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
    exact LinearMap.range_eq_top.mp htop
  · intro U l hl h
    have key : ∀ l' : ℝ, 0 < l' → l = (l' : ℂ) →
        ∃ l' : ℝ, 0 < l' ∧
          (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = (l' : ℂ) * ⟪x, y⟫_ℂ) ∧
          ∀ x ∈ U, A (LinearMap.adjoint A x) = (l' : ℂ) • x := by
      intro l' hpos hl'
      subst hl'
      refine ⟨l', hpos, h, ?_⟩
      intro x hx
      apply ext_inner_right ℂ
      intro v
      rw [← LinearMap.adjoint_inner_right, h x hx v, inner_smul_left, Complex.conj_ofReal]
    by_cases hU : U = ⊥
    · refine ⟨1, one_pos, ?_, ?_⟩
      · intro x hx y
        rw [hU, Submodule.mem_bot] at hx
        subst hx
        simp
      · intro x hx
        rw [hU, Submodule.mem_bot] at hx
        subst hx
        simp
    · obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      have hxx := h x hxU x
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hxx
      have hn : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
      have hlval : l = ((‖LinearMap.adjoint A x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ) := by
        have hne : ((‖x‖ : ℂ)) ^ 2 ≠ 0 := by
          have : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx0)
          exact pow_ne_zero _ this
        push_cast
        rw [eq_div_iff hne]
        exact hxx.symm
      apply key _ _ hlval
      rcases (div_nonneg (sq_nonneg ‖LinearMap.adjoint A x‖) hn.le).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; apply hl; rw [hlval, ← heq]; simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalApplyComm
section
namespace GlobalTheory.AevalCommute

theorem pow_apply_comm {O : Type} [CommRing O] {k : Type} [Field k] [Algebra O k]
    {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module k V]
    (J : M →+ V) (ν : Module.End O M) (μ : Module.End k V)
    (hνμ : ∀ y : M, J (ν y) = μ (J y)) (n : ℕ) (y : M) :
    J ((ν ^ n) y) = (μ ^ n) (J y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hνμ]

theorem aeval_apply_comm {O : Type} [CommRing O] {k : Type} [Field k] [Algebra O k]
    {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module k V]
    (J : M →+ V) (hJ : ∀ (c : O) (y : M), J (c • y) = algebraMap O k c • J y)
    (ν : Module.End O M) (μ : Module.End k V)
    (hνμ : ∀ y : M, J (ν y) = μ (J y)) (f : Polynomial O) (y : M) :
    J (Polynomial.aeval ν f y) = Polynomial.aeval μ (f.map (algebraMap O k)) (J y) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, hJ, pow_apply_comm J ν μ hνμ]

theorem main : ∀ {O : Type} [inst : CommRing O] {k : Type} [inst_1 : Field k] [inst_2 : Algebra O k] {M V : Type} [inst_3 : AddCommGroup M] [inst_4 : Module O M] [inst_5 : AddCommGroup V] [inst_6 : Module k V] (J : M →+ V), (∀ (c : O) (y : M), (J : M → V) (c • y) = (Algebra.algebraMap O k : O → k) c • (J : M → V) y) → ∀ (ν : Module.End O M) (μ : Module.End k V), (∀ (y : M), (J : M → V) ((ν : M → M) y) = (μ : V → V) ((J : M → V) y)) → ∀ (f : Polynomial O) (y : M), (J : M → V) (((Polynomial.aeval ν : Polynomial O → Module.End O M) f : M → M) y) = ((Polynomial.aeval μ : Polynomial k → Module.End k V) (Polynomial.map (Algebra.algebraMap O k) f) : V → V) ((J : M → V) y) :=
  fun J hJ ν μ hνμ f y => aeval_apply_comm J hJ ν μ hνμ f y

end GlobalTheory.AevalCommute
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroOfLowCoeffOfNilpotentMultiple
section
namespace GlobalTheory.NewPrime

theorem aeval_eq_zero_of_low_coeff_of_pow_eq_zero :
    ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t : B) (K : ℕ) (ξ : ι → B)
      (F : MvPolynomial ι O), t ^ K = 0 → (∀ q, t ∣ ξ q) →
      (∀ u : ι →₀ ℕ, u.degree < K → algebraMap O B (F.coeff u) = 0) →
      MvPolynomial.aeval ξ F = 0 := by
  intro O B _ _ _ ι t K ξ F htK hdvd hlow
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : u.degree < K
  · rw [hlow u hu, zero_mul]
  ·
    have hmon : t ^ u.degree ∣ ∏ i ∈ u.support, ξ i ^ u i := by
      rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => pow_dvd_pow_of_dvd (hdvd i) _
    have hK : t ^ K ∣ ∏ i ∈ u.support, ξ i ^ u i :=
      (pow_dvd_pow t (not_lt.mp hu)).trans hmon
    rw [htK, zero_dvd_iff] at hK
    rw [hK, mul_zero]

end GlobalTheory.NewPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalLogDefect
section
noncomputable section

namespace GlobalTheory.LogU

def truncLogF {R : Type} [CommRing R] (n : ℕ) (u : R) : R :=
  ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * u ^ (k + 1)

theorem map_truncLogF {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n : ℕ) (u : R) :
    f (truncLogF n u) = truncLogF n (f u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [truncLogF, map_sum, map_mul, map_pow, map_neg, map_one, map_natCast]

def logDefect (n : ℕ) : MvPolynomial (Fin 2) ℤ :=
  truncLogF n (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 1) -
    truncLogF n (MvPolynomial.X 0) - truncLogF n (MvPolynomial.X 1)

theorem aeval_logDefect {R : Type} [CommRing R] (n : ℕ) (a b : R) :
    MvPolynomial.aeval ![a, b] (logDefect n) = truncLogF n (a + b + a * b) - truncLogF n a - truncLogF n b := by
  have h := fun u => map_truncLogF (MvPolynomial.aeval (R := ℤ) ![a, b]).toRingHom n u
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  simp [logDefect, h]

end GlobalTheory.LogU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfIsHausdorff
section
namespace GlobalTheory.PowerSeriesAdicEval

open PowerSeries

theorem exists_algHom_apply_X {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) [h : IsAdicComplete I A] {y : A} (hy : y ∈ I) :
    ∃ ev : PowerSeries R →ₐ[R] A, ev PowerSeries.X = y := by
  let _ : WithIdeal A := ⟨I⟩
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval y := WithIdeal.isTopologicallyNilpotent_of_mem hy
  have _ : ContinuousSMul R A := DiscreteTopology.instContinuousSMul R A
  refine ⟨PowerSeries.aeval ha, ?_⟩
  rw [← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]

theorem algHom_coe {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (f : PowerSeries R →ₐ[R] A) (p : Polynomial R) :
    f (p : PowerSeries R) = Polynomial.aeval (f PowerSeries.X) p := by
  have : f.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (f PowerSeries.X) := by
    apply Polynomial.algHom_ext
    simp
  have h := DFunLike.congr_fun this p
  simpa using h

theorem algHom_ext_of_isHausdorff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) [h : IsHausdorff I A] (f f' : PowerSeries R →ₐ[R] A)
    (hX : f PowerSeries.X = f' PowerSeries.X) (hy : f PowerSeries.X ∈ I) : f = f' := by
  apply AlgHom.ext
  intro F
  rw [← sub_eq_zero]
  refine IsHausdorff.haus h _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have e := F.eq_X_pow_mul_shift_add_trunc n
  set G : PowerSeries R := PowerSeries.mk fun i => PowerSeries.coeff (i + n) F
  have : f F - f' F = f PowerSeries.X ^ n * (f G - f' G) := by
    conv_lhs => rw [e]
    rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, algHom_coe, algHom_coe, ← hX]
    ring
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hy n)

theorem exists_eval_and_unique :
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (y : A),
      IsAdicComplete (Ideal.span {y}) A →
        (∃ ev : PowerSeries R →ₐ[R] A, ev PowerSeries.X = y) ∧
          ∀ f f' : PowerSeries R →ₐ[R] A, f PowerSeries.X = f' PowerSeries.X →
            y ∣ f PowerSeries.X → f = f' := by
  intro R A _ _ _ y h
  exact ⟨exists_algHom_apply_X (Ideal.span {y}) (Ideal.mem_span_singleton_self y),
    fun f f' h1 h2 => algHom_ext_of_isHausdorff (Ideal.span {y}) f f' h1
      (Ideal.mem_span_singleton.2 h2)⟩

end GlobalTheory.PowerSeriesAdicEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTwistedNorm
section
open Polynomial

namespace GlobalTheory

theorem antidiag_twisted_norm : ∀ (E : Type) [Field E] (c : E ≃+* E), (∀ x, c (c x) = x) → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) E), Φ = Matrix.of (fun i j : Fin a => if j = i.rev then (-1 : E) ^ (i : ℕ) else 0) → Φ.transpose = (-1 : E) ^ (a - 1) • Φ ∧ IsUnit Φ.det ∧ ∀ δ : Matrix (Fin a) (Fin a) E, IsUnit δ.det → δ * (Φ * ((δ.map c).transpose)⁻¹ * Φ⁻¹) = (-1 : E) ^ (a - 1) • ((δ * Φ) * (((δ * Φ).map c).transpose)⁻¹) ∧ Φ * (((Φ * ((δ.map c).transpose)⁻¹ * Φ⁻¹).map c).transpose)⁻¹ * Φ⁻¹ = δ := by
  intro E _ c hc a Φ hΦ
  have hpm : ∀ n : ℕ, (-1 : E) ^ n * (-1 : E) ^ n = 1 := by
    intro n; rw [← mul_pow]; simp
  have hss : (-1 : E) ^ (a - 1) * (-1 : E) ^ (a - 1) = 1 := hpm _
  have hsign : ∀ i : Fin a, (-1 : E) ^ (i.rev : ℕ) = (-1 : E) ^ (a - 1) * (-1 : E) ^ (i : ℕ) := by
    intro i
    have hi := i.isLt
    rw [Fin.val_rev, ← pow_add]
    have : a - 1 + (i:ℕ) = (a - ((i:ℕ) + 1)) + 2 * (i:ℕ) := by omega
    rw [this, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  have hT : Φ.transpose = (-1 : E) ^ (a - 1) • Φ := by
    subst hΦ
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases h : j = i.rev
    · subst h
      simp only [Fin.rev_rev, if_true]
      exact hsign i
    · have h' : ¬ i = j.rev := by
        intro h2; apply h; rw [h2, Fin.rev_rev]
      simp [h, h']
  have hsq : Φ * Φ = (-1 : E) ^ (a - 1) • (1 : Matrix (Fin a) (Fin a) E) := by
    subst hΦ
    ext i k
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i.rev]
    · by_cases h : k = i
      · subst h
        simp only [Fin.rev_rev, if_true, hsign]
        rw [mul_one, mul_left_comm, hpm, mul_one]
      · have : ¬ k = i.rev.rev := by rwa [Fin.rev_rev]
        simp [this, h, Ne.symm h]
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hright : Φ * Φ.transpose = 1 := by
    rw [hT, Matrix.mul_smul, hsq, smul_smul, hss, one_smul]
  have hleft : Φ.transpose * Φ = 1 := by
    rw [hT, Matrix.smul_mul, hsq, smul_smul, hss, one_smul]
  have hinv : Φ⁻¹ = Φ.transpose := Matrix.inv_eq_left_inv hleft
  have hTinv : (Φ.transpose)⁻¹ = Φ := Matrix.inv_eq_left_inv hright
  have hdet : IsUnit Φ.det := Matrix.isUnit_det_of_left_inverse hleft
  have hΦc : Φ.map c = Φ := by
    subst hΦ
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hmapmul : ∀ A B : Matrix (Fin a) (Fin a) E, (A * B).map c = A.map c * B.map c :=
    fun A B => Matrix.map_mul (f := (c : E →+* E))
  have hmapinv : ∀ A : Matrix (Fin a) (Fin a) E, IsUnit A.det → (A⁻¹).map c = (A.map c)⁻¹ := by
    intro A hA
    refine (Matrix.inv_eq_left_inv ?_).symm
    rw [← hmapmul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ c.map_zero c.map_one]
  have hcc : ∀ A : Matrix (Fin a) (Fin a) E, (A.map c).map c = A := by
    intro A; ext i j; simp [hc]
  refine ⟨hT, hdet, fun δ hδ => ⟨?_, ?_⟩⟩
  · rw [hmapmul, hΦc, Matrix.transpose_mul, Matrix.mul_inv_rev, hTinv, hinv, hT]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  · have hYd : IsUnit ((δ.map c).transpose).det := by
      rw [Matrix.det_transpose]
      have h1 := RingHom.map_det (c : E →+* E) δ
      rw [RingHom.mapMatrix_apply] at h1
      have h2 : (δ.map c).det = c δ.det := h1.symm
      rw [h2]; exact hδ.map c
    have hΦTc : (Φ.transpose).map c = Φ.transpose := by rw [Matrix.transpose_map, hΦc]
    rw [hinv, hmapmul, hmapmul, hΦc, hΦTc, hmapinv _ hYd,
      Matrix.transpose_map, hcc, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
      Matrix.mul_inv_rev, Matrix.mul_inv_rev, hTinv, Matrix.nonsing_inv_nonsing_inv _ hδ, hinv]
    have e : Φ * (Φ * δ * Φ.transpose) * Φ.transpose = (Φ * Φ) * δ * (Φ.transpose * Φ.transpose) := by
      simp only [Matrix.mul_assoc]
    rw [e, ← Matrix.transpose_mul, hsq, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hss, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntitoneFiltrationExistsAdaptedLinearIndepSet
section
namespace GlobalTheory

open Submodule

theorem antitone_filtration_exists_adapted_linearIndep_set {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hi : ℤ) (hhi : A hi = ⊥) (n : ℕ) :
    ∃ (s : Set M) (k : M → ℤ), LinearIndepOn L id s ∧ (∀ x ∈ s, hi - n ≤ k x) ∧
      ∀ a, hi - n ≤ a → A a = span L {x | x ∈ s ∧ a ≤ k x} := by
  classical
  induction n with
  | zero =>
    refine ⟨∅, fun _ => hi, linearIndepOn_empty L id, fun x hx => hx.elim, fun a ha => ?_⟩
    simp only [Set.mem_empty_iff_false, false_and, Set.ofPred_false, Submodule.span_empty]
    rw [eq_bot_iff, ← hhi]
    exact hA (by simpa using ha)
  | succ n ih =>
    obtain ⟨s, k, hs, hk, hspan⟩ := ih
    have hsA : s ⊆ A (hi - (n + 1 : ℕ)) := by
      intro x hx
      have hx' : x ∈ A (hi - n) := by
        rw [hspan _ le_rfl]
        exact Submodule.subset_span ⟨hx, hk x hx⟩
      exact hA (by push_cast; omega) hx'
    obtain ⟨t, htA, hst, hAt, ht⟩ := exists_linearIndepOn_id_extension hs hsA
    have hkt : ∀ x ∈ t, hi - ((n + 1 : ℕ) : ℤ) ≤ (if x ∈ s then k x else hi - (n + 1 : ℕ)) := by
      intro x _
      split_ifs with h
      · have := hk x h
        push_cast at this ⊢
        omega
      · exact le_rfl
    refine ⟨t, fun x => if x ∈ s then k x else hi - (n + 1 : ℕ), ht, hkt, fun a ha => ?_⟩
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have hset : {x | x ∈ t ∧ hi - ((n + 1 : ℕ) : ℤ) ≤
          (if x ∈ s then k x else hi - (n + 1 : ℕ))} = t := by
        ext x
        exact ⟨fun hx => hx.1, fun hx => ⟨hx, hkt x hx⟩⟩
      rw [hset]
      exact le_antisymm (fun x hx => hAt hx) (Submodule.span_le.2 htA)
    · have ha' : hi - (n : ℤ) ≤ a := by
        push_cast at h
        omega
      rw [hspan a ha']
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hx, hkx⟩
        exact ⟨hst hx, by rw [if_pos hx]; exact hkx⟩
      · rintro ⟨hx, hkx⟩
        split_ifs at hkx with hxs
        · exact ⟨hxs, hkx⟩
        · push_cast at h hkx
          omega

theorem filtration_adapted_basis {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hfd : FiniteDimensional L ↥(⨆ a, A a))
    (hsep : ∀ x, (∀ a, x ∈ A a) → x = 0) :
    ∃ (m : ℕ) (d : Fin m → M) (k : Fin m → ℤ), LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {i | a ≤ k i}) := by
  classical
  have hle : ∀ a, A a ≤ ⨆ b, A b := fun a => le_iSup A a
  have hfa : ∀ a, FiniteDimensional L (A a) := fun a => Submodule.finiteDimensional_of_le (hle a)
  obtain ⟨a0, ha0⟩ : ∃ a0, ∀ a, Module.finrank L (A a0) ≤ Module.finrank L (A a) := by
    have hex : ∃ m, ∃ a, Module.finrank L (A a) = m := ⟨_, 0, rfl⟩
    obtain ⟨a0, h0⟩ := Nat.find_spec hex
    refine ⟨a0, fun a => ?_⟩
    have h := Nat.find_min' hex ⟨a, rfl⟩
    rw [← h0] at h
    exact h
  have hbot : A a0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply hsep
    intro a
    rcases le_total a a0 with h | h
    · exact hA h hx
    · rw [Submodule.eq_of_le_of_finrank_le (hA h) (ha0 a)]
      exact hx
  obtain ⟨a1, ha1⟩ : ∃ a1, ∀ a, Module.finrank L (A a) ≤ Module.finrank L (A a1) := by
    have hex : ∃ m, ∃ a, Module.finrank L ↥(⨆ b, A b) - Module.finrank L (A a) = m := ⟨_, 0, rfl⟩
    obtain ⟨a1, h1⟩ := Nat.find_spec hex
    refine ⟨a1, fun a => ?_⟩
    have h2 := Nat.find_min' hex ⟨a, rfl⟩
    rw [← h1] at h2
    have h3 := Submodule.finrank_mono (hle a)
    have h4 := Submodule.finrank_mono (hle a1)
    omega
  have htop : ⨆ b, A b = A a1 := by
    refine le_antisymm (iSup_le fun a => ?_) (hle a1)
    rcases le_total a1 a with h | h
    · exact hA h
    · exact (Submodule.eq_of_le_of_finrank_le (hA h) (ha1 a)).symm.le
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a0 - n ≤ a1 := ⟨(a0 - a1).toNat, by omega⟩
  obtain ⟨s, k, hs, hk, hspan⟩ := antitone_filtration_exists_adapted_linearIndep_set A hA a0 hbot n
  have hlow : ∀ a, a ≤ a0 - n → A a = A (a0 - n) := by
    intro a ha
    refine le_antisymm ?_ (hA ha)
    calc A a ≤ ⨆ c, A c := hle a
      _ = A a1 := htop
      _ ≤ A (a0 - n) := hA hn
  have hsU : ∀ x ∈ s, x ∈ (⨆ b, A b : Submodule L M) := by
    intro x hx
    have hx' : x ∈ A (a0 - n) := by
      rw [hspan _ le_rfl]
      exact Submodule.subset_span ⟨hx, hk x hx⟩
    exact hle _ hx'
  have hli : LinearIndependent L (fun x : s => (⟨x, hsU x x.2⟩ : (⨆ b, A b : Submodule L M))) :=
    LinearIndependent.of_comp (⨆ b, A b).subtype hs
  have hfin : s.Finite := Set.finite_coe_iff.1 hli.finite
  have _ := hfin.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => (e.symm i : M), fun i => k (e.symm i),
    LinearIndependent.comp hs e.symm e.symm.injective, fun a => ?_⟩
  show A a = Submodule.span L ((fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)})
  have himg : (fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)} = {x | x ∈ s ∧ a ≤ k x} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(e.symm i).2, hi⟩
    · rintro ⟨hx, hkx⟩
      exact ⟨e ⟨x, hx⟩, by simpa using hkx, by simp⟩
  rw [himg]
  rcases le_or_gt (a0 - n) a with h | h
  · exact hspan a h
  · rw [hlow a h.le, hspan _ le_rfl]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, -⟩
      exact ⟨hx, by have := hk x hx; omega⟩
    · rintro ⟨hx, -⟩
      exact ⟨hx, hk x hx⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
section
open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

variable {E : Type} [Field E] [NumberField E]

def Bnd (p : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Prop :=
  ∃ m : ℕ, m.Coprime p ∧ ∀ (i j : Fin n) (Q : HeightOneSpectrum (𝓞 E)),
    Valued.v ((((m : FiniteAdeleRing (𝓞 E) E) * A i j)) Q) ≤ 1

theorem bnd_mul (p n : ℕ) (A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (hA : Bnd p A) (hB : Bnd p B) :
    Bnd p (A * B) := by
  obtain ⟨a, ha, hA⟩ := hA
  obtain ⟨b, hb, hB⟩ := hB
  refine ⟨a * b, Nat.Coprime.mul_left ha hb, fun i j Q => ?_⟩
  let φ : FiniteAdeleRing (𝓞 E) E →+* _ := RestrictedProduct.evalRingHom _ Q
  have hφ : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = φ x := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hφ, Matrix.mul_apply, Finset.mul_sum, map_sum]
  apply Valuation.map_sum_le
  intro k _
  have hsplit : ((a * b : ℕ) : FiniteAdeleRing (𝓞 E) E) * (A i k * B k j) =
      ((a : FiniteAdeleRing (𝓞 E) E) * A i k) * ((b : FiniteAdeleRing (𝓞 E) E) * B k j) := by
    push_cast; ring
  rw [hsplit, map_mul, Valuation.map_mul, ← hφ, ← hφ]
  exact mul_le_one' (hA i k Q) (hB k j Q)

end GlobalTheory.StdAtPrime
end

