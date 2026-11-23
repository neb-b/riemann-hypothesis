module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedFrameOrthogonalSubspace
section
open Matrix

namespace GlobalTheory.CompanionTheory.MidConj

theorem mul_single_one_mul_apply {l m o s : Type*} [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
    (A : Matrix l m ℂ) (C : Matrix o s ℂ) (x : m) (y : o) (i : l) (k : s) :
    (A * Matrix.single x y (1 : ℂ) * C) i k = A i x * C y k := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, mul_ite, ite_mul]

theorem conj_units_of_mid (n n' a : ℕ) (hdim : a + n' + a = n) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P.det)
    (J : Matrix (Fin n) (Fin n') ℂ) (Jp : Matrix (Fin n') (Fin n) ℂ) (B Bi : Matrix (Fin n') (Fin n') ℂ)
    (hJJ : Jp * J = 1) (hBB : B * Bi = 1)
    (hJ : ∀ (i : Fin n) (j : Fin n'), J i j = ∑ r : Fin n', P i (⟨a + r.val, by omega⟩ : Fin n) * B r j)
    (hout : ∀ b : Fin n, (b.val < a ∨ n ≤ b.val + a) → Jp *ᵥ (fun k => P k b) = 0)
    (p q : Fin n') :
    J * Matrix.single p q (1 : ℂ) * Jp = ∑ r : Fin n', ∑ u : Fin n', (B r p * Bi q u) •
      (P * Matrix.single (⟨a + r.val, by omega⟩ : Fin n) (⟨a + u.val, by omega⟩ : Fin n) (1 : ℂ) * P⁻¹) := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  let Pm : Matrix (Fin n) (Fin n') ℂ := fun i s => P i ⟨a + s.val, by omega⟩
  have hJm : J = Pm * B := by
    ext i j
    rw [hJ i j]
    rfl
  have hmid : Jp * Pm = Bi := by
    calc Jp * Pm = Jp * Pm * (B * Bi) := by rw [hBB, Matrix.mul_one]
      _ = (Jp * J) * Bi := by rw [hJm]; simp only [Matrix.mul_assoc]
      _ = Bi := by rw [hJJ, Matrix.one_mul]
  have hN_mid : ∀ (q : Fin n') (s : Fin n'), (Jp * P) q ⟨a + s.val, by omega⟩ = Bi q s := by
    intro q s
    calc (Jp * P) q ⟨a + s.val, by omega⟩ = (Jp * Pm) q s := rfl
      _ = Bi q s := by rw [hmid]
  have hN_out : ∀ (q : Fin n') (b : Fin n), (b.val < a ∨ n ≤ b.val + a) → (Jp * P) q b = 0 := by
    intro q b hb
    have h := congrFun (hout b hb) q
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h
  have hJp : ∀ (q : Fin n') (k : Fin n),
      Jp q k = ∑ u : Fin n', Bi q u * P⁻¹ ⟨a + u.val, by omega⟩ k := by
    intro q k
    calc Jp q k = ((Jp * P) * P⁻¹) q k := by rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
      _ = ∑ b : Fin n, (Jp * P) q b * P⁻¹ b k := by rw [Matrix.mul_apply]
      _ = ∑ u : Fin n', Bi q u * P⁻¹ ⟨a + u.val, by omega⟩ k := by
        symm
        refine Fintype.sum_of_injective (fun u : Fin n' => (⟨a + u.val, by omega⟩ : Fin n)) ?_ _ _ ?_ ?_
        · intro u v huv
          simp only [Fin.mk.injEq] at huv
          exact Fin.ext (by omega)
        · intro b hb
          have hb' : b.val < a ∨ n ≤ b.val + a := by
            by_contra hc
            simp only [not_or, not_lt] at hc
            exact hb (Set.mem_range.mpr ⟨⟨b.val - a, by omega⟩, Fin.ext (show a + (b.val - a) = b.val by omega)⟩)
          rw [hN_out q b hb', zero_mul]
        · intro u
          rw [hN_mid q u]
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_single_one_mul_apply]
  rw [hJ i p, hJp q k, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun u _ => ?_))
  ring

end GlobalTheory.CompanionTheory.MidConj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfCompactCoercive
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Glob

theorem finiteDimensional_of_compact_coercive :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c →
        (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by
  intro H _ _ _ A hA S c hc hS
  have hS' : ∀ u ∈ S.topologicalClosure, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re := by
    intro u hu
    have hcl : IsClosed {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re} :=
      isClosed_le (continuous_const.mul (continuous_norm.pow 2))
        (Complex.continuous_re.comp (continuous_id.inner A.continuous))
    have hsub : (S : Set H) ⊆ {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re} := fun u hu ↦ hS u hu
    have h := closure_minimal hsub hcl
    rw [← Submodule.topologicalClosure_coe] at h
    exact h hu
  have hbd : ∀ u ∈ S.topologicalClosure, ‖u‖ ≤ c⁻¹ * ‖A u‖ := by
    intro u hu
    have h1 := hS' u hu
    have h2 : (⟪u, A u⟫_ℂ).re ≤ ‖u‖ * ‖A u‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have h3 : c * ‖u‖ ≤ ‖A u‖ := by
      rcases (norm_nonneg u).eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]
        exact norm_nonneg _
      · nlinarith
    rw [inv_mul_eq_div, le_div_iff₀ hc]
    linarith
  let T : S.topologicalClosure →L[ℂ] H := A.comp S.topologicalClosure.subtypeL
  have hT : IsCompactOperator T := hA.comp_clm S.topologicalClosure.subtypeL
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) T := by
    refine ContinuousLinearMap.antilipschitz_of_bound T fun x ↦ ?_
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
    exact hbd x x.2
  have hemb : Topology.IsClosedEmbedding T := hanti.isClosedEmbedding T.uniformContinuous
  have hK := IsCompactOperator.isCompact_closure_image_closedBall
    (f := (T : S.topologicalClosure →ₗ[ℂ] H)) hT 1
  have hball : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1) := by
    refine (hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_
    intro x hx
    exact subset_closure ⟨x, hx, rfl⟩
  have : FiniteDimensional ℂ S.topologicalClosure :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one hball
  exact Submodule.finiteDimensional_of_le S.le_topologicalClosure

end GlobalTheory.CompanionTheory.Glob
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan
section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

def LocPrincipal {A : Type} [CommRing A] (I p : Ideal A) : Prop :=
  ∃ t f : A, t ∉ p ∧ f ∈ I ∧ f ≠ 0 ∧ ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NearIdentityMatrixPositiveSolution
section
namespace GlobalTheory.CompanionTheory.DiagDom

theorem perturb_bound {κ : Type} [Fintype κ] [DecidableEq κ] (W : κ → κ → ℝ) (ε C : ℝ)
    (hW : ∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) (c : κ → ℝ)
    (hC : ∀ i, |c i| ≤ C) (σ : κ) :
    |∑ i, W σ i * c i - c σ| ≤ (Fintype.card κ : ℝ) * ε * C := by
  have hrw : ∑ i, W σ i * c i - c σ = ∑ i, (W σ i - if σ = i then 1 else 0) * c i := by
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [hrw]
  calc |∑ i, (W σ i - if σ = i then 1 else 0) * c i|
      ≤ ∑ i, |(W σ i - if σ = i then 1 else 0) * c i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : κ, ε * C := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hW σ i).le (hC i) (abs_nonneg _) ((abs_nonneg _).trans (hW σ i).le)
    _ = (Fintype.card κ : ℝ) * ε * C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

theorem small_perturbation_injective_pos :
    ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ,
      (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
      (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
      ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) →
        (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by
  intro κ _ _ M
  have hn0 : (0 : ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hM1 : 0 < |M| + 1 := by positivity
  refine ⟨1 / (2 * ((Fintype.card κ : ℝ) + 1) * (|M| + 1)), by positivity, fun W hW => ?_⟩
  set n : ℝ := (Fintype.card κ : ℝ) with hn
  set ε := 1 / (2 * (n + 1) * (|M| + 1)) with hε
  have hδ : n * ε * (2 * (|M| + 1)) ≤ 1 := by
    have e : n * ε * (2 * (|M| + 1)) = n / (n + 1) := by
      rw [hε]
      field_simp
    rw [e, div_le_one (by linarith)]
    linarith
  have hε0 : 0 < ε := by positivity
  have hδ0 : 0 ≤ n * ε := by positivity
  have hδh : n * ε ≤ 1 / 2 := by nlinarith [abs_nonneg M]
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨fun c _ => funext fun i => (IsEmpty.false i).elim, fun c _ _ i => (IsEmpty.false i).elim⟩
  have bound : ∀ c : κ → ℝ, ∃ j, ∀ σ,
      |∑ i, W σ i * c i - c σ| ≤ n * ε * |c j| ∧ |c σ| ≤ |c j| := by
    intro c
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |c i|) Finset.univ_nonempty
    exact ⟨j, fun σ => ⟨perturb_bound W ε |c j| hW c (fun i => hj i (Finset.mem_univ i)) σ,
      hj σ (Finset.mem_univ σ)⟩⟩
  constructor
  · intro c hc
    obtain ⟨j, hj⟩ := bound c
    have h1 := (hj j).1
    rw [hc j, zero_sub, abs_neg] at h1
    have hC : |c j| = 0 := by nlinarith [abs_nonneg (c j)]
    funext i
    have h2 := (hj i).2
    rw [hC] at h2
    exact abs_nonpos_iff.mp h2
  · intro c hpos hratio i
    obtain ⟨j, hj⟩ := bound c
    have hC0 : 0 ≤ |c j| := abs_nonneg _
    have h1 : |c j| ≤ ∑ k, W j k * c k + n * ε * |c j| := by
      have e := abs_sub_abs_le_abs_sub (c j) (∑ k, W j k * c k)
      rw [abs_sub_comm (c j), abs_of_pos (hpos j)] at e
      linarith [(hj j).1]
    have h2 : ∑ k, W i k * c k - n * ε * |c j| ≤ c i := by
      linarith [(abs_le.mp (hj i).1).2]
    have h3 := hratio j i
    have hyi := hpos i
    have hMy : M * ∑ k, W i k * c k ≤ |M| * ∑ k, W i k * c k :=
      mul_le_mul_of_nonneg_right (le_abs_self M) hyi.le
    have s1 : n * ε * |c j| * (2 * (|M| + 1)) ≤ |c j| := by
      nlinarith [mul_le_mul_of_nonneg_right hδ hC0]
    have s2 : |c j| * (1 - n * ε) ≤ |M| * ∑ k, W i k * c k := by nlinarith
    have s3 : n * ε * |c j| * (|M| + 1) < (∑ k, W i k * c k) * (|M| + 1) := by
      nlinarith [mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ 1 - 2 * (n * ε))]
    have s4 : n * ε * |c j| < ∑ k, W i k * c k := lt_of_mul_lt_mul_right s3 hM1.le
    linarith

end GlobalTheory.CompanionTheory.DiagDom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RamifiedPrimeContainsDiscriminant
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

theorem natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (hdvd : P ∣ differentIdeal ℤ (𝓞 E)) :
    (((discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm : ℕ) : 𝓞 E) ∈ P := by
  by_contra ht
  have hv0 : P.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hP0
  have hvp : (P.under (𝓞 F)).IsPrime := inferInstance
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.under (𝓞 F), hvp, hv0⟩
  have hcast : ∀ (n : ℕ), (n : 𝓞 F) ∈ v.asIdeal → (n : 𝓞 E) ∈ P := fun n hn => by
    have : algebraMap (𝓞 F) (𝓞 E) (n : 𝓞 F) ∈ P := hn
    simpa [map_natCast] using this
  have hvS : v ∉ S := by
    intro hvS
    apply ht
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_left
    have hd : v.asIdeal.absNorm ∣ ∏ w ∈ S, w.asIdeal.absNorm := Finset.dvd_prod_of_mem _ hvS
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hcast _ (Ideal.absNorm_mem _))
  have hlies : P.LiesOver v.asIdeal := ⟨rfl⟩
  have hun : Algebra.IsUnramifiedAt (𝓞 F) P := hS v hvS P hP hlies
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)] at hdvd
  rcases (Ideal.prime_of_isPrime hP0 hP).dvd_or_dvd hdvd with h | h
  · exact not_dvd_differentIdeal_iff.2 hun h
  · apply ht
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_right
    apply hcast
    have hmap : differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
    apply hmap
    rw [← absNorm_differentIdeal F (𝓞 F)]
    exact Ideal.absNorm_mem _

end GlobalTheory.CompanionTheory.GlobalFiniteness
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOperatorBoundedByPolynomialRoots
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.SkewSpec

theorem aeval_intertwine {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (f : A →ₗ[ℂ] B) (SA : Module.End ℂ A) (SB : Module.End ℂ B)
    (h : ∀ v, f (SA v) = SB (f v)) (p : Polynomial ℂ) (v : A) :
    f (Polynomial.aeval SA p v) = Polynomial.aeval SB p (f v) := by
  induction p using Polynomial.induction_on generalizing v with
  | C a => simp [Polynomial.aeval_C, Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    have hp : Polynomial.C a * Polynomial.X ^ (n + 1) =
        (Polynomial.C a * Polynomial.X ^ n) * (Polynomial.X : Polynomial ℂ) := by ring
    rw [hp, map_mul (Polynomial.aeval SA), map_mul (Polynomial.aeval SB), Polynomial.aeval_X, Polynomial.aeval_X,
      Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem functional_aeval {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : A → ℂ) (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hsmul : ∀ (c : ℂ) a, φ (c • a) = c * φ a)
    (S : Module.End ℂ A) (c : ℂ)
    (h : ∀ v, φ (S v) = c * φ v) (p : Polynomial ℂ) (v : A) :
    φ (Polynomial.aeval S p v) = p.eval c * φ v := by
  induction p using Polynomial.induction_on generalizing v with
  | C a => simp [Polynomial.aeval_C, Module.algebraMap_end_apply, hsmul]
  | add p q hp hq => simp [hp, hq, hadd, add_mul]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply, ih, h]
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
    ring

theorem fd_bound {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : Module.End ℂ E) (hS : ∀ x y, ⟪S x, y⟫_ℂ = -⟪x, S y⟫_ℂ) (m : Polynomial ℂ) (hm : m ≠ 0)
    (κ : ℝ) (hκ : 0 ≤ κ) (hr : ∀ r ∈ m.roots, ‖r‖ ≤ κ) (u : E)
    (hu : Polynomial.aeval S m u = 0) : ‖S u‖ ≤ κ * ‖u‖ := by
  have hA : (Complex.I • S : E →ₗ[ℂ] E).IsSymmetric := by
    intro x y
    simp [inner_smul_left, inner_smul_right, hS]
  let b := hA.eigenvectorBasis (n := Module.finrank ℂ E) rfl
  let μ := hA.eigenvalues (n := Module.finrank ℂ E) rfl
  have hb : ∀ i, S (b i) = (-Complex.I * (μ i : ℂ)) • b i := by
    intro i
    have h1 := hA.apply_eigenvectorBasis (n := Module.finrank ℂ E) rfl i
    have h2 : Complex.I • S (b i) = ((μ i : ℝ) : ℂ) • b i := by simpa using h1
    have h3 := congrArg (fun w => (-Complex.I) • w) h2
    simp only [smul_smul] at h3
    simpa using h3
  have hφ : ∀ i v, ⟪b i, S v⟫_ℂ = (-Complex.I * (μ i : ℂ)) * ⟪b i, v⟫_ℂ := by
    intro i v
    have h1 := hS (b i) v
    rw [hb, inner_smul_left] at h1
    simp at h1
    linear_combination h1
  have hc : ∀ i, ⟪b i, u⟫_ℂ = 0 ∨ ‖(μ i : ℂ)‖ ≤ κ := by
    intro i
    have h1 := functional_aeval (fun v => ⟪b i, v⟫_ℂ) (fun a c => inner_add_right _ _ _)
      (fun c a => inner_smul_right _ _ _) S _ (hφ i) m u
    simp only [hu, inner_zero_right] at h1
    rcases mul_eq_zero.mp h1.symm with h2 | h2
    · right
      have h3 := hr _ ((Polynomial.mem_roots hm).mpr h2)
      simpa using h3
    · exact Or.inl h2
  have hsq : ‖S u‖ ^ 2 ≤ (κ * ‖u‖) ^ 2 := by
    rw [mul_pow, ← b.sum_sq_norm_inner_right (S u), ← b.sum_sq_norm_inner_right u, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hφ, norm_mul, mul_pow]
    rcases hc i with h | h
    · simp [h]
    · have h4 : ‖-Complex.I * (μ i : ℂ)‖ ≤ κ := by simpa using h
      gcongr
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem norm_le_of_aeval_eq_zero (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : M →ₗ[ℂ] H) (hι : Function.Injective ι) (T : Module.End ℂ M)
    (hT : ∀ x y, ⟪ι (T x), ι y⟫_ℂ = -⟪ι x, ι (T y)⟫_ℂ) (m : Polynomial ℂ) (hm : m ≠ 0) (κ : ℝ)
    (hκ : 0 ≤ κ) (hr : ∀ r ∈ m.roots, ‖r‖ ≤ κ) (x : M) (hx : Polynomial.aeval T m x = 0) :
    ‖ι (T x)‖ ≤ κ * ‖ι x‖ := by
  classical
  let L : Polynomial ℂ →ₗ[ℂ] M :=
    { toFun := fun p => Polynomial.aeval T p x
      map_add' := fun p q => by simp
      map_smul' := fun c p => by simp }
  have hL : ∀ p, L p = Polynomial.aeval T p x := fun _ => rfl
  let N : Submodule ℂ M := LinearMap.range L
  have hNeq : N = (Polynomial.degreeLT ℂ m.natDegree).map L := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      refine ⟨p % m, ?_, ?_⟩
      · have h1 := Polynomial.degree_mod_lt p hm
        rw [Polynomial.degree_eq_natDegree hm] at h1
        exact Polynomial.mem_degreeLT.mpr h1
      · have h2 : L (m * (p / m)) = 0 := by
          rw [hL, mul_comm, map_mul, Module.End.mul_apply, hx, map_zero]
        have h3 := congrArg L (EuclideanDomain.div_add_mod p m)
        rw [map_add (f := _), h2, zero_add] at h3
        exact h3
    · exact LinearMap.map_le_range
  haveI : Module.Finite ℂ (Polynomial.degreeLT ℂ m.natDegree) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ m.natDegree).symm
  haveI hfin : Module.Finite ℂ N := by
    rw [hNeq]
    exact Module.Finite.map _ _
  have hN : ∀ v ∈ N, T v ∈ N := by
    rintro _ ⟨p, rfl⟩
    refine ⟨Polynomial.X * p, ?_⟩
    rw [hL, hL, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  have hxN : x ∈ N := ⟨1, by simp [hL]⟩
  let R : Module.End ℂ N := T.restrict hN
  let e := Submodule.equivMapOfInjective ι hι N
  let S : Module.End ℂ (N.map ι) := e.toLinearMap ∘ₗ R ∘ₗ e.symm.toLinearMap
  have hSe : ∀ v, S (e v) = e (R v) := fun v => by simp [S]
  have heι : ∀ v : N, ((e v : N.map ι) : H) = ι v := fun v => rfl
  have hRc : ∀ v : N, ((R v : N) : M) = T v := fun v => rfl
  have hS : ∀ a b, ⟪S a, b⟫_ℂ = -⟪a, S b⟫_ℂ := by
    intro a b
    obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    rw [hSe, hSe, Submodule.coe_inner, Submodule.coe_inner, heι, heι, heι, heι, hRc, hRc]
    exact hT _ _
  let x' : N := ⟨x, hxN⟩
  have h1 : ((Polynomial.aeval R m x' : N) : M) = 0 := by
    have := aeval_intertwine N.subtype R T (fun v => rfl) m x'
    simpa [x', hx] using this
  have h2 : Polynomial.aeval R m x' = 0 := Subtype.ext h1
  have h3 : Polynomial.aeval S m (e x') = 0 := by
    have := aeval_intertwine e.toLinearMap R S (fun v => (hSe v).symm) m x'
    rw [h2] at this
    simpa using this.symm
  have h4 := fd_bound S hS m hm κ hκ hr (e x') h3
  rw [hSe, Submodule.coe_norm, Submodule.coe_norm, heι, heι, hRc] at h4
  exact h4

end GlobalTheory.CompanionTheory.SkewSpec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UniqueReducedOrbitRepresentative
section
namespace GlobalTheory.CompanionTheory.SiegelKlingen

theorem exists_unique_minimal_translate :
    ∀ {G M : Type} [Group G] [Monoid M] (φ : G →* M) (f : G →* ℝ), (∀ g, 0 < f g) →
    Function.Injective f → ∀ (D : Set M),
    {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite → ∀ (x : M), (∃ g, φ g * x ∈ D) →
    ∃! g, φ g * x ∈ {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D} := by
  intro G M _ _ φ f hpos hinj D hfin x ⟨g0, hg0⟩
  have key : ∀ a b : G, φ (a * b⁻¹) * (φ b * x) = φ a * x := by
    intro a b
    rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
  have hS : {g : G | φ g * x ∈ D}.Finite := by
    refine (hfin.image (fun h => h * g0)).subset ?_
    intro g hg
    exact ⟨g * g0⁻¹, ⟨φ g0 * x, hg0, by rw [key]; exact hg⟩, inv_mul_cancel_right g g0⟩
  obtain ⟨g, hgS, hmin⟩ := Set.exists_min_image _ f hS ⟨g0, hg0⟩
  refine ⟨g, ⟨hgS, fun g' hg' hD => ?_⟩, ?_⟩
  · have hmem : φ (g' * g) * x ∈ D := by rwa [map_mul, mul_assoc]
    have h1 := hmin _ hmem
    rw [map_mul] at h1
    have hp := hpos g
    nlinarith
  · rintro g2 ⟨hg2, hmin2⟩
    have h1 : 1 ≤ f (g * g2⁻¹) := not_lt.1 fun hlt => hmin2 _ hlt (by rw [key]; exact hgS)
    rw [map_mul, map_inv] at h1
    have hp2 := hpos g2
    have h3 := mul_le_mul_of_nonneg_right h1 hp2.le
    rw [one_mul, inv_mul_cancel_right₀ hp2.ne'] at h3
    exact hinj (le_antisymm h3 (hmin g2 hg2))

end GlobalTheory.CompanionTheory.SiegelKlingen
end

