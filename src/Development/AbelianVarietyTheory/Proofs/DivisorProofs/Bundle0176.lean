module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityAsSumExpMinusOne
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalLinearZero
section
namespace GlobalTheory.CharInvForm

theorem iteratedDeriv_exp_I (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (Complex.I * y)) =
      fun y : ℝ => Complex.I ^ n * Complex.exp (Complex.I * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => Complex.I ^ n * Complex.exp (Complex.I * y))
        (Complex.I ^ n * (Complex.exp (Complex.I * y) * (Complex.I * 1))) y :=
      ((h1.const_mul Complex.I).cexp).const_mul (Complex.I ^ n)
    rw [h.deriv]; ring

theorem temperate_exp_I : Function.HasTemperateGrowth (fun y : ℝ => Complex.exp (Complex.I * y)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (Complex.I * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun n => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_I, pow_zero, mul_one, norm_mul, norm_pow,
    mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
  simp

theorem kills_linear_mul : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := by
  intro V _ _ _ T hT L h g hg
  obtain ⟨n, a, A, hA, hdiv⟩ := _root_.GlobalTheory.ExpDivision.exists_division
  have hAL : ∀ j, Function.HasTemperateGrowth (fun x : V => A j (L x)) := fun j =>
    (hA j).comp L.hasTemperateGrowth
  have hE : ∀ j, Function.HasTemperateGrowth
      (fun x : V => Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ))) := fun j =>
    temperate_exp_I.comp (a j • L).hasTemperateGrowth
  let k : Fin n → SchwartzMap V ℂ := fun j => SchwartzMap.smulLeftCLM ℂ (fun x : V => A j (L x)) h
  let f' : Fin n → SchwartzMap V ℂ := fun j =>
    SchwartzMap.smulLeftCLM ℂ (fun x : V => Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ))) (k j)
  have hk : ∀ j x, k j x = A j (L x) * h x := fun j x => by
    simp only [k]
    rw [SchwartzMap.smulLeftCLM_apply_apply (hAL j), smul_eq_mul]
  have hf : ∀ j x, f' j x = Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ)) * k j x := fun j x => by
    simp only [f']
    rw [SchwartzMap.smulLeftCLM_apply_apply (hE j), smul_eq_mul]
  have hsum : g = ∑ j, (f' j - k j) := by
    ext x
    rw [SchwartzMap.sum_apply, hg x]
    conv_lhs => rw [hdiv (L x)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SchwartzMap.sub_apply, hf, hk, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_sub, hT (a j • L) (k j) (f' j) (hf j), sub_self]

end GlobalTheory.CharInvForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorIdempotentOfGroupAlgebraIdem
section
open NumberField

namespace GlobalTheory

theorem eOp_comp_self_of_conv_idem {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL)
    (he : ∀ k, ∑ g, eC g * eC (g⁻¹ * k) = eC k) : A.eOp eC ∘ₗ A.eOp eC = A.eOp eC := by
  set c : G0 → LL := fun g => eC g * ((A.chi g)⁻¹ : LLˣ) with hc
  have hchi : ∀ g k : G0, (((A.chi g)⁻¹ : LLˣ) : LL) * (((A.chi (g⁻¹ * k))⁻¹ : LLˣ) : LL)
      = (((A.chi k)⁻¹ : LLˣ) : LL) := by
    intro g k
    rw [← Units.val_mul, ← mul_inv, ← map_mul, mul_inv_cancel_left]
  have hcc : ∀ k, ∑ g, c g * c (g⁻¹ * k) = c k := by
    intro k
    calc ∑ g, c g * c (g⁻¹ * k)
        = ∑ g, (eC g * eC (g⁻¹ * k)) * (((A.chi k)⁻¹ : LLˣ) : LL) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [hc, ← hchi g k]; ring
      _ = c k := by rw [← Finset.sum_mul, he k]
  have hE : A.eOp eC = ∑ g, c g • A.ρ g := rfl
  rw [← Module.End.mul_eq_comp, hE, Finset.sum_mul_sum]
  calc ∑ g, ∑ h, (c g • A.ρ g) * (c h • A.ρ h)
      = ∑ g, ∑ k, (c g * c (g⁻¹ * k)) • A.ρ k := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [← Equiv.sum_comp (Equiv.mulLeft g) (fun k => (c g * c (g⁻¹ * k)) • A.ρ k)]
        refine Finset.sum_congr rfl fun h _ => ?_
        simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, smul_mul_smul_comm]
    _ = ∑ k, (∑ g, c g * c (g⁻¹ * k)) • A.ρ k := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, c k • A.ρ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcc k]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorOrthogonalOfUnitaryAction
section
open NumberField

open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory

theorem twistedProjector_orthogonal_of_unitary : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL), ∀ σ : LL →+* ℂ, A.eOp eC ∘ₗ A.eOp eC = A.eOp eC →
    (∀ g x y, inner ℂ (A.j σ (A.ρ g x)) (A.j σ (A.ρ g y)) = inner ℂ (A.j σ x) (A.j σ y)) →
    (∀ g, σ (eC g⁻¹) = starRingEnd ℂ (σ (eC g))) →
    ∀ x y, ‖A.j σ (A.eOp eC x + (y - A.eOp eC y))‖ ^ 2 = ‖A.j σ (A.eOp eC x)‖ ^ 2 + ‖A.j σ (y - A.eOp eC y)‖ ^ 2 := by
  intro LL Ks _ _ _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G0 _ _ A eC σ hid hu hc x y
  have hunit : ∀ g : G0, starRingEnd ℂ (σ ((A.chi g : LLˣ) : LL)) = (σ ((A.chi g : LLˣ) : LL))⁻¹ := by
    intro g
    set z := σ ((A.chi g : LLˣ) : LL)
    have hpow : z ^ orderOf g = 1 := by
      have h1 : A.chi g ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      have h2 : ((A.chi g : LLˣ) : LL) ^ orderOf g = 1 := by
        rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
      simp only [z]; rw [← map_pow, h2, map_one]
    have hn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow (orderOf_pos g).ne'
    have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    have hm : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    exact eq_inv_of_mul_eq_one_right hm
  have key : ∀ g u v, ⟪A.j σ (A.ρ g u), A.j σ v⟫_ℂ = ⟪A.j σ u, A.j σ (A.ρ g⁻¹ v)⟫_ℂ := by
    intro g u v
    have h1 : A.ρ g (A.ρ g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← hu g u (A.ρ g⁻¹ v), h1]
  have sa : ∀ u v, ⟪A.j σ (A.eOp eC u), A.j σ v⟫_ℂ = ⟪A.j σ u, A.j σ (A.eOp eC v)⟫_ℂ := by
    intro u v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.IndefR.Arith.FormsL.eOp_apply, map_sum, map_smulₛₗ, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right]
    conv_rhs => rw [← Equiv.sum_comp (Equiv.inv G0)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [key g, Equiv.inv_apply]
    congr 1
    rw [map_mul, map_mul, map_mul, hc, map_inv, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val,
      map_inv₀, map_inv₀, map_inv₀, hunit]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
  have horth : ⟪A.j σ (A.eOp eC x), A.j σ (y - A.eOp eC y)⟫_ℂ = 0 := by
    have hy : A.eOp eC (A.eOp eC y) = A.eOp eC y := LinearMap.congr_fun hid y
    rw [sa, map_sub, hy, sub_self, map_zero, inner_zero_right]
  rw [map_add (f := _)]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  simpa only [sq] using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionAvoidPrime
section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem one_tmul_mem_locOrder_of_nsmul_mem : ∀ {B : Type} [Ring B] [Algebra ℚ B] (OB : Subring B) (b : B) (m : ℕ),
    0 < m → (m : B) * b ∈ OB → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ m →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b ∈ locOrder ℓ OB := by
  intro B _ _ OB b m hm hmb ℓ _ hℓ
  have hunit : IsUnit (m : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)).mpr hℓ)
  obtain ⟨u, hu⟩ := hunit
  have hgen : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b) ∈ locOrder ℓ OB :=
    Algebra.subset_adjoin ⟨_, hmb, rfl⟩
  have key : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b)) := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    have : ((m : B) * b) = (m : ℚ) • b := by rw [Algebra.smul_def]; simp
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    have h1 : ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = (m : ℚ_[ℓ]) := by rw [hu]; simp
    have h2 : (((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) * ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = 1 := by
      rw [← PadicInt.coe_mul]; simp
    rw [h1] at h2
    rw [Algebra.smul_def]
    simp only [map_natCast]
    rw [PadicInt.algebraMap_apply]
    linear_combination h2.symm
  rw [key]
  exact Subalgebra.smul_mem _ hgen _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryConjMapsKerAevalBasisAndGram
section
open Matrix Polynomial

namespace GlobalTheory

theorem unitary_conj_ker_basis_gram {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K)
    (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1)
    (Q : K[X]) {ι : Type} (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hspan : Submodule.span K (Set.range u) =
      LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))) :
    LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧
    Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
      LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧
    (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) *
        ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) = Matrix.of fun i j => ∑ k, σ (u i k) * u j k := by
  first
  | exact @_root_.GlobalTheory.ConjugateAlgebraLemmas.main
  | exact _root_.GlobalTheory.ConjugateAlgebraLemmas.main
  | (apply _root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateAlgebraLemmas.main ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupContinuousCharEqDetZpow
section
open Matrix

namespace GlobalTheory.UnitaryChar

variable {n : ℕ}

theorem exists_conj_diagonal (u : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ (V : Matrix.unitaryGroup (Fin n) ℂ) (d : Fin n → ℂ),
      ((V⁻¹ * u * V : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = diagonal d := by
  obtain ⟨z, hz1, hz⟩ : ∃ z : ℂ, ‖z‖ = 1 ∧ z ∉ spectrum ℂ (u : Matrix (Fin n) (Fin n) ℂ) := by
    have hfin := Matrix.finite_spectrum (u : Matrix (Fin n) (Fin n) ℂ)
    have hinf : (Metric.sphere (0 : ℂ) 1).Infinite := by
      have hc : IsConnected (Metric.sphere (0 : ℂ) 1) :=
        isConnected_sphere (by simp) 0 zero_le_one
      refine hc.isPreconnected.infinite_of_nontrivial ⟨1, by simp, -1, by simp, by norm_num⟩
    obtain ⟨z, h1, h2⟩ := hinf.exists_notMem_finite hfin
    exact ⟨z, by simpa using h1, h2⟩
  have hzz : star z * z = 1 := by
    rw [mul_comm]; simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz1]
  set U : Matrix (Fin n) (Fin n) ℂ := (u : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : star U * U = 1 := u.2.1
  have hA : IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) - U) := by
    have := spectrum.notMem_iff.1 hz
    rwa [Algebra.algebraMap_eq_smul_one] at this
  obtain ⟨B, hAB, hBA⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ, (z • 1 - U) * B = 1 ∧ B * (z • 1 - U) = 1 :=
    isUnit_iff_exists.1 hA
  have hBA' : star B * (star z • 1 - star U) = 1 := by
    have := congrArg star hAB
    simpa [star_mul, star_smul] using this
  have key : z • B + star z • star B = 1 := by
    have h1 : (star z • 1 - star U) * (z • 1 - U) =
        z • (star z • 1 - star U) + star z • (z • (1 : Matrix (Fin n) (Fin n) ℂ) - U) := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hUU, smul_sub,
        smul_smul, hzz, mul_comm z (star z), one_smul]
      abel
    have h2 : star B * ((star z • 1 - star U) * (z • 1 - U)) * B = 1 := by
      rw [← mul_assoc, hBA', one_mul, hAB]
    rw [h1, mul_add, add_mul, mul_smul_comm, hBA', mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
      mul_assoc, hAB, one_mul, mul_one] at h2
    exact h2
  have hH : (Complex.I • (z • B - (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))).IsHermitian := by
    have h3 : star z • star B = 1 - z • B := by rw [← key]; abel
    change star _ = _
    rw [star_smul, star_sub, star_smul, h3, star_smul]
    simp only [star_one, RCLike.star_def, Complex.conj_I, map_div₀, map_one, map_ofNat]
    module
  have hs := hH.conjStarAlgAut_star_eigenvectorUnitary
  set V := hH.eigenvectorUnitary
  generalize (RCLike.ofReal ∘ hH.eigenvalues : Fin n → ℂ) = e at hs
  rw [Unitary.conjStarAlgAut_star_apply] at hs
  set W : Matrix (Fin n) (Fin n) ℂ := (V : Matrix (Fin n) (Fin n) ℂ) with hW
  have hWW : star W * W = 1 := V.2.1
  have hWW' : W * star W = 1 := V.2.2
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
  have hB : star W * B * W = diagonal (fun i => z⁻¹ * (-Complex.I * e i + 1 / 2)) := by
    have h4 : diagonal (fun i => z⁻¹ * (-Complex.I * e i + 1 / 2)) =
        z⁻¹ • ((-Complex.I) • diagonal e + (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [diagonal_apply, one_apply, h]
    rw [h4, ← hs]
    simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, hWW, smul_smul, neg_mul,
      Complex.I_mul_I, neg_neg, one_smul, sub_add_cancel, inv_mul_cancel₀ hz0]
  generalize (fun i => z⁻¹ * (-Complex.I * e i + 1 / 2)) = b at hB
  have h5 : (z • 1 - star W * U * W) * diagonal b = 1 := by
    have h6 : z • 1 - star W * U * W = star W * (z • 1 - U) * W := by
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hWW]
    rw [h6, ← hB]
    calc star W * (z • 1 - U) * W * (star W * B * W)
        = star W * ((z • 1 - U) * (W * star W) * B) * W := by simp only [mul_assoc]
      _ = 1 := by rw [hWW', mul_one, hAB, mul_one, hWW]
  refine ⟨V, fun i => (star W * U * W) i i, ?_⟩
  change star W * U * W = _
  ext i j
  by_cases h : i = j
  · subst h; simp
  · have h7 := congrFun (congrFun h5 i) j
    have h8 := congrFun (congrFun h5 j) j
    rw [mul_diagonal] at h7 h8
    rw [one_apply_eq] at h8
    have hb : b j ≠ 0 := right_ne_zero_of_mul_eq_one h8
    rw [one_apply_ne h, mul_eq_zero] at h7
    rw [diagonal_apply_ne _ h]
    simpa [one_apply_ne h] using h7.resolve_right hb

noncomputable def diagHom (n : ℕ) : (Fin n → Circle) →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun t := ⟨diagonal fun i => (t i : ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    simp [Complex.mul_conj]⟩
  map_one' := by ext i j; simp
  map_mul' s t := by
    apply Subtype.ext
    simp [diagonal_mul_diagonal]

theorem coe_diagHom (t : Fin n → Circle) :
    (diagHom n t : Matrix (Fin n) (Fin n) ℂ) = diagonal fun i => (t i : ℂ) := rfl

theorem continuous_diagHom : Continuous (diagHom n) := by
  refine Continuous.subtype_mk ?_ _
  exact Continuous.matrix_diagonal (continuous_pi fun i =>
    continuous_subtype_val.comp (continuous_apply i))

theorem exists_conj_diagHom (u : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ (V : Matrix.unitaryGroup (Fin n) ℂ) (t : Fin n → Circle), V⁻¹ * u * V = diagHom n t := by
  obtain ⟨V, d, h⟩ := exists_conj_diagonal u
  have h1 := (V⁻¹ * u * V).2.2
  rw [h, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal] at h1
  have h2 : ∀ i, ‖d i‖ = 1 := fun i => by
    have := congrFun (congrFun h1 i) i
    simp only [diagonal_apply_eq, one_apply_eq, Pi.star_apply, RCLike.star_def,
      Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
    have h3 : ‖d i‖ ^ 2 = 1 := by exact_mod_cast this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
  exact ⟨V, fun i => ⟨d i, by simpa [Submonoid.unitSphere] using h2 i⟩, Subtype.ext h⟩

theorem exists_conj_perm (σ : Equiv.Perm (Fin n)) (t : Fin n → Circle) :
    ∃ P : Matrix.unitaryGroup (Fin n) ℂ, P * diagHom n t = diagHom n (t ∘ σ) * P := by
  refine ⟨⟨σ.permMatrix ℂ, ?_⟩, Subtype.ext ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix,
      ← permMatrix_mul]
    simp
  · change σ.permMatrix ℂ * diagonal _ = diagonal _ * σ.permMatrix ℂ
    ext i j
    rw [mul_diagonal, diagonal_mul]
    by_cases h : σ i = j
    · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
    · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]

theorem char_eq_det_zpow : ∀ (n : ℕ) (c : Matrix.unitaryGroup (Fin n) ℂ →* Circle), Continuous c → ∃ m : ℤ, ∀ u : Matrix.unitaryGroup (Fin n) ℂ, ((c u : Circle) : ℂ) = (Matrix.det (u : Matrix (Fin n) (Fin n) ℂ)) ^ m := by
  intro n c hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, fun u => ?_⟩
    have : u = 1 := Subtype.ext (Subsingleton.elim _ _)
    simp [this]
  set i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨m, hm⟩ := GlobalTheory.circle_hom_eq_zpow
    (c.comp ((diagHom n).comp (MonoidHom.mulSingle (fun _ : Fin n => Circle) i₀)))
    (hc.comp (continuous_diagHom.comp (continuous_mulSingle (A := fun _ : Fin n => Circle) i₀)))
  have hi : ∀ i z, c (diagHom n (Pi.mulSingle i z)) = z ^ m := fun i z => by
    obtain ⟨P, hP⟩ := exists_conj_perm (Equiv.swap i₀ i) (Pi.mulSingle i₀ z)
    have h1 : (Pi.mulSingle i₀ z : Fin n → Circle) ∘ (Equiv.swap i₀ i) = Pi.mulSingle i z := by
      ext j
      simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff,
        Equiv.swap_apply_left]
    have h2 := congrArg c hP
    rw [h1, map_mul, map_mul, mul_comm] at h2
    rw [← mul_right_cancel h2]
    exact hm z
  refine ⟨m, fun u => ?_⟩
  obtain ⟨V, t, h⟩ := exists_conj_diagHom u
  have h1 : c u = c (diagHom n t) := by
    rw [← h, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  have h2 : (u : Matrix (Fin n) (Fin n) ℂ).det = ∏ i, (t i : ℂ) := by
    rw [← det_diagonal, ← coe_diagHom, ← h]
    have h3 : (V : Matrix (Fin n) (Fin n) ℂ) * star (V : Matrix (Fin n) (Fin n) ℂ) = 1 := V.2.2
    change _ = (star (V : Matrix (Fin n) (Fin n) ℂ) * u * V).det
    rw [det_mul_comm, ← mul_assoc, h3, one_mul]
  have h4 : c (diagHom n t) = (∏ i, t i) ^ m := by
    have h5 := map_prod (c.comp (diagHom n)) (fun i => Pi.mulSingle i (t i)) Finset.univ
    rw [Finset.univ_prod_mulSingle] at h5
    simp only [MonoidHom.comp_apply, hi] at h5
    rw [h5, Finset.prod_zpow]
  rw [h1, h2, h4, Circle.coe_zpow]
  congr 1
  exact map_prod Circle.coeHom _ _

end GlobalTheory.UnitaryChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieAlgebraSpannedStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lie_algebra_spanned : ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ), A.det ≠ 0 → ∀ v : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ, LinearIndependent ℝ v → (∀ i, (v i)ᵀ * A + A * (v i).map (starRingEnd ℂ) = 0 ∧ (v i).trace = 0) → ∀ Y : Matrix (Fin r) (Fin r) ℂ, Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0 → Y.trace = 0 → Y ∈ Submodule.span ℝ (Set.range v) := by
  first | exact @GlobalTheory.TracelessSkewSpan.mem_span_of_linearIndependent | exact GlobalTheory.TracelessSkewSpan.mem_span_of_linearIndependent | (intros; apply GlobalTheory.TracelessSkewSpan.mem_span_of_linearIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStandardLatticeAlternatingFormBijective
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory.UnitaryStd

theorem form_basis_basis {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (a c : Fin g ⊕ Fin g) :
    form ρ g S (basis ρ g (j, c)) (basis ρ g (i, a)) =
      S j i * (Matrix.J (Fin g) ℤ) a c := by
  rw [form_apply, Matrix.J]
  simp only [basis_apply, dotProduct]
  rcases a with k | k <;> rcases c with l | l <;>
    simp [Pi.single_apply, Prod.ext_iff, Matrix.one_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  all_goals simp [ite_and, Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, mul_ite]
  all_goals (split_ifs <;> simp_all)

theorem toMatrix_basis_dualBasis_form {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ) :
    LinearMap.toMatrix (basis ρ g) (basis ρ g).dualBasis (form ρ g S) =
      Matrix.kroneckerMap (· * ·) S.transpose (Matrix.J (Fin g) ℤ) := by
  ext ⟨i, a⟩ ⟨j, c⟩
  rw [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr, form_basis_basis]
  rfl

theorem form_bijective_of_unimodular : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), IsUnit S.det → Function.Bijective (GlobalTheory.UnitaryStd.form ρ g S) := by
  intro E _ _ r ρ g S hS
  set b := basis ρ g
  set M := LinearMap.toMatrix b b.dualBasis (form ρ g S) with hMdef
  have hM : IsUnit M.det := by
    rw [hMdef, toMatrix_basis_dualBasis_form, Matrix.det_kronecker, Matrix.det_transpose]
    exact (hS.pow _).mul ((Matrix.isUnit_det_J (Fin g) ℤ).pow _)
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have hf : form ρ g S = Matrix.toLin b b.dualBasis M := by rw [hMdef, Matrix.toLin_toMatrix]
  set Ψ := Matrix.toLin b.dualBasis b M⁻¹
  have hl : ∀ x, Ψ (form ρ g S x) = x := fun x => by
    rw [hf, ← LinearMap.comp_apply, ← Matrix.toLin_mul, h2, Matrix.toLin_one, LinearMap.id_apply]
  have hr : ∀ f, form ρ g S (Ψ f) = f := fun f => by
    rw [hf, ← LinearMap.comp_apply, ← Matrix.toLin_mul, h1, Matrix.toLin_one, LinearMap.id_apply]
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

end GlobalTheory.UnitaryStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularNearUnitDiagonalOfTwistedGramNearStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperTriangular_near_unitDiagonal_of_twistedGram_near : ∀ (r : ℕ) (ε : Fin r → ℝ) (b : Matrix (Fin r) (Fin r) ℂ) (δ : ℝ), (∀ a, ε a = 1 ∨ ε a = -1) → 0 ≤ δ → (r : ℝ) * δ ≤ 1 / 100 → (∀ a c : Fin r, c < a → b a c = 0) → (∀ a c : Fin r, ‖(bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c - Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) a c‖ ≤ 3 * δ) → (∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ) ∧ ∀ a c : Fin r, a < c → ‖b a c‖ ≤ 6 * δ := by
  first | exact @GlobalTheory.upperTriangular_near_diag_of_gram_near | exact GlobalTheory.upperTriangular_near_diag_of_gram_near | (intros; apply GlobalTheory.upperTriangular_near_diag_of_gram_near <;> assumption)
end

