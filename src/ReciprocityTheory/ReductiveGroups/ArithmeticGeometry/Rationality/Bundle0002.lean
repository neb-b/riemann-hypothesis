module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0001
public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangePf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

namespace BasisChangePf

open MvPolynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}

def CB (Q : MvPolynomial ι K) (c : ℝ) : Prop := ∀ μ, ‖AddMonoidAlgebra.coeff Q μ‖ ≤ c

lemma cb_sum {α : Type*} (s : Finset α) (g : α → MvPolynomial ι K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a ∈ s, CB (g a) c) : CB (∑ a ∈ s, g a) c := by
  classical
  intro μ
  rw [MvPolynomial.coeff_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc (fun a ha => h a ha μ)

lemma cb_mul {Q R : MvPolynomial ι K} {c d : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (hR : CB R d)
    (hd : 0 ≤ d) : CB (Q * R) (c * d) := by
  classical
  intro μ
  rw [MvPolynomial.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) (fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hQ _) (hR _) (norm_nonneg _) hc

lemma cb_one : CB (1 : MvPolynomial ι K) 1 := by
  classical
  intro μ
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

lemma cb_pow {Q : MvPolynomial ι K} {c : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (n : ℕ) : CB (Q ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using (cb_one : CB (1 : MvPolynomial ι K) 1)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact cb_mul (pow_nonneg hc n) ih hQ hc

lemma cb_prod {α : Type*} (s : Finset α) (g : α → MvPolynomial ι K) (c : α → ℝ) (hc : ∀ a, 0 ≤ c a)
    (h : ∀ a ∈ s, CB (g a) (c a)) : CB (∏ a ∈ s, g a) (∏ a ∈ s, c a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (cb_one : CB (1 : MvPolynomial ι K) 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact cb_mul (hc a) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
      (Finset.prod_nonneg fun b _ => hc b)

lemma cb_C_mul (a : K) {Q : MvPolynomial ι K} {c : ℝ} (hQ : CB Q c) : CB (C a * Q) (‖a‖ * c) := by
  classical
  intro μ
  rw [MvPolynomial.coeff_C_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hQ μ) (norm_nonneg a)

lemma cb_lin [Fintype ι] (A : ι → ι → K) {c : ℝ} (hc : 0 ≤ c) (hA : ∀ i k, ‖A i k‖ ≤ c) (i : ι) :
    CB (∑ k, C (A i k) * X k) c := by
  classical
  refine cb_sum _ _ hc (fun k _ => fun μ => ?_)
  rw [MvPolynomial.coeff_C_mul, norm_mul]
  calc ‖A i k‖ * ‖AddMonoidAlgebra.coeff (X k : MvPolynomial ι K) μ‖ ≤ ‖A i k‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [MvPolynomial.coeff_X']
        split_ifs <;> simp
    _ ≤ c := by simpa using hA i k

end BasisChangePf

open BasisChangePf in
theorem basisChange_holds : BasisChangeStatement := by
  intro K _ _ ι _ P d hP hP1 A C hC hA μ
  classical
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hL : ∀ i, CB (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k : MvPolynomial ι K) C :=
    fun i => cb_lin A hC0 hA i
  have key : CB (MvPolynomial.bind₁ (fun i => ∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) P) (C ^ d) := by
    conv => arg 1; rw [P.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine cb_sum _ _ (pow_nonneg hC0 d) (fun v hv => ?_)
    rw [MvPolynomial.bind₁_monomial]
    have hdeg : v.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact hP (MvPolynomial.mem_support_iff.1 hv)
    have hprod : CB (∏ i ∈ v.support, (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) ^ v i)
        (∏ i ∈ v.support, C ^ v i) :=
      cb_prod _ _ _ (fun i => pow_nonneg hC0 _) (fun i _ => cb_pow hC0 (hL i) (v i))
    have hb := cb_C_mul (AddMonoidAlgebra.coeff P v) hprod
    have hpow : ∏ i ∈ v.support, C ^ v i = C ^ d := by
      rw [Finset.prod_pow_eq_pow_sum, ← hdeg]
      rfl
    intro ν
    calc ‖AddMonoidAlgebra.coeff (MvPolynomial.C (AddMonoidAlgebra.coeff P v) *
          ∏ i ∈ v.support, (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) ^ v i) ν‖
        ≤ ‖AddMonoidAlgebra.coeff P v‖ * ∏ i ∈ v.support, C ^ v i := hb ν
      _ ≤ 1 * C ^ d := by
          rw [hpow]
          exact mul_le_mul_of_nonneg_right (hP1 v) (pow_nonneg hC0 d)
      _ = C ^ d := one_mul _
  exact key μ

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DescSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

section Defs

variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]

noncomputable def galAct (σ : K₂ ≃ₐ[K] K₂) : K₂ ⊗[K] V →ₗ[K] K₂ ⊗[K] V :=
  LinearMap.rTensor V σ.toLinearMap

def kPoints (W : Submodule K₂ (K₂ ⊗[K] V)) : Submodule K V :=
  (W.restrictScalars K).comap (TensorProduct.mk K K₂ V 1)

end Defs

def GaloisDescentStatement : Prop :=
  ∀ (K K₂ V : Type) [Field K] [Field K₂] [Algebra K K₂] [FiniteDimensional K K₂] [IsGalois K K₂]
    [AddCommGroup V] [Module K V] (W : Submodule K₂ (K₂ ⊗[K] V)),
    (∀ σ : K₂ ≃ₐ[K] K₂, ∀ x ∈ W, galAct σ x ∈ W) →
    W = baseSpan K₂ (kPoints W)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DiscSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def DiscStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (K₀ : Subfield K),
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K) →
    ∀ S : Set K, (∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1) →
    (∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - r| < ε) →
    ∀ (c : ℤ → K) (b : ℕ), (∀ n, n < -(b : ℤ) → c n = 0) →
      (∀ t ∈ S,
        Filter.Tendsto (fun n => ‖c n * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ∀ τ ∈ K₀, ‖τ‖ = 1 → ‖∑' n, c n * (t * τ) ^ n‖ ≤ 1) →
      ∀ n, ‖c n‖ ≤ 1 ∧ (n < 0 → c n = 0)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCoreSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def FinCoreStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (K₀ : Subfield K),
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K) →
    ∀ S : Set K, (∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1) →
    (∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - r| < ε) →
    (∀ t ∈ S, ∀ τ ∈ K₀, ‖τ‖ = 1 → t * τ ∈ S) →
    ∀ (ι : Type) [Fintype ι] (δ : MvPolynomial ι K),
      (∀ μ, ‖AddMonoidAlgebra.coeff δ μ‖ ≤ 1) → (∃ μ, ‖AddMonoidAlgebra.coeff δ μ‖ = 1) →
    ∀ (P : ℤ → MvPolynomial ι K) (b : ℕ), (∀ n, n < -(b : ℤ) → P n = 0) →
      (∀ t ∈ S, ∀ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) → ‖MvPolynomial.eval x δ‖ = 1 →
        Filter.Tendsto (fun n => ‖MvPolynomial.eval x (P n) * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ‖∑' n, MvPolynomial.eval x (P n) * t ^ n‖ ≤ 1) →
      ∀ n, (∀ μ, ‖AddMonoidAlgebra.coeff (P n) μ‖ ≤ 1) ∧ (n < 0 → P n = 0)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDimensionalBaseSpan
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def incU (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    F ⊗[K] U →ₗ[F] F ⊗[K] V :=
  AlgebraTensorModule.map (LinearMap.id : F →ₗ[F] F) U.subtype

theorem incU_apply_eq_lTensor (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    (y : F ⊗[K] U) : incU F U y = LinearMap.lTensor F U.subtype y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a u => simp [incU]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem baseSpan_eq_range (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    baseSpan F U = LinearMap.range (incU F U) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨(1 : F) ⊗ₜ[K] (⟨u, hu⟩ : U), by simp [incU]⟩
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
      have : incU F U (a ⊗ₜ[K] u) = a • ((1 : F) ⊗ₜ[K] (u : V)) := by
        simp [incU, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, u.2, rfl⟩)
    | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem incU_injective (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    Function.Injective (incU F U) := by
  intro x y h
  rw [incU_apply_eq_lTensor, incU_apply_eq_lTensor] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := F) U.subtype U.injective_subtype h

theorem finrank_baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    [FiniteDimensional K U] : Module.finrank F (baseSpan F U) = Module.finrank K U := by
  rw [baseSpan_eq_range, LinearMap.finrank_range_of_inj (incU_injective F U),
    Module.finrank_baseChange]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FreeQuotPf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open Module

section
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]

theorem freeQuot_exists_smul_mem (S : Submodule R X) {x : X}
    (hx : x ∈ Submodule.span F (S : Set X)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ S := by
  exact Bl.SecondBlockLemmaK.goal1 S hx

theorem freeQuot_rank_span (S : Submodule R X) :
    Module.rank R S = Module.rank F (Submodule.span F (S : Set X)) := by
  set T := Submodule.span F (S : Set X)
  have hST : S ≤ T.restrictScalars R := fun x hx => Submodule.subset_span hx
  let S' : Submodule R (T.restrictScalars R) := S.comap (T.restrictScalars R).subtype
  have h0 : Module.rank R ((T.restrictScalars R) ⧸ S') = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective S' q
    obtain ⟨d, hd, hd'⟩ := freeQuot_exists_smul_mem S (y.2 : (y : X) ∈ T)
    refine ⟨d, hd, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hd'
  have h1 := rank_quotient_add_rank_of_isDomain S'
  rw [h0, zero_add, (Submodule.comapSubtypeEquivOfLe hST).rank_eq] at h1
  rw [h1, IsLocalization.rank_eq (N := T) F (nonZeroDivisors R) le_rfl]
  rfl

end

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField

noncomputable def logN {K₁ : Type*} [Field K₁] [NumberField K₁]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ)

def GlobalQuotStatement : Prop :=
  ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (ρ : ℕ) (m : Matrix (Fin ρ) (Fin ρ) K₁),
    m.det ≠ 0 →
    ∀ (s : Fin ρ → IsDedekindDomain.HeightOneSpectrum (𝓞 K₁) → ℝ)
      (β : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁) → ℝ)
      (a b : Fin ρ → InfinitePlace K₁ → ℝ) (B : Fin ρ → ℝ) (Bfin : ℝ),
      (∀ i, (Function.support (s i)).Finite) → (Function.support β).Finite →
      (∀ (σ : InfinitePlace K₁) (i j : Fin ρ), m i j ≠ 0 →
        Real.log (σ (m i j)) + a i σ ≤ b j σ) →
      (∀ i, ((∑ᶠ w, s i w * logN w) - ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * a i σ) /
          (Module.finrank ℚ K₁ : ℝ) ≤ B i) →
      (∑ᶠ w, β w * logN w) / (Module.finrank ℚ K₁ : ℝ) ≤ Bfin →
      (∑ᶠ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w) /
          (Module.finrank ℚ K₁ : ℝ) ≤
        ∑ j, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) / (Module.finrank ℚ K₁ : ℝ) +
          (ρ : ℝ) / 2 * Real.log ρ + ∑ i, B i + ρ * Bfin

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.KerCoreSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

def KerCoreStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V)
    (Fam : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁], (V →ₗ[K] K₁) → Prop),
    (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (f : V →ₗ[K] K₁), Fam K₁ f →
      W ≤ LinearMap.ker f) →
    (∀ v : V, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (f : V →ₗ[K] K₁),
      Fam K₁ f → f v = 0) → v ∈ W) →
    (∀ (K' K₁ : Type) [Field K'] [NumberField K'] [Algebra K K'] [Field K₁] [NumberField K₁]
      [Algebra K K₁] (e : K' →ₐ[K] K₁) (f : V →ₗ[K] K'), Fam K' f →
      ∃ f₁ : V →ₗ[K] K₁, Fam K₁ f₁ ∧ ∀ v, f₁ v = e (f v)) →
    ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁) (ρ : ℕ)
      (g : Fin ρ → (V →ₗ[K] K₁)) (cfL : Fin ρ → Module.Dual K₁ (K₁ ⊗[K] V)),
      (∀ i, Fam K₁ (g i)) ∧ (∀ i v, cfL i ((1 : K₁) ⊗ₜ[K] v) = g i v) ∧
      (∀ x : K₁ ⊗[K] V, (∀ i, cfL i x = 0) ↔ x ∈ baseSpan K₁ W) ∧
      Module.finrank K W + ρ = Module.finrank K V

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

