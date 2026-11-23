module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CoprimeFactorizationUnique
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory

theorem sl2_right_factor_of_coprime_factorizations :
    ∀ (a c : ℤ), IsCoprime a c → c ≠ 0 → ∀ (y y' β β' : Matrix (Fin 2) (Fin 2) ℤ),
      y.det = a → y'.det = a → β.det = c → β'.det = c → y * β = y' * β' →
      ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * β = β' := by
  intro a c hac hc y y' β β' hy hy' hβ hβ' hyβ
  set P : Matrix (Fin 2) (Fin 2) ℤ := β' * adjugate β with hP
  set Q : Matrix (Fin 2) (Fin 2) ℤ := adjugate y' * y with hQ
  have hPQ : a • P = c • Q := by
    have h1 : adjugate y' * y * β = a • β' := by
      rw [Matrix.mul_assoc, hyβ, ← Matrix.mul_assoc, adjugate_mul, hy', Matrix.smul_mul, Matrix.one_mul]
    have h2 : β * adjugate β = c • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [mul_adjugate, hβ]
    calc a • P = (a • β') * adjugate β := by rw [hP, Matrix.smul_mul]
      _ = adjugate y' * y * β * adjugate β := by rw [h1]
      _ = Q * (β * adjugate β) := by rw [hQ, Matrix.mul_assoc]
      _ = c • Q := by rw [h2, Matrix.mul_smul, Matrix.mul_one]
  have hdiv : ∀ i j, c ∣ P i j := by
    intro i j
    have := congrFun (congrFun hPQ i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact hac.symm.dvd_of_dvd_mul_left ⟨Q i j, this⟩
  choose M hM using hdiv
  set Mm : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of M with hMm
  have hPM : P = c • Mm := by
    ext i j; simp [hMm, hM i j]
  have hMβ : Mm * β = β' := by
    have : c • (Mm * β) = c • β' := by
      rw [← Matrix.smul_mul, ← hPM, hP, Matrix.mul_assoc, adjugate_mul, hβ, Matrix.mul_smul, Matrix.mul_one]
    ext i j
    have := congrFun (congrFun this i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this
  have hdet : Mm.det = 1 := by
    have h1 : P.det = c * c := by
      rw [hP, det_mul, det_adjugate, hβ, hβ']
      simp
    rw [hPM, det_smul] at h1
    simp at h1
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
    have : c ^ 2 * Mm.det = c ^ 2 * 1 := by rw [h1]; ring
    exact mul_left_cancel₀ hc2 this
  exact ⟨⟨Mm, hdet⟩, hMβ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetProperties
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem slzDen_ne_zero (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    ((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rcases him with h0 | h0
  · rw [h0] at hre
    simp at hre
    rw [Matrix.det_fin_two, h0, hre] at hδ
    simp at hδ
  · exact absurd h0 τ.im_pos.ne'

theorem slzMob_im (δ : M2) (τ : ℍ) :
    ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))).im
      = (δ.det : ℝ) * τ.im / Complex.normSq (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
  rw [Complex.div_im, Matrix.det_fin_two]
  simp
  push_cast
  ring

theorem slzMob_im_pos (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    0 < ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))).im := by
  rw [slzMob_im]
  apply div_pos
  · exact mul_pos (by exact_mod_cast hδ) τ.im_pos
  · exact Complex.normSq_pos.2 (slzDen_ne_zero δ hδ τ)

theorem slzMob_coe (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    ((ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))) : ℍ) : ℂ)
      = (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
  rw [ofComplex_apply_of_im_pos (slzMob_im_pos δ hδ τ)]

theorem automorphyFactor_mobius_cocycle_complex (a b c d a' b' c' d' t : ℂ) (h1 : c' * t + d' ≠ 0)
    (h2 : c * ((a' * t + b') / (c' * t + d')) + d ≠ 0) :
    (c * a' + d * c') * t + (c * b' + d * d') = (c * ((a' * t + b') / (c' * t + d')) + d) * (c' * t + d') ∧
    ((a * a' + b * c') * t + (a * b' + b * d')) / ((c * a' + d * c') * t + (c * b' + d * d'))
      = (a * ((a' * t + b') / (c' * t + d')) + b) / (c * ((a' * t + b') / (c' * t + d')) + d) := by
  have e1 : (c * a' + d * c') * t + (c * b' + d * d') = (c * ((a' * t + b') / (c' * t + d')) + d) * (c' * t + d') := by
    field_simp
    ring
  refine ⟨e1, ?_⟩
  rw [e1]
  field_simp
  ring

theorem slz_mul (k : ℕ) (f : ℍ → ℂ) (δ δ' : M2) (hδ : 0 < δ.det) (hδ' : 0 < δ'.det) :
    slz k (δ * δ') f = slz k δ' (slz k δ f) := by
  funext τ
  have h2 := slzDen_ne_zero δ hδ (ofComplex ((((δ' 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ' 0 1 : ℤ) : ℂ)) / (((δ' 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ' 1 1 : ℤ) : ℂ))))
  rw [slzMob_coe δ' hδ' τ] at h2
  obtain ⟨e1, e2⟩ := automorphyFactor_mobius_cocycle_complex ((δ 0 0 : ℤ) : ℂ) ((δ 0 1 : ℤ) : ℂ) ((δ 1 0 : ℤ) : ℂ) ((δ 1 1 : ℤ) : ℂ)
    ((δ' 0 0 : ℤ) : ℂ) ((δ' 0 1 : ℤ) : ℂ) ((δ' 1 0 : ℤ) : ℂ) ((δ' 1 1 : ℤ) : ℂ) (τ : ℂ) (slzDen_ne_zero δ' hδ' τ) h2
  simp only [slz]
  rw [slzMob_coe δ' hδ' τ, Matrix.det_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [e2, e1]
  simp only [mul_pow, mul_inv]
  ring

theorem slz_SL (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    slz k (γ : M2) f τ = ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ * f (γ • τ) := by
  have hdet : (γ : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  have hg : ofComplex (((((γ : M2) 0 0 : ℤ) : ℂ) * (τ : ℂ) + (((γ : M2) 0 1 : ℤ) : ℂ)) / ((((γ : M2) 1 0 : ℤ) : ℂ) * (τ : ℂ) + (((γ : M2) 1 1 : ℤ) : ℂ))) = γ • τ := by
    ext
    rw [slzMob_coe _ (by rw [hdet]; exact one_pos) τ, coe_specialLinearGroup_apply]
    simp
  simp only [slz]
  rw [hg, hdet]
  simp

theorem slzDen_SL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ≠ 0 :=
  slzDen_ne_zero (γ : M2) (by rw [Matrix.SpecialLinearGroup.det_coe γ]; exact one_pos) τ

theorem slz_continuous (k : ℕ) (f : ℍ → ℂ) (δ : M2) (hδ : 0 < δ.det) (hf : Continuous f) :
    Continuous (slz k δ f) := by
  have hw : Continuous (fun τ : ℍ => (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))) :=
    ((continuous_const.mul continuous_coe).add continuous_const).div
      ((continuous_const.mul continuous_coe).add continuous_const) (slzDen_ne_zero δ hδ)
  have hg : Continuous (fun τ : ℍ => ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)))) := by
    rw [isOpenEmbedding_coe.isInducing.continuous_iff]
    have : (UpperHalfPlane.coe ∘ fun τ : ℍ => ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ))))
        = fun τ : ℍ => (((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) := by
      funext τ
      exact slzMob_coe δ hδ τ
    rw [this]
    exact hw
  have hj : Continuous (fun τ : ℍ => ((((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹) :=
    (((continuous_const.mul continuous_coe).add continuous_const).pow k).inv₀
      (fun τ => pow_ne_zero k (slzDen_ne_zero δ hδ τ))
  exact (continuous_const.mul hj).mul (hf.comp hg)

theorem slz_scalar (k : ℕ) (f : ℍ → ℂ) (hk : 1 ≤ k) (n : ℕ) (τ : ℍ) (hn : 0 < n) :
    slz k !![(n : ℤ), 0; 0, (n : ℤ)] f τ = (n : ℂ) ^ k / (n : ℂ) ^ 2 * f τ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hτ : ofComplex ((((n : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((n : ℤ) : ℂ))) = τ := by
    have : (((n : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((n : ℤ) : ℂ)) = (τ : ℂ) := by
      simp only [Int.cast_zero, Int.cast_natCast, add_zero, zero_mul, zero_add]
      exact mul_div_cancel_left₀ _ hn'
    rw [this]
    exact ofComplex_apply τ
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of]
  rw [hτ]
  push_cast
  field_simp
  ring

theorem slz_props : ∀ (k : ℕ) (f : ℍ → ℂ), 1 ≤ k → (∀ δ δ' : M2, 0 < δ.det → 0 < δ'.det → slz k (δ * δ') f = slz k δ' (slz k δ f)) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), slz k (γ : M2) f τ = ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ * f (γ • τ)) ∧ (∀ (L : ℕ) (χ : ℤ → ℂ), Inv k L χ f ↔ ∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → slz k (γ : M2) f = fun τ => χ (γ 1 1) * f τ) ∧ (∀ δ : M2, 0 < δ.det → Continuous f → Continuous (slz k δ f)) ∧ ∀ (n : ℕ) (τ : ℍ), 0 < n → slz k !![(n : ℤ), 0; 0, (n : ℤ)] f τ = (n : ℂ) ^ k / (n : ℂ) ^ 2 * f τ := by
  intro k f hk
  refine ⟨fun δ δ' hδ hδ' => slz_mul k f δ δ' hδ hδ', fun γ τ => slz_SL k f γ τ, ?_,
    fun δ hδ hf => slz_continuous k f δ hδ hf, fun n τ hn => slz_scalar k f hk n τ hn⟩
  intro L χ
  constructor
  · intro h γ hγ
    funext τ
    have hne := pow_ne_zero k (slzDen_SL_ne_zero γ τ)
    rw [slz_SL, h γ hγ τ]
    field_simp
  · intro h γ hγ τ
    have := congrFun (h γ hγ) τ
    rw [slz_SL, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero k (slzDen_SL_ne_zero γ τ))] at this
    rw [this]
    ring

end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitModularSSmul
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem act_S (x : Fin 2 → ℚ) : act x ModularGroup.S = ![x 1, -x 0] := by
  funext i
  fin_cases i <;> simp [act, ModularGroup.S, Fin.sum_univ_two]

theorem sg_S : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x →
    sg c x (ModularGroup.S • τ) = sg c (act x ModularGroup.S) τ := by
  intro c x τ h
  obtain ⟨hc, hc6, hx⟩ := h
  set z : ℂ := (x 1 : ℂ) * (τ : ℂ) - (x 0 : ℂ) with hz
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h1 : pt x (ModularGroup.S • τ) = z / (τ : ℂ) := by
    rw [pt, UpperHalfPlane.modular_S_smul, hz]
    simp only [UpperHalfPlane.coe_mk]
    field_simp
    ring
  have h2 : pt (act x ModularGroup.S) τ = z := by
    rw [act_S, pt, hz]
    simp
    ring
  have hnot : ∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n := by
    intro m n heq
    apply hx
    have him := congrArg Complex.im heq
    have hre := congrArg Complex.re heq
    simp [hz, mul_sub] at him hre
    have hpos : 0 < τ.im := τ.im_pos
    have e1 : (c : ℝ) * (x 1 : ℝ) = m := by
      have : ((c : ℝ) * (x 1 : ℝ) - m) * τ.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hpos.ne'
    have e0 : (c : ℝ) * (x 0 : ℝ) = ((-n : ℤ) : ℝ) := by
      rw [← mul_assoc, e1] at hre
      push_cast
      linarith
    refine ⟨⟨-n, ?_⟩, ⟨m, ?_⟩⟩
    · exact_mod_cast e0.symm
    · exact_mod_cast e1.symm
  unfold sg
  rw [h1, h2]
  exact GlobalTheory.T.smoothedThetaQProduct_modularS_transform c τ z hc hc6 hnot

end GlobalTheory.Sieg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialiseGenericSolutionAlmostAllPoints
section
open Polynomial

namespace GlobalTheory
namespace GenericSpecial

theorem ext_unit_ne {k R : Type} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    (S : Subalgebra k R) (L : R →ₗ[k] k) (hone : L 1 = 1)
    (hmul : ∀ x ∈ S, ∀ z ∈ S, L (x * z) = L x * L z) (x : R) (hx : x ∈ S) (hu : IsUnit x)
    (hi : Ring.inverse x ∈ S) : L x ≠ 0 := by
  intro h
  have e := hmul x hx _ hi
  rw [Ring.mul_inverse_cancel x hu, hone, h, zero_mul] at e
  exact one_ne_zero e

theorem lin_eq_of_zero_iff {k A : Type} [Field k] [CommRing A] [Algebra k A]
    (g h : A →ₗ[k] k) (hg : g 1 = 1) (hh : h 1 = 1) (hk : ∀ u, g u = 0 ↔ h u = 0) (u : A) :
    g u = h u := by
  have h1 : g (u - g u • 1) = 0 := by simp [hg]
  have h2 := (hk _).1 h1
  rw [map_sub, map_smul, hh, smul_eq_mul, mul_one, sub_eq_zero] at h2
  exact h2.symm

end GenericSpecial

theorem specialise_generic_solution : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (R : Type) [CommRing R] [IsDomain R] [Algebra k R] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D : Ideal A), 2 ≤ N → (∃ (ξ : A →ₐ[k] R) (Δ : I → ℕ → A →ₗ[k] R) (m : ℕ) (v : Fin m → A) (y : Fin m → R),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ i p u * Δ i (l - p) w))) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u))) → ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∃ (Q' : I → Ideal A) (f : A), (∀ i, (Q' i).IsMaximal) ∧ Function.Injective Q' ∧ (∀ i, Q' i ≠ P) ∧ (∀ i, ¬ D ≤ Q' i) ∧ ¬ D ≤ P ∧ f ∈ V ∧ f ≠ 0 ∧ f ∈ P ∧ ∀ i, f ∈ Q' i ^ N := by
  intro k A _ _ _ _ _ _ _ R _ _ _ N I _ V D hN hex
  classical
  obtain ⟨ξ, Δ, m, v, y, hinj, h01, hleib, hπ, hvV, hli, ⟨j0, hj0⟩, heq0, heqΔ, hsep, hsepξ,
    hD, hDξ⟩ := hex
  have hsep' : ∀ p : I × I, ∃ u : A, p.1 ≠ p.2 → IsUnit (Δ p.1 0 u - Δ p.2 0 u) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨0, fun h => absurd hp h⟩
    · obtain ⟨u, hu⟩ := hsep p.1 p.2 hp
      exact ⟨u, fun _ => hu⟩
  choose us hus using hsep'
  choose uξ huξ using hsepξ
  choose uD huDmem huD using hD
  obtain ⟨u0, hu0D, hu0⟩ := hDξ
  choose TJ hTJ using fun i => _root_.GlobalTheory.jets_mem_subalgebra_of_finiteType k A R N (Δ i) (h01 i) (hleib i)
  let T : Finset R := Finset.univ.biUnion TJ ∪ Finset.univ.image y ∪
    Finset.univ.image (fun p : I × I => Ring.inverse (Δ p.1 0 (us p) - Δ p.2 0 (us p))) ∪
    Finset.univ.image (fun i => Ring.inverse (Δ i 0 (uξ i) - ξ (uξ i))) ∪
    Finset.univ.image (fun i => Ring.inverse (Δ i 0 (uD i))) ∪
    {Ring.inverse (ξ u0), Ring.inverse (y j0)}
  obtain ⟨a, S, hξS, ha0, hTS, hspec⟩ := _root_.GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra k A R ξ hinj T
  refine ⟨a, ha0, ?_⟩
  intro P hPmax haP
  obtain ⟨-, φ, hφ⟩ := (_root_.GlobalTheory.DedekindCodim.dedekind_finiteType_codim k A).2.1 P hPmax
  obtain ⟨ψ, hψ⟩ := hspec φ (fun h => haP ((hφ a).2 h))
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (ψ.toLinearMap.comp
    (LinearEquiv.refl k (Subalgebra.toSubmodule S)).toLinearMap)
  have hLS : ∀ x (hx : x ∈ S), L x = ψ ⟨x, hx⟩ := by
    intro x hx
    exact LinearMap.congr_fun hL ⟨x, hx⟩
  have hone : L 1 = 1 := by rw [hLS 1 S.one_mem]; exact map_one ψ
  have hmul : ∀ x ∈ S, ∀ z ∈ S, L (x * z) = L x * L z := by
    intro x hx z hz
    rw [hLS _ (S.mul_mem hx hz), hLS x hx, hLS z hz, ← map_mul]; rfl
  have hLξ : ∀ u, L (ξ u) = φ u := fun u => by rw [hLS _ (hξS u), hψ]
  have hSΔ : ∀ i l, l < N → ∀ u, Δ i l u ∈ S := fun i =>
    hTJ i S (fun t ht => hTS t (by simp only [T, Finset.mem_union, Finset.mem_biUnion]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, Finset.mem_univ _, ht⟩))))))
  have hy : ∀ j, y j ∈ S := fun j => hTS _ (by simp [T])
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  let Δ' : I → ℕ → A →ₗ[k] k := fun i l => if l < N then L ∘ₗ Δ i l else 0
  have hΔ' : ∀ i l, l < N → ∀ u, Δ' i l u = L (Δ i l u) := by
    intro i l h u; simp [Δ', h]
  have hjet : ∀ i, ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ' i 0 u = 0) ∧
      ∀ f : A, (∀ l < N, Δ' i l f = 0) → f ∈ Q ^ N := by
    intro i
    apply GlobalTheory.T.mem_maximal_pow_of_jets_vanish k A N (Δ' i) hN
    · rw [hΔ' i 0 hN0, h01 i, hone]
    · intro l hl u w
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΔ' i l hl, hleib i l u w, map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p < l + 1 := Finset.mem_range.1 hp
      rw [map_nsmul, hmul _ (hSΔ i p (by omega) u) _ (hSΔ i (l - p) (by omega) w),
        hΔ' i p (by omega), hΔ' i (l - p) (by omega)]
    · obtain ⟨π, hπ'⟩ := hπ i
      exact ⟨π, by rw [hΔ' i 1 hN1, hπ', hone]⟩
  choose Q' hQmax hQmem hQpow using hjet
  have hunit : ∀ x ∈ S, IsUnit x → Ring.inverse x ∈ S → L x ≠ 0 :=
    fun x hx hu hi => GenericSpecial.ext_unit_ne S L hone hmul x hx hu hi
  let f : A := ∑ j, L (y j) • v j
  refine ⟨Q', f, hQmax, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i i' hii'
    by_contra hne
    have hu := hus (i, i') hne
    set u := us (i, i')
    have heqv := GenericSpecial.lin_eq_of_zero_iff (Δ' i 0) (Δ' i' 0)
      (by rw [hΔ' i 0 hN0, h01 i, hone]) (by rw [hΔ' i' 0 hN0, h01 i', hone])
      (fun w => by rw [← hQmem, ← hQmem, hii']) u
    rw [hΔ' i 0 hN0, hΔ' i' 0 hN0] at heqv
    refine hunit _ (S.sub_mem (hSΔ i 0 hN0 u) (hSΔ i' 0 hN0 u)) hu
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, i'), Finset.mem_univ _, rfl⟩))))) ?_
    rw [map_sub, heqv, sub_self]
  · intro i hiP
    have hu := huξ i
    have heqv := GenericSpecial.lin_eq_of_zero_iff (Δ' i 0) φ.toLinearMap
      (by rw [hΔ' i 0 hN0, h01 i, hone]) (map_one φ)
      (fun w => by rw [← hQmem, hiP, hφ]; rfl) (uξ i)
    rw [hΔ' i 0 hN0, AlgHom.toLinearMap_apply, ← hLξ] at heqv
    refine hunit _ (S.sub_mem (hSΔ i 0 hN0 _) (hξS _)) hu
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inr ⟨i, Finset.mem_univ _, rfl⟩)))) ?_
    rw [map_sub, heqv, sub_self]
  · intro i hDQ
    have h0 : Δ' i 0 (uD i) = 0 := (hQmem i _).1 (hDQ (huDmem i))
    rw [hΔ' i 0 hN0] at h0
    exact hunit _ (hSΔ i 0 hN0 _) (huD i)
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨i, Finset.mem_univ _, rfl⟩))) h0
  · intro hDP
    have h0 : φ u0 = 0 := (hφ u0).1 (hDP hu0D)
    rw [← hLξ] at h0
    exact hunit _ (hξS _) hu0 (hTS _ (by simp [T])) h0
  · exact Submodule.sum_mem _ fun j _ => V.smul_mem _ (hvV j)
  · intro hf
    have := (Fintype.linearIndependent_iff.1 hli) (fun j => L (y j)) hf j0
    exact hunit _ (hy j0) hj0 (hTS _ (by simp [T])) this
  · apply (hφ f).2
    have : φ f = L (∑ j, y j * ξ (v j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [f, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hmul _ (hy j) _ (hξS _), hLξ]
    rw [this, heq0, map_zero]
  · intro i
    apply hQpow i
    intro l hl
    have : Δ' i l f = L (∑ j, y j * Δ i l (v j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [f, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hmul _ (hy j) _ (hSΔ i l hl _), hΔ' i l hl]
    rw [this, heqΔ i l hl, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPeriodicCotEqQExpansionFourier
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.CotQExp

theorem hasSum_pi_cot (w : ℂ) (hw : 0 < w.im) :
    HasSum (fun m : ℕ => -2 * π * Complex.I * cexp (2 * π * Complex.I * w) ^ (m + 1))
      (π * Complex.cot (π * w) + π * Complex.I) := by
  have h : (π : ℂ) * Complex.cot (π * w) =
      π * Complex.I - 2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ n :=
    pi_mul_cot_pi_q_exp (⟨w, hw⟩ : ℍ)
  have hq : ‖cexp (2 * π * Complex.I * w)‖ < 1 :=
    UpperHalfPlane.norm_exp_two_pi_I_lt_one (⟨w, hw⟩ : ℍ)
  have hs : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ n :=
    summable_geometric_of_norm_lt_one hq
  have hs1 : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hs
  have h2 := hs1.hasSum.mul_left (-2 * π * Complex.I)
  have e : (π : ℂ) * Complex.cot (π * w) + π * Complex.I =
      -2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ (n + 1) := by
    rw [h, hs.tsum_eq_zero_add]
    ring
  rw [e]
  exact h2

theorem sum_cot_eq_qexp : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 →
    ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) =
      -2 * π * Complex.I / L *
        ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
  intro L φ z hL hz h0
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum0 : ∑ r ∈ Finset.range L, φ r = 0 := by
    simpa [hat] using h0
  have him : ∀ r : ℕ, 0 < ((z + r) / L : ℂ).im := by
    intro r
    rw [Complex.div_natCast_im]
    simpa using div_pos hz hLr
  have hs := hasSum_sum (s := Finset.range L)
    (fun r _ => (hasSum_pi_cot _ (him r)).mul_left (φ r / L))
  rw [← tsum_mul_left]
  have e1 : ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) =
      ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I) := by
    have : ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I)
        = ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L)))
          + (∑ r ∈ Finset.range L, φ r) * (π * Complex.I / L) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [this, hsum0, zero_mul, add_zero]
  rw [e1, ← hs.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [hat, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Complex.exp_nat_mul, mul_assoc (φ r), ← Complex.exp_add]
  have e2 : ((m + 1 : ℕ) : ℂ) * (2 * π * Complex.I * ((z + r) / L)) =
      2 * π * Complex.I * (r * (((m + 1 : ℕ) : ℤ) : ℂ)) / L
        + 2 * π * Complex.I * (m + 1 : ℕ) * z / L := by
    push_cast
    ring
  rw [e2]
  ring

end GlobalTheory.CotQExp
end

