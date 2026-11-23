module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexTwoOfFiniteReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSquareMulInfinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0061
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
section
noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Matrix

variable {p q : ℕ}

def vecM (V : Mat p q) : Ix p q × Ix p q → ℂ := fun ab => V ab.1 ab.2

def sAd (Y V : Mat p q) : Mat p q := Matrix.of fun a b => (sinhcAd Y *ᵥ vecM V) (a, b)

def pY (B : Fin p → Fin q → ℂ) : Mat p q := pOf (Matrix.of B)

theorem pY_add (B C : Fin p → Fin q → ℂ) : pY (B + C) = pY B + pY C := by
  ext (i | i) (j | j) <;> simp [pY, pOf]

theorem pY_smul (t : ℝ) (B : Fin p → Fin q → ℂ) : pY (t • B) = t • pY B := by
  ext (i | i) (j | j) <;> simp [pY, pOf, Complex.real_smul, mul_comm]

theorem continuous_pY : Continuous (pY : (Fin p → Fin q → ℂ) → Mat p q) := by
  show Continuous fun B : Fin p → Fin q → ℂ => Matrix.fromBlocks 0 (Matrix.of B) (Matrix.of B)ᴴ 0
  refine continuous_pi fun a => continuous_pi fun b => ?_
  rcases a with a | a <;> rcases b with b | b <;> simp <;> fun_prop

theorem sAd_add (Y V W : Mat p q) : sAd Y (V + W) = sAd Y V + sAd Y W := by
  have h : vecM (V + W) = vecM V + vecM W := rfl
  ext a b
  simp [sAd, h, Matrix.mulVec_add]

theorem sAd_smul_real (Y V : Mat p q) (t : ℝ) : sAd Y (t • V) = t • sAd Y V := by
  have h : vecM (t • V) = (t : ℂ) • vecM V := by
    funext ab
    simp [vecM, Complex.real_smul]
  ext a b
  simp [sAd, h, Matrix.mulVec_smul, Complex.real_smul]

def sP (Y : Mat p q) : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ) where
  toFun B := fun i j => sAd Y (pY B) (Sum.inl i) (Sum.inr j)
  map_add' B C := by funext i j; simp [pY_add, sAd_add]
  map_smul' t B := by funext i j; simp [pY_smul, sAd_smul_real]

theorem adMat_mulVec (Y V : Mat p q) : adMat Y *ᵥ vecM V = vecM (Y * V - V * Y) := by
  funext ⟨a, b⟩
  have h1 : (Matrix.kroneckerMap (· * ·) Y (1 : Mat p q) *ᵥ vecM V) (a, b) = (Y * V) a b := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, Matrix.mul_apply,
      vecM, mul_ite, ite_mul]
  have h2 : (Matrix.kroneckerMap (· * ·) (1 : Mat p q) Yᵀ *ᵥ vecM V) (a, b) = (V * Y) a b := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type_right, Matrix.one_apply, Matrix.mul_apply,
      vecM, mul_ite, mul_comm]
  simp only [adMat, Matrix.sub_mulVec, Pi.sub_apply, h1, h2, vecM, Matrix.sub_apply]

theorem pY_conjTranspose (B : Fin p → Fin q → ℂ) : (pY B)ᴴ = pY B := by
  simp [pY, pOf, Matrix.fromBlocks_conjTranspose]

theorem pY_mem (B : Fin p → Fin q → ℂ) : pY B ∈ pR p q := by
  show pY B ∈ upq p q ∧ IsPC (pY B)
  refine ⟨?_, ?_⟩
  · show (pY B)ᴴ * Jm p q + Jm p q * pY B = 0
    rw [pY_conjTranspose]
    simp [pY, pOf, Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · intro a b h
    rcases a with a | a <;> rcases b with b | b <;> simp_all [pY, pOf, sameBlock]

theorem exists_pY {Y : Mat p q} (hY : Y ∈ pR p q) : ∃ B, Y = pY B := by
  have hY' : Y ∈ upq p q ∧ IsPC Y := hY
  obtain ⟨hu, hP⟩ := hY'
  have hu' : Yᴴ * Jm p q + Jm p q * Y = 0 := hu
  refine ⟨Y.toBlocks₁₂, ?_⟩
  ext (i | i) (j | j)
  · simpa [pY, pOf] using hP (Sum.inl i) (Sum.inl j) (by simp [sameBlock])
  · rfl
  · have h := congrFun (congrFun hu' (Sum.inr i)) (Sum.inl j)
    simp [Matrix.mul_apply, Jm, Formalism.UG.Jpq, Fintype.sum_sum_type, Matrix.one_apply, mul_ite,
      ite_mul] at h
    rw [starRingEnd_apply] at h
    show Y (Sum.inr i) (Sum.inl j) = star (Y (Sum.inl j) (Sum.inr i))
    linear_combination -h
  · simpa [pY, pOf] using hP (Sum.inr i) (Sum.inr j) (by simp [sameBlock])

def posIx : Ix p q → ℕ := Sum.elim (fun i => i.val) (fun j => j.val)

def cutH (p q : ℕ) (h : ℕ → ℝ) (n : ℕ) : ℝ := if n < min p q then h n else 0

def rootP (h : ℕ → ℝ) (ab : Ix p q × Ix p q) : ℝ :=
  if ab.1.isLeft then cutH p q h (posIx ab.1) - cutH p q h (posIx ab.2)
  else cutH p q h (posIx ab.1) + cutH p q h (posIx ab.2)

def eigP (ab cd : Ix p q × Ix p q) : ℂ :=
  if cd = ab then 1
  else if ¬ sameBlock cd.1 cd.2 ∧ posIx cd.1 = posIx ab.1 ∧ posIx cd.2 = posIx ab.2 then
    (if ab.1.isLeft then 1 else -1)
  else 0

theorem eigenvectorMatrix_eq_zero_of_sameBlock (ab : PIx p q) (cd : Ix p q × Ix p q) (h : sameBlock cd.1 cd.2) :
    eigP ab.1 cd = 0 := by
  have hne : cd ≠ ab.1 := by
    rintro rfl
    exact ab.2 h
  simp [eigP, hne, h]

def matG (T : GrpData p q) (x : T.G) : Mat p q := ((T.cov x : GL (Ix p q) ℂ) : Mat p q)

theorem matG_mul (T : GrpData p q) (x y : T.G) : matG T (x * y) = matG T x * matG T y := by
  simp only [matG, map_mul, Units.val_mul]

theorem matG_expt (T : GrpData p q) (B : Fin p → Fin q → ℂ) :
    matG T (T.expt (pY B)) = NormedSpace.exp (pY B) := by
  exact T.expt_cov (pY B) (show pY B ∈ upq p q ∧ IsPC (pY B) from pY_mem B).1

theorem continuous_expt_pY (T : GrpData p q) :
    Continuous fun B : Fin p → Fin q → ℂ => T.expt (pY B) := by
  exact T.expt_cont.comp_continuous continuous_pY
    (fun B => (show pY B ∈ upq p q ∧ IsPC (pY B) from pY_mem B).1)

theorem continuous_matG (T : GrpData p q) : Continuous (matG T) := by
  show Continuous fun x => ((T.cov x : GL (Ix p q) ℂ) : Mat p q)
  exact Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)

theorem matG_J (T : GrpData p q) (x : T.G) : (matG T x)ᴴ * Jm p q * matG T x = Jm p q := by
  have h : Formalism.UG.cT (starRingEnd ℂ) (matG T x) * Formalism.UG.Jpq p q * matG T x = Formalism.UG.Jpq p q :=
    T.cov_mem x
  have hc : Formalism.UG.cT (starRingEnd ℂ) (matG T x) = (matG T x)ᴴ := by
    ext i j
    simp [Formalism.UG.cT]
  rw [hc] at h
  exact h

theorem matG_one (T : GrpData p q) : matG T 1 = 1 := by
  simp [matG]

theorem matG_inv (T : GrpData p q) (x : T.G) :
    matG T x⁻¹ = (((T.cov x)⁻¹ : GL (Ix p q) ℂ) : Mat p q) := by
  simp only [matG, map_inv]

theorem exists_blocks (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      matG T k = Matrix.fromBlocks U 0 0 V := by
  have hK : IsKC (matG T k) := hk
  have h12 : (matG T k).toBlocks₁₂ = 0 := by
    ext i j
    exact hK (Sum.inl i) (Sum.inr j) (by simp [sameBlock])
  have h21 : (matG T k).toBlocks₂₁ = 0 := by
    ext i j
    exact hK (Sum.inr i) (Sum.inl j) (by simp [sameBlock])
  have hMe : matG T k = Matrix.fromBlocks (matG T k).toBlocks₁₁ 0 0 (matG T k).toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (matG T k)]
    rw [h12, h21]
  have hJ := matG_J T k
  rw [hMe] at hJ
  generalize (matG T k).toBlocks₁₁ = A at hJ hMe
  generalize (matG T k).toBlocks₂₂ = D at hJ hMe
  simp only [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hJ
  simp [Matrix.fromBlocks_inj] at hJ
  obtain ⟨hA, hD⟩ := hJ
  refine ⟨A, ?_, D, ?_, hMe⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hA
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hD

theorem matG_star_mul (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    (matG T k)ᴴ * matG T k = 1 := by
  obtain ⟨U, hU, V, hV, h⟩ := exists_blocks T hk
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU hV
  rw [h, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hU, hV]

theorem matG_inv_of_mem (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    matG T k⁻¹ = (matG T k)ᴴ := by
  rw [matG_inv]
  exact Units.inv_eq_of_mul_eq_one_left (matG_star_mul T hk)

def Ksub (T : GrpData p q) : Subgroup T.G where
  carrier := T.Kset
  one_mem' := by
    show IsKC (matG T 1)
    rw [matG_one]; intro a b h
    have : a ≠ b := by rintro rfl; cases a <;> simp [sameBlock] at h
    simp [Matrix.one_apply, this]
  mul_mem' := by
    intro x y hx hy
    obtain ⟨U, -, V, -, h⟩ := exists_blocks T hx
    obtain ⟨U', -, V', -, h'⟩ := exists_blocks T hy
    show IsKC (matG T (x * y))
    rw [matG_mul, h, h', Matrix.fromBlocks_multiply]
    intro a b hab
    cases a <;> cases b <;> simp_all [sameBlock]
  inv_mem' := by
    intro x hx
    show IsKC (matG T x⁻¹)
    rw [matG_inv_of_mem T hx]
    have hx' : IsKC (matG T x) := hx
    intro a b hab
    have : ¬ sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp [hx' b a this]

end GlobalTheory.PolarU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedActionsAdjointCasimirSymmetric
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FockTensor

theorem derived_adjoint_and_casimir (p q : ℕ) (T : GrpData p q) (πU : URep T) (V₁ V₂ : Type)
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V₁) (a₂ : Mat p q →ₗ[ℂ] Module.End ℂ V₂)
    (E₁ : V₁ →ₗ[ℂ] πU.H) (E₂ : V₂ →ₗ[ℂ] πU.H)
    (h₁ : ∀ Y ∈ upq p q, ∀ x,
      HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E₁ x)) (E₁ (a₁ Y x)) 0)
    (h₂ : ∀ Y ∈ upq p q, ∀ y,
      HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E₂ y)) (E₂ (a₂ Y y)) 0) :
    (∀ Z x y, inner ℂ (E₁ (a₁ Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (a₂ (adjZ Z) y))) ∧
      ∀ x y, inner ℂ (E₁ (casimir a₁ x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (casimir a₂ y)) := by
  have hreal : ∀ Y ∈ upq p q, ∀ x y,
      inner ℂ (E₁ (a₁ Y x)) (E₂ y) = - inner ℂ (E₁ x) (E₂ (a₂ Y y)) := by
    intro Y hY x y
    have h := (h₁ Y hY x).inner ℂ (h₂ Y hY y)
    simp only [inner_pi_pi] at h
    have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
    simp only [zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h0
    linear_combination h0
  have hZ : ∀ Z x y, inner ℂ (E₁ (a₁ Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (a₂ (adjZ Z) y)) := by
    intro Z x y
    obtain ⟨X, hX, Y, hY, rfl⟩ := exists_upq_add Z
    rw [adjZ_add, adjZ_smul, (mem_upq_iff X).1 hX, (mem_upq_iff Y).1 hY]
    simp only [map_add (f := _), map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_neg_right, hreal X hX, hreal Y hY]
    rfl
  refine ⟨hZ, fun x y => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [casimir, LinearMap.sum_apply, map_sum, sum_inner, inner_sum, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hZ, hZ, adjZ_Eab, adjZ_Eab]
  simp only [map_smul, LinearMap.smul_apply, inner_smul_right]
  linear_combination (sgnIx b * sgnIx b * inner ℂ (E₁ x) (E₂ (a₂ (Eab a b) (a₂ (Eab b a) y)))) *
    sgnIx_mul_self a + inner ℂ (E₁ x) (E₂ (a₂ (Eab a b) (a₂ (Eab b a) y))) * sgnIx_mul_self b

end GlobalTheory.FockTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFactorialBound
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FactorialJet

open Set Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_right (g : ℕ → ℝ → E) (C ρ t0 : ℝ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k t0 = 0) (n : ℕ) :
    ∀ k t, t0 ≤ t →
      ‖g k t‖ ≤ C * ρ ^ (k + n) * ((k + n).factorial : ℝ) * ((t - t0) ^ n / (n.factorial : ℝ)) := by
  induction n with
  | zero => intro k t _; simpa using hb k t
  | succ n ih =>
    intro k t ht
    set A : ℝ := C * ρ ^ (k + (n + 1)) * ((k + (n + 1)).factorial : ℝ) with hA
    have hB : ∀ x : ℝ, HasDerivAt (fun s : ℝ => A * ((s - t0) ^ (n + 1) / ((n + 1).factorial : ℝ)))
        (A * ((x - t0) ^ n / (n.factorial : ℝ))) x := by
      intro x
      have h1 : HasDerivAt (fun s : ℝ => (s - t0) ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * (x - t0) ^ n * 1) x := by
        exact ((hasDerivAt_id x).sub_const t0).pow (n + 1)
      have h2 := (h1.div_const ((n + 1).factorial : ℝ)).const_mul A
      refine h2.congr_deriv ?_
      congr 1
      rw [Nat.factorial_succ]
      have : (n.factorial : ℝ) ≠ 0 := by positivity
      have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast at *
      field_simp
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := g k) (f' := g (k + 1))
      (a := t0) (b := t) (fun x _ => (hd k x).continuousAt.continuousWithinAt)
      (fun x _ => (hd k x).hasDerivWithinAt) (by simp [h0 k]) hB
      (fun x hx => by
        have h := ih (k + 1) x hx.1
        have e : k + 1 + n = k + (n + 1) := by ring
        rwa [e] at h) (x := t) ⟨ht, le_rfl⟩
    exact this

theorem eq_zero_near_right (g : ℕ → ℝ → E) (C ρ t0 : ℝ) (hρ : 0 < ρ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k t0 = 0)
    (k : ℕ) (t : ℝ) (ht : t0 ≤ t) (ht' : ρ * (t - t0) < 1) : g k t = 0 := by
  have hr : ‖ρ * (t - t0)‖ < 1 := by
    rw [Real.norm_of_nonneg (mul_nonneg hρ.le (sub_nonneg.2 ht))]; exact ht'
  have hs := (summable_choose_mul_geometric_of_norm_lt_one k hr).tendsto_atTop_zero
  have hs2 := hs.const_mul (C * ρ ^ k * (k.factorial : ℝ))
  rw [mul_zero] at hs2
  have hle : ‖g k t‖ ≤ 0 := by
    refine ge_of_tendsto' hs2 fun n => ?_
    have h := norm_le_right g C ρ t0 hd hb h0 n k t ht
    refine h.trans (le_of_eq ?_)
    have e : ((k + n).factorial : ℝ) = ((n + k).choose k : ℝ) * n.factorial * k.factorial := by
      rw [add_comm k n]; exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial n k).symm
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [e, mul_pow, pow_add]
    field_simp
  exact norm_le_zero_iff.1 hle

theorem eq_zero_right (g : ℕ → ℝ → E) (C ρ : ℝ) (hρ : 0 < ρ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k 0 = 0)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) : g k t = 0 := by
  have key : ∀ m : ℕ, ∀ k (t : ℝ), 0 ≤ t → 2 * ρ * t ≤ m → g k t = 0 := by
    intro m
    induction m with
    | zero =>
      intro k t ht h
      have : t = 0 := by
        have : t ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos hρ hc
          simp at h
          nlinarith
        linarith
      rw [this, h0]
    | succ m ih =>
      intro k t ht h
      by_cases hm : 2 * ρ * t ≤ m
      · exact ih k t ht hm
      · push_neg at hm
        have e : 2 * ρ * ((m : ℝ) / (2 * ρ)) = m := by field_simp
        have h1 : (m : ℝ) / (2 * ρ) ≤ t := by
          rw [div_le_iff₀ (by positivity)]; linarith
        refine eq_zero_near_right g C ρ ((m : ℝ) / (2 * ρ)) hρ hd hb
          (fun j => ih j _ (by positivity) e.le) k t h1 ?_
        push_cast at h
        linarith
  exact key ⌈2 * ρ * t⌉₊ k t ht (Nat.le_ceil _)

theorem eq_zero_of_factorial_bound :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ → ℝ → E) (C ρ : ℝ), 0 ≤ C → 0 < ρ → (∀ k t, HasDerivAt (g k) (g (k + 1) t) t) → (∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → (∀ k, g k 0 = 0) → ∀ k t, g k t = 0 := by
  intro E _ _ g C ρ _ hρ hd hb h0 k t
  rcases le_total 0 t with ht | ht
  · exact eq_zero_right g C ρ hρ hd hb h0 k t ht
  · have h := eq_zero_right (fun j s => ((-1 : ℝ) ^ j) • g j (-s)) C ρ hρ
      (fun j s => by
        have h1 := ((hd j (-s)).scomp s (hasDerivAt_neg s)).const_smul ((-1 : ℝ) ^ j)
        refine h1.congr_deriv ?_
        rw [smul_smul, pow_succ])
      (fun j s => by simpa [norm_smul] using hb j (-s))
      (fun j => by simp [h0 j]) k (-t) (by linarith)
    simpa using h

end GlobalTheory.FactorialJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaProdEqOfEverywhereNormDiv
section
open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

theorem eta_eq_of_div_mem {K L : Type} [Field K] [Field L] [Algebra K L] {A : Type} [CommRing A]
    [Algebra K A] {a b : Aˣ} (h : a / b ∈ normGroup K L A) : eta K L A a = eta K L A b := by
  have hiff : a ∈ normGroup K L A ↔ b ∈ normGroup K L A := by
    have := (normGroup K L A).mul_mem_cancel_left (x := a / b) (y := b) h
    rwa [div_mul_cancel] at this
  by_cases hb : b ∈ normGroup K L A
  · rw [eta_eq_one_iff.2 hb, eta_eq_one_iff.2 (hiff.2 hb)]
  · rw [eta_eq_neg_one_iff.2 hb, eta_eq_neg_one_iff.2 (fun ha => hb (hiff.1 ha))]

theorem etaProd_eq_of_everywhereNorm_div {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    {x x' : FinFam K} {y y' : InfFam K} (h : EverywhereNorm K L (x / x') (y / y')) :
    etaProd K L x y = etaProd K L x' y' := by
  unfold etaProd
  congr 1
  · exact finprod_congr fun v => eta_eq_of_div_mem (h.1 v)
  · exact Finset.prod_congr rfl fun w _ => eta_eq_of_div_mem (h.2 w)

theorem exactSequence (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] : ExactSequence K L := by
  refine ⟨almostNorm_finDiag K L, fun t => (normTheorem K L t).symm, fun x y hx => ⟨?_, ?_⟩,
    exists_almostNorm_etaProd_eq_neg_one K L⟩
  · rintro ⟨t, ht⟩
    rw [etaProd_eq_of_everywhereNorm_div ht]
    exact (productFormula K L t).2
  · exact exists_everywhereNorm_div_of_etaProd_eq_one K L x y hx

end GlobalTheory.QuadSymbol

namespace GlobalTheory.Published

open GlobalTheory.QuadSymbol

theorem quadraticClassFieldTheory_holds : QuadraticClassFieldTheory :=
  ⟨fun K L _ _ _ _ _ _ =>
    ⟨localCharacters K L, normTheorem K L, exactSequence K L, productFormula K L⟩,
   fun F E K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => baseChange F E K L h⟩

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSimpleModuleOfFinrankEnd
section
open GlobalTheory.GLq Polynomial
open scoped Classical

namespace GlobalTheory.AbsIrrDescent

theorem isSimpleModule_of_finrank_end {k R M : Type} [Field k] [Ring R] [Algebra k R] [AddCommGroup M] [Module R M]
    [Module k M] [IsScalarTower k R M] [SMulCommClass R k M] [IsSemisimpleModule R M]
    (h : Module.finrank k (Module.End R M) = 1) : IsSimpleModule R M := by
  have hE : Nontrivial (Module.End R M) := Module.nontrivial_of_finrank_eq_succ h
  have hM : Nontrivial M := by
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    exact not_subsingleton (Module.End R M) inferInstance
  have : Nontrivial (Submodule R M) := (Submodule.nontrivial_iff R).2 hM
  refine { eq_bot_or_eq_top := fun U => ?_ }
  obtain ⟨U', hU⟩ := exists_isCompl U
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) one_ne_zero).1 h
    (U.subtype ∘ₗ U.projectionOnto U' hU)
  by_cases h0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := LinearMap.congr_fun hc x
    rw [h0, zero_smul] at this
    have h2 : (U.subtype ∘ₗ U.projectionOnto U' hU) x = x := by
      simpa using congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨x, hx⟩)
    rw [← h2, ← this]; rfl
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have := LinearMap.congr_fun hc (c⁻¹ • x)
    have h2 : (c • (1 : Module.End R M)) (c⁻¹ • x) = x := by
      simp [smul_smul, h0]
    rw [← h2, this]
    exact Subtype.property _

theorem isIrreducible_of_norm_one {k G V : Type} [Field k] [CharZero k] [Group G] [Fintype G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (hn : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : k)) : ρ.IsIrreducible := by
  have hc : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have : NeZero (Nat.card G : k) := ⟨hc⟩
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [hn, inv_mul_cancel₀ hc, eq_comm, Nat.cast_eq_one] at h
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  refine isSimpleModule_of_finrank_end (k := k) ?_
  rw [← h]
  exact (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).toLinearEquiv.finrank_eq.symm

end GlobalTheory.AbsIrrDescent
end

