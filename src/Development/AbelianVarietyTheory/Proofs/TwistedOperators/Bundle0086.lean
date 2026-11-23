module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtExpTwoAddSmulSinhcAdjoint
section
noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem adMat_real_smul {p q : ℕ} (u : ℝ) (Y : Mat p q) : adMat (u • Y) = u • adMat Y := by
  ext i j
  simp only [adMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, smul_sub]
  congr 1
  · rw [smul_mul_assoc]
  · rw [mul_smul_comm]

def sandwichAct {p q : ℕ} (P V Q : Mat p q) :
    Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →ₗ[ℝ] Mat p q where
  toFun M := P * (Matrix.of fun a b => (M *ᵥ vecM V) (a, b)) * Q
  map_add' M N := by
    rw [← add_mul, ← mul_add]
    congr 2
    ext a b; simp [Matrix.add_mulVec]
  map_smul' t M := by
    rw [RingHom.id_apply, ← smul_mul_assoc, ← mul_smul_comm]
    congr 2
    ext a b; simp [Matrix.smul_mulVec]

theorem exp_real_smul_add {p q : ℕ} (Y : Mat p q) (u v : ℝ) :
    NormedSpace.exp ((u + v) • Y) = NormedSpace.exp (u • Y) * NormedSpace.exp (v • Y) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left u).smul_right v)

theorem duhamel_integrand_eq {p q : ℕ} (Y V : Mat p q) (s : ℝ) :
    NormedSpace.exp ((1 - s) • (Y + Y)) * V * NormedSpace.exp (s • (Y + Y)) =
      sandwichAct (NormedSpace.exp Y) V (NormedSpace.exp Y)
        (NormedSpace.exp ((1 - 2 * s) • adMat Y)) := by
  have hl : (1 - s) • (Y + Y) = ((1 : ℝ) + (1 - 2 * s)) • Y := by
    rw [← two_smul ℝ Y, smul_smul]; congr 1; ring
  have hr : s • (Y + Y) = (-(1 - 2 * s) + (1 : ℝ)) • Y := by
    rw [← two_smul ℝ Y, smul_smul]; congr 1; ring
  have hof : ∀ W : Mat p q, (Matrix.of fun a b => vecM W (a, b)) = W := fun W => by
    ext a b; rfl
  rw [hl, hr, exp_real_smul_add, exp_real_smul_add, one_smul, neg_smul]
  simp only [sandwichAct, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← adMat_real_smul, exp_adMat_mulVec, hof]
  simp only [Matrix.mul_assoc]

open scoped Matrix.Norms.Operator in
theorem integral_duhamel_eq_sAd {p q : ℕ} (Y V : Mat p q) :
    ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - s) • (Y + Y)) * V * NormedSpace.exp (s • (Y + Y)) =
      NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y := by
  let L : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →L[ℝ] Mat p q :=
    LinearMap.toContinuousLinearMap (sandwichAct (NormedSpace.exp Y) V (NormedSpace.exp Y))
  have hcont : Continuous fun s : ℝ => NormedSpace.exp ((1 - 2 * s) • adMat Y) :=
    NormedSpace.exp_continuous.comp ((by fun_prop : Continuous fun s : ℝ => 1 - 2 * s).smul
      continuous_const)
  have hsin : sinhcAd Y =
      ∑' k : ℕ, (((2 * k + 1).factorial : ℝ)⁻¹) • adMat Y ^ (2 * k) := by
    simp only [sinhcAd]
    congr 1
    funext k
    rw [← Complex.coe_smul]
    push_cast
    rfl
  calc ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - s) • (Y + Y)) * V * NormedSpace.exp (s • (Y + Y))
      = ∫ s in (0 : ℝ)..1, L (NormedSpace.exp ((1 - 2 * s) • adMat Y)) := by
        congr 1
        funext s
        exact duhamel_integrand_eq Y V s
    _ = L (∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - 2 * s) • adMat Y)) :=
        L.intervalIntegral_comp_comm (hcont.intervalIntegrable 0 1)
    _ = NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y := by
        have hI : ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - 2 * s) • adMat Y) = sinhcAd Y := by
          rw [hsin]
          exact integral_exp_one_sub_two_mul_smul _ (adMat Y)
        rw [hI]
        rfl

theorem hasDerivAt_exp_two_add_smul (p q : ℕ) (Y V : Mat p q) (a b : Ix p q) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + Y + t • V) a b)
      ((NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y) a b) 0 := by
  letI : NormedRing (Mat p q) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat p q) := Matrix.linftyOpNormedAlgebra
  have hD0 := GlobalTheory.hasDerivAt_exp_add_smul_duhamel (Mat p q) (Y + Y) V
  have hD : HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + Y + t • V))
      (NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y) 0 := by
    rw [← integral_duhamel_eq_sAd Y V]
    exact hD0
  let e : Mat p q →ₗ[ℝ] ℂ :=
    { toFun := fun M => M a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap e).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD

end GlobalTheory.PolarU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobianActionUpperRightBlockExpCoords
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem jac_exp_herm {p q : ℕ} (B : Fin p → Fin q → ℂ) :
    (NormedSpace.exp (pY B))ᴴ = NormedSpace.exp (pY B) := by
  rw [← Matrix.exp_conjTranspose, pY_conjTranspose]

theorem jac_exp_two {p q : ℕ} (B : Fin p → Fin q → ℂ) :
    NormedSpace.exp (pY B + pY B) = NormedSpace.exp (pY B) * NormedSpace.exp (pY B) := Matrix.exp_add_of_commute _ _ (Commute.refl _)

theorem jac_cancel {p q : ℕ} (B : Fin p → Fin q → ℂ) (X Z : Mat p q)
    (h : NormedSpace.exp (pY B) * X * NormedSpace.exp (pY B)
      = NormedSpace.exp (pY B) * Z * NormedSpace.exp (pY B)) : X = Z := by
  have hu := Matrix.isUnit_exp (pY B)
  exact hu.mul_left_cancel (hu.mul_right_cancel h)

theorem jac_block {p q : ℕ} (X Z : Fin p → Fin q → ℂ) (U : Matrix (Fin p) (Fin p) ℂ)
    (V : Matrix (Fin q) (Fin q) ℂ)
    (h : pY X = (Matrix.fromBlocks U 0 0 V : Mat p q)ᴴ * pY Z * Matrix.fromBlocks U 0 0 V) :
    Matrix.of X = Uᴴ * Matrix.of Z * V := by
  have h1 := congrArg Matrix.toBlocks₁₂ h
  simpa [pY, pOf, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_assoc] using h1

noncomputable def jacMul {m n : Type} [Fintype m] [Fintype n] (U : Matrix m m ℂ) (V : Matrix n n ℂ) :
    (m → n → ℂ) →ₗ[ℝ] (m → n → ℂ) where
  toFun Z := fun i j => (U * Matrix.of Z * V) i j
  map_add' Z W := by
    have : Matrix.of (Z + W) = Matrix.of Z + Matrix.of W := rfl
    rw [this, Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' t Z := by
    have : Matrix.of (t • Z) = t • Matrix.of Z := rfl
    rw [this, Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem of_jacMul {m n : Type} [Fintype m] [Fintype n] (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (Z : m → n → ℂ) : Matrix.of (jacMul U V Z) = U * Matrix.of Z * V := rfl

private theorem pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ {E : Type*} [AddCommGroup E] [Module ℝ E] (X Z : E)
    (h : X + X = Z + Z) : X = Z := by
  have h2 : (2 : ℝ) • X = (2 : ℝ) • Z := by rw [two_smul, two_smul]; exact h
  have h3 := congrArg (fun W => (1 / 2 : ℝ) • W) h2
  simpa [smul_smul] using h3

private theorem pY_injective {p q : ℕ} (X Z : Fin p → Fin q → ℂ) (h : pY X = pY Z) : X = Z := by
  funext i j
  have h1 := congrFun (congrFun (congrArg Matrix.toBlocks₁₂ h) i) j
  simpa [pY, pOf] using h1

private theorem conjTranspose_mul_mul_mul_eq_of_mul_eq {n : Type*} [Fintype n] [DecidableEq n] (g E F k X : Matrix n n ℂ)
    (hE : Eᴴ = E) (hF : Fᴴ = F) (h : E * g = k * F) :
    gᴴ * (E * X * E) * g = F * (kᴴ * X * k) * F := by
  have h1 : gᴴ * E = (E * g)ᴴ := by rw [Matrix.conjTranspose_mul, hE]
  calc gᴴ * (E * X * E) * g = (gᴴ * E) * X * (E * g) := by simp only [Matrix.mul_assoc]
    _ = (k * F)ᴴ * X * (k * F) := by rw [h1, h]
    _ = F * (kᴴ * X * k) * F := by rw [Matrix.conjTranspose_mul, hF]; simp only [Matrix.mul_assoc]

private theorem fromBlocks_unitary_conjTranspose_mul_self {p q : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (V : Matrix (Fin q) (Fin q) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin p) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin q) ℂ) :
    (Matrix.fromBlocks U 0 0 V)ᴴ * Matrix.fromBlocks U 0 0 V = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU hV
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hU, hV]

private theorem injective_of_det_ne_zero {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (h : LinearMap.det f ≠ 0) : Function.Injective f :=
  (LinearMap.equivOfDetNeZero f h).injective

private theorem conjTranspose_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hU
  exact hU

theorem jacobian_action_p : ∀ (p q : ℕ) (g : Mat p q) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous ψ → (∀ B, ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, NormedSpace.exp (pY B) * g = Matrix.fromBlocks U 0 0 V * NormedSpace.exp (pY (ψ B))) → (∀ B : Fin p → Fin q → ℂ, 0 < LinearMap.det (sP (pY B))) → (∀ B C : Fin p → Fin q → ℂ, sAd (pY B) (pY C) = pY (sP (pY B) C)) → (∀ B : Fin p → Fin q → ℂ, ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B)) → ∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * LinearMap.det (sP (pY (ψ B))) = LinearMap.det (sP (pY B)) := by
  intro p q g ψ hψ hK hdet hsAd hdiff B
  obtain ⟨A, hA, hAeq⟩ := hdiff (ψ B)
  obtain ⟨A0, hA0, hA0eq⟩ := hdiff B
  obtain ⟨U, hU, V, hV, hUV⟩ := hK B
  set L := LinearMap.toContinuousLinearMap (jacMul gᴴ g) with hL
  have hLapp : ∀ M, Matrix.of (L M) = gᴴ * Matrix.of M * g := fun M => of_jacMul gᴴ g M

  have hcomp : (fun y => (fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) (ψ y)) =
      fun y => L ((fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) y) := by
    funext y
    obtain ⟨U', hU', V', hV', hy⟩ := hK y
    have hmat : NormedSpace.exp (pY (ψ y) + pY (ψ y)) = gᴴ * NormedSpace.exp (pY y + pY y) * g := by
      have hs := conjTranspose_mul_mul_mul_eq_of_mul_eq g _ _ _ 1 (jac_exp_herm y) (jac_exp_herm (ψ y)) hy
      rw [Matrix.mul_one, Matrix.mul_one, fromBlocks_unitary_conjTranspose_mul_self U' V' hU' hV', Matrix.mul_one] at hs
      rw [jac_exp_two, jac_exp_two, hs]
    apply Matrix.of.injective
    rw [hLapp]
    exact hmat
  have hLd : HasFDerivAt (fun y => (fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) (ψ y))
      (L.comp A0) B := by
    rw [hcomp]
    exact L.hasFDerivAt.comp B hA0.hasFDerivAt
  have hinj : Function.Injective A := by
    intro C1 C2 h
    have h1 : Matrix.of (A C1) = Matrix.of (A C2) := by rw [h]
    rw [hAeq, hAeq] at h1
    have h2 := jac_cancel (ψ B) _ _ h1
    rw [← pY_add, ← pY_add, hsAd, hsAd] at h2
    exact pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ _ _ (injective_of_det_ne_zero _ (hdet (ψ B)).ne' (pY_injective _ _ h2))
  obtain ⟨P, hP, hPA⟩ := GlobalTheory.hasFDerivAt_of_comp_immersion (Fin p → Fin q → ℂ) (Ix p q → Ix p q → ℂ)
    (fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) ψ B A (L.comp A0) hA hinj
    hψ.continuousAt hLd
  refine ⟨P, hP, ?_⟩

  have hkey : ∀ C, sP (pY (ψ B)) (P C) = jacMul Uᴴ V (sP (pY B) C) := by
    intro C
    have h1 := congrArg (fun T : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ) => Matrix.of (T C)) hPA
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [hLapp, hAeq, hA0eq, conjTranspose_mul_mul_mul_eq_of_mul_eq g _ _ _ _ (jac_exp_herm B) (jac_exp_herm (ψ B)) hUV] at h1
    have h3 := jac_cancel (ψ B) _ _ h1
    rw [← pY_add, ← pY_add, hsAd, hsAd] at h3
    have h4 := jac_block _ _ U V h3
    rw [← of_jacMul] at h4
    have h5 := Matrix.of.injective h4
    simp only [map_add (f := _)] at h5
    exact pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ _ _ h5
  have hlin : (sP (pY (ψ B))).comp (P : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ)) =
      (jacMul Uᴴ V).comp (sP (pY B)) := LinearMap.ext hkey
  have hd := congrArg (fun T => |LinearMap.det T|) hlin
  simp only [LinearMap.det_comp, abs_mul] at hd
  rw [abs_det_unitary_mul_mul p q Uᴴ (conjTranspose_mem_unitaryGroup hU) V hV _ (of_jacMul Uᴴ V), one_mul,
    abs_of_pos (hdet (ψ B)), abs_of_pos (hdet B)] at hd
  show |LinearMap.det (P : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ))| * _ = _
  rw [mul_comm]
  exact hd

end GlobalTheory.PolarU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeNormPowerIntegrableOfBallVolume
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.powerIntegrability

theorem one_le_hsn {m : ℕ} {ε : Fin m → Bool} (hm : 1 ≤ m) (g : UJ ε) : 1 ≤ hsn (umat g) := by
  set a : Fin m := ⟨0, hm⟩
  have h : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h2 := congrFun (congrFun h a) a
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_apply_eq] at h2
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h2
  have hn : (1 : ℝ) ≤ ∑ l, ‖umat g l a‖ ^ 2 := by
    have e1 : ‖((if ε a = true then 1 else -1 : ℂ))‖ = 1 := by split_ifs <;> simp
    rw [← e1, ← h2]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp [sq]
  have hc : ∑ l, ‖umat g l a‖ ^ 2 ≤ ∑ l, ∑ b, ‖umat g l b‖ ^ 2 :=
    Finset.sum_le_sum fun l _ => Finset.single_le_sum (f := fun b => ‖umat g l b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a)
  unfold hsn
  exact Real.one_le_sqrt.mpr (hn.trans hc)

theorem continuous_hsn_umat {m : ℕ} (ε : Fin m → Bool) : Continuous fun g : UJ ε => hsn (umat g) := by
  unfold hsn
  have hu : Continuous fun g : UJ ε => umat g := Units.continuous_val.comp continuous_subtype_val
  refine Real.continuous_sqrt.comp ?_
  fun_prop

end GlobalTheory.SepReal.powerIntegrability

namespace GlobalTheory.SepReal.powerIntegrability

theorem const_le (m : ℕ) (hm : 1 ≤ m) : 2 * (33 : ℝ) ^ (2 * m ^ 2) ≤ Real.exp (10 * (m : ℝ) ^ 2) := by
  have hk : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  have e1 : Real.exp (10 * (m : ℝ) ^ 2) = Real.exp 10 ^ (m ^ 2) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have e10 : (2178 : ℝ) ≤ Real.exp 10 := by
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (2178 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h1.le 10
  have e2 : (33 : ℝ) ^ (2 * m ^ 2) = 1089 ^ (m ^ 2) := by rw [pow_mul]; norm_num
  rw [e1, e2]
  calc 2 * (1089 : ℝ) ^ (m ^ 2) ≤ 2 ^ (m ^ 2) * 1089 ^ (m ^ 2) := by
        gcongr; exact le_self_pow₀ (by norm_num) (by omega)
    _ = 2178 ^ (m ^ 2) := by rw [← mul_pow]; norm_num
    _ ≤ Real.exp 10 ^ (m ^ 2) := pow_le_pow_left₀ (by norm_num) e10 _

theorem term_le (m : ℕ) (A : ℝ) (hA : 4 * (m : ℝ) ^ 2 + 1 ≤ A) (j : ℕ) :
    ((2 : ℝ) ^ (-A)) ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2) ≤ 33 ^ (2 * m ^ 2) * (1 / 2) ^ j := by
  have h4 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  have hb : 1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4) ≤ 33 * 4 ^ j := by
    have : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * 4 ^ j := by
      rw [← pow_mul, pow_mul', show (2 : ℝ) ^ 2 = 4 by norm_num, pow_succ]; ring
    rw [this]; linarith
  have hr0 : 0 ≤ (2 : ℝ) ^ (-A) := by positivity
  have hq : (2 : ℝ) ^ (-A) * 4 ^ (2 * m ^ 2) ≤ 1 / 2 := by
    have e : (4 : ℝ) ^ (2 * m ^ 2) = (2 : ℝ) ^ ((4 * m ^ 2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    rw [e, ← Real.rpow_add (by norm_num)]
    calc (2 : ℝ) ^ (-A + ((4 * m ^ 2 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  calc ((2 : ℝ) ^ (-A)) ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)
      ≤ ((2 : ℝ) ^ (-A)) ^ j * (33 * 4 ^ j) ^ (2 * m ^ 2) := by
        gcongr
    _ = 33 ^ (2 * m ^ 2) * ((2 : ℝ) ^ (-A) * 4 ^ (2 * m ^ 2)) ^ j := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j]; ring
    _ ≤ 33 ^ (2 * m ^ 2) * (1 / 2) ^ j := by
        gcongr

end GlobalTheory.SepReal.powerIntegrability

namespace GlobalTheory.SepReal


open GlobalTheory.SepReal.powerIntegrability in
theorem powInt_of_volBall : VolBall → PowInt := by
  intro hV m ε A hm hA
  obtain ⟨-, hfin, -⟩ := hV m ε (1 / 4) 1 (by norm_num) one_pos
  set μN := muG ε (nbh ε (1 / 4)) with hμN
  set r : ℝ := (2 : ℝ) ^ (-A) with hr
  have hcont := continuous_hsn_umat ε
  have hpos : ∀ g : UJ ε, 0 < hsn (umat g) := fun g => lt_of_lt_of_le one_pos (one_le_hsn hm g)
  have hf_cont : Continuous fun g : UJ ε => hsn (umat g) ^ (-A) :=
    hcont.rpow_const fun g => Or.inl (hpos g).ne'
  have hf_nn : ∀ g : UJ ε, 0 ≤ hsn (umat g) ^ (-A) := fun g => (Real.rpow_pos_of_pos (hpos g) _).le
  let S : ℕ → Set (UJ ε) := fun j => {g | hsn (umat g) ≤ (2 : ℝ) ^ (j + 1)}
  have hS : ∀ j, MeasurableSet (S j) := fun j => measurableSet_le hcont.measurable measurable_const
  have hpt : ∀ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ≤ ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g := by
    intro g
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (one_le_hsn hm g) (one_lt_two : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem (show g ∈ S j from hj2.le)]
    apply ENNReal.ofReal_le_ofReal
    have key : r ^ j = ((2 : ℝ) ^ j) ^ (-A) := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num), mul_comm]
    rw [key]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hj1 (by linarith [sq_nonneg (m : ℝ)])
  have hL : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε ≤ ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN := by
    calc ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε
        ≤ ∫⁻ g, ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g ∂muG ε := lintegral_mono hpt
      _ = ∑' j, ∫⁻ g, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g ∂muG ε :=
          lintegral_tsum fun j => (measurable_const.indicator (hS j)).aemeasurable
      _ = ∑' j, ENNReal.ofReal (r ^ j) * muG ε (S j) := by
          congr 1; funext j; exact lintegral_indicator_const (hS j) _
      _ ≤ ∑' j, ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          have hb := (hV m ε (1 / 4) ((2 : ℝ) ^ (j + 1)) (by norm_num) (by positivity)).2.2
          calc ENNReal.ofReal (r ^ j) * muG ε (S j)
              ≤ ENNReal.ofReal (r ^ j) * (ENNReal.ofReal ((1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)) * μN) :=
                by gcongr
            _ = ENNReal.ofReal (r ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)) * μN := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            _ ≤ ENNReal.ofReal (33 ^ (2 * m ^ 2) * (1 / 2) ^ j) * μN := by
                exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (term_le m A hA j)) (zero_le')
            _ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by
                have h2 : ENNReal.ofReal ((1 / 2 : ℝ) ^ j) = 2⁻¹ ^ j := by
                  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
                rw [ENNReal.ofReal_mul (by positivity), h2]
      _ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * (∑' j : ℕ, (2⁻¹ : ENNReal) ^ j) * μN := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN := by
          rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat, mul_comm (2 : ENNReal)]
  have hLfin : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε < ⊤ :=
    lt_of_le_of_lt hL (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  have hnn : 0 ≤ᵐ[muG ε] fun g => hsn (umat g) ^ (-A) := Filter.Eventually.of_forall hf_nn
  refine ⟨⟨hf_cont.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hLfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf_cont.aestronglyMeasurable]
  calc (∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε).toReal
      ≤ (ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hL
    _ = 2 * 33 ^ (2 * m ^ 2) * μN.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    _ ≤ Real.exp (10 * (m : ℝ) ^ 2) * μN.toReal :=
        mul_le_mul_of_nonneg_right (const_le m hm) ENNReal.toReal_nonneg

end GlobalTheory.SepReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionSmooth
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SepReal.ProjSm

variable {m : ℕ}

theorem mem_iff (ε : Fin m → Bool) (g : Mat m) : g ∈ UJset ε ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := Iff.rfl

theorem mul_mem' {ε : Fin m → Bool} {g h : Mat m} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  rw [mem_iff] at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Formalism.REAL.Jm ε * (g * h) = hᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem one_mem' (ε : Fin m → Bool) : (1 : Mat m) ∈ UJset ε := by
  rw [mem_iff]; simp

theorem exp_mem {ε : Fin m → Bool} {X : Mat m} (hX : X ∈ lieOf (Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε := by
  have JJ := Formalism.REAL.Jm_mul_self ε
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  set Y : Mat m := t • X with hY
  have hYh : Yᴴ = Formalism.REAL.Jm ε * (-Y) * Formalism.REAL.Jm ε := by
    have : Xᴴ = -(Formalism.REAL.Jm ε * X) * Formalism.REAL.Jm ε := by
      have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
      calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, JJ, Matrix.mul_one]
        _ = _ := by rw [h1]
    rw [hY, Matrix.conjTranspose_smul, this]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_neg]
  have hc : NormedSpace.exp Yᴴ = Formalism.REAL.Jm ε * NormedSpace.exp (-Y) * Formalism.REAL.Jm ε := by
    have hJi : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv JJ
    have := Matrix.exp_conj (Formalism.REAL.Jm ε) (-Y) ⟨⟨_, _, JJ, JJ⟩, rfl⟩
    rw [hJi] at this
    rw [hYh, this]
  rw [mem_iff, ← Matrix.exp_conjTranspose, hc]
  have he : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel, NormedSpace.exp_zero]
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-Y) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp Y
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-Y) * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * NormedSpace.exp Y) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [JJ, Matrix.mul_one, he, Matrix.mul_one]

theorem list_mem {m : ℕ} {ε : Fin m → Bool} : ∀ l : List (Mat m), (∀ x ∈ l, x ∈ UJset ε) → l.prod ∈ UJset ε
  | [], _ => by simpa using one_mem' ε
  | a :: l, h => by
    rw [List.prod_cons]
    exact mul_mem' (h a (by simp)) (list_mem l fun x hx => h x (by simp [hx]))

theorem embH_list {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) : ∀ l : List (Mat n), embH e l.prod = (l.map (embH e)).prod
  | [] => by simp [embH_one]
  | a :: l => by rw [List.prod_cons, embH_mul, embH_list e l, List.map_cons, List.prod_cons]

variable {n : ℕ} {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}
  {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {π : Mat (n + 1) → (H →L[ℂ] H)} {σ : Mat n → (H' →L[ℂ] H')} {j : H' →L[ℂ] H} {P : H →L[ℂ] H'}

end GlobalTheory.SepReal.ProjSm
end
end

