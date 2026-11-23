module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetOnStableSubspaceConjTranspose
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.FlagMeas.DetAdj

lemma mul_basisMat_eq {n : ℕ} (V : Submodule ℂ (Fin n → ℂ)) {d : Type} [Fintype d] [DecidableEq d]
    (b : Module.Basis d ℂ V) (g : Matrix (Fin n) (Fin n) ℂ) (f : V →ₗ[ℂ] V)
    (hf : ∀ v : V, ((f v : V) : Fin n → ℂ) = g *ᵥ (v : Fin n → ℂ)) :
    g * Matrix.of (fun i j => (b j : Fin n → ℂ) i) =
      Matrix.of (fun i j => (b j : Fin n → ℂ) i) * LinearMap.toMatrix b b f := by
  ext i j
  have h1 : (g * Matrix.of (fun i j => (b j : Fin n → ℂ) i)) i j = (g *ᵥ (b j : Fin n → ℂ)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, ← hf]
  have h2 : ((f (b j) : V) : Fin n → ℂ) = ∑ k, b.repr (f (b j)) k • (b k : Fin n → ℂ) := by
    conv_lhs => rw [← b.sum_repr (f (b j))]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  rw [h2]
  simp [Matrix.mul_apply, LinearMap.toMatrix_apply, Finset.sum_apply, mul_comm]

theorem detOn_conjTranspose : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)),
    (∀ y ∈ V, g *ᵥ y ∈ V) → (∀ y ∈ V, gᴴ *ᵥ y ∈ V) →
      GlobalTheory.FlagMeas.detOn gᴴ V = GlobalTheory.FlagMeas.detOn g V := by
  intro n g V hg hgh
  have hg' : ∀ y ∈ V, Matrix.toLin' g y ∈ V := by simpa [Matrix.toLin'_apply] using hg
  have hgh' : ∀ y ∈ V, Matrix.toLin' gᴴ y ∈ V := by simpa [Matrix.toLin'_apply] using hgh
  unfold GlobalTheory.FlagMeas.detOn
  rw [dite_eq_left hgh', dite_eq_left hg']
  set f := (Matrix.toLin' g).restrict hg'
  set f' := (Matrix.toLin' gᴴ).restrict hgh'
  let b := Module.finBasis ℂ V
  set B : Matrix (Fin n) (Fin (Module.finrank ℂ V)) ℂ := Matrix.of (fun i j => (b j : Fin n → ℂ) i) with hB
  set A := LinearMap.toMatrix b b f
  set A' := LinearMap.toMatrix b b f'
  have h1 : g * B = B * A := mul_basisMat_eq V b g f (fun v => by simp [f, Matrix.toLin'_apply])
  have h2 : gᴴ * B = B * A' := mul_basisMat_eq V b gᴴ f' (fun v => by simp [f', Matrix.toLin'_apply])
  have hinj : Function.Injective B.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    have : B.col = fun j => (b j : Fin n → ℂ) := by ext j i; rfl
    rw [this]
    exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hG : (Bᴴ * B).det ≠ 0 := (Matrix.PosDef.conjTranspose_mul_self B hinj).det_pos.ne'
  have key : (Bᴴ * B) * A = A'ᴴ * (Bᴴ * B) := by
    calc (Bᴴ * B) * A = Bᴴ * (g * B) := by rw [h1, Matrix.mul_assoc]
      _ = (gᴴ * B)ᴴ * B := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = A'ᴴ * (Bᴴ * B) := by rw [h2, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hdet : A.det = star A'.det := by
    have := congrArg Matrix.det key
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_comm (star _)] at this
    exact mul_left_cancel₀ hG this
  rw [← LinearMap.det_toMatrix b f, ← LinearMap.det_toMatrix b f']
  change ‖A'.det‖ = ‖A.det‖
  rw [hdet, norm_star]

end GlobalTheory.FlagMeas.DetAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetUnitaryMulMul
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU


open Kronecker in
theorem abs_det_unitary_mul_mul : ∀ (p q : ℕ), ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∀ T : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ), (∀ B, Matrix.of (T B) = U * Matrix.of B * V) → |LinearMap.det T| = 1 := by
  classical
  intro p q U hU V hV T hT

  let e : (Fin p → Fin q → ℂ) ≃ₗ[ℂ] (Fin q → Fin p → ℂ) :=
    { toFun := fun B j i => B i j
      invFun := fun C i j => C j i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

  let L : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ) :=
    LinearMap.pi (fun j => (Matrix.toLin' U).comp (LinearMap.proj j))

  let R : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ) :=
    LinearMap.pi (fun i => (Matrix.toLin' Vᵀ).comp (LinearMap.proj i))
  let C : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ) :=
    ((e.symm : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ)) ∘ₗ L ∘ₗ
      (e.symm.symm : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ))) ∘ₗ R
  have hTC : T = C.restrictScalars ℝ := by
    apply LinearMap.ext
    intro B
    funext i j
    have h := congrFun (congrFun (hT B) i) j
    simp only [Matrix.of_apply] at h
    rw [h, Matrix.mul_assoc]
    simp [C, L, R, e, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hL : LinearMap.det L = U.det ^ q := by
    simp [L, LinearMap.det_pi, LinearMap.det_toLin']
  have hR : LinearMap.det R = V.det ^ p := by
    simp [R, LinearMap.det_pi, LinearMap.det_toLin', Matrix.det_transpose]
  have hC : LinearMap.det C = U.det ^ q * V.det ^ p := by
    simp only [C]
    rw [LinearMap.det_comp, LinearMap.det_conj L e.symm, hL, hR]
  have hu : ‖U.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)
  have hv : ‖V.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hV)
  rw [hTC, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, hC, map_mul, map_pow,
    map_pow, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hu, hv]
  simp

end GlobalTheory.PolarU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitP
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

variable {p q : ℕ}

def posMat (p q : ℕ) (f : Bool → ℕ → Bool → ℕ → ℂ) : Mat p q :=
  Matrix.of fun a b => f a.isLeft (posIx a) b.isLeft (posIx b)

theorem sum_ite_val {n : ℕ} (m : ℕ) (g : ℕ → ℂ) :
    (∑ j : Fin n, if m = (j : ℕ) then g j else 0) = if m < n then g m else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨m, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [if_neg]
      rintro rfl
      exact hb rfl
    · simp
  · refine Finset.sum_eq_zero fun j _ => if_neg ?_
    rintro rfl
    exact h j.2

theorem posIx_inl (i : Fin p) : posIx (Sum.inl i : Ix p q) = i := rfl

theorem posIx_inr (j : Fin q) : posIx (Sum.inr j : Ix p q) = j := rfl

theorem aOf_apply (h : ℕ → ℝ) (a b : Ix p q) :
    aOf p q h a b = if a.isLeft = b.isLeft then 0
      else if posIx a = posIx b then ((h (posIx a) : ℝ) : ℂ) else 0 := by
  rcases a with i | i <;> rcases b with j | j <;> by_cases hij : (i : ℕ) = j <;>
    simp [aOf, pOf, posIx_inl, posIx_inr, hij, eq_comm (a := (j : ℕ))]

theorem aOf_symm (h : ℕ → ℝ) (a b : Ix p q) : aOf p q h a b = aOf p q h b a := by
  rw [aOf_apply, aOf_apply]
  by_cases h1 : a.isLeft = b.isLeft
  · simp [h1]
  · by_cases h2 : posIx a = posIx b
    · simp [h1, Ne.symm h1, h2]
    · simp [h1, Ne.symm h1, h2, Ne.symm h2]

theorem sum_aOf (h : ℕ → ℝ) (a : Ix p q) (g : Bool → ℕ → ℂ) :
    ∑ c, aOf p q h a c * g c.isLeft (posIx c)
      = (cutH p q h (posIx a) : ℂ) * g (!a.isLeft) (posIx a) := by
  rw [Fintype.sum_sum_type]
  rcases a with i | i
  · have h1 : ∀ k : Fin p, aOf p q h (Sum.inl i) (Sum.inl k) = 0 := fun k => by simp [aOf_apply]
    have h2 : ∀ k : Fin q, aOf p q h (Sum.inl i) (Sum.inr k) * g false k
        = if (i : ℕ) = k then ((h i : ℝ) : ℂ) * g false k else 0 := fun k => by
      by_cases hk : (i : ℕ) = k <;> simp [aOf_apply, posIx_inl, posIx_inr, hk]
    simp only [h1, posIx_inl, posIx_inr, Sum.isLeft_inl, Sum.isLeft_inr, h2, zero_mul,
      Finset.sum_const_zero, zero_add, Bool.not_true]
    rw [sum_ite_val (n := q) i (fun m => ((h i : ℝ) : ℂ) * g false m)]
    by_cases hi : (i : ℕ) < q <;> simp [cutH, hi]
  · have h1 : ∀ k : Fin q, aOf p q h (Sum.inr i) (Sum.inr k) = 0 := fun k => by simp [aOf_apply]
    have h2 : ∀ k : Fin p, aOf p q h (Sum.inr i) (Sum.inl k) * g true k
        = if (i : ℕ) = k then ((h i : ℝ) : ℂ) * g true k else 0 := fun k => by
      by_cases hk : (i : ℕ) = k <;> simp [aOf_apply, posIx_inl, posIx_inr, hk]
    simp only [h1, posIx_inl, posIx_inr, Sum.isLeft_inl, Sum.isLeft_inr, h2, zero_mul,
      Finset.sum_const_zero, add_zero, Bool.not_false]
    rw [sum_ite_val (n := p) i (fun m => ((h i : ℝ) : ℂ) * g true m)]
    by_cases hi : (i : ℕ) < p <;> simp [cutH, hi]

theorem ad_aOf_posMat (h : ℕ → ℝ) (f : Bool → ℕ → Bool → ℕ → ℂ) :
    aOf p q h * posMat p q f - posMat p q f * aOf p q h
      = posMat p q fun s m t n =>
        (cutH p q h m : ℂ) * f (!s) m t n - (cutH p q h n : ℂ) * f s m (!t) n := by
  ext a b
  simp only [Matrix.sub_apply, Matrix.mul_apply, posMat, Matrix.of_apply]
  rw [sum_aOf h a (fun s m => f s m b.isLeft (posIx b)),
    ← sum_aOf h b (fun t n => f a.isLeft (posIx a) t n)]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comm, aOf_symm]

theorem eigP_eq_posMat (ab : PIx p q) :
    eigP ab.1 = vecM (posMat p q fun s m t n =>
      if s ≠ t ∧ m = posIx ab.1.1 ∧ n = posIx ab.1.2 then
        (if ab.1.1.isLeft then 1 else if s then -1 else 1) else 0) := by
  obtain ⟨⟨a, b⟩, hab⟩ := ab
  funext ⟨c, d⟩
  rcases a with i | i <;> rcases b with j | j <;> simp only [sameBlock, not_true] at hab <;>
    rcases c with k | k <;> rcases d with l | l <;>
    simp [eigP, vecM, posMat, posIx_inl, posIx_inr, sameBlock, Fin.ext_iff]
  split_ifs <;> rfl

theorem adMat_sq_mulVec_eigP (p q : ℕ) (h : ℕ → ℝ) (ab : PIx p q) :
    (adMat (aOf p q h) ^ 2) *ᵥ eigP ab.1 = (((rootP h ab.1 : ℝ) : ℂ) ^ 2) • eigP ab.1 := by
  rw [pow_two (adMat _), ← Matrix.mulVec_mulVec, eigP_eq_posMat, adMat_mulVec, ad_aOf_posMat,
    adMat_mulVec, ad_aOf_posMat]
  funext ⟨c, d⟩
  simp only [vecM, posMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, rootP, Bool.not_not]
  generalize c.isLeft = s
  generalize d.isLeft = t
  generalize ab.1.1.isLeft = u
  by_cases hm : posIx c = posIx ab.1.1 ∧ posIx d = posIx ab.1.2
  · rw [hm.1, hm.2]
    cases s <;> cases t <;> cases u <;> simp <;> ring
  · simp [hm]

end GlobalTheory.PolarU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockPartitionOfEqTwoBlock
section
noncomputable section

open Matrix Formalism.L2.DIV

namespace GlobalTheory.ParIndex

variable {κ : Type} [CommRing κ] {n r : ℕ}

def parSub (hr : r ≤ n) (H : Subgroup (GL (Fin r) κ)) : Subgroup (GL (Fin n) κ) where
  carrier := {g | g ∈ blockTri (blk2 r) ∧ upperLeftBlock hr g ∈ H}
  one_mem' := ⟨Subgroup.one_mem _, by
    show ext1 (blockTri (blk2 r)) (blkR hr) 1 ∈ H
    rw [blockDiagonalExtendByOnePrimeField_one]; exact Subgroup.one_mem _⟩
  mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
    show ext1 (blockTri (blk2 r)) (blkR hr) (x * y) ∈ H
    rw [extendMatrixByIdentityAlongIndices_mul _ hx.1 hy.1]; exact Subgroup.mul_mem _ hx.2 hy.2⟩
  inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by
    show ext1 (blockTri (blk2 r)) (blkR hr) x⁻¹ ∈ H
    rw [extendOne_inv _ hx.1]; exact Subgroup.inv_mem _ hx.2⟩

theorem mem_parSub {hr : r ≤ n} {H : Subgroup (GL (Fin r) κ)} {g : GL (Fin n) κ} :
    g ∈ parSub hr H ↔ g ∈ blockTri (blk2 r) ∧ upperLeftBlock hr g ∈ H := Iff.rfl

theorem blockPartitionOf_eq_twoBlock {t : ℕ} (hn : n = r + t) : (blkOf r t : Fin n → ℕ) = blk2 r := by
  funext a
  unfold blkOf blk2
  split_ifs with h
  · rfl
  · have : (a.val - r) / t = 0 := Nat.div_eq_of_lt (by have := a.2; omega)
    rw [this]

theorem blockTri_blkOf_eq {t : ℕ} (hn : n = r + t) :
    blockTri (κ := κ) (n := n) (blkOf r t) = blockTri (blk2 r) := by
  rw [blockPartitionOf_eq_twoBlock hn]

end GlobalTheory.ParIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPolarCoordinatesJacobian
section
noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem continuous_sinhc_series {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    Continuous fun x : A => ∑' k : ℕ, (((2 * k + 1).factorial : ℂ)⁻¹) • x ^ (2 * k) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  set R : ℝ := ‖x₀‖ + 1
  have hball : Metric.ball x₀ 1 ∈ nhds x₀ := Metric.ball_mem_nhds x₀ one_pos
  refine ContinuousOn.continuousAt ?_ hball
  have hsum : Summable fun k : ℕ => ((2 * k + 1).factorial : ℝ)⁻¹ * (‖(1 : A)‖ + R ^ (2 * k)) := by
    have h1 : Summable fun n : ℕ => R ^ n / (n.factorial : ℝ) := Real.summable_pow_div_factorial R
    have h2 : Summable fun k : ℕ => R ^ (2 * k) / ((2 * k).factorial : ℝ) := by
      have := h1.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simp only at h; omega)
      simpa only [Function.comp_def] using this
    have h3 : Summable fun n : ℕ => (1 : ℝ) ^ n / (n.factorial : ℝ) := Real.summable_pow_div_factorial 1
    have h4 : Summable fun k : ℕ => ((2 * k + 1).factorial : ℝ)⁻¹ := by
      have := h3.comp_injective (i := fun k : ℕ => 2 * k + 1) (fun a b h => by simp only at h; omega)
      simpa only [Function.comp_def, one_pow, one_div] using this
    refine (((h4.mul_left ‖(1 : A)‖)).add h2).of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    rw [mul_add, mul_comm _ ‖(1 : A)‖]
    gcongr
    have hf : ((2 * k).factorial : ℝ) ≤ ((2 * k + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hp : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hp hf) (by positivity)
  refine continuousOn_tsum (fun k => (continuous_const.smul (continuous_pow _)).continuousOn) hsum ?_
  intro k x hx
  have hxR : ‖x‖ ≤ R := by
    have := Metric.mem_ball.1 hx
    have h := norm_le_norm_add_norm_sub' x x₀
    rw [dist_eq_norm] at this
    simp only [R]; linarith
  have hpow : ‖x ^ (2 * k)‖ ≤ ‖(1 : A)‖ + R ^ (2 * k) := by
    rcases Nat.eq_zero_or_pos (2 * k) with h | h
    · rw [h, pow_zero, pow_zero]; linarith [norm_nonneg (1 : A)]
    · calc ‖x ^ (2 * k)‖ ≤ ‖x‖ ^ (2 * k) := norm_pow_le' x h
        _ ≤ R ^ (2 * k) := pow_le_pow_left₀ (norm_nonneg x) hxR _
        _ ≤ ‖(1 : A)‖ + R ^ (2 * k) := le_add_of_nonneg_left (norm_nonneg _)
  calc ‖(((2 * k + 1).factorial : ℂ)⁻¹) • x ^ (2 * k)‖
      ≤ ‖(((2 * k + 1).factorial : ℂ)⁻¹)‖ * ‖x ^ (2 * k)‖ := norm_smul_le _ _
    _ = ((2 * k + 1).factorial : ℝ)⁻¹ * ‖x ^ (2 * k)‖ := by rw [norm_inv, Complex.norm_natCast]
    _ ≤ ((2 * k + 1).factorial : ℝ)⁻¹ * (‖(1 : A)‖ + R ^ (2 * k)) := by gcongr

theorem continuous_adMat (p q : ℕ) : Continuous (adMat : Mat p q → _) := by
  unfold adMat
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  exact ((continuous_apply_apply a.1 b.1).mul continuous_const).sub
    (continuous_const.mul (continuous_apply_apply b.2 a.2))

open scoped Matrix.Norms.Operator in
theorem continuous_sinhcAd (p q : ℕ) : Continuous (sinhcAd : Mat p q → _) := by
  unfold sinhcAd
  exact continuous_sinhc_series.comp (continuous_adMat p q)

theorem continuous_polJ : ∀ (p q : ℕ), Continuous (polJ : Mat p q → ℝ) := by
  intro p q
  unfold polJ
  exact Complex.continuous_re.comp
    (((continuous_sinhcAd p q).matrix_submatrix _ _).matrix_det)

end GlobalTheory.PolarU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedActionsAdjointCasimirSymmetricStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derived_actions_adjoint_casimir_symmetric : ∀ (p q : ℕ) (T : GrpData p q) (πU : URep T) (V₁ V₂ : Type) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V₁) (a₂ : Mat p q →ₗ[ℂ] Module.End ℂ V₂) (E₁ : V₁ →ₗ[ℂ] πU.H) (E₂ : V₂ →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E₁ x)) (E₁ (a₁ Y x)) 0) → (∀ Y ∈ upq p q, ∀ y, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E₂ y)) (E₂ (a₂ Y y)) 0) → (∀ Z x y, inner ℂ (E₁ (a₁ Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (a₂ (adjZ Z) y))) ∧ ∀ x y, inner ℂ (E₁ (casimir a₁ x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (casimir a₂ y)) := by
  first | exact @GlobalTheory.FockTensor.derived_adjoint_and_casimir | exact GlobalTheory.FockTensor.derived_adjoint_and_casimir | (intros; apply GlobalTheory.FockTensor.derived_adjoint_and_casimir <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetAdSqEigenvectorMatrixUnitPNeZero
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU


open scoped ComplexOrder in
theorem det_ne_zero_of_add_conjTranspose {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (h : P + Pᴴ = (2 : ℂ) • (1 : Matrix n n ℂ)) : P.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0

  have hquad : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 2 * (star v ⬝ᵥ v) := by
    rw [h]
    first
      | simp [smul_mulVec, dotProduct_smul, smul_eq_mul]
      | simp [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
      | simp [dotProduct_smul, smul_eq_mul]

  have hzero : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 0 := by
    have hstar : star v ᵥ* Pᴴ = star (P *ᵥ v) := (star_mulVec P v).symm
    rw [add_mulVec, dotProduct_add, dotProduct_mulVec (star v) Pᴴ v, hstar, hv]
    simp
  have hnorm : star v ⬝ᵥ v = 0 := by
    have h2 : (2 : ℂ) * (star v ⬝ᵥ v) = 0 := hquad.symm.trans hzero
    rcases mul_eq_zero.mp h2 with h2 | h2
    · norm_num at h2
    · exact h2
  exact dotProduct_star_self_eq_zero.mp hnorm

private lemma isLeft_ne_of_posIx_eq {p q : ℕ} (x y : Ix p q × Ix p q) (hx : ¬ sameBlock x.1 x.2)
    (hy : ¬ sameBlock y.1 y.2) (hne : y ≠ x) (h1 : posIx y.1 = posIx x.1)
    (h2 : posIx y.2 = posIx x.2) : x.1.isLeft ≠ y.1.isLeft := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rcases x1 with i | i <;> rcases x2 with j | j <;> rcases y1 with k | k <;> rcases y2 with l | l <;>
    simp_all [sameBlock, posIx, Fin.ext_iff]

private lemma eigP_add_star_eigP_eq_zero {p q : ℕ} (x y : Ix p q × Ix p q) (hx : ¬ sameBlock x.1 x.2)
    (hy : ¬ sameBlock y.1 y.2) (hne : y ≠ x) : eigP x y + star (eigP y x) = 0 := by
  unfold eigP
  rw [if_neg hne, if_neg (Ne.symm hne)]
  by_cases h : posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2
  · have c1 : ¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2 := ⟨hy, h⟩
    have c2 : ¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2 :=
      ⟨hx, h.1.symm, h.2.symm⟩
    rw [if_pos c1, if_pos c2]
    have hL := isLeft_ne_of_posIx_eq x y hx hy hne h.1 h.2
    generalize x.1.isLeft = s at hL ⊢
    generalize y.1.isLeft = t at hL ⊢
    cases s <;> cases t <;> simp at hL ⊢
  · have c1 : ¬ (¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2) :=
      fun h' => h ⟨h'.2.1, h'.2.2⟩
    have c2 : ¬ (¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2) :=
      fun h' => h ⟨h'.2.1.symm, h'.2.2.symm⟩
    rw [if_neg c1, if_neg c2]
    simp

theorem eigenvectorMatrix_add_star {p q : ℕ} (ab cd : PIx p q) :
    eigP ab.1 cd.1 + star (eigP cd.1 ab.1) = if cd = ab then 2 else 0 := by
  by_cases hc : cd = ab
  · subst hc
    rw [if_pos rfl]
    norm_num [eigP]
  · rw [if_neg hc]
    exact eigP_add_star_eigP_eq_zero ab.1 cd.1 ab.2 cd.2 (fun h => hc (Subtype.ext h))

theorem det_eigenvectorMatrix_ne_zero :
    ∀ (p q : ℕ), (Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1).det ≠ 0 := by
  intro p q
  apply det_ne_zero_of_add_conjTranspose
  ext cd ab
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [eigenvectorMatrix_add_star]
  split_ifs <;> norm_num

end GlobalTheory.PolarU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbLEqEmbOptL
section
noncomputable section

namespace GlobalTheory.PackLoc

def embOpt {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (h : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => h i j
    | none, none => 1
    | _, _ => 0

def embOptL {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (X : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => X i j
    | _, _ => 0

theorem embH_eq_embOpt {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (h : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepReal.embH e h = embOpt e h := rfl

theorem embL_eq_embOptL {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (X : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepReal.embL e X = embOptL e X := rfl

theorem embOpt_one {m N : ℕ} (e : Option (Fin m) ≃ Fin N) : embOpt e 1 = 1 := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt, Matrix.one_apply]

end GlobalTheory.PackLoc

end
end

