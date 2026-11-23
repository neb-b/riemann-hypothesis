module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusMul
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem ballMat_ballPt (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ) (τ : Ψ) :
    ballMat q (ballPt q W) τ = (W τ)ᵀ := by
  ext a b
  simp [ballMat, ballPt]

theorem sgI_form (a : Fin j → ℂ) (b : Fin j' → ℂ) :
    star (Sum.elim a b : Sg j j' → ℂ) ⬝ᵥ (sgI j j' *ᵥ Sum.elim a b) = star a ⬝ᵥ a - star b ⬝ᵥ b := by
  simp [sgI, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def, sub_eq_add_neg,
    neg_mulVec, Finset.sum_neg_distrib]

theorem form_mulVec {v : Matrix (Sg j j') (Sg j j') ℂ} (hv : IsSgU v) (z : Sg j j' → ℂ) :
    star (v *ᵥ z) ⬝ᵥ (sgI j j' *ᵥ (v *ᵥ z)) = star z ⬝ᵥ (sgI j j' *ᵥ z) := by
  have hv' : vᴴ * sgI j j' * v = sgI j j' := hv
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hv']

theorem norm_lt_of_ball {W : Matrix (Fin j') (Fin j) ℂ} (hW : (1 - (Wᵀ)ᴴ * Wᵀ).PosDef) {y : Fin j' → ℂ}
    (hy : y ≠ 0) : (star (Wᴴ *ᵥ y) ⬝ᵥ (Wᴴ *ᵥ y)).re < (star y ⬝ᵥ y).re := by
  have hc : star y ≠ 0 := by simpa using hy
  have h := hW.dotProduct_mulVec_pos hc
  have hw : Wᵀ *ᵥ star y = star (Wᴴ *ᵥ y) := by
    rw [star_mulVec, conjTranspose_conjTranspose, mulVec_transpose]
  have e : star (star y) ⬝ᵥ ((1 - (Wᵀ)ᴴ * Wᵀ) *ᵥ star y) =
      star y ⬝ᵥ y - star (Wᴴ *ᵥ y) ⬝ᵥ (Wᴴ *ᵥ y) := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hw, dotProduct_sub, star_star, dotProduct_comm y (star y)]
    congr 1
    rw [dotProduct_mulVec, vecMul_conjTranspose, hw, star_star, dotProduct_comm]
  rw [e] at h
  have := (Complex.lt_def.1 h).1
  simpa using this

theorem isUnit_det_P {v : Matrix (Sg j j') (Sg j j') ℂ} (hv : IsSgU v) {W : Matrix (Fin j') (Fin j) ℂ}
    (hW : (1 - (Wᵀ)ᴴ * Wᵀ).PosDef) : IsUnit (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det := by
  by_contra hne
  have h0 : (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det = 0 := by simpa using hne
  obtain ⟨x, hx, hPx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hz : v *ᵥ Sum.elim x (W *ᵥ x) =
      Sum.elim (0 : Fin j → ℂ) ((v.toBlocks₂₁ + v.toBlocks₂₂ * W) *ᵥ x) := by
    conv_lhs => rw [← fromBlocks_toBlocks v]
    rw [fromBlocks_mulVec]
    have h1 : v.toBlocks₁₁ *ᵥ x + v.toBlocks₁₂ *ᵥ (W *ᵥ x) = 0 := by
      rw [← hPx, add_mulVec, mulVec_mulVec]
    show Sum.elim (v.toBlocks₁₁ *ᵥ x + v.toBlocks₁₂ *ᵥ (W *ᵥ x))
      (v.toBlocks₂₁ *ᵥ x + v.toBlocks₂₂ *ᵥ (W *ᵥ x)) = _
    rw [h1, add_mulVec, mulVec_mulVec]
  have hen := form_mulVec hv (Sum.elim x (W *ᵥ x))
  rw [hz, sgI_form, sgI_form] at hen
  set y := W *ᵥ x with hy
  set Qx := (v.toBlocks₂₁ + v.toBlocks₂₂ * W) *ᵥ x
  have hxx : 0 < (star x ⬝ᵥ x).re := by
    have := (Complex.lt_def.1 (dotProduct_star_self_pos_iff.2 hx)).1
    simpa using this
  have hQ : 0 ≤ (star Qx ⬝ᵥ Qx).re := (Complex.le_def.1 (dotProduct_star_self_nonneg Qx)).1
  have hre := congrArg Complex.re hen
  simp only [Complex.sub_re, star_zero, dotProduct_zero, Complex.zero_re] at hre
  have hyy : (star x ⬝ᵥ x).re ≤ (star y ⬝ᵥ y).re := by linarith
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hyy
    simp at hyy
    linarith
  have hlt := norm_lt_of_ball hW hy0
  set w := Wᴴ *ᵥ y with hw
  have hnn : 0 ≤ (star (x - w) ⬝ᵥ (x - w)).re :=
    (Complex.le_def.1 (dotProduct_star_self_nonneg (x - w))).1
  have h1 : star x ⬝ᵥ w = star y ⬝ᵥ y := by
    rw [hw, dotProduct_mulVec, hy, star_mulVec]
  have h2 : star w ⬝ᵥ x = star y ⬝ᵥ y := by
    rw [hw, star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have hexp : star (x - w) ⬝ᵥ (x - w) = star x ⬝ᵥ x - star x ⬝ᵥ w - star w ⬝ᵥ x + star w ⬝ᵥ w := by
    simp only [star_sub, sub_dotProduct, dotProduct_sub]
    ring
  rw [hexp, h1, h2] at hnn
  simp only [Complex.add_re, Complex.sub_re] at hnn
  linarith

theorem moebW_mul (u v : Matrix (Sg j j') (Sg j j') ℂ) (W : Matrix (Fin j') (Fin j) ℂ)
    (hP : IsUnit (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det) :
    moebW (u * v) W = moebW u (moebW v W) := by
  set P := v.toBlocks₁₁ + v.toBlocks₁₂ * W with hPd
  set Q := v.toBlocks₂₁ + v.toBlocks₂₂ * W with hQd
  have hPP : P⁻¹ * P = 1 := nonsing_inv_mul _ hP
  have hPP' : P * P⁻¹ = 1 := mul_nonsing_inv _ hP
  have hv : moebW v W = Q * P⁻¹ := rfl
  have huv : u * v = fromBlocks
      (u.toBlocks₁₁ * v.toBlocks₁₁ + u.toBlocks₁₂ * v.toBlocks₂₁)
      (u.toBlocks₁₁ * v.toBlocks₁₂ + u.toBlocks₁₂ * v.toBlocks₂₂)
      (u.toBlocks₂₁ * v.toBlocks₁₁ + u.toBlocks₂₂ * v.toBlocks₂₁)
      (u.toBlocks₂₁ * v.toBlocks₁₂ + u.toBlocks₂₂ * v.toBlocks₂₂) := by
    rw [← fromBlocks_multiply, fromBlocks_toBlocks, fromBlocks_toBlocks]
  have e1 : (u * v).toBlocks₁₁ + (u * v).toBlocks₁₂ * W =
      (u.toBlocks₁₁ + u.toBlocks₁₂ * (Q * P⁻¹)) * P := by
    have hr : (u.toBlocks₁₁ + u.toBlocks₁₂ * (Q * P⁻¹)) * P = u.toBlocks₁₁ * P + u.toBlocks₁₂ * Q := by
      rw [Matrix.add_mul, Matrix.mul_assoc u.toBlocks₁₂, Matrix.mul_assoc Q, hPP, Matrix.mul_one]
    rw [hr, huv, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, hPd, hQd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  have e2 : (u * v).toBlocks₂₁ + (u * v).toBlocks₂₂ * W =
      (u.toBlocks₂₁ + u.toBlocks₂₂ * (Q * P⁻¹)) * P := by
    have hr : (u.toBlocks₂₁ + u.toBlocks₂₂ * (Q * P⁻¹)) * P = u.toBlocks₂₁ * P + u.toBlocks₂₂ * Q := by
      rw [Matrix.add_mul, Matrix.mul_assoc u.toBlocks₂₂, Matrix.mul_assoc Q, hPP, Matrix.mul_one]
    rw [hr, huv, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hPd, hQd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [hv]
  unfold moebW
  rw [e1, e2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul]

theorem moebBall_mul : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → ∀ t ∈ ballDom q, moebBall q (fun τ => u τ * v τ) t = moebBall q u (moebBall q v t) := by
  intro Ψ _ j j' n q u v hu hv t ht
  unfold moebBall
  congr 1
  funext τ
  rw [ballMat_ballPt, transpose_transpose]
  refine moebW_mul _ _ _ (isUnit_det_P (hv τ) ?_)
  simpa using ht τ

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusTransitive
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Boost

section Blocks

open scoped MatrixOrder

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem exists_congr_one {A : Matrix a a ℂ} (hA : A.PosDef) : ∃ X : Matrix a a ℂ, Xᴴ * A * X = 1 ∧ IsUnit X.det := by
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  have hs : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  obtain ⟨C, hCA⟩ : ∃ C : Matrix a a ℂ, A = Cᴴ * C :=
    ⟨CFC.sqrt A, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self A h0]⟩
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit
  have hC : IsUnit C.det := by
    rw [hCA, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  have h1 : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hC
  refine ⟨C⁻¹, ?_, ?_⟩
  · calc (C⁻¹)ᴴ * A * C⁻¹ = (C * C⁻¹)ᴴ * (C * C⁻¹) := by
          rw [hCA, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp
  · exact (Matrix.isUnit_nonsing_inv_det_iff).2 hC

theorem posDef_one_sub_swap {W : Matrix b a ℂ} (h : (1 - W * Wᴴ).PosDef) : (1 - Wᴴ * W).PosDef := by
  set B := 1 - W * Wᴴ with hB
  have hBu : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBu
  have hP : (1 + Wᴴ * B⁻¹ * W).PosDef :=
    Matrix.PosDef.one.add_posSemidef (h.inv.posSemidef.conjTranspose_mul_mul_same W)
  have hinv : (1 + Wᴴ * B⁻¹ * W) * (1 - Wᴴ * W) = 1 := by
    have e2 : W * Wᴴ = 1 - B := by rw [hB]; abel
    have e : Wᴴ * B⁻¹ * W * (Wᴴ * W) = Wᴴ * B⁻¹ * (W * Wᴴ) * W := by simp only [Matrix.mul_assoc]
    have e3 : Wᴴ * B⁻¹ * (1 - B) * W = Wᴴ * B⁻¹ * W - Wᴴ * W := by
      have hBi' : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBu
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc (Wᴴ) (B⁻¹) B, hBi', Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, e, e2, e3]
    abel
  have : (1 - Wᴴ * W) = (1 + Wᴴ * B⁻¹ * W)⁻¹ := (Matrix.inv_eq_right_inv hinv).symm
  rw [this]
  exact hP.inv

theorem exists_boost {W : Matrix b a ℂ} (h : (1 - W * Wᴴ).PosDef) :
    ∃ u : Matrix (a ⊕ b) (a ⊕ b) ℂ,
      uᴴ * fromBlocks 1 0 0 (-1) * u = fromBlocks 1 0 0 (-1) ∧ u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ = W := by
  obtain ⟨X, hX, hXu⟩ := exists_congr_one (posDef_one_sub_swap h)
  obtain ⟨Y, hY, -⟩ := exists_congr_one h
  refine ⟨fromBlocks X (Wᴴ * Y) (W * X) Y, ?_, ?_⟩
  · have e11 : Xᴴ * X - Xᴴ * Wᴴ * (W * X) = 1 := by
      rw [← hX, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    have e22 : Yᴴ * W * (Wᴴ * Y) - Yᴴ * Y = -1 := by
      rw [← hY, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.mul_neg, add_zero, zero_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.neg_mul]
    congr 1
    · simp only [Matrix.mul_assoc, add_neg_cancel]
    · simp only [Matrix.mul_assoc, add_neg_cancel]
  · have : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hXu
    simp only [Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁]
    rw [Matrix.mul_assoc, this, Matrix.mul_one]

end Blocks

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Boost

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem moebBall_transitive : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ), t ∈ ballDom q → ∃ u : Ψ → Matrix (Sg j j') (Sg j j') ℂ, (∀ τ, IsSgU (u τ)) ∧ moebBall q u 0 = t := by
  intro Ψ _ j j' n q t ht
  have hW : ∀ τ, (1 - (ballMat q t τ)ᵀ * ((ballMat q t τ)ᵀ)ᴴ).PosDef := by
    intro τ
    have h := (ht τ).transpose
    have e : (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᵀ = 1 - (ballMat q t τ)ᵀ * ((ballMat q t τ)ᵀ)ᴴ := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul]
      congr 2
    rwa [e] at h
  choose u hu hm using fun τ => Boost.exists_boost (hW τ)
  refine ⟨u, hu, ?_⟩
  have h0 : ∀ τ, moebW (u τ) (ballMat q 0 τ)ᵀ = (ballMat q t τ)ᵀ := by
    intro τ
    have hz : ballMat q 0 τ = 0 := by
      ext a b
      simp [ballMat]
    rw [hz, moebW, Matrix.transpose_zero, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
    exact hm τ
  funext k
  simp only [moebBall, ballPt, h0]
  simp [ballMat]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroContinuous
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

open Matrix GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem IsSgU.det_toBlocks₁₁_ne_zero {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) :
    u.toBlocks₁₁.det ≠ 0 := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, u = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks u).symm⟩
  rw [toBlocks_fromBlocks₁₁]
  unfold IsSgU sgI at hu
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at hu
  have h := (fromBlocks_inj.1 hu).1
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg] at h
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have h1 : -(Cᴴ *ᵥ (C *ᵥ v)) = v := by
    have h2 := congrArg (fun M => M *ᵥ v) h
    simp only [Matrix.add_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, hAv,
      Matrix.mulVec_zero, zero_add] at h2
    exact h2
  have h3 : star v ⬝ᵥ v = -(star (C *ᵥ v) ⬝ᵥ (C *ᵥ v)) := by
    calc star v ⬝ᵥ v = star v ⬝ᵥ (-(Cᴴ *ᵥ (C *ᵥ v))) := by rw [h1]
      _ = -(star (C *ᵥ v) ⬝ᵥ (C *ᵥ v)) := by
        rw [dotProduct_neg, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have h4 : 0 ≤ star v ⬝ᵥ v := dotProduct_star_self_nonneg v
  have h5 : 0 ≤ star (C *ᵥ v) ⬝ᵥ (C *ᵥ v) := dotProduct_star_self_nonneg _
  have h6 : star v ⬝ᵥ v = 0 := le_antisymm (by rw [h3]; exact neg_nonpos.2 h5) h4
  exact hv (dotProduct_star_self_eq_zero.1 h6)

theorem moebW_zero (u : Matrix (Sg j j') (Sg j j') ℂ) : moebW u 0 = u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ := by
  simp [moebW]

theorem continuous_matrix_inv {X m : Type} [TopologicalSpace X] [Fintype m] [DecidableEq m]
    {A : X → Matrix m m ℂ} (hA : Continuous A) (hd : ∀ x, (A x).det ≠ 0) :
    Continuous fun x => (A x)⁻¹ := by
  have h : (fun x => (A x)⁻¹) = fun x => ((A x).det)⁻¹ • (A x).adjugate := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hA.matrix_det.inv₀ hd).smul hA.matrix_adjugate

theorem continuous_moebBall_zero (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (X : Type) [TopologicalSpace X] (f : X → Ψ → Matrix (Sg j j') (Sg j j') ℂ)
    (hc : ∀ τ, Continuous fun x => f x τ) (hu : ∀ x τ, IsSgU (f x τ)) :
    Continuous fun x => moebBall q (f x) 0 := by
  have hb : ∀ τ, (ballMat q 0 τ)ᵀ = 0 := by
    intro τ
    ext a b
    simp [ballMat]
  refine continuous_pi fun k => ?_
  simp only [moebBall, ballPt, hb, moebW_zero]
  set τ := (q.symm k).1
  have h11 : Continuous fun x => (f x τ).toBlocks₁₁ :=
    continuous_matrix fun a b => (hc τ).matrix_elem _ _
  have h21 : Continuous fun x => (f x τ).toBlocks₂₁ :=
    continuous_matrix fun a b => (hc τ).matrix_elem _ _
  have hm := h21.matrix_mul (continuous_matrix_inv h11 fun x => (hu x τ).det_toBlocks₁₁_ne_zero)
  exact hm.matrix_elem _ _

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroEqIffUnitary
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab

variable {j j' : ℕ}

theorem sg_fb {a : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {c : Matrix (Fin j') (Fin j) ℂ} {d : Matrix (Fin j') (Fin j') ℂ}
    (h : IsSgU (fromBlocks a b c d)) :
    aᴴ * a - cᴴ * c = 1 ∧ aᴴ * b - cᴴ * d = 0 ∧ bᴴ * b - dᴴ * d = -1 := by
  unfold IsSgU sgI at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨h1, h2, -, h4⟩ := fromBlocks_inj.1 h
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.mul_neg, add_zero, zero_add] at h1 h2 h4
  refine ⟨?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using h1
  · simpa [sub_eq_add_neg] using h2
  · simpa [sub_eq_add_neg] using h4

theorem unit_of_rel {a : Matrix (Fin j) (Fin j) ℂ} {c : Matrix (Fin j') (Fin j) ℂ}
    (h : aᴴ * a - cᴴ * c = 1) : IsUnit a.det := by
  have e : aᴴ * a = 1 + cᴴ * c := by rw [← h]; abel
  have pd : (aᴴ * a).PosDef := by
    rw [e]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self c)
  have hu : IsUnit (aᴴ * a).det := (Matrix.isUnit_iff_isUnit_det _).1 pd.isUnit
  rw [Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

theorem sgI_mul_self : sgI j j' * sgI j j' = 1 := by
  unfold sgI
  rw [fromBlocks_multiply]
  simp

theorem IsSgU.mul {u v : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) (hv : IsSgU v) : IsSgU (u * v) := by
  unfold IsSgU at *
  rw [conjTranspose_mul]
  calc vᴴ * uᴴ * sgI j j' * (u * v) = vᴴ * (uᴴ * sgI j j' * u) * v := by
        simp only [Matrix.mul_assoc]
    _ = sgI j j' := by rw [hu, hv]

theorem IsSgU.det_unit {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) : IsUnit u.det := by
  have : (sgI j j' * uᴴ * sgI j j') * u = 1 := by
    have e : sgI j j' * uᴴ * sgI j j' * u = sgI j j' * (uᴴ * sgI j j' * u) := by
      simp only [Matrix.mul_assoc]
    rw [e, show uᴴ * sgI j j' * u = sgI j j' from hu, sgI_mul_self]
  exact Matrix.isUnit_det_of_left_inverse this

theorem unitary_iff_fb {p : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {r : Matrix (Fin j') (Fin j) ℂ} {s : Matrix (Fin j') (Fin j') ℂ}
    (h : IsSgU (fromBlocks p b r s)) :
    (fromBlocks p b r s)ᴴ * fromBlocks p b r s = 1 ↔ r = 0 := by
  obtain ⟨h1, h2, h3⟩ := sg_fb h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
  constructor
  · intro e
    obtain ⟨e1, -, -, -⟩ := fromBlocks_inj.1 e
    have hz : (2 : ℂ) • (rᴴ * r) = 0 := by
      have : rᴴ * r + rᴴ * r = 0 := by
        have := sub_eq_zero.2 (e1.trans h1.symm)
        rw [← this]; abel
      rw [two_smul]; exact this
    have hz' : rᴴ * r = 0 := (smul_eq_zero.1 hz).resolve_left two_ne_zero
    exact conjTranspose_mul_self_eq_zero.1 hz'
  · rintro rfl
    simp only [conjTranspose_zero, Matrix.zero_mul, sub_zero, add_zero] at h1 h2 h3 ⊢
    have hp : p * pᴴ = 1 := mul_eq_one_comm.1 h1
    have hb : b = 0 := by
      have : p * (pᴴ * b) = b := by rw [← Matrix.mul_assoc, hp, Matrix.one_mul]
      rw [← this, h2, Matrix.mul_zero]
    subst hb
    simp only [conjTranspose_zero, Matrix.zero_mul, zero_sub, neg_inj] at h3
    simp [h1, h3]

theorem single_fb {a p : Matrix (Fin j) (Fin j) ℂ} {b e : Matrix (Fin j) (Fin j') ℂ}
    {c r : Matrix (Fin j') (Fin j) ℂ} {d s : Matrix (Fin j') (Fin j') ℂ}
    (hu : IsSgU (fromBlocks a b c d)) (hv : IsSgU (fromBlocks p e r s)) :
    c * a⁻¹ = (c * p + d * r) * (a * p + b * r)⁻¹ ↔ r = 0 := by
  have ha : IsUnit a.det := unit_of_rel (sg_fb hu).1
  have hp : IsUnit p.det := unit_of_rel (sg_fb hv).1
  have hw : IsUnit (a * p + b * r).det := by
    have := IsSgU.mul hu hv
    rw [fromBlocks_multiply] at this
    exact unit_of_rel (sg_fb this).1
  constructor
  · intro h
    have h' : c * a⁻¹ * (a * p + b * r) = c * p + d * r := by
      rw [h, Matrix.nonsing_inv_mul_cancel_right _ _ hw]
    have hs : (d - c * a⁻¹ * b) * r = 0 := by
      have e1 : c * a⁻¹ * (a * p + b * r) = c * p + c * a⁻¹ * b * r := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ ha, Matrix.mul_assoc (c * a⁻¹) b r]
      rw [e1] at h'
      have : c * a⁻¹ * b * r = d * r := add_left_cancel h'
      rw [Matrix.sub_mul, this, sub_self]
    have hS : IsUnit (d - c * a⁻¹ * b).det := by
      have hd := IsSgU.det_unit hu
      letI := Matrix.invertibleOfIsUnitDet a ha
      rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at hd
      exact isUnit_of_mul_isUnit_right hd
    have : (d - c * a⁻¹ * b)⁻¹ * ((d - c * a⁻¹ * b) * r) = r :=
      Matrix.nonsing_inv_mul_cancel_left _ _ hS
    rw [← this, hs, Matrix.mul_zero]
  · rintro rfl
    simp only [Matrix.mul_zero, add_zero]
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hp]

theorem single {u v : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) (hv : IsSgU v) :
    u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ = (u * v).toBlocks₂₁ * (u * v).toBlocks₁₁⁻¹ ↔ vᴴ * v = 1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, u = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks u).symm⟩
  obtain ⟨p, e, r, s, rfl⟩ : ∃ a b c d, v = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks v).symm⟩
  rw [unitary_iff_fb hv, ← single_fb hu hv, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₁₁]

theorem ballPt_inj {Ψ : Type} {n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    {W W' : Ψ → Matrix (Fin j') (Fin j) ℂ} (h : ballPt q W = ballPt q W') : W = W' := by
  funext τ
  ext i' i
  have := congrFun h (q (τ, i, i'))
  simpa [ballPt] using this

theorem moebBall_zero {Ψ : Type} [Fintype Ψ] {n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (w : Ψ → Matrix (Sg j j') (Sg j j') ℂ) :
    moebBall q w 0 = ballPt q fun τ => (w τ).toBlocks₂₁ * (w τ).toBlocks₁₁⁻¹ := by
  have hb : ∀ τ, (ballMat q (0 : Fin n → ℂ) τ)ᵀ = 0 := by
    intro τ
    ext a b
    simp [ballMat]
  unfold moebBall
  congr 1
  funext τ
  rw [hb τ]
  simp [moebW]

theorem moebBall_zero_iff : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → (moebBall q u 0 = moebBall q (fun τ => u τ * v τ) 0 ↔ ∀ τ, (v τ)ᴴ * v τ = 1) := by
  intro Ψ _ j j' n q u v hu hv
  rw [moebBall_zero, moebBall_zero]
  constructor
  · intro h τ
    exact (single (hu τ) (hv τ)).1 (congrFun (ballPt_inj q h) τ)
  · intro h
    congr 1
    funext τ
    exact (single (hu τ) (hv τ)).2 (h τ)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab
end
end

