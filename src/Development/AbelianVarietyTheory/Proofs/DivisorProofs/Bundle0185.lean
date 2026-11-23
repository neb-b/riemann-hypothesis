module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfPeriodOfDvdSumPowersetCard
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexWittBasisNormalForm
section
open scoped ComplexOrder

namespace GlobalTheory.MajPosCpx

theorem gram_sub_eq {n r a b : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) (g : Fin b → Fin r) (R : Matrix (Fin a) (Fin b) ℂ)
    (hR : ∀ i j, (X.conjTranspose * J * Y) (f i) (g j) = R i j) :
    (X.submatrix id f).conjTranspose * J * (Y.submatrix id g) = R := by
  ext i j; rw [← hR]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem mul_submatrix_id {n r a : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) : u * X.submatrix id f = (u * X).submatrix id f := by
  ext i j; simp [Matrix.mul_apply]

theorem exists_unip_conj_unitary : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 → Y.conjTranspose * J * Y = 0 → X.conjTranspose * J * Y = 1 →
    ∀ (c : GL (Fin n) ℂ) (ε : Fin n → Bool), (c.1).conjTranspose * J * c.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) →
    ∀ (l d : ℕ) (h : l + d ≤ r),
      ∃ (u : GL (Fin n) ℂ) (N : Matrix (Fin r) (Fin r) ℂ),
        (u.1).conjTranspose * J * u.1 = J ∧ u.1 * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u.1 v - v = Matrix.mulVec X w) ∧
        ∃ y₀ : GL (Fin d) ℂ, ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
          let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
          let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
          let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
          let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
          let M : Matrix (Fin n) (Fin n) ℂ := (c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1
          M.conjTranspose * M = 1 := by
  intro n r J hJ X Y hXX hYY hXY c ε hc l d h
  set Dg : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => if ε i then 1 else -1) with hDg
  have hDD : Dg * Dg = 1 := by
    rw [hDg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> norm_num
  have hcc : c.1 * (c⁻¹).1 = 1 := Units.mul_inv c
  have hcc' : (c⁻¹).1 * c.1 = 1 := Units.inv_mul c
  have hcH : (c⁻¹).1.conjTranspose * (c.1).conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, hcc, Matrix.conjTranspose_one]
  have hJc : J = (c⁻¹).1.conjTranspose * Dg * (c⁻¹).1 := by
    have e : (c⁻¹).1.conjTranspose * Dg * (c⁻¹).1 =
        ((c⁻¹).1.conjTranspose * (c.1).conjTranspose) * J * (c.1 * (c⁻¹).1) := by
      rw [← hc]; simp only [Matrix.mul_assoc]
    rw [e, hcH, hcc, Matrix.one_mul, Matrix.mul_one]
  set θ : Matrix (Fin n) (Fin n) ℂ := c.1 * Dg * (c⁻¹).1 with hθ
  have hθθ : θ * θ = 1 := by
    simp only [hθ, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (c⁻¹).1 c.1, hcc', Matrix.one_mul, ← Matrix.mul_assoc Dg Dg, hDD, Matrix.one_mul, hcc]
  have hQ : J * θ = (c⁻¹).1.conjTranspose * (c⁻¹).1 := by
    rw [hJc]; simp only [hθ, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (c⁻¹).1 c.1, hcc', Matrix.one_mul, ← Matrix.mul_assoc Dg Dg, hDD, Matrix.one_mul]
  have hQpd : (J * θ).PosDef := by
    rw [hQ]; exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 (c⁻¹).isUnit)
  set X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩ with hX₁
  set Y₁ : Matrix (Fin n) (Fin l) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩ with hY₁
  set Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩ with hXb
  set Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩ with hYb
  set X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩ with hX₂
  set Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩ with hY₂
  have w11 : X₁.conjTranspose * J * X₁ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have w1b : X₁.conjTranspose * J * Xb = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have wbb : Xb.conjTranspose * J * Xb = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have v11 : X₁.conjTranspose * J * Y₁ = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have v1b : X₁.conjTranspose * J * Yb = 0 :=
    gram_sub_eq J X Y _ _ 0 (fun i j => by
      rw [hXY, Matrix.one_apply, if_neg]
      · rfl
      · simp only [Fin.ext_iff]; omega)
  have ybb : Yb.conjTranspose * J * Yb = 0 := gram_sub_eq J Y Y _ _ 0 (fun i j => by rw [hYY]; rfl)
  have vbb : Xb.conjTranspose * J * Yb = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have w22 : X₂.conjTranspose * J * X₂ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have y22 : Y₂.conjTranspose * J * Y₂ = 0 := gram_sub_eq J Y Y _ _ 0 (fun i j => by rw [hYY]; rfl)
  have v22 : X₂.conjTranspose * J * Y₂ = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have w21 : X₂.conjTranspose * J * X₁ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  obtain ⟨u₂, A, hu₂J, hu₂X₁, hu₂Xb, hu₂Yb, hu₂v, hA⟩ :=
    _root_.GlobalTheory.levi_element_cpx n l d J (J * θ) hJ hQpd X₁ Y₁ Xb Yb w11 w1b wbb v11 v1b ybb vbb
  obtain ⟨u₁, hu₁J, hu₁X₂, hu₁v, hθX₂⟩ := GlobalTheory.T.exists_unitary_fixing_mulVec_conj_eq_of_majorant n (l + d) J θ hJ hθθ hQpd X₂ Y₂ w22 y22 v22
  have hu₁X₁ : u₁.1 * X₁ = X₁ := by
    have e : X₁ = X₂.submatrix id (fun j : Fin l => ⟨j.val, by omega⟩) := rfl
    rw [e, mul_submatrix_id, hu₁X₂]
  have hu₁Xb : u₁.1 * Xb = Xb := by
    have e : Xb = X₂.submatrix id (fun j : Fin d => ⟨l + j.val, by omega⟩) := rfl
    rw [e, mul_submatrix_id, hu₁X₂]
  set u : GL (Fin n) ℂ := u₁ * u₂ with hu
  have huv : u.1 = u₁.1 * u₂.1 := Units.val_mul u₁ u₂
  have huJ : (u.1).conjTranspose * J * u.1 = J := by
    have e : (u₂.1).conjTranspose * (u₁.1).conjTranspose * J * (u₁.1 * u₂.1) =
        (u₂.1).conjTranspose * ((u₁.1).conjTranspose * J * u₁.1) * u₂.1 := by simp only [Matrix.mul_assoc]
    rw [huv, Matrix.conjTranspose_mul, e, hu₁J, hu₂J]
  have huX₁ : u.1 * X₁ = X₁ := by rw [huv, Matrix.mul_assoc, hu₂X₁, hu₁X₁]
  have huXb : u.1 * Xb = Xb + X₁ * A := by
    rw [huv, Matrix.mul_assoc, hu₂Xb, Matrix.mul_add, hu₁Xb, ← Matrix.mul_assoc, hu₁X₁]
  have huYb : u.1 * Yb = u₁.1 * Yb := by rw [huv, Matrix.mul_assoc, hu₂Yb]
  have huP : ∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
      ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u.1 v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a := by
    intro v hv
    have h1 : Matrix.mulVec (X₁.conjTranspose * J) v = 0 := by
      funext i; exact congrFun hv ⟨i.val, by omega⟩
    set a := Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v) with ha
    have h2 : Matrix.mulVec (X₂.conjTranspose * J) (v + Matrix.mulVec X₁ a) = 0 := by
      rw [Matrix.mulVec_add, hv, Matrix.mulVec_mulVec, w21, Matrix.zero_mulVec, add_zero]
    obtain ⟨w, hw⟩ := hu₁v _ h2
    refine ⟨w, a, ?_⟩
    rw [huv, ← Matrix.mulVec_mulVec, hu₂v v h1, ← hw]
    abel
  obtain ⟨N, hN, hNs, hNp⟩ := GlobalTheory.T.hermitian_flag_unipotent_matrix_exists_sparse n r J X hXX l d h u.1 A huX₁ huXb huP
  obtain ⟨hθX', hHpd⟩ := GlobalTheory.T.hermitian_flag_complement_posDef_factorization n r J θ hJ hQpd X Y hXY l d h u₁.1 A hθX₂ hA
  set H : Matrix (Fin d) (Fin d) ℂ := Xb.conjTranspose * (J * θ) * (Xb + X₁ * A) with hHdef
  obtain ⟨y₀, hy₀⟩ := _root_.GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one d H hHpd
  have hθu : θ * u.1 * Xb = u.1 * Yb * H := by
    rw [Matrix.mul_assoc, huXb, hθX', huYb]
  have hy1 : (y₀⁻¹).1.conjTranspose * (y₀.1).conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have hHy : H = (y₀⁻¹).1.conjTranspose * (y₀⁻¹).1 := by
    calc H = ((y₀⁻¹).1.conjTranspose * (y₀.1).conjTranspose) * H * (y₀.1 * (y₀⁻¹).1) := by
          rw [hy1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = (y₀⁻¹).1.conjTranspose * ((y₀.1).conjTranspose * H * y₀.1) * (y₀⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hy₀, Matrix.mul_one]
  have hHinv : H * (y₀.1 * (y₀.1).conjTranspose) = 1 := by
    calc H * (y₀.1 * (y₀.1).conjTranspose) = (y₀⁻¹).1.conjTranspose * ((y₀⁻¹).1 * y₀.1) * (y₀.1).conjTranspose := by
          rw [hHy]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.inv_mul, Matrix.mul_one, hy1]
  have huJ' : (u.1).conjTranspose * J = J * (u⁻¹).1 := by
    calc (u.1).conjTranspose * J = (u.1).conjTranspose * J * (u.1 * (u⁻¹).1) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = ((u.1).conjTranspose * J * u.1) * (u⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = J * (u⁻¹).1 := by rw [huJ]
  have hθuY : θ * u.1 * Yb = u.1 * Xb * (y₀.1 * (y₀.1).conjTranspose) := by
    calc θ * u.1 * Yb = θ * u.1 * Yb * (H * (y₀.1 * (y₀.1).conjTranspose)) := by rw [hHinv, Matrix.mul_one]
      _ = θ * (θ * u.1 * Xb) * (y₀.1 * (y₀.1).conjTranspose) := by rw [hθu]; simp only [Matrix.mul_assoc]
      _ = (θ * θ) * u.1 * Xb * (y₀.1 * (y₀.1).conjTranspose) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hθθ, Matrix.one_mul]
  have hPX : (u.1).conjTranspose * (J * θ) * u.1 * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) := by
    calc (u.1).conjTranspose * (J * θ) * u.1 * Xb = ((u.1).conjTranspose * J) * (θ * u.1 * Xb) := by
          simp only [Matrix.mul_assoc]
      _ = J * ((u⁻¹).1 * u.1) * Yb * H := by rw [huJ', hθu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.mul_one, hHy]
  have hPY : (u.1).conjTranspose * (J * θ) * u.1 * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) := by
    calc (u.1).conjTranspose * (J * θ) * u.1 * Yb = ((u.1).conjTranspose * J) * (θ * u.1 * Yb) := by
          simp only [Matrix.mul_assoc]
      _ = J * ((u⁻¹).1 * u.1) * Xb * (y₀.1 * (y₀.1).conjTranspose) := by rw [huJ', hθuY]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.mul_one]
  have hPH : ((u.1).conjTranspose * (J * θ) * u.1).conjTranspose = (u.1).conjTranspose * (J * θ) * u.1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQpd.1.eq]
    simp only [Matrix.mul_assoc]
  refine ⟨u, N, huJ, hN, hNs, fun v hv => hNp v hv, y₀, fun k hk => ?_⟩
  intro Xb' Yb' m G M
  have hG : G.conjTranspose * ((u.1).conjTranspose * (J * θ) * u.1) * G = (u.1).conjTranspose * (J * θ) * u.1 :=
    GlobalTheory.T.conjTranspose_mul_self_of_witt_frame_unitary n d J ((u.1).conjTranspose * (J * θ) * u.1) Xb Yb y₀ hJ hPH wbb ybb vbb hPX hPY k hk
  show ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1) = 1
  have e1 : ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1) =
      (c.1).conjTranspose * ((u⁻¹).1.conjTranspose *
        (G.conjTranspose * ((u.1).conjTranspose * ((c⁻¹).1.conjTranspose * (c⁻¹).1) * u.1) * G) * (u⁻¹).1) * c.1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e1, ← hQ, hG]
  have e2 : (c.1).conjTranspose * ((u⁻¹).1.conjTranspose * ((u.1).conjTranspose * (J * θ) * u.1) * (u⁻¹).1) * c.1 =
      (c.1).conjTranspose * ((u.1 * (u⁻¹).1).conjTranspose * (J * θ) * (u.1 * (u⁻¹).1)) * c.1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e2, Units.mul_inv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hQ]
  have e3 : (c.1).conjTranspose * ((c⁻¹).1.conjTranspose * (c⁻¹).1) * c.1 =
      ((c⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * c.1) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e3, hcc', Matrix.conjTranspose_one, Matrix.one_mul]

end GlobalTheory.MajPosCpx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.TermSmooth

def term (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y t : ℝ) : ℂ :=
  ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a * (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) * (y : ℂ) ^ m *
    Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem u_ne {y : ℝ} (hy : y ≠ 0) (t : ℝ) : (t : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; exact hy this

theorem hasDerivAt_term (σ : ℂ) (ν : ℝ) (a b m : ℕ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    HasDerivAt (fun y => term σ ν a b m y t)
      (-(a : ℂ) * I * term σ ν (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y t
        + (m : ℂ) * term σ ν a b (m - 1) y t) y := by
  have hu := u_ne hy t
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => (t : ℂ) + (y : ℂ) * I) I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (t : ℂ)
  have h2 : HasDerivAt (fun y : ℝ => ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a)
      ((a : ℂ) * ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ (a - 1) * (-(((t : ℂ) + (y : ℂ) * I) ^ 2)⁻¹ * I)) y :=
    (((hasDerivAt_inv hu).comp y h1).pow a)
  have h3 : HasDerivAt (fun y : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))) ((2 * y : ℝ) : ℂ) y := by
    have : HasDerivAt (fun y : ℝ => t ^ 2 + y ^ 2) (2 * y) y := by
      simpa using ((hasDerivAt_pow 2 y).const_add (t ^ 2))
    exact this.ofReal_comp
  have h4 := (Complex.hasStrictDerivAt_cpow_const (c := -σ - (b : ℂ))
      (Complex.ofReal_mem_slitPlane.2 hQ)).hasDerivAt.comp y h3
  have h5 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ m) ((m : ℂ) * (y : ℂ) ^ (m - 1)) y :=
    (hasDerivAt_pow m (y : ℂ)).comp_ofReal
  have h := ((h2.mul h4).mul h5).mul_const (Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))))
  refine h.congr_deriv ?_
  simp only [term, Function.comp_def, Pi.mul_apply, ← inv_pow]
  generalize ((t : ℂ) + (y : ℂ) * I)⁻¹ = v
  rw [show -σ - ((b + 1 : ℕ) : ℂ) = -σ - (b : ℂ) - 1 by push_cast; ring]
  rcases a with _ | a <;> rcases m with _ | m <;>
    simp only [Nat.add_sub_cancel, Nat.zero_sub, pow_zero, Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add,
      neg_zero, Complex.ofReal_mul, Complex.ofReal_ofNat] <;> push_cast <;> ring

theorem continuous_term (σ : ℂ) (ν : ℝ) (a b m : ℕ) {y : ℝ} (hy : y ≠ 0) : Continuous (term σ ν a b m y) := by
  unfold term
  have h1 : Continuous fun t : ℝ => ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a :=
    ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) + (y : ℂ) * I).inv₀ (u_ne hy)).pow a
  have h2 : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) :=
    (by fun_prop : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))).cpow continuous_const
      fun t => Complex.ofReal_mem_slitPlane.2 (by positivity)
  exact ((h1.mul h2).mul continuous_const).mul (by fun_prop)

theorem norm_term_le (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) (a b m : ℕ) (hab : 2 ≤ a + 2 * b) {y₀ : ℝ}
    (hy₀ : y₀ ≠ 0) : ∃ bd : ℝ → ℝ, MeasureTheory.Integrable bd ∧
      ∀ t, ∀ y ∈ Metric.ball y₀ (|y₀| / 2), ‖term σ ν a b m y t‖ ≤ bd t := by
  have hσ' : -1 / 2 < σ.re := hσ
  set c := |y₀| / 2 with hc
  have hc0 : 0 < c := by positivity
  set e : ℝ := (a : ℝ) / 2 + b + σ.re with he
  have hab' : (2 : ℝ) ≤ a + 2 * b := by exact_mod_cast hab
  have he1 : 1 / 2 < e := by rw [he]; linarith
  set κ := min 1 (c ^ 2) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  refine ⟨fun t => (3 * c) ^ m * κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2), ?_, ?_⟩
  · exact (integrable_rpow_neg_one_add_norm_sq (by simp; linarith)).const_mul _
  intro t y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hyl : c ≤ |y| := by
    have := abs_sub_abs_le_abs_sub y₀ y
    rw [abs_sub_comm] at this; rw [hc]; linarith
  have hyu : |y| ≤ 3 * c := by
    have := abs_sub_abs_le_abs_sub y y₀
    rw [hc]; linarith
  have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hyl; linarith
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  have hnorm : ‖term σ ν a b m y t‖ = (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m := by
    unfold term
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_inv, hnu, Complex.norm_cpow_eq_rpow_re_of_pos hQ,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one, he, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg_one,
      ← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le, ← Real.rpow_add hQ]
    congr 2
    simp
    ring
  rw [hnorm]
  have hQk : κ * (1 + ‖t‖ ^ 2) ≤ t ^ 2 + y ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    have h1 : κ ≤ 1 := min_le_left _ _
    have h2 : κ ≤ c ^ 2 := min_le_right _ _
    have h3 : c ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ hc0.le hyl 2
    nlinarith [sq_nonneg t]
  have hA : (t ^ 2 + y ^ 2) ^ (-e) ≤ κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2) := by
    rw [show -(2 * e) / 2 = -e by ring, ← Real.mul_rpow hκ0.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hQk (by linarith)
  have hB : |y| ^ m ≤ (3 * c) ^ m := pow_le_pow_left₀ (abs_nonneg y) hyu m
  calc (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m ≤ (κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2)) * (3 * c) ^ m :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = _ := by ring

theorem ne_zero_of_mem_ball {y₀ y : ℝ} (hy₀ : y₀ ≠ 0) (hy : y ∈ Metric.ball y₀ (|y₀| / 2)) : y ≠ 0 := by
  rintro rfl
  rw [Metric.mem_ball, Real.dist_eq, zero_sub, abs_neg] at hy
  have : 0 < |y₀| := abs_pos.2 hy₀
  linarith

theorem integrable_term (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) {a b : ℕ} (m : ℕ) (hab : 2 ≤ a + 2 * b) {y : ℝ}
    (hy : y ≠ 0) : MeasureTheory.Integrable (term σ ν a b m y) := by
  obtain ⟨bd, hbd, h⟩ := norm_term_le σ hσ ν a b m hab hy
  exact hbd.mono' (continuous_term σ ν a b m hy).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t => h t y (Metric.mem_ball_self (by positivity)))

def intT (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y : ℝ) : ℂ := ∫ t : ℝ, term σ ν a b m y t

theorem hasDerivAt_intT (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) {a b : ℕ} (m : ℕ) (hab : 2 ≤ a + 2 * b) {y₀ : ℝ}
    (hy₀ : y₀ ≠ 0) :
    HasDerivAt (intT σ ν a b m)
      (-(a : ℂ) * I * intT σ ν (a + 1) b m y₀ + 2 * (-σ - (b : ℂ)) * intT σ ν a (b + 1) (m + 1) y₀
        + (m : ℂ) * intT σ ν a b (m - 1) y₀) y₀ := by
  obtain ⟨b1, hb1, h1⟩ := norm_term_le σ hσ ν (a + 1) b m (by omega) hy₀
  obtain ⟨b2, hb2, h2⟩ := norm_term_le σ hσ ν a (b + 1) (m + 1) (by omega) hy₀
  obtain ⟨b3, hb3, h3⟩ := norm_term_le σ hσ ν a b (m - 1) hab hy₀
  have i1 := integrable_term σ hσ ν m (a := a + 1) (b := b) (by omega) hy₀
  have i2 := integrable_term σ hσ ν (m + 1) (a := a) (b := b + 1) (by omega) hy₀
  have i3 := integrable_term σ hσ ν (m - 1) (a := a) (b := b) hab hy₀
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (F := fun y t => term σ ν a b m y t)
    (F' := fun y t => -(a : ℂ) * I * term σ ν (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y t
        + (m : ℂ) * term σ ν a b (m - 1) y t)
    (bound := fun t => ‖-(a : ℂ) * I‖ * b1 t + ‖2 * (-σ - (b : ℂ))‖ * b2 t + ‖(m : ℂ)‖ * b3 t)
    (Metric.ball_mem_nhds y₀ (by positivity))
    (Filter.eventually_of_mem (isOpen_ne.mem_nhds hy₀) fun y hy => (continuous_term σ ν a b m hy).aestronglyMeasurable)
    (integrable_term σ hσ ν m hab hy₀)
    ((((continuous_term σ ν _ _ _ hy₀).const_mul _).add ((continuous_term σ ν _ _ _ hy₀).const_mul _)).add
      ((continuous_term σ ν _ _ _ hy₀).const_mul _)).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t y hy => by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
        rw [norm_mul] <;> gcongr
      · exact h1 t y hy
      · exact h2 t y hy
      · exact h3 t y hy)
    (((hb1.const_mul _).add (hb2.const_mul _)).add (hb3.const_mul _))
    (MeasureTheory.ae_of_all _ fun t y hy => hasDerivAt_term σ ν a b m (ne_zero_of_mem_ball hy₀ hy) t)
  have k2 := key.2
  have hI : (∫ t, (-(a : ℂ) * I * term σ ν (a + 1) b m y₀ t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y₀ t
        + (m : ℂ) * term σ ν a b (m - 1) y₀ t)) = -(a : ℂ) * I * intT σ ν (a + 1) b m y₀ +
        2 * (-σ - (b : ℂ)) * intT σ ν a (b + 1) (m + 1) y₀ + (m : ℂ) * intT σ ν a b (m - 1) y₀ := by
    unfold intT
    rw [MeasureTheory.integral_add _ (i3.const_mul _), MeasureTheory.integral_add (i1.const_mul _) (i2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact (i1.const_mul _).add (i2.const_mul _)
  rw [hI] at k2
  exact k2

theorem contDiffOn_intT (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) :
    ∀ n : ℕ, ∀ a b m : ℕ, 2 ≤ a + 2 * b → ContDiffOn ℝ n (intT σ ν a b m) {y | y ≠ 0} := by
  intro n
  induction n with
  | zero =>
    intro a b m hab
    exact contDiffOn_zero.2 fun y hy => (hasDerivAt_intT σ hσ ν m hab hy).continuousAt.continuousWithinAt
  | succ n ih =>
    intro a b m hab
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_ne]
    refine ⟨fun y hy => (hasDerivAt_intT σ hσ ν m hab hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have c1 := (contDiffOn_const (c := -(a : ℂ) * I)).mul (ih (a + 1) b m (by omega))
    have c2 := (contDiffOn_const (c := 2 * (-σ - (b : ℂ)))).mul (ih a (b + 1) (m + 1) (by omega))
    have c3 := (contDiffOn_const (c := (m : ℂ))).mul (ih a b (m - 1) hab)
    refine ((c1.add c2).add c3).congr fun y hy => ?_
    exact (hasDerivAt_intT σ hσ ν m hab hy).deriv

theorem hTrans_eq (σ : ℂ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) : hTrans σ ν y = intT σ ν 2 0 0 y := by
  unfold hTrans intT
  congr 1
  funext t
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  unfold term phi
  rw [hnu]
  simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one]
  congr 2
  have hs : 0 < Real.sqrt (t ^ 2 + y ^ 2) := Real.sqrt_pos.2 hQ
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hs.ne'), Complex.cpow_def_of_ne_zero (by exact_mod_cast hQ.ne'),
    ← Complex.ofReal_log hs.le, ← Complex.ofReal_log hQ.le, Real.log_sqrt hQ.le]
  congr 1
  push_cast
  ring

theorem contDiffOn_hTrans (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) :
    ContDiffOn ℝ ∞ (hTrans σ ν) {y | y ≠ 0} := by
  refine (contDiffOn_infty.2 fun n => contDiffOn_intT σ hσ ν n 2 0 0 (by norm_num)).congr fun y hy => ?_
  exact hTrans_eq σ ν hy

end GlobalTheory.HeckeTwo.TermSmooth

namespace GlobalTheory.HeckeTwo

theorem fTerm_contDiffOn : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ σ ∈ halfPlane,
    ContDiffOn ℝ ∞ (fun z : Emb F → ℂ => fTerm σ z b ν) (upperHalf F) := by
  intro F _ _ b ν hb σ hσ
  unfold fTerm
  refine contDiffOn_prod fun τ _ => ?_
  have he : ContDiff ℝ ∞ (fun z : Emb F → ℂ =>
      Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ))) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) τ))))).cexp
  have hg : ContDiff ℝ ∞ (fun z : Emb F → ℂ => τ b * (z τ).im) :=
    contDiff_const.mul (Complex.imCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) τ))
  have hh : ContDiffOn ℝ ∞ (fun z : Emb F → ℂ => hTrans σ (τ ν) (τ b * (z τ).im)) (upperHalf F) :=
    (TermSmooth.contDiffOn_hTrans σ hσ (τ ν)).comp hg.contDiffOn
      fun z hz => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  exact he.contDiffOn.mul hh

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorPowerSummable
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.AffGlue

end GlobalTheory.AffGlue

namespace GlobalTheory.AffGlue


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
theorem _root_.GlobalTheory.AffGlue.existsUnique_ringHom_of_affineOpens : ∀ (Z : Scheme.{0}) (R : Type) [CommRing R] (φ : ∀ U : Z.affineOpens, R →+* Γ(Z, U)), (∀ (U V : Z.affineOpens) (h : (U : Z.Opens) ≤ V), (Z.presheaf.map (homOfLE h).op).hom.comp (φ V) = φ U) → ∃! Φ : R →+* Γ(Z, ⊤), ∀ U : Z.affineOpens, (Z.presheaf.map (homOfLE (le_top : (U : Z.Opens) ≤ ⊤)).op).hom.comp Φ = φ U := by
  intro Z R _ φ hφ
  have hcomp : ∀ {A B C : Z.Opens} (f : A ⟶ B) (g : B ⟶ C) (s : Γ(Z, C)),
      (Z.presheaf.map f.op).hom ((Z.presheaf.map g.op).hom s) =
        (Z.presheaf.map (f ≫ g).op).hom s := by
    intro A B C f g s
    rw [op_comp, Functor.map_comp]
    rfl
  have hφ' : ∀ (U V : Z.affineOpens) (f : (U : Z.Opens) ⟶ V) (r : R),
      (Z.presheaf.map f.op).hom (φ V r) = φ U r := by
    intro U V f r
    rw [show f = homOfLE (leOfHom f) from Subsingleton.elim _ _]
    exact RingHom.congr_fun (hφ U V (leOfHom f)) r
  have hcov : ∀ V : Z.Opens,
      V ≤ ⨆ W : {W : Z.affineOpens // (W : Z.Opens) ≤ V}, (W.1 : Z.Opens) := by
    intro V x hx
    obtain ⟨W, hW, hxW, hWle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hxW⟩
  have hglue : ∀ r : R, ∃! s : Γ(Z, ⊤), ∀ W : Z.affineOpens,
      (Z.presheaf.map (homOfLE (le_top : (W : Z.Opens) ≤ ⊤)).op).hom s = φ W r := by
    intro r
    have htop : (⊤ : Z.Opens) ≤ ⨆ W : Z.affineOpens, (W : Z.Opens) := by
      intro x hx
      obtain ⟨W, hW, hxW, -⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hxW⟩
    refine Z.sheaf.existsUnique_gluing' (fun W : Z.affineOpens => (W : Z.Opens)) ⊤
      (fun W => homOfLE le_top) htop (fun W => φ W r) ?_
    intro i j
    refine Z.sheaf.eq_of_locally_eq'
      (fun k : {W : Z.affineOpens // (W : Z.Opens) ≤ (i : Z.Opens) ⊓ j} => (k.1 : Z.Opens))
      _ (fun k => homOfLE k.2) (hcov _) _ _ fun k => ?_
    change (Z.presheaf.map _).hom ((Z.presheaf.map _).hom (φ i r)) =
      (Z.presheaf.map _).hom ((Z.presheaf.map _).hom (φ j r))
    rw [hcomp, hcomp, hφ', hφ']
  choose s hs hu using hglue
  let Φ : R →+* Γ(Z, ⊤) :=
    { toFun := s
      map_one' := (hu 1 1 fun W => by rw [map_one, map_one]).symm
      map_mul' := fun a b => (hu (a * b) (s a * s b) fun W => by
        rw [map_mul, hs a W, hs b W, map_mul]).symm
      map_zero' := (hu 0 0 fun W => by rw [map_zero, map_zero]).symm
      map_add' := fun a b => (hu (a + b) (s a + s b) fun W => by
        rw [map_add (f := _), hs a W, hs b W, map_add (f := _)]).symm }
  refine ⟨Φ, fun W => RingHom.ext fun r => hs r W,
    fun Ψ hΨ => RingHom.ext fun r => hu r (Ψ r) fun W => ?_⟩
  exact RingHom.congr_fun (hΨ W) r

end GlobalTheory.AffGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfPeriodOfDvdSumPowersetCardStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_period_of_dvd_sum_powersetCard' : ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d → (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) → (∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, q ^ i)) → ∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l := by
  first | exact @GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard | exact GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard | (intros; apply GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMaximalQuotientAlgebraicStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_maximal_quotient_algebraic : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (f : B), f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (M : MaximalSpectrum (FractionRing (Localization.Away (algebraMap B A' f)))), ∃ _ : Algebra (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal), Algebra.IsAlgebraic (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) := by
  first | (exact @GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue) | (exact GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue) | (intros; apply GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue  <;> assumption)
end

