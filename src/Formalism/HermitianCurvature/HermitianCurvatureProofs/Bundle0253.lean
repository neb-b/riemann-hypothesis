module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCoefficientHasCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0245
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0247
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointCornerScaledSingleComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0242
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0248

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMK2
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMK

def HB {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ)
    (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)) : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp) :=
  PBI.chartCoefficient b b' (fun Z' y' => ((β Z' : ℝ) : ℂ) • Φ Z' y')

def kapL {k p ρ : ℕ} (z : Fin (2 * ρ + k + 1) → ℂ) (b : U.RC k p ρ → ℝ) : ℂ :=
  ∫ x, (b x : ℂ) * psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x) ∂(U.muRC k p ρ)

def kapR {k p ρ : ℕ} (z' : Fin (2 * ρ + k + 1) → ℂ) (b' : U.RC k p ρ → ℝ) : ℂ :=
  ∫ x, (b' x : ℂ) * star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)) ∂(U.muRC k p ρ)

def RightAvg : Prop :=
  ∀ (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq),
    B0.z' = liftVec k p ρ Bj.z' → (∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) →
    Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl) →
    Bj.μN = D.muN k ρ → B0.μN = D.muN k (p + ρ) →
    ∀ (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)),
    Continuous b' → HasCompactSupport b' →
    ∀ Z : Fin p → Fin p → ℂ, (Matrix.of Z).det ≠ 0 →
    Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) →
    ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1 →
    ∀ y : Mt k ρ, (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ →
    (∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2))) →
    (∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') →
    ∀ h ∈ UWset k ρ Bj.z, ∀ a : U.RC k p ρ,
      PBG.Kr B0 (HB b b' β Φ) (U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) =
        (((b a : ℝ) : ℂ) * kapR Bj.z' b') • (Bj.π h⁻¹).comp (Φ Z y)

def LeftAvg : Prop :=
  ∀ (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq),
    Bj.μW Set.univ = 1 → Bj.μN = D.muN k ρ →
    ∀ (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k (p + ρ)) (b : U.RC k p ρ → ℝ) (c : ℂ)
      (A : Wq →L[ℂ] Wp), Continuous b → HasCompactSupport b →
    (∀ h ∈ UWset k ρ Bj.z, ∀ a : U.RC k p ρ,
      PBG.Kr B0 H (U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * g) = (((b a : ℝ) : ℂ) * c) • (Bj.π h⁻¹).comp A) →
    PBQ.pbF Bj B0 rfl H g = (kapL Bj.z b * c) • A

def CoreN : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (e : p + ρ = n), ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq),
    D.castV e (liftVec k p ρ Bj.z') = B0.z' → (∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y))) →
    Bj.μW Set.univ = 1 → Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e) →
    Bj.μN = D.muN k ρ → B0.μN = D.muN k n →
    ∀ (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)),
    Continuous b → HasCompactSupport b → Continuous b' → HasCompactSupport b' →
    ∀ Z : Fin p → Fin p → ℂ, (Matrix.of Z).det ≠ 0 →
    Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) →
    ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1 →
    ∀ y : Mt k ρ, (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ →
    (∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2))) →
    (∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') →
    PBQ.pbF Bj B0 e (D.castF e.symm (HB b b' β Φ)) (D.castM e (U.mMap k p ρ (Matrix.of Z) (Matrix.of y))) =
      (kapL Bj.z b * kapR Bj.z' b') • Φ Z y

def TopMk : Prop := CoreN → CutEX.MkTop

section assembly

theorem coreRfl (hR : RightAvg) (hL : LeftAvg) (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (hρ : ρ = 0) (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hz' : B0.z' = liftVec k p ρ Bj.z') (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y))
    (hW : Bj.μW Set.univ = 1) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k (p + ρ))
    (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp))
    (hb : Continuous b) (hbc : HasCompactSupport b) (hb' : Continuous b') (hbc' : HasCompactSupport b')
    (Z : Fin p → Fin p → ℂ) (hZ : (Matrix.of Z).det ≠ 0)
    (hβi : Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))))
    (hβ1 : ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1)
    (y : Mt k ρ) (hy : (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ)
    (hΦL : ∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2)))
    (hΦU : ∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') :
    PBQ.pbF Bj B0 rfl (HB b b' β Φ) (U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) =
      (kapL Bj.z b * kapR Bj.z' b') • Φ Z y := hL k p ρ Wp Wq hρ Bj B0 hW hNj (HB b b' β Φ) (U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) b
    (kapR Bj.z' b') (Φ Z y) hb hbc
    (fun h hh a => hR k p ρ Wp Wq hρ Bj B0 hz' hπ' hW' hW0' hNj hN0 b b' β Φ hb' hbc' Z hZ hβi hβ1 y hy
      hΦL hΦU h hh a)

theorem coreN_of (hR : RightAvg) (hL : LeftAvg) : CoreN := by
  intro k p ρ n Wp Wq _ _ _ _ _ _ e hρ Bj B0 hz' hπ' hW hW' hW0' hNj hN0 b b' β Φ hb hbc hb' hbc' Z hZ hβi hβ1 y hy
    hΦL hΦU
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz'
  have hπ'' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hF : D.castF (rfl : p + ρ = p + ρ).symm (HB b b' β Φ) = HB b b' β Φ := funext fun x => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [hF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact coreRfl hR hL k p ρ Wp Wq hρ Bj B0 hz'.symm hπ'' hW hW' hW0' hNj hN0 b b' β Φ hb hbc hb' hbc' Z hZ hβi hβ1
    y hy hΦL hΦU

theorem mkTop_of_leaves (hR : RightAvg) (hL : LeftAvg) (hT : TopMk) : CutEX.MkTop := hT (coreN_of hR hL)

end assembly

end Formalism.FourierDecayAlt.P.CutMK
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianPartLevi
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem castM_mul' {k a b : ℕ} (h : a = b) (g g' : B.Mat k a) :
    D.castM h (g * g') = D.castM h g * D.castM h g' := by
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem exp_castM {k a b : ℕ} (h : a = b) (M : B.Mat k a) :
    NormedSpace.exp (D.castM h M) = D.castM h (NormedSpace.exp M) := by
  unfold D.castM; exact exp_reindex _ M

theorem exp_block_three_diagonal {k j ρ : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) (Bm : B.Mat k ρ) (C : Matrix (Fin j) (Fin j) ℂ) :
    NormedSpace.exp (U.blk3 A 0 0 0 Bm 0 0 0 C) =
      U.blk3 (NormedSpace.exp A) 0 0 0 (NormedSpace.exp Bm) 0 0 0 (NormedSpace.exp C) := by
  unfold U.blk3
  rw [exp_reindex]
  have h1 : Matrix.fromRows (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) = 0 := by
    ext i l; rcases i with i | i <;> rfl
  have h2 : Matrix.fromCols (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) = 0 := by
    ext i l; rcases l with l | l <;> rfl
  rw [h1, h2, exp_fromBlocks, exp_fromBlocks]

theorem exp_block_two_diagonal {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Dd : Matrix (Fin s) (Fin s) ℂ) :
    NormedSpace.exp (U.blk2 A 0 0 Dd) = U.blk2 (NormedSpace.exp A) 0 0 (NormedSpace.exp Dd) := by
  unfold U.blk2
  rw [exp_reindex, exp_fromBlocks]

theorem symmetricScalarBlockMatrix_one_zero {p s : ℕ} : U.blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
  simp [U.blk2]

theorem block_two_identity_conjTranspose {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) :
    (U.blk2 A 0 0 (1 : Matrix (Fin s) (Fin s) ℂ))ᴴ = U.blk2 Aᴴ 0 0 1 := by
  ext a b
  simp only [Matrix.conjTranspose_apply, block_two_apply]
  split_ifs <;> simp [Matrix.one_apply, Fin.ext_iff, eq_comm]

theorem w_inv (d : ℕ) : (G.wMat d)⁻¹ = G.wMat d :=
  Matrix.inv_eq_left_inv (Ux4.wMat_mul_self d)

theorem exp_w_conj (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    NormedSpace.exp (G.wMat d * M * G.wMat d) = G.wMat d * NormedSpace.exp M * G.wMat d := by
  have hu : IsUnit (G.wMat d) := ⟨⟨G.wMat d, G.wMat d, Ux4.wMat_mul_self d, Ux4.wMat_mul_self d⟩, rfl⟩
  have e := Matrix.exp_conj (G.wMat d) M hu
  rw [w_inv] at e
  exact e

theorem block_two_exp_conjTranspose_inv {j : ℕ} (y : MJ j) :
    (U.blk2 (NormedSpace.exp y) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))ᴴ⁻¹ = U.blk2 (NormedSpace.exp (-yᴴ)) 0 0 1 := by
  rw [block_two_identity_conjTranspose]
  apply Matrix.inv_eq_left_inv
  rw [Ux4.symmetricScalarBlockMatrix_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  have hu : IsUnit (NormedSpace.exp yᴴ).det := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  rw [Matrix.exp_neg, ← Matrix.exp_conjTranspose, Matrix.nonsing_inv_mul _ hu, symmetricScalarBlockMatrix_one_zero]

theorem exp_levi {k r j : ℕ} (hj : j + 1 ≤ r) (x : MJ j) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • levi k r j x) = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.muP k (j + 1) (r - (j + 1)) (U.blk2 (NormedSpace.exp ((t : ℂ) • x)) 0 0 1)) := by
  have hs : (t : ℂ) • levi k r j x = levi k r j ((t : ℂ) • x) := by
    ext p q
    simp only [levi, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [Complex.conj_ofReal]
  rw [hs, levi_eq hj, exp_castM, exp_block_three_diagonal, exp_w_conj, exp_block_two_diagonal, exp_block_two_diagonal]
  simp only [NormedSpace.exp_zero]
  unfold U.muP
  rw [block_two_exp_conjTranspose_inv]

theorem zfull_mul {j : ℕ} (Z E : MJ j) (τ : ℂ) :
    zfull Z τ * U.blk2 E 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) = zfull (Z * E) τ := by
  unfold zfull
  rw [Ux4.symmetricScalarBlockMatrix_mul]
  simp

theorem curveLevi : CurveLevi := by
  intro k r j hj Z τ γ x t
  rw [exp_levi hj]
  unfold x0
  rw [← castM_mul', Ux4.mMap_mul_muP, zfull_mul]

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

theorem Formalism.FourierDecayAlt.P.levi_curve : Formalism.FourierDecayAlt.P.WirtingerOperators.CurveLevi := Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.curveLevi

theorem Formalism.FourierDecayAlt.P.hermitian_part_levi : Formalism.FourierDecayAlt.P.WirtingerOperators.HpartLevi := Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.hpartLevi
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftRuleLevelPoint
section
open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section hpart

variable {k r j : ℕ}

theorem hpk_row_eI (l : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r (eI k r c) l = if l = esI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem single_mul_hpk_eI (p : Fin (2 * r + k + 1)) (c : Fin r) (x : ℂ) :
    Matrix.single p (eI k r c) x * Hpk k r = Matrix.single p (esI k r c) x := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r c)]
  · rw [hpk_row_eI]
    by_cases hi : i = p <;> by_cases hl : l = esI k r c <;> simp [Matrix.single_apply, hi, hl, eq_comm]
  · intro m _ hm; simp [Matrix.single_apply, Ne.symm hm]
  · simp

theorem hpart1_single (hj : j + 1 ≤ r) (b : Fin j) :
    hpart1 (Hpk k r) (Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (1 / 2) := by
  unfold hpart1 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, single_mul_hpk_eI,
    smul_sub]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2]
  rfl

theorem hpart2_single (hj : j + 1 ≤ r) (b : Fin j) :
    hpart2 (Hpk k r) (Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (1 / (2 * Complex.I)) := by
  unfold hpart2 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, single_mul_hpk_eI,
    smul_add]
  have h2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp [Complex.conj_I]
  rw [h2, neg_smul, sub_neg_eq_add]
  rfl

theorem nN_smul_real (hj : j + 1 ≤ r) (a : Fin j → ℂ) (t : ℝ) :
    nN k r j hj (fun c => (t : ℂ) * a c) = (t : ℂ) • nN k r j hj a := by
  unfold nN
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_sub, smul_smul, smul_smul, map_mul, Complex.conj_ofReal]

theorem ell_nL (hj : j + 1 ≤ r) (hj1 : 1 ≤ j) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a : Fin j → ℂ) :
    ell k r z (nL k r j hj a) = -conj (a ⟨j - 1, by omega⟩) := by
  unfold ell
  rw [Finset.sum_eq_single (⟨j - 1, by omega⟩ : Fin r)]
  · rw [dite_eq_left (show j - 1 + 1 < r by omega), SingleEntryHermitianProducts.nL_apply, Matrix.one_apply_ne (by simp [eI, Fin.ext_iff]),
      zero_add, Finset.sum_eq_single (⟨j - 1, by omega⟩ : Fin j)]
    · have e2 : eI k r ⟨j - 1 + 1, by omega⟩ = eI k r ⟨j, by omega⟩ := by ext; simp [eI]; omega
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, e2]
      rw [show (eI k r ⟨((⟨j - 1, by omega⟩ : Fin j) : ℕ), by omega⟩ : Fin (2 * r + k + 1)) = eI k r ⟨j - 1, by omega⟩
        from rfl, Matrix.single_apply_same, mul_one]
    · intro b _ hb
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub,
        Matrix.single_apply_of_row_ne, mul_zero, neg_zero]
      intro h
      apply hb
      have := congrArg Fin.val h
      simp only [eI] at this
      exact Fin.ext this
    · simp
  · intro a' _ ha'
    have hne : a'.val ≠ j - 1 := fun h => ha' (Fin.ext h)
    split_ifs with h
    · rw [SingleEntryHermitianProducts.nL_apply, Matrix.one_apply_ne (by simp [eI, Fin.ext_iff]), zero_add]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, Matrix.single_apply]
      rw [if_neg, mul_zero, neg_zero]
      rintro ⟨h1, h2⟩
      have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
      simp only [eI] at e1 e2
      omega
    · have hrow : ∀ q, nL k r j hj a (eI k r a') q = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a') q := by
        intro q
        rw [SingleEntryHermitianProducts.nL_apply, Finset.sum_eq_zero, add_zero]
        intro b _
        rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, Matrix.single_apply]
        rw [if_neg, mul_zero, neg_zero]
        rintro ⟨h1, _⟩
        have e1 := congrArg Fin.val h1
        simp only [eI] at e1
        have := b.isLt
        omega
      rw [Matrix.mulVec, dotProduct]
      simp_rw [hrow]
      rw [← dotProduct, ← Matrix.mulVec, Matrix.one_mulVec, hz _ (Or.inl (by simp [eI]))]
  · simp

end hpart

section deriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r j : ℕ}

theorem hpk_row_esI (l : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r (esI k r c) l = if l = eI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem single_mul_hpk_esI (p : Fin (2 * r + k + 1)) (c : Fin r) (x : ℂ) :
    Matrix.single p (esI k r c) x * Hpk k r = Matrix.single p (eI k r c) x := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r c)]
  · rw [hpk_row_esI]
    by_cases hi : i = p <;> by_cases hl : l = eI k r c <;> simp [Matrix.single_apply, hi, hl, eq_comm]
  · intro m _ hm; simp [Matrix.single_apply, Ne.symm hm]
  · simp

theorem hM_lie (hj : j + 1 ≤ r) (x y : Fin (j + 1)) (s : ℂ) :
    (hM k r j hj x y s)ᴴ * Hpk k r + Hpk k r * hM k r j hj x y s = 0 := by
  unfold hM
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, SingleEntryHermitianProducts.single_conjT,
    SingleEntryHermitianProducts.single_conjT, star_one, star_star, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, single_mul_hpk_eI,
    single_mul_hpk_esI, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, SingleEntryHermitianProducts.hpk_mul_single_eI,
    SingleEntryHermitianProducts.hpk_mul_single_esI]
  abel

theorem psi_nL_hasDeriv (hj : j + 1 ≤ r) (hj1 : 1 ≤ j) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (a : Fin j → ℂ) :
    HasDerivAt (fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c)))
      (a ⟨j - 1, by omega⟩ - conj (a ⟨j - 1, by omega⟩)) 0 := by
  set R : ℝ := (cStd * -conj (a ⟨j - 1, by omega⟩)).re with hR
  have hfun : (fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c))) =
      fun t : ℝ => Complex.exp (Complex.I * (((t * R : ℝ)) : ℂ)) := by
    funext t
    unfold psi
    rw [ell_nL hj hj1 z hz]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, hR]
    rw [show cStd * -((t : ℂ) * conj (a ⟨j - 1, by omega⟩)) = (t : ℂ) * (cStd * -conj (a ⟨j - 1, by omega⟩)) by ring,
      Complex.re_ofReal_mul]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => ((t * R : ℝ) : ℂ)) ((R : ℝ) : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const R).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul Complex.I).cexp
  have hval : Complex.I * ((R : ℝ) : ℂ) = a ⟨j - 1, by omega⟩ - conj (a ⟨j - 1, by omega⟩) := by
    apply Complex.ext <;> simp [hR, cStd, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  rw [← hval]
  simpa using h2

theorem rdV_hM (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))) (hj1 : 1 ≤ j) (hz : inWb k r z) (hS : Q.SmoothLev k r 0 Dm Ψ) (hZ : Z.det ≠ 0)
    (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) (hx : x0 k r j hj Z τ γ ∈ Dm)
    (hEq : ∀ a : Fin j → ℂ,
      Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ))
    (b : Fin j) (s : ℂ) :
    RdV (hM k r j hj (Fin.last j) b.castSucc s) Ψ (x0 k r j hj Z τ γ) =
      (s * τ * Z⁻¹ b ⟨j - 1, by omega⟩ - conj (s * τ * Z⁻¹ b ⟨j - 1, by omega⟩)) • Ψ (x0 k r j hj Z τ γ) := by
  set x₁ := x0 k r j hj Z τ γ with hx₁
  have hxG : x₁ ∈ Q.Glev k r 0 := SingleEntryHermitianProducts.glev0 (x0_GV hj hZ hτ hγ)
  obtain ⟨U, F, hU, hxU, hF, hFU⟩ := hS x₁ ⟨hxG, hx⟩
  have hd : DifferentiableAt ℝ F x₁ := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
  set a : Fin j → ℂ := fun c => s * τ * Z⁻¹ b c with ha
  have hrd : RdV (hM k r j hj (Fin.last j) b.castSucc s) Ψ x₁ =
      fderiv ℝ F x₁ (x₁ * hM k r j hj (Fin.last j) b.castSucc s) :=
    (Formalism.FourierDecayAlt.P.Qx2.hasDeriv_ext hU hxU hxG ⟨hM_lie hj _ _ s, fun a ha => absurd ha (Nat.not_lt_zero _)⟩ hd
      hFU).deriv
  rw [hrd, hx₁, level_point_conj_unipotent hj hZ hτ γ b s, ← hx₁]
  have hc : HasDerivAt (fun t : ℝ => x₁ + (t : ℂ) • (nN k r j hj a * x₁)) (nN k r j hj a * x₁) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have := (h0.smul_const (nN k r j hj a * x₁)).const_add x₁
    rw [one_smul] at this
    exact this
  have hcF := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have hcurve : ∀ t : ℝ, x₁ + (t : ℂ) • (nN k r j hj a * x₁) = nL k r j hj (fun c => (t : ℂ) * a c) * x₁ := by
    intro t
    rw [nL_eq, nN_smul_real, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have hev : (F ∘ fun t : ℝ => x₁ + (t : ℂ) • (nN k r j hj a * x₁)) =ᶠ[𝓝 0]
      fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c)) • Ψ x₁ := by
    have hUn : U ∈ 𝓝 (x₁ + ((0 : ℝ) : ℂ) • (nN k r j hj a * x₁)) := by
      rw [Complex.ofReal_zero, zero_smul, add_zero]; exact hU.mem_nhds hxU
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, x₁ + (t : ℂ) • (nN k r j hj a * x₁) ∈ U :=
      hc.continuousAt.preimage_mem_nhds hUn
    filter_upwards [hmem] with t ht
    have hG : x₁ + (t : ℂ) • (nN k r j hj a * x₁) ∈ Q.Glev k r 0 := by
      rw [hcurve t]; exact Formalism.FourierDecayAlt.P.Qx3.glev_mul (HeadLetterLemmas.nL_glev0 hj _) hxG
    simp only [Function.comp]
    rw [← hFU _ ht hG, hcurve t, hEq]
  have h2 := (psi_nL_hasDeriv hj hj1 z hz a).smul_const (Ψ x₁)
  exact (hcF.congr_of_eventuallyEq hev.symm).unique h2

theorem left_rule_level_point : CutHL.LeftActionRuleAtBasePoint := by
  intro E _ _ k r j hj z Dm Ψ Z τ γ hj1 hz hD hS hZ hτ hγ hx hEq b
  show EabH (Hpk k r) _ _ Ψ _ = _
  unfold EabH
  rw [hpart1_single hj b, hpart2_single hj b, rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b,
    rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b, smul_smul, ← add_smul]
  congr 1
  set w := τ * Z⁻¹ b ⟨j - 1, by omega⟩
  have e1 : (1 / 2 : ℂ) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = w / 2 := by simp only [w]; ring
  have e2 : 1 / (2 * Complex.I) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = -(Complex.I * w) / 2 := by
    simp only [w]; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2]
  simp only [map_div₀, map_neg, map_mul, Complex.conj_I, map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring

end deriv

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

