module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0242
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0243
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0206
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0181
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0240
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0237
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeKeepsCharacter
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeadLetterLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5

theorem nL_glev0 {k r j : ℕ} (hj : j + 1 ≤ r) (a : Fin j → ℂ) : LevelPointCoordinates.nL k r j hj a ∈ Q.Glev k r 0 :=
  ⟨SingleEntryHermitianProducts.nL_uh j hj a, fun b hb => absurd hb (by simp)⟩

theorem derivative_keeps_character {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r j : ℕ} (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) {Dm : Set (Q.Mx k r)} (hD : IsOpen Dm)
    (hDm : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ, LevelPointCoordinates.nL k r j hj a * g ∈ Dm)
    (p q : Fin (2 * r + k + 1)) (w : VS k r 0 Dm E)
    (hw : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
      (w : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * g) = psi k r z cStd (LevelPointCoordinates.nL k r j hj a) • (w : Q.Mx k r → E) g)
    (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ Dm) (a : Fin j → ℂ) :
    ((PBG.E0 hD p q w : VS k r 0 Dm E) : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * g) =
      psi k r z cStd (LevelPointCoordinates.nL k r j hj a) • ((PBG.E0 hD p q w : VS k r 0 Dm E) : Q.Mx k r → E) g := by
  have hng : LevelPointCoordinates.nL k r j hj a * g ∈ Q.Glev k r 0 ∩ Dm :=
    ⟨Qx3.glev_mul (nL_glev0 hj a) hg.1, hDm g hg a⟩
  set c := psi k r z cStd (LevelPointCoordinates.nL k r j hj a) with hc
  have hG := Qx2.good_eh (E := E) (k := k) (r := r) (i := 0) hD (PBG.c0 p) (PBG.c0 q)
  simp only [PBG.position_level_zero_coord] at hG
  unfold PBG.E0
  rw [ev_E hD _ _ w hng, ev_E hD _ _ w hg, PBG.position_level_zero_coord, PBG.position_level_zero_coord]
  rw [← WeylCellAction.eH_left (LevelPointCoordinates.nL k r j hj a) p q (w : Q.Mx k r → E) g]
  rw [hG.loc (fun x => (w : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * x)) (fun x => (fun _ => (0 : E)) x + c • (w : Q.Mx k r → E) x)
    (fun x hx => by simp only [zero_add]; exact hw x hx a) g hg]
  rw [hG.lin (fun _ => (0 : E)) (w : Q.Mx k r → E) c Qx2.smooth_zero w.2.1 g hg]
  have h0 : Q.EH k r p q (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
    simp [Q.EH, EabH, RdV]
  rw [h0, zero_add]

theorem _root_.Formalism.FourierDecayAlt.P.adjoin_lower_unipotent : LevelPointCoordinates.AdjoinNL := by
  intro E _ _ k r j hj z Dm hD hDm x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨⟨p, q⟩, rfl⟩ := hy
    intro v hv g hg a
    exact derivative_keeps_character hj z hD hDm p q v hv g hg a
  | algebraMap c =>
    intro v hv g hg a
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hv g hg a, smul_comm]
  | add y1 y2 _ _ h1 h2 =>
    intro v hv g hg a
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [h1 v hv g hg a, h2 v hv g hg a, smul_add]
  | mul y1 y2 _ _ h1 h2 =>
    intro v hv
    exact h1 _ (h2 v hv)

end Formalism.FourierDecayAlt.P.HeadLetterLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelPointEntryContDiffOn
section
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.XiPf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem fsym (m n : ℕ) (i : Fin (m + n)) : finSumFinEquiv.symm i =
    if h : i.val < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i - m, by omega⟩ := by
  split_ifs with h
  · rw [Equiv.symm_apply_eq]; ext; simp
  · rw [Equiv.symm_apply_eq]; ext; simp; omega

theorem castM_apply' {k a b : ℕ} (h : a = b) (g : B.Mat k a) (p q : Fin (2 * b + k + 1)) :
    D.castM h g p q = g (Fin.cast (by omega) p) (Fin.cast (by omega) q) := by
  subst h; simp [D.castM, Matrix.reindex_apply]

theorem castM_GV' {k a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ B.GV k a) : D.castM h g ∈ B.GV k b := by
  subst h; simpa [D.castM] using hg

theorem zfull_apply {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (c d : Fin (j + 1)) :
    zfull Z τ c d = if hc : c.val < j then (if hd : d.val < j then Z ⟨c.val, hc⟩ ⟨d.val, hd⟩ else 0)
      else (if d.val < j then 0 else τ) := by
  simp only [zfull, U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply, fsym]
  split_ifs <;> simp [Matrix.fromBlocks]

theorem det_zfull {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) : (zfull Z τ).det = Z.det * τ := by
  unfold zfull U.blk2
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp [Matrix.det_unique]

theorem wMat_mul_apply {d n : ℕ} (M : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) (c : Fin n) :
    (G.wMat d * M) i c = M i.rev c := by
  simp [G.wMat, Matrix.mul_apply]

theorem level_point_first_lines (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a : Fin j) (q : Fin (2 * r + k + 1)) :
    x0 k r j hj Z τ γ (esI k r (Fin.castLE (by omega) a)) q = if hq : q.val < j then Z a ⟨q.val, hq⟩ else 0 := by
  unfold x0
  rw [castM_apply']
  have hrow : (Fin.cast (by omega) (esI k r (Fin.castLE (by omega) a)) : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1)) =
      U.eB k (j + 1) (r - (j + 1)) (Sum.inr ⟨j - a.val, by omega⟩) := by
    ext; rw [Ux4.block_index_last_val_eq]; simp [esI]; omega
  rw [hrow]
  obtain ⟨y, hy⟩ : ∃ y, U.eB k (j + 1) (r - (j + 1)) y = Fin.cast (by omega) q := ⟨_, Equiv.apply_symm_apply _ _⟩
  rw [← hy]
  unfold U.mMap
  rw [Ux4.block3_apply]
  rcases y with ((c | c) | c)
  · have hq : q.val = c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_first_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    rw [wMat_mul_apply]
    have hrev : (⟨j - a.val, by omega⟩ : Fin (j + 1)).rev = ⟨a.val, by omega⟩ := by
      ext; simp [Fin.rev]; omega
    rw [hrev, zfull_apply, dite_eq_left (by simp)]
    by_cases h : c.val < j
    · rw [dite_eq_left h, dite_eq_left (by omega)]
      exact congrArg₂ Z (Fin.ext rfl) (Fin.ext hq.symm)
    · rw [dite_eq_right h, dite_eq_right (by omega)]
  · have hq : q.val = j + 1 + c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_middle_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inr, Matrix.zero_apply]
    rw [dite_eq_right (by omega)]
  · have hq : q.val = j + 1 + (2 * (r - (j + 1)) + k + 1) + c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_last_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    rw [dite_eq_right (by omega)]

theorem Hpk_eI_row (k r : ℕ) (a : Fin r) (s : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) s = if s = esI k r a then 1 else 0 := by
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_eI_col (k r : ℕ) (a : Fin r) (s : Fin (2 * r + k + 1)) :
    Hpk k r s (eI k r a) = if s = esI k r a then 1 else 0 := by
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_low (k r : ℕ) (p s : Fin (2 * r + k + 1)) (hs : s.val < r) :
    Hpk k r p s = if p.val + s.val = 2 * r + k then 1 else 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem xiCoef : XiCoef := by
  intro k r j hj Z τ γ a p
  have h1 : ∀ v : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) v (bvec (eI k r (Fin.castLE (by omega) a))) =
      ∑ s, Hpk k r (eI k r (Fin.castLE (by omega) a)) s * v s := by
    intro v
    simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [h1]
  simp only [Hpk_eI_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [bvec, Matrix.mulVec_single_one, Matrix.transpose_apply]
  exact level_point_first_lines k r j hj Z τ γ a p

theorem x0_GV (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) : x0 k r j hj Z τ γ ∈ B.GV k r := by
  unfold x0
  apply castM_GV'
  exact (Ux2.sliceMem k (j + 1) (r - (j + 1))).1 _ _ (by rw [det_zfull]; exact mul_ne_zero hZ hτ) hγ

theorem xiMem : XiMem := by
  intro k r j hj Z τ γ hZ hτ hγ
  exact ⟨x0_GV k r j hj Z τ γ hZ hτ hγ, fun a ha => absurd ha (by simp)⟩

theorem xiCoefV : XiCoefV := by
  intro k r j hj Z τ γ hZ hτ hγ a p
  have hinv := PBG.inv_GV (x0_GV k r j hj Z τ γ hZ hτ hγ)
  rw [hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hH : Hpk k r *ᵥ bvec (eI k r (Fin.castLE (by omega) a)) = bvec (esI k r (Fin.castLE (by omega) a)) := by
    ext s
    simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Hpk_eI_col, Pi.single_apply]
  rw [hH]
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.conjTranspose_apply, level_point_first_lines]
  simp only [Matrix.mulVec, dotProduct]
  simp only [Matrix.col_apply, Matrix.conjTranspose_apply, level_point_first_lines]
  split_ifs with hp
  · rw [Fintype.sum_eq_single ⟨2 * r + k - p.val, by omega⟩]
    · have hH1 : Hpk k r p ⟨2 * r + k - p.val, by omega⟩ = 1 := by
        rw [Hpk_low _ _ _ _ (by simp only [Fin.val_mk]; omega), if_pos (by simp only [Fin.val_mk]; omega)]
      rw [hH1, one_mul, dite_eq_left (by simp only [Fin.val_mk]; omega)]
      rfl
    · intro s hs
      by_cases h : s.val < j
      · rw [dite_eq_left h]
        have : Hpk k r p s = 0 := by
          rw [Hpk_low _ _ _ _ (by omega), if_neg (by intro h'; apply hs; ext; simp only [Fin.val_mk]; omega)]
        rw [this, zero_mul]
      · rw [dite_eq_right h, star_zero, mul_zero]
  · refine Finset.sum_eq_zero fun s _ => ?_
    by_cases h : s.val < j
    · rw [dite_eq_left h]
      have : Hpk k r p s = 0 := by
        rw [Hpk_low _ _ _ _ (by omega), if_neg (by omega)]
      rw [this, zero_mul]
    · rw [dite_eq_right h, star_zero, mul_zero]

section smooth

variable {j : ℕ}

theorem contDiff_zfull (τ : ℂ) (c d : Fin (j + 1)) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun Z : MJ j => zfull Z τ c d) := by
  simp only [zfull_apply]
  split_ifs
  · exact contDiff_apply_apply ℝ _ _
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

theorem contDiff_adj_zfull (τ : ℂ) (c d : Fin (j + 1)) :
    ContDiff ℝ ⊤ (fun Z : MJ j => (zfull Z τ).adjugate c d) := by
  simp only [Matrix.adjugate_apply]
  apply PBG.contDiff_det'
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_zfull τ a b

theorem contDiffOn_inv_zfull (τ : ℂ) (c d : Fin (j + 1)) :
    ContDiffOn ℝ ∞ (fun Z : MJ j => (zfull Z τ)⁻¹ c d) {Z | Z.det ≠ 0} := by
  have he : ∀ Z : MJ j, (zfull Z τ)⁻¹ c d = (Z.det)⁻¹ * τ⁻¹ * (zfull Z τ).adjugate c d := by
    intro Z
    rw [Matrix.inv_def, Matrix.smul_apply, det_zfull, Ring.inverse_eq_inv', mul_inv, smul_eq_mul]
  simp only [he]
  have hdet : ContDiff ℝ ⊤ (fun Z : MJ j => Z.det) :=
    PBG.contDiff_det' (fun Z : MJ j => Z) (fun a b => contDiff_apply_apply ℝ a b)
  exact ((((hdet.of_le le_top).contDiffOn.inv (fun Z hZ => hZ)).mul contDiffOn_const).mul
    ((contDiff_adj_zfull τ c d).of_le le_top).contDiffOn)

theorem level_point_entry_contDiffOn (k r j : ℕ) (hj : j + 1 ≤ r) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (p q : Fin (2 * r + k + 1)) :
    ContDiffOn ℝ ∞ (fun Z : MJ j => x0 k r j hj Z τ γ p q) {Z | Z.det ≠ 0} := by
  obtain ⟨x, hx⟩ : ∃ x, U.eB k (j + 1) (r - (j + 1)) x = Fin.cast (by omega) p := ⟨_, Equiv.apply_symm_apply _ _⟩
  obtain ⟨y, hy⟩ : ∃ y, U.eB k (j + 1) (r - (j + 1)) y = Fin.cast (by omega) q := ⟨_, Equiv.apply_symm_apply _ _⟩
  have he : ∀ Z : MJ j, x0 k r j hj Z τ γ p q =
      Matrix.fromBlocks (Matrix.fromBlocks 0 0 0 γ) (Matrix.fromRows ((zfull Z τ)ᴴ⁻¹ * G.wMat (j + 1)) 0)
        (Matrix.fromCols (G.wMat (j + 1) * zfull Z τ) 0) 0 x y := by
    intro Z
    unfold x0 U.mMap
    rw [castM_apply', ← hx, ← hy, Ux4.block3_apply]
  simp only [he]
  have h13 : ∀ c d : Fin (j + 1),
      ContDiffOn ℝ ∞ (fun Z : MJ j => ((zfull Z τ)ᴴ⁻¹ * G.wMat (j + 1)) c d) {Z | Z.det ≠ 0} := by
    intro c d
    simp only [Matrix.mul_apply, ← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply]
    exact ContDiffOn.sum fun t _ =>
      (PBG.contDiff_starC.comp_contDiffOn (contDiffOn_inv_zfull τ t c)).mul contDiffOn_const
  have h31 : ∀ c d : Fin (j + 1),
      ContDiffOn ℝ ∞ (fun Z : MJ j => (G.wMat (j + 1) * zfull Z τ) c d) {Z | Z.det ≠ 0} := by
    intro c d
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun t _ => contDiffOn_const.mul (contDiff_zfull τ t d).contDiffOn
  rcases x with ((c | c) | c) <;> rcases y with ((d | d) | d) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply]
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact h13 c d
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact h31 c d
  · exact contDiffOn_const
  · exact contDiffOn_const

theorem xiSmooth : XiSmooth := by
  intro k r j hj τ γ
  exact contDiffOn_pi.2 fun p => contDiffOn_pi.2 fun q => level_point_entry_contDiffOn k r j hj τ γ p q

end smooth

end Formalism.FourierDecayAlt.P.WirtingerOperators.XiPf

namespace Formalism.FourierDecayAlt.P

theorem xi_coefficient : WirtingerOperators.XiCoef := WirtingerOperators.XiPf.xiCoef

theorem xi_coefficient_vector : WirtingerOperators.XiCoefV := WirtingerOperators.XiPf.xiCoefV

theorem xiMem_statement : WirtingerOperators.XiMem := WirtingerOperators.XiPf.xiMem

theorem xi_smooth : WirtingerOperators.XiSmooth := WirtingerOperators.XiPf.xiSmooth

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfHat
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_hat (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer)
    (hHat : JDHatOpQQ) (hBdd : JA.JABddOpQQ) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_genTransfer hJ hG (jDecayTrQQ_of_open hHat) (JA.jAdjTrQQ_of_three hHat hBdd JA.star_operator_transfer_holds)

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVOfEq
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeadLetterLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBG

variable {k r : ℕ}


open Formalism.FourierDecayAlt.Q.QRR in
theorem rdV_of_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z') (Φ : Q.Mx k r → E) (g : Q.Mx k r)
    (hΦ : ∀ n ∈ QuantumDeterminants.Nset k r, Φ (g * n) = psi k r z' cStd n • Φ g)
    (l : Fin r) (X : Q.Mx k r) (hX : Pat k r l X) (hS : dag k r X = -X) :
    RdV X Φ g = (ell k r z' X - star (ell k r z' X)) • Φ g := by
  unfold RdV
  have hfun : (fun t : ℝ => Φ (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => psi k r z' cStd (NormedSpace.exp ((t : ℂ) • X)) • Φ g := by
    funext t
    apply hΦ
    apply (exp_mem_nlev (pat_smul _ hX) _).1
    rw [dag_smul, hS, Complex.star_def, Complex.conj_ofReal, smul_neg]
  rw [hfun]
  exact ((hasDerivAt_psi z' hz X).smul_const (Φ g)).deriv

theorem _root_.Formalism.FourierDecayAlt.P.rule_of_eq : LevelPointCoordinates.RuleOfEq := by
  intro E _ _ k r z' Φ g hz hΦ p q hpq
  obtain ⟨l, hl⟩ := exists_pat p q hpq
  have hr : 1 ≤ r := by have := l.isLt; omega
  set Z : B.Mat k r := Matrix.single p q (1 : ℂ) with hZ
  have h1 := rdV_of_eq z' hz Φ g hΦ l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart1 Z)
  have h2 := rdV_of_eq z' hz Φ g hΦ l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart2 Z)
  set Λ : B.Mat k r → ℂ := fun X => ∑ a, ∑ b, X a b * C3.dpsiP k r z' a b with hΛ
  have hΛ1 : ell k r z' (hpart1 (Hpk k r) Z) - star (ell k r z' (hpart1 (Hpk k r) Z)) = Λ (hpart1 (Hpk k r) Z) := by
    rw [← dEll_eq_ell _ _ hr]
    exact (Formalism.FourierDecayAlt.P.dpsi_is_derivation k r z' _ hr hz (Formalism.FourierDecayAlt.P.PBG.hermitian_part_one_mem_lie Z)
      (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl))).symm
  have hΛ2 : ell k r z' (hpart2 (Hpk k r) Z) - star (ell k r z' (hpart2 (Hpk k r) Z)) = Λ (hpart2 (Hpk k r) Z) := by
    rw [← dEll_eq_ell _ _ hr]
    exact (Formalism.FourierDecayAlt.P.dpsi_is_derivation k r z' _ hr hz (Formalism.FourierDecayAlt.P.PBG.hermitian_part_two_mem_lie Z)
      (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl))).symm
  have hsum : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
    unfold hpart1 hpart2
    rw [smul_smul]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
    rw [this, ← smul_add]
    rw [show Z - (Hpk k r)⁻¹ * Zᴴ * Hpk k r + (Z + (Hpk k r)⁻¹ * Zᴴ * Hpk k r) = (2 : ℂ) • Z by
      rw [two_smul]; abel]
    rw [smul_smul]; norm_num
  have hΛZ : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) = C3.dpsiP k r z' p q := by
    have hlin : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) =
        Λ (hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z) := by
      simp only [hΛ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hlin, hsum]
    simp only [hΛ, hZ, Matrix.single_apply]
    rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [Ne.symm ha]
    · simp
  show EabH (Hpk k r) p q Φ g = _
  unfold EabH
  rw [h1, h2, hΛ1, hΛ2, smul_smul, ← add_smul, hΛZ]

end Formalism.FourierDecayAlt.P.HeadLetterLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichApply
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem hpk_inv' (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r :=
  Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.WeylGroupFacts.hpk_sq (k := k) (r := r))

theorem sandwich_apply {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (u v p q : Fin N) :
    (H * Matrix.single u v (1 : ℂ) * H) p q = H p u * H v q := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

theorem hpk_col_eI (k r : ℕ) (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r p (eI k r b) = if p.val + b.val = 2 * r + k then 1 else 0 := by
  have := b.isLt
  unfold Hpk eI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_row_eI (k r : ℕ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) q = if a.val + q.val = 2 * r + k then 1 else 0 := by
  have := a.isLt
  unfold Hpk eI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_col_esI (k r : ℕ) (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r p (esI k r b) = if p.val = b.val then 1 else 0 := by
  have := b.isLt
  unfold Hpk esI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_row_esI (k r : ℕ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) q = if q.val = a.val then 1 else 0 := by
  have := a.isLt
  unfold Hpk esI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpartLevi : HpartLevi := by
  intro k r j hj a b
  have ha := a.isLt
  have hb := b.isLt
  have hcI : (starRingEnd ℂ) (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]
  have hc2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext p q <;>
    simp only [hpart1, hpart2, hpk_inv', Matrix.conjTranspose_single, star_one, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.add_apply, sandwich_apply, hpk_col_eI, hpk_row_eI, hpk_col_esI, hpk_row_esI] <;>
    simp only [levi, Matrix.of_apply, Matrix.single_apply, eI, esI, Fin.ext_iff, Fin.val_castLE, smul_eq_mul,
      Matrix.smul_apply] <;>
    split_ifs <;> first | (exfalso; omega) | skip
  all_goals first
    | (exfalso; omega)
    | (simp; done)
    | (simp [Complex.conj_I]; done)
    | (simp [Complex.conj_I]; ring; done)
    | (simp only [mul_one, mul_zero, sub_zero, zero_sub, add_zero, zero_add, map_neg, hcI, hc2, neg_neg,
        neg_mul] <;> ring)

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
end
end

