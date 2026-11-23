module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0133
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0187
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0210
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0106
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensityOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0169
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0208
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCrd
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceAtApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbGermRateLowBOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0159
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0186
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0154
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RulesOnPbT
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbRight2
section
open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbRight

theorem castM_nset {k a b : ℕ} (e : a = b) {g : B.Mat k a} (hg : g ∈ Nset k a) : D.castM e g ∈ Nset k b := by
  subst e
  have : D.castM rfl g = g := by
    ext i j
    simp [D.castM]
  rw [this]
  exact hg

end Formalism.FourierDecayAlt.P.CutEXPbRight

namespace Formalism.FourierDecayAlt.P

open CutEX

private theorem castM_mul_eq_mul_castM {k a b : ℕ} (e : a = b) (g h : B.Mat k a) :
    D.castM e (g * h) = D.castM e g * D.castM e h := by
  subst e
  ext i j
  simp [D.castM]

theorem pullback_right_action : CutEX.PbRight := by
  intro Wp Wq _ _ _ _ _ _ P p G _ Z u μ hu
  have hm : D.castM (by omega) (U.muP P.k P.r (P.r - P.r) u) ∈ Nset P.k P.r :=
    CutEXPbRight.castM_nset _ (BigCellDiagonalMap.leviElement_nset u hu)
  unfold CutEX.pbTop CutEX.psiU PBQ.pbT CutEX.xT
  rw [← Ux4.mMap_mul_muP, castM_mul_eq_mul_castM]
  exact PBQ.pbF_right _ _ _ _ _ _ hm

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSuppHyp
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

section hyp

variable {m : ℕ}

theorem rev_cs (a b : Fin (m + 1) → ℂ) (c : ℂ) (t : ℝ) (ht : 0 < t)
    (ha : ∑ i : Fin m, ‖a i.castSucc‖ ^ 2 ≤ ‖a (Fin.last m)‖ ^ 2)
    (hb : ∑ i : Fin m, ‖b i.castSucc‖ ^ 2 ≤ ‖b (Fin.last m)‖ ^ 2 - t)
    (hc : ‖c‖ ≤ ∑ i : Fin m, ‖a i.castSucc‖ * ‖b i.castSucc‖) :
    ‖a (Fin.last m)‖ * t ≤ 2 * ‖b (Fin.last m)‖ * ‖a (Fin.last m) * b (Fin.last m) + c‖ := by
  set A := ‖a (Fin.last m)‖ with hA
  set Bn := ‖b (Fin.last m)‖ with hBn
  set P := ∑ i : Fin m, ‖a i.castSucc‖ * ‖b i.castSucc‖ with hPdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hCS : P ^ 2 ≤ (∑ i : Fin m, ‖a i.castSucc‖ ^ 2) * (∑ i : Fin m, ‖b i.castSucc‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsb : 0 ≤ ∑ i : Fin m, ‖b i.castSucc‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ Bn := norm_nonneg _
  have hBt : t ≤ Bn ^ 2 := by linarith
  have hP2 : P ^ 2 ≤ A ^ 2 * (Bn ^ 2 - t) := hCS.trans (mul_le_mul ha hb hsb (sq_nonneg _))
  have key : 2 * Bn * P ≤ A * (2 * Bn ^ 2 - t) := by
    have hR : 0 ≤ A * (2 * Bn ^ 2 - t) := mul_nonneg hA0 (by linarith)
    have hL : 0 ≤ 2 * Bn * P := by positivity
    have hsq : (2 * Bn * P) ^ 2 ≤ (A * (2 * Bn ^ 2 - t)) ^ 2 := by
      have e1 : (2 * Bn * P) ^ 2 = 4 * Bn ^ 2 * P ^ 2 := by ring
      have e2 : (A * (2 * Bn ^ 2 - t)) ^ 2 = 4 * Bn ^ 2 * (A ^ 2 * (Bn ^ 2 - t)) + A ^ 2 * t ^ 2 := by ring
      rw [e1, e2]
      have h4 : 4 * Bn ^ 2 * P ^ 2 ≤ 4 * Bn ^ 2 * (A ^ 2 * (Bn ^ 2 - t)) :=
        mul_le_mul_of_nonneg_left hP2 (by positivity)
      nlinarith [sq_nonneg (A * t)]
    nlinarith
  have h1 : A * Bn ≤ ‖a (Fin.last m) * b (Fin.last m) + c‖ + ‖c‖ := by
    rw [hA, hBn, ← norm_mul]
    calc ‖a (Fin.last m) * b (Fin.last m)‖ = ‖(a (Fin.last m) * b (Fin.last m) + c) - c‖ := by
          rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  have h2 : A * Bn - P ≤ ‖a (Fin.last m) * b (Fin.last m) + c‖ := by linarith
  calc A * t = 2 * A * Bn ^ 2 - A * (2 * Bn ^ 2 - t) := by ring
    _ ≤ 2 * A * Bn ^ 2 - 2 * Bn * P := by linarith
    _ = 2 * Bn * (A * Bn - P) := by ring
    _ ≤ 2 * Bn * ‖a (Fin.last m) * b (Fin.last m) + c‖ := mul_le_mul_of_nonneg_left h2 (by positivity)

def dS (m : ℕ) : Fin (m + 1) → ℂ := fun i => if i = Fin.last m then -1 else 1

theorem dS_cs (i : Fin m) : dS m i.castSucc = 1 := by simp [dS, Fin.castSucc_ne_last]

theorem dS_last : dS m (Fin.last m) = -1 := by simp [dS]

theorem dS_sq : diagonal (dS m) * diagonal (dS m) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; unfold dS; split_ifs <;> norm_num

theorem sum_dS (v : Fin (m + 1) → ℂ) :
    ∑ i, star (v i) * dS m i * v i =
      ((∑ i : Fin m, ‖v i.castSucc‖ ^ 2 - ‖v (Fin.last m)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Fin.sum_univ_castSucc, dS_last]
  simp only [dS_cs, mul_one, Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_pow]
  have e : ∀ w : ℂ, star w * w = ((‖w‖ : ℝ) : ℂ) ^ 2 := fun w => by
    rw [Complex.star_def, Complex.conj_mul']
  rw [sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => e _
  · rw [mul_neg_one, neg_mul, e]

theorem quad_eq (v w : Fin (m + 1) → ℂ) :
    star w ⬝ᵥ (diagonal (dS m) *ᵥ v) = ∑ i, star (w i) * dS m i * v i := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, mul_assoc]

theorem quad_unitary (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (v : Fin (m + 1) → ℂ) :
    star (μ *ᵥ v) ⬝ᵥ (diagonal (dS m) *ᵥ (μ *ᵥ v)) = star v ⬝ᵥ (diagonal (dS m) *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hμ]

theorem row_unitary (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) :
    μ * diagonal (dS m) * μᴴ = diagonal (dS m) := by
  have h1 : (diagonal (dS m) * μᴴ * diagonal (dS m)) * μ = 1 := by
    calc (diagonal (dS m) * μᴴ * diagonal (dS m)) * μ = diagonal (dS m) * (μᴴ * diagonal (dS m) * μ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hμ, dS_sq]
  have h2 : μ * (diagonal (dS m) * μᴴ * diagonal (dS m)) = 1 := mul_eq_one_comm.mp h1
  calc μ * diagonal (dS m) * μᴴ = μ * (diagonal (dS m) * μᴴ * diagonal (dS m)) * diagonal (dS m) := by
        simp only [Matrix.mul_assoc, dS_sq, Matrix.mul_one]
    _ = diagonal (dS m) := by rw [h2, Matrix.one_mul]

theorem col_id (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (j : Fin (m + 1)) :
    ((∑ i : Fin m, ‖μ i.castSucc j‖ ^ 2 - ‖μ (Fin.last m) j‖ ^ 2 : ℝ) : ℂ) = dS m j := by
  have e := congrFun (congrFun hμ j) j
  rw [Matrix.mul_apply] at e
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at e
  rw [← sum_dS (fun i => μ i j), ← e]

theorem row_id (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (i : Fin (m + 1)) :
    ((∑ j : Fin m, ‖μ i j.castSucc‖ ^ 2 - ‖μ i (Fin.last m)‖ ^ 2 : ℝ) : ℂ) = dS m i := by
  have e := congrFun (congrFun (row_unitary μ hμ) i) i
  rw [Matrix.mul_apply] at e
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at e
  rw [← sum_dS (fun j => μ i j), ← e]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem real_of_cs {x : ℝ} (h : (x : ℂ) = 1) : x = 1 := by exact_mod_cast h

theorem real_of_last {x : ℝ} (h : (x : ℂ) = -1) : x = -1 := by exact_mod_cast h

theorem entry_le_last (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (i j : Fin (m + 1)) :
    ‖μ i j‖ ≤ ‖μ (Fin.last m) (Fin.last m)‖ := by
  have hrow := real_of_last (by rw [row_id μ hμ (Fin.last m), dS_last])
  have hsq : ‖μ i j‖ ^ 2 ≤ ‖μ (Fin.last m) (Fin.last m)‖ ^ 2 := by
    have hrow' : ∀ j0 : Fin m, ‖μ (Fin.last m) j0.castSucc‖ ^ 2 ≤ ‖μ (Fin.last m) (Fin.last m)‖ ^ 2 - 1 := by
      intro j0
      have : ‖μ (Fin.last m) j0.castSucc‖ ^ 2 ≤ ∑ j : Fin m, ‖μ (Fin.last m) j.castSucc‖ ^ 2 :=
        Finset.single_le_sum (f := fun j : Fin m => ‖μ (Fin.last m) j.castSucc‖ ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ j0)
      linarith
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j0, rfl⟩ | rfl
    · have hcol := real_of_cs (by rw [col_id μ hμ j0.castSucc, dS_cs])
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i0, rfl⟩ | rfl
      · have : ‖μ i0.castSucc j0.castSucc‖ ^ 2 ≤ ∑ i : Fin m, ‖μ i.castSucc j0.castSucc‖ ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin m => ‖μ i.castSucc j0.castSucc‖ ^ 2)
            (fun i _ => by positivity) (Finset.mem_univ i0)
        linarith [hrow' j0]
      · linarith [hrow' j0]
    · have hcol := real_of_last (by rw [col_id μ hμ (Fin.last m), dS_last])
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i0, rfl⟩ | rfl
      · have : ‖μ i0.castSucc (Fin.last m)‖ ^ 2 ≤ ∑ i : Fin m, ‖μ i.castSucc (Fin.last m)‖ ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin m => ‖μ i.castSucc (Fin.last m)‖ ^ 2)
            (fun i _ => by positivity) (Finset.mem_univ i0)
        linarith
      · exact le_rfl
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.mp hsq

theorem entry_bound (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (z z' : Fin (m + 1) → ℂ) (T T' : ℝ) (hT : 0 < T)
    (hT' : 0 < T') (hz : ∑ i : Fin m, ‖z i.castSucc‖ ^ 2 = ‖z (Fin.last m)‖ ^ 2 - T)
    (hz' : ∑ i : Fin m, ‖z' i.castSucc‖ ^ 2 = ‖z' (Fin.last m)‖ ^ 2 - T') (i j : Fin (m + 1)) :
    ‖μ i j‖ * (T * T') ≤
      4 * ‖z (Fin.last m)‖ * ‖z' (Fin.last m)‖ * ‖star z ⬝ᵥ (diagonal (dS m) *ᵥ (μ *ᵥ z'))‖ := by
  set y := μ *ᵥ z' with hy

  have hyq : ∑ i : Fin m, ‖y i.castSucc‖ ^ 2 ≤ ‖y (Fin.last m)‖ ^ 2 := by
    have e := quad_unitary μ hμ z'
    rw [quad_eq, quad_eq, sum_dS, sum_dS] at e
    have e' : ∑ i : Fin m, ‖y i.castSucc‖ ^ 2 - ‖y (Fin.last m)‖ ^ 2 =
        ∑ i : Fin m, ‖z' i.castSucc‖ ^ 2 - ‖z' (Fin.last m)‖ ^ 2 := by exact_mod_cast e
    linarith

  have h1 : ‖y (Fin.last m)‖ * T ≤ 2 * ‖z (Fin.last m)‖ *
      ‖star z ⬝ᵥ (diagonal (dS m) *ᵥ y)‖ := by
    have hb : ∑ i : Fin m, ‖(fun i => -star (z i)) i.castSucc‖ ^ 2 ≤
        ‖(fun i => -star (z i)) (Fin.last m)‖ ^ 2 - T := by
      simp only [norm_neg, norm_star]; linarith
    have := rev_cs y (fun i => -star (z i)) (∑ i : Fin m, star (z i.castSucc) * y i.castSucc) T hT hyq hb (by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [norm_mul, norm_neg, norm_star, mul_comm])
    simp only [norm_neg, norm_star] at this
    have hζ : star z ⬝ᵥ (diagonal (dS m) *ᵥ y) =
        y (Fin.last m) * -star (z (Fin.last m)) + ∑ i : Fin m, star (z i.castSucc) * y i.castSucc := by
      rw [quad_eq, Fin.sum_univ_castSucc, dS_last]
      simp only [dS_cs, mul_one]
      ring
    rw [hζ]; exact this

  have h2 : ‖μ (Fin.last m) (Fin.last m)‖ * T' ≤ 2 * ‖z' (Fin.last m)‖ * ‖y (Fin.last m)‖ := by
    have hrow := real_of_last (by rw [row_id μ hμ (Fin.last m), dS_last])
    have ha : ∑ j : Fin m, ‖(fun j => μ (Fin.last m) j) j.castSucc‖ ^ 2 ≤
        ‖(fun j => μ (Fin.last m) j) (Fin.last m)‖ ^ 2 := by simp only; linarith
    have hb : ∑ i : Fin m, ‖z' i.castSucc‖ ^ 2 ≤ ‖z' (Fin.last m)‖ ^ 2 - T' := le_of_eq hz'
    have := rev_cs (fun j => μ (Fin.last m) j) z' (∑ j : Fin m, μ (Fin.last m) j.castSucc * z' j.castSucc) T' hT'
      ha hb (by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [norm_mul])
    have hyL : y (Fin.last m) =
        μ (Fin.last m) (Fin.last m) * z' (Fin.last m) + ∑ j : Fin m, μ (Fin.last m) j.castSucc * z' j.castSucc := by
      rw [hy, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]; ring
    rw [hyL]; exact this
  have h3 := entry_le_last μ hμ i j
  have hzL : 0 ≤ ‖z (Fin.last m)‖ := norm_nonneg _
  have hz'L : 0 ≤ ‖z' (Fin.last m)‖ := norm_nonneg _
  calc ‖μ i j‖ * (T * T') ≤ ‖μ (Fin.last m) (Fin.last m)‖ * T' * T := by
        rw [mul_comm T T', ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hT'.le) hT.le
    _ ≤ 2 * ‖z' (Fin.last m)‖ * ‖y (Fin.last m)‖ * T := mul_le_mul_of_nonneg_right h2 hT.le
    _ = 2 * ‖z' (Fin.last m)‖ * (‖y (Fin.last m)‖ * T) := by ring
    _ ≤ 2 * ‖z' (Fin.last m)‖ * (2 * ‖z (Fin.last m)‖ * ‖star z ⬝ᵥ (diagonal (dS m) *ᵥ y)‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

end hyp

end Formalism.FourierDecayAlt.P.CutEXPbSupp
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXRadSliceTop
section
noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem radial_slice_top : CutEX.RadSliceTop := by
  intro Wp Wq _ _ _ _ _ _ P p G hG h hh
  have hc : P.r - P.r = P.r - D.ptSize h := by rw [hh.2]
  have hcpt : KB.CptCoef (p.T.bs P.r) (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    cases P with
    | mk k r T T' u u' =>
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        exact PBE.slice_level_zero_compact_support k 0 Wp Wq p.T G hG.1 (Nat.zero_le _) [] h hc hh (fun x => x.elim0)
      · exact PBE.slice_pos_cpt k r Wp Wq p.T G hG.1 r le_rfl h0 [] h hc hh (fun x => x.elim0)
  obtain ⟨R, hR⟩ := hcpt.2.1
  have hJ : P5.JFOK (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z'
      (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    refine ⟨fun A m => JFxG.cptInCC_G hcpt.1 (PBE.isCompact_gN_le _ _ R) (fun g hg hgC => ?_) A m, hcpt.2.2⟩
    by_contra hne
    exact hgC (hR g hg hne)
  obtain ⟨Φ, hΦ⟩ := P5.radJFExists Wp Wq (JC.parLev P P.r) _ _ _ _ (p.T.bs P.r) _
    (JCTx5.isPlace_lev P p.T ⟨P.r, Nat.lt_succ_self _⟩ p.hP) rfl rfl rfl rfl hJ
  exact ⟨Φ, hΦ⟩

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXTopPt
section
noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutEXTop

theorem domR_pt (k i r' : ℕ) (hr' : r' = 0) (zs zs' : Fin (2 * r' + k + 1) → ℂ) (x : (Fin (i + r') → ℂ) × Q.Mx k (i + r'))
    (hx : x ∈ Q.DomR k (i + r') (liftVec k i r' zs) (liftVec k i r' zs')) :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = ιLev k i r' g := by
  subst hr'
  obtain ⟨-, hxG, hxP⟩ := hx
  have himg := Formalism.FourierDecayAlt.P.level_group_image k i 0
  have hxG' : x.2 ∈ Q.Glev k (i + 0) ⟨i, by omega⟩ := hxG
  rw [himg] at hxG'
  obtain ⟨g, hgU, hgx⟩ := hxG'
  refine ⟨g, ⟨hgU, fun a => a.elim0⟩, ?_, hgx.symm⟩
  rw [← Formalism.FourierDecayAlt.P.WordCorrespondence.ggl_lift zs zs' g, hgx]
  exact hxP

theorem domR_pt_cast (k n i r' : ℕ) (hn : i + r' = n) (hr' : r' = 0) {z z' : Fin (2 * n + k + 1) → ℂ}
    {zs zs' : Fin (2 * r' + k + 1) → ℂ} (hz : D.castV hn (liftVec k i r' zs) = z)
    (hz' : D.castV hn (liftVec k i r' zs') = z') (x : (Fin n → ℂ) × Q.Mx k n) (hx : x ∈ Q.DomR k n z z') :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = D.castM hn (ιLev k i r' g) := by
  subst hn
  subst hz
  subst hz'
  obtain ⟨g, h1, h2, h3⟩ := domR_pt k i r' hr' zs zs' x hx
  exact ⟨g, h1, h2, h3⟩

theorem gv_iff_glev (k ρ : ℕ) (hρ : ρ = 0) (γ : B.Mat k ρ) : γ ∈ B.GV k ρ ↔ γ ∈ Q.Glev k ρ (Fin.last ρ) := by
  subst hρ
  constructor
  · intro h
    exact ⟨h, fun a => a.elim0⟩
  · intro h
    exact h.1

end Formalism.FourierDecayAlt.P.CutEXTop

open Formalism.FourierDecayAlt.P.CutEXTop in
theorem Formalism.FourierDecayAlt.P.top_point_existence : Formalism.FourierDecayAlt.P.CutEX.TopPt := by
  intro Wp Wq _ _ _ _ _ _ P p
  refine ⟨fun x hx => ?_, fun γ => gv_iff_glev P.k (P.r - P.r) (by omega) γ⟩
  exact domR_pt_cast P.k P.r P.r (P.r - P.r) (by omega) (by omega) (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) x hx
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXp
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem residue_top_exceptional : ResTop := by
  intro E _ _ k ρ hρ J c g
  subst hρ
  simp [Q.resG, Q.wCell]

theorem radial_extension_holds : RadExt := by
  intro Wp Wq _ _ _ _ k ρ z z' π π' Ψ Ψ' h
  apply Subtype.ext
  funext c g
  by_cases hx : ((c, g) : (Fin ρ → ℂ) × Q.Mx k ρ) ∈ Q.DomR k ρ z z'
  · exact h _ hx
  · rw [Ψ.2.1 (c, g) hx, Ψ'.2.1 (c, g) hx]

theorem radial_of_function_holds : RadOfFun := by
  classical
  intro Wp Wq _ _ _ _ k ρ z z' π π' f hloc hequiv
  have hUW : ∀ {w : Fin (2 * ρ + k + 1) → ℂ} {h : Mx k ρ}, h ∈ UWset k ρ w → h ∈ Glev k ρ (Fin.last ρ) :=
    fun hh => ⟨hh.1, fun a _ => hh.2.1 a⟩
  refine ⟨⟨fun c g => if (c, g) ∈ DomR k ρ z z' then f g else 0, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = 0
    exact if_neg hx
  · intro x₀ hx₀
    obtain ⟨hΩ, hG, hpos⟩ := hx₀
    obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hloc x₀.2 hG hpos
    refine ⟨OmX ρ ×ˢ (U ∩ {g | 0 < GGl k ρ z z' g}), fun x => F x.2, ?_, ?_, ?_, ?_⟩
    · exact (Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX ρ).prod
        (hU.inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous k ρ z z')))
    · exact ⟨hΩ, hgU, hpos⟩
    · exact hF.comp contDiff_snd.contDiffOn (fun x hx => hx.2.1)
    · intro x hx hxG
      have hxD : (x.1, x.2) ∈ DomR k ρ z z' := ⟨hx.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = F x.2
      rw [if_pos hxD]
      exact hFe x.2 hx.2.1 hxG
  · intro x hx h hh h' hh'
    obtain ⟨hΩ, hG, hpos⟩ := hx
    have hD : (x.1, h * x.2 * h') ∈ DomR k ρ z z' :=
      ⟨hΩ, Formalism.FourierDecayAlt.P.Qx5.Glev_mul (Formalism.FourierDecayAlt.P.Qx5.Glev_mul (hUW hh) hG) (hUW hh'),
        by rw [Formalism.FourierDecayAlt.P5.Rad.GGl_uw hh hh']; exact hpos⟩
    have hD0 : (x.1, x.2) ∈ DomR k ρ z z' := ⟨hΩ, hG, hpos⟩
    show (if (x.1, h * x.2 * h') ∈ DomR k ρ z z' then f (h * x.2 * h') else 0) =
      π h ∘SL (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) ∘SL π' h'
    rw [if_pos hD, if_pos hD0]
    exact hequiv x.2 hG hpos h hh h' hh'
  · intro x hx
    show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = f x.2
    exact if_pos hx

theorem determinant_vanishing_holds : ZxDet := by
  intro r h hh v
  unfold PBQ.zxH
  rw [Matrix.det_reindex_self, Matrix.det_mul]
  exact mul_ne_zero (LeftFubiniLemmas.lh_unit _ v).ne_zero
    (Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (fun a => Formalism.FourierDecayAlt.P.PBJ.Asm.ptScal_ne h hh.1 a a.isLt))

end Formalism.FourierDecayAlt.P.CutEX

namespace Formalism.FourierDecayAlt.P

theorem residue_top_exceptional_level : CutEX.ResTop := CutEX.residue_top_exceptional
theorem radial_extension_exceptional : CutEX.RadExt := CutEX.radial_extension_holds
theorem radial_of_function_exceptional : CutEX.RadOfFun := CutEX.radial_of_function_holds
theorem determinant_exceptional_holds : CutEX.ZxDet := CutEX.determinant_vanishing_holds

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaV
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem jda_capelli_toda_mirror_proof : JDACapTodaV :=
  jDACapTodaV_of_parts toda_coefficient_holds TVG.toda_group_action_holds toda_coordinate_holds

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateLowerBound
section
namespace Formalism.FourierDecayAlt.P

theorem germ_at_place : FormNormSumIdentities.GermPlace :=
  FormNormSumIdentities.germPlace_of slice_integral_cutoff slice_germ_points form_model

theorem germ_rate_lower_bound : GermRateSplit.GermRateLowB :=
  FormNormSumIdentities.germRateLowB_of germ_at_place germ_null_set_compact germ_constant

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RulesEq
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

theorem rules_eq : CutHB.RulesEq := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj _hF
  refine ⟨fun g hg m hm => ⟨minorDomain_mul_unipotent p.T.base j hg.2 hm, ?_⟩,
    fun g hg a => ⟨domP_N_mul p.T.base j hg.2 (nL_mem hj a), ?_⟩⟩
  · exact pbF_right _ _ _ F g m hm
  · show pbF (p.T.bs j) p.T.base _ F (LevelPointCoordinates.nL P.k P.r j hj a * g) =
      psi P.k P.r p.T.base.z cStd (LevelPointCoordinates.nL P.k P.r j hj a) • pbF (p.T.bs j) p.T.base _ F g
    rw [nL_castM hj a, pbF_left_rn p.T.base _ (p.T.bs j).z_mem F (cL a, 0) g,
      psi_castM _ (p.T.bs j).z p.T.base.z (p.T.z_lev j (by omega))]

end Formalism.FourierDecayAlt.P
end
end

