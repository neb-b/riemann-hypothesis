module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0111
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0100

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DpsiIsDerivation
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

section dpsi

variable {k r : ℕ}

theorem hpk_col_esI (a : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r l (esI k r a) = if l.val = a.val then 1 else 0 := by
  have ha := a.isLt
  have hl := l.isLt
  unfold Hpk esI
  by_cases hla : l.val = a.val
  · rw [if_pos (by simp only [Fin.val_mk]; omega), if_pos hla]
  · rw [if_neg (by simp only [Fin.val_mk]; omega), if_neg (by simp only [Fin.val_mk]; omega),
      if_neg (by simp only [Fin.ext_iff, Fin.val_mk]; omega), if_neg hla]

theorem hpk_W_row (w p : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r w p = if p = w then Hpk k r w w else 0 := by
  by_cases hpw : p = w
  · subst hpw
    simp
  · rw [if_neg hpw]
    have hp := p.isLt
    unfold Hpk
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hpw h.2.2.symm)]

theorem hpk_W_col (w p : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r p w = if p = w then Hpk k r w w else 0 := by
  by_cases hpw : p = w
  · subst hpw
    simp
  · rw [if_neg hpw]
    have hp := p.isLt
    unfold Hpk
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hpw h.2.2)]

theorem hpk_W_sq (w : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) : Hpk k r w w * Hpk k r w w = 1 := by
  unfold Hpk
  rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hw.1, hw.2, rfl⟩]
  split_ifs <;> norm_num

theorem herm_Hpk_bvec_eq_star_mul_diag_of_middle (z' : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    herm (Hpk k r) (bvec p) z' = star (z' p) * Hpk k r p p := by
  have hc : ∀ l, Hpk k r l p = if l = p then Hpk k r p p else 0 := fun l => hpk_W_col p l hp
  unfold herm bvec
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single p]
  · intro l _ hl
    rw [hc l, if_neg hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem unit_entry (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (i j : Fin (2 * r + k + 1)) :
    (∑ l, star (X l i) * Hpk k r l j) + ∑ l, Hpk k r i l * X l j = 0 := by
  have h := congrFun (congrFun hU i) j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h

theorem unit_a (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (a : Fin r) (ha : a.val + 1 < r) :
    X (esI k r ⟨a.val + 1, ha⟩) (esI k r a) = -star (X (eI k r a) (eI k r ⟨a.val + 1, ha⟩)) := by
  have hcol : ∀ l, Hpk k r l (esI k r a) = if l = eI k r a then 1 else 0 := by
    intro l
    rw [hpk_col_esI]
    simp only [eI, Fin.ext_iff]
  have hrow : ∀ l, Hpk k r (eI k r ⟨a.val + 1, ha⟩) l = if l = esI k r ⟨a.val + 1, ha⟩ then 1 else 0 := by
    intro l
    unfold Hpk eI esI
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega) | omega | norm_num | simp_all | (simp_all; omega)
  have h := unit_entry X hU (eI k r ⟨a.val + 1, ha⟩) (esI k r a)
  simp only [hcol, hrow, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  linear_combination h

theorem unit_w (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (hr : 1 ≤ r) (w : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r w w * X w (esI k r ⟨r - 1, by omega⟩) = -star (X (eI k r ⟨r - 1, by omega⟩) w) := by
  have hcol : ∀ l, Hpk k r l (esI k r ⟨r - 1, by omega⟩) = if l = eI k r ⟨r - 1, by omega⟩ then 1 else 0 := by
    intro l
    rw [hpk_col_esI]
    simp only [eI, Fin.ext_iff]
  have hrow : ∀ l, Hpk k r w l = if l = w then Hpk k r w w else 0 := fun l => hpk_W_row w l hw
  have h := unit_entry X hU w (esI k r ⟨r - 1, by omega⟩)
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [Finset.sum_eq_single w (fun l _ hl => by rw [hrow l, if_neg hl, zero_mul])
    (fun h' => absurd (Finset.mem_univ w) h')] at h
  linear_combination h

end dpsi

theorem dpsi_is_derivation : DpsiDerivation := by
  intro k r z' X hr hz' hU _

  let in1 : Fin (2 * r + k + 1) → ℂ := fun p => if h : p.val + 1 < r then X p ⟨p.val + 1, by omega⟩ else 0
  let in2 : Fin (2 * r + k + 1) → ℂ := fun p => if p.val + 1 = r then (X *ᵥ z') p else 0
  let in3 : Fin (2 * r + k + 1) → ℂ := fun p => -star (X (eI k r ⟨r - 1, by omega⟩) p * z' p)
  let in4 : Fin (2 * r + k + 1) → ℂ := fun p => if h : r + k < p.val ∧ p.val + 1 < 2 * r + k + 1 then X p ⟨p.val + 1, h.2⟩ else 0
  have hrow : ∀ p : Fin (2 * r + k + 1), ∑ q, X p q * dpsiP k r z' p q =
      in1 p + in2 p + (if r ≤ p.val ∧ p.val ≤ r + k then X p (esI k r ⟨r - 1, by omega⟩) * herm (Hpk k r) (bvec p) z' else 0)
        + in4 p := by
    intro p
    by_cases h1 : p.val + 1 < r
    · rw [Finset.sum_eq_single ⟨p.val + 1, by omega⟩]
      · rw [dp1 _ _ _ (by omega) (by simp; omega), if_pos (by simp), mul_one]
        simp only [in1, in2, in4, dif_pos h1, if_neg (show ¬ p.val + 1 = r by omega), dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
          if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
        ring
      · intro q _ hq
        by_cases hq1 : q.val < r
        · rw [dp1 _ _ _ (by omega) hq1, if_neg, mul_zero]; intro h'; apply hq; ext; simp; omega
        · by_cases hq2 : q.val ≤ r + k
          · rw [dp2 _ _ _ (by omega) (by omega) hq2, if_neg (by omega), mul_zero]
          · rw [dp0 _ _ _ (by omega) (by omega), mul_zero]
      · simp
    · by_cases h2 : p.val + 1 = r
      · have hterm : ∀ q, X p q * dpsiP k r z' p q = X p q * z' q := by
          intro q
          by_cases hq1 : q.val < r
          · rw [dp1 _ _ _ (by omega) hq1, if_neg (by omega), hz' q (by omega)]
          · by_cases hq2 : q.val ≤ r + k
            · rw [dp2 _ _ _ (by omega) (by omega) hq2, if_pos h2]
            · rw [dp0 _ _ _ (by omega) (by omega), hz' q (by omega)]
        simp only [hterm, in1, in2, in4, dif_neg h1, if_pos h2, dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
          if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
        simp [Matrix.mulVec, dotProduct]
      · by_cases h3 : p.val ≤ r + k
        · rw [Finset.sum_eq_single (esI k r ⟨r - 1, by omega⟩)]
          · rw [dp3 _ _ _ (by omega) h3 (by simp [esI]; omega), if_pos (by simp [esI]; omega)]
            simp only [in1, in2, in4, dif_neg h1, if_neg h2, dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
              if_pos (show r ≤ p.val ∧ p.val ≤ r + k by omega)]
            ring
          · intro q _ hq
            by_cases hq1 : q.val ≤ r + k
            · have : ¬ (r ≤ q.val ∧ q.val ≤ r + k ∧ r + k < q.val) := by omega
              unfold dpsiP; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_zero]
            · rw [dp3 _ _ _ (by omega) h3 (by omega), if_neg, mul_zero]
              intro h'; apply hq; ext; simp [esI]; omega
          · simp
        · by_cases h4 : p.val + 1 < 2 * r + k + 1
          · rw [Finset.sum_eq_single ⟨p.val + 1, h4⟩]
            · rw [dp4 _ _ _ (by omega) (by simp; omega), if_pos (by simp), mul_one]
              simp only [in1, in2, in4, dif_neg h1, if_neg h2, dif_pos (show r + k < p.val ∧ p.val + 1 < 2 * r + k + 1 from ⟨by omega, h4⟩),
                if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
              ring
            · intro q _ hq
              by_cases hq1 : r + k < q.val
              · rw [dp4 _ _ _ (by omega) hq1, if_neg, mul_zero]; intro h'; apply hq; ext; simp; omega
              · unfold dpsiP; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_zero]
            · simp
          · rw [Finset.sum_eq_zero]
            · simp only [in1, in2, in4, dif_neg h1, if_neg h2, dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
                if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
              ring
            · intro q _
              by_cases hq1 : r + k < q.val
              · rw [dp4 _ _ _ (by omega) hq1, if_neg (by omega), mul_zero]
              · unfold dpsiP; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_zero]

  have h3eq : ∀ p : Fin (2 * r + k + 1), (if r ≤ p.val ∧ p.val ≤ r + k then X p (esI k r ⟨r - 1, by omega⟩) * herm (Hpk k r) (bvec p) z' else 0) =
      in3 p := by
    intro p
    simp only [in3]
    split_ifs with hp
    · rw [herm_Hpk_bvec_eq_star_mul_diag_of_middle z' p hp]
      have hu := unit_w X hU hr p hp
      have hsq := hpk_W_sq (k := k) p hp
      rw [star_mul']
      linear_combination (star (z' p)) * hu
        + (X p (esI k r ⟨r - 1, by omega⟩) * star (z' p)) * (hpk_W_sq (k := k) p hp) - (X p (esI k r ⟨r - 1, by omega⟩) * star (z' p)) * (hpk_W_sq (k := k) p hp)
    · rw [hz' p (by omega)]; simp
  simp_rw [hrow, h3eq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  set L1 : ℂ := ∑ a : Fin r, if h : a.val + 1 < r then X (eI k r a) (eI k r ⟨a.val + 1, h⟩) else 0 with hL1
  set M2 : ℂ := (X *ᵥ z') (eI k r ⟨r - 1, by omega⟩) with hM2
  have s2 : ∑ p, in2 p = M2 := by
    rw [Finset.sum_eq_single (eI k r ⟨r - 1, by omega⟩)]
    · simp only [in2]; rw [if_pos (show (eI k r ⟨r - 1, by omega⟩).val + 1 = r by simp [eI]; omega)]
    · intro p _ hp; simp only [in2]; rw [if_neg]; intro h'; apply hp; ext; simp [eI]; omega
    · simp
  have s3 : ∑ p, in3 p = -star M2 := by
    simp only [in3, M2, Matrix.mulVec, dotProduct]
    rw [Finset.sum_neg_distrib, star_sum]
  have e1inj : Function.Injective (eI k r) := fun a b h => by
    have := congrArg Fin.val h; simp [eI] at this; exact Fin.ext this
  have s1 : ∑ p, in1 p = L1 := by
    rw [hL1, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨eI k r, e1inj⟩))]
    · rw [Finset.sum_map]; rfl
    · intro p _ hp
      simp only [in1]
      rw [dif_neg]
      intro h'
      apply hp
      exact Finset.mem_map.mpr ⟨⟨p.val, by omega⟩, Finset.mem_univ _, by ext; simp [eI]⟩
  have e4inj : Function.Injective (fun a : Fin r => (⟨2 * r + k - 1 - a.val, by omega⟩ : Fin (2 * r + k + 1))) := by
    intro a b h; have := congrArg Fin.val h; simp at this; have := a.isLt; have := b.isLt; exact Fin.ext (by omega)
  have s4 : ∑ p, in4 p = -star L1 := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨_, e4inj⟩))]
    · rw [Finset.sum_map, hL1, star_sum, ← Finset.sum_neg_distrib]
      congr 1; ext a
      have hav := a.isLt
      simp only [in4, Function.Embedding.coeFn_mk]
      by_cases ha : a.val + 1 < r
      · rw [dif_pos ⟨by omega, by omega⟩, dif_pos ha]
        have hu := unit_a X hU a ha
        have e1 : (⟨2 * r + k - 1 - a.val, by omega⟩ : Fin (2 * r + k + 1)) = esI k r ⟨a.val + 1, ha⟩ := by
          ext; simp [esI]; omega
        have e2 : (⟨2 * r + k - 1 - a.val + 1, by omega⟩ : Fin (2 * r + k + 1)) = esI k r a := by
          ext; simp [esI]; omega
        have hx : ∀ p q : Fin (2 * r + k + 1), p = esI k r ⟨a.val + 1, ha⟩ → q = esI k r a →
            X p q = X (esI k r ⟨a.val + 1, ha⟩) (esI k r a) := by
          rintro p q rfl rfl; rfl
        rw [hx _ _ e1 e2, hu]
      · rw [dif_neg (by omega), dif_neg ha, star_zero, neg_zero]
    · intro p _ hp
      simp only [in4]
      rw [dif_neg]
      rintro ⟨h1, h2⟩
      apply hp
      exact Finset.mem_map.mpr ⟨⟨2 * r + k - 1 - p.val, by omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
  rw [s1, s2, s3, s4]
  unfold dEll
  rw [← hL1, ← hM2, star_add]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FubiniRightIntegral
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBF

section slots

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {n r : ℕ}

theorem liftM_star (M : SlopeTestRemainingChoices (Fin n) A) : liftM (star M) = star (liftM M) := by
  ext z z'
  simp only [Matrix.star_apply, liftM_apply]
  by_cases h : z 0 = z' 0
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem liftM_neg (M : SlopeTestRemainingChoices (Fin n) A) : liftM (-M) = -liftM M := by
  rw [← liftRingHom_apply_eq_liftM, map_neg, liftRingHom_apply_eq_liftM]

theorem liftM_sub (M N : SlopeTestRemainingChoices (Fin n) A) : liftM (M - N) = liftM M - liftM N := by
  rw [← liftRingHom_apply_eq_liftM, map_sub, liftRingHom_apply_eq_liftM, liftRingHom_apply_eq_liftM]

theorem liftM_pow (M : SlopeTestRemainingChoices (Fin n) A) (m : ℕ) : liftM (M ^ m) = liftM M ^ m := by
  rw [← liftRingHom_apply_eq_liftM, map_pow, liftRingHom_apply_eq_liftM]

theorem matrix_two_map_lift (a b c d : SlopeTestRemainingChoices (Fin n) A) :
    (!![a, b; c, d] : M2 (SlopeTestRemainingChoices (Fin n) A)).map liftM = !![liftM a, liftM b; liftM c, liftM d] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

structure Lifted (f : FrameData (Fin n) A) (f' : FrameData (Fin (n + 1)) A) : Prop where
  F : f'.F = liftM f.F
  ee : ∀ Y, f'.ee Y = liftM (f.ee Y)
  x : ∀ Y, f'.x Y = liftM (f.x Y)
  xi : ∀ Y, f'.xi Y = liftM (f.xi Y)
  c : f'.c = liftM f.c
  ci : f'.ci = liftM f.ci
  q : f'.q = f.q
  N : f'.N = f.N

variable (L : LevelData A r)

theorem io_lift (x : A) : (io x : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (io x) := io_succ x

theorem lifted_l {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y : ℂ) :
    f'.l L Y = liftM (f.l L Y) := by
  simp only [FrameData.l, kapL, liftM_add, liftM_mul, hf.ee Y, io_lift]

theorem lifted_m {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y : ℂ) :
    f'.m L Y = liftM (f.m L Y) := by
  simp only [FrameData.m, FrameData.d, FrameData.di, wt, wti, liftM_mul, liftM_pow, hf.N, hf.c, hf.ci,
    lifted_l L hf, liftM_star, io_lift]

theorem lifted_DD {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y Ya : ℂ) :
    f'.DD Y Ya = liftM (f.DD Y Ya) := by
  simp only [FrameData.DD, liftM_smul, liftM_sub, hf.ee]

theorem tz_lift : (tz L : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (tz L) := io_succ _

theorem lifted_plus {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (a : Fin n)
    (Ya : ℂ) : Lifted (f.plus L a Ya) (f'.plus L a.succ Ya) := by
  refine ⟨?_, fun Y => ?_, fun Y => ?_, fun Y => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [FrameData.plus]
    rw [hf.F, liftM_mul, ← ins_succ, map_mul_liftM, matrix_two_map_lift, matrix_two_map_lift, lifted_l L hf]
    simp only [liftM_mul, liftM_zero, liftM_one, io_lift]
  · simp only [FrameData.plus]
    rw [← ins_succ, matrix_two_map_lift]
    simp only [liftM_add, liftM_sub, liftM_mul, liftM_neg, liftM_smul, liftM_zero, liftM_one, hf.ee, hf.x, hf.xi,
      lifted_DD hf, tz_lift]
  · simp only [FrameData.plus]
    rw [hf.x, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.plus]
    rw [hf.xi, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.plus]
    rw [hf.c, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.plus]
    rw [hf.ci, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.plus, hf.q]
  · simp only [FrameData.plus, hf.N]

theorem lifted_minus {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (b : Fin n)
    (Yb : ℂ) : Lifted (f.minus L b Yb) (f'.minus L b.succ Yb) := by
  refine ⟨?_, fun Y => ?_, fun Y => ?_, fun Y => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [FrameData.minus]
    rw [hf.F, liftM_mul, ← ins_succ, map_mul_liftM, matrix_two_map_lift, matrix_two_map_lift, lifted_m L hf]
    simp only [liftM_mul, liftM_zero, liftM_one, io_lift]
  · simp only [FrameData.minus]
    rw [← ins_succ, matrix_two_map_lift]
    simp only [liftM_add, liftM_sub, liftM_mul, liftM_neg, liftM_smul, liftM_zero, liftM_one, hf.ee, hf.x, hf.xi,
      hf.q, lifted_DD hf, tz_lift]
  · simp only [FrameData.minus]
    rw [hf.x, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.minus]
    rw [hf.xi, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.minus]
    rw [hf.c, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.minus]
    rw [hf.ci, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.minus, hf.q]
  · simp only [FrameData.minus, hf.N]

theorem lifted_ofWord (st : Start A) :
    ∀ u : List (Letter ℂ (Fin n)), Lifted (ofWord L st u) (ofWord L st (u.map upL))
  | [] => ⟨by simp [ofWord, Start.frame, liftM_one], fun Y => io_succ _, fun Y => io_succ _, fun Y => io_succ _,
      by simp [ofWord, Start.frame, liftM_one], by simp [ofWord, Start.frame, liftM_one], rfl, rfl⟩
  | l :: u => by
    have ih := lifted_ofWord st u
    rw [List.map_cons]
    by_cases hp : l.plus
    · have e1 : ofWord L st (l :: u) = (ofWord L st u).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      have e2 : ofWord L st (upL l :: u.map upL) = (ofWord L st (u.map upL)).plus L l.intersection_update_fsHerm_neg_one.succ l.pt := by
        simp [ofWord, upL, hp]
      rw [e1, e2]
      exact lifted_plus L ih l.intersection_update_fsHerm_neg_one l.pt
    · have e1 : ofWord L st (l :: u) = (ofWord L st u).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      have e2 : ofWord L st (upL l :: u.map upL) = (ofWord L st (u.map upL)).minus L l.intersection_update_fsHerm_neg_one.succ l.pt := by
        simp [ofWord, upL, hp]
      rw [e1, e2]
      exact lifted_minus L ih l.intersection_update_fsHerm_neg_one l.pt

theorem bT_lift (σ : Site A) : ∀ u : List (Letter ℂ (Fin n)), bT σ (u.map upL) = liftM (bT σ u)
  | [] => by simp [bT, liftM_one]
  | l :: u => by
    rw [List.map_cons, bT, bT, bT_lift σ u, liftM_mul]
    congr 1
    show ins l.intersection_update_fsHerm_neg_one.succ (lift0 (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star)) =
      liftM (ins l.intersection_update_fsHerm_neg_one (lift0 (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star)))
    rw [liftZero_succ_eq_map, ins_succ]

theorem bTA_lift (u : List (Letter ℂ (Fin n))) : TL.bTA L (u.map upL) = liftM (TL.bTA L u) := by
  simp only [TL.bTA, bT_lift]
  rw [← liftRingHom_apply_eq_liftM, map_list_prod, List.map_map]
  rfl

end slots

end Formalism.FourierDecayAlt.P.PBN
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTypesAtOfWeight
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Topx1
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem exAt (p : KB.Pl P Wp Wq) {ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    {m₀r : B.Mat P.k (P.r - P.r)} (hLev : LevFrame p ν'r m₀r)
    (Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
      (p.T.bs P.r).π')
    (x : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r)
    (hx : x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z')
    {γ₀ : B.Mat P.k (P.r - P.r)} (hγG : γ₀ ∈ B.GV P.k (P.r - P.r))
    (hζ : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)
    (hγF : D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀) :
    ∑ ρ : M.Ty P, (p.TP.E ρ).comp ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) =
      (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ := by
  classical
  have hV := grpInt_at_dframe p hLev Ψ x hx hγG hζ hγF
  have hPl : Q.IsPlace (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' :=
    Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T ⟨P.r, by omega⟩ p.hP
  have hn : P.r + (P.r - P.r) = P.r := by omega
  have hz : D.castV hn (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) = p.T.base.z := p.T.z_lev P.r le_rfl
  have hν : D.castV hn (liftVec P.k P.r (P.r - P.r) (m₀r *ᵥ ν'r)) = p.m₀ *ᵥ p.ν' := by
    rw [← Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.castV_mulVec_lift hn, hLev.1, hLev.2.1]
  have hπ : (p.T.bs P.r).π = fun y => p.T.base.π (D.castM hn (ιLev P.k P.r (P.r - P.r) y)) :=
    funext fun y => p.T.π_lev P.r le_rfl y
  have hcap : ∀ (Bs : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (w : ℂ) (v : Wp),
      Q.capRep P.k (P.r - P.r) (p.T.bs P.r).π Bs w v =
        Q.capRep P.k P.r p.T.base.π (fun c => D.castV hn (liftVec P.k P.r (P.r - P.r) (Bs c))) w v := by
    intro Bs w v
    rw [Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.capRep_lift_cast hn, hπ]
  have hfr : ∀ Bs : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ,
      Q.IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z, m₀r *ᵥ ν'r] Bs →
        Q.IsFrameOf P.k P.r [p.T.base.z, p.m₀ *ᵥ p.ν'] (fun c => D.castV hn (liftVec P.k P.r (P.r - P.r) (Bs c))) := by
    intro Bs hB
    have h := Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.frame_lift_cast hn _ Bs hB
    simpa only [List.map_cons, List.map_nil, hz, hν] using h
  let TP' : Top.TypeProj (JC.parLev P P.r) (p.T.bs P.r).π (p.T.bs P.r).z (m₀r *ᵥ ν'r) :=
    { E := p.TP.E
      idem := p.TP.idem
      orth := p.TP.orth
      selfAdj := p.TP.selfAdj
      eigen := fun Bs hB ρ w v => (hcap Bs w _).trans (p.TP.eigen _ (hfr Bs hB) ρ w v)
      full := fun Bs hB ρ v h => p.TP.full _ (hfr Bs hB) ρ v fun w => (hcap Bs w v).symm.trans (h w) }
  exact types_of_grpInt (JC.parLev P P.r) (p.T.bs P.r) ν'r m₀r TP' hPl hLev.2.2 _ hV

def HeadWeightAt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → LevFrame p ν'r m₀r →
    ∀ x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z',
    ∀ γ₀ ∈ B.GV P.k (P.r - P.r),
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
        Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 →
      D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀ →
    (∀ h : C.LPt, D.IsLocPt h P.r →
        ∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ =
          ∑ ρ : M.Ty P, ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w
              (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) e ρ ^ 2 : ℝ) : ℂ) •
            (p.TP.E ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀))

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem head_types_at_of_weight : PBI.HeadWeightAt → PBI.HeadTypesAt := by
  intro hW Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hI hC hCut hLev x hx γ₀ hγG hζ hγF
  exact ⟨fun Ψ => PBI.exAt p hLev Ψ x hx hγG hζ hγF,
    hW Wp Wq P p F w X μ L st Cb ν'r m₀r hD hI hC hCut hLev x hx γ₀ hγG hζ hγF⟩

end Formalism.FourierDecayAlt.P
end
end

