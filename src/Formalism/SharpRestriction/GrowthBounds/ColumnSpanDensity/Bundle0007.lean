module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ThresholdFinalFacts
public import Formalism.PolynomialDimension.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0006

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DensAbs
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

theorem dens_abs (N : ℕ) (hN : 1 ≤ N) (x1 x2 wa wb e : ℝ) (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (hwa : 0 < wa) (hwb : 0 < wb)
    (he : 0 ≤ e) (hs : (N : ℝ) * (x1 + x2 + e / wa + e / wb) ≤ 1 / 2) :
    (wa + e) ^ N * (wb + e) ^ N ≤ 2 * ((1 - x1) * (1 - x2)) ^ N * (wa ^ N * wb ^ N) := by
  set u := e / wa with hu
  set v := e / wb with hv
  have hu0 : 0 ≤ u := div_nonneg he hwa.le
  have hv0 : 0 ≤ v := div_nonneg he hwb.le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs' : (N : ℝ) * x1 + N * x2 + N * u + N * v ≤ 1 / 2 := by nlinarith
  have hp1 : 0 ≤ (N : ℝ) * u := by positivity
  have hp2 : 0 ≤ (N : ℝ) * v := by positivity
  have hp3 : 0 ≤ (N : ℝ) * x1 := by positivity
  have hp4 : 0 ≤ (N : ℝ) * x2 := by positivity
  have hu1 : u ≤ 1 := by nlinarith
  have hv1 : v ≤ 1 := by nlinarith
  have hx1 : x1 ≤ 1 := by nlinarith
  have hx2 : x2 ≤ 1 := by nlinarith
  have hwa' : wa + e = wa * (1 + u) := by rw [hu]; field_simp
  have hwb' : wb + e = wb * (1 + v) := by rw [hv]; field_simp
  rw [hwa', hwb', mul_pow, mul_pow, mul_pow]

  have hB : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (1 + z) ^ N * (1 - N * z) ≤ 1 := by
    intro z hz0 hz1
    have hb := one_add_mul_le_pow (a := -z) (by linarith) N
    have hzz : (1 + -z) ^ N = (1 - z) ^ N := by ring
    have h1 : (1 + z) ^ N * (1 - z) ^ N ≤ 1 := by
      rw [← mul_pow]; exact pow_le_one₀ (by nlinarith) (by nlinarith)
    have h2 : 0 ≤ (1 + z) ^ N := by positivity
    calc (1 + z) ^ N * (1 - N * z) ≤ (1 + z) ^ N * (1 - z) ^ N :=
          mul_le_mul_of_nonneg_left (by linarith) h2
      _ ≤ 1 := h1
  have hC : ∀ x : ℝ, x ≤ 1 → 1 - N * x ≤ (1 - x) ^ N := by
    intro x hx1
    have hb := one_add_mul_le_pow (a := -x) (by linarith) N
    have hxx : (1 + -x) ^ N = (1 - x) ^ N := by ring
    linarith
  have ha := hB u hu0 hu1
  have hb := hB v hv0 hv1
  have hc := hC x1 hx1
  have hd := hC x2 hx2
  have hA0 : 0 ≤ (1 + u) ^ N := by positivity
  have hB0 : 0 ≤ (1 + v) ^ N := by positivity

  have e1 : 1 - N * u - N * v ≤ (1 - N * u) * (1 - N * v) := by nlinarith [mul_nonneg hp1 hp2]
  have e2 : 1 - N * x1 - N * x2 ≤ (1 - N * x1) * (1 - N * x2) := by nlinarith [mul_nonneg hp3 hp4]
  have e3 : (1 - N * u - N * v) * (1 - N * x1 - N * x2) ≤
      (1 - N * u) * (1 - N * v) * ((1 - N * x1) * (1 - N * x2)) :=
    mul_le_mul e1 e2 (by linarith) (by nlinarith)
  have e4 : 1 - (N * u + N * v) - (N * x1 + N * x2) ≤ (1 - N * u - N * v) * (1 - N * x1 - N * x2) := by
    nlinarith [mul_nonneg (add_nonneg hp1 hp2) (add_nonneg hp3 hp4)]
  have hprod : 1 ≤ 2 * ((1 - N * u) * (1 - N * v) * ((1 - N * x1) * (1 - N * x2))) := by linarith
  have hAB : (1 + u) ^ N * (1 + v) ^ N * ((1 - N * u) * (1 - N * v)) ≤ 1 := by
    have := mul_le_one₀ ha (mul_nonneg hB0 (by linarith)) hb
    calc (1 + u) ^ N * (1 + v) ^ N * ((1 - N * u) * (1 - N * v))
        = (1 + u) ^ N * (1 - N * u) * ((1 + v) ^ N * (1 - N * v)) := by ring
      _ ≤ 1 := this
  have hCD : (1 - N * x1) * (1 - N * x2) ≤ (1 - x1) ^ N * (1 - x2) ^ N :=
    mul_le_mul hc hd (by linarith) (le_trans (by linarith) hc)
  have key : (1 + u) ^ N * (1 + v) ^ N ≤ 2 * ((1 - x1) ^ N * (1 - x2) ^ N) := by
    have hγδ : 0 ≤ (1 - N * x1) * (1 - N * x2) := by nlinarith
    calc (1 + u) ^ N * (1 + v) ^ N
        ≤ (1 + u) ^ N * (1 + v) ^ N *
            (2 * ((1 - N * u) * (1 - N * v) * ((1 - N * x1) * (1 - N * x2)))) :=
          le_mul_of_one_le_right (mul_nonneg hA0 hB0) hprod
      _ = 2 * ((1 - N * x1) * (1 - N * x2)) *
            ((1 + u) ^ N * (1 + v) ^ N * ((1 - N * u) * (1 - N * v))) := by ring
      _ ≤ 2 * ((1 - N * x1) * (1 - N * x2)) * 1 :=
          mul_le_mul_of_nonneg_left hAB (by linarith)
      _ ≤ 2 * ((1 - x1) ^ N * (1 - x2) ^ N) := by linarith
  have hw : 0 ≤ wa ^ N * wb ^ N := by positivity
  calc wa ^ N * (1 + u) ^ N * (wb ^ N * (1 + v) ^ N)
      = (1 + u) ^ N * (1 + v) ^ N * (wa ^ N * wb ^ N) := by ring
    _ ≤ 2 * ((1 - x1) ^ N * (1 - x2) ^ N) * (wa ^ N * wb ^ N) := mul_le_mul_of_nonneg_right key hw

theorem Nexp_le (N Y La : ℝ) (hN : 2 ≤ N) (hY : 1 ≤ Y) (hLa : 8 * Real.log (N * Y) ≤ La) :
    N * Real.exp (-La / 3) ≤ 0.36 := by
  have hNY : 2 ≤ N * Y := by nlinarith
  have hL2 : Real.log 2 ≤ Real.log (N * Y) := Real.log_le_log (by norm_num) hNY
  have hlog2 := Real.log_two_gt_d9
  set L := Real.log (N * Y) with hL
  have hexpL : Real.exp L = N * Y := Real.exp_log (by linarith)
  have h1 : N ^ 2 ≤ Real.exp (2 * L) := by
    have hNY1 : N ≤ N * Y := by nlinarith
    rw [show 2 * L = L + L by ring, Real.exp_add, hexpL, sq]
    exact mul_le_mul hNY1 hNY1 (by linarith) (by linarith)
  have h2 : 1 + 2 * L / 3 ≤ Real.exp (2 * L / 3) := by linarith [Real.add_one_le_exp (2 * L / 3)]
  have h3 : Real.exp (2 * L) * Real.exp (2 * L / 3) ≤ Real.exp (La / 3) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have h4 : N ^ 2 * (1 + 2 * L / 3) ≤ Real.exp (La / 3) :=
    le_trans (mul_le_mul h1 h2 (by linarith) (Real.exp_pos _).le) h3
  have h5 : N ^ 2 * 1.46 ≤ Real.exp (La / 3) :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg N)) h4
  have hpos : 0 < Real.exp (La / 3) := Real.exp_pos _
  rw [show -La / 3 = -(La / 3) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankLetter
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

theorem hwt_apply (m A B : ℕ) (i : Fin (m + 2)) :
    hwt m A B i = if i = 0 then (A : ℤ) else if i = Fin.last (m + 1) then -(B : ℤ) else 0 := by
  unfold hwt
  induction i using Fin.cases with
  | zero => simp
  | succ j =>
    rw [Fin.cons_succ, if_neg (Fin.succ_ne_zero j)]
    induction j using Fin.lastCases with
    | last => simp [Fin.succ_last]
    | cast j =>
      rw [Fin.snoc_castSucc, if_neg]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega

theorem cov_apply (m : ℕ) (d : ℤ) (i : Fin (m + 2)) :
    (Fin.cons d (Fin.snoc (fun _ : Fin m => d) 0) : Fin (m + 2) → ℤ) i =
      if i = Fin.last (m + 1) then 0 else d := by
  induction i using Fin.cases with
  | zero =>
    rw [Fin.cons_zero, if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  | succ j =>
    rw [Fin.cons_succ]
    induction j using Fin.lastCases with
    | last => simp [Fin.succ_last]
    | cast j =>
      rw [Fin.snoc_castSucc, if_neg]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega

theorem dimHar_comm (k A B : ℕ) : dimHar k A B = dimHar k B A := by
  unfold dimHar
  rw [mul_comm (dimPol k A), mul_comm (dimPol k (A - 1))]
  simp only [or_comm]

theorem last_ne_zero' (m : ℕ) : Fin.last (m + 1) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem prod_tops {n' : ℕ} (TT : Finset (Fin n')) (f : TT → ℚ) :
    ∏ s : Fin n', (if h : s ∈ TT then f ⟨s, h⟩ else 1) = ∏ s : TT, f s := by
  classical
  have h1 : ∏ s : Fin n', (if h : s ∈ TT then f ⟨s, h⟩ else 1) =
      ∏ s ∈ TT, (if h : s ∈ TT then f ⟨s, h⟩ else 1) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro s _ hs
    rw [dite_eq_right hs]
  rw [h1, ← Finset.prod_attach, Finset.univ_eq_attach]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [dif_pos s.2]

theorem flatW_dom {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (A B : TT → ℕ) : IsDominant (flatW (m + 1) A B) := by
  intro s i j hij
  unfold flatW
  split_ifs with hs h1 h2 h3 h4 h5 h6 h7 <;> first | omega | skip
  all_goals
    first
    | (exfalso
       subst_vars
       first
       | exact absurd (Fin.le_zero_iff.1 hij) (by assumption)
       | exact absurd (le_antisymm (Fin.le_last _) hij) (by assumption))

theorem lamAt_flat {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (A B : TT → ℕ) (s : Fin n') :
    weylDim (m + 2) (lamAt (flatW (m + 1) A B) s) =
      if h : s ∈ TT then (dimHar (m + 1) (A ⟨s, h⟩) (B ⟨s, h⟩) : ℚ) else 1 := by
  by_cases hs : s ∈ TT
  · rw [dif_pos hs]
    unfold lamAt
    split_ifs with he
    · have : flatW (m + 1) A B s = hwt m (A ⟨s, hs⟩) (B ⟨s, hs⟩) := by
        funext i
        rw [hwt_apply]
        simp [flatW, hs]
      rw [this, weylDim_hwt_eq]
    · have : (fun i : Fin (m + 1 + 1) => -flatW (m + 1) A B s i.rev) = hwt m (B ⟨s, hs⟩) (A ⟨s, hs⟩) := by
        funext i
        rw [hwt_apply]
        simp only [flatW, hs, dif_pos]
        by_cases h0 : i = 0
        · subst h0
          rw [Fin.rev_zero, if_neg (last_ne_zero' m)]
          simp
        · by_cases hl : i = Fin.last (m + 1)
          · subst hl
            rw [Fin.rev_last]
            simp [last_ne_zero' m]
          · have h1 : i.rev ≠ 0 := by
              intro h
              apply hl
              rw [← Fin.rev_rev i, h, Fin.rev_zero]
            have h2 : i.rev ≠ Fin.last (m + 1) := by
              intro h
              apply h0
              rw [← Fin.rev_rev i, h, Fin.rev_last]
            rw [if_neg h1, if_neg h2, if_neg h0, if_neg hl, neg_zero]
      rw [this, weylDim_hwt_eq, dimHar_comm]
  · rw [dite_eq_right hs]
    have : lamAt (flatW (m + 1) A B) s = fun _ => (0 : ℤ) := by
      unfold lamAt
      split_ifs <;> funext i <;> simp [flatW, hs]
    rw [this, weylDim_zero]

theorem finrank_weyl (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (K : Type) [Field K] [CharZero K] (n : ℕ)
    (nu : Fin n → ℕ) (hnu : Antitone nu) :
    (Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K n n nu) : ℚ) = weylDim n (fun i => (nu i : ℤ)) := by
  rw [h3 K n nu hnu]
  unfold weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  push_cast
  rfl

theorem finrank_letter (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (K : Type) [Field K] [CharZero K] (m d : ℕ)
    (vec : Bool) :
    Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (letterWt (m + 1) d vec))) =
      dimPol (m + 1) d := by
  have hq : (Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K (m + 1 + 1) (m + 1 + 1) (nuOf (letterWt (m + 1) d vec))) : ℚ) =
      (dimPol (m + 1) d : ℚ) := by
    cases vec with
    | true =>
      have hnu : nuOf (letterWt (m + 1) d true) = fun i => if i = 0 then d else 0 := by
        funext i
        simp only [nuOf, letterWt, if_true, if_neg (last_ne_zero' m), sub_zero]
        split_ifs <;> simp
      have hanti : Antitone (nuOf (letterWt (m + 1) d true)) := by
        rw [hnu]
        intro i j hij
        simp only
        split_ifs with h1 h2 <;> first | omega | skip
        exact absurd (Fin.le_zero_iff.1 (h1 ▸ hij)) h2
      rw [finrank_weyl D h3 K _ _ hanti, ← weylDim_vec]
      congr 1
      funext i
      have := hwt_apply m d 0 i
      unfold hwt at this
      simp only [Nat.cast_zero, neg_zero] at this
      rw [this, hnu]
      by_cases h : i = 0 <;> simp [h]
    | false =>
      have hnu : nuOf (letterWt (m + 1) d false) = fun i => if i = Fin.last (m + 1) then 0 else d := by
        funext i
        simp only [nuOf, letterWt, Bool.false_eq_true, if_false, if_true]
        split_ifs <;> simp
      have hanti : Antitone (nuOf (letterWt (m + 1) d false)) := by
        rw [hnu]
        intro i j hij
        simp only
        by_cases hj : j = Fin.last (m + 1)
        · rw [if_pos hj]; exact Nat.zero_le _
        · have hi : i ≠ Fin.last (m + 1) := fun h => hj (le_antisymm (Fin.le_last _) (h ▸ hij))
          rw [if_neg hj, if_neg hi]
      rw [finrank_weyl D h3 K _ _ hanti, ← weylDim_cov]
      congr 1
      funext i
      rw [cov_apply, hnu]
      by_cases h : i = Fin.last (m + 1) <;> simp [h]
  exact_mod_cast hq

theorem restDims_of (D : Formalism.BasicNotions.D7) (h3 : Formalism.MainNotions.ColumnSystems.adm3 D) (hW : WeylV) : RestDims := by
  classical
  intro p n' R m hm TT A B
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have := R.charZero
  constructor
  · unfold dimHH VHH
    rw [finrank_tensor, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Fintype.prod_bool]
    unfold hhWt
    rw [finrank_letter D h3, finrank_letter D h3]
    have hA : ex A s.val = A s := by unfold ex; rw [dif_pos s.2]
    have hB : ex B s.val = B s := by unfold ex; rw [dif_pos s.2]
    unfold hhDeg
    simp only [if_true, Bool.false_eq_true, if_false, hA, hB]
    split_ifs
    · rfl
    · exact mul_comm _ _
  · have h := hW R.Kf n' (m + 1) (flatW (m + 1) A B) (flatW_dom m A B)
    have h2 : ((dimV R.Kf (flatW (m + 1) A B) : ℕ) : ℚ) =
        ∏ s : Fin n', weylDim (m + 2) (lamAt (flatW (m + 1) A B) s) := by
      rw [h]
      unfold weylDim
      refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      push_cast
      rfl
    simp only [lamAt_flat] at h2
    rw [prod_tops TT (fun s => (dimHar (m + 1) (A s) (B s) : ℚ))] at h2
    exact_mod_cast h2

end Formalism.MainNotions.flipOneThree.Pf

end
end

