module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0004

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TopWeightFalseZeroEqOne
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

def tgHD (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ)
    (du : Fin (2 * segS X.TT j + 1) → ℕ) (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) : ℕ :=
  (∑ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i *
    ((jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) * ω ((topOdd X j i, true), Fin.succ 0) +
      (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) * ω ((topOdd X j i, false), Fin.succ 0))) +
  (L.jp j * (ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0)) +
    du (chU _) * ω ((topEnd X j, true), Fin.succ 0))

def tgWM (X : Loc) (j : Fin (numSeg X.TT)) (A : MonH X) (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) : ℕ :=
  (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
    (A ((topOdd X j i, true), c) * ω ((topOdd X j i, true), c) + A ((topOdd X j i, false), c) * ω ((topOdd X j i, false), c))) +
  ∑ c : Fin (X.m + 1), (A ((topEnd X j, true), c) * ω ((topEnd X j, true), c) +
    A ((topEnd X j, false), c) * ω ((topEnd X j, false), c))

variable (O : Type) [CommRing O] [IsDomain O]

theorem tg_segMon_wh (j : Fin (numSeg X.TT)) (A : MonH X) (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) :
    IsWeightedHomogeneous ω (segMon O X j A) (tgWM X j A ω) := by
  have h1 : IsWeightedHomogeneous ω (∏ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
      ((MvPolynomial.X ((topOdd X j i, true), c) : RHH O X) ^ A ((topOdd X j i, true), c) *
        MvPolynomial.X ((topOdd X j i, false), c) ^ A ((topOdd X j i, false), c)))
      (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
        (A ((topOdd X j i, true), c) • ω ((topOdd X j i, true), c) +
          A ((topOdd X j i, false), c) • ω ((topOdd X j i, false), c))) :=
    IsWeightedHomogeneous.prod _ _ _ (fun i _ => IsWeightedHomogeneous.prod _ _ _ (fun c _ =>
      ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)))
  have h2 : IsWeightedHomogeneous ω (∏ c : Fin (X.m + 1),
      ((MvPolynomial.X ((topEnd X j, true), c) : RHH O X) ^ A ((topEnd X j, true), c) *
        MvPolynomial.X ((topEnd X j, false), c) ^ A ((topEnd X j, false), c)))
      (∑ c : Fin (X.m + 1), (A ((topEnd X j, true), c) • ω ((topEnd X j, true), c) +
          A ((topEnd X j, false), c) • ω ((topEnd X j, false), c))) :=
    IsWeightedHomogeneous.prod _ _ _ (fun c _ =>
      ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _))
  exact h1.mul h2

theorem tg_head_wh (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ)
    (Gu : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) (du : Fin (2 * segS X.TT j + 1) → ℕ)
    (hG : Gu ∈ Pol (KK O) X.m du)
    (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) (hc : ∀ x (c c' : Fin X.m), ω (x, c.succ) = ω (x, c'.succ))
    (hU : ∀ i : Fin (segS X.TT j),
      ω ((topOdd X j i, true), 0) + ω ((topOdd X j i, false), 0) =
      ω ((topOdd X j i, true), Fin.succ 0) + ω ((topOdd X j i, false), Fin.succ 0))
    (hP : ω ((topEnd X j, true), 0) + ω ((topEnd X j, false), 0) =
      ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0)) :
    IsWeightedHomogeneous ω (L.head O j ju Gu) (tgHD L j ju du ω) := by
  let ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ :=
    fun v => symLev X.p C0 CE1 CE2 X j v * ω (symVar C0 CE1 CE2 X j v)
  let ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ := fun a => ω' (Sum.inl (a, 0))
  have h1 : ∀ a c, ω' (Sum.inl (a, c)) = ωL a := by
    intro a c
    simp only [ω', ωL, symLev, symVar]
    split_ifs <;> rw [hc _ c 0]
  have e0 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ)) =
      Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val) (2 * segS X.TT j + 1) = 2 * i.val
    omega
  have e1 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ) + 1) =
      Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val + 1) (2 * segS X.TT j + 1) = 2 * i.val + 1
    omega
  have hW : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [symbol_variable_lower_letter, symbol_level_lower_letter]
  have hE : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [sv_E, sl_E]
  have hUU : ωL (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      ω ((topEnd X j, true), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_U, sl_U, one_mul]
  have hXi : ωL (Fin.last _) = ω ((topEnd X j, false), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_xi, sl_xi, one_mul]
  have hZ : ∀ (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool), ω' (Sum.inr (Fin.castSucc l, β)) =
      (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) * ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β), 0) := by
    intro l β
    simp only [ω']
    rw [sv_Z, sl_Z]
  have hx : ∀ β : Bool, ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, β)) = ω ((topEnd X j, !β), 0) := by
    intro β
    simp only [ω']
    rw [symbol_variable_last, symbol_level_last, one_mul]
  have h2 : ∀ l : Fin (X.seg C0 CE1 CE2 j).t, ω' (Sum.inr (Fin.castSucc l, false)) + ω' (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ))) +
        ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1)) := by
    intro l
    rw [hZ, hZ, e0, e1, hW, hE, ← mul_add, ← mul_add]
    congr 1
    exact hU _
  have h3 : ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, false)) + ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, true)) =
      ωL (Fin.castSucc ⟨2 * segS X.TT j, by omega⟩) + ωL (Fin.last _) := by
    rw [hx, hx, hUU, hXi]
    exact hP
  have hEh : ∀ l : Fin (X.seg C0 CE1 CE2 j).t, IsWeightedHomogeneous ω' ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) l)
      (ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ))) +
        ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1))) := by
    intro l
    refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_)
    · rw [← h2 l]
      exact (isWeightedHomogeneous_X _ ω' _).mul (isWeightedHomogeneous_X _ ω' _)
    · have := (isWeightedHomogeneous_X (KK O) ω' (Sum.inl (finPos (2 * segS X.TT j + 1)
          (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)), c))).mul
        (isWeightedHomogeneous_X (KK O) ω' (Sum.inl (finPos (2 * segS X.TT j + 1)
          (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1), c)))
      rw [h1, h1] at this
      exact this
  have hEp : IsWeightedHomogeneous ω' ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m))
      (ωL (Fin.castSucc ⟨2 * segS X.TT j, by omega⟩) + ωL (Fin.last _)) := by
    refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_)
    · rw [← h3]
      exact (isWeightedHomogeneous_X _ ω' _).mul (isWeightedHomogeneous_X _ ω' _)
    · have := (isWeightedHomogeneous_X (KK O) ω' (Sum.inl (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ :
          Fin (2 * segS X.TT j + 1)), c))).mul
        (isWeightedHomogeneous_X (KK O) ω' (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)))
      rw [h1, h1] at this
      exact this
  have hA := IsWeightedHomogeneous.prod Finset.univ
    (fun l : Fin (X.seg C0 CE1 CE2 j).t => (BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) l ^ ju l) _
    (fun l _ => (hEh l).pow (ju l))
  have hB := hEp.pow (L.jp j)
  have hY := wh_chain (t := (X.seg C0 CE1 CE2 j).t) ω' ωL h1 du Gu hG
  have hall := (hA.mul hB).mul hY
  have hfin := wh_aeval ω (symVar C0 CE1 CE2 X j) (symLev X.p C0 CE1 CE2 X j) _ _ hall
  refine wh_congr hfin ?_
  have hs1 : ∑ a : Fin (2 * segS X.TT j + 1), jE (X.seg C0 CE1 CE2 j) ju (a.val / 2) * ωL (Fin.castSucc a) =
      ∑ i : Fin (segS X.TT j), (jE (X.seg C0 CE1 CE2 j) ju i.val *
          ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        jE (X.seg C0 CE1 CE2 j) ju i.val * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) := by
    rw [sum_chain]
    have t0 : jE (X.seg C0 CE1 CE2 j) ju ((2 * segS X.TT j) / 2) = 0 := by
      rw [Nat.mul_div_cancel_left _ (by norm_num)]; exact jE_top _ ju
    show (∑ i : Fin (segS X.TT j), (jE (X.seg C0 CE1 CE2 j) ju ((2 * i.val) / 2) * ωL _ +
      jE (X.seg C0 CE1 CE2 j) ju ((2 * i.val + 1) / 2) * ωL _)) + jE (X.seg C0 CE1 CE2 j) ju ((2 * segS X.TT j) / 2) * ωL _ = _
    rw [t0, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, hE, show 2 * i.val / 2 = i.val by omega, show (2 * i.val + 1) / 2 = i.val by omega]
  have hs2 : ∑ a : Fin (2 * segS X.TT j + 1), du a * ωL (Fin.castSucc a) =
      ∑ i : Fin (segS X.TT j), (du (chW i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        du (chE i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) +
      du (chU _) * ω ((topEnd X j, true), Fin.succ 0) := by
    rw [sum_chain, hUU]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, hE]
    rfl
  simp only [smul_eq_mul]
  rw [← tie_sum (X.seg C0 CE1 CE2 j) ju ωL, hs1, hs2, hUU, hXi]
  unfold tgHD
  have e : ∑ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i *
      ((jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) * ω ((topOdd X j i, true), Fin.succ 0) +
        (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) * ω ((topOdd X j i, false), Fin.succ 0)) =
      ∑ i : Fin (segS X.TT j), (jE (X.seg C0 CE1 CE2 j) ju i.val *
          ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        jE (X.seg C0 CE1 CE2 j) ju i.val * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) +
      ∑ i : Fin (segS X.TT j), (du (chW i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        du (chE i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

end

def tgWN (X : Loc) : (X.TT × Bool) × Fin (X.m + 1) → ℕ := fun v =>
  if ((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨ ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1) then 1 else 0

theorem weight_tgWN (X : Loc) (m : MonH X) : Finsupp.weight (tgWN X) m = ndM X m := by
  unfold ndM degUS
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold tgWN
  by_cases h : ((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨ ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1)
  · rw [if_pos h, if_pos h, smul_eq_mul, mul_one]
  · rw [if_neg h, if_neg h, smul_eq_mul, mul_zero]

theorem tgWN_true_zero_eq_zero (X : Loc) (t : X.TT) : tgWN X ((t, true), 0) = 0 := by simp [tgWN, hhLetters]
theorem tgWN_ts (X : Loc) (t : X.TT) (c : Fin X.m) : tgWN X ((t, true), c.succ) = 1 := by simp [tgWN, hhLetters]
theorem top_weight_false_zero_eq_one (X : Loc) (t : X.TT) : tgWN X ((t, false), 0) = 1 := by simp [tgWN, hhLetters]
theorem tgWN_fs (X : Loc) (t : X.TT) (c : Fin X.m) : tgWN X ((t, false), c.succ) = 0 := by simp [tgWN, hhLetters]

theorem tg_nd_eval {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X} (L : LvDat C0 CE1 CE2 mu X β)
    (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) :
    tgHD L j ju du (tgWN X) + tgWM X j A (tgWN X) =
      nuSeg C0 CE1 CE2 X j ju (L.jp j) du A + A ((topEnd X j, false), 0) := by
  unfold tgHD tgWM nuSeg
  simp only [Fin.sum_univ_succ, tgWN_true_zero_eq_zero, tgWN_ts, top_weight_false_zero_eq_one, tgWN_fs, mul_one, mul_zero, add_zero, zero_add,
    Finset.sum_add_distrib, Finset.sum_const_zero]
  ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.YcondCongr
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem ycond_congr {K : Type} [CommRing K] {N r : ℕ} [NeZero r] {LL LL' : ChainLetters N} (h : LL.vec = LL'.vec) (j : ℕ)
    (M : WithTop ℤ) : YCond K (r := r) LL j M = YCond K (r := r) LL' j M := by
  simp only [YCond, chWt, chStable, h]

section E

variable {s r : ℕ}

theorem chW_ne_chE (i i' : Fin s) : chW i ≠ chE i' := by
  simp only [chW, chE, ne_eq, Fin.mk.injEq]
  omega

theorem chW_ne_chU (i : Fin s) : chW i ≠ chU s := by
  simp only [chW, chU, ne_eq, Fin.mk.injEq]
  have := i.2
  omega

theorem chE_ne_chU (i : Fin s) : chE i ≠ chU s := by
  simp only [chE, chU, ne_eq, Fin.mk.injEq]
  have := i.2
  omega

theorem chW_inj {i i' : Fin s} (h : chW i = chW i') : i = i' := by
  simp only [chW, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

theorem chE_inj {i i' : Fin s} (h : chE i = chE i') : i = i' := by
  simp only [chE, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

def eCh (a0 : Fin (2 * s + 1)) : Fin (2 * s + 1) → ℕ := fun a => if a = a0 then 1 else 0

def dEps (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) : Fin (2 * s + 1) → ℕ :=
  (∑ i, ∑ c, (ez i c • eCh (chW i) + ey i c • eCh (chE i))) + ∑ c, ax c • eCh (chU s)

theorem mEps_pol (K : Type) [CommRing K] [Nontrivial K] (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    mEps K ez ey ax ∈ Pol K r (dEps ez ey ax) := by
  classical
  unfold mEps dEps
  refine hom_Pol_mul K (pol_prod' _ _ _ fun i _ => pol_prod' _ _ _ fun c _ => ?_) (pol_prod' _ _ _ fun c _ => ?_)
  · exact hom_Pol_mul K (pol_pow' (pol_X' (chW i) c) _) (pol_pow' (pol_X' (chE i) c) _)
  · exact pol_pow' (pol_X' (chU s) c) _

theorem dEps_chW_eq_sum (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) (i : Fin s) : dEps ez ey ax (chW i) = ∑ c, ez i c := by
  have hWW : ∀ c, chW i = chW c ↔ i = c := fun c => ⟨chW_inj, fun h => h ▸ rfl⟩
  simp only [dEps, eCh, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hWW, chW_ne_chE i,
    chW_ne_chU i, if_false, mul_zero, add_zero, Finset.sum_const_zero, mul_ite, mul_one]
  rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun c _ => if_neg (fun h => hb h.symm))
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem dEps_E (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) (i : Fin s) : dEps ez ey ax (chE i) = ∑ c, ey i c := by
  have hEE : ∀ c, chE i = chE c ↔ i = c := fun c => ⟨chE_inj, fun h => h ▸ rfl⟩
  have hEW : ∀ c, chE i = chW c ↔ False := fun c => ⟨fun h => chW_ne_chE c i h.symm, False.elim⟩
  simp only [dEps, eCh, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hEE, hEW,
    chE_ne_chU i, if_false, mul_zero, add_zero, zero_add, Finset.sum_const_zero, mul_ite, mul_one]
  rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun c _ => if_neg (fun h => hb h.symm))
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem dEps_U (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) : dEps ez ey ax (chU s) = ∑ c, ax c := by
  have hUW : ∀ c, chU s = chW c ↔ False := fun c => ⟨fun h => chW_ne_chU c h.symm, False.elim⟩
  have hUE : ∀ c, chU s = chE c ↔ False := fun c => ⟨fun h => chE_ne_chU c h.symm, False.elim⟩
  simp [dEps, eCh, hUW, hUE]

theorem mEps_int {O : Type} [CommRing O] [IsDomain O] (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    mEps (KK O) ez ey ax ∈ IntPol O (Fin (2 * s + 1) × Fin r) :=
  ⟨mEps O ez ey ax, by simp [mEps]⟩

variable {K : Type} [Field K] [CharZero K] [NeZero r]

theorem ycond_mEps (LL : ChainLetters (2 * s + 1)) (J : ℕ) (hE : ∀ i : Fin s, LL.vec (chE i) = false)
    (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    mEps K ez ey ax ∈ YCond K (r := r) LL J
      (((∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) + ((∑ c, ax c : ℕ) : ℤ) * (vWt LL J (chU s) : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  unfold mEps
  rw [WithTop.coe_add]
  refine ycond_mul LL J _ _ (ycond_prod LL J _ _ _ fun i _ => ?_) ?_
  · have h1 := ycond_prod (K := K) LL J Finset.univ (fun c : Fin r => (ez i c : ℤ) * (vWt LL J (chW i) : ℤ))
      (fun c => X (chW i, c) ^ ez i c * X (chE i, c) ^ ey i c) (fun c _ => by
        have a1 := ycond_pow LL J _ (ycond_X (K := K) LL J (chW i) c) (ez i c)
        have a2 := ycond_pow LL J _ (ycond_X (K := K) LL J (chE i) c) (ey i c)
        have hv : vWt LL J (chE i) = 0 := by unfold vWt; rw [if_neg]; rw [hE i]; simp
        rw [hv] at a2
        have := ycond_mul LL J _ _ a1 a2
        rw [← WithTop.coe_add] at this
        simpa using this)
    rw [← Finset.sum_mul] at h1
    rw [Nat.cast_sum]
    exact h1
  · have h1 := ycond_prod (K := K) LL J Finset.univ (fun c : Fin r => (ax c : ℤ) * (vWt LL J (chU s) : ℤ))
      (fun c => X (chU s, c) ^ ax c) (fun c _ => ycond_pow LL J _ (ycond_X (K := K) LL J (chU s) c) (ax c))
    rw [← Finset.sum_mul] at h1
    rw [Nat.cast_sum]
    exact h1

theorem ycond_pairs (S : SegData s) (LL : ChainLetters (2 * s + 1)) (J : ℕ) (hW : ∀ i : Fin s, LL.vec (chW i) = true)
    (hE : ∀ i : Fin s, LL.vec (chE i) = false) (k : Fin S.t → ℕ) :
    ∏ l, pairU K r S l ^ k l ∈ YCond K (r := r) LL J
      ((∑ l, (k l : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) : ℤ) : WithTop ℤ) :=
  ycond_prod LL J _ _ _ fun l _ => ycond_pow LL J _ (ycond_pair LL J _ _ (hW _) (hE _)) (k l)

theorem pWt_sum_le (S : SegData s) (LL : ChainLetters (2 * s + 1)) (J : ℕ) :
    (∑ l : Fin S.t, pWt J (chW (uTop S l)) (chE (uTop S l))) + vWt LL J (chU s) ≤ 1 := by
  have hu : ∀ l : Fin S.t, ((uTop S l : Fin s) : ℕ) = S.sigma + l := fun l => rfl
  have hlt : ∀ l : Fin S.t, S.sigma + (l : ℕ) < s := fun l => by rw [← hu]; exact (uTop S l).2
  by_cases hJ : ∃ l : Fin S.t, J = 2 * (S.sigma + (l : ℕ)) + 1
  · obtain ⟨l0, hl0⟩ := hJ
    have hsum : ∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) = 1 := by
      rw [Finset.sum_eq_single l0]
      · simp only [pWt, chW, chE, hu]
        rw [if_pos]
        constructor <;> omega
      · intro l _ hl
        simp only [pWt, chW, chE, hu]
        rw [if_neg]
        rintro ⟨h1, h2⟩
        apply hl
        exact Fin.ext (by omega)
      · intro h
        exact absurd (Finset.mem_univ l0) h
    have hv : vWt LL J (chU s) = 0 := by
      simp only [vWt, chU]
      have := hlt l0
      apply ite_eq_right_iff.mpr
      intro h
      exact absurd h.2 (by omega)
    omega
  · have hsum : ∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      simp only [pWt, chW, chE, hu]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hJ ⟨l, by omega⟩
    have hv : vWt LL J (chU s) ≤ 1 := by
      unfold vWt
      split_ifs <;> omega
    omega

theorem rowInc_le (S : SegData s) (LL : ChainLetters (2 * s + 1)) (J : ℕ) (ez : Fin s → Fin r → ℕ) (ax : Fin r → ℕ)
    (k : Fin S.t → ℕ) (Qe : ℕ) (h1 : ∀ i, ∑ c, ez i c ≤ Qe) (h2 : ∑ c, ax c ≤ Qe) (h3 : ∀ l, k l ≤ Qe) :
    ((∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) + ((∑ c, ax c : ℕ) : ℤ) * (vWt LL J (chU s) : ℤ)) +
      ∑ l, (k l : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) ≤ ((s : ℤ) + 1) * Qe := by
  have hv : ∀ a, (vWt LL J a : ℤ) ≤ 1 := fun a => by
    unfold vWt
    split_ifs <;> simp
  have hA : (∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) ≤ (s : ℤ) * Qe := by
    calc (∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) ≤ ∑ _i : Fin s, (Qe : ℤ) :=
          Finset.sum_le_sum fun i _ => by
            have e1 : ((∑ c, ez i c : ℕ) : ℤ) ≤ Qe := by exact_mod_cast h1 i
            have e2 := hv (chW i)
            have e3 : (0 : ℤ) ≤ ((∑ c, ez i c : ℕ) : ℤ) := Nat.cast_nonneg _
            have e4 : (0 : ℤ) ≤ (vWt LL J (chW i) : ℤ) := Nat.cast_nonneg _
            nlinarith
      _ = (s : ℤ) * Qe := by simp
  have hpw := pWt_sum_le S LL J
  have e3 : ((∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) : ℕ) : ℤ) + (vWt LL J (chU s) : ℤ) ≤ 1 := by
    exact_mod_cast hpw
  push_cast at e3
  have eB : ((∑ c, ax c : ℕ) : ℤ) * (vWt LL J (chU s) : ℤ) ≤ (Qe : ℤ) * (vWt LL J (chU s) : ℤ) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (Nat.cast_nonneg _)
  have eC : ∑ l, (k l : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) ≤
      ∑ l, (Qe : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) :=
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (by exact_mod_cast h3 l) (Nat.cast_nonneg _)
  rw [← Finset.mul_sum] at eC
  have eQ := mul_le_mul_of_nonneg_left e3 (Nat.cast_nonneg Qe : (0 : ℤ) ≤ Qe)
  nlinarith

end E

def capIdx {s : ℕ} (S : SegData s) (k : Fin (S.t + 1)) : ℕ := if h : (k : ℕ) < S.t then (uTop S ⟨k, h⟩ : ℕ) else s

theorem thr_eq {s r : ℕ} (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (mu : ℝ) (b : SegBlock s r) (k : Fin (S.t + 1)) :
    (blockData p S aTop aPlus mu b).T.thr k = ((⌊((cap p S b (capIdx S k) : ℤ) : ℝ) - mu⌋ : ℤ) : WithTop ℤ) := by
  show (segmentCapacities p S b k).map (fun x : ℤ => ⌊(x : ℝ) - mu⌋) = _
  unfold segmentCapacities capIdx
  split_ifs with h <;> rfl

end Formalism.MainNotions.ColumnSystems.Pf
end
end

