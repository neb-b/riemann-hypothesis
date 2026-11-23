module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0025
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1774
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweredWeightInterpolationAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingMonomialProductsLinearIndependent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaPrimeAllPoints
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

def wd (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau) : WeightData where
  k := D.R.k
  m := D.R.m
  t := D.R.t
  j := (j : ℕ) + 1
  e := ((D.hc τ).e_int j).choose
  v := fun n => if h : 2 ≤ n ∧ n - 2 < D.R.k - 1 then ((D.hc τ).v_int ⟨n - 2, h.2⟩).choose else 0
  b := fun n => if h : 1 ≤ n ∧ n - 1 < D.R.m then ((D.hc τ).b_int ⟨n - 1, h.2⟩).choose else 0

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem wd_e : ((wd D j τ).e : ℚ) = (D.hc τ).e j := ((D.hc τ).e_int j).choose_spec.symm

theorem wd_v (n : ℕ) (h : 2 ≤ n ∧ n - 2 < D.R.k - 1) : ((wd D j τ).v n : ℚ) = (D.hc τ).v ⟨n - 2, h.2⟩ := by
  show (((if h : 2 ≤ n ∧ n - 2 < D.R.k - 1 then ((D.hc τ).v_int ⟨n - 2, h.2⟩).choose else 0 : ℤ)) : ℚ) = _
  rw [dite_eq_left h]
  exact ((D.hc τ).v_int _).choose_spec.symm

theorem wd_b (n : ℕ) (h : 1 ≤ n ∧ n - 1 < D.R.m) : ((wd D j τ).b n : ℚ) = (D.hc τ).b ⟨n - 1, h.2⟩ := by
  show (((if h : 1 ≤ n ∧ n - 1 < D.R.m then ((D.hc τ).b_int ⟨n - 1, h.2⟩).choose else 0 : ℤ)) : ℚ) = _
  rw [dite_eq_left h]
  exact ((D.hc τ).b_int _).choose_spec.symm

end GlobalTheory.LiftWeightForced

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem wd_lam_lo (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k - 1) :
    ((wd D j τ).lam i : ℚ) = (D.hc τ).v ⟨i - 1, by omega⟩ := by
  have hk : (wd D j τ).k = D.R.k := rfl
  unfold WeightData.lam
  rw [if_pos (by rw [hk]; exact h2), wd_v D j τ (i + 1) ⟨by omega, by omega⟩]
  exact congrArg _ (Fin.ext (by simp))

theorem wd_lam_hi (i : ℕ) (h1 : D.R.k - 1 < i) (h2 : i - (D.R.k - 1) - 1 < D.R.m) :
    ((wd D j τ).lam i : ℚ) = -(D.hc τ).b ⟨i - (D.R.k - 1) - 1, h2⟩ := by
  have hk : (wd D j τ).k = D.R.k := rfl
  unfold WeightData.lam
  rw [if_neg (by rw [hk]; omega)]
  push_cast
  rw [hk, wd_b D j τ _ ⟨by omega, h2⟩]

theorem wd_hyp : (wd D j τ).Hyp := by
  have hR := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hjm := j.2
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  set P := D.hc τ with hP
  have hu : ∀ a b : Fin D.R.k, a.1 = b.1 → P.u a = P.u b := fun a b h => congrArg _ (Fin.ext h)
  have hb : ∀ a b : Fin D.R.m, a.1 = b.1 → P.b a = P.b b := fun a b h => congrArg _ (Fin.ext h)
  refine ⟨show 1 ≤ D.R.k by omega, show 1 ≤ (j : ℕ) + 1 by omega, show (j : ℕ) + 1 ≤ D.R.m by omega, ?_, D.R.t_odd, ?_, ?_, ?_⟩
  · show Odd (D.R.k + D.R.m - 1)
    exact Nat.Even.sub_odd (by omega) (D.R.k_even.add D.R.m_even) odd_one
  · intro i hi1 hi2
    have hi2' : i < D.R.k + D.R.m - 1 := hi2
    suffices ((wd D j τ).lam (i + 1) : ℚ) < (wd D j τ).lam i by exact_mod_cast this
    rcases lt_trichotomy (i + 1) (D.R.k) with h | h | h
    · rw [wd_lam_lo D j τ (i + 1) (by omega) (by omega), wd_lam_lo D j τ i hi1 (by omega)]
      have h1 := P.u_gt_v ⟨i, by omega⟩
      have h2 := P.v_gt_u ⟨i - 1, by omega⟩
      rw [hu ⟨i - 1 + 1, _⟩ ⟨i, by omega⟩ (by simp; omega)] at h2
      have e1 : (⟨i + 1 - 1, by omega⟩ : Fin (D.R.k - 1)) = ⟨i, by omega⟩ := Fin.ext (by simp)
      rw [e1]
      exact h1.trans h2
    · rw [wd_lam_hi D j τ (i + 1) (by omega) (by omega), wd_lam_lo D j τ i hi1 (by omega)]
      have h1 := P.u_last_gt (by omega) (by omega)
      have h2 := P.v_gt_u ⟨i - 1, by omega⟩
      rw [hu ⟨i - 1 + 1, _⟩ ⟨D.R.k - 1, by omega⟩ (by simp; omega)] at h2
      rw [hb ⟨i + 1 - (D.R.k - 1) - 1, _⟩ ⟨0, by omega⟩ (by simp; omega)]
      exact h1.trans h2
    · rw [wd_lam_hi D j τ (i + 1) (by omega) (by omega), wd_lam_hi D j τ i (by omega) (by omega)]
      have h1 := P.gap_be ⟨i - (D.R.k - 1) - 1, by omega⟩
      have h2 := P.gap_eb ⟨i - (D.R.k - 1) - 1, by omega⟩ (by simp; omega)
      rw [hb ⟨i - (D.R.k - 1) - 1 + 1, _⟩ ⟨i + 1 - (D.R.k - 1) - 1, by omega⟩ (by simp; omega)] at h2
      linarith
  · show (((wd D j τ).b ((j : ℕ) + 1)) : ℤ) < (wd D j τ).e
    suffices ((wd D j τ).b ((j : ℕ) + 1) : ℚ) < (wd D j τ).e by exact_mod_cast this
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ j (by simp)]
    have := P.gap_be j
    linarith
  · intro hj'
    have hj'' : (j : ℕ) + 1 < D.R.m := hj'
    show ((wd D j τ).e : ℤ) < (wd D j τ).b ((j : ℕ) + 1 + 1)
    suffices ((wd D j τ).e : ℚ) < (wd D j τ).b ((j : ℕ) + 1 + 1) by exact_mod_cast this
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ ⟨(j : ℕ) + 1, hj''⟩ (by simp)]
    have := P.gap_eb j hj''
    linarith

theorem wd_gap : (wd D j τ).GapHyp := by
  have hjm := j.2
  set P := D.hc τ with hP
  have hb : ∀ a b : Fin D.R.m, a.1 = b.1 → P.b a = P.b b := fun a b h => congrArg _ (Fin.ext h)
  refine ⟨?_, ?_⟩
  · show ((D.R.t : ℚ) + 3) / 2 ≤ ((wd D j τ).e : ℚ) - (wd D j τ).b ((j : ℕ) + 1)
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ j (by simp)]
    exact P.gap_be j
  · intro hj'
    have hj'' : (j : ℕ) + 1 < D.R.m := hj'
    show ((D.R.t : ℚ) + 3) / 2 ≤ ((wd D j τ).b ((j : ℕ) + 1 + 1) : ℚ) - (wd D j τ).e
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ ⟨(j : ℕ) + 1, hj''⟩ (by simp)]
    exact P.gap_eb j hj''

end GlobalTheory.LiftWeightForced

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem exists_isLamPrime :
    ∃ lam : DomWeight (Vc D j).rank, Formalism.IndefR.Bridge.IsLamPrime (D := D) lam ((j : ℕ) + 1) τ := by
  have hjm := j.2
  have hC := GlobalTheory.LowestKType.thetaSide (wd D j τ) (wd_hyp D j τ) (wd_gap D j τ)
  have hint := hC.2.2.2.1
  have hdom := hC.2.2.2.2.1
  have hN : (Vc D j).rank = (wd D j τ).nV := D.sp.V_rank _ (by omega) (by omega)

  have hmono : ∀ d a : ℕ, 1 ≤ a → a + d ≤ (wd D j τ).nV →
      (wd D j τ).lamPrime (a + d) ≤ (wd D j τ).lamPrime a := by
    intro d
    induction d with
    | zero => intro a _ _; simp
    | succ d ih =>
      intro a ha had
      have := hdom (a + d) (by omega) (by omega)
      rw [← add_assoc]
      exact this.trans (ih a ha (by omega))
  let w : Fin (Vc D j).rank → ℤ := fun i => (hint (i.1 + 1) (by omega) (by have := i.2; omega)).choose
  have hw : ∀ i, (w i : ℚ) = (wd D j τ).lamPrime (i.1 + 1) := fun i =>
    (hint (i.1 + 1) (by omega) (by have := i.2; omega)).choose_spec.symm
  have hanti : Antitone w := by
    intro a b hab
    have hab' : a.1 ≤ b.1 := hab
    have := hmono (b.1 - a.1) (a.1 + 1) (by omega) (by have := b.2; omega)
    rw [show a.1 + 1 + (b.1 - a.1) = b.1 + 1 by omega] at this
    have h' : (w b : ℚ) ≤ w a := by rw [hw, hw]; exact this
    exact_mod_cast h'
  refine ⟨⟨w, hanti⟩, ⟨by omega, by omega⟩, wd D j τ, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [wd_e]
    exact congrArg _ (Fin.ext (by simp))
  · intro a
    rw [wd_v D j τ _ ⟨by omega, by have := a.2; omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  · intro a
    rw [wd_b D j τ _ ⟨by omega, by have := a.2; omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  · intro i
    exact hw i

theorem isLamPrime_lamLdef :
    Formalism.IndefR.Bridge.IsLamPrime (D := D)
      (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
  have hex := exists_isLamPrime D j τ
  unfold Formalism.IndefR.Bridge.lamLdef
  rw [dite_eq_left hex]
  exact hex.choose_spec

end GlobalTheory.LiftWeightForced
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.ExpTie.Lift

variable {D : D7}

abbrev lamL (j : Fin D.R.m) (τ : D.what₂.Tau) : DomWeight (Vc D j).rank :=
  Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ

def lamT (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) : ℕ :=
  if h : a < (Vc D j).rank then (lamL j τ).natW ⟨a, h⟩ else 0

def cT (j : Fin D.R.m) (τ : D.what₂.Tau) : ℝ :=
  ((Vc D j).rank : ℝ) / 2 - 1 - ((lamL j τ).detShift : ℝ)


open Classical in
def wts (L : SizeData₂ D) (j : Fin D.R.m) : Wts D.what₂.Tau where
  lam := lamT j
  T2 := Finset.univ.filter fun τ => (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
  j := fun _ => (j : ℕ) + 1
  q := fun _ => D.R.m - ((j : ℕ) + 1)
  xm := fun τ => ⌈cT j τ⌉
  xp := fun τ => ⌊cT j τ + L.Sc⌋
  c := cT j
  e := fun τ => wj D ((j : ℕ) + 1) τ
  fr := fun _ τ => τ
  cj := fun _ _ => false
  Sp := Formalism.MainNotions.JumpSetsAlt.excSet D

def ValsAt (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) : Prop :=
  (∀ (a : ℕ) (ha : a < D.R.k - 1),
      ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ = (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ)) ∧
    (∀ i : Fin D.R.m, (i : ℕ) ≤ j →
      ((wts L j).U (parOf L j) τ (D.R.k - 1 + i) : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ)) ∧
    (∀ s : ℕ, s < D.R.t →
      ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) - (wts L j).c τ =
        -wj D ((j : ℕ) + 1) τ + ((D.R.t : ℝ) - 1) / 2 - s) ∧
    (∀ i : Fin D.R.m, (j : ℕ) < i →
      ((wts L j).U (parOf L j) τ (D.R.k - 1 + i + D.R.t) : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ))

end GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

open Formalism.IndefR.Bridge

variable {D : D7}

theorem lamT_of_lt (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (h : a < (Vc D j).rank) :
    (lamT j τ a : ℤ) = (lamL j τ).w ⟨a, h⟩ - (lamL j τ).detShift := by
  have hn : 0 < (Vc D j).rank := by omega
  have hle : (lamL j τ).detShift ≤ (lamL j τ).w ⟨a, h⟩ := by
    unfold DomWeight.detShift
    rw [dite_eq_left hn]
    exact (lamL j τ).anti (Fin.mk_le_mk.2 (by omega))
  unfold lamT DomWeight.natW
  rw [dite_eq_left h]
  omega

theorem anti (L : SizeData₂ D) (j : Fin D.R.m) : ∀ τ a b, a ≤ b → b < (parOf L j).Nr → (wts L j).lam τ b ≤ (wts L j).lam τ a := by
  intro τ a b hab hb
  have ha : a < (Vc D j).rank := lt_of_le_of_lt hab hb
  have h1 := lamT_of_lt j τ a ha
  have h2 := lamT_of_lt j τ b hb
  have h3 := (lamL j τ).anti (show (⟨a, ha⟩ : Fin _) ≤ ⟨b, hb⟩ from Fin.mk_le_mk.2 hab)
  show lamT j τ b ≤ lamT j τ a
  omega

theorem rank_eq (j : Fin D.R.m) : (Vc D j).rank = D.R.k - 1 + D.R.m + D.R.t := by
  have h := D.sp.V_rank ((j : ℕ) + 1) (by omega) (by omega)
  have hk := D.R.m_add_three_le_k
  simp only [Vc, h, Ranks.nV, Ranks.r]
  omega

theorem what₂ (L : SizeData₂ D) (j : Fin D.R.m) : ∀ τ, Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t + (wts L j).q τ = (parOf L j).Nr := by
  intro τ
  have := rank_eq j
  have hj := j.2
  simp only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]
  omega

end GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

open Formalism.IndefR.Bridge

variable {D : D7}

theorem U_last (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) :
    (wts L j).U (parOf L j) τ ((Vc D j).rank - 1) = 0 := by
  have hn := rank_eq j
  have ht0 := D.R.t_odd.pos
  have hlt : (Vc D j).rank - 1 < (Vc D j).rank := by omega
  have h1 := lamT_of_lt j τ _ hlt
  have h2 : (lamL j τ).detShift = (lamL j τ).w ⟨(Vc D j).rank - 1, hlt⟩ := by
    unfold DomWeight.detShift; rw [dite_eq_left (by omega)]
  show Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) ((Vc D j).rank - 1) = 0
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem liftWeightCombinatorialData_U_le_U_zero (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    (wts L j).U (parOf L j) τ a ≤ (wts L j).U (parOf L j) τ 0 := by
  have h := anti L j τ 0 a (Nat.zero_le _) ha
  show Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) 0
  change lamT j τ a ≤ lamT j τ 0 at h
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem U_nonneg (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    0 ≤ (wts L j).U (parOf L j) τ a := by
  show 0 ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem T2_card (L : SizeData₂ D) (j : Fin D.R.m) : (wts L j).T2.card ≤ D.host.T2.card := by
  classical
  calc (wts L j).T2.card ≤ D.host.thickPlaces.card := by
        refine Finset.card_le_card_of_injOn (fun τ => (D.eTau τ : D.R.GG)) ?_ ?_
        · intro τ hτ
          simp only [wts, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ
          exact hτ
        · intro a _ b _ h
          exact D.eTau.injective (Subtype.ext h)
    _ ≤ D.host.T2.card := by
        unfold Host.thickPlaces
        exact Finset.card_image_le

theorem c_le (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (hv : ValsAt L j τ) :
    (wts L j).c τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2 := by
  have hn := rank_eq j
  have hU := U_last L j τ
  have ht : (1 : ℝ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have ht0 := D.R.t_odd.pos
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm : 0 < D.R.m := by omega
  by_cases hj : (j : ℕ) + 1 < D.R.m
  · have h := hv.2.2.2 ⟨D.R.m - 1, by omega⟩ (by simp; omega)
    have hrow : D.R.k - 1 + (D.R.m - 1) + D.R.t = (Vc D j).rank - 1 := by omega
    simp only [hrow, hU] at h
    have hg := (D.hc τ).gap_be ⟨D.R.m - 1, by omega⟩
    have hw : wj D D.R.m τ = (((D.hc τ).e ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) := by
      unfold wj; rw [dite_eq_left (by omega)]
    have hg' : (((D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) + ((D.R.t : ℝ) + 3) / 2 ≤
        (((D.hc τ).e ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) := by
      have h2 : ((((D.hc τ).e ⟨D.R.m - 1, by omega⟩ - (D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ)) : ℝ) ≥ ((((D.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) := by
        exact_mod_cast hg
      push_cast at h2
      linarith
    push_cast at h
    rw [hw]; linarith
  · have hjm : (j : ℕ) + 1 = D.R.m := by omega
    have h := hv.2.2.1 (D.R.t - 1) (by omega)
    have hrow : D.R.k + (j : ℕ) + (D.R.t - 1) = (Vc D j).rank - 1 := by omega
    simp only [hrow, hU] at h
    have hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hts, hjm] at h
    push_cast at h
    linarith

end GlobalTheory.ExpTie.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocZero
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertAvg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem tens_inj (v : Pl (F := F)) {κ : Type} (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0)
    (hRt : ∀ x z, At (evFin F v) z → R (x + z) = R x) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (e : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hRt 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

section Grp
variable {n : ℕ} {W : Spc F E n}

end Grp

section Loc
variable {a a' : ℕ} {B : Base F E} (G : Geo σ a a') {X : Chars F E}


variable {G} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

end Loc

end GlobalTheory.InertAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnipotentEmbeddingsExistStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unipotent_embeddings_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW (t.comp σ)) = 0 ∧ (uT Y).map (piW t) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW t) = 0 ∧ GlobalTheory.LinWAt.coW G t (uM z) = z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinWAt.coW G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinWAt.coW G t x i j * (u.map (piW t)) i j) := by
  first | exact @GlobalTheory.LinWCoords.exists_split_coords | exact GlobalTheory.LinWCoords.exists_split_coords | (intros; apply GlobalTheory.LinWCoords.exists_split_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerRankCuspFormsDetWeightOneComponent
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem GlobalTheory.ShareOn.lowerRank_oneComponent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa), GlobalTheory.Shares.Margins X.toData Xa → 0 < X.p0 → X.p0 < r → GapsGe X.p0 Xa.L 1 → PairGe Xa.L (1.9 * Xa.T) → GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0 → PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1 → ∀ s : ℕ, Even s → s ≤ Xa.T → ∀ u : Frame X.Ψ r → ℂ, u ∈ X.SS (deMul X.Ψ r X.p0 s) → (∃ x ∈ X.dom, u x ≠ 0) → ∃ g : Fin (Fl.δ * (Xa.T + nd X.toData).choose (nd X.toData)) → Frame X.Ψ r → ℂ, (∀ q, g q ∈ X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s)) ∧ ∀ a : _ → ℂ, (∀ x ∈ X.dom, ∑ q, a q * g q x = 0) → a = 0 := by
  intro E _ _ _ r X Xa Fl hM hp0 hp0r hg1 hp1 hg2 hp2 s hs hsT u hu hune
  classical
  have hF := _root_.GlobalTheory.LowerInterp.lowered_interp E r X Xa Fl hM hp0 hp0r hg1 hp1 hg2 hp2 s hs hsT u hu hune
  choose F hFd hFval hFss using hF
  set M := ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X.toData) (Xa.T + 1) with hM'
  have hMcard : M.card = (Xa.T + nd X.toData).choose (nd X.toData) := by
    have e : M = ReciprocityTheory.L2DbarEstimates.Y.multiLe (nd X.toData) Xa.T := by
      ext α
      rw [ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff, ReciprocityTheory.L2DbarEstimates.Y.mem_multiLe_iff]
      omega
    rw [e]
    exact ReciprocityTheory.L2DbarEstimates.Y.ind_count (nd X.toData) Xa.T
  set PM := (Finset.univ : Finset (Fin Fl.δ)) ×ˢ M with hPM
  have hcard : PM.card = Fl.δ * (Xa.T + nd X.toData).choose (nd X.toData) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, hMcard]
  let e := (Finset.equivFinOfCardEq hcard).symm
  let f : Fin Fl.δ → (Fin (nd X.toData) → ℕ) → Frame X.Ψ r → ℂ :=
    fun j α x => F j x * monoM X.toData Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q)
  have hαT : ∀ α ∈ M, ∑ q, α q ≤ Xa.T := fun α hα => by
    rw [hM', ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff] at hα
    omega
  refine ⟨fun q => f (e q).1.1 (e q).1.2, fun q => ?_, fun a ha => ?_⟩
  · exact hFss _ _ (hαT _ (Finset.mem_product.mp (e q).2).2)
  · let cc : (Fin (nd X.toData) → ℕ) → Fin Fl.δ → ℂ := fun α j =>
      if h : (j, α) ∈ PM then a (e.symm ⟨(j, α), h⟩) else 0
    have hc : ∀ q, cc (e q).1.2 (e q).1.1 = a q := by
      intro q
      have h : ((e q).1.1, (e q).1.2) ∈ PM := (e q).2
      simp only [cc, dif_pos h]
      exact congrArg a (e.symm_apply_apply q)
    have hlead : ∀ x ∈ X.dom, leadM X.toData Fl.s Fl.w0 F Xa.T (Xa.T + 1) cc x = 0 := by
      intro x hx
      have h1 : leadM X.toData Fl.s Fl.w0 F Xa.T (Xa.T + 1) cc x =
          ∑ p ∈ PM, cc p.2 p.1 * f p.1 p.2 x := by
        unfold leadM
        rw [hPM, Finset.sum_product, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => ?_
        simp only [f]
        ring
      rw [h1, ← Finset.sum_coe_sort PM, ← e.sum_comp]
      rw [← ha x hx]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hc q]
    have h7 := _root_.GlobalTheory.JetIndepAtPts.leadM_coeff_zero E r X.toData Xa Fl F hFd hFval Xa.T cc hlead
    funext q
    rw [← hc q]
    exact h7 _ (Finset.mem_product.mp (e q).2).2 _
end

