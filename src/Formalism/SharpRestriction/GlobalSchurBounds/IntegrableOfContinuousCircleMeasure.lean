module

public import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LogVandermondeBounds.HookGammaAmgmMultinomialBounds
public import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0001
public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0001
public import Formalism.LogVandermondeBounds.Bundle0001
public import Formalism.GL3MeanSquares.HookFormulaTorsion.SquareMomentArithmeticBound

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipTwoThree

section PA
open Formalism.BasicNotions NumberField Finset

section Use

open Formalism.HermitianLattices.TraceIntegrality Formalism.LogVandermondeBounds.flipTwoThree

end Use

end PA

section PB
open Formalism.BasicNotions NumberField Finset

end PB

section PC
open Formalism.BasicNotions NumberField Finset

theorem b_nums {D : D7} {T g1 g2 : ℕ} {Cn x b L b' Sc eta : ℝ} (h : Nums D T g1 g2 Cn x b L b' Sc eta) :
    1 ≤ L ∧ 0 ≤ Cn ∧ 4 ≤ b' ∧ b' ≤ b ∧ (D.R.N D.R.m : ℝ) ≤ b' ∧ Sc + eta + D.R.m * D.R.t ≤ b' ∧
      Real.log (x * b * D.host.v) ≤ L ∧ 8 ≤ x * b * D.host.v := by
  obtain ⟨hb, hL, -, -, -, hbb, hSc, heta, hSe, -, -, -, hd, hx, hv, hN⟩ := h
  have hx0 : 0 < x := by linarith
  have hbb' : b' ≤ b := by rwa [mul_div_cancel_left₀ b hx0.ne'] at hbb
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr D.R.t_odd.pos.ne'
  have hmt : (2 : ℝ) ≤ D.R.m * D.R.t := by nlinarith [mul_nonneg (sub_nonneg.2 hm2) (sub_nonneg.2 ht1)]
  have hq : 4 ≤ b' / x := by linarith
  have hb'4x : 4 * x ≤ b' := by rwa [le_div_iff₀ hx0] at hq
  have hb'0 : 0 ≤ b' := by linarith
  have hb'4 : 4 ≤ b' := by linarith
  have hdiv : b' / x ≤ b' := div_le_self hb'0 (by linarith)
  have h8 : 8 ≤ x * b * D.host.v := by
    have hxb : 16 ≤ x * b := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x * b) (by linarith : (0 : ℝ) ≤ D.host.v - 1)]
  have hL1 : 1 ≤ L := by
    have h1 : (1 : ℝ) < Real.log 8 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_d9.trans (by norm_num)
    have h2 : Real.log 8 ≤ Real.log (x * b * D.host.v) := Real.log_le_log (by norm_num) h8
    linarith
  have hCn : 0 ≤ Cn := by
    by_contra hc
    push_neg at hc
    have : Cn * L < 0 := mul_neg_of_neg_of_pos hc (by linarith)
    linarith [abs_nonneg (dlogL D 1)]
  have hNb : (D.R.N D.R.m : ℝ) ≤ b' := by
    have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
    have hm3 : (8 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (D.R.m : ℝ) - 2)
        (by positivity : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 2 + 2 * D.R.m + 4)]
    have hA : (1 : ℝ) ≤ (1 + 2 * (2 * Cn + 4)) * (D.R.m : ℝ) ^ 3 := by
      nlinarith [mul_nonneg hCn (by positivity : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 3)]
    nlinarith [mul_nonneg (sub_nonneg.2 hA) hN0]
  exact ⟨hL1, hCn, hb'4, hbb', hNb, hSe.trans hdiv, hL, h8⟩

theorem b_lam_eq (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (i : Fin (D.R.N j)) :
    (((D.fm u).lam j τ).w i : ℚ) = lamLiftN D u τ i := by
  rw [(D.fm u).lam_eq j hj τ i]
  unfold lamLiftN lamCol wJ
  by_cases h : i.1 < D.R.k
  · rw [dite_eq_left h, if_pos h, dite_eq_left h]
  · rw [dite_eq_right h, if_neg h, dite_eq_left (D.R.blk_lt hj i h)]

theorem b_mem_tops (D : D7) (τ : D.what₂.Tau) : τ ∈ tops D ↔ IsTop D τ := by
  classical
  simp only [tops, topsOf, IsTop, plc, Finset.mem_filter, Finset.mem_univ, true_and]

theorem b_card_tops (D : D7) : (tops D).card = D.host.TT.card := by
  classical
  have hF := Formalism.BasicNotions.factTopsThick D.R D.host
  rw [← hF.2.2.2.1]
  symm
  refine Finset.card_bij (fun g hg => D.eTau.symm ⟨g, hF.1 g hg⟩) ?_ ?_ ?_
  · intro g hg
    rw [b_mem_tops]
    unfold IsTop plc
    rw [Equiv.apply_symm_apply]
    exact hg
  · intro g hg g' hg' h
    exact congrArg Subtype.val (D.eTau.symm.injective h)
  · intro τ hτ
    rw [b_mem_tops] at hτ
    refine ⟨plc D τ, hτ, ?_⟩
    apply D.eTau.injective
    rw [Equiv.apply_symm_apply]
    rfl

theorem b_Tu_pos (D : D7) (u : D.what₂.Word) : (0 : ℝ) < (Tu D u : ℝ) := by
  exact_mod_cast (D.mem u).A.T_prime.pos

end PC

section PD
open Formalism.BasicNotions NumberField Finset

end PD

section PE
open Formalism.BasicNotions NumberField Finset

end PE

section PF
open Formalism.BasicNotions NumberField Finset

end PF

section PG
open Formalism.BasicNotions NumberField Finset

end PG

section PH
open Formalism.BasicNotions NumberField Finset

def toEuc (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (w : Gx D i → ℂ) : EuclideanSpace ℂ (Gx D i) :=
  WithLp.toLp 2 fun g => (((Real.sqrt (Real.pi * D.gx.Om g.1 s))⁻¹ : ℝ) : ℂ) * w g

end PH

section PI
open Formalism.BasicNotions NumberField Finset

theorem b_finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have hb := (factEmb D.R D.host).1
  have h1 : Nat.card (D.R.GG) = Nat.card (D.host.E →+* ℂ) := Nat.card_congr (Equiv.ofBijective _ hb)
  have h2 : Nat.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E := by
    rw [Nat.card_eq_fintype_card]; exact NumberField.Embeddings.card D.host.E ℂ
  have h4 : Nat.card (D.R.GG) = 4 * D.R.ord := D.R.natCard_GG
  rw [← h2, ← h1, h4]
  simp only [Ranks.f, Ranks.n]
  ring

end PI

section Z2
open Formalism.BasicNotions

end Z2

section Z56a
open Formalism.BasicNotions NumberField
open Formalism.HermitianLattices.TraceIntegrality (Numbers wt plus MeanSquareWeightBound)

def colAbs (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  ∑ i ∈ Finset.range D.R.k, (lamCol D u τ i : ℝ)

def colAbsP (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  ∑ i ∈ Finset.range D.R.k, ((lamCol D u τ i : ℝ) - (lamCol D u τ (D.R.k - 1) : ℝ))

def firstColumnSpread (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  (lamCol D u τ 0 : ℝ) - (lamCol D u τ (D.R.k - 1) : ℝ)

theorem nums_basic {D : D7} {T g1 g2 : ℕ} {Cn x b L b' Sc eta : ℝ}
    (h : Nums D T g1 g2 Cn x b L b' Sc eta) : 1 ≤ L ∧ 0 ≤ Cn ∧ 4 ≤ b' ∧ b' ≤ b := by
  obtain ⟨h1, h2, h3, h4, -⟩ := b_nums h
  exact ⟨h1, h2, h3, h4⟩

theorem numbers_of_nums {D : D7} {T g1 g2 : ℕ} {Cn x b L b' Sc eta : ℝ} (K : ℝ) (hK1 : 1 ≤ K) (hKx : K ≤ x)
    (h : Nums D T g1 g2 Cn x b L b' Sc eta) :
    Numbers (2 * Cn + 4) (x * b) b' L D.host.v (Real.log T) (Real.log ((g1 : ℝ) * g2)) eta (K * Sc)
      D.R.k D.R.m D.R.t (D.R.N D.R.m) := by
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic h
  obtain ⟨hb, hL, hT, hg1, hg2, hb', hSc, heta, hsm, hsq, hlin, hmn, hdl, hx, hv, hpow⟩ := h
  have hx0 : (0 : ℝ) < x := by linarith
  have hmt : (0 : ℝ) ≤ (D.R.m : ℝ) * D.R.t := by positivity
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := by positivity
  refine ⟨hL1, hv, hL, by linarith, ?_, Real.log_natCast_nonneg _, ?_, ?_, ?_, ?_, ?_, rfl, by linarith,
    by positivity, ?_, hsq, hlin, hpow⟩
  · nlinarith
  · have : 0 ≤ (D.R.m : ℝ) * L := by positivity
    nlinarith
  · have : ((g1 : ℝ) * g2) = ((g1 * g2 : ℕ) : ℝ) := by push_cast; ring
    rw [this]; exact Real.log_natCast_nonneg _
  · by_cases h1 : (g1 : ℝ) = 0
    · rw [h1, zero_mul, Real.log_zero]; positivity
    by_cases h2 : (g2 : ℝ) = 0
    · rw [h2, mul_zero, Real.log_zero]; positivity
    rw [Real.log_mul h1 h2]
    nlinarith
  · have := D.R.m_add_three_le_k; omega
  · have := D.R.two_le_m; omega
  · have h1 : x * (Sc + eta + (D.R.m : ℝ) * D.R.t) ≤ b' := by
      rw [le_div_iff₀ hx0] at hsm; linarith
    have h2 : K * (Sc + eta + (D.R.m : ℝ) * D.R.t) ≤ x * (Sc + eta + (D.R.m : ℝ) * D.R.t) :=
      mul_le_mul_of_nonneg_right hKx (by linarith)
    nlinarith

theorem lamCol_stepB (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (h : i + 1 < D.R.k) :
    lamCol D u τ (i + 1) < lamCol D u τ i + 1 := by
  unfold lamCol
  rw [dite_eq_left h, dite_eq_left (show i < D.R.k by omega)]
  simp only [hcToWeightQ, rhoVec]
  have h1 := (D.hcW u τ).u_gt_v ⟨i, by omega⟩
  have h2 := (D.hcW u τ).v_gt_u ⟨i, by omega⟩
  push_cast
  linarith

theorem mem_tops (D : D7) (τ : D.what₂.Tau) : τ ∈ tops D ↔ IsTop D τ := by
  exact b_mem_tops D τ

theorem tops_card (D : D7) : (tops D).card = D.host.TT.card := by
  exact b_card_tops D

theorem col_setup (D : D7) (u : D.what₂.Word) (Cn x b L b' Sc eta K : ℝ) (hK1 : 1 ≤ K) (hKC : Cn ≤ K)
    (hN : Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta) (hW : Wts D u Cn x b b' Sc eta) :
    ∃ (κ : ℕ) (lam : D.what₂.Tau → Fin (κ + 1 + 1) → ℤ),
      D.R.k = κ + 1 + 1 ∧ (∀ τ, Antitone (lam τ)) ∧
      (∀ τ, colAbs D u τ = (wt (lam τ) : ℝ)) ∧ (∀ τ, colAbsP D u τ = (wt (plus (lam τ)) : ℝ)) ∧
      (∀ τ, firstColumnSpread D u τ = (plus (lam τ) 0 : ℝ)) ∧
      (∀ τ, (lamCol D u τ (D.R.k - 1) : ℝ) = (lam τ (Fin.last (κ + 1)) : ℝ)) ∧
      (∀ τ ∈ tops D, x * b ≤ aT D u τ ∧ aT D u τ ≤ 2 * (x * b) ∧ b' ≤ bT D u τ ∧ bT D u τ ≤ 2 * b') ∧
      (∀ τ ∈ tops D, (wt (lam τ) : ℝ) ≤ aT D u τ + (((κ + 1 : ℕ) : ℝ) + 1) * (K * Sc)) ∧
      (∀ τ ∈ tops D, (wt (plus (lam τ)) : ℝ) ≤ aT D u τ + (((κ + 1 : ℕ) : ℝ) + 1) * (bT D u τ + K * Sc)) ∧
      (∀ τ, τ ∉ tops D → (wt (plus (lam τ)) : ℝ) ≤ (((κ + 1 : ℕ) : ℝ) + 1 + 3) * (K * Sc)) ∧
      (∀ τ, τ ∉ tops D → (wt (lam τ) : ℝ) ≤ (2 * Cn + 4) * (((κ + 1 : ℕ) : ℝ) + 1) * (K * Sc)) ∧
      (∀ τ, τ ∉ tops D → |(lam τ (Fin.last (κ + 1)) : ℝ)| ≤ (2 * Cn + 4) * (K * Sc)) := by
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  have hSc : 1 ≤ Sc := hN.2.2.2.2.2.2.1
  obtain ⟨κ, hκ⟩ : ∃ κ, D.R.k = κ + 1 + 1 := ⟨D.R.k - 2, by have := D.R.m_add_three_le_k; omega⟩
  have hint : ∀ τ (i : Fin (κ + 1 + 1)), ∃ z : ℤ, lamCol D u τ i = z :=
    fun τ i => (hW τ).1 i (by have := i.2; omega)
  choose lam hlam using hint
  have hl : ∀ τ (i : Fin (κ + 1 + 1)), (lamCol D u τ i : ℝ) = (lam τ i : ℝ) := fun τ i => by
    rw [hlam τ i]; norm_cast
  have hk1 : D.R.k - 1 = κ + 1 := by omega
  have hlk : ∀ τ, (lamCol D u τ (D.R.k - 1) : ℝ) = (lam τ (Fin.last (κ + 1)) : ℝ) := fun τ => by
    rw [← hl τ (Fin.last (κ + 1)), hk1, Fin.val_last]
  have hl0 : ∀ τ, (lamCol D u τ 0 : ℝ) = (lam τ 0 : ℝ) := fun τ => by
    rw [← hl τ 0]; rfl
  have hanti : ∀ τ, Antitone (lam τ) := fun τ => by
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have h1 := lamCol_stepB D u τ i (by have := i.2; omega)
    have h2 := hlam τ i.succ
    have h3 := hlam τ i.castSucc
    rw [Fin.val_succ] at h2
    rw [Fin.val_castSucc] at h3
    rw [h2, h3] at h1
    have h4 : lam τ i.succ < lam τ i.castSucc + 1 := by exact_mod_cast h1
    omega
  have hKSc : Sc ≤ K * Sc := by nlinarith
  have hwt : ∀ τ, colAbs D u τ = (wt (lam τ) : ℝ) := fun τ => by
    unfold colAbs wt
    rw [hκ, Finset.sum_range]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hl τ i
  have hwtp : ∀ τ, colAbsP D u τ = (wt (plus (lam τ)) : ℝ) := fun τ => by
    unfold colAbsP wt plus
    rw [hlk τ, hκ, Finset.sum_range]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [hl τ i]
  have hp1 : ∀ τ, firstColumnSpread D u τ = (plus (lam τ) 0 : ℝ) := fun τ => by
    unfold firstColumnSpread plus
    rw [hlk τ, hl0 τ]; push_cast; ring
  have htop : ∀ τ ∈ tops D, ((wt (lam τ) : ℝ) ≤ aT D u τ + (((κ + 1 : ℕ) : ℝ) + 1) * (K * Sc)) ∧
      ((wt (plus (lam τ)) : ℝ) ≤ aT D u τ + (((κ + 1 : ℕ) : ℝ) + 1) * (bT D u τ + K * Sc)) := by
    intro τ hτ
    obtain ⟨-, -, hb1, -, hmid⟩ := (hW τ).2.1 ((mem_tops D τ).1 hτ)
    rw [hlk τ] at hb1
    have hbt : (0 : ℤ) ≤ -lam τ (Fin.last (κ + 1)) := by
      have : (0 : ℝ) ≤ ((-lam τ (Fin.last (κ + 1)) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hS0 : (0 : ℤ) ≤ ⌊K * Sc⌋ := Int.floor_nonneg.2 (by positivity)
    obtain ⟨c1, c2⟩ := Formalism.HermitianLattices.TraceIntegrality.column_top_entry κ (lam τ) (lam τ 0) (-lam τ (Fin.last (κ + 1))) ⌊K * Sc⌋
      hbt hS0 rfl (by ring) (fun i hi0 hil => by
        have hi1 : 0 < (i : ℕ) := Nat.pos_of_ne_zero fun h => hi0 (Fin.ext h)
        have hi2 : (i : ℕ) < D.R.k - 1 := by
          rw [hk1]
          have h5 : (i : ℕ) ≠ κ + 1 := fun h => hil (Fin.ext (by rw [h, Fin.val_last]))
          have := i.2
          omega
        obtain ⟨m1, m2⟩ := hmid i hi1 hi2
        rw [hl τ i] at m1 m2
        refine ⟨by exact_mod_cast m1, Int.le_floor.2 (by linarith)⟩)
    have hfl : (⌊K * Sc⌋ : ℝ) ≤ K * Sc := Int.floor_le _
    have c1' : (wt (lam τ) : ℝ) ≤ (lam τ 0 : ℝ) + ((κ : ℝ) + 2) * (⌊K * Sc⌋ : ℝ) := by exact_mod_cast c1
    have c2' : (wt (plus (lam τ)) : ℝ) ≤
        (lam τ 0 : ℝ) + ((κ : ℝ) + 2) * (-(lam τ (Fin.last (κ + 1)) : ℝ) + (⌊K * Sc⌋ : ℝ)) := by
      exact_mod_cast c2
    have hκ0 : (0 : ℝ) ≤ (κ : ℝ) + 2 := by positivity
    unfold aT bT
    rw [hl0 τ, hlk τ]
    push_cast
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hfl hκ0]
    · nlinarith [mul_le_mul_of_nonneg_left hfl hκ0]
  have hnt : ∀ τ, τ ∉ tops D → ∀ i : Fin (κ + 1 + 1), 0 ≤ (lam τ i : ℝ) ∧ (lam τ i : ℝ) ≤ Cn * Sc := by
    intro τ hτ i
    have := (hW τ).2.2.1 (fun h => hτ ((mem_tops D τ).2 h)) i (by have := i.2; omega)
    rwa [hl τ i] at this
  have hCS : Cn * Sc ≤ K * Sc := mul_le_mul_of_nonneg_right hKC (by linarith)
  have hKS0 : 0 ≤ K * Sc := by positivity
  refine ⟨κ, lam, hκ, hanti, hwt, hwtp, hp1, hlk, ?_, fun τ hτ => (htop τ hτ).1, fun τ hτ => (htop τ hτ).2,
    ?_, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨t1, t2, t3, t4, -⟩ := (hW τ).2.1 ((mem_tops D τ).1 hτ)
    exact ⟨t1, t2, t3, t4.le⟩
  · intro τ hτ
    have h1 : (wt (plus (lam τ)) : ℝ) ≤ ∑ _i : Fin (κ + 1 + 1), K * Sc := by
      unfold wt plus
      push_cast
      refine Finset.sum_le_sum fun i _ => ?_
      have := hnt τ hτ i
      have := hnt τ hτ (Fin.last (κ + 1))
      linarith
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    push_cast at h1 ⊢
    nlinarith
  · intro τ hτ
    have h1 : (wt (lam τ) : ℝ) ≤ ∑ _i : Fin (κ + 1 + 1), K * Sc := by
      unfold wt
      push_cast
      refine Finset.sum_le_sum fun i _ => ?_
      have := hnt τ hτ i
      linarith
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    push_cast at h1 ⊢
    have hκ0 : (0 : ℝ) ≤ ((κ : ℝ) + 1 + 1) * (K * Sc) := by positivity
    nlinarith
  · intro τ hτ
    have := hnt τ hτ (Fin.last (κ + 1))
    rw [abs_of_nonneg this.1]
    nlinarith

end Z56a

section Z56
open Formalism.BasicNotions NumberField
open Formalism.HermitianLattices.TraceIntegrality (Numbers wt plus MeanSquareWeightBound)

def SlopeLow (D : D7) (u : D.what₂.Word) : Prop :=
  -(∑ τ, colAbs D u τ / D.R.k * Real.log (Tu D u)) -
      ∑ τ, (colAbsP D u τ * Real.log D.R.k + (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k)) ≤
    ((D.fm u).lat 0).mu

def SlopeMax (D : D7) (u : D.what₂.Word) (C5 : ℝ) : Prop :=
  ((D.fm u).lat 0).muMax ≤
    ∑ τ, (colAbsP D u τ * (C5 * Real.log (D.R.k * D.host.v)) +
      (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k) +
      |(lamCol D u τ (D.R.k - 1) : ℝ)| * Real.log (Tu D u))

def SlopeLowerOpenPart (D : D7) : Prop := ∀ u, ColVal D u → SlopeLow D u

def SlopeMaxOpenPart (D : D7) (C5 : ℝ) : Prop := ∀ u, ColVal D u → SlopeMax D u C5

private theorem mulmax_lemma (C K P X Y : ℝ) (hP : 0 ≤ P) (hX : 0 ≤ X) (hXY : X ≤ K * Y) :
    C * (P * X) ≤ max C 0 * K * (P * Y) := by
  have h0 : 0 ≤ max C 0 := le_max_right _ _
  calc C * (P * X) ≤ max C 0 * (P * X) := mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hP hX)
    _ ≤ max C 0 * (P * (K * Y)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXY hP) h0
    _ = max C 0 * K * (P * Y) := by ring

theorem arith5 (C K n a lk f k b' Sc lT L : ℝ) (hK1 : 1 ≤ K) (hn : 0 ≤ n) (ha : 0 ≤ a) (hlk : 0 ≤ lk)
    (hf : 0 ≤ f) (hk : 0 ≤ k) (hb : 0 ≤ b') (hS : 0 ≤ Sc) (hT : 0 ≤ lT) (hL : 0 ≤ L) :
    C * n * a * lk ≤ max C 0 * K * n * a * lk ∧
    C * f * k * (b' + K * Sc) * lk ≤ max C 0 * K * f * k * (b' + Sc) * lk ∧
    C * f * (K * Sc) * lT ≤ max C 0 * K * f * Sc * lT ∧
    C * f * k ^ 2 * L ≤ max C 0 * K * f * k ^ 2 * L := by
  have hK0 : 0 ≤ K := by linarith
  have hX2 : b' + K * Sc ≤ K * (b' + Sc) := by nlinarith [mul_nonneg (sub_nonneg.2 hK1) hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc C * n * a * lk = C * ((n * a * lk) * 1) := by ring
      _ ≤ max C 0 * K * ((n * a * lk) * 1) :=
        mulmax_lemma C K _ 1 1 (mul_nonneg (mul_nonneg hn ha) hlk) zero_le_one (by linarith)
      _ = max C 0 * K * n * a * lk := by ring
  · calc C * f * k * (b' + K * Sc) * lk = C * ((f * k * lk) * (b' + K * Sc)) := by ring
      _ ≤ max C 0 * K * ((f * k * lk) * (b' + Sc)) :=
        mulmax_lemma C K _ _ _ (mul_nonneg (mul_nonneg hf hk) hlk) (add_nonneg hb (mul_nonneg hK0 hS)) hX2
      _ = max C 0 * K * f * k * (b' + Sc) * lk := by ring
  · calc C * f * (K * Sc) * lT = C * ((f * lT) * (K * Sc)) := by ring
      _ ≤ max C 0 * K * ((f * lT) * Sc) :=
        mulmax_lemma C K _ _ _ (mul_nonneg hf hT) (mul_nonneg hK0 hS) le_rfl
      _ = max C 0 * K * f * Sc * lT := by ring
  · calc C * f * k ^ 2 * L = C * ((f * k ^ 2 * L) * 1) := by ring
      _ ≤ max C 0 * K * ((f * k ^ 2 * L) * 1) :=
        mulmax_lemma C K _ 1 1 (mul_nonneg (mul_nonneg hf (sq_nonneg k)) hL) zero_le_one (by linarith)
      _ = max C 0 * K * f * k ^ 2 * L := by ring

theorem ramifiedLattice_of_chain_estimates (Cn : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x : ℝ), max Cn 1 ≤ x → SlopeLowerOpenPart D → Conclusion5 D Cn C x := by
  classical
  obtain ⟨C, hC⟩ := Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_second (2 * max Cn 0 + 4) (by positivity)
  refine ⟨max C 0 * max Cn 1, fun D x hx hZ u b L b' Sc eta hN hW Y => ?_⟩
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  rw [max_eq_left hCn] at hC
  set K := max Cn 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hSc : 1 ≤ Sc := hN.2.2.2.2.2.2.1
  have hb0 : 0 < b := hN.1
  have hx2 : 2 ≤ x := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨κ, lam, hκ, hanti, hwt, hwtp, hp1, hlk, ht0, ht1, ht2, hn1, hn2, hn3⟩ :=
    col_setup D u Cn x b L b' Sc eta K hK1 (le_max_left _ _) hN hW
  have hNum := numbers_of_nums K hK1 hx hN
  rw [hκ] at hNum
  have hkR : (D.R.k : ℝ) = ((κ + 1 : ℕ) : ℝ) + 1 := by rw [hκ]; push_cast; ring
  have hf : (Fintype.card D.what₂.Tau : ℝ) = D.R.f := by rw [D.what₂.card_Tau]
  have hf0 : (0 : ℝ) < (Fintype.card D.what₂.Tau : ℝ) := by
    have hfpos : 0 < Fintype.card D.what₂.Tau := by
      rw [D.what₂.card_Tau]
      have := D.R.two_le_m
      have := D.R.m_le_f
      unfold Ranks.f Ranks.n at *
      omega
    exact_mod_cast hfpos
  have hlow := hZ u Y
  unfold SlopeLow at hlow
  set mu := ((D.fm u).lat 0).mu with hmu
  set lT := Real.log (Tu D u) with hlT
  have hZ4 : ∀ τ, colAbsP D u τ * Real.log D.R.k + (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k) =
      MeanSquareWeightBound (lam τ) := fun τ => by
    unfold MeanSquareWeightBound
    have e : ((plus (lam τ) 0 : ℤ) : ℝ) + (((κ + 1 : ℕ) : ℝ) + 1) =
        ((plus (lam τ) 0 : ℤ) : ℝ) + ((κ + 1 : ℕ) : ℝ) + 1 := by ring
    rw [hwtp τ, hp1 τ, hkR, e]
  simp only [hZ4, hwt] at hlow
  set δ := mu + (∑ τ, (wt (lam τ) : ℝ) / D.R.k * lT) + ∑ τ, MeanSquareWeightBound (lam τ) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have key := hC D.what₂.Tau Unit (tops D) (κ + 1) D.R.m D.R.t (D.R.N D.R.m) lam (aT D u) (bT D u)
    (x * b) b' L D.host.v lT (Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) eta (K * Sc) mu (fun _ => mu)
    (fun τ => -MeanSquareWeightBound (lam τ) + δ / (Fintype.card D.what₂.Tau : ℝ))
    (fun τ => MeanSquareWeightBound (lam τ) - δ / (Fintype.card D.what₂.Tau : ℝ))
    (fun τ => MeanSquareWeightBound (lam τ) - δ / (Fintype.card D.what₂.Tau : ℝ))
    hNum hanti ht0 ht1 ht2 hn1 hn2 (by simp [Formalism.HermitianLattices.TraceIntegrality.mean])
    (fun _ => by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_div_cancel₀ _ hf0.ne', Finset.sum_neg_distrib, hδ, ← hkR]
      ring)
    (fun τ => by ring) (fun τ => le_rfl)
    (fun τ => by have : 0 ≤ δ / (Fintype.card D.what₂.Tau : ℝ) := by positivity
                 linarith)
  rw [← hkR, hf, tops_card] at key
  refine le_trans ?_ key
  have hlk0 : 0 ≤ Real.log (D.R.k : ℝ) := Real.log_natCast_nonneg _
  have hlT0 : 0 ≤ lT := Real.log_natCast_nonneg _
  obtain ⟨e1, e2, e3, e4⟩ := arith5 C K (D.host.TT.card : ℝ) (x * b) (Real.log D.R.k) D.R.f D.R.k b' Sc lT L hK1
    (by positivity) (by positivity) hlk0 (by positivity) (by positivity) (by linarith) (by linarith) hlT0 (by linarith)
  linarith

theorem arith6 (C K n a l f k b' Sc lT L : ℝ) (hK1 : 1 ≤ K) (hn : 0 ≤ n) (ha : 0 ≤ a) (hl : 0 ≤ l)
    (hf : 0 ≤ f) (hk : 0 ≤ k) (hb : 0 ≤ b') (hS : 0 ≤ Sc) (hT : 0 ≤ lT) (hL : 0 ≤ L) :
    C * n * a * l + C * f * (b' + K * Sc) * (k * l + lT) + C * f * k ^ 2 * L ≤
      max C 0 * K * n * a * l + max C 0 * K * f * (b' + Sc) * (k * l + lT) + max C 0 * K * f * k ^ 2 * L := by
  have hK0 : 0 ≤ K := by linarith
  have hX2 : b' + K * Sc ≤ K * (b' + Sc) := by nlinarith [mul_nonneg (sub_nonneg.2 hK1) hb]
  have h1 : C * n * a * l ≤ max C 0 * K * n * a * l := by
    calc C * n * a * l = C * ((n * a * l) * 1) := by ring
      _ ≤ max C 0 * K * ((n * a * l) * 1) :=
        mulmax_lemma C K _ 1 1 (mul_nonneg (mul_nonneg hn ha) hl) zero_le_one (by linarith)
      _ = max C 0 * K * n * a * l := by ring
  have h2 : C * f * (b' + K * Sc) * (k * l + lT) ≤ max C 0 * K * f * (b' + Sc) * (k * l + lT) := by
    calc C * f * (b' + K * Sc) * (k * l + lT) = C * ((f * (k * l + lT)) * (b' + K * Sc)) := by ring
      _ ≤ max C 0 * K * ((f * (k * l + lT)) * (b' + Sc)) :=
        mulmax_lemma C K _ _ _ (mul_nonneg hf (add_nonneg (mul_nonneg hk hl) hT)) (add_nonneg hb (mul_nonneg hK0 hS)) hX2
      _ = max C 0 * K * f * (b' + Sc) * (k * l + lT) := by ring
  have h3 : C * f * k ^ 2 * L ≤ max C 0 * K * f * k ^ 2 * L := by
    calc C * f * k ^ 2 * L = C * ((f * k ^ 2 * L) * 1) := by ring
      _ ≤ max C 0 * K * ((f * k ^ 2 * L) * 1) :=
        mulmax_lemma C K _ 1 1 (mul_nonneg (mul_nonneg hf (sq_nonneg k)) hL) zero_le_one (by linarith)
      _ = max C 0 * K * f * k ^ 2 * L := by ring
  linarith

theorem classMap_estimate_of_partial (Cn C5 : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x : ℝ), max Cn 1 ≤ x → SlopeMaxOpenPart D C5 → Conclusion6 D Cn C x := by
  classical
  obtain ⟨C, hC⟩ := Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_third (2 * max Cn 0 + 4) (by positivity)
  refine ⟨max C 0 * max Cn 1 * max 1 (C5 / (2 * max Cn 0 + 4)), fun D x hx hZ u b L b' Sc eta hN hW Y => ?_⟩
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  rw [max_eq_left hCn] at hC ⊢
  set K := max Cn 1 with hK
  set K' := max 1 (C5 / (2 * Cn + 4)) with hK'
  have hC0 : 0 < 2 * Cn + 4 := by linarith
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK'1 : 1 ≤ K' := le_max_left _ _
  have hK'0 : 0 < K' := by linarith
  have hC5 : C5 ≤ K' * (2 * Cn + 4) := by
    have : C5 / (2 * Cn + 4) ≤ K' := le_max_right _ _
    rwa [div_le_iff₀ hC0] at this
  have hSc : 1 ≤ Sc := hN.2.2.2.2.2.2.1
  have hb0 : 0 < b := hN.1
  have hx2 : 2 ≤ x := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv1 : 1 ≤ D.host.v := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨κ, lam, hκ, hanti, hwt, hwtp, hp1, hlk, ht0, ht1, ht2, hn1, hn2, hn3⟩ :=
    col_setup D u Cn x b L b' Sc eta K hK1 (le_max_left _ _) hN hW
  have hNum := numbers_of_nums K hK1 hx hN
  rw [hκ] at hNum
  have hkR : (D.R.k : ℝ) = ((κ + 1 : ℕ) : ℝ) + 1 := by rw [hκ]; push_cast; ring
  have hf : (Fintype.card D.what₂.Tau : ℝ) = D.R.f := by rw [D.what₂.card_Tau]
  have hmax := hZ u Y
  unfold SlopeMax at hmax
  set mM := ((D.fm u).lat 0).muMax with hmM
  set lT := Real.log (Tu D u) with hlT
  have hlT0 : 0 ≤ lT := Real.log_natCast_nonneg _
  have hk1 : (1 : ℝ) ≤ (D.R.k : ℝ) := by rw [hkR]; have : (0 : ℝ) ≤ ((κ + 1 : ℕ) : ℝ) := by positivity
                                         linarith
  have hlkv : 0 ≤ Real.log ((D.R.k : ℝ) * D.host.v) := Real.log_nonneg (by nlinarith)
  have hplus0 : ∀ τ i, 0 ≤ plus (lam τ) i := fun τ i => by
    unfold plus
    have := hanti τ (Fin.le_last i)
    omega
  have hwp0 : ∀ τ, (0 : ℝ) ≤ (wt (plus (lam τ)) : ℝ) := fun τ => by
    have : 0 ≤ wt (plus (lam τ)) := Finset.sum_nonneg fun i _ => hplus0 τ i
    exact_mod_cast this
  have hterm : ∀ τ, colAbsP D u τ * (C5 * Real.log (D.R.k * D.host.v)) +
      (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k) + |(lamCol D u τ (D.R.k - 1) : ℝ)| * lT ≤
      K' * ((wt (plus (lam τ)) : ℝ) * ((2 * Cn + 4) * Real.log ((((κ + 1 : ℕ) : ℝ) + 1) * D.host.v))
        + (((κ + 1 : ℕ) : ℝ) + 1) ^ 2 * Real.log ((plus (lam τ) 0 : ℝ) + ((κ + 1 : ℕ) : ℝ) + 1)
        + |(lam τ (Fin.last (κ + 1)) : ℝ)| * lT) := fun τ => by
    have e : ((plus (lam τ) 0 : ℤ) : ℝ) + ((κ + 1 : ℕ) : ℝ) + 1 =
        ((plus (lam τ) 0 : ℤ) : ℝ) + (((κ + 1 : ℕ) : ℝ) + 1) := by ring
    rw [e, ← hkR, hwtp τ, hp1 τ, hlk τ]
    have hp0 : (0 : ℝ) ≤ ((plus (lam τ) 0 : ℤ) : ℝ) := by exact_mod_cast hplus0 τ 0
    have hlog : 0 ≤ Real.log (((plus (lam τ) 0 : ℤ) : ℝ) + D.R.k) := Real.log_nonneg (by linarith)
    have t1 : (wt (plus (lam τ)) : ℝ) * (C5 * Real.log (D.R.k * D.host.v)) ≤
        K' * ((wt (plus (lam τ)) : ℝ) * ((2 * Cn + 4) * Real.log (D.R.k * D.host.v))) := by
      calc (wt (plus (lam τ)) : ℝ) * (C5 * Real.log (D.R.k * D.host.v))
          = C5 * ((wt (plus (lam τ)) : ℝ) * Real.log (D.R.k * D.host.v)) := by ring
        _ ≤ K' * (2 * Cn + 4) * ((wt (plus (lam τ)) : ℝ) * Real.log (D.R.k * D.host.v)) :=
            mul_le_mul_of_nonneg_right hC5 (mul_nonneg (hwp0 τ) hlkv)
        _ = _ := by ring
    have t2 : (D.R.k : ℝ) ^ 2 * Real.log (((plus (lam τ) 0 : ℤ) : ℝ) + D.R.k) ≤
        K' * ((D.R.k : ℝ) ^ 2 * Real.log (((plus (lam τ) 0 : ℤ) : ℝ) + D.R.k)) :=
      le_mul_of_one_le_left (by positivity) hK'1
    have t3 : |(lam τ (Fin.last (κ + 1)) : ℝ)| * lT ≤ K' * (|(lam τ (Fin.last (κ + 1)) : ℝ)| * lT) :=
      le_mul_of_one_le_left (by positivity) hK'1
    linarith
  have hmax2 := le_trans hmax (Finset.sum_le_sum fun τ _ => hterm τ)
  rw [← Finset.mul_sum] at hmax2
  have key := hC D.what₂.Tau Unit (tops D) (κ + 1) D.R.m D.R.t (D.R.N D.R.m) lam (aT D u) (bT D u)
    (x * b) b' L D.host.v lT (Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) eta (K * Sc) (mM / K')
    (fun _ => ∑ τ, ((wt (plus (lam τ)) : ℝ) * ((2 * Cn + 4) * Real.log ((((κ + 1 : ℕ) : ℝ) + 1) * D.host.v))
        + (((κ + 1 : ℕ) : ℝ) + 1) ^ 2 * Real.log ((plus (lam τ) 0 : ℝ) + ((κ + 1 : ℕ) : ℝ) + 1)
        + |(lam τ (Fin.last (κ + 1)) : ℝ)| * lT))
    hNum hanti ht0 ht2
    (fun τ hτ => by
      have h1 := (ht0 τ hτ).2.2.1
      unfold bT at h1 ⊢
      rw [hlk τ] at h1 ⊢
      rw [abs_of_nonpos (by linarith)])
    hn1 hn3 ⟨(), by rw [div_le_iff₀ hK'0]; linarith⟩ (fun _ => le_rfl)
  rw [← hkR, hf, tops_card, div_le_iff₀ hK'0] at key
  have ar := arith6 C K (D.host.TT.card : ℝ) (x * b) (Real.log ((D.R.k : ℝ) * D.host.v)) D.R.f D.R.k b' Sc lT L hK1
    (by positivity) (by positivity) hlkv (by positivity) (by positivity) (by linarith) (by linarith) hlT0 (by linarith)
  have := le_trans key (mul_le_mul_of_nonneg_right ar hK'0.le)
  refine le_trans this (le_of_eq ?_)
  ring

def FamilySlopeLowerOpenPart {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := fam0 Fm SlopeLowerOpenPart

def FamilySlopeMaxOpenPart {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C5 : ℝ) : Prop := fam0 Fm fun D => SlopeMaxOpenPart D C5

theorem familySlopeLower_of_open {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : FamilySlopeLowerOpenPart Fm) : ConclusionF5 Fm := by
  intro Cn
  obtain ⟨C, hC⟩ := ramifiedLattice_of_chain_estimates Cn
  obtain ⟨x0, h0⟩ := h
  exact ⟨C, max x0 (max Cn 1), fun x hx hx1 i =>
    hC _ x (le_trans (le_max_right _ _) hx) (h0 x (le_trans (le_max_left _ _) hx) hx1 i)⟩

theorem familySlopeMax_of_open {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C5 : ℝ) (h : FamilySlopeMaxOpenPart Fm C5) : ConclusionF6 Fm := by
  intro Cn
  obtain ⟨C, hC⟩ := classMap_estimate_of_partial Cn C5
  obtain ⟨x0, h0⟩ := h
  exact ⟨C, max x0 (max Cn 1), fun x hx hx1 i =>
    hC _ x (le_trans (le_max_right _ _) hx) (h0 x (le_trans (le_max_left _ _) hx) hx1 i)⟩

end Z56

section Ms
open Formalism.BasicNotions NumberField

end Ms

section Z1a
open Formalism.BasicNotions NumberField

end Z1a

section Z1b
open Formalism.BasicNotions NumberField

end Z1b

section continuousCocycles
open Formalism.BasicNotions NumberField

end continuousCocycles

section JI
open Formalism.BasicNotions NumberField

end JI

section JG
open MeasureTheory

end JG

section GrowthPolynomialOperator
open MeasureTheory Complex

end GrowthPolynomialOperator

section HilbertSchmidtNorm
open MeasureTheory Complex

variable {ι : Type} [Fintype ι]

end HilbertSchmidtNorm

section PB3
open MeasureTheory Complex

end PB3

section Z1d
open Formalism.BasicNotions

end Z1d

section UF
open Formalism.BasicNotions NumberField MeasureTheory

end UF

section MV1
open Formalism.BasicNotions NumberField MeasureTheory Complex

end MV1

section MV2
open Formalism.BasicNotions NumberField MeasureTheory Complex

def rho (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (w : Gx D i → ℂ) : ℝ :=
  2 ^ Fintype.card (Gx D i) * Real.exp (-(2 * Real.pi) * Hq D i s w)

end MV2

section crystallineCocycles
open Formalism.BasicNotions

end crystallineCocycles

section PJ
open Formalism.BasicNotions NumberField

end PJ

end Formalism.MainNotions.flipTwoThree
