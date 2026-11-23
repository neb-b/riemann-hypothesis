module

public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0004
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.AlcoveOf
section
noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.Alc

open Formalism.BasicNotions Formalism.MainNotions

theorem entryR (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N i)) :
    ((((D.fm u).lam i τ).w a : ℤ) : ℝ) = ((flipTwoThree.lamLiftN D u τ a.1 : ℚ) : ℝ) := by
  have h : ((((D.fm u).lam i τ).w a : ℤ) : ℚ) = flipTwoThree.lamLiftN D u τ a.1 := by
    rw [(D.fm u).lam_eq i hi τ a]
    unfold flipTwoThree.lamLiftN flipTwoThree.lamCol flipTwoThree.wJ
    by_cases h : a.1 < D.R.k
    · rw [dite_eq_left h, if_pos h, dite_eq_left h]
    · rw [dite_eq_right h, if_neg h, dite_eq_left (D.R.blk_lt hi a h)]
  rw [← h]
  simp

theorem wJ_mono {D : D7} {u : D.what₂.Word} {τ : D.what₂.Tau}
    (h : ∀ j, j + 1 < D.R.m → flipTwoThree.wJ D u τ j ≤ flipTwoThree.wJ D u τ (j + 1)) (c : ℕ) (hc : c < D.R.m) :
    flipTwoThree.wJ D u τ 0 ≤ flipTwoThree.wJ D u τ c := by
  induction c with
  | zero => exact le_rfl
  | succ n ih => exact le_trans (ih (by omega)) (h n hc)

theorem nums {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (u : D.what₂.Word) (hN : J.NumsL D L Cn cL) :
    24 * L.sc.x ≤ L.sc.b' ∧ L.sc.b' ≤ L.sc.b ∧ (D.R.N D.R.m : ℝ) ≤ L.sc.b' ∧ 2 * L.Sc ≤ L.sc.b' ∧ 2 * L.etaSz ≤ L.sc.b' ∧
      1 ≤ L.Sc ∧ 32 * Cn ≤ L.sc.b' := by
  obtain ⟨n1, _, _, _, _, n6, n7, n8, n9, _, n11, _, _, n14, _, n16⟩ := hN u
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hNn : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (11 : ℝ) ≤ D.R.t := by
    have h1 := D.R.rank_add_five_le
    have h2 := D.R.m_add_three_le_k
    have h3 := D.R.two_le_m
    have : 11 ≤ D.R.t := by omega
    exact_mod_cast this
  have hmt : (22 : ℝ) ≤ D.R.m * D.R.t := by nlinarith
  have hq : 24 ≤ L.sc.b' / L.sc.x := by linarith
  have hb24 : 24 * L.sc.x ≤ L.sc.b' := by rwa [le_div_iff₀ hx0] at hq
  have hb0 : 0 < L.sc.b' := by nlinarith
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb0.le (by norm_num) n14
  have hbb : L.sc.b' ≤ L.sc.b := by
    rwa [mul_div_assoc, mul_comm, div_mul_cancel₀ _ hx0.ne'] at n6
  have hNb : (D.R.N D.R.m : ℝ) ≤ L.sc.b' := by
    have h1 : (D.R.N D.R.m : ℝ) * 1 ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hNn
    linarith
  have hN1 : (1 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast D.R.N_pos D.R.m
  have hm3 : (8 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by nlinarith [mul_self_nonneg ((D.R.m : ℝ) - 2)]
  have hmN : (8 : ℝ) ≤ (D.R.m : ℝ) ^ 3 * D.R.N D.R.m := by nlinarith
  refine ⟨hb24, hbb, hNb, by linarith, by linarith, n7, ?_⟩
  by_cases hC : Cn ≤ 0
  · linarith
  · have hC' : 0 < Cn := not_le.1 hC
    have h2 : (1 + 2 * (2 * Cn + 4)) * 8 ≤ (1 + 2 * (2 * Cn + 4)) * ((D.R.m : ℝ) ^ 3 * D.R.N D.R.m) :=
      mul_le_mul_of_nonneg_left hmN (by linarith)
    nlinarith

theorem entry_bd {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : J.NumsL D L Cn cL) (hW : J.WtsL D L Cn)
    (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (hi : i ≤ D.R.m) (a : Fin (D.R.N i)) :
    -(2 * L.sc.b + L.sc.b') ≤ ((((D.fm u).lam i τ).w a : ℤ) : ℝ) ∧
      ((((D.fm u).lam i τ).w a : ℤ) : ℝ) ≤ 2 * (L.sc.x * L.sc.b) + L.sc.b' * L.sc.b' / 64 := by
  classical
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := nums hcL u hN
  have hx1 := L.sc.one_lt_alt
  have hb0 : 0 < L.sc.b' := by linarith
  have hxb : 0 ≤ L.sc.x * L.sc.b := mul_nonneg (by linarith) (by linarith)
  have hsq : 0 ≤ L.sc.b' * L.sc.b' / 64 := by positivity
  have hxb1 : L.sc.b ≤ L.sc.x * L.sc.b := le_mul_of_one_le_left (by linarith) hx1.le

  have hCS : Cn * L.Sc ≤ L.sc.b' * L.sc.b' / 64 := by
    by_cases hC : Cn ≤ 0
    · have : Cn * L.Sc ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (by linarith)
      linarith
    · have hC' : 0 < Cn := not_le.1 hC
      have : (32 * Cn) * (2 * L.Sc) ≤ L.sc.b' * L.sc.b' := mul_le_mul s7 s4 (by linarith) hb0.le
      linarith
  obtain ⟨_, w2, w3, w4, w5, w6, w7, _⟩ := hW u τ
  have hk := D.R.m_add_three_le_k
  have w7' : -((flipTwoThree.lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) ≤ ((flipTwoThree.wJ D u τ 0 : ℚ) : ℝ) := by exact_mod_cast w7

  have hlast : ((flipTwoThree.lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) ≤ L.sc.b' * L.sc.b' / 64 := by
    by_cases hT : flipTwoThree.IsTop D τ
    · have := (w2 hT).2.2.1
      linarith
    · have := (w3 hT (D.R.k - 1) (by omega)).2
      linarith
  rw [entryR D u i hi τ a]
  unfold flipTwoThree.lamLiftN
  by_cases hak : a.1 < D.R.k
  · rw [if_pos hak]
    by_cases hT : flipTwoThree.IsTop D τ
    · obtain ⟨t1, t2, t3, t4, t5⟩ := w2 hT
      by_cases h0 : a.1 = 0
      · rw [h0]; constructor <;> linarith
      · by_cases hl : a.1 < D.R.k - 1
        · obtain ⟨e1, e2⟩ := t5 a.1 (Nat.pos_of_ne_zero h0) hl
          constructor <;> linarith
        · have : a.1 = D.R.k - 1 := by omega
          rw [this]
          constructor <;> linarith
    · obtain ⟨e1, e2⟩ := w3 hT a.1 hak
      constructor <;> linarith
  · rw [if_neg hak]
    have hb := D.R.blk_lt hi a hak
    have e2 : ((flipTwoThree.wJ D u τ 0 : ℚ) : ℝ) ≤ ((flipTwoThree.wJ D u τ ((a.1 - D.R.k) / (D.R.t + 1)) : ℚ) : ℝ) := by
      exact_mod_cast wJ_mono w4 _ hb
    have e1 : ((flipTwoThree.wJ D u τ ((a.1 - D.R.k) / (D.R.t + 1)) : ℚ) : ℝ) ≤ 2 * L.sc.b + L.sc.b' := by
      by_cases hK : flipTwoThree.IsThick D τ
      · have := (w6 hK _ hb).2
        linarith
      · have := w5 hK _ hb
        linarith
    push_cast
    constructor <;> linarith

theorem alcove_of {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : J.NumsL D L Cn cL) (hW : J.WtsL D L Cn)
    (hT : L.TuGe) (hm : 4 ≤ D.R.m) (u : D.what₂.Word) : product_first_zeroth_parts.Alcove D u := by
  intro j hj τ a b
  obtain ⟨s1, s2, s3, _, _, _, _⟩ := nums hcL u hN
  have hx1 := L.sc.one_lt_alt
  have hb24 : 24 ≤ L.sc.b := by linarith
  have hb1 : 1 ≤ L.sc.b := by linarith
  have hb'0 : 0 ≤ L.sc.b' := by linarith
  have hb2 : L.sc.b ^ 2 ≤ ((D.mem u).A.T : ℝ) := by
    refine le_trans ?_ (hT u)
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have : (4 : ℝ) ≤ D.R.m := by exact_mod_cast hm
    push_cast
    linarith
  have hbb : L.sc.b ^ 2 = L.sc.b * L.sc.b := sq _
  have h24 : 24 * L.sc.b ≤ L.sc.b * L.sc.b := mul_le_mul_of_nonneg_right hb24 (by linarith)
  have h8 : 24 * L.sc.x * L.sc.b ≤ L.sc.b * L.sc.b := mul_le_mul_of_nonneg_right (s1.trans s2) (by linarith)
  have hq : L.sc.b' * L.sc.b' ≤ L.sc.b * L.sc.b := mul_le_mul s2 s2 hb'0 (by linarith)
  have hNj : (D.R.N j : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.N j ≤ D.R.N D.R.m := by
      have := Nat.mul_le_mul_right (D.R.t + 1) hj
      unfold Ranks.N; omega
    exact_mod_cast this
  have ea := (entry_bd hcL hN hW u τ j hj a).2
  have eb := (entry_bd hcL hN hW u τ j hj b).1
  have : (2 * (((((D.fm u).lam j τ).w a : ℤ) : ℝ) - ((((D.fm u).lam j τ).w b : ℤ) : ℝ) + (D.R.N j : ℝ))) < ((D.mem u).A.T : ℝ) := by
    nlinarith
  exact_mod_cast this

end Formalism.MainNotions.GlobalTheoryTheory.Alc

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.WachTwistLocalTheory
section
noncomputable section

namespace Formalism.MainNotions.product_first_zeroth_parts

open Formalism.BasicNotions Classical NumberField

section Gen

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
  (M : MemberForms LL embLL Pl Tau hc C A P)

end Gen

section Fm

variable (D : D7) (u : D.what₂.Word)

end Fm

section Tw

variable (D : D7)

variable {D}

variable (D)

structure PendTw (u : D.what₂.Word) (μ : D.what₂.Tup) where

  clsLat : letI := D.host.cmStar; ∀ i, (D.chTw u μ).cls i → Submodule (𝓞 D.host.E) (D.sp.X i).V
  clsLat_lat : letI := D.host.cmStar; ∀ i c, Submodule.IsLattice D.host.E (clsLat i c)

  detCls : ∀ i, (D.chTw u μ).cls i → D.Dt

  xi : D.Dt →* ℂˣ
  xi_fin : ∃ n : ℕ, 0 < n ∧ ∀ x, xi x ^ n = 1
  trueColumnChoices_heckeChar_reference_eq_one : μ = D.what₂.mu0 → xi = 1

  rhoDet_eq_inv_muTilde_chiD_pow : ∀ i (c : (D.chTw u μ).cls i),
    (D.chTw u μ).rhoDet i c = (((D.muTil (i + 1) (detCls i c) * xi (detCls i c))⁻¹ *
      (D.chiD (detCls i c)) ^ (-(((D.R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
  rhoDetPrime_eq_muTilde_mul_chi_pow : ∀ i (c : (D.chTw u μ).cls (i + 1)),
    (D.chTw u μ).rhoDet' i c = ((D.muTil (i + 1) (detCls (i + 1) c) * xi (detCls (i + 1) c) *
      (D.chiD (detCls (i + 1) c)) ^ ((((D.R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)

  c0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0
  y0 : (D.mem u).C.Y 0 ≃ (D.chTw u μ).Y 0
  zero_class_lattice_eq : ∀ c, clsLat 0 (c0 c) = D.clsLat u 0 c
  zero_class_det_eq : ∀ c, detCls 0 (c0 c) = D.detCls u 0 c

  zero_identification_is_identity : ∀ φ c y, D.e0Tw u μ φ (c0 c) (y0 y) = φ c y

variable {D}

def colTw (u : D.what₂.Word) (μ : D.what₂.Tup) (x : Vl D u 0) : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ :=
  (D.chTw u μ).col (D.e0Tw u μ ((D.fm u).emb 0 x))

def TwistedT5ColumnBound (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (C : ℝ) : Prop :=
  ∀ w, OverT D u w →
    ∃ e : ℕ, (e : ℝ) ≤ D.R.m * (4 * ∑ τ, (Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m) +
        ∑ v ∈ VV D u w, ((D.R.t : ℝ) + 1 + 2 * Wt D u ((D.fm u).tauOf w v) + C * D.R.N D.R.m) *
          ((D.R.m : ℝ) * (D.R.m + 1) / 2) ∧
      ∀ x ∈ Nlam D u w, ∃ y ∈ (T.fm u μ).S D.R.m w, (T.fm u μ).emb D.R.m y = tpow D u e • colTw u μ x

def TupleChainSharpColumnValuation (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ μ, D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam D u w,
      Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w))

end Tw

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Fam

section Ref

open Formalism.BasicNotions.DV

variable {D : D7}

end Ref

end Formalism.MainNotions.product_first_zeroth_parts
end
end

