module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Development
public import Formalism.PeriodIntegrals.Bundle0023

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.FirstCoordinateLeThreeScale
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G
open scoped BigOperators

namespace PI.SzCt.UnitaryGroupMassFormula

theorem five_le_k (D : D7) : 5 ≤ D.R.k := by
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  omega

theorem cloudU_le (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (h : i < D.R.k)
    (h1 : 1 ≤ i) : (((D.hcW u τ).u ⟨i, h⟩ : ℚ) : ℝ) ≤ L.Sc := by
  by_cases hi : i + 1 < D.R.k
  · exact (L.cloud_u u τ ⟨i, h⟩ h1 hi).2
  · have hk := five_le_k D
    have hik : i = D.R.k - 1 := by omega
    have hgt := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
    have hv := (L.cloud_v τ ⟨D.R.k - 2, by omega⟩).2
    have hlast := D.hcW_last u τ (by omega)
    have e1 : (⟨i, h⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext hik
    have hgt' : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨D.R.k - 2, by omega⟩ := by
      have e2 : (⟨D.R.k - 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 2 + 1, by omega⟩ :=
        Fin.ext (show D.R.k - 1 = D.R.k - 2 + 1 by omega)
      rw [e2]
      exact hgt
    have hgtR : (((D.hc τ).u ⟨D.R.k - 1, by omega⟩ : ℚ) : ℝ) <
        (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hgt'
    rw [e1, hlast]
    linarith

private lemma wSz_eq_wj' (D : D7) (j : ℕ) (τ : D.what₂.Tau) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m) :
    DV.wSz D j τ = wj D j τ := by
  unfold DV.wSz wj
  rw [dite_eq_left ⟨hj1, hj2⟩, dite_eq_left (by omega : j - 1 < D.R.m)]

private lemma exists_wj_mem_Icc_add_etaSz (D : D7) (L : SizeData₂ D) (τ : D.what₂.Tau) :
    ∃ lo : ℝ, ∀ j, 1 ≤ j → j ≤ D.R.m → lo ≤ wj D j τ ∧ wj D j τ ≤ lo + L.etaSz + 1 := by
  have hPsi : (D.eTau τ : D.R.GG) ∈ D.R.Psi := (D.eTau τ).2
  by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · unfold Formalism.BasicNotions.Host.topPlaces at htop
    rw [Finset.mem_image] at htop
    obtain ⟨t, ht, hteq⟩ := htop
    refine ⟨(L.bT ⟨t, ht⟩ : ℝ) + L.sc.b' / L.sc.x, fun j hj1 hj2 => ?_⟩
    have hw := L.win_top j hj1 hj2 τ ⟨t, ht⟩ hteq.symm
    constructor <;> linarith [hw.1, hw.2]
  · by_cases hthick : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · refine ⟨L.sc.b, fun j hj1 hj2 => ?_⟩
      have hw := L.win_thick j hj1 hj2 τ hthick
      constructor <;> linarith [hw.1, hw.2]
    · have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := ⟨hPsi, htop, hthick⟩
      refine ⟨L.sc.w'' D.R.n, fun j hj1 hj2 => ?_⟩
      have hw := L.win_thin j hj1 hj2 τ hthin
      constructor <;> linarith [hw.1, hw.2]

private lemma hcW_e_cast_eq_wj_succ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (q : ℕ) (hq : q < D.R.m) :
    (((D.hcW u τ).e ⟨q, hq⟩ : ℚ) : ℝ) = wj D (q + 1) τ := by
  unfold wj
  rw [dite_eq_left (by omega : q + 1 - 1 < D.R.m), D.hcW_e u τ]
  have e : (⟨q + 1 - 1, by omega⟩ : Fin D.R.m) = ⟨q, hq⟩ := Fin.ext (show q + 1 - 1 = q by omega)
  rw [e]

theorem blocks_le (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau)
    (hj : 1 ≤ j) (hm : j ≤ D.R.m) :
    ∑ i ∈ Finset.Ico D.R.k (D.R.N (j - 1)), DV.nuRow D u j τ i ≤
      2 * (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
  obtain ⟨lo, hlo⟩ := exists_wj_mem_Icc_add_etaSz D L τ
  have hη : 0 ≤ L.etaSz := L.etaSz_pos.le
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hN1 : D.R.N (j - 1) = D.R.k + (j - 1) * (D.R.t + 1) := rfl
  have hterm : ∀ i ∈ Finset.Ico D.R.k (D.R.N (j - 1)), DV.nuRow D u j τ i ≤ L.etaSz := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    obtain ⟨hi1, hi2⟩ := hi
    have ht1 : 0 < D.R.t + 1 := Nat.succ_pos _
    have hlt : i - D.R.k < (j - 1) * (D.R.t + 1) := by rw [hN1] at hi2; omega
    have hq_lt : (i - D.R.k) / (D.R.t + 1) < j - 1 := (Nat.div_lt_iff_lt_mul ht1).2 hlt
    have hqm : (i - D.R.k) / (D.R.t + 1) < D.R.m := lt_of_lt_of_le hq_lt (by omega)
    have hdm := Nat.div_add_mod (i - D.R.k) (D.R.t + 1)
    have hnk : ¬ i < D.R.k := by omega
    have he := hcW_e_cast_eq_wj_succ D u τ _ hqm
    have hnat : ∀ q : ℕ, q < j - 1 → q + 1 ≤ D.R.m ∧ q + 2 ≤ j := fun q h1 => by omega
    obtain ⟨hq1, hq2⟩ := hnat _ hq_lt
    obtain ⟨hlo0, -⟩ := hlo ((i - D.R.k) / (D.R.t + 1) + 1) (Nat.succ_pos _) hq1
    obtain ⟨-, hhi⟩ := hlo j hj hm
    have hw := wSz_eq_wj' D j τ hj hm
    have hiR : (i : ℝ) = (D.R.k : ℝ) + ((D.R.t : ℝ) + 1) * (((i - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) +
        (((i - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have hsplit : ∀ A : ℕ, A = i - D.R.k → i = D.R.k + A := fun A hA => by omega
      have h' := hsplit _ hdm
      conv_lhs => rw [h']
      push_cast
      ring
    have hN1R : (D.R.N (j - 1) : ℝ) = (D.R.k : ℝ) + ((j : ℝ) - 1) * ((D.R.t : ℝ) + 1) := by
      rw [hN1]
      push_cast [Nat.cast_sub hj]
      ring
    have hN2R : (D.R.N j : ℝ) = (D.R.k : ℝ) + (j : ℝ) * ((D.R.t : ℝ) + 1) := by
      show ((D.R.k + j * (D.R.t + 1) : ℕ) : ℝ) = _
      push_cast
      ring
    have hqj : ((((i - D.R.k) / (D.R.t + 1) : ℕ) : ℝ)) + 2 ≤ (j : ℝ) := by
      exact_mod_cast hq2
    have hprod : 0 ≤ ((D.R.t : ℝ) + 1) * ((j : ℝ) - (((i - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) - 2) :=
      mul_nonneg (by linarith) (by linarith)
    unfold DV.nuRow DV.srcPar
    rw [dite_eq_right hnk, dite_eq_left hqm, hw, hN1R, hN2R, hiR]
    push_cast
    nlinarith
  calc ∑ i ∈ Finset.Ico D.R.k (D.R.N (j - 1)), DV.nuRow D u j τ i
      ≤ ∑ _i ∈ Finset.Ico D.R.k (D.R.N (j - 1)), L.etaSz := Finset.sum_le_sum hterm
    _ = ((D.R.N (j - 1) - D.R.k : ℕ) : ℝ) * L.etaSz := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ 2 * (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
        have hN : D.R.N (j - 1) - D.R.k = (j - 1) * (D.R.t + 1) := by
          rw [hN1]
          exact Nat.add_sub_cancel_left _ _
        rw [hN, Nat.cast_mul, Nat.cast_sub hj]
        push_cast
        have hjm : (j : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm
        have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        have hp : 0 ≤ (2 * (D.R.m : ℝ) - ((j : ℝ) - 1)) * ((D.R.t : ℝ) + 1) * L.etaSz :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) hη
        nlinarith

theorem nuAbs_split (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) :
    nuAbs D u j τ = (∑ i ∈ Finset.range (D.R.k - 1), DV.nuRow D u j τ (i + 1)) + DV.nuRow D u j τ 0 +
      ∑ i ∈ Finset.Ico D.R.k (D.R.N (j - 1)), DV.nuRow D u j τ i := by
  have hk := five_le_k D
  have hN : D.R.k ≤ D.R.N (j - 1) := by
    unfold Formalism.BasicNotions.Ranks.N
    exact Nat.le_add_right _ _
  have hr : ∑ i ∈ Finset.range D.R.k, DV.nuRow D u j τ i =
      (∑ i ∈ Finset.range (D.R.k - 1), DV.nuRow D u j τ (i + 1)) + DV.nuRow D u j τ 0 := by
    have h := Finset.sum_range_succ' (fun i => DV.nuRow D u j τ i) (D.R.k - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ D.R.k)] at h
    exact h
  unfold nuAbs
  rw [← Finset.sum_range_add_sum_Ico _ hN, hr]

private lemma nuRow_le_Sc_add_wSz (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ)
    (h1 : 1 ≤ i) (hi : i < D.R.k) : DV.nuRow D u j τ i ≤ L.Sc + DV.wSz D j τ := by
  have hu := cloudU_le D L u τ i hi h1
  have hN1 : (D.R.k : ℝ) ≤ (D.R.N (j - 1) : ℝ) := by
    unfold Formalism.BasicNotions.Ranks.N
    exact_mod_cast Nat.le_add_right _ _
  have hN2 : (D.R.k : ℝ) ≤ (D.R.N j : ℝ) := by
    unfold Formalism.BasicNotions.Ranks.N
    exact_mod_cast Nat.le_add_right _ _
  have hik : (i : ℝ) + 1 ≤ (D.R.k : ℝ) := by exact_mod_cast hi
  unfold DV.nuRow DV.srcPar
  rw [dite_eq_left hi]
  linarith

theorem cloudRows_le (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) :
    ∑ i ∈ Finset.range (D.R.k - 1), DV.nuRow D u j τ (i + 1) ≤
      ((D.R.k : ℝ) - 1) * (L.Sc + DV.wSz D j τ) := by
  have hk := five_le_k D
  calc ∑ i ∈ Finset.range (D.R.k - 1), DV.nuRow D u j τ (i + 1)
      ≤ ∑ _i ∈ Finset.range (D.R.k - 1), (L.Sc + DV.wSz D j τ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        exact nuRow_le_Sc_add_wSz D L u j τ (i + 1) (by omega) (by omega)
    _ = ((D.R.k : ℝ) - 1) * (L.Sc + DV.wSz D j τ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ D.R.k)]
        push_cast
        ring

theorem rowA : RowA := by
  intro D L j hj u τ
  simp only [SizeData₂.lifts, Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  have hk := five_le_k D
  have hw := wSz_eq_wj' D j τ hj1 hj2
  have hsplit := nuAbs_split D u j τ
  have hcl := cloudRows_le D L u j τ
  have hbl := blocks_le D L u j τ hj1 hj2
  have hr1 := nuRow_le_Sc_add_wSz D L u j τ 1 le_rfl (by omega)
  rw [hw] at hcl hr1
  have e : ((D.R.k : ℝ) - 1) * (L.Sc + wj D j τ) + (L.Sc + wj D j τ) =
      (D.R.k : ℝ) * (L.Sc + wj D j τ) := by ring
  rw [hsplit]
  linarith

theorem first_coordinate_le_three_scale (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hτ : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces) :
    (((D.hcW u τ).u ⟨0, by have := five_le_k D; omega⟩ : ℚ) : ℝ) ≤ 3 * L.Sc := by
  have hk := five_le_k D
  have hfirst := D.hcW_first u τ (by omega)
  have h2 := P.cloud_place_bound τ (by omega) hτ
  have hv := (L.cloud_v τ ⟨0, by omega⟩).2
  rw [hfirst]
  push_cast at h2
  linarith

theorem rowC : RowC := by
  intro D L P j hj u τ hτ
  simp only [SizeData₂.lifts, Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  have hk := five_le_k D
  have hu := first_coordinate_le_three_scale D L P u τ hτ
  have hw := wSz_eq_wj' D j τ hj1 hj2
  have hN1 : (D.R.k : ℝ) ≤ (D.R.N (j - 1) : ℝ) := by
    unfold Formalism.BasicNotions.Ranks.N
    exact_mod_cast Nat.le_add_right _ _
  have hN2 : (D.R.k : ℝ) ≤ (D.R.N j : ℝ) := by
    unfold Formalism.BasicNotions.Ranks.N
    exact_mod_cast Nat.le_add_right _ _
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk
  unfold DV.nuRow DV.srcPar
  rw [dite_eq_left (by omega : 0 < D.R.k), hw]
  push_cast
  linarith

theorem rowB : RowB := by
  intro D L P j hj u τ hτ
  have hC := rowC D L P j hj u τ hτ
  simp only [SizeData₂.lifts, Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  have hw := wSz_eq_wj' D j τ hj1 hj2
  have hsplit := nuAbs_split D u j τ
  have hcl := cloudRows_le D L u j τ
  have hbl := blocks_le D L u j τ hj1 hj2
  rw [hw] at hcl
  have e : ((D.R.k : ℝ) - 1) * (L.Sc + wj D j τ) + (3 * L.Sc + wj D j τ) =
      ((D.R.k : ℝ) + 2) * L.Sc + (D.R.k : ℝ) * wj D j τ := by ring
  rw [hsplit]
  linarith

end PI.SzCt.UnitaryGroupMassFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.SizeFacts
section
noncomputable section

namespace PI.SzCt.UnitaryGroupMassFormula

open Formalism.BasicNotions Formalism.MainNotions.G

theorem sizeFacts : SizeFacts := by
  intro D L hSz hx
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, hEta, -, -, hDel, -⟩ := hSz
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  have hx1 : (1 : ℝ) ≤ L.sc.x := by linarith
  have hb1 : 1 ≤ L.sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hb'0 : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a
    exact div_nonneg (mul_nonneg hx0.le (by linarith)) (Real.exp_pos _).le
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    unfold Formalism.BasicNotions.Ranks.n; exact_mod_cast D.R.ord_pos
  have ht1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have hη := L.etaSz_pos
  refine ⟨?_, ?_, hDel.2.2.2.1, ?_, hEta.2.2.2.2.1, hb1, hb'0⟩
  · intro t
    have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg hx0.le _) hLa.1
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    set Q := Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k with hQ
    have h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
      div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.log_nonneg hx1)) hLa0) hk0
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have h4 : 4 * Q ≤ 1 := by
      have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * Q := by rw [hQ]; ring
      unfold Formalism.MainNotions.SizeRho at hRho
      linarith
    have h5 := hBot t
    have h6 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = Q * L.sc.b' := by
      rw [hQ]; ring
    rw [h6] at h5
    nlinarith
  · have h := hEta.2.2.2.1
    calc L.etaSz ≤ (D.R.t : ℝ) * L.etaSz := le_mul_of_one_le_left hη.le ht1
      _ ≤ _ := h
  · unfold Scale.w''
    exact div_le_div_of_nonneg_left hb'0 hx0 (le_mul_of_one_le_right hx0.le hn1)

end PI.SzCt.UnitaryGroupMassFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.SzCtOf
section
noncomputable section

namespace PI.SzCt.UnitaryGroupMassFormula

open Formalism.BasicNotions Formalism.MainNotions.G

theorem ct_le (hA : RowA) (hB : RowB) (hC : RowC) (hS : SizeFacts) (hP : PlaceFacts)
    (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (hx : 3 ≤ L.sc.x) (hSz : Formalism.MainNotions.SizesAt L)
    (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (u : D.what₂.Word) (t : HH D) :
    ctD D u j t ≤ (if t ∈ D.host.TT then 2 * L.sc.b else 0) + 4 * (D.R.k : ℝ) * L.sc.b' := by
  obtain ⟨hbT, hη, hkSc, hw'', hmη, hb1, hb'0⟩ := hS D L hSz hx
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hP D
  have hj' := hj
  simp only [SizeData₂.lifts, Finset.mem_Icc] at hj'
  obtain ⟨hj1, hj2⟩ := hj'
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hx0 : 0 < L.sc.x := by linarith
  have hxne : L.sc.x ≠ 0 := hx0.ne'
  have hSc : 0 < L.Sc := L.Sc_pos
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := by linarith

  have hq : L.sc.b' / L.sc.x * L.sc.x = L.sc.b' := by field_simp
  have hq0 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb'0 hx0.le
  have hbx : 3 * (L.sc.b' / L.sc.x) ≤ L.sc.b' := by nlinarith
  have hkSc0 : 0 ≤ (D.R.k : ℝ) * L.Sc := mul_nonneg hk0 hSc.le
  have hw0 : 0 ≤ L.sc.w'' D.R.n := le_trans hkSc0 hkSc
  have hr : L.sc.w'' D.R.n / L.sc.x * L.sc.x = L.sc.w'' D.R.n := by field_simp
  have hr0 : 0 ≤ L.sc.w'' D.R.n / L.sc.x := div_nonneg hw0 hx0.le
  have hwx : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n := by nlinarith
  have h3Sc : 3 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := by nlinarith
  have hkb' : 5 * L.sc.b' ≤ (D.R.k : ℝ) * L.sc.b' := mul_le_mul_of_nonneg_right hk5 hb'0
  have hmη0 : 0 ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
    have : (0 : ℝ) ≤ L.etaSz := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hEta, -⟩ := hSz
      exact le_trans (Nat.cast_nonneg _) hEta.1
    positivity
  by_cases ht : t ∈ D.host.TT
  · simp only [ctD, if_pos ht]
    have hRA := hA D L j hj u (tauPl D (false, t))
    have hRC := hC D L P j hj u (tauPl D (true, t)) (hP3 t)
    have hwF := L.win_top j hj1 hj2 (tauPl D (false, t)) ⟨t, ht⟩ (hP1 t)
    have hbt := hbT ⟨t, ht⟩
    have hwT : wj D j (tauPl D (true, t)) ≤ L.sc.b + L.etaSz + 1 ∨
        wj D j (tauPl D (true, t)) ≤ L.sc.w'' D.R.n + L.etaSz := by
      rcases hP4 t with h | h
      · exact Or.inl (L.win_thick j hj1 hj2 _ h).2
      · exact Or.inr (L.win_thin j hj1 hj2 _ h).2
    have hkw : (D.R.k : ℝ) * wj D j (tauPl D (false, t)) ≤
        (D.R.k : ℝ) * ((L.bT ⟨t, ht⟩ : ℝ) + L.sc.b' / L.sc.x + L.etaSz) :=
      mul_le_mul_of_nonneg_left hwF.2 hk0
    have e1 : (D.R.k : ℝ) * ((L.bT ⟨t, ht⟩ : ℝ) + L.sc.b' / L.sc.x + L.etaSz) =
        (D.R.k : ℝ) * (L.bT ⟨t, ht⟩ : ℝ) + (D.R.k : ℝ) * (L.sc.b' / L.sc.x) +
          (D.R.k : ℝ) * L.etaSz := by ring
    have e2 : (D.R.k : ℝ) * (L.Sc + wj D j (tauPl D (false, t))) =
        (D.R.k : ℝ) * L.Sc + (D.R.k : ℝ) * wj D j (tauPl D (false, t)) := by ring
    have k1 : (D.R.k : ℝ) * (L.bT ⟨t, ht⟩ : ℝ) ≤ (D.R.k : ℝ) * (5 / 4 * L.sc.b') :=
      mul_le_mul_of_nonneg_left hbt hk0
    have k2 : (D.R.k : ℝ) * (L.sc.b' / L.sc.x) ≤ (D.R.k : ℝ) * (L.sc.b' / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0
    have k3 : (D.R.k : ℝ) * L.etaSz ≤ (D.R.k : ℝ) * (L.sc.b' / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0
    have e3 : (D.R.k : ℝ) * (5 / 4 * L.sc.b') + (D.R.k : ℝ) * (L.sc.b' / 3) +
        (D.R.k : ℝ) * (L.sc.b' / 3) = 23 / 12 * ((D.R.k : ℝ) * L.sc.b') := by ring
    have e4 : 4 * (D.R.k : ℝ) * L.sc.b' = 4 * ((D.R.k : ℝ) * L.sc.b') := by ring
    rcases hwT with hT | hT <;> linarith
  · simp only [ctD, if_neg ht]
    have hthin := hP2 t ht
    have hRB := hB D L P j hj u (tauPl D (false, t)) hthin.2.1
    have hwF := (L.win_thin j hj1 hj2 (tauPl D (false, t)) hthin).2
    have hkw : (D.R.k : ℝ) * wj D j (tauPl D (false, t)) ≤
        (D.R.k : ℝ) * (L.sc.w'' D.R.n + L.etaSz) :=
      mul_le_mul_of_nonneg_left hwF hk0
    have k1 : (D.R.k : ℝ) * (L.sc.w'' D.R.n + L.etaSz) ≤ (D.R.k : ℝ) * (2 * (L.sc.b' / 3)) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0
    have e1 : ((D.R.k : ℝ) + 2) * L.Sc = (D.R.k : ℝ) * L.Sc + 2 * L.Sc := by ring
    have e2 : (D.R.k : ℝ) * (2 * (L.sc.b' / 3)) = 2 / 3 * ((D.R.k : ℝ) * L.sc.b') := by ring
    have e4 : 4 * (D.R.k : ℝ) * L.sc.b' = 4 * ((D.R.k : ℝ) * L.sc.b') := by ring
    linarith

theorem szCt_of (hA : RowA) (hB : RowB) (hC : RowC) (hS : SizeFacts) (hP : PlaceFacts) :
    PI.SzCt.SzCt := by
  unfold PI.SzCt.SzCt
  intro eps Ct CGam Cc CT2 PK
  refine ⟨3, ?_⟩
  intro D L P _ hx hSz j hj u
  have hsum : ∑ t : HH D, ctD D u j t ≤
      ∑ t : HH D, ((if t ∈ D.host.TT then 2 * L.sc.b else 0) + 4 * (D.R.k : ℝ) * L.sc.b') :=
    Finset.sum_le_sum (fun t _ => ct_le hA hB hC hS hP D L P hx hSz j hj u t)
  refine le_trans hsum ?_
  obtain ⟨-, -, -, -, -, -, hb'0⟩ := hS D L hSz hx
  have hcard : Fintype.card (HH D) = D.R.n := by
    rw [Fintype.card_eq_nat_card]
    show Nat.card (Fin D.R.ord) = D.R.n
    simp [Nat.card_eq_fintype_card, Formalism.BasicNotions.Ranks.n]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ, hcard]
  have hf : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by
    unfold Formalism.BasicNotions.Ranks.f
    push_cast
    ring
  rw [hf]
  have e : (D.R.n : ℝ) * (4 * (D.R.k : ℝ) * L.sc.b') = 2 * (2 * (D.R.n : ℝ)) * (D.R.k : ℝ) * L.sc.b' := by
    ring
  have e2 : (D.host.TT.card : ℝ) * (2 * L.sc.b) = 2 * (D.host.TT.card : ℝ) * L.sc.b := by ring
  linarith

end PI.SzCt.UnitaryGroupMassFormula
end
end

