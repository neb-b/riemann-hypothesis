module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaFiveOneOfTheoremTwo
public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PointsPropertyOfD7

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LogFactorialProductDifference
section
noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

theorem exp_neg_r_le_third (D : D7) : Real.exp (-(D.R.r : ℝ)) ≤ 1 / 3 := by
  have hr : 2 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    first
      | (show 2 ≤ D.R.k + D.R.m - 1; omega)
      | omega
  have hr' : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  calc Real.exp (-(D.R.r : ℝ)) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
    _ = 1 / Real.exp 2 := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3

theorem place_dimension_upper_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (h3 : SigmaDegreeTwoSidedBoundOfGap D) (hgap : ∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D 8192 (1 / 3)))
    (u : D.what₂.Word) (ρ : D.what₂.Tau) :
    Real.log (D.dsig ρ) - Real.log (dimV (uColR D u ρ)) ≤
      (D.R.k : ℝ) * D.R.m * (Real.log 3 + 5 * Real.log (2 * D.R.k) + 5 * sc.L + 10) := by
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hpl := place_data_under_section_B D sc C0 Δ w hB u ρ
  have b7 : 1 ≤ Δ := hB.2.2.2.2.2.2.1
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have h := (h3 (1 / 3) (exp_neg_r_le_third D) (by norm_num) ρ
    (fun a b hab => le_trans (explicit_gap_le_general_gap D 8192 (1 / 3) le_rfl) (hgap ρ a b hab))).2
  rw [formal_degree_line_eq, count_plus_eq, count_minus_eq] at h
  obtain ⟨hd, hT, hlog⟩ := Formalism.LogVandermondeBounds.StandardLattice.UpperPlace_holds sc.eps sc.x sc.eps_pos sc.one_lt_alt.le D.R.k D.R.m Δ 3
      (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) hm D.R.m_even (by omega) hmk b7 (by norm_num) hpl
      (fun i j hij hj => one_le_column_sub_of_lt D u ρ i j hij hj)
  have a1 := abs_param_sup_nonneg (rowLam D ρ)
  have a2 := abs_param_sup_le D ρ
  have hr1 : (1 : ℝ) ≤ ((D.R.k - 1 + D.R.m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ D.R.k - 1 + D.R.m)
  have h' : D.dsig ρ ≤ 4 * Formalism.LogVandermondeBounds.StandardLattice.dTau D.R.k D.R.m (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) *
      (3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * ((D.R.k - 1 + D.R.m : ℕ) : ℝ) *
        (vN D ρ 0 + bN D ρ (D.R.m - 1))) ^ ((D.R.k - 1 + D.R.m / 2) * (D.R.m / 2)) := by
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have c0 : 0 ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) := by positivity
    calc 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * lamAbs (rowLam D ρ)
        ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * (vN D ρ 0 + bN D ρ (D.R.m - 1)) :=
          mul_le_mul_of_nonneg_left a2 c0
      _ = 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * 1 * (vN D ρ 0 + bN D ρ (D.R.m - 1)) := by ring
      _ ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * ((D.R.k - 1 + D.R.m : ℕ) : ℝ) *
          (vN D ρ 0 + bN D ρ (D.R.m - 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 c0) (le_trans a1 a2)
  rw [dim_weyl_column_eq]
  have h4 := Real.log_le_log (D.dsig_pos ρ) h'
  have eL : sc.L = sc.x ^ sc.eps := rfl
  rw [eL]
  linarith

theorem facProd_pos' (N : ℕ) : 0 < facProd N :=
  Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i

theorem log_factorial_product_difference (k r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    Real.log (facProd r) - Real.log (facProd k) ≤ ((r - k : ℕ) : ℝ) * ((r : ℝ) * Real.log r) := by
  have hsplit : facProd r = facProd k * ∏ i ∈ Finset.Ico k r, ((i.factorial : ℕ) : ℝ) := by
    unfold facProd
    rw [Finset.prod_range_mul_prod_Ico _ hkr]
  have hk0 : 0 < facProd k := facProd_pos' k
  have hP0 : 0 < ∏ i ∈ Finset.Ico k r, ((i.factorial : ℕ) : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  rw [hsplit, Real.log_mul hk0.ne' hP0.ne', add_sub_cancel_left,
    Real.log_prod (fun i _ => by exact_mod_cast (Nat.factorial_pos i).ne')]
  calc ∑ i ∈ Finset.Ico k r, Real.log ((i.factorial : ℕ) : ℝ)
      ≤ ∑ i ∈ Finset.Ico k r, ((r : ℝ) * Real.log r) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hir : i ≤ r := (Finset.mem_Ico.mp hi).2.le
        have h1 : ((i.factorial : ℕ) : ℝ) ≤ (r : ℝ) ^ r := by
          exact_mod_cast (Nat.factorial_le_pow i).trans
            ((Nat.pow_le_pow_left hir i).trans (Nat.pow_le_pow_right (by omega) hir))
        calc Real.log ((i.factorial : ℕ) : ℝ) ≤ Real.log ((r : ℝ) ^ r) :=
              Real.log_le_log (by exact_mod_cast Nat.factorial_pos i) h1
          _ = (r : ℝ) * Real.log r := by rw [Real.log_pow]
    _ = ((r - k : ℕ) : ℝ) * ((r : ℝ) * Real.log r) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

theorem log_X_upper_arithmetic (f k m L CY lv l2v SL lg S5 S6 X : ℝ) (hf : 0 < f) (hk : 5 ≤ k) (hm : 44 ≤ m) (hmk : m ≤ k)
    (hL : 9 ≤ L) (hlv0 : 0 ≤ lv) (hlv : lv ≤ L) (h2v : 0 ≤ l2v) (hSL : SL ≤ f * m) (hlg0 : 0 ≤ lg)
    (hlg : lg ≤ 2 * CY * L) (hS5 : S5 ≤ 0)
    (hS6 : S6 ≤ f * (k * m * (2 + 5 * L + 5 * L + 10) + m * (2 * k * L)))
    (id : f * k * X = f * ((m - 1) * k + m * (m - 1) / 2) * lv - f * ((m - 1) / 2) * l2v + SL +
      f * (m * (2 * k + m - 1) / 2) * lg + f * S5 + S6) :
    X ≤ (15 + 3 * CY) * m * L := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hL0 : 0 < L := by linarith
  have hCY : 0 ≤ CY := by
    by_contra h
    push_neg at h
    have : 2 * CY * L < 0 := by nlinarith
    linarith
  have ht1 : f * ((m - 1) * k + m * (m - 1) / 2) * lv ≤ f * ((m - 1) * k + m * (m - 1) / 2) * L :=
    mul_le_mul_of_nonneg_left hlv (by have : 0 ≤ (m - 1) * k := by nlinarith
                                      have : 0 ≤ m * (m - 1) / 2 := by nlinarith
                                      positivity)
  have ht2 : 0 ≤ f * ((m - 1) / 2) * l2v := by
    have : 0 ≤ (m - 1) / 2 := by linarith
    positivity
  have ht4 : f * (m * (2 * k + m - 1) / 2) * lg ≤ f * (m * (2 * k + m - 1) / 2) * (2 * CY * L) :=
    mul_le_mul_of_nonneg_left hlg (by have : 0 ≤ m * (2 * k + m - 1) / 2 := by nlinarith
                                      positivity)
  have ht5 : f * S5 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf.le hS5
  have hsum : f * k * X ≤ f * (((m - 1) * k + m * (m - 1) / 2) * L + m +
      m * (2 * k + m - 1) * CY * L + k * m * (12 + 12 * L)) := by
    rw [id]
    nlinarith
  have hpoly : ((m - 1) * k + m * (m - 1) / 2) * L + m + m * (2 * k + m - 1) * CY * L +
      k * m * (12 + 12 * L) ≤ k * ((15 + 3 * CY) * m * L) := by
    have a1 : 0 ≤ CY * L * m * (k - m + 1) := by
      have : 0 ≤ k - m + 1 := by linarith
      positivity
    have a2 : 0 ≤ k * m * (L - 9) := by
      have : 0 ≤ L - 9 := by linarith
      positivity
    have a3 : 0 ≤ m * (k - m) * L := by
      have : 0 ≤ k - m := by linarith
      positivity
    have a4 : 0 ≤ k * L := by positivity
    have a5 : m ≤ k * m * L := by nlinarith
    nlinarith
  have hfk : 0 < f * k := mul_pos hf hk0
  have : f * k * X ≤ f * k * ((15 + 3 * CY) * m * L) := by
    calc f * k * X ≤ f * (((m - 1) * k + m * (m - 1) / 2) * L + m +
          m * (2 * k + m - 1) * CY * L + k * m * (12 + 12 * L)) := hsum
      _ ≤ f * (k * ((15 + 3 * CY) * m * L)) := mul_le_mul_of_nonneg_left hpoly hf.le
      _ = f * k * ((15 + 3 * CY) * m * L) := by ring
  exact le_of_mul_le_mul_left this hfk

end Formalism.MainNotions.StandardLattice
end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LogWeightMinusLogBBound
section
noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

theorem b_ge_one_section_B (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : 1 ≤ bN D ρ j := by
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  have hL := scale_one_le_L sc
  have hkpos : (0 : ℝ) < D.R.k := by
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    nlinarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 0 < D.R.k := by exact_mod_cast hkpos
    exact_mod_cast Nat.one_le_of_lt this
  have hx := sc.one_lt_alt
  have hpos : ∀ i, i < D.R.m → 1 ≤ bN D ρ i := by
    intro i
    induction i with
    | zero =>
      intro _
      have h0 := (hb0 ρ).1
      have h4 : 1 ≤ bN D ρ 0 / sc.x := le_trans (by nlinarith) h0
      have h5 := (le_div_iff₀ (by linarith)).mp h4
      nlinarith
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := (hw ρ i (by omega)).2.1
      have h3 := hinc ρ i hi
      linarith
  exact hpos j hj

theorem weights_le_two_b (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : w j ρ ≤ 2 * sc.b := by
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  have hstep : ∀ i, i + 1 < D.R.m → w i ρ ≤ w (i + 1) ρ := fun i hi =>
    le_of_lt (lt_trans (hinc ρ i hi) (hw ρ (i + 1) hi).2.1)
  have hmono : ∀ d, ∀ i, i + d = D.R.m - 1 → w i ρ ≤ w (D.R.m - 1) ρ := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have h : i = D.R.m - 1 := by omega
      simp only [h, le_refl]
    | succ d ih =>
      intro i hi
      exact le_trans (hstep i (by omega)) (ih (i + 1) (by omega))
  exact le_trans (hmono (D.R.m - 1 - j) j (by omega)) (hb0 ρ).2

theorem log_weight_minus_log_b_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    (D.R.k : ℝ) * Real.log (w j ρ) - ((D.R.k : ℝ) - 1) * Real.log (bN D ρ j) ≤ (D.R.k : ℝ) / sc.x + 2 * sc.L := by
  have hb1 := b_ge_one_section_B D sc C0 Δ w hB ρ j hj
  have hwl := weights_le_two_b D sc C0 Δ w hB ρ j hj
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  obtain ⟨hw0, hbw, habs⟩ := hw ρ j hj
  have hL := scale_one_le_L sc
  have hx := sc.one_lt_alt
  have hkpos : (0 : ℝ) < D.R.k := by
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    nlinarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 0 < D.R.k := by exact_mod_cast hkpos
    exact_mod_cast Nat.one_le_of_lt this
  have hBpos : 0 < bN D ρ j := by linarith
  have hratio : Real.log (w j ρ) - Real.log (bN D ρ j) ≤ 1 / sc.x := by
    rw [← Real.log_div hw0.ne' hBpos.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hw0 hBpos)
    have h2 : w j ρ / bN D ρ j - 1 ≤ 1 / sc.x := by
      rw [div_sub_one hBpos.ne', div_le_div_iff₀ hBpos (by linarith)]
      have h4 := (abs_le.mp habs).2
      have h3 : (w j ρ - bN D ρ j) * sc.x ≤ bN D ρ j := by rwa [le_div_iff₀ (by linarith)] at h4
      linarith
    linarith
  have hlogW : Real.log (w j ρ) ≤ 2 * sc.L := by
    have h1 : Real.log (w j ρ) ≤ Real.log (2 * sc.b) := Real.log_le_log hw0 hwl
    have h2 : Real.log (2 * sc.b) = Real.log 2 + sc.L := by
      unfold Scale.b
      rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]
    have h3 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hx1 : 0 < 1 / sc.x := one_div_pos.mpr (by linarith)
  have hkx : ((D.R.k : ℝ) - 1) * (1 / sc.x) ≤ (D.R.k : ℝ) / sc.x := by
    have e : ((D.R.k : ℝ) - 1) * (1 / sc.x) = (D.R.k : ℝ) / sc.x - 1 / sc.x := by ring
    linarith
  have hmul : ((D.R.k : ℝ) - 1) * (Real.log (w j ρ) - Real.log (bN D ρ j)) ≤
      ((D.R.k : ℝ) - 1) * (1 / sc.x) :=
    mul_le_mul_of_nonneg_left hratio (by linarith)
  nlinarith

theorem place_dimension_lower_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (h2k : Real.log (2 * (D.R.k : ℝ)) ≤ sc.L)
    (hx : 2 * (Real.log 8 + 1 + Real.log sc.x) ≤ sc.L) (u : D.what₂.Word) (ρ : D.what₂.Tau)
    (h3 : (2 / 3 : ℝ) * dimV (rowLam D ρ) ≤ D.dsig ρ) :
    Real.log (2 / 3) + ((D.R.k : ℝ) - 1) * ∑ j ∈ range D.R.m, Real.log (bN D ρ j) - 5 * D.R.k * sc.L ≤
      Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) := by
  have hP := place_data_under_section_B D sc C0 Δ w hB u ρ
  have hm2 := D.R.two_le_m
  have hk5 := D.R.m_add_three_le_k
  have hΔ : 1 ≤ Δ := by
    unfold DataB at hB
    exact hB.2.2.2.2.2.2.1
  have hx1 : (1 : ℝ) ≤ sc.x := sc.one_lt_alt.le
  obtain ⟨hvu, hvr, hVV⟩ := Formalism.LogVandermondeBounds.StandardLattice.VandPlace_holds sc.eps sc.x sc.eps_pos hx1 D.R.k D.R.m Δ
    (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) (by omega) (by omega) hΔ hP
  have hfac : 0 < facProd D.R.r := Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  have hvandu : vand (uColR D u ρ) = Formalism.LogVandermondeBounds.StandardLattice.vandN (uN D u ρ) D.R.k := by
    rw [column_param_eq_fun, vandermonde_fin_eq_nat]
  have hdimrow : dimV (rowLam D ρ) =
      Formalism.LogVandermondeBounds.StandardLattice.vandN (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) (D.R.k - 1 + D.R.m) /
        facProd D.R.r := by
    rw [dim_weyl_line_eq, rank_eq_sum]
    rfl
  set A := Formalism.LogVandermondeBounds.StandardLattice.vandN (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) (D.R.k - 1 + D.R.m) with hAdef
  set U := Formalism.LogVandermondeBounds.StandardLattice.vandN (uN D u ρ) D.R.k with hUdef
  have hdsig : (2 / 3 : ℝ) * (A / facProd D.R.r) ≤ D.dsig ρ := by
    rw [← hdimrow]
    exact h3
  have hA' : (2 / 3 : ℝ) * A ≤ D.dsig ρ * facProd D.R.r := by
    have := mul_le_mul_of_nonneg_right hdsig hfac.le
    rwa [mul_assoc, div_mul_cancel₀ _ hfac.ne'] at this
  have hdivle : (2 / 3 : ℝ) * A / U ≤ D.dsig ρ * facProd D.R.r / U := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hA' (inv_nonneg.mpr hvu.le)
  have hlog1 := Real.log_le_log (div_pos (mul_pos (by norm_num) hvr) hvu) hdivle
  rw [Real.log_div (mul_pos (by norm_num) hvr).ne' hvu.ne', Real.log_mul (by norm_num) hvr.ne'] at hlog1
  have hLd : sc.L = sc.x ^ sc.eps := rfl
  have h8 : Real.log (8 * (sc.x * Real.exp (sc.x ^ sc.eps))) = Real.log 8 + Real.log sc.x + sc.L := by
    rw [Real.log_mul (by norm_num) (mul_pos (by linarith) (Real.exp_pos _)).ne',
      Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, hLd]
    ring
  rw [h8] at hVV
  have hkpos : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hlogk : Real.log D.R.k ≤ sc.L := le_trans (Real.log_le_log hkpos (by linarith)) h2k
  have hm1 := mul_le_mul_of_nonneg_left hx hkpos.le
  have hm2' := mul_le_mul_of_nonneg_left hlogk hkpos.le
  rw [hvandu]
  linarith

theorem log_X_lower_arithmetic (F K Mm Lr lv l2v G SL SG SP SW X lo : ℝ)
    (hF : 1 ≤ F) (hM : 44 ≤ Mm) (hMK : Mm ≤ K) (hL : 1 ≤ Lr) (hlv0 : 0 ≤ lv) (hlv : lv ≤ Lr) (hl2v : l2v ≤ Lr)
    (hG : 0 ≤ G) (hSL : -(F * (Mm - 1)) ≤ SL) (hSG : -2 ≤ SG)
    (hSPW : F * (-1 - 5 * K * Lr - (K + 2 * K * Lr)) ≤ SP - K * SW)
    (hid : F * K * X = F * ((Mm - 1) * K + Mm * (Mm - 1) / 2) * lv - F * ((Mm - 1) / 2) * l2v + SL +
      F * (Mm * (2 * K + Mm - 1) / 2) * G + F * SG + SP)
    (hlo : F * K * lo = K * SW + F * K * Mm * lv + F * K * Mm * G - 11 * F * K * Lr) : lo ≤ X := by
  have hK : 0 < K := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hFK : 0 < F * K := mul_pos (by linarith) hK
  have hMM : 0 ≤ Mm * (Mm - 1) / 2 := by nlinarith
  have key : F * K * (X - lo) = F * (Mm * (Mm - 1) / 2) * lv - F * K * lv - F * ((Mm - 1) / 2) * l2v +
      SL + F * (Mm * (Mm - 1) / 2) * G + F * SG + (SP - K * SW) + 11 * F * K * Lr := by
    linear_combination hid - hlo
  have hQ : 0 ≤ 3 * K * Lr - (Mm - 1) / 2 * Lr - Mm - 2 - K := by
    nlinarith [mul_le_mul_of_nonneg_right hMK (by linarith : (0 : ℝ) ≤ Lr),
      mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ K),
      mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ Mm)]
  have h1 : 0 ≤ F * (Mm * (Mm - 1) / 2) * lv := mul_nonneg (mul_nonneg hF0 hMM) hlv0
  have h2 : F * K * lv ≤ F * K * Lr := mul_le_mul_of_nonneg_left hlv hFK.le
  have h3 : F * ((Mm - 1) / 2) * l2v ≤ F * ((Mm - 1) / 2) * Lr :=
    mul_le_mul_of_nonneg_left hl2v (mul_nonneg hF0 (by linarith))
  have h4 : 0 ≤ F * (Mm * (Mm - 1) / 2) * G := mul_nonneg (mul_nonneg hF0 hMM) hG
  have h5 : F * (-2) ≤ F * SG := mul_le_mul_of_nonneg_left hSG hF0
  have h6 : 0 ≤ F * (3 * K * Lr - (Mm - 1) / 2 * Lr - Mm - 2 - K) := mul_nonneg hF0 hQ
  have hpos : 0 ≤ F * K * (X - lo) := by
    rw [key]
    nlinarith
  by_contra hlt
  push_neg at hlt
  have : F * K * (X - lo) < 0 := mul_neg_of_pos_of_neg hFK (by linarith)
  linarith

end Formalism.MainNotions.StandardLattice
end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.RamificationTwoAndConjugationAtQAndD
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal

def RamPart (D : D7) : Prop :=
  ∀ p : ℕ, p.Prime →
    (1 < (span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) ↔ p ∣ D.host.condN)

private theorem deg_part (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  show 4 * D.R.toFrame.ord = 2 * (2 * D.R.toFrame.ord)
  ring

private theorem unram_part (D : D7) (𝔭 : Ideal (𝓞 D.host.F)) (h𝔭 : 𝔭.IsPrime) (h0 : 𝔭 ≠ ⊥) :
    𝔭.ramificationIdxIn (𝓞 D.host.E) = 1 := by

  haveI := D.host.der.cm
  haveI := D.host.galois
  haveI := h𝔭.isMaximal h0
  haveI : IsGalois D.host.F D.host.E := by
    first
    | infer_instance
    | exact IsGalois.tower_top_of_isGalois ℚ D.host.F D.host.E
  have h3 : Module.finrank D.host.F D.host.E = 2 := by
    first
    | exact IsQuadraticExtension.finrank_eq_two _ _
    | (have h4 := Module.finrank_mul_finrank ℚ D.host.F D.host.E; have h5 : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos; rw [D.host.der.finrank_E] at h4; rw [D.host.der.finrank_F] at h4 h5; exact Nat.eq_of_mul_eq_mul_left h5 (by linarith))
  have h2 : Nat.card (D.host.E ≃ₐ[D.host.F] D.host.E) = 2 := by
    first
    | rw [IsGalois.card_aut_eq_finrank, h3]
    | rw [Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h3]
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭 (𝓞 D.host.E)
    (D.host.E ≃ₐ[D.host.F] D.host.E)
  rw [h2] at h1
  rcases D.host.der.eta.1 𝔭 h𝔭 h0 with h | ⟨h, hf⟩
  · rw [h] at h1
    have h6 : 𝔭.ramificationIdxIn (𝓞 D.host.E) * 𝔭.inertiaDegIn (𝓞 D.host.E) = 1 := by
      linarith
    exact Nat.eq_one_of_mul_eq_one_right h6
  · rw [h, hf] at h1
    omega

private theorem split_part (D : D7) (p : ℕ) (hpp : p.Prime) (hp : p ∣ D.host.condN)
    (𝔭 : Ideal (𝓞 D.host.F)) (h𝔭 : 𝔭.IsPrime) (hlo : 𝔭.LiesOver (span {(p : ℤ)})) :
    (primesOver 𝔭 (𝓞 D.host.E)).ncard = 2 := by
  have h0 : 𝔭 ≠ ⊥ := by
    rintro rfl
    have h2 : span {(p : ℤ)} = ⊥ := by
      rw [hlo.over]
      exact Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 D.host.F)).injective_int
    rw [Ideal.span_singleton_eq_bot] at h2
    exact hpp.ne_zero (by exact_mod_cast h2)
  rcases D.host.der.eta.1 𝔭 h𝔭 h0 with h | ⟨h, -⟩
  · exact h
  ·
    exfalso
    obtain ⟨P, hP⟩ := Set.ncard_eq_one.mp h
    have hPm : P ∈ primesOver 𝔭 (𝓞 D.host.E) := by
      rw [hP]
      exact Set.mem_singleton P
    haveI : P.IsPrime := hPm.1
    haveI : P.LiesOver 𝔭 := hPm.2
    haveI : Fact p.Prime := ⟨hpp⟩
    haveI : P.LiesOver (span {(p : ℤ)}) := by
      first
      | exact Ideal.LiesOver.trans P 𝔭 (span {(p : ℤ)})
      | infer_instance
    have h1 := D.host.der.eta.2.2 p hp P
    have hc : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = 𝔭 :=
      (Ideal.LiesOver.over (P := P) (p := 𝔭)).symm
    rw [hc] at h1
    simp [Formalism.HC.HostRaw.etaF, h] at h1

private theorem rd_part (D : D7) : rdF D = D.host.rdE := by
  unfold Formalism.MainNotions.GlobalTheoryTheory.rdF Formalism.BasicNotions.Host.rdE
  rw [D.host.der.discr_sq, D.host.der.finrank_E, D.host.der.finrank_F]
  push_cast
  rw [abs_pow, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  ring

theorem lemma_one_one_of_ramified (D : D7) (hRam : RamPart D) : Conclusion1 D := by
  unfold Conclusion1
  exact ⟨D.host.der.cm, deg_part D, hRam, D.host.der.norm_mu,
    fun 𝔭 h𝔭 h0 => unram_part D 𝔭 h𝔭 h0,
    fun p hpp hp 𝔭 h𝔭 hlo => split_part D p hpp hp 𝔭 h𝔭 hlo, rd_part D⟩

theorem ramification_two_and_conjugation_at_q_and_d (D : D7) : Conclusion1 D :=
  lemma_one_one_of_ramified D (fun p hp => SlopeTestRemainingChoices.ram_iff D p hp)

end Formalism.MainNotions.UnusedSlot33

end
end

