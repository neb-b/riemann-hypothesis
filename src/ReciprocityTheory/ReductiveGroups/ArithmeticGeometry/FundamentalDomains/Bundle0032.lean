module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorBoundOfCoefficientBounds

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LogDOfPosBound
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate

noncomputable section

lemma spread_bound {n : ℕ} (f Δ : Fin n → ℝ) (h0 : ∑ k, Δ k = 0) :
    |∑ k, f k * Δ k| ≤ ((⨆ k, f k) - ⨅ k, f k) * ∑ k, |Δ k| := by
  have hb : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
  have hb' : BddBelow (Set.range f) := (Set.finite_range f).bddBelow
  have hc : ∑ k, (⨅ j, f j) * Δ k = 0 := by rw [← Finset.mul_sum, h0, mul_zero]
  have key : ∑ k, f k * Δ k = ∑ k, (f k - ⨅ j, f j) * Δ k := by
    simp only [sub_mul, Finset.sum_sub_distrib, hc, sub_zero]
  rw [key, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  have h1 : f k ≤ ⨆ j, f j := le_ciSup hb k
  have h2 : ⨅ j, f j ≤ f k := ciInf_le hb' k
  have h3 : |f k - ⨅ j, f j| ≤ (⨆ j, f j) - ⨅ j, f j := by
    rw [abs_of_nonneg (sub_nonneg.mpr h2)]
    linarith
  exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma norm_dOf {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    ‖dOf X y τ k‖ = |(dOf X y τ k).re| := by
  have h : dOf X y τ k = ((dOf X y τ k).re : ℂ) := by
    apply Complex.ext <;> simp [dOf_real X hy τ k]
  rw [h, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]

lemma ratio_eq {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    dmin X.Gm y τ k.succ / dmin X.Gm y τ k.castSucc = dOf X y τ k := by
  have hd0 : dmin X.Gm y τ k.castSucc ≠ 0 := by
    intro h0; have h := (hy τ).2 k.castSucc; rw [h0] at h; simp at h
  rw [dmin_succ X hy τ k]
  field_simp

lemma nfac_log {y : Frame X.Ψ r} (hy : y ∈ X.dom) (la : Wt X.Ψ r) :
    Real.log (X.nfac la y) = ∑ τ, ∑ k : Fin r, (-(la τ k : ℝ) / 2) * Real.log ‖dOf X y τ k‖ := by
  unfold Data.nfac
  have hpos : ∀ τ k, 0 < ‖dOf X y τ k‖ := fun τ k => by
    rw [norm_dOf X hy τ k]
    apply abs_pos.2
    have h := sgn_dOf_pos X hy τ k
    intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (by
      rw [ratio_eq X hy τ k]; exact hpos τ k) _).ne')]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun k _ => (Real.rpow_pos_of_pos (by rw [ratio_eq X hy τ k]; exact hpos τ k) _).ne')]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ratio_eq X hy τ k, Real.log_rpow (hpos τ k)]

lemma sum_log_dOf {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) : ∑ k : Fin r, Real.log ‖dOf X (X.xZ x Z) τ k‖ = 0 := by
  have hy := xZ_mem_dom X hx ho hZ
  have hpos : ∀ k, ‖dOf X (X.xZ x Z) τ k‖ ≠ 0 := fun k => by
    rw [norm_dOf X hy τ k]
    apply (abs_pos.2 _).ne'
    have h := sgn_dOf_pos X hy τ k
    intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  rw [← Real.log_prod (fun k _ => hpos k), ← norm_prod]
  have hp : ∏ k : Fin r, dOf X (X.xZ x Z) τ k = dmin X.Gm (X.xZ x Z) τ (Fin.last r) := by
    rw [dmin_prod X hy τ (Fin.last r)]
    rfl
  rw [hp]
  unfold dmin
  rw [gram_xZ X ho Z τ, lminor_last]
  unfold Gp
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_lowBlock, Matrix.det_diagonal, one_mul]
  rw [show ((X.lowBlock Z τ).map (starRingEnd ℂ)).det = (starRingEnd ℂ) (X.lowBlock Z τ).det from
    (RingHom.map_det _ _).symm, det_lowBlock, map_one, mul_one, norm_prod]
  rw [Finset.prod_eq_one fun k _ => ?_, Real.log_one]
  unfold sgn
  split_ifs <;> simp

lemma log_dOf_pos_bound {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (k : Fin r) (hk : (k : ℕ) < X.p0) :
    Real.log ‖dOf X (X.xZ x Z) τ k‖ ≤ 0 ∧
      -Real.log ‖dOf X (X.xZ x Z) τ k‖ ≤ X.zN Z ^ 2 / (1 - X.zN Z ^ 2) := by
  have hy := xZ_mem_dom X hx ho hZ
  obtain ⟨h1, h2⟩ := pivot_pos X hx ho hZ τ k hk
  have h0 : 0 ≤ X.zN Z := le_trans (opN_nonneg _) (opN_le_zN X Z τ)
  have hu : X.zN Z ^ 2 < 1 := by nlinarith
  have htpos : 0 < (dOf X (X.xZ x Z) τ k).re := by linarith
  rw [norm_dOf X hy τ k, abs_of_pos htpos]
  refine ⟨Real.log_nonpos htpos.le h2, ?_⟩
  rw [← Real.log_inv]
  have h3 := Real.log_le_sub_one_of_pos (inv_pos.2 htpos)
  have h4 : (dOf X (X.xZ x Z) τ k).re⁻¹ ≤ (1 - X.zN Z ^ 2)⁻¹ := inv_anti₀ (by linarith) h1
  have hne : (1 - X.zN Z ^ 2) ≠ 0 := (by linarith : (0:ℝ) < 1 - X.zN Z ^ 2).ne'
  have h5 : (1 - X.zN Z ^ 2)⁻¹ - 1 = X.zN Z ^ 2 / (1 - X.zN Z ^ 2) := by
    field_simp
    ring
  linarith

lemma log_dOf_neg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (k : Fin r) (hk : X.p0 ≤ (k : ℕ)) : 0 ≤ Real.log ‖dOf X (X.xZ x Z) τ k‖ := by
  have hy := xZ_mem_dom X hx ho hZ
  have hk' : k = nI X ⟨(k : ℕ) - X.p0, by have := k.isLt; omega⟩ := by
    apply Fin.ext; simp only [nI]; omega
  have h := pivot_neg X hx ho hZ τ ⟨(k : ℕ) - X.p0, by have := k.isLt; omega⟩
  rw [← hk'] at h
  rw [norm_dOf X hy τ k, abs_of_neg (by linarith)]
  exact Real.log_nonneg (by linarith)

lemma spread_nonneg (la : Wt X.Ψ r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  unfold Data.spread
  rcases isEmpty_or_nonempty (Fin r) with h | h
  · simp [Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]
  · exact sub_nonneg.mpr (ciInf_le_ciSup (Set.finite_range _).bddBelow (Set.finite_range _).bddAbove)

theorem nfac_xZ {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 10)
    {Z : X.Coord} (hZ : X.zN Z ≤ ρ) (la : Wt X.Ψ r) (w : ℝ) (hw : (∑ τ, X.spread la τ) ≤ w) :
    |Real.log (X.nfac la (X.xZ x Z)) - Real.log (X.nfac la x)| ≤ 4 * w * r * X.zN Z ^ 2 := by
  have hZ1 : X.zN Z < 1 := by linarith
  have hy := xZ_mem_dom X hx ho hZ1

  have hx1 : Real.log (X.nfac la x) = 0 := by
    have hn : ∀ τ (i : Fin (r + 1)), ‖dmin X.Gm x τ i‖ = 1 := by
      intro τ i
      unfold dmin
      rw [ho τ, lminor_diagonal, norm_prod]
      refine Finset.prod_eq_one fun j _ => ?_
      unfold sgn
      split_ifs <;> simp
    unfold Data.nfac
    rw [Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => by rw [norm_div, hn, hn, div_one,
      Real.one_rpow], Real.log_one]
  rw [hx1, sub_zero, nfac_log X hy la]
  set s := X.zN Z with hs
  have hs0 : 0 ≤ s := by
    rw [hs]
    unfold Data.zN
    exact Real.iSup_nonneg fun τ => opN_nonneg _
  have hu : s ^ 2 ≤ 1 / 100 := by nlinarith
  have hq : s ^ 2 / (1 - s ^ 2) ≤ 2 * s ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith

  have hτ : ∀ τ : X.Ψ, |∑ k : Fin r, (la τ k : ℝ) * Real.log ‖dOf X (X.xZ x Z) τ k‖| ≤
      X.spread la τ * (4 * r * s ^ 2) := by
    intro τ
    refine (spread_bound _ _ (sum_log_dOf X hx ho hZ1 τ)).trans ?_
    have hsp := spread_nonneg X la τ
    refine mul_le_mul_of_nonneg_left ?_ hsp

    have hsplit : ∑ k : Fin r, |Real.log ‖dOf X (X.xZ x Z) τ k‖| =
        ∑ k : Fin r, (if (k : ℕ) < X.p0 then -2 * Real.log ‖dOf X (X.xZ x Z) τ k‖ else 0) +
          ∑ k : Fin r, Real.log ‖dOf X (X.xZ x Z) τ k‖ := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : (k : ℕ) < X.p0
      · rw [if_pos hk, abs_of_nonpos (log_dOf_pos_bound X hx ho hZ1 τ k hk).1]
        ring
      · rw [if_neg hk, abs_of_nonneg (log_dOf_neg X hx ho hZ1 τ k (not_lt.1 hk)), zero_add]
    rw [hsplit, sum_log_dOf X hx ho hZ1 τ, add_zero]
    calc ∑ k : Fin r, (if (k : ℕ) < X.p0 then -2 * Real.log ‖dOf X (X.xZ x Z) τ k‖ else 0)
        ≤ ∑ _k : Fin r, 2 * (2 * s ^ 2) := Finset.sum_le_sum fun k _ => by
          by_cases hk : (k : ℕ) < X.p0
          · rw [if_pos hk]
            have := (log_dOf_pos_bound X hx ho hZ1 τ k hk).2
            nlinarith
          · rw [if_neg hk]; positivity
      _ = 4 * r * s ^ 2 := by simp [Finset.card_univ]; ring
  have hsum : |∑ τ, ∑ k : Fin r, (-(la τ k : ℝ) / 2) * Real.log ‖dOf X (X.xZ x Z) τ k‖| ≤
      ∑ τ, X.spread la τ * (4 * r * s ^ 2) / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    have e : ∑ k : Fin r, (-(la τ k : ℝ) / 2) * Real.log ‖dOf X (X.xZ x Z) τ k‖ =
        -(1 / 2) * ∑ k : Fin r, (la τ k : ℝ) * Real.log ‖dOf X (X.xZ x Z) τ k‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [hτ τ]
  refine hsum.trans ?_
  rw [← Finset.sum_div, ← Finset.sum_mul]
  have hw0 : (0 : ℝ) ≤ 4 * r * s ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hw hw0
  have hw1 : 0 ≤ w := le_trans (Finset.sum_nonneg fun τ _ => spread_nonneg X la τ) hw
  have hw2 : 0 ≤ w * (4 * r * s ^ 2) := mul_nonneg hw1 hw0
  nlinarith

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer TwoSidedBoostBounds
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace MinimumGrowthBounds

variable {r : ℕ} (X : Data E r)

theorem minimumSq_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) : 0 ≤ X.firstMinimumSq x := by
  apply Real.sInf_nonneg
  rintro t ⟨v, _, _, rfl⟩
  exact Finset.sum_nonneg fun τ _ =>
    mul_nonneg (TwoSidedBoostBounds.c_pos (X := X) τ).le (MajorantConjugateTransfer.maj_nonneg (X := X) hx τ _)

theorem minimumSq_two_sided_bounds {x y : Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) {k1 k2 : ℝ}
    (hk1 : 0 ≤ k1) (hk2 : 0 < k2) (hlow : ∀ τ w, k1 * X.maj x τ w ≤ X.maj y τ w)
    (hup : ∀ τ w, X.maj y τ w ≤ k2 * X.maj x τ w) :
    k1 * X.firstMinimumSq x ≤ X.firstMinimumSq y ∧ X.firstMinimumSq y ≤ k2 * X.firstMinimumSq x := by
  have hc : ∀ τ, 0 ≤ X.c τ := fun τ => (TwoSidedBoostBounds.c_pos (X := X) τ).le
  have e : ∀ g' : (Fin r → E) → ℝ, (¬ ∃ v ∈ X.Λ, v ≠ 0) → {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g' v} = ∅ := by
    intro g' hne
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨v, hv, hv', _⟩
    exact hne ⟨v, hv, hv'⟩
  have key1 : ∀ (g h : (Fin r → E) → ℝ) (a : ℝ), 0 ≤ a → (∀ v, 0 ≤ g v) → (∀ v, a * g v ≤ h v) →
      a * sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} ≤ sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = h v} := by
    intro g h a ha hg hgh
    by_cases hne : ∃ v ∈ X.Λ, v ≠ 0
    · obtain ⟨v0, hv0, hv0'⟩ := hne
      refine le_csInf ⟨_, v0, hv0, hv0', rfl⟩ ?_
      rintro t ⟨v, hv, hv', rfl⟩
      have hb : BddBelow {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} := ⟨0, by
        rintro s ⟨w, _, _, rfl⟩
        exact hg w⟩
      exact (mul_le_mul_of_nonneg_left (csInf_le hb ⟨v, hv, hv', rfl⟩) ha).trans (hgh v)
    · rw [e g hne, e h hne, Real.sInf_empty, mul_zero]
  have key2 : ∀ (g h : (Fin r → E) → ℝ) (a : ℝ), 0 < a → (∀ v, 0 ≤ g v) → (∀ v, g v ≤ a * h v) →
      sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} ≤ a * sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = h v} := by
    intro g h a ha hg hgh
    by_cases hne : ∃ v ∈ X.Λ, v ≠ 0
    · obtain ⟨v0, hv0, hv0'⟩ := hne
      rw [← div_le_iff₀' ha]
      refine le_csInf ⟨_, v0, hv0, hv0', rfl⟩ ?_
      rintro t ⟨v, hv, hv', rfl⟩
      rw [div_le_iff₀' ha]
      have hb : BddBelow {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} := ⟨0, by
        rintro s ⟨w, _, _, rfl⟩
        exact hg w⟩
      exact (csInf_le hb ⟨v, hv, hv', rfl⟩).trans (hgh v)
    · rw [e g hne, e h hne, Real.sInf_empty, mul_zero]
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
  refine ⟨key1 _ _ k1 hk1 ?_ ?_, key2 _ _ k2 hk2 ?_ ?_⟩
  · intro v
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ) (MajorantConjugateTransfer.maj_nonneg (X := X) hx τ _)
  · intro v
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ =>
      (mul_left_comm _ _ _).trans_le (mul_le_mul_of_nonneg_left (hlow τ _) (hc τ))
  · intro v
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ) (MajorantConjugateTransfer.maj_nonneg (X := X) hy τ _)
  · intro v
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ =>
      (mul_le_mul_of_nonneg_left (hup τ _) (hc τ)).trans_eq (mul_left_comm _ _ _)

theorem sqrt_rpow_le (A : ℝ) {k1 k2 L Ly : ℝ} (hk1 : 0 < k1) (hk12 : k1 ≤ k2) (hL : 0 ≤ L)
    (h1 : k1 * L ≤ Ly) (h2 : Ly ≤ k2 * L) :
    Real.sqrt Ly ^ (-A) ≤ max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * Real.sqrt L ^ (-A) := by
  rcases hL.eq_or_lt with hL0 | hLpos
  · subst hL0
    have hLy : Ly = 0 := le_antisymm (by linarith) (by linarith)
    subst hLy
    simp only [Real.sqrt_zero]
    by_cases hA : A = 0
    · subst hA
      simp
    · rw [Real.zero_rpow (neg_ne_zero.mpr hA), mul_zero]
  · have hs : ∀ z : ℝ, 0 ≤ z → Real.sqrt z ^ (-A) = z ^ (-A / 2) := by
      intro z hz
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz]
      congr 1
      ring
    have hLy : 0 < Ly := lt_of_lt_of_le (mul_pos hk1 hLpos) h1
    rw [hs Ly hLy.le, hs L hL]
    have hLy_eq : Ly = Ly / L * L := (div_mul_cancel₀ Ly hLpos.ne').symm
    have hs1 : k1 ≤ Ly / L := by
      rw [le_div_iff₀ hLpos]
      exact h1
    have hs2 : Ly / L ≤ k2 := by
      rw [div_le_iff₀ hLpos]
      exact h2
    have hspos : 0 < Ly / L := lt_of_lt_of_le hk1 hs1
    rw [hLy_eq, Real.mul_rpow hspos.le hL]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL _)
    rcases le_total 0 (-A / 2) with hp | hp
    · exact (Real.rpow_le_rpow hspos.le hs2 hp).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hk1 hs1 hp).trans (le_max_left _ _)

theorem nfac_pos (la : Wt X.Ψ r) {y : Frame X.Ψ r} (hy : y ∈ X.dom) : 0 < X.nfac la y := by
  have hd : ∀ τ i, dmin X.Gm y τ i ≠ 0 := by
    intro τ i h0
    have h1 := (hy τ).2 i
    rw [h0] at h1
    simp at h1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _

theorem growth (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ)
    (hmod : ∀ z ∈ X.dom, X.pnorm la P z ≤ C * X.la1 z ^ (-A)) {x y : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hy : y ∈ X.dom) {k1 k2 : ℝ} (hk1 : 0 < k1) (hk12 : k1 ≤ k2)
    (hlow : ∀ τ w, k1 * X.maj x τ w ≤ X.maj y τ w) (hup : ∀ τ w, X.maj y τ w ≤ k2 * X.maj x τ w)
    {R : ℝ} (hR : X.nfac la x / X.nfac la y ≤ R) :
    ‖P y‖ * X.nfac la x ≤ max C 0 * max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * R * X.la1 x ^ (-A) := by
  have hny := nfac_pos X la hy
  have hnx := nfac_pos X la hx
  obtain ⟨b1, b2⟩ := minimumSq_two_sided_bounds X hx hy hk1.le (lt_of_lt_of_le hk1 hk12) hlow hup
  have hla : X.la1 y ^ (-A) ≤ max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * X.la1 x ^ (-A) :=
    sqrt_rpow_le A hk1 hk12 (minimumSq_nonneg X hx) b1 b2
  have hq0 : 0 ≤ X.nfac la x / X.nfac la y := div_nonneg hnx.le hny.le
  have hR0 : 0 ≤ R := le_trans hq0 hR
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hly : 0 ≤ X.la1 y ^ (-A) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hPy : ‖P y‖ * X.nfac la y ≤ max C 0 * X.la1 y ^ (-A) :=
    calc ‖P y‖ * X.nfac la y = X.pnorm la P y := rfl
      _ ≤ C * X.la1 y ^ (-A) := hmod y hy
      _ ≤ max C 0 * X.la1 y ^ (-A) := mul_le_mul_of_nonneg_right (le_max_left _ _) hly
  have hny' := hny.ne'
  calc ‖P y‖ * X.nfac la x = (‖P y‖ * X.nfac la y) * (X.nfac la x / X.nfac la y) := by
        field_simp
    _ ≤ (max C 0 * X.la1 y ^ (-A)) * R := mul_le_mul hPy hR hq0 (mul_nonneg hC0 hly)
    _ ≤ (max C 0 * (max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * X.la1 x ^ (-A))) * R := by gcongr
    _ = max C 0 * max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * R * X.la1 x ^ (-A) := by ring

end MinimumGrowthBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorBound
section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem shortVectorBound : ShortVectorBound (E := E) :=
  shortVectorBound_of_coefficient_bounds fourier_coefficients_holds cusp_coefficient_quantitative_holds flowCoefficientDecay coefficientIndex_lowerBound coefficientHeight_bound counting_exponential_sum_holds isotropic_outside_line

end ReciprocityTheory.ChartRestriction.G.FD
end

