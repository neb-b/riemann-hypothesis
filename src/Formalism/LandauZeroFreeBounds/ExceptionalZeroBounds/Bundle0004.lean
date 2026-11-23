module

public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf

@[expose] public section

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealSmallTOf
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hρ
  have hz : ((σ : ℂ) - ρ).re = σ - ρ.re := by simp
  have hpos : 0 < ((σ : ℂ) - ρ).re := by rw [hz]; linarith
  have hne : ((σ : ℂ) - ρ) ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  rw [one_div, Complex.inv_re]
  exact div_pos hpos (Complex.normSq_pos.mpr hne)

lemma re_one_div_ofReal_sub (σ : ℝ) (ρ : ℂ) :
    (1 / ((σ : ℂ) - ρ)).re = (σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma mul_le_div_sq_add_sq (T X G : ℝ) (hT : 0 < T) (h1 : 1 ≤ T * X) (h2 : T * X ≤ 11 / 10)
    (h3 : |T * G| ≤ 1 / 10) : 4 / 5 * T ≤ X / (X ^ 2 + G ^ 2) := by
  have hX : 0 < X := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hv : (T * G) ^ 2 ≤ 1 / 100 := by
    have := sq_abs (T * G)
    nlinarith [abs_nonneg (T * G)]
  have key : T * (4 / 5 * T * (X ^ 2 + G ^ 2)) ≤ T * X := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ T * X) (by linarith : 0 ≤ 11 / 10 - T * X)]
  have := le_of_mul_le_mul_left key hT
  rw [le_div_iff₀ (add_pos_of_pos_of_nonneg (pow_pos hX 2) (sq_nonneg G))]
  exact this

theorem realCharZeroSmallHeightOfBounds : RealSmallTOf := by
  intro hLZ hLD hPos hConj
  obtain ⟨C, hC⟩ := hLZ
  obtain ⟨C₀, hC₀, hLD⟩ := hLD
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hCCp : C ≤ Cp := le_max_left _ _
  set K : ℝ := 2 * C₀ + Cp with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  set W : ℝ := 10 * (K + 1) with hW
  have hW10 : 10 ≤ W := by rw [hW]; linarith
  have hWpos : 0 < W := by linarith
  refine ⟨1 / (10 * W), 1 / (10 * W), by positivity, by positivity, ?_⟩
  intro q _ χ hχ2 hχ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)

  obtain ⟨Z, m, hZ, hm1, hm2, hb⟩ := hC q χ hχ 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hZ hb
  set L₀ := Real.log ((q : ℝ) * 2) with hL₀
  have hlog2 := Real.log_two_gt_d9
  have hL₀2 : Real.log 2 ≤ L₀ := Real.log_le_log (by norm_num) (by nlinarith)
  have hL₀h : 1 / 2 < L₀ := by norm_num at hlog2; linarith
  have hL₀pos : 0 < L₀ := by linarith
  set T : ℝ := W * L₀ with hT
  have hTpos : 0 < T := mul_pos hWpos hL₀pos
  have hT5 : 5 ≤ T := by rw [hT]; nlinarith
  have hTe : T = 10 * (K * L₀) + 10 * L₀ := by rw [hT, hW]; ring
  have hKL : K * L₀ = 2 * (C₀ * L₀) + Cp * L₀ := by rw [hK]; ring
  set σ : ℝ := 1 + 1 / T with hσ
  have hσ1 : 1 < σ := by
    have : 0 < 1 / T := by positivity
    linarith
  have hσ2 : σ ≤ 6 / 5 := by
    have : 1 / T ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hT5
    linarith

  have hF1 : ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤ (11 * K + 10) * L₀ := by
    have hP := (hPos q σ hσ1).2.1 χ hχ2
    have h0 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ T + C₀ := by
      have h := hLD q 1 (σ : ℂ) (by simpa using hσ1)
      have e : 1 / ((σ : ℂ).re - 1) = T := by
        rw [Complex.ofReal_re, hσ, add_sub_cancel_left, one_div_one_div]
      rw [e] at h
      exact (Complex.re_le_norm _).trans h
    have h1 := hb σ hσ1 hσ2
    have h2 : C * L₀ ≤ Cp * L₀ := mul_le_mul_of_nonneg_right hCCp hL₀pos.le
    have h3 : C₀ ≤ 2 * (C₀ * L₀) := by nlinarith
    have h4 : (11 * K + 10) * L₀ = 11 * (K * L₀) + 10 * L₀ := by ring
    rw [h4]
    linarith

  have hnn : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re := fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos' χ hχ ρ ((hZ ρ).mp hρ).2 σ hσ1).le

  have hcons : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
      InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 →
      ρ ∈ Z ∧ 4 / 5 * T ≤ (1 / ((σ : ℂ) - ρ)).re := by
    intro ρ hi hr hz
    unfold InRegion at hr
    obtain ⟨Lρ, hLρdef⟩ : ∃ x : ℝ, x = Real.log ((q : ℝ) * (|ρ.im| + 2)) := ⟨_, rfl⟩
    rw [← hLρdef] at hi hr
    have hLρ : L₀ ≤ Lρ := by
      rw [hLρdef, hL₀]
      exact Real.log_le_log (by positivity) (by nlinarith [abs_nonneg ρ.im])
    have hdiv : 1 / (10 * W) / Lρ ≤ 1 / (10 * T) := by
      have := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1 / (10 * W)) hL₀pos hLρ
      have e : 1 / (10 * W) / L₀ = 1 / (10 * T) := by rw [hT, div_div, mul_assoc]
      linarith
    have hβ1 : ρ.re < 1 := by
      by_contra h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hz
    have hβ : 1 - 1 / (10 * T) ≤ ρ.re := by linarith
    have hγ : |ρ.im| ≤ 1 / (10 * T) := by linarith
    have hsmall : 1 / (10 * T) ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hTT : T * (1 / (10 * T)) = 1 / 10 := by field_simp
    refine ⟨(hZ ρ).mpr ⟨?_, hz⟩, ?_⟩
    · rw [Metric.mem_closedBall, Complex.dist_eq]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e0 : (11 / 10 : ℂ) = ((11 / 10 : ℝ) : ℂ) := by push_cast; rfl
      rw [e0, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      have : |ρ.re - 11 / 10| ≤ 1 / 10 + 1 / (10 * T) := by
        rw [abs_le]; constructor <;> linarith
      linarith
    · rw [re_one_div_ofReal_sub]
      have hTσ : T * (σ - ρ.re) = T * (1 - ρ.re) + 1 := by
        rw [hσ]; field_simp; ring
      have hA : 0 < T * (1 - ρ.re) := mul_pos hTpos (by linarith)
      have hB : T * (1 - ρ.re) ≤ T * (1 / (10 * T)) :=
        mul_le_mul_of_nonneg_left (by linarith) hTpos.le
      apply mul_le_div_sq_add_sq T (σ - ρ.re) ρ.im hTpos
      · rw [hTσ]; linarith
      · rw [hTσ]; linarith
      · rw [abs_mul, abs_of_pos hTpos]
        have := mul_le_mul_of_nonneg_left hγ hTpos.le
        linarith
  have hbig : (11 * K + 10) * L₀ < 8 / 5 * T := by
    have : 0 ≤ K * L₀ := mul_nonneg hK0 hL₀pos.le
    nlinarith

  have htwo : ∀ ρ₁ ρ₂ : ℂ,
      (|ρ₁.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₁.im| + 2)) ∧
        InRegion (1 / (10 * W)) q ρ₁ ∧ DirichletCharacter.LFunction χ ρ₁ = 0) →
      (|ρ₂.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₂.im| + 2)) ∧
        InRegion (1 / (10 * W)) q ρ₂ ∧ DirichletCharacter.LFunction χ ρ₂ = 0) →
      ρ₁ ≠ ρ₂ → False := by
    rintro ρ₁ ρ₂ ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ hne
    obtain ⟨h1Z, h1r⟩ := hcons ρ₁ a1 b1 c1
    obtain ⟨h2Z, h2r⟩ := hcons ρ₂ a2 b2 c2
    have hsub : ({ρ₁, ρ₂} : Finset ℂ) ⊆ Z := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1Z
      · exact h2Z
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ _ => hnn ρ hρ)
    rw [Finset.sum_pair hne] at hs
    have hm1' : (1 : ℝ) ≤ m ρ₁ := by exact_mod_cast hm1 ρ₁ h1Z
    have hm2' : (1 : ℝ) ≤ m ρ₂ := by exact_mod_cast hm1 ρ₂ h2Z
    have hr1 : 0 ≤ (1 / ((σ : ℂ) - ρ₁)).re := by linarith
    have hr2 : 0 ≤ (1 / ((σ : ℂ) - ρ₂)).re := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1') hr1, mul_nonneg (sub_nonneg.mpr hm2') hr2]

  have hdouble : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
      InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 →
      deriv (DirichletCharacter.LFunction χ) ρ = 0 → False := by
    intro ρ a b c hd
    obtain ⟨hρZ, hρr⟩ := hcons ρ a b c
    have hs := Finset.single_le_sum hnn hρZ
    have hm : (2 : ℝ) ≤ m ρ := by exact_mod_cast hm2 ρ hρZ hd
    have hr : 0 ≤ (1 / ((σ : ℂ) - ρ)).re := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hr]
  intro s s' hs hs' hrs hrs' hz hz'
  have hsim : s.im = 0 := by
    by_contra hne
    refine htwo s (starRingEnd ℂ s) ⟨hs, hrs, hz⟩ ⟨?_, ?_, ?_⟩ ?_
    · simpa [Complex.conj_im, abs_neg] using hs
    · unfold InRegion at hrs ⊢
      simpa [Complex.conj_re, Complex.conj_im, abs_neg] using hrs
    · rw [hConj q χ hχ2 hχ s, hz, map_zero]
    · intro h
      apply hne
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
  refine ⟨hsim, fun hd => hdouble s hs hrs hz hd, ?_⟩
  by_contra hne
  exact htwo s' s ⟨hs', hrs', hz'⟩ ⟨hs, hrs, hz⟩ hne

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TwoRealOf
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos_bis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h) hρ
  have hw : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ).re = σ - ρ.re := by simp
  have hwpos : 0 < ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ).re := by rw [hw]; linarith
  rw [one_div, Complex.inv_re]
  apply div_pos hwpos
  rw [Complex.normSq_pos]
  intro h0
  rw [h0] at hwpos
  simp at hwpos

lemma sum_re_one_div_sub_zero_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : Finset ℂ)
    (m : ℂ → ℕ) (hZ : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
  apply Finset.sum_nonneg
  intro ρ hρ
  exact mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_bis χ hχ ρ (hZ ρ hρ) σ hσ).le

lemma re_negLogDeriv_le_of_real_zero (C : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔
        (ρ ∈ Metric.closedBall ((11 / 10 : ℂ) + ((0 : ℝ) : ℂ) * I) (1 / 5) ∧
          DirichletCharacter.LFunction χ ρ = 0))
    (hm1 : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (β σ : ℝ) (hσ : 1 < σ) (hβσ : β < σ) (hβ9 : 9 / 10 ≤ β) (hβ1 : β < 1)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hb : (negLD χ ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re ≤
      C * Real.log ((q : ℝ) * (|(0 : ℝ)| + 2)) -
        ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re) :
    (negLD χ (σ : ℂ)).re ≤ C * Real.log ((q : ℝ) * 2) - 1 / (σ - β) := by
  have hs0 : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) = (σ : ℂ) := by simp
  have hl : (negLD χ ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re = (negLD χ (σ : ℂ)).re := by
    rw [hs0]
  have h02 : |(0 : ℝ)| + 2 = 2 := by norm_num
  rw [h02] at hb
  have hβZ : (β : ℂ) ∈ Z := by
    rw [hZ]
    refine ⟨?_, hzero⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h' : (β : ℂ) - ((11 / 10 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((β - 11 / 10 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h', Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hterm : (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))).re = 1 / (σ - β) := by
    have h' : (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))) = ((1 / (σ - β) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h', Complex.ofReal_re]
  have hrest : 0 ≤ ∑ ρ ∈ Z.erase (β : ℂ), (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρZ := ((hZ ρ).1 (Finset.mem_of_mem_erase hρ)).2
    exact mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_bis χ hχ ρ hρZ σ hσ).le
  have hsplit : (m (β : ℂ) : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))).re +
      ∑ ρ ∈ Z.erase (β : ℂ), (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re =
      ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re :=
    Finset.add_sum_erase Z (fun ρ => (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re) hβZ
  rw [hterm] at hsplit
  have hpos : 0 < 1 / (σ - β) := one_div_pos.mpr (sub_pos.mpr hβσ)
  have hm : (1 : ℝ) ≤ (m (β : ℂ) : ℝ) := by exact_mod_cast hm1 _ hβZ
  have hbig : 1 / (σ - β) ≤ (m (β : ℂ) : ℝ) * (1 / (σ - β)) := by nlinarith
  linarith

theorem twoRealCharNoCommonZeroOfBounds : TwoRealOf := by
  intro hZS hLD hPos
  obtain ⟨C, hC⟩ := hZS
  obtain ⟨C', hC'0, hC'⟩ := hLD
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 3 * |C| + 2 * C' + 1 := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by have := abs_nonneg C; linarith
  have hA0 : 0 < A := by linarith
  refine ⟨1 / (20 * A), one_div_pos.mpr (mul_pos (by norm_num) hA0), ?_⟩
  intro q hq0 χ₁ χ₂ h₁ h₂ h₁1 h₂1 h12 β₁ β₂ hr₁ hr₂
  by_contra hcon
  obtain ⟨hz₁', hz₂'⟩ := not_or.mp hcon
  have hz₁ := not_not.mp hz₁'
  have hz₂ := not_not.mp hz₂'
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * 2) := ⟨_, rfl⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL2 : Real.log 2 ≤ L := by
    rw [hL]; exact Real.log_le_log (by norm_num) (by linarith)
  have hLhalf : 1 / 2 < L := by have := Real.log_two_gt_d9; linarith
  have hL0 : 0 < L := by linarith
  have hAL0 : 0 < 20 * A * L := mul_pos (mul_pos (by norm_num) hA0) hL0
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 1 / (20 * A * L) := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; exact one_div_pos.mpr hAL0
  have hE : 20 * A * L * e = 1 := by rw [he]; exact mul_one_div_cancel hAL0.ne'
  have hAL : A * L = 3 * |C| * L + 2 * C' * L + L := by rw [hA]; ring
  have hAL10 : 10 ≤ 20 * A * L := by nlinarith
  have he10 : e ≤ 1 / 10 := by
    have := mul_le_mul_of_nonneg_left hAL10 he0.le
    linarith
  have hreg : ∀ β : ℝ, InRegion (1 / (20 * A)) q (β : ℂ) → 1 - e ≤ β := by
    intro β hr
    simp only [InRegion, Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add] at hr
    have : 1 / (20 * A) / Real.log ((q : ℝ) * 2) = e := by rw [he, hL, div_div]
    linarith
  have hσ : (1 : ℝ) < 1 + 2 * e := by linarith
  have hσ6 : 1 + 2 * e ≤ 6 / 5 := by linarith
  have hβlt : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β < 1 := by
    intro χ hχ β hz
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using not_lt.mp h) hz
  have hbound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      InRegion (1 / (20 * A)) q (β : ℂ) → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      (negLD χ ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L - 20 * A * L / 3 := by
    intro χ hχ β hr hz
    have hb1 := hβlt χ hχ β hz
    have hb0 := hreg β hr
    obtain ⟨Z, m, hZ, hm, -, hb⟩ := hC q χ hχ 0
    have key := re_negLogDeriv_le_of_real_zero C χ hχ Z m hZ hm β (1 + 2 * e) hσ
      (by linarith) (by linarith) hb1 hz (hb (1 + 2 * e) hσ hσ6)
    rw [← hL] at key
    have h3 : 1 / (3 * e) = 20 * A * L / 3 := by
      rw [div_eq_iff (mul_pos (by norm_num) he0).ne']
      linear_combination -hE
    have hinv : 1 / (3 * e) ≤ 1 / (1 + 2 * e - β) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have h0b : (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ)).re ≤ 10 * A * L + C' := by
    have h := hC' q 1 ((1 + 2 * e : ℝ) : ℂ) (by rw [Complex.ofReal_re]; exact hσ)
    rw [Complex.ofReal_re] at h
    have h2 : 1 / (1 + 2 * e - 1) = 10 * A * L := by
      rw [div_eq_iff (show (0 : ℝ) < 1 + 2 * e - 1 by linarith).ne']
      linear_combination -hE
    rw [h2] at h
    have := Complex.re_le_norm (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ))
    linarith
  have h12ne : χ₁ * χ₂ ≠ 1 := by
    intro h
    apply h12
    calc χ₁ = χ₁ * χ₂ ^ 2 := by rw [h₂, mul_one]
      _ = χ₁ * χ₂ * χ₂ := by rw [pow_two, mul_assoc]
      _ = χ₂ := by rw [h, one_mul]
  have h12b : (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L := by
    obtain ⟨Z, m, hZ, -, -, hb⟩ := hC q (χ₁ * χ₂) h12ne 0
    have hb' := hb (1 + 2 * e) hσ hσ6
    have hs := sum_re_one_div_sub_zero_nonneg (χ₁ * χ₂) h12ne Z m
      (fun ρ hρ => ((hZ ρ).1 hρ).2) (1 + 2 * e) hσ
    have hs0 : (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((1 + 2 * e : ℝ) : ℂ) := by simp
    have hl : (negLD (χ₁ * χ₂) (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)).re =
        (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re := by rw [hs0]
    have h02 : |(0 : ℝ)| + 2 = 2 := by norm_num
    rw [h02, ← hL] at hb'
    linarith
  have hpos := (hPos q (1 + 2 * e) hσ).2.2 χ₁ χ₂ h₁ h₂
  have k1 := hbound χ₁ h₁1 β₁ hr₁ hz₁
  have k2 := hbound χ₂ h₂1 β₂ hr₂ hz₂
  have hCL : C * L ≤ |C| * L := mul_le_mul_of_nonneg_right (le_abs_self C) hL0.le
  have hC'L : C' * (1 / 2) ≤ C' * L := mul_le_mul_of_nonneg_left hLhalf.le hC'0
  have hCL0 : 0 ≤ |C| * L := mul_nonneg (abs_nonneg C) hL0.le
  have hC'L0 : 0 ≤ C' * L := mul_nonneg hC'0 hL0.le
  linarith

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZFRDirichletOf
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma one_le_natCast (q : ℕ) [NeZero q] : (1 : ℝ) ≤ q := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)

lemma log_two_le_log_mul_abs_add_two (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq := one_le_natCast q
  apply Real.log_le_log (by norm_num)
  nlinarith [abs_nonneg t]

lemma log_mul_abs_add_two_pos (q : ℕ) [NeZero q] (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_log_mul_abs_add_two q t)

lemma inRegion_mono' {c c' : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (h : c ≤ c') (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at *
  have hL := log_mul_abs_add_two_pos q s.im
  have := div_le_div_of_nonneg_right h hL.le
  linarith

lemma re_pos_of_inRegion {c : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hc : c ≤ 1 / 2) (hs : InRegion c q s) :
    0 < s.re := by
  unfold InRegion at hs
  have hL := log_two_le_log_mul_abs_add_two q s.im
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := div_le_div_of_nonneg_right hc hLpos.le
  have h2 : (1 / 2 : ℝ) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ (1 / 2) / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) h2pos hL
  have h3 : (1 / 2 : ℝ) / Real.log 2 < 1 := by
    rw [div_lt_one h2pos]; linarith [Real.log_two_gt_d9]
  linarith

lemma one_sub_div_log_le_re {c cz : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hcz : 0 < cz) (h : c ≤ cz)
    (hs : InRegion c q s) : 1 - cz / Real.log (|s.im| + 2) ≤ s.re := by
  unfold InRegion at hs
  have hq := one_le_natCast q
  have hT : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hlogT : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith)
  have hle : Real.log (|s.im| + 2) ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h1 := div_le_div_of_nonneg_right h hLpos.le
  have h2 := div_le_div_of_nonneg_left hcz.le hlogT hle
  linarith

theorem zeroFreeRegionExceptionalZeroOfBounds : ZFRDirichletOf := by
  intro hZ hT hN hL hS h2
  obtain ⟨cz, hcz, hZ⟩ := hZ
  obtain ⟨cN, hcN, hN⟩ := hN
  obtain ⟨δ, cS, hδ, hcS, hS⟩ := hS
  obtain ⟨cL, hcL, hL⟩ := hL δ hδ
  obtain ⟨c2, hc2, h2⟩ := h2
  set c := min (min (min cz cN) (min cL cS)) (min c2 (1 / 2)) with hc
  have hc0 : 0 < c := lt_min (lt_min (lt_min hcz hcN) (lt_min hcL hcS)) (lt_min hc2 (by norm_num))
  have hccz : c ≤ cz := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hccN : c ≤ cN := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hccL : c ≤ cL := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hccS : c ≤ cS := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcc2 : c ≤ c2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc12 : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc0, ?_⟩
  intro q _ χ s hs hz

  have key : ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), InRegion c q s → IsLZero χ s →
      χ ^ 2 = 1 ∧ χ ≠ 1 ∧ |s.im| < δ / Real.log ((q : ℝ) * (|s.im| + 2)) := by
    intro χ s hs hz
    obtain ⟨hne, h0⟩ := hz
    have hχ1 : χ ≠ 1 := by
      rintro rfl
      have hs1 : s ≠ 1 := hne.resolve_left (fun h => h rfl)
      have hre := re_pos_of_inRegion hc12 hs
      exact hZ s hs1 (one_sub_div_log_le_re hcz hccz hs) (hT q s hre hs1 h0)
    have hsq : χ ^ 2 = 1 := by
      by_contra hsq
      exact hN q χ s hsq (inRegion_mono' hccN hs) h0
    refine ⟨hsq, hχ1, ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hL q χ s hsq hχ1 hlt (inRegion_mono' hccL hs) h0
  obtain ⟨hsq, hχ1, hsm⟩ := key χ s hs hz
  obtain ⟨him, hder, -⟩ := hS q χ hsq hχ1 s s hsm hsm (inRegion_mono' hccS hs)
    (inRegion_mono' hccS hs) hz.2 hz.2
  refine ⟨hsq, hχ1, him, hder, ?_⟩
  intro χ' s' hs' hz'
  obtain ⟨hsq', hχ1', hsm'⟩ := key χ' s' hs' hz'
  have him' := (hS q χ' hsq' hχ1' s' s' hsm' hsm' (inRegion_mono' hccS hs')
    (inRegion_mono' hccS hs') hz'.2 hz'.2).1
  have hχeq : χ' = χ := by
    by_contra hne
    have es : ((s.re : ℝ) : ℂ) = s := Complex.ext (by simp) (by simp [him])
    have es' : ((s'.re : ℝ) : ℂ) = s' := Complex.ext (by simp) (by simp [him'])
    have r1 : InRegion c2 q ((s.re : ℝ) : ℂ) := by rw [es]; exact inRegion_mono' hcc2 hs
    have r2 : InRegion c2 q ((s'.re : ℝ) : ℂ) := by rw [es']; exact inRegion_mono' hcc2 hs'
    rcases h2 q χ χ' hsq hsq' hχ1 hχ1' (Ne.symm hne) s.re s'.re r1 r2 with h | h
    · exact h (by rw [es]; exact hz.2)
    · exact h (by rw [es']; exact hz'.2)
  refine ⟨hχeq, ?_⟩
  rw [hχeq] at hz'
  exact (hS q χ hsq hχ1 s s' hsm hsm' (inRegion_mono' hccS hs) (inRegion_mono' hccS hs')
    hz.2 hz'.2).2.2

end Formalism.ZeroFreeDirichlet
end
end

