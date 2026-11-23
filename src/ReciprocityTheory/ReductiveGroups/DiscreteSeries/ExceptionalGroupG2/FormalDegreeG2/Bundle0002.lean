module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0011
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdStep
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdS_strictAnti {lam : Fin n → ℝ} (hlam : StrictAnti lam) {c : Fin n → ℕ} (hc : Antitone c) :
    StrictAnti (lam + fun i => (c i : ℝ)) := by
  intro i j hij
  have h1 := hlam hij
  have h2 : (c j : ℝ) ≤ c i := by exact_mod_cast hc hij.le
  simp only [Pi.add_apply]
  linarith

theorem fdS_hc {lam : Fin n → ℝ} (hlam : IsHCParam lam) {c : Fin n → ℕ} (hc : Antitone c) :
    IsHCParam (lam + fun i => (c i : ℝ)) := by
  obtain ⟨h1, h2⟩ := hlam
  refine ⟨fdS_strictAnti h1 hc, fun a => ?_⟩
  obtain ⟨m, hm⟩ := h2 a
  refine ⟨m + (c a : ℤ), ?_⟩
  simp only [Pi.add_apply]
  push_cast
  linarith

theorem fdS_gap {ε : Fin n → Bool} {h : ℝ} {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) {c : Fin n → ℕ} (hc : Antitone c) :
    GapAtLeast ε (lam + fun i => (c i : ℝ)) h := by
  intro a b hab
  have hg := hgap a b hab
  rcases lt_trichotomy a b with h | h | h
  · have h1 := hlam h
    have h2 : (c b : ℝ) ≤ c a := by exact_mod_cast hc h.le
    simp only [Pi.add_apply]
    rw [abs_of_pos (by linarith)] at *
    linarith
  · exact absurd (h ▸ rfl) hab
  · have h1 := hlam h
    have h2 : (c a : ℝ) ≤ c b := by exact_mod_cast hc h.le
    simp only [Pi.add_apply]
    rw [abs_of_neg (by linarith)] at *
    linarith

theorem fdS_stepQ {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {μ : Fin n → ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (s : Fin n)
    (hg' : GapAtLeast ε (μ + Pi.single s 1) h) (hs : StrictAnti (μ + Pi.single s 1)) :
    dfun (μ + Pi.single s 1) / Vand (μ + Pi.single s 1) = dfun μ / Vand μ := by
  have hμs : StrictAnti μ := hμ.1
  rw [hstep μ s hμ hg hg' hs, ratioV_eq_vand hμs s]
  have h1 := vand_pos hμs
  have h2 := vand_pos hs
  field_simp

theorem fdS_main {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) :
    ∀ (N : ℕ) (c : Fin n → ℕ), Antitone c → ∑ i, c i = N →
      dfun (lam + fun i => (c i : ℝ)) / Vand (lam + fun i => (c i : ℝ)) = dfun lam / Vand lam := by
  intro N
  induction N with
  | zero =>
    intro c hc hsum
    have h0 : ∀ i, c i = 0 := fun i => Finset.sum_eq_zero_iff.mp hsum i (Finset.mem_univ i)
    have hl : (lam + fun i => (c i : ℝ)) = lam := by
      funext i
      simp [h0 i]
    rw [hl]
  | succ N ih =>
    intro c hc hsum
    have hne : (univ.filter (fun i => c i ≠ 0)).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
      have : ∑ i, c i = 0 := Finset.sum_eq_zero (fun i _ => by simpa using hcon (Finset.mem_univ i))
      omega
    obtain ⟨s, hs, hafter⟩ : ∃ s, c s ≠ 0 ∧ ∀ j, s < j → c j = 0 := by
      refine ⟨(univ.filter (fun i => c i ≠ 0)).max' hne, ?_, ?_⟩
      · have := Finset.max'_mem _ hne
        simp only [Finset.mem_filter] at this
        exact this.2
      · intro j hj
        by_contra hcj
        exact absurd (Finset.le_max' _ j (by simp [hcj])) (not_le.mpr hj)
    let c' : Fin n → ℕ := fun i => if i = s then c i - 1 else c i
    have hc' : Antitone c' := by
      intro i j hij
      simp only [c']
      have hcij := hc hij
      by_cases hi : i = s <;> by_cases hj : j = s
      · rw [if_pos hj, if_pos hi]
        omega
      · rw [if_neg hj, if_pos hi]
        have hsj : s < j := lt_of_le_of_ne (by rw [← hi]; exact hij) (Ne.symm hj)
        rw [hafter j hsj]
        exact Nat.zero_le _
      · rw [if_pos hj, if_neg hi]
        omega
      · rw [if_neg hj, if_neg hi]
        exact hcij
    have hcs : c' s = c s - 1 := by simp [c']
    have hsum' : ∑ i, c' i = N := by
      have e1 := Finset.add_sum_erase univ c (Finset.mem_univ s)
      have e2 := Finset.add_sum_erase univ c' (Finset.mem_univ s)
      have e3 : ∑ x ∈ univ.erase s, c x = ∑ x ∈ univ.erase s, c' x :=
        Finset.sum_congr rfl (fun x hx => by simp [c', Finset.ne_of_mem_erase hx])
      rw [hcs] at e2
      omega
    have hih := ih c' hc' hsum'
    have heq : ((lam + fun i => (c' i : ℝ)) + Pi.single s 1) = lam + fun i => (c i : ℝ) := by
      funext i
      simp only [Pi.add_apply, Pi.single_apply, c']
      by_cases hi : i = s
      · rw [if_pos hi, if_pos hi]
        subst hi
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hs)]
        push_cast
        ring
      · rw [if_neg hi, if_neg hi]
        ring
    have hμ := fdS_hc hlam hc'
    have hg := fdS_gap hlam.1 hgap hc'
    have hg' : GapAtLeast ε ((lam + fun i => (c' i : ℝ)) + Pi.single s 1) h := by
      rw [heq]
      exact fdS_gap hlam.1 hgap hc
    have hsa : StrictAnti ((lam + fun i => (c' i : ℝ)) + Pi.single s 1) := by
      rw [heq]
      exact fdS_strictAnti hlam.1 hc
    have key := fdS_stepQ dfun hstep hμ hg s hg' hsa
    rw [heq] at key
    rw [key, hih]

theorem fd_step {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) (t : ℕ) :
    dfun (lamT lam t) / Vand (lamT lam t) = dfun lam / Vand lam := by
  have hn : ∀ i : Fin n, (i : ℕ) ≤ n - 1 := fun i => by
    have := i.isLt
    omega
  let c : Fin n → ℕ := fun i => t * (n - 1 - (i : ℕ))
  have hc : Antitone c := by
    intro i j hij
    simp only [c]
    have : (i : ℕ) ≤ j := hij
    exact Nat.mul_le_mul_left _ (by omega)
  have heq : lamT lam t = lam + fun i => (c i : ℝ) := by
    funext i
    simp only [lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, c]
    have h1 : 1 ≤ n := by
      have := i.isLt
      omega
    push_cast [Nat.cast_sub (hn i), Nat.cast_sub h1]
    ring
  rw [heq]
  exact fdS_main dfun hstep hlam hgap _ c hc rfl

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdUpperB
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdU_hs_smul {ε : Fin n → Bool} (s : ℝ) (y : PCoord ε → ℂ) :
    hs (pmat ((s : ℂ) • y)) = s ^ 2 * hs (pmat y) := by
  have hS : ∑ ab, ‖((s : ℂ) • y) ab‖ ^ 2 = s ^ 2 * ∑ ab, ‖y ab‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    simp [Pi.smul_apply, smul_eq_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hs_pmat, hs_pmat, hS]
  ring

theorem fdU_hs_nonneg {ε : Fin n → Bool} (y : PCoord ε → ℂ) : 0 ≤ hs (pmat y) := by
  rw [hs_pmat]; positivity

theorem fdU_sqrt_hs_smul {ε : Fin n → Bool} {s : ℝ} (hs0 : 0 ≤ s) (y : PCoord ε → ℂ) :
    Real.sqrt (hs (pmat ((s : ℂ) • y))) = s * Real.sqrt (hs (pmat y)) := by
  rw [fdU_hs_smul, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]

theorem fdU_qf_smul {ε : Fin n → Bool} (lam : Fin n → ℝ) (s : ℝ) (y : PCoord ε → ℂ) :
    Qf lam ((s : ℂ) • y) = s ^ 2 * Qf lam y := by
  unfold Qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  simp [Pi.smul_apply, smul_eq_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem fdU_antitone_zero : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl

theorem fdU_ph_ge {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (t : ℕ) (z : PCoord ε → ℂ) :
    (t : ℝ) * Ph (0 : Fin n → ℝ) (pmat z) ≤ Ph (lamT lam t) (pmat z) := by
  rw [ph_lamT]
  linarith [ph_nonneg hlam z]

theorem fdU_near {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) {s : ℝ} (hs0 : 0 < s) {t : ℕ}
    (hst : s ^ 2 * t = 1) (y : PCoord ε → ℂ) (hr : s * rhoP y ≤ 1) :
    Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y) ≤
      Real.exp (-(1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y +
        ((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) * (s * Real.sqrt (hs (pmat y)))) := by
  have hrho : rhoP ((s : ℂ) • y) = s * rhoP y := by rw [rhoP_real_smul, abs_of_pos hs0]
  have hl := ph_lower (lam := (0 : Fin n → ℝ)) fdU_antitone_zero ((s : ℂ) • y) (ep := s * rhoP y) hrho.le hr
  rw [fdU_qf_smul] at hl
  have hg := fdU_ph_ge hlam t ((s : ℂ) • y)
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hQ : (1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y =
      (t : ℝ) * ((1 - s * rhoP y) * (s ^ 2 * Qf (0 : Fin n → ℝ) y)) := by
    calc _ = (s ^ 2 * t) * ((1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y) := by rw [hst]; ring
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hl ht
  have h1 : (1 - s * rhoP y) * Qf (0 : Fin n → ℝ) y ≤ 2 * Ph (lamT lam t) (pmat ((s : ℂ) • y)) := by
    rw [hQ]; linarith
  have hJ := jac_le_exp ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le] at hJ
  rw [Real.exp_add]
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hJ (le_trans zero_le_one (jac_ge_one _))
    (Real.exp_pos _).le

theorem fdU_far {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) {t₀ t : ℕ} (h0 : 1 ≤ t₀)
    (ht : t₀ ≤ t) {s : ℝ} (hs0 : 0 < s) (hst : s ^ 2 * t = 1) (y : PCoord ε → ℂ) :
    Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y) ≤
      Real.exp ((Real.sqrt t₀ / Real.sqrt (2 * (q0 ε : ℝ))) ^ 2 / 32 -
        (Real.sqrt t₀ / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
          |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt t₀) * Real.sqrt (hs (pmat y))) := by
  have hhs : hs (pmat y) = Real.sqrt (hs (pmat y)) ^ 2 := (Real.sq_sqrt (fdU_hs_nonneg y)).symm
  have hm := potential_lower_min ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le, fdU_hs_smul] at hm
  have hJ := jac_le_exp ((s : ℂ) • y)
  rw [fdU_sqrt_hs_smul hs0.le] at hJ
  have hPh := fdU_ph_ge hlam t ((s : ℂ) • y)
  set k := Real.sqrt (2 * (q0 ε : ℝ)) with hk
  set r := Real.sqrt (hs (pmat y)) with hr
  set X := Real.sqrt (t₀ : ℝ) with hX
  set a := X / k with ha
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hT0 : 0 < X := Real.sqrt_pos.mpr (by exact_mod_cast h0)
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hsT : s * X ≤ 1 := by
    have h1 : s ^ 2 * t₀ ≤ 1 := by
      rw [← hst]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast ht) (sq_nonneg s)
    have h2 : (s * X) ^ 2 ≤ 1 := by rw [mul_pow, hX, Real.sq_sqrt (Nat.cast_nonneg _)]; exact h1
    nlinarith [mul_pos hs0 hT0]
  have hsinv : X ≤ s⁻¹ := by
    calc X = s⁻¹ * (s * X) := by field_simp
      _ ≤ s⁻¹ * 1 := mul_le_mul_of_nonneg_left hsT (inv_nonneg.mpr hs0.le)
      _ = s⁻¹ := mul_one _
  have hmin : a * r - a ^ 2 / 4 ≤ (t : ℝ) * min (s ^ 2 * hs (pmat y)) (s * r / k) := by
    rw [mul_min_of_nonneg _ _ ht0]
    refine le_min ?_ ?_
    · have e : (t : ℝ) * (s ^ 2 * hs (pmat y)) = r ^ 2 := by
        rw [hhs]; linear_combination r ^ 2 * hst
      rw [e]; nlinarith [sq_nonneg (r - a / 2)]
    · have hrk : 0 ≤ r / k := div_nonneg hr0 hk0
      have e : (t : ℝ) * (s * r / k) = s⁻¹ * (r / k) := by
        have : s⁻¹ = s * t := by field_simp; linear_combination -hst
        rw [this]; ring
      have ea : a * r = X * (r / k) := by rw [ha]; ring
      rw [e]; nlinarith [mul_le_mul_of_nonneg_right hsinv hrk, sq_nonneg a]
  have hs' : s ≤ 1 / X := by rw [le_div_iff₀ hT0]; exact hsT
  have hJ2 : ((n : ℝ) - 1) * k * (s * r) ≤ |(n : ℝ) - 1| * k / X * r := by
    calc ((n : ℝ) - 1) * k * (s * r) ≤ |(n : ℝ) - 1| * k * (s * r) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hk0) (by positivity)
      _ ≤ |(n : ℝ) - 1| * k * (1 / X * r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs' hr0) (by positivity)
      _ = _ := by ring
  have hm2 := mul_le_mul_of_nonneg_left hm ht0
  have hE : -2 * Ph (lamT lam t) (pmat ((s : ℂ) • y)) ≤ a ^ 2 / 32 - a / 8 * r := by
    nlinarith
  calc Real.exp (-2 * Ph (lamT lam t) (pmat ((s : ℂ) • y))) * Jac ((s : ℂ) • y)
      ≤ Real.exp (a ^ 2 / 32 - a / 8 * r) * Real.exp (|(n : ℝ) - 1| * k / X * r) :=
        mul_le_mul (Real.exp_le_exp.mpr hE) (hJ.trans (Real.exp_le_exp.mpr hJ2))
          (le_trans zero_le_one (jac_ge_one _)) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem one_le_q0_of_coord {ε : Fin n → Bool} (ab : PCoord ε) : 1 ≤ q0 ε := by
  have h : 0 < Fintype.card (PCoord ε) := Fintype.card_pos_iff.mpr ⟨ab⟩
  rw [card_PCoord] at h
  rcases Nat.eq_zero_or_pos (pOf ε) with hp | hp
  · simp [hp] at h
  rcases Nat.eq_zero_or_pos (qOf ε) with hq | hq
  · simp [hq] at h
  exact le_min hp hq

theorem fdU_c_pos {ε : Fin n → Bool} (ab : PCoord ε) :
    0 < Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) / Real.sqrt (2 * (q0 ε : ℝ)) / 8 -
      |(n : ℝ) - 1| * Real.sqrt (2 * (q0 ε : ℝ)) / Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) := by
  have hq : (1 : ℝ) ≤ q0 ε := by exact_mod_cast one_le_q0_of_coord ab
  have hn : (1 : ℝ) ≤ n := by
    have := ab.1.1.pos
    exact_mod_cast this
  set k := Real.sqrt (2 * (q0 ε : ℝ)) with hk
  set X := Real.sqrt ((16 * n * q0 ε + 1 : ℕ) : ℝ) with hX
  have hk0 : 0 < k := Real.sqrt_pos.mpr (by linarith)
  have hX0 : 0 < X := Real.sqrt_pos.mpr (by positivity)
  have hk2 : k ^ 2 = 2 * (q0 ε : ℝ) := Real.sq_sqrt (by linarith)
  have hX2 : X ^ 2 = ((16 * n * q0 ε + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have habs : |(n : ℝ) - 1| = (n : ℝ) - 1 := abs_of_nonneg (by linarith)
  have e : X / k / 8 - |(n : ℝ) - 1| * k / X = (X ^ 2 - 8 * ((n : ℝ) - 1) * k ^ 2) / (8 * k * X) := by
    rw [habs]; field_simp
  rw [e]
  apply div_pos _ (by positivity)
  rw [hX2, hk2]
  push_cast
  nlinarith

theorem fdU_exp_le_prod {ε : Fin n → Bool} {c : ℝ} (hc : 0 ≤ c) (y : PCoord ε → ℂ) :
    Real.exp (-c * Real.sqrt (hs (pmat y))) ≤
      ∏ ab : PCoord ε, Real.exp (-(c / ((Fintype.card (PCoord ε) : ℝ) + 1)) * ‖y ab‖) := by
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  set r := Real.sqrt (hs (pmat y)) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hle : ∀ ab, ‖y ab‖ ≤ r := by
    intro ab
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    rw [hs_pmat]
    have h1 := Finset.single_le_sum (f := fun ab => ‖y ab‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ ab)
    have h2 : 0 ≤ ∑ ab, ‖y ab‖ ^ 2 := by positivity
    linarith
  have hsum : ∑ ab, ‖y ab‖ ≤ (Fintype.card (PCoord ε) : ℝ) * r := by
    calc ∑ ab, ‖y ab‖ ≤ ∑ _ab : PCoord ε, r := Finset.sum_le_sum fun ab _ => hle ab
      _ = _ := by simp
  set N := (Fintype.card (PCoord ε) : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  have e : ∑ ab : PCoord ε, -(c / N) * ‖y ab‖ = -(c / N * ∑ ab, ‖y ab‖) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; simp only [neg_mul]
  rw [e]
  have key : c / N * ∑ ab, ‖y ab‖ ≤ c * r := by
    calc c / N * ∑ ab, ‖y ab‖ ≤ c / N * ((Fintype.card (PCoord ε) : ℝ) * r) :=
          mul_le_mul_of_nonneg_left hsum (div_nonneg hc hN0.le)
      _ ≤ c / N * (N * r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by rw [hN]; linarith) hr0)
            (div_nonneg hc hN0.le)
      _ = c * r := by field_simp
  linarith

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

