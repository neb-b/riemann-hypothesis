module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfE
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def idF (X : Data E r) : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

theorem idF_mem (X : Data E r) : idF X ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  refine ⟨?_, fun a c h => ?_⟩
  · have h1 : mat (idF X) τ = 1 := by
      ext i j
      rfl
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  · simp [idF, Matrix.one_apply, ne_of_gt h]

theorem rmul_idF (X : Data E r) (y : Frame X.Ψ r) : rmul y (idF X) = y := by
  funext τ
  show (mat y τ * mat (idF X) τ : Matrix (Fin r) (Fin r) ℂ) = y τ
  have h1 : mat (idF X) τ = 1 := by
    ext i j
    rfl
  rw [h1, mul_one]
  rfl

theorem bchar_idF (X : Data E r) (la : Wt X.Ψ r) : bchar la (idF X) = 1 := by
  simp [bchar, idF]

theorem bchar_contAt (X : Data E r) (la : Wt X.Ψ r) : ContinuousAt (bchar la) (idF X) := by
  unfold bchar
  refine tendsto_finsetProd _ fun τ _ => tendsto_finsetProd _ fun i _ => ?_
  have hc : Continuous fun b : Frame X.Ψ r => b τ i i := by fun_prop
  exact hc.continuousAt.zpow₀ _ (Or.inl (by simp [idF]))

theorem ball_int_bound (X : Data E r) (la : Wt X.Ψ r) {R0 ρ : ℝ}
    (hgood : ∀ w ∈ Metric.ball (0 : V (nd X)) R0, (∀ τ, (mat (nmat X w) τ).det ≠ 0) ∧
      (∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (lminor (Gw X w τ) i).re) ∧ 1 / 2 < nfw X la w)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hxo : IsOrth X x) (P : Frame X.Ψ r → ℂ) :
    Metric.ball (0 : V (nd X)) (min R0 ρ) ⊆ Bset X x ρ ∧
      ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x z)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
        ∫⁻ w in Bset X x ρ, ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
  have hgoodR := fun w (hw : w ∈ Metric.ball (0 : V (nd X)) (min R0 ρ)) =>
    hgood w (Metric.ball_subset_ball (min_le_left _ _) hw)
  have hmem : Metric.ball (0 : V (nd X)) (min R0 ρ) ⊆ Bset X x ρ := fun w hw => by
    obtain ⟨h1, h2, -⟩ := hgoodR w hw
    exact ⟨lt_of_lt_of_le (mem_ball_zero_iff.1 hw) (min_le_right _ _), cpt_mem_dom X hx hxo h1 h2⟩
  refine ⟨hmem, ?_⟩
  have hpt : ∀ w ∈ Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x w)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
      (‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by
    intro w hw
    obtain ⟨-, -, h3⟩ := hgoodR w hw
    have hn : X.nfac la (cpt X x w) = nfw X la w := nfac_cpt_orth X la hxo w
    have he : 1 ≤ ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
      rw [exp_neg_phla X la (by rw [hn]; linarith), hn, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    calc ‖P (cpt X x w)‖ₑ ^ 2 = ‖P (cpt X x w)‖ₑ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖P (cpt X x w)‖ₑ ^ 2 *
          (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by gcongr
      _ = _ := by ring
  calc ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x z)‖ₑ ^ 2
      ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ENNReal.ofReal 4 *
          (‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z)))) :=
        setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
    _ = ENNReal.ofReal 4 * ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ),
          ‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_mono_set hmem) zero_le

theorem subMeanLoc_of (hLU : LUStatement (E := E)) : SubMeanLocStatement (E := E) := by
  intro r X la ρ hρ hρ1 x hx hxo
  obtain ⟨R0, hR0, hgood⟩ := good_ball X la
  have hR : 0 < min R0 ρ := lt_min hR0 hρ
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, hb, hdec, hinv⟩ := hLU r X x hxo
  have hx0 : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rw [cpt_zero]; exact hx
  obtain ⟨hΔx, hzx, hbx⟩ := hinv 0 hx0 (idF X) (idF_mem X)
  rw [rmul_idF, cpt_zero] at hΔx hzx hbx
  have hOo : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
    (isOpenDom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have hxO : x ∈ {y | y ∈ X.dom ∧ Δ y ≠ 0} := ⟨hx, hΔx⟩
  have hzc : ContinuousAt zOf x := hz.continuousOn.continuousAt (hOo.mem_nhds hxO)
  have hbc : ContinuousAt (fun y => bchar la (bOf y)) x := by
    have h := bchar_contAt X la
    rw [← hbx] at h
    exact h.comp (hb.continuousOn.continuousAt (hOo.mem_nhds hxO))
  have e1 : ∀ᶠ y in 𝓝 x, y ∈ {y | y ∈ X.dom ∧ Δ y ≠ 0} := hOo.mem_nhds hxO
  have e2 : ∀ᶠ y in 𝓝 x, ‖zOf y‖ < min R0 ρ / 2 :=
    hzc.norm.eventually_lt continuousAt_const (by rw [hzx, norm_zero]; positivity)
  have e3 : ∀ᶠ y in 𝓝 x, ‖bchar la (bOf y)‖ < 2 :=
    hbc.norm.eventually_lt continuousAt_const (by rw [hbx, bchar_idF, norm_one]; norm_num)
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  set v := volume (Metric.ball (0 : V (nd X)) (min R0 ρ / 2)) with hv
  have hvpos : v ≠ 0 := (Metric.measure_ball_pos volume _ (by positivity)).ne'
  have hvtop : v ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨ε, hε, ENNReal.ofReal 4 * v⁻¹ * ENNReal.ofReal 4,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hvpos))) ENNReal.ofReal_lt_top, fun P hP y hy => ?_⟩
  obtain ⟨⟨hyd, hΔy⟩, hzy, hby⟩ := hall y hy
  obtain ⟨hzO, hbB, hyeq⟩ := hdec y hyd hΔy
  have hPy : P y = bchar la (bOf y) * P (cpt X x (zOf y)) := by
    conv_lhs => rw [hyeq]
    exact hP.2 _ hzO _ hbB
  have hsub : Metric.ball (zOf y) (min R0 ρ / 2) ⊆ Metric.ball (0 : V (nd X)) (min R0 ρ) := by
    intro w hw
    rw [mem_ball_zero_iff]
    rw [Metric.mem_ball, dist_eq_norm] at hw
    calc ‖w‖ = ‖(w - zOf y) + zOf y‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - zOf y‖ + ‖zOf y‖ := norm_add_le _ _
      _ < min R0 ρ / 2 + min R0 ρ / 2 := add_lt_add hw hzy
      _ = min R0 ρ := by ring
  obtain ⟨hmemB, hint⟩ := ball_int_bound X la hgood hx hxo P
  have hu : DifferentiableOn ℂ (fun w => P (cpt X x w)) (Metric.ball (zOf y) (min R0 ρ / 2)) :=
    hP.1.comp (diff_cpt X x).differentiableOn fun w hw => (hmemB (hsub hw)).2
  have hmv := ReciprocityTheory.L2DbarEstimates.C.mv (nd X) (zOf y) (min R0 ρ / 2) (fun w => P (cpt X x w)) (fun _ => 1)
    hu measurable_const
  simp only [mul_one, one_mul, lintegral_const, Measure.restrict_apply_univ] at hmv
  rw [Measure.addHaar_ball_center] at hmv
  have hle : ‖P (cpt X x (zOf y))‖ₑ ^ 2 ≤
      v⁻¹ * ∫⁻ w in Metric.ball (zOf y) (min R0 ρ / 2), ‖P (cpt X x w)‖ₑ ^ 2 := by
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hvpos) (Or.inl hvtop)]
    exact hmv
  have hbb : ‖bchar la (bOf y)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (bchar la (bOf y))])
  calc ‖P y‖ₑ ^ 2 = ‖bchar la (bOf y)‖ₑ ^ 2 * ‖P (cpt X x (zOf y))‖ₑ ^ 2 := by
        rw [hPy, enorm_mul, mul_pow]
    _ ≤ ENNReal.ofReal 4 * (v⁻¹ * (ENNReal.ofReal 4 * ∫⁻ w in Bset X x ρ,
          ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))))) := by
        refine mul_le_mul' hbb (hle.trans (mul_le_mul_of_nonneg_left ?_ zero_le))
        exact (lintegral_mono_set hsub).trans hint
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivB

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

variable {n : ℕ} {U : Set (V n)}

theorem norm_sum_sq_le {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    ‖∑ i ∈ s, x i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  calc ‖∑ i ∈ s, x i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ s.card * ∑ i ∈ s, ‖x i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

def stp {p : ℕ} (α : Fin p → ℕ) (k : Fin p) : Fin p → ℕ := fun i => α i + if i = k then 1 else 0

theorem mem_step {p N : ℕ} {α : Fin p → ℕ} (hα : α ∈ Finset.Nat.antidiagonalTuple p N) (k : Fin p) :
    stp α k ∈ Finset.Nat.antidiagonalTuple p (N + 1) := by
  rw [Finset.Nat.mem_antidiagonalTuple] at hα ⊢
  simp [stp, Finset.sum_add_distrib, hα]

theorem pow_step {p : ℕ} (g : Fin p → ℂ) (α : Fin p → ℕ) (k : Fin p) :
    ∏ i, g i ^ stp α k i = (∏ i, g i ^ α i) * g k := by
  simp only [stp, pow_add, Finset.prod_mul_distrib]
  congr 1
  have h : ∀ i, g i ^ (if i = k then 1 else 0) = if i = k then g i else 1 := by
    intro i; split_ifs <;> simp
  simp only [h, Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem iter_div (hU : IsOpen U) (S : EtaleStein n U) (hz : S.z = Subtype.val) {p : ℕ}
    (g : Fin p → V n → ℂ) (ph0 : V n → ℝ) (hp : 2 ≤ p)
    (hg : ∀ i, DifferentiableOn ℂ (g i) U) (hnz : ∀ y ∈ U, ∃ i, g i y ≠ 0)
    (hph : ContDiffOn ℝ ∞ ph0 U)
    (hl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (ph0 w : ℂ)) y ξ).re)
    (τ0 : ℝ) : ∀ (N : ℕ), (p : ℝ) - 1 < τ0 - N - 1 + 1 →
    ∀ F : V n → ℂ, DifferentiableOn ℂ F U →
    ∫⁻ y in U, ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-τ0) * Real.exp (-ph0 y)) < ⊤ →
    ∃ H : (Fin p → ℕ) → V n → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple p N, DifferentiableOn ℂ (H α) U ∧
        ∫⁻ y in U, ENNReal.ofReal (‖H α y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - N)) *
          Real.exp (-ph0 y)) < ⊤) ∧
      ∀ y ∈ U, F y = ∑ α ∈ Finset.Nat.antidiagonalTuple p N, (∏ i, g i y ^ α i) * H α y := by
  have hSpos : ∀ y ∈ U, 0 < ∑ i, ‖g i y‖ ^ 2 := by
    intro y hy
    obtain ⟨i, hi⟩ := hnz y hy
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩
  have hScont : ContinuousOn (fun y => ∑ i, ‖g i y‖ ^ 2) U :=
    continuousOn_finsetSum _ fun i _ => ((hg i).continuousOn.norm).pow 2
  intro N
  induction N with
  | zero =>
    intro _ F hF hI
    refine ⟨fun _ => F, fun α hα => ⟨hF, by simpa using hI⟩, fun y _ => ?_⟩
    rw [Finset.Nat.antidiagonalTuple_zero_right]
    simp
  | succ N ih =>
    intro hN F hF hI
    have hN' : (p : ℝ) - 1 < τ0 - N - 1 + 1 := by push_cast at hN; linarith
    obtain ⟨H, hH, hid⟩ := ih hN' F hF hI
    set t : ℝ := τ0 - N - 1 with htdef
    have ht : (p : ℝ) - 1 < t := by rw [htdef]; push_cast at hN; linarith
    have hstep : ∀ α ∈ Finset.Nat.antidiagonalTuple p N, ∃ hh : Fin p → V n → ℂ,
        (∀ i, DifferentiableOn ℂ (hh i) U) ∧ (∀ y ∈ U, H α y = ∑ i, g i y * hh i y) ∧
        ∫⁻ y in U, ENNReal.ofReal ((∑ i, ‖hh i y‖ ^ 2) * (∑ i, ‖g i y‖ ^ 2) ^ (-t) *
          Real.exp (-ph0 y)) < ⊤ := by
      intro α hα
      have hIα : ∫⁻ y in U, ENNReal.ofReal (‖H α y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) *
          Real.exp (-ph0 y)) < ⊤ := by
        have e : -(t + 1) = -(τ0 - N) := by rw [htdef]; ring
        rw [e]; exact (hH α hα).2
      obtain ⟨hh, hhd, hhid, hhest⟩ := UpDivA.skoda_open hU S hz g ph0 t (H α) hp hg hnz hph hl ht
        (hH α hα).1 hIα
      exact ⟨hh, hhd, hhid, lt_of_le_of_lt hhest (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIα)⟩
    choose! hh hhd hhid hhI using hstep
    set A := Finset.Nat.antidiagonalTuple p N with hA
    obtain ⟨w, hw⟩ : ∃ w : V n → ℝ, w = fun y => (∑ i, ‖g i y‖ ^ 2) ^ (-t) * Real.exp (-ph0 y) :=
      ⟨_, rfl⟩
    have hw0 : ∀ y, 0 ≤ w y := fun y => by
      rw [hw]; exact mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _)
        (Real.exp_pos _).le
    have hwc : ContinuousOn w U := by
      rw [hw]
      exact (hScont.rpow_const fun y hy => Or.inl (hSpos y hy).ne').mul
        (Real.continuous_exp.comp_continuousOn hph.continuousOn.neg)
    refine ⟨fun β y => ∑ α ∈ A, ∑ k, if stp α k = β then hh α k y else 0,
      fun β _ => ⟨?_, ?_⟩, ?_⟩
    · have hk : ∀ α ∈ A, ∀ k ∈ (Finset.univ : Finset (Fin p)),
          DifferentiableOn ℂ (fun y => if stp α k = β then hh α k y else 0) U := by
        intro α hα k _
        by_cases hk : stp α k = β
        · simp only [hk, if_true]; exact hhd α hα k
        · simp only [hk, if_false]; exact differentiableOn_const (c := (0 : ℂ))
      have hα : ∀ α ∈ A, DifferentiableOn ℂ
          (fun y => ∑ k, if stp α k = β then hh α k y else 0) U := fun α hα =>
        (DifferentiableOn.sum (u := Finset.univ) (A := fun k y => if stp α k = β then hh α k y else 0)
          (hk α hα)).congr fun y _ => by simp [Finset.sum_apply]
      exact (DifferentiableOn.sum (u := A)
        (A := fun α y => ∑ k, if stp α k = β then hh α k y else 0) hα).congr fun y _ => by
          simp [Finset.sum_apply]
    · set C : ℝ := ((A ×ˢ (Finset.univ : Finset (Fin p))).card : ℝ) with hC
      have hpt : ∀ y, ‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2
          ≤ C * ∑ α ∈ A, ∑ k, ‖hh α k y‖ ^ 2 := by
        intro y
        rw [← Finset.sum_product']
        refine (norm_sum_sq_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        rw [Finset.sum_product]
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun k _ => ?_
        split_ifs
        · exact le_rfl
        · simp
      have hbound : ∀ y, ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2
          * w y) ≤ ENNReal.ofReal C * ∑ α ∈ A, ENNReal.ofReal ((∑ k, ‖hh α k y‖ ^ 2) * w y) := by
        intro y
        rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ => mul_nonneg (Finset.sum_nonneg fun _ _ =>
          by positivity) (hw0 y)), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 * w y
            ≤ (C * ∑ α ∈ A, ∑ k, ‖hh α k y‖ ^ 2) * w y := mul_le_mul_of_nonneg_right (hpt y) (hw0 y)
          _ = C * ∑ α ∈ A, (∑ k, ‖hh α k y‖ ^ 2) * w y := by rw [mul_assoc, Finset.sum_mul]
      have hfin : ∫⁻ y in U, ENNReal.ofReal C * ∑ α ∈ A, ENNReal.ofReal ((∑ k, ‖hh α k y‖ ^ 2) * w y)
          < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [lintegral_finsetSum']
        · refine ENNReal.sum_lt_top.mpr fun α hα => ?_
          have := hhI α hα
          rw [hw]
          simpa [mul_assoc] using this
        · intro α hα
          have hc : ContinuousOn (fun y => (∑ k, ‖hh α k y‖ ^ 2) * w y) U :=
            (continuousOn_finsetSum _ fun k _ => ((hhd α hα k).continuousOn.norm).pow 2).mul hwc
          exact (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hU.measurableSet
      have e2 : (fun y => ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 *
          (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - ((N + 1 : ℕ) : ℝ))) * Real.exp (-ph0 y))) =
          fun y => ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 * w y) := by
        funext y
        rw [hw, mul_assoc]
        congr 4
        rw [htdef]; push_cast; ring
      show ∫⁻ y in U, ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 *
          (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - ((N + 1 : ℕ) : ℝ))) * Real.exp (-ph0 y)) < ⊤
      rw [e2]
      exact lt_of_le_of_lt (lintegral_mono hbound) hfin
    · intro y hy
      rw [hid y hy]
      have h1 : ∀ α ∈ A, (∏ i, g i y ^ α i) * H α y =
          ∑ k, (∏ i, g i y ^ stp α k i) * hh α k y := by
        intro α hα
        rw [hhid α hα y hy, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_step]; ring
      rw [Finset.sum_congr rfl h1]
      symm
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq, if_pos (mem_step hα k)]

end UpDivB

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

