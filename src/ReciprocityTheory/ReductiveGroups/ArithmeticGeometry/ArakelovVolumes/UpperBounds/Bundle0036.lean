module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0031

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfQ
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nsq_eq_normSq (s : Fin (nd X) → Frame X.Ψ r → ℂ) (x0 : Frame X.Ψ r) (z : V (nd X)) :
    (∑ k, ‖s k (cpt X x0 z)‖ ^ 2) = HE.nsq (fun k z => s k (cpt X x0 z)) z := by
  unfold HE.nsq
  exact Finset.sum_congr rfl fun k _ => (Complex.normSq_eq_norm_sq _).symm

theorem lhs_finite (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (Xa : ArchInM X) (Fl : FlatM X Xa)
    (ψ : Frame X.Ψ r → ℝ) (C0 : ℝ) (hψb : ∀ x ∈ X.dom, ψ x ≤ C0) (bb : ℝ) (hbb : 0 ≤ bb)
    (ε : ℝ) (hε : 0 < ε)
    (hnull : volume {y | y ∈ OmF X x0 ∧ HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y = 0} = 0)
    (F : V (nd X) → ℂ)
    (hI : ∫⁻ y in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤)
    (P : Frame X.Ψ r → ℂ) (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) (N : Set (Frame X.Ψ r))
    (hN2 : ∀ z ∈ OmF X x0, cpt X x0 z ∈ N → z ∉ closedBall (0 : V (nd X)) (2 * ε)) :
    ∫⁻ z, N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z) ∂muF X x0 < ⊤ := by
  rw [muF_lintegral]
  have hO := ExF.isOpen_OmF X x0
  have hpt : ∀ᵐ z ∂(volume.restrict (OmF X x0)),
      ENNReal.ofReal (densF X x0 z) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z) ≤
        ENNReal.ofReal (Real.exp C0) * ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := by
    rw [ae_restrict_iff' hO.measurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz0 hz
    by_cases hzN : cpt X x0 z ∈ N
    swap
    · rw [Set.indicator_of_notMem hzN, mul_zero]; exact zero_le
    rw [Set.indicator_of_mem hzN]
    have hx : cpt X x0 z ∈ X.dom := hz
    have hN : 0 < HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z := by
      rcases (HE.nsq_nonneg _ z).lt_or_eq with h | h
      · exact h
      · exact absurd ⟨hz, h.symm⟩ hz0
    have hcut : HE.cut ε hε z = 0 := HE.cut_zero ε hε (by
      have := hN2 z hz hzN
      rw [mem_closedBall, dist_zero_right, not_le] at this; exact this.le)
    set S := ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2 with hSdef
    have hS : S = HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z * Real.exp (-phla X Xa.L (cpt X x0 z)) :=
      pnorm_sum_eq X Xa.L Fl.s hx
    have hSpos : 0 < S := by rw [hS]; positivity
    have hrho := rhoF_eq X x0 Xa.Fp Xa.L ψ bb Fl.s hz hN
    rw [← hSdef] at hrho
    rw [gφ_dom X P Xa.Fp Xa.L Fl.s hx, ← hSdef, ← ENNReal.ofReal_inv_of_pos hSpos,
      ← ENNReal.ofReal_pow (inv_nonneg.2 hSpos.le), ← mul_assoc,
      ← ENNReal.ofReal_mul (densF_pos X x0 hz).le,
      ← ENNReal.ofReal_mul (mul_nonneg (densF_pos X x0 hz).le (by positivity)),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    rw [hPF z hz, hcut, zero_sub, norm_neg]
    have hd := densF_pos X x0 hz
    have hrho2 : rhoF X x0 Xa.Fp ψ bb z = Real.exp (-phla X Xa.Fp (cpt X x0 z)) *
        Real.exp (-ψ (cpt X x0 z)) * Real.exp (bb * rhF X x0 z) * densF X x0 z := by
      rw [rhoF, Real.exp_add, Real.exp_add, Real.exp_log hd, neg_add, Real.exp_add]
    have hSn : S⁻¹ ^ (nd X) = (S ^ (nd X : ℝ))⁻¹ := by
      rw [Real.rpow_natCast, inv_pow]
    have hSn0 : 0 < S ^ (nd X : ℝ) := Real.rpow_pos_of_pos hSpos _
    set A := Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
      HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ)) with hAdef
    have hA0 : 0 ≤ A := by positivity

    have key : densF X x0 z * Real.exp (-phla X Xa.Fp (cpt X x0 z)) * S⁻¹ ^ (nd X) =
        A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z)) := by
      have e1 : A = rhoF X x0 Xa.Fp ψ bb z / S ^ (nd X : ℝ) := by
        rw [hrho]; field_simp
      rw [e1, hrho2, hSn]
      have h1 : Real.exp (-ψ (cpt X x0 z)) * Real.exp (ψ (cpt X x0 z)) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h2 : Real.exp (bb * rhF X x0 z) * Real.exp (-(bb * rhF X x0 z)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      field_simp
      nlinarith [h1, h2]
    have hle : A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z)) ≤ Real.exp C0 * A := by
      have e2 : Real.exp (ψ (cpt X x0 z)) ≤ Real.exp C0 := Real.exp_le_exp.2 (hψb _ hx)
      have e3 : Real.exp (-(bb * rhF X x0 z)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg hbb (ExF.rhF_nonneg X x0 ho hz)
      have e4 := (Real.exp_pos (-(bb * rhF X x0 z))).le
      calc A * Real.exp (ψ (cpt X x0 z)) * Real.exp (-(bb * rhF X x0 z))
          ≤ A * Real.exp C0 * 1 := by gcongr
        _ = Real.exp C0 * A := by ring
    have hF2 : 0 ≤ ‖F z‖ ^ 2 := sq_nonneg _
    calc densF X x0 z * (‖F z‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x0 z))) * S⁻¹ ^ (nd X)
        = ‖F z‖ ^ 2 * (densF X x0 z * Real.exp (-phla X Xa.Fp (cpt X x0 z)) * S⁻¹ ^ (nd X)) := by ring
      _ ≤ ‖F z‖ ^ 2 * (Real.exp C0 * A) := by rw [key]; exact mul_le_mul_of_nonneg_left hle hF2
      _ = Real.exp C0 * (‖F z‖ ^ 2 * Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
            HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := by rw [hAdef]; ring
  calc ∫⁻ z in OmF X x0, ENNReal.ofReal (densF X x0 z) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x0 z)
      ≤ ∫⁻ z in OmF X x0, ENNReal.ofReal (Real.exp C0) * ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Real.exp C0) * ∫⁻ z in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε z - F z‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb z) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) z ^ (-(nd X : ℝ))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

theorem rhs_bound (x1 : Frame X.Ψ r) (Xa : ArchInM X) (Fl : FlatM X Xa) (P : Frame X.Ψ r → ℂ)
    (N : Set (Frame X.Ψ r)) (ρ1 : ℝ) (hρ1 : 0 < ρ1) (hcb : closedBall (0 : V (nd X)) ρ1 ⊆ OmF X x1)
    (hN1 : ∀ w ∈ ball (0 : V (nd X)) ρ1, cpt X x1 w ∈ N) :
    ∃ c1 : ℝ, 0 < c1 ∧ ENNReal.ofReal c1 * ∫⁻ w in ball (0 : V (nd X)) ρ1,
      ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) ≤
      ∫⁻ w, N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) ∂muF X x1 := by
  set h1 : V (nd X) → ℝ := fun w => Real.exp (Real.log (densF X x1 w) - phla X Xa.Fp (cpt X x1 w) +
    (nd X : ℝ) * phla X Xa.L (cpt X x1 w)) with hh1
  have hc : ContinuousOn h1 (closedBall (0 : V (nd X)) ρ1) := fun w hw =>
    (Real.continuous_exp.continuousAt.comp ((((logDens_cdAt X x1 (hcb hw)).sub
      (phla_cpt_cdAt X x1 (hcb hw) Xa.Fp)).add (contDiffAt_const.mul
        (phla_cpt_cdAt X x1 (hcb hw) Xa.L))).continuousAt)).continuousWithinAt
  obtain ⟨w0, hw0, hmin⟩ := (isCompact_closedBall (0 : V (nd X)) ρ1).exists_isMinOn
    ⟨0, mem_closedBall_self hρ1.le⟩ hc
  refine ⟨h1 w0, Real.exp_pos _, ?_⟩
  have hpt : ∀ w ∈ ball (0 : V (nd X)) ρ1, ENNReal.ofReal (h1 w0) *
      ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) ≤
      ENNReal.ofReal (densF X x1 w) * N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) := by
    intro w hw
    have hwO := hcb (ball_subset_closedBall hw)
    have hx : cpt X x1 w ∈ X.dom := hwO
    rw [Set.indicator_of_mem (hN1 w hw), gφ_dom X P Xa.Fp Xa.L Fl.s hx, nsq_eq_normSq]
    set n2 := HE.nsq (fun k z => Fl.s k (cpt X x1 z)) w with hn2
    rcases (HE.nsq_nonneg (fun k z => Fl.s k (cpt X x1 z)) w).lt_or_eq with hN | hN
    · have hN' : 0 < n2 := hN
      set S := ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x1 w) ^ 2 with hSdef
      have hS : S = n2 * Real.exp (-phla X Xa.L (cpt X x1 w)) := pnorm_sum_eq X Xa.L Fl.s hx
      have hSpos : 0 < S := by rw [hS]; positivity
      have hd := densF_pos X x1 hwO
      rw [← ENNReal.ofReal_inv_of_pos hSpos, ← ENNReal.ofReal_pow (inv_nonneg.2 hSpos.le), ← mul_assoc,
        ← ENNReal.ofReal_mul hd.le, ← ENNReal.ofReal_mul (mul_nonneg hd.le (by positivity)),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hid : densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) * S⁻¹ ^ (nd X) =
          h1 w * n2 ^ (-(nd X : ℝ)) := by
        have e1 : h1 w = densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) *
            Real.exp (phla X Xa.L (cpt X x1 w)) ^ (nd X) := by
          simp only [hh1]
          rw [Real.exp_add, Real.exp_sub, Real.exp_log hd, Real.exp_neg, Real.exp_nat_mul]
          ring
        rw [e1, hS, Real.rpow_neg hN'.le, Real.rpow_natCast, mul_inv, mul_pow,
          show (Real.exp (-phla X Xa.L (cpt X x1 w)))⁻¹ = Real.exp (phla X Xa.L (cpt X x1 w)) by
            rw [Real.exp_neg, inv_inv], inv_pow]
        ring
      have hm : h1 w0 ≤ h1 w := hmin (ball_subset_closedBall hw)
      have hq : 0 ≤ ‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ)) := by positivity
      calc h1 w0 * (‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ)))
          ≤ h1 w * (‖P (cpt X x1 w)‖ ^ 2 * n2 ^ (-(nd X : ℝ))) := mul_le_mul_of_nonneg_right hm hq
        _ = densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x1 w))) *
              S⁻¹ ^ (nd X) := by
            rw [show densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X Xa.Fp (cpt X x1 w))) *
              S⁻¹ ^ (nd X) = ‖P (cpt X x1 w)‖ ^ 2 * (densF X x1 w * Real.exp (-phla X Xa.Fp (cpt X x1 w)) *
              S⁻¹ ^ (nd X)) by ring, hid]
            ring
    · have hN' : n2 = 0 := hN.symm
      rw [hN', Real.zero_rpow (by have := Xa.n_ge; simp; omega), mul_zero, ENNReal.ofReal_zero,
        mul_zero]
      exact zero_le
  calc ENNReal.ofReal (h1 w0) * ∫⁻ w in ball (0 : V (nd X)) ρ1,
        ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ)))
      = ∫⁻ w in ball (0 : V (nd X)) ρ1, ENNReal.ofReal (h1 w0) *
        ENNReal.ofReal (‖P (cpt X x1 w)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X x1 w)‖ ^ 2) ^ (-(nd X : ℝ))) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ w in ball (0 : V (nd X)) ρ1, ENNReal.ofReal (densF X x1 w) *
          N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) := setLIntegral_mono' measurableSet_ball hpt
    _ ≤ ∫⁻ w in OmF X x1, ENNReal.ofReal (densF X x1 w) *
          N.indicator (gφ X P Xa.Fp Xa.L Fl.s) (cpt X x1 w) :=
        lintegral_mono_set (ball_subset_closedBall.trans hcb)
    _ = _ := (muF_lintegral X x1 _).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem sumP_contOn {N : ℕ} (L : Wt X.Ψ r) (P : Fin N → Frame X.Ψ r → ℂ)
    (hP : ∀ k, ContinuousOn (P k) X.dom) :
    ContinuousOn (fun x => ∑ k, X.pnorm L (P k) x ^ 2) X.dom := by
  have hphl := IW.phla_contOn X L
  have hc : ContinuousOn (fun x => (∑ k, Complex.normSq (P k x)) * Real.exp (-phla X L x)) X.dom :=
    (continuousOn_finsetSum _ fun k _ => Complex.continuous_normSq.comp_continuousOn (hP k)).mul
      (Real.continuous_exp.comp_continuousOn hphl.neg)
  exact hc.congr fun x hx => sum_pnorm_sq X L P hx

theorem WSk_meas (Xa : ArchInM X) (Fl : FlatM X Xa) : Measurable (WSk X Xa Fl) := by
  classical
  have hdo : IsOpen X.dom := IW.isOpen_dom X
  have hwc : ∀ k, ContinuousOn (Xa.w k) X.dom := fun k => (Xa.w_van k).1.1.1.1.continuousOn
  have hsc : ∀ k, ContinuousOn (Fl.s k) X.dom := fun k => (Fl.s_van k).1.1.1.1.continuousOn
  have hSw := sumP_contOn Xa.L Xa.w hwc
  have hSs := sumP_contOn Xa.L Fl.s hsc
  have hSw0 : ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≠ 0 := fun x hx => by
    rw [sum_pnorm_sq X _ _ hx]
    exact (mul_pos (sumw_pos Xa hx) (Real.exp_pos _)).ne'
  have h1 : Measurable (X.dom.piecewise
      (fun x => ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x))) 0) :=
    ContinuousOn.measurable_piecewise
      (ENNReal.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn (IW.phla_contOn X _).neg))
      continuousOn_const hdo.measurableSet
  have h2 : Measurable (X.dom.piecewise
      (fun x => ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ))) 0) :=
    ContinuousOn.measurable_piecewise
      ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).comp_continuousOn hSw)
      continuousOn_const hdo.measurableSet
  have h3 : Measurable (X.dom.piecewise
      (fun x => ENNReal.ofReal ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) /
        ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) 0) :=
    ContinuousOn.measurable_piecewise
      ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).comp_continuousOn
        (hSs.div hSw hSw0))
      continuousOn_const hdo.measurableSet
  have key : WSk X Xa Fl = X.dom.piecewise
      (fun x => ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x))) 0 *
      X.dom.piecewise
        (fun x => ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ))) 0 *
      X.dom.piecewise
        (fun x => ENNReal.ofReal ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) /
          ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) 0 := by
    funext x
    by_cases hx : x ∈ X.dom
    · simp only [WSk, if_pos hx, Pi.mul_apply, Set.piecewise_eq_of_mem _ _ _ hx]
    · simp only [WSk, if_neg hx, Pi.mul_apply, Set.piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply,
        zero_mul]
  rw [key]
  exact (h1.mul h2).mul h3

theorem pnorm_lact (L : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : X.IsSec L P) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.pnorm L P (lact γ x) = X.pnorm L P x := by
  rw [pnorm_eq X, pnorm_eq X, hP.2.2 γ hγ x hx, norm_mul, OntoE.chi_norm X L hγ, one_mul,
    normFactor_leftAction_holds r X L γ hγ x hx]

theorem phla_lact (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phla X la (lact γ x) = phla X la x := by
  unfold phla
  rw [normFactor_leftAction_holds r X la γ hγ x hx]

theorem WSk_metric (Xa : ArchInM X) (Fl : FlatM X Xa) :
    IsMetricW X (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) := by
  have hwS : ∀ k, X.IsSec Xa.L (Xa.w k) := fun k => (Xa.w_van k).1.1.1
  have hsS : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  refine ⟨WSk_meas Xa Fl, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hxb := OntoS.dom_rmul X hx hb
    have hbc : 0 < ‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2 := by
      have := OntoE.bchar_ne X (Xa.Fp + Xa.T • Xa.L) hb
      positivity
    have hpw : ∀ k, X.pnorm Xa.L (Xa.w k) (rmul x b) = X.pnorm Xa.L (Xa.w k) x := fun k =>
      IW.pnorm_rmul X normFactor_rightBorel_holds Xa.L (hwS k) hx hb
    have hps : ∀ k, X.pnorm Xa.L (Fl.s k) (rmul x b) = X.pnorm Xa.L (Fl.s k) x := fun k =>
      IW.pnorm_rmul X normFactor_rightBorel_holds Xa.L (hsS k) hx hb
    simp only [WSk, if_pos hxb, if_pos hx, hpw, hps]
    rw [IW.exp_neg_phla_rmul X normFactor_rightBorel_holds _ hx hb, ENNReal.ofReal_div_of_pos hbc]
    simp only [div_eq_mul_inv]
    ring
  · have hxg := OntoS.dom_lact X hγ hx
    have hpw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ x) = X.pnorm Xa.L (Xa.w k) x := fun k =>
      pnorm_lact Xa.L (hwS k) hγ hx
    have hps : ∀ k, X.pnorm Xa.L (Fl.s k) (lact γ x) = X.pnorm Xa.L (Fl.s k) x := fun k =>
      pnorm_lact Xa.L (hsS k) hγ hx
    simp only [WSk, if_pos hxg, if_pos hx, hpw, hps, phla_lact _ hγ hx]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem nfac_nonneg (la : Wt X.Ψ r) (x : Frame X.Ψ r) : 0 ≤ X.nfac la x := by
  unfold Data.nfac
  exact Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _

theorem pnorm_nonneg (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : 0 ≤ X.pnorm la P x := by
  rw [pnorm_eq X]
  exact mul_nonneg (norm_nonneg _) (nfac_nonneg la x)

theorem WSk_lower (Xa : ArchInM X) (Fl : FlatM X Xa) :
    WLower X (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) := by
  have hT1 : (1 : ℝ) ≤ Xa.T := by
    have h1 := Xa.T_ge
    have h2 := Xa.n_ge
    exact_mod_cast (by nlinarith : 1 ≤ Xa.T)
  choose Cw hCw using fun k => (Xa.w_van k).1.1.2
  choose Cs hCs using fun k => (Fl.s_van k).1.1.2
  set u : ℝ := (Xa.T : ℝ) - 1 / 2 with hu
  have hu0 : 0 < u := by linarith
  set Mw : ℝ := ∑ k, max (Cw k) 0 ^ 2 + 1 with hMw
  set Ms : ℝ := ∑ k, max (Cs k) 0 ^ 2 + 1 with hMs
  have hMw0 : 0 < Mw := by positivity
  have hMs0 : 0 < Ms := by positivity
  refine ⟨Mw ^ (-(1 / 2 : ℝ)) * (Ms ^ u)⁻¹, by positivity, fun x hx => ?_⟩
  have hSwM : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ Mw := by
    have : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ ∑ k, max (Cw k) 0 ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (pnorm_nonneg _ _ _)
        ((hCw k x hx).trans (le_max_left _ _)) 2
    linarith
  have hSsM : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 ≤ Ms := by
    have : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 ≤ ∑ k, max (Cs k) 0 ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (pnorm_nonneg _ _ _)
        ((hCs k x hx).trans (le_max_left _ _)) 2
    linarith
  have hSw : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
    rw [sum_pnorm_sq X _ _ hx]
    exact mul_pos (sumw_pos Xa hx) (Real.exp_pos _)
  have hSs0 : 0 ≤ ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  set Sw := ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hSwd
  set Ss := ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 with hSsd
  set e := Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x) with he
  have he0 : 0 < e := Real.exp_pos _
  simp only [WSk, if_pos hx]
  rw [← hSwd, ← hSsd, ← he]
  rcases hSs0.eq_or_lt with hS | hS
  · rw [← hS, zero_div, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.mul_top]
    · exact le_top
    · exact mul_ne_zero (ENNReal.ofReal_pos.mpr he0).ne'
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hSw) ENNReal.ofReal_ne_top).ne'
  · rw [ENNReal.ofReal_rpow_of_pos hSw, ENNReal.ofReal_rpow_of_pos (div_pos hS hSw),
      ← ENNReal.ofReal_mul he0.le, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have eq : Sw ^ (-(Xa.T : ℝ)) * (Ss / Sw) ^ (-u) = Sw ^ (-(1 / 2 : ℝ)) * (Ss ^ u)⁻¹ := by
      have hsplit : Sw ^ u = Sw ^ (Xa.T : ℝ) * Sw ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hSw]
        congr 1
      rw [Real.rpow_neg hSw.le, Real.rpow_neg (div_pos hS hSw).le, Real.div_rpow hS.le hSw.le,
        inv_div, hsplit]
      have h1 : 0 < Sw ^ (Xa.T : ℝ) := Real.rpow_pos_of_pos hSw _
      have h2 : 0 < Ss ^ u := Real.rpow_pos_of_pos hS _
      field_simp
    have hA : Mw ^ (-(1 / 2 : ℝ)) ≤ Sw ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hSw hSwM (by norm_num)
    have hB : (Ms ^ u)⁻¹ ≤ (Ss ^ u)⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos hS _) (Real.rpow_le_rpow hS.le hSsM hu0.le)
    have hC : Mw ^ (-(1 / 2 : ℝ)) * (Ms ^ u)⁻¹ ≤ Sw ^ (-(1 / 2 : ℝ)) * (Ss ^ u)⁻¹ :=
      mul_le_mul hA hB (by positivity) (by positivity)
    calc Mw ^ (-(1 / 2 : ℝ)) * (Ms ^ u)⁻¹ * e ≤ Sw ^ (-(1 / 2 : ℝ)) * (Ss ^ u)⁻¹ * e :=
          mul_le_mul_of_nonneg_right hC he0.le
      _ = e * Sw ^ (-(Xa.T : ℝ)) * (Ss / Sw) ^ (-u) := by rw [mul_assoc e, eq]; ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
end

