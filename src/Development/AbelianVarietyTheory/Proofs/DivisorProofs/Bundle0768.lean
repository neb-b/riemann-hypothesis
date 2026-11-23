module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0757
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakExtensionVanishOtherOrbitPoints
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
  Topology Filter Metric
open scoped ENNReal

noncomputable section

namespace GlobalTheory.PeakOrbit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem rank_pos (X : Data E r) (hn : 0 < nd X) : 0 < r := by
  obtain ⟨e⟩ : Nonempty (Ent X) := Fintype.card_pos_iff.1 hn
  exact Fin.pos e.2.1.1

theorem isOrth_translate (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (ho : IsOrth X x) : IsOrth X (lact γ x) := fun τ => by
  rw [OntoS.gram_lact X hγ]; exact ho τ

def testFn (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (Ψ : Frame X.Ψ r → ℝ≥0∞)
    (y : Frame X.Ψ r) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal (‖X.dom.piecewise P 0 y‖ ^ 2 * Real.exp (-(X.dom.piecewise (phla X la) 0 y))) * Ψ y

theorem testFn_dom (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (Ψ : Frame X.Ψ r → ℝ≥0∞)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    testFn X la P Ψ y = ENNReal.ofReal (‖P y‖ ^ 2 * Real.exp (-phla X la y)) * Ψ y := by
  classical
  simp only [testFn, Set.piecewise_eq_of_mem _ _ _ hy]

theorem testFn_meas (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : ContinuousOn P X.dom)
    {Ψ : Frame X.Ψ r → ℝ≥0∞} (hΨ : Measurable Ψ) : Measurable (testFn X la P Ψ) := by
  classical
  have hm := (IW.isOpen_dom X).measurableSet
  have h1 : Measurable (X.dom.piecewise P 0) := hP.measurable_piecewise continuousOn_const hm
  have h2 : Measurable (X.dom.piecewise (phla X la) 0) :=
    (IW.phla_contOn X la).measurable_piecewise continuousOn_const hm
  unfold testFn
  exact ((h1.norm.pow_const 2).mul (h2.neg.exp)).ennreal_ofReal.mul hΨ

theorem testFn_rmul (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : IsBEq X la P)
    {Ψ : Frame X.Ψ r → ℝ≥0∞} (hΨ : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψ (rmul y b) = Ψ y)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    testFn X la P Ψ (rmul y b) = testFn X la P Ψ y := by
  rw [testFn_dom X la P Ψ (OntoS.dom_rmul X hy hb), testFn_dom X la P Ψ hy,
    IW.exp_neg_phla_rmul X GlobalTheory.NormFactor.nfacRmul_holds la hy hb, hP.2 y hy b hb, hΨ y hy b hb]
  congr 2
  have : ‖bchar la b‖ ≠ 0 := norm_ne_zero_iff.2 (IW.bchar_ne_zero X hb la)
  rw [norm_mul]
  field_simp

theorem vanish_translate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → 0 < nd X →
    ∀ (Ψ : Frame X.Ψ r → ℝ≥0∞), Measurable Ψ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψ (rmul y b) = Ψ y) →
    (∀ γ ∈ X.Γ, ∀ y ∈ X.dom, Ψ (lact γ y) = Ψ y) → ∀ (c ρ' : ℝ), 0 < c → 0 < ρ' →
    (∀ w ∈ Metric.ball (0 : V (nd X)) ρ',
      ENNReal.ofReal (c * ‖w‖ ^ (-(2 * (nd X : ℝ)))) ≤ Ψ (cpt X x w)) →
    (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
      ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) →
    ∀ (F0 F : V (nd X) → ℂ), (∀ z, 1 / (100 * (r : ℝ) ^ 2) < ‖z‖ → F0 z = 0) →
    DifferentiableOn ℂ F (OmF X x) →
    ∫⁻ z, ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z))) * Ψ (cpt X x z)
      ∂muF X x < ⊤ →
    ∀ P : Frame X.Ψ r → ℂ, IsBEq X la P → (∀ z ∈ OmF X x, P (cpt X x z) = F z) →
    ∀ γ ∈ X.Γ, γ ≠ 1 → P (lact γ x) = 0 := by
  intro E _ _ _ r X la x ho hn Ψ hΨm hΨB hΨΓ c ρ' hc hρ' hlow hinj F0 F hF0 _ hI P hP hPF γ hγ hγ1
  by_contra hne
  have hr : (0 : ℝ) < r := Nat.cast_pos.2 (rank_pos X hn)
  have hR : (0 : ℝ) < 1 / (100 * (r : ℝ) ^ 2) := by positivity
  set x1 := lact γ x with hx1def
  have ho1 : IsOrth X x1 := isOrth_translate X hγ ho
  have h01 := IW.zero_mem_OmF X x1 ho1
  have hO1 := (ExF.isOpen_OmF X x1).mem_nhds h01
  have hO := (ExF.isOpen_OmF X x).mem_nhds (IW.zero_mem_OmF X x ho)

  set h : V (nd X) → ℝ := fun w => Real.exp (Real.log (densF X x1 w) - phla X la (cpt X x1 w)) *
    ‖P (cpt X x1 w)‖ ^ 2 with hh
  have hcont : ContinuousAt h 0 :=
    (Real.continuous_exp.continuousAt.comp (((IW.logDens_cdAt X x1 h01).sub
      (IW.phla_cpt_cdAt X x1 h01 la)).continuousAt)).mul
      (((IW.comp_cpt_diffOn X hP.1 x1).continuousOn.continuousAt hO1).norm.pow 2)
  have hh0 : 0 < h 0 := by
    simp only [hh, IW.cpt_zero]
    exact mul_pos (Real.exp_pos _) (pow_pos (norm_pos_iff.2 hne) 2)
  have hev : ∀ᶠ w in 𝓝 (0 : V (nd X)), h 0 / 2 < h w :=
    hcont.eventually (lt_mem_nhds (by linarith))
  have hall : ∀ᶠ w in 𝓝 (0 : V (nd X)), h 0 / 2 < h w ∧ w ∈ OmF X x1 ∧ w ∈ OmF X x ∧
      w ∈ ball (0 : V (nd X)) ρ' ∧ w ∈ ball (0 : V (nd X)) (1 / (100 * (r : ℝ) ^ 2)) := by
    filter_upwards [hev, hO1, hO, ball_mem_nhds 0 hρ', ball_mem_nhds 0 hR] with w a b c d e
    exact ⟨a, b, c, d, e⟩
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.1 hall
  obtain ⟨Δ, zOf, bOf, hΔd, -, hzOf, -, hdec, hlast⟩ := lu_holds (E := E) r X x1 ho1
  have hG : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
    hΔd.continuous.continuousOn.isOpen_inter_preimage (IW.isOpen_dom X) isOpen_compl_singleton
  have hNo : IsOpen (IW.Nset X Δ zOf ρ) := hzOf.continuousOn.isOpen_inter_preimage hG isOpen_ball
  have hN1 : ∀ w ∈ ball (0 : V (nd X)) ρ, cpt X x1 w ∈ IW.Nset X Δ zOf ρ := by
    intro w hw
    have hwO := (hsub hw).2.1
    obtain ⟨h1, h2, -⟩ := hlast w hwO (IW.idF X) (IW.idF_mem X)
    rw [IW.rmul_idF] at h1 h2
    exact ⟨⟨hwO, h1⟩, by simp only [Set.mem_preimage]; rw [h2]; exact hw⟩
  have hN2 : ∀ z, cpt X x z ∈ IW.Nset X Δ zOf ρ → z ∈ OmF X x ∧ F0 z = 0 := by
    intro z hzN
    obtain ⟨⟨hzd, hΔz⟩, hzb⟩ := hzN
    refine ⟨hzd, hF0 z (lt_of_not_ge fun hz => hγ1 ?_)⟩
    obtain ⟨-, hbO, hd⟩ := hdec _ hzd hΔz
    have e := IW.rmul_binv X (cpt X x1 (zOf (cpt X x z))) hbO
    rw [← hd, hx1def, IW.cpt_lact] at e
    have hw := (hsub hzb).2.2.2.2
    rw [mem_ball, dist_zero_right] at hw
    exact hinj γ hγ _ z hw.le hz _ (IW.binv_mem X hbO) e.symm
  have hφm : Measurable ((IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ)) :=
    (testFn_meas X la hP.1.continuousOn hΨm).indicator hNo.measurableSet
  have hφinv : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (rmul y b) =
        (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) y := by
    intro y hy b hb
    by_cases hyN : y ∈ IW.Nset X Δ zOf ρ
    · rw [Set.indicator_of_mem hyN,
        Set.indicator_of_mem ((IW.Nset_sat X x1 hdec hlast ρ hy hb).2 hyN),
        testFn_rmul X hP hΨB hy hb]
    · rw [Set.indicator_of_notMem hyN, Set.indicator_of_notMem
        (fun h => hyN ((IW.Nset_sat X x1 hdec hlast ρ hy hb).1 h))]
  have hMI := measInv_holds (E := E) r X x x1 ho ho1 _ hφm hφinv
  have hL : ∫⁻ z, (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x z) ∂muF X x < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hI
    by_cases hzN : cpt X x z ∈ IW.Nset X Δ zOf ρ
    · obtain ⟨hz, hz0⟩ := hN2 z hzN
      have hzd : cpt X x z ∈ X.dom := hz
      rw [Set.indicator_of_mem hzN, testFn_dom X la P Ψ hzd, hPF z hz, hz0, zero_sub, norm_neg]
    · rw [Set.indicator_of_notMem hzN]; exact zero_le
  have hk : 0 < h 0 / 2 * c := by positivity
  have hpt : ∀ w ∈ ball (0 : V (nd X)) ρ, ENNReal.ofReal (h 0 / 2 * c) *
      ENNReal.ofReal (‖w‖ ^ (-2 * (nd X : ℝ))) ≤
      ENNReal.ofReal (densF X x1 w) * (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x1 w) := by
    intro w hw
    obtain ⟨h1, hw1, hw0, hwρ, -⟩ := hsub hw
    have hd := IW.densF_pos X x1 hw1
    have hwd : cpt X x1 w ∈ X.dom := hw1
    have hΨw : Ψ (cpt X x1 w) = Ψ (cpt X x w) := by
      rw [hx1def, IW.cpt_lact]; exact hΨΓ γ hγ _ hw0
    have hval : h w = densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X la (cpt X x1 w))) := by
      simp only [hh]
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hd]
      ring
    rw [Set.indicator_of_mem (hN1 w hw), testFn_dom X la P Ψ hwd, hΨw, ← mul_assoc,
      ← ENNReal.ofReal_mul hd.le, ← hval, ← ENNReal.ofReal_mul hk.le, mul_assoc,
      ENNReal.ofReal_mul (by positivity), neg_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h1.le) (hlow w hwρ)
  have hR1 : ENNReal.ofReal (h 0 / 2 * c) *
      ∫⁻ w in ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖w‖ ^ (-2 * (nd X : ℝ))) ≤
      ∫⁻ w, (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x1 w) ∂muF X x1 := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, IW.muF_lintegral]
    exact (setLIntegral_mono' measurableSet_ball hpt).trans
      (lintegral_mono_set fun w hw => (hsub hw).2.1)
  rw [VanishPf.crit_div hn hρ, ENNReal.mul_top (ENNReal.ofReal_pos.2 hk).ne', ← hMI] at hR1
  exact absurd (hR1.trans_lt hL) (lt_irrefl _)

end GlobalTheory.PeakOrbit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDividedSlopeWeightsBaseHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.DividedSlope

theorem strictAnti_of_adj {N : ℕ} (v : Fin N → ℝ)
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → v b < v a) : ∀ a b : Fin N, a < b → v b < v a := by
  intro a b hab
  obtain ⟨b, hb⟩ := b
  have hab' : (a : ℕ) < b := hab
  induction b, hab' using Nat.le_induction with
  | base => exact h a _ rfl
  | succ n hn ih =>
    have h1 := ih (by omega) (show (a : ℕ) < n from hn)
    have h2 := h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl
    linarith

variable {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N)

omit [Fintype ι] in
theorem T_pos (hW : W.Hyp) : (0 : ℝ) < W.T := by
  have := hW.h1
  have : 0 < W.T := by omega
  exact_mod_cast this

omit [Fintype ι] in
theorem pos_dividedSlopeWeights_baseHeight (hW : W.Hyp) : (0 : ℝ) < W.h0 := by
  have h1 := hW.h2.1
  have h2 := hW.weightConst_nonneg
  have : 0 < W.h0 := by omega
  exact_mod_cast this

omit [Fintype ι] in
theorem g_pos (hW : W.Hyp) : 0 < W.g := by
  have := T_pos W hW
  have := pos_dividedSlopeWeights_baseHeight W hW
  unfold Wts.g
  positivity

omit [Fintype ι] in
theorem g_le_of (hW : W.Hyp) {x : ℤ} (hx : W.h0 ≤ 4 * W.T * x) : W.g ≤ (x : ℝ) := by
  have hT := T_pos W hW
  have hx' : (W.h0 : ℝ) ≤ 4 * W.T * x := by exact_mod_cast hx
  unfold Wts.g
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem adj_ge (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) (hb : W.p ≤ (b : ℕ)) :
    W.g ≤ reWt W.u' τ a - reWt W.u' τ b := by
  obtain ⟨-, h2, h3⟩ := _root_.GlobalTheory.MeanTop.divided_gaps ι N W hW hD τ a b hab
  have hk := hW.kc_lt
  by_cases hp : (b : ℕ) = W.p
  · have := g_le_of W hW (h2 hp).2
    have ha : (a : ℕ) < W.p := by omega
    have hb' : ¬ (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_true, if_false]
    push_cast at this ⊢
    linarith
  · have := g_le_of W hW (h3 hp (by omega))
    have ha : ¬ (a : ℕ) < W.p := by omega
    have hb' : ¬ (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_false]
    push_cast at this ⊢
    linarith

theorem adj_lt (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) :
    reWt W.u' τ b < reWt W.u' τ a := by
  by_cases hb : W.p ≤ (b : ℕ)
  · have := adj_ge W hW hD τ a b hab hb
    have := g_pos W hW
    linarith
  · obtain ⟨h1, -, -⟩ := _root_.GlobalTheory.MeanTop.divided_gaps ι N W hW hD τ a b hab
    have h := h1 (by omega)
    have h' : W.u1 τ b < W.u1 τ a := by omega
    have ha : (a : ℕ) < W.p := by omega
    have hb' : (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_true]
    exact_mod_cast h'

theorem regular (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : a < b) :
    reWt W.u' τ b < reWt W.u' τ a :=
  strictAnti_of_adj _ (adj_lt W hW hD τ) a b hab

theorem anti (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : a ≤ b) :
    reWt W.u' τ b ≤ reWt W.u' τ a := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · exact (regular W hW hD τ a b h).le

theorem far (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (ha : W.p ≤ (a : ℕ)) (hab : a ≠ b) :
    W.g ≤ |reWt W.u' τ a - reWt W.u' τ b| := by
  have hk := hW.kc_lt
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℕ) < b := h
    have hb := b.2
    have h1 := adj_ge W hW hD τ a ⟨a + 1, by omega⟩ rfl (by simp only; omega)
    have h2 := anti W hW hD τ ⟨a + 1, by omega⟩ b (show (a : ℕ) + 1 ≤ b from h')
    exact le_trans (by linarith) (le_abs_self _)
  · have h' : (b : ℕ) < a := h
    have hb := a.2
    have h1 := adj_ge W hW hD τ ⟨a - 1, by omega⟩ a (by simp only; omega) ha
    have h2 := anti W hW hD τ b ⟨a - 1, by omega⟩ (show (b : ℕ) ≤ a - 1 by omega)
    exact le_trans (by linarith) (neg_le_abs _)

theorem entry_le (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (i : Fin N) :
    |reWt W.u' τ i| ≤ 2 * W.b / W.T := by
  have hT := T_pos W hW
  have h1 := (GlobalTheory.MeanTop.divided_entries ι N W hW hD τ i).1
  have h2 := (_root_.GlobalTheory.MeanTop.divided_weight_size ι N W hW hD).2.2 τ i
  have h3 := hW.h5 τ i
  have h1' : ((W.T : ℝ) + W.Dd + 1) * |(W.u1 τ i : ℝ)| ≤ |(W.u τ i : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h1
  have h2' : |(W.u' τ i : ℝ)| ≤ |(W.u1 τ i : ℝ)| := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ W.Dd := Nat.cast_nonneg _
  have h5 := abs_nonneg (W.u1 τ i : ℝ)
  rw [le_div_iff₀ hT]
  show |(W.u' τ i : ℝ)| * W.T ≤ 2 * W.b
  nlinarith [mul_le_mul_of_nonneg_right h2' hT.le, mul_nonneg h4 h5]

end GlobalTheory.MeanTop.DividedSlope
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresConj
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

noncomputable section

namespace GlobalTheory.SqConj

lemma wp_eq_of_sub_mem (L : PeriodPair) {z w : ℂ} (h : z - w ∈ L.lattice) :
    L.weierstrassP z = L.weierstrassP w := by
  have := L.weierstrassP_add_coe w ⟨z - w, h⟩
  simpa using this

lemma dwp_eq_of_sub_mem (L : PeriodPair) {z w : ℂ} (h : z - w ∈ L.lattice) :
    L.derivWeierstrassP z = L.derivWeierstrassP w := by
  have := L.derivWeierstrassP_add_coe w ⟨z - w, h⟩
  simpa using this

theorem sqProd_conj : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → (σ (sqProd p L t) = sqProd p L t ∧ ∃ e : Sq p ≃ Sq p, ∀ k, GlobalTheory.ConjPoint.IsConj L L σ (sqPt p t k) (sqPt p t (e k))) ∨ σ (sqProd p L t) = -sqProd p L t := by
  intro p F L t hp hp4 hp3 hD σ hσ
  obtain ⟨c, hpc, hc⟩ := _root_.GlobalTheory.CMModel.exists_conj_kernel_mul p F L t hp hp4 hp3 hD σ hσ
  obtain ⟨e, ε, hε, he⟩ := _root_.GlobalTheory.CMModel.sq_perm_mul p c hp hp4 hpc
  have hker := (_root_.GlobalTheory.CMModel.ker_sqrtNegNat_cyclic p F L t hp hp4 hp3 hD).1
  obtain ⟨hne, -⟩ := _root_.GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero p F L t hp hp4 hp3 hD
  obtain ⟨-, hodd⟩ := _root_.GlobalTheory.CMModel.card_sq_mod_prime p hp hp4
  have hmem : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) - (ε : ℂ) * sqPt p t (e k) ∈ L.lattice := by
    intro k
    have := (hker _).2 (he k)
    convert this using 1
    simp only [sqPt]
    push_cast
    ring
  have hconj : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) ∉ L.lattice ∧
      L.weierstrassP (((k.1 : ℕ) : ℂ) * ((c : ℂ) * t)) = σ (L.weierstrassP (sqPt p t k)) ∧
      L.derivWeierstrassP (((k.1 : ℕ) : ℂ) * ((c : ℂ) * t)) = σ (L.derivWeierstrassP (sqPt p t k)) := by
    intro k
    rcases hc k.1 with h | h
    · exact absurd h.1 (hne k).1
    · exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  have hσprod : σ (sqProd p L t) = ∏ k : Sq p, L.derivWeierstrassP (((k.1 : ℕ) : ℂ) * ((c : ℂ) * t)) := by
    simp only [sqProd, map_prod]
    exact Finset.prod_congr rfl fun k _ => (hconj k).2.2.symm
  rcases hε with rfl | rfl
  · left
    have hm : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) - sqPt p t (e k) ∈ L.lattice := by
      intro k; simpa using hmem k
    refine ⟨?_, e, fun k => ?_⟩
    · rw [hσprod]
      simp only [dwp_eq_of_sub_mem L (hm _)]
      exact Equiv.prod_comp e (fun k => L.derivWeierstrassP (sqPt p t k))
    · right
      refine ⟨(hne k).1, (hne (e k)).1, ?_, ?_⟩
      · rw [← wp_eq_of_sub_mem L (hm k)]; exact (hconj k).2.1
      · rw [← dwp_eq_of_sub_mem L (hm k)]; exact (hconj k).2.2
  · right
    have hm : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) - (-sqPt p t (e k)) ∈ L.lattice := by
      intro k; simpa using hmem k
    rw [hσprod]
    simp only [dwp_eq_of_sub_mem L (hm _), PeriodPair.derivWeierstrassP_neg]
    rw [Finset.prod_neg, Equiv.prod_comp e (fun k => L.derivWeierstrassP (sqPt p t k)),
      Finset.card_univ, hodd.neg_one_pow, sqProd]
    ring

end GlobalTheory.SqConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexOfLeNsmul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.HalfReps

section Group

variable {H : Type} [AddCommGroup H] [Module ℚ H] [Module.Finite ℚ H]

theorem relIndex_nsmul (Λ : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c) :
    (Λ.map (nsmulAddMonoidHom c)).relIndex Λ ≠ 0 ∧
      (Λ.map (nsmulAddMonoidHom c)).relIndex Λ ≤ c ^ Module.finrank ℚ H := by
  have : HasUniqueDiv H := HasUniqueDiv.of_module_rat H
  have : Module.Finite ℤ Λ.toIntSubmodule := hΛ
  have : Module.Free ℤ Λ.toIntSubmodule := inferInstance
  rw [AddSubgroup.relIndex_map_nsmul]
  refine ⟨pow_ne_zero _ hc.ne', Nat.pow_le_pow_right hc ?_⟩
  have hb := (Module.finBasis ℤ Λ.toIntSubmodule).linearIndependent.map' Λ.toIntSubmodule.subtype
    (Submodule.ker_subtype _)
  have := ((LinearIndependent.iff_fractionRing ℤ ℚ).1 hb).fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  exact this

theorem relIndex_of_nsmul_le (Λ B : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c)
    (hB : ∀ x ∈ B, c • x ∈ Λ) : Λ.relIndex B ≠ 0 ∧ Λ.relIndex B ≤ c ^ Module.finrank ℚ H := by
  have : HasUniqueDiv H := HasUniqueDiv.of_module_rat H
  obtain ⟨h0, h1⟩ := relIndex_nsmul Λ hΛ hc
  have hle : B.map (nsmulAddMonoidHom c) ≤ Λ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := nsmulAddMonoidHom c) Λ B (nsmul_right_injective hc.ne')]
  exact ⟨fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_right hle h),
    (AddSubgroup.relIndex_le_of_le_right hle h0).trans h1⟩

theorem relIndex_of_le_nsmul (Λ A B : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c)
    (hB : ∀ x ∈ Λ, c • x ∈ B) : B.relIndex (Λ ⊓ A) ≠ 0 := by
  obtain ⟨h0, -⟩ := relIndex_nsmul Λ hΛ hc
  have hle : Λ.map (nsmulAddMonoidHom c) ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  exact fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_left hle
    (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h))

end Group

section Twist

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
  [IsScalarTower (𝓞 E) E W]

theorem mem_twO (M : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : W) :
    y ∈ twist₂ M c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  simp [twist₂, Submodule.mem_iInf]

theorem nsmul_mem_twO (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) {e : HeightOneSpectrum (𝓞 E) → ℤ}
    (he : ∀ Q, e Q ≤ 1) {x : W} (hx : x ∈ M) : c • x ∈ twist₂ M c e := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine (mem_twO M c e _).2 fun Q => GlobalTheory.ThetaMove.mem_localization_of_mem Q ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 1 - e Q by have := he Q; omega)
  have : ((c : E) ^ e Q)⁻¹ • c • x = (c ^ m) • x := by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← zpow_natCast, ← hm,
      zpow_sub₀ hcE, zpow_one, div_eq_inv_mul]
  rw [this]
  exact nsmul_mem hx _

theorem nsmul_mem_of_twO (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) {e : HeightOneSpectrum (𝓞 E) → ℤ}
    (he : ∀ Q, -1 ≤ e Q) {x : W} (hx : x ∈ twist₂ M c e) : c • x ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine GlobalTheory.ThetaMove.mem_of_locP fun Q => ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 1 + e Q by have := he Q; omega)
  have : c • x = (c ^ m) • ((c : E) ^ e Q)⁻¹ • x := by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← zpow_natCast, ← hm,
      zpow_add₀ hcE, zpow_one, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hcE), mul_one]
  rw [this]
  exact nsmul_mem ((mem_twO M c e x).1 hx Q) _

end Twist

theorem half_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (dl : ℂ) (AA : Submodule (𝓞 E) E) (S : Finset (HeightOneSpectrum (𝓞 E))) (L : Submodule (𝓞 E) (Sp E a)) (L' : Submodule (𝓞 E) (Sp E b)) (c : ℕ), dl ≠ 0 → AA.FG → Submodule.IsFullLattice E L → Submodule.IsLattice E L' → 0 < c → Formalism.L2.Th1.H.IsReps (BC emb dl AA S L L' c) (LamC emb dl AA L L' ⊓ AC emb dl AA S L L' c) (repsOf (BC emb dl AA S L L' c) (LamC emb dl AA L L' ⊓ AC emb dl AA S L L' c)) ∧ Formalism.L2.Th1.H.IsReps (LamC emb dl AA L L') (BC emb dl AA S L L' c) (repsOf (LamC emb dl AA L L') (BC emb dl AA S L L' c)) ∧ (repsOf (LamC emb dl AA L L') (BC emb dl AA S L L' c)).card ≤ c ^ (Module.finrank ℚ E * a * b) := by
  intro E _ _ _ ι _ _ a b emb dl AA S L L' c hdl hA hL hL' hc
  have hinj := GlobalTheory.ThetaMove.embH_injective (a := a) (b := b) emb hdl
  have hfg : (perO AA L L').FG :=
    GlobalTheory.ThetaMove.VolumePos.perO_fg hA
      (GlobalTheory.ThetaMove.VolumePos.homO_fg hL.fg hL'.fg
        (Submodule.IsFullLattice.span_eq_top (self := hL)))
  have : Module.Finite (𝓞 E) (perO AA L L') := Module.Finite.iff_fg.2 hfg
  have hfin : Module.Finite ℤ (perO AA L L') := Module.Finite.trans (𝓞 E) _
  have : Module.Finite ℚ (Formalism.L2.Col.HomE E a b) := Module.Finite.trans E _
  have hrk : Module.finrank ℚ (Formalism.L2.Col.HomE E a b) = Module.finrank ℚ E * a * b := by
    rw [← Module.finrank_mul_finrank ℚ E, Module.finrank_linearMap]
    simp [mul_assoc]
  have h1 := relIndex_of_le_nsmul (perO AA L L').toAddSubgroup (halfAO S (perO AA L L') c).toAddSubgroup
    (halfBO S (perO AA L L') c).toAddSubgroup hfin hc
    (fun x hx => nsmul_mem_twO _ hc (fun Q => (GlobalTheory.ThetaMove.expS_bound S Q).2) hx)
  have h2 := relIndex_of_nsmul_le (perO AA L L').toAddSubgroup
    (halfBO S (perO AA L L') c).toAddSubgroup hfin hc
    (fun x hx => nsmul_mem_of_twO _ hc (fun Q => (GlobalTheory.ThetaMove.expS_bound S Q).1) hx)
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf _ _ _ hinj] at h1
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hrk] at h2
  have r2 := Classical.epsilon_spec (GlobalTheory.RepsMod.exists_reps _ _ h2.1)
  refine ⟨Classical.epsilon_spec (GlobalTheory.RepsMod.exists_reps _ _ h1), r2, ?_⟩
  exact (GlobalTheory.RepsMod.card_reps _ _ _ r2).le.trans h2.2

end GlobalTheory.ColNorms.HalfReps
end

