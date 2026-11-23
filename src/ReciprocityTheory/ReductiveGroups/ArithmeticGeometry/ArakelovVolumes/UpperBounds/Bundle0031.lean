module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfG

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfL
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Wpsi {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x : Frame X.Ψ r) : ℝ≥0∞ := by
  classical
  exact if x ∈ X.dom then ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))) else 0

theorem metricW_of (hR : NfacRmulStatement (E := E)) (hLa : NfacLactStatement (E := E))
    (hO : OrthoStatement (E := E)) (hLU : LUStatement (E := E)) {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (ψ : Frame X.Ψ r → ℝ) (hψ : IsInvFn X ψ)
    (hψs : ∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0))
    (hψb : ∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) :
    IsMetricW X la (Wpsi X la ψ) ∧ WLower X la (Wpsi X la ψ) := by
  classical

  have hlact1 : ∀ y : Frame X.Ψ r, lact (1 : GL (Fin r) E) y = y := by
    intro y; funext τ a c
    simp [lact, mat]
  have hψr : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    have h := hψ 1 X.Γ.one_mem x hx b hb
    rwa [hlact1] at h
  have hψl : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ψ (lact γ x) = ψ x := by
    intro γ hγ x hx
    have h := hψ γ hγ x hx (ExtFPf.oneF X) (ExtFPf.oneF_mem (X := X))
    rwa [ExtFPf.rmul_oneF] at h

  have hnpos : ∀ x ∈ X.dom, 0 < X.nfac la x := by
    intro x hx
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.mpr (div_ne_zero (ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.dmin_ne (X := X) hx τ _)
      (ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.dmin_ne (X := X) hx τ _))
  have hopen : IsOpen X.dom := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom (X := X)

  have hphr : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      0 < ‖bchar la b‖ ∧ phla X la (rmul x b) = phla X la x + 2 * Real.log ‖bchar la b‖ := by
    intro x hx b hb
    have hn := hnpos x hx
    have h1 := hnpos (rmul x b) (OntoS.dom_rmul (X := X) hx hb)
    rw [hR r X la x hx b hb] at h1
    have hinv : 0 < ‖bchar la b‖⁻¹ := by
      by_contra hc
      push_neg at hc
      nlinarith
    refine ⟨inv_pos.mp hinv, ?_⟩
    unfold phla
    rw [hR r X la x hx b hb, Real.log_mul hinv.ne' hn.ne', Real.log_inv]
    ring
  have hphl : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, phla X la (lact γ x) = phla X la x := by
    intro γ hγ x hx
    unfold phla
    rw [hLa r X la γ hγ x hx]

  have hψc : ContinuousOn ψ X.dom := by
    intro x hx
    obtain ⟨x1, ho, b, hb, hxe⟩ := hO r X x hx
    obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hdec, hcomp⟩ := hLU r X x1 ho
    have hn0 : nmat X (0 : V (nd X)) = ExtFPf.oneF X := by
      funext τ a c
      simp only [nmat, ExtFPf.oneF, Matrix.one_apply]
      split_ifs <;> first | rfl | (exfalso; subst_vars; exact lt_irrefl _ ‹_ < _›) | simp_all
    have hc0 : cpt X x1 0 = x1 := by
      unfold cpt
      rw [hn0, ExtFPf.rmul_oneF]
    have hΔx : Δ x ≠ 0 := by
      have h := (hcomp 0 (zero_mem_OmF (X := X) x1 ho) b hb).1
      rwa [hc0, ← hxe] at h
    have hUo : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
      hopen.inter (isOpen_ne_fun hΔ.continuous continuous_const)
    have hmap : Set.MapsTo zOf {y | y ∈ X.dom ∧ Δ y ≠ 0} (OmF X x1) :=
      fun y hy => (hdec y hy.1 hy.2).1
    have hcomp' : ContinuousOn ((fun z => ψ (cpt X x1 z)) ∘ zOf) {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
      (hψs x1 ho).continuousOn.comp hz.continuousOn hmap
    have heq : Set.EqOn ψ ((fun z => ψ (cpt X x1 z)) ∘ zOf) {y | y ∈ X.dom ∧ Δ y ≠ 0} := by
      intro y hy
      obtain ⟨hzy, hby, hye⟩ := hdec y hy.1 hy.2
      have hmem : cpt X x1 (zOf y) ∈ X.dom := hzy
      show ψ y = ψ (cpt X x1 (zOf y))
      exact (congrArg ψ hye).trans (hψr _ hmem _ hby)
    exact ((hcomp'.congr heq).continuousAt (hUo.mem_nhds ⟨hx, hΔx⟩)).continuousWithinAt
  have hphc : ContinuousOn (phla X la) X.dom := by
    show ContinuousOn (fun x => -2 * Real.log (X.nfac la x)) X.dom
    exact continuousOn_const.mul
      ((ExtFPf.nfac_contOn (X := X) la).log fun x hx => (hnpos x hx).ne')
  have hcont : ContinuousOn (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) X.dom :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (hphc.add hψc).neg)
  have hW : ∀ x ∈ X.dom, Wpsi X la ψ x = ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))) := by
    intro x hx
    simp [Wpsi, hx]
  have hWeq : Wpsi X la ψ = X.dom.piecewise
      (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ X.dom <;> simp [Wpsi, Set.piecewise, hx]
  unfold IsMetricW WLower
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hWeq]
    exact ContinuousOn.measurable_piecewise hcont continuousOn_const hopen.measurableSet
  · intro x hx b hb
    obtain ⟨hB, hph⟩ := hphr x hx b hb
    rw [hW _ (OntoS.dom_rmul (X := X) hx hb), hW x hx, hph, hψr x hx b hb,
      ← ENNReal.ofReal_div_of_pos (pow_pos hB 2)]
    congr 1
    rw [show -(phla X la x + 2 * Real.log ‖bchar la b‖ + ψ x)
        = -(phla X la x + ψ x) - Real.log (‖bchar la b‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_sub, Real.exp_log (pow_pos hB 2)]
  · intro γ hγ x hx
    rw [hW _ (OntoS.dom_lact (X := X) hγ hx), hW x hx, hphl γ hγ x hx, hψl γ hγ x hx]
  · obtain ⟨C, hC⟩ := hψb
    refine ⟨Real.exp (-C), Real.exp_pos _, fun x hx => ?_⟩
    rw [hW x hx, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hC x hx]))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfJ
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

namespace OntoJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Dt (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (la : Wt X.Ψ r)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X la P ∧
    ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z


open Classical in
def TL {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℂ) : Lp ℂ 2 ν :=
  if h : MemLp f 2 ν then h.toLp f else 0

section TLs

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

theorem TL_eq {f : α → ℂ} (h : MemLp f 2 ν) : TL ν f = h.toLp f := by
  unfold TL
  rw [dite_eq_left h]

theorem TL_congr {f g : α → ℂ} (hf : MemLp f 2 ν) (hfg : f =ᵐ[ν] g) : TL ν f = TL ν g := by
  rw [TL_eq hf, TL_eq (hf.ae_eq hfg)]
  exact (MemLp.toLp_eq_toLp_iff _ _).2 hfg

theorem TL_add {f g : α → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    TL ν (f + g) = TL ν f + TL ν g := by
  rw [TL_eq (hf.add hg), TL_eq hf, TL_eq hg]
  exact MemLp.toLp_add hf hg

theorem TL_sub {f g : α → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    TL ν (f - g) = TL ν f - TL ν g := by
  rw [TL_eq (hf.sub hg), TL_eq hf, TL_eq hg]
  exact MemLp.toLp_sub hf hg

theorem TL_smul {f : α → ℂ} (a : ℂ) (hf : MemLp f 2 ν) : TL ν (a • f) = a • TL ν f := by
  rw [TL_eq (hf.const_smul a), TL_eq hf]
  exact MemLp.toLp_const_smul a hf

theorem TL_zero : TL ν (0 : α → ℂ) = 0 := by
  rw [TL_eq MeasureTheory.MemLp.zero]
  exact MemLp.toLp_zero _

end TLs

variable (X : Data E r) (x0 : Frame X.Ψ r) {W : Frame X.Ψ r → ℝ≥0∞} {bb : ℝ} {la : Wt X.Ψ r}

theorem ka_cont : ContinuousOn (kaF X x0 bb) (OmF X x0) :=
  fun _ hz => (ka_contDiffAt bb hz).continuousAt.continuousWithinAt

theorem aemF (hWm : Measurable W) {F : V (nd X) → ℂ} (hF : ContinuousOn F (OmF X x0)) :
    AEMeasurable (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) (muF X x0) := by
  have h1 : ContinuousOn (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z)) (OmF X x0) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((hF.norm.pow 2).div (ka_cont X x0) fun z _ => (Real.exp_pos _).ne')
  have h2 : Measurable fun z => W (cpt X x0 z) := hWm.comp (cd_cpt X x0).continuous.measurable
  have h3 : AEMeasurable (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z))
      (volume.restrict (OmF X x0)) :=
    (h1.aemeasurable (isOpen_OmF X x0).measurableSet).mul h2.aemeasurable
  exact h3.mono_ac (withDensity_absolutelyContinuous _ _)

theorem Dt_zero : Dt X x0 W bb la (fun _ => 0) (fun _ => 0) := by
  refine ⟨differentiableOn_const _, ?_, ⟨differentiableOn_const _, fun _ _ _ _ => by simp⟩, fun _ _ => rfl⟩
  unfold InAt
  simp

theorem Dt_add (hWm : Measurable W) {F1 F2 : V (nd X) → ℂ} {P1 P2 : Frame X.Ψ r → ℂ}
    (h1 : Dt X x0 W bb la F1 P1) (h2 : Dt X x0 W bb la F2 P2) :
    Dt X x0 W bb la (fun z => F1 z + F2 z) (fun y => P1 y + P2 y) := by
  refine ⟨h1.1.add h2.1, ?_, ⟨h1.2.2.1.1.add h2.2.2.1.1, fun x hx b hb => ?_⟩, fun z hz => ?_⟩
  · unfold InAt
    refine lt_of_le_of_lt (lint_add_le (k := kaF X x0 bb) (fun z => Real.exp_pos _)
      (aemF X x0 hWm h1.1.continuousOn)) ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) h1.2.1, ENNReal.mul_lt_top (by simp) h2.2.1⟩
  · beta_reduce
    rw [h1.2.2.1.2 x hx b hb, h2.2.2.1.2 x hx b hb]
    ring
  · beta_reduce
    rw [h1.2.2.2 z hz, h2.2.2.2 z hz]

theorem Dt_smul (a : ℂ) {F : V (nd X) → ℂ} {P : Frame X.Ψ r → ℂ} (h : Dt X x0 W bb la F P) :
    Dt X x0 W bb la (fun z => a * F z) (fun y => a * P y) := by
  refine ⟨h.1.const_mul a, ?_, ⟨h.2.2.1.1.const_mul a, fun x hx b hb => ?_⟩, fun z hz => ?_⟩
  · have heq : ∀ z, ENNReal.ofReal (‖a * F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) =
        ENNReal.ofReal (‖a‖ ^ 2) * (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := by
      intro z
      rw [norm_mul, mul_pow, mul_div_assoc, ENNReal.ofReal_mul (by positivity), mul_assoc]
    unfold InAt
    simp_rw [heq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.2.1
  · beta_reduce
    rw [h.2.2.1.2 x hx b hb]
    ring
  · beta_reduce
    rw [h.2.2.2 z hz]

end OntoJ

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

section V

variable {n : ℕ} {U : Set (V n)}

def twoLog {N M : ℕ} (a c : ℝ) (w : Fin N → V n → ℂ) (s : Fin M → V n → ℂ) (y : V n) : ℝ :=
  a * Real.log (∑ k, Complex.normSq (w k y)) + c * Real.log (∑ k, Complex.normSq (s k y))

theorem sumSq_cdAt {N : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} (hw : ∀ k, DifferentiableOn ℂ (w k) U)
    {y : V n} (hy : y ∈ U) : ContDiffAt ℝ ∞ (fun v => ∑ k, Complex.normSq (w k v)) y :=
  ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (HE.contDiffAt_of_punct hU (hw k) hy)

theorem twoLog_cdAt {N M : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} {s : Fin M → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hs : ∀ k, DifferentiableOn ℂ (s k) U) (a c : ℝ)
    {y : V n} (hy : y ∈ U) (hwp : 0 < ∑ k, Complex.normSq (w k y)) (hsp : 0 < ∑ k, Complex.normSq (s k y)) :
    ContDiffAt ℝ ∞ (twoLog a c w s) y := by
  unfold twoLog
  exact (contDiffAt_const.mul ((sumSq_cdAt hU hw hy).log hwp.ne')).add
    (contDiffAt_const.mul ((sumSq_cdAt hU hs hy).log hsp.ne'))

theorem logSum_levi_nonneg {N : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hwp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (w k y))
    {y : V n} (hy : y ∈ U) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun v => ((Real.log (∑ k, Complex.normSq (w k v)) : ℝ) : ℂ)) y ξ).re :=
  lseV n N U (fun k v => Complex.normSq (w k v)) hU
    (fun k => Or.inr ⟨w k, ((contDiffOn_of_differentiableOn n (w k) U hU (hw k)).of_le HE.two_le_inf),
      fun _ _ => rfl⟩) hwp y hy ξ

theorem twoLog_levi_nonneg {N M : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} {s : Fin M → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hwp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (w k y)) (hsp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (s k y))
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {y : V n} (hy : y ∈ U) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun v => ((twoLog a c w s v : ℝ) : ℂ)) y ξ).re := by
  have h1 : ContDiffAt ℝ 2 (fun v => Real.log (∑ k, Complex.normSq (w k v))) y :=
    ((sumSq_cdAt hU hw hy).log (hwp y hy).ne').of_le HE.two_le_inf
  have h2 : ContDiffAt ℝ 2 (fun v => Real.log (∑ k, Complex.normSq (s k v))) y :=
    ((sumSq_cdAt hU hs hy).log (hsp y hy).ne').of_le HE.two_le_inf
  have e : (fun v => ((twoLog a c w s v : ℝ) : ℂ)) = fun v =>
      ((a * Real.log (∑ k, Complex.normSq (w k v)) + c * Real.log (∑ k, Complex.normSq (s k v)) : ℝ) : ℂ) := rfl
  rw [e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h1) (contDiffAt_const.mul h2),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h1, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have := logSum_levi_nonneg hU hw hwp hy ξ
  have := logSum_levi_nonneg hU hs hsp hy ξ
  positivity

end V

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem pnorm_eq (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl

theorem exp_neg_phla (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
  have hn : 0 < X.nfac la x := by
    unfold Data.nfac
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.mpr (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))
  unfold phla
  rw [neg_mul, neg_neg, show 2 * Real.log (X.nfac la x) = Real.log (X.nfac la x ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

theorem pnorm_sq (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P x ^ 2 = Complex.normSq (P x) * Real.exp (-phla X la x) := by
  rw [pnorm_eq, mul_pow, exp_neg_phla X la hx, Complex.normSq_eq_norm_sq]

theorem sum_pnorm_sq {N : ℕ} (la : Wt X.Ψ r) (P : Fin N → Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∑ k, X.pnorm la (P k) x ^ 2 = (∑ k, Complex.normSq (P k x)) * Real.exp (-phla X la x) := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => pnorm_sq X la (P k) hx)

theorem phla_add_nsmul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la1 la2 : Wt X.Ψ r) (k : ℕ) :
    phla X (la1 + k • la2) x = phla X la1 x + k * phla X la2 x := by
  rw [IW.phla_eq X hx, IW.phla_eq X hx, IW.phla_eq X hx, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  push_cast
  ring

variable {X}

def PsK (Xa : ArchInM X) (Fl : FlatM X Xa) (x : Frame X.Ψ r) : ℝ :=
  phla X (Xa.Fp + Xa.T • Xa.L) x + (Xa.T : ℝ) * Real.log (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) +
    ((Xa.T : ℝ) - 1 / 2) * Real.log ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) / ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2)

theorem sumw_pos (Xa : ArchInM X) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, Complex.normSq (Xa.w k x) := by
  obtain ⟨k, hk⟩ := Xa.w_nz x hx
  exact lt_of_lt_of_le (Complex.normSq_pos.2 hk)
    (Finset.single_le_sum (f := fun k => Complex.normSq (Xa.w k x)) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ k))

theorem sums_pos {Xa : ArchInM X} (Fl : FlatM X Xa) {x : Frame X.Ψ r} {k0 : Fin (nd X)}
    (h : Fl.s k0 x ≠ 0) : 0 < ∑ k, Complex.normSq (Fl.s k x) :=
  lt_of_lt_of_le (Complex.normSq_pos.mpr h)
    (Finset.single_le_sum (f := fun k => Complex.normSq (Fl.s k x)) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ k0))

theorem PsK_eq (Xa : ArchInM X) (Fl : FlatM X Xa) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : 0 < ∑ k, Complex.normSq (Fl.s k x)) :
    PsK Xa Fl x = phla X Xa.Fp x + ((1 / 2 : ℝ) * Real.log (∑ k, Complex.normSq (Xa.w k x)) +
      ((Xa.T : ℝ) - 1 / 2) * Real.log (∑ k, Complex.normSq (Fl.s k x))) := by
  have hw := sumw_pos Xa hx
  have he : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  unfold PsK
  rw [sum_pnorm_sq X _ _ hx, sum_pnorm_sq X _ _ hx, phla_add_nsmul X hx, mul_div_mul_right _ _ he.ne',
    Real.log_mul hw.ne' he.ne', Real.log_exp, Real.log_div hs.ne' hw.ne']
  ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem WSk_eq_exp (Xa : ArchInM X) (Fl : FlatM X Xa) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : 0 < ∑ k, Complex.normSq (Fl.s k x)) :
    WSk X Xa Fl x = ENNReal.ofReal (Real.exp (-PsK Xa Fl x)) := by
  have hw := sumw_pos Xa hx
  have he : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  have hA : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
    rw [sum_pnorm_sq X _ _ hx]; positivity
  have hS : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 := by
    rw [sum_pnorm_sq X _ _ hx]; positivity
  have hR : 0 < (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) / ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := div_pos hS hA
  unfold WSk
  rw [if_pos hx, ENNReal.ofReal_rpow_of_pos hA, ENNReal.ofReal_rpow_of_pos hR,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hR, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold PsK
  ring

def Uk {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) : Set (V (nd X)) :=
  {z | z ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 z) ≠ 0}

theorem s_diffOn {Xa : ArchInM X} (Fl : FlatM X Xa) (k : Fin (nd X)) : DifferentiableOn ℂ (Fl.s k) X.dom :=
  (Fl.s_van k).1.1.1.1

theorem w_diffOn (Xa : ArchInM X) (k : Fin Xa.N) : DifferentiableOn ℂ (Xa.w k) X.dom :=
  (Xa.w_van k).1.1.1.1

theorem isOpen_Uk {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) :
    IsOpen (Uk Fl x0 k0) :=
  HE.isOpen_punct (ExF.isOpen_OmF X x0) (IW.comp_cpt_diffOn X (s_diffOn Fl k0) x0)

theorem PsK_cpt_eventually {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) :
    (fun v => PsK Xa Fl (cpt X x0 v)) =ᶠ[𝓝 z] fun v => phla X Xa.Fp (cpt X x0 v) +
      twoLog (1 / 2) ((Xa.T : ℝ) - 1 / 2) (fun k v => Xa.w k (cpt X x0 v)) (fun k v => Fl.s k (cpt X x0 v)) v := by
  filter_upwards [(isOpen_Uk Fl x0 k0).mem_nhds hz] with v hv
  rw [PsK_eq Xa Fl hv.1 (sums_pos Fl hv.2)]
  rfl

theorem twoLog_cpt_cdAt {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) (a c : ℝ) :
    ContDiffAt ℝ ∞ (twoLog a c (fun k v => Xa.w k (cpt X x0 v)) (fun k v => Fl.s k (cpt X x0 v))) z :=
  twoLog_cdAt (ExF.isOpen_OmF X x0) (fun k => IW.comp_cpt_diffOn X (w_diffOn Xa k) x0)
    (fun k => IW.comp_cpt_diffOn X (s_diffOn Fl k) x0) a c hz.1 (sumw_pos Xa hz.1) (sums_pos Fl hz.2)

theorem PsK_cpt_cdAt {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) : ContDiffAt ℝ ∞ (fun v => PsK Xa Fl (cpt X x0 v)) z :=
  ((IW.phla_cpt_cdAt X x0 hz.1 Xa.Fp).add (twoLog_cpt_cdAt Fl x0 k0 hz _ _)).congr_of_eventuallyEq
    (PsK_cpt_eventually Fl x0 k0 hz)

theorem PsK_levi {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) (m : ℝ)
    (hm : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ)
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) (ξ : Fin (nd X) → ℂ) :
    m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
      (leviV (nd X) (fun w => ((PsK Xa Fl (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re := by
  have hT : (0 : ℝ) ≤ (Xa.T : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ Xa.T := by
      have h1 := Xa.T_ge
      have h2 := Xa.n_ge
      have : 1 ≤ Xa.T := by nlinarith
      exact_mod_cast this
    linarith
  set tl := twoLog (1 / 2) ((Xa.T : ℝ) - 1 / 2) (fun k v => Xa.w k (cpt X x0 v))
    (fun k v => Fl.s k (cpt X x0 v)) with htl
  have hev : (fun w => ((PsK Xa Fl (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => (((phla X Xa.Fp (cpt X x0 w) + (-1) * Real.log (densF X x0 w)) + tl w : ℝ) : ℂ) := by
    filter_upwards [PsK_cpt_eventually Fl x0 k0 hz] with w hw
    rw [hw]
    push_cast
    ring
  have h1 := (IW.phla_cpt_cdAt X x0 hz.1 Xa.Fp).of_le HE.two_le_inf
  have h2 := (IW.logDens_cdAt X x0 hz.1).of_le HE.two_le_inf
  have h3 := (twoLog_cpt_cdAt Fl x0 k0 hz (1 / 2) ((Xa.T : ℝ) - 1 / 2)).of_le HE.two_le_inf
  have hU := isOpen_Uk Fl x0 k0
  have hpos : 0 ≤ (leviV (nd X) (fun v => ((tl v : ℝ) : ℂ)) z ξ).re :=
    twoLog_levi_nonneg hU (fun k => (IW.comp_cpt_diffOn X (w_diffOn Xa k) x0).mono fun v hv => hv.1)
      (fun k => (IW.comp_cpt_diffOn X (s_diffOn Fl k) x0).mono fun v hv => hv.1)
      (fun v hv => sumw_pos Xa hv.1) (fun v hv => sums_pos Fl hv.2) (by norm_num) hT hz ξ
  have hmz := hm z hz.1 ξ
  rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (h1.add (contDiffAt_const.mul h2)) h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h2), Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  unfold leviRh leviO leviM leviDens at hmz
  linarith

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
end

