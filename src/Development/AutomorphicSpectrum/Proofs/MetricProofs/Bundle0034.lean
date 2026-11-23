module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import Development.WeilBound.CoreStatements.AmpleLineBundles.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricQuotientOfMultihomogPair
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Decay

open Filter Topology

theorem analyticAt_aeval {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {v : E → σ → ℂ} {z : E}
    (hv : ∀ p, AnalyticAt ℂ (fun w => v w p) z) (q : MvPolynomial σ ℤ) :
    AnalyticAt ℂ (fun w => (aeval (v w) q : ℂ)) z := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, aeval_X]
    exact hp.mul (hv i)

theorem continuousAt_of_chart {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
    (c : OpenPartialHomeomorph X E) {x : X} (hx : x ∈ c.source) {F : X → Y}
    (h : ContinuousAt (fun z => F (c.symm z)) (c x)) : ContinuousAt F x := by
  have h1 : ContinuousAt (fun y => F (c.symm (c y))) x :=
    ContinuousAt.comp (f := c) (g := fun z => F (c.symm z)) h (c.continuousAt hx)
  refine h1.congr ?_
  filter_upwards [c.open_source.mem_nhds hx] with y hy
  rw [c.left_inv hy]

theorem isOpen_multicone {K : Type*} [Finite K] {ι : K → Type*} :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem eventually_abs_le {X : Type*} [TopologicalSpace X] {u : X → ℝ} {x : X} (h : ContinuousAt u x) :
    ∀ᶠ y in 𝓝 x, |u y| ≤ |u x| + 1 :=
  (h.abs.eventually_lt (continuousAt_const (y := |u x| + 1)) (by linarith)).mono fun _ hy => hy.le

theorem section_zero {e : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) {x x' y : X} (hy : y ∈ L.U x ∩ L.U x') (h0 : s x y = 0) :
    s x' y = 0 := by
  have h := hs.2 x x' y hy
  rw [h0, norm_zero, zero_mul] at h
  exact norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right (Real.exp_ne_zero _))

theorem logNormSec_eq {e : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) {x y : X} (hy : y ∈ L.U x) (h0 : s x y ≠ 0) :
    logNormSec L s y = Real.log ‖s x y‖ - L.φ x y := by
  unfold logNormSec
  rw [hs.2 y x y ⟨L.mem_U y, hy⟩, Real.log_mul (norm_ne_zero_iff.2 h0) (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem log_ratio_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (Eh : HermLine ι)
    {dg dh : K → ℕ} {G Hf : MRing ι} (hG : IsMultiHomog G dg) (hH : IsMultiHomog Hf dh)
    (hdeg : ∀ k, (dg k : ℤ) = dh k + Eh.a k) (t : K → ℂ) (ht : ∀ k, t k ≠ 0) (w : (Σ k, ι k) → ℂ)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hGw : aeval w G ≠ (0 : ℂ)) (hHw : aeval w Hf ≠ (0 : ℂ)) :
    Real.log ‖(aeval w G : ℂ) / aeval w Hf‖ - Real.log (Eh.h w) =
      Real.log ‖(aeval (fun p => t p.1 * w p) G : ℂ) / aeval (fun p => t p.1 * w p) Hf‖ -
        Real.log (Eh.h fun p => t p.1 * w p) := by
  rw [aeval_scale hG, aeval_scale hH, Eh.smul t w ht]
  have hT : 0 < ∏ k, ‖t k‖ ^ Eh.a k := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (ht k)) _
  have hP : ‖∏ k, t k ^ dg k‖ = ‖∏ k, t k ^ dh k‖ * ∏ k, ‖t k‖ ^ Eh.a k := by
    simp only [norm_prod, norm_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, hdeg k, zpow_add₀ (norm_ne_zero_iff.2 (ht k)), zpow_natCast]
  have hPh : ‖∏ k, t k ^ dh k‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k))
  have hn : ‖((∏ k, t k ^ dg k) * aeval w G : ℂ) / ((∏ k, t k ^ dh k) * aeval w Hf)‖ =
      (∏ k, ‖t k‖ ^ Eh.a k) * ‖(aeval w G : ℂ) / aeval w Hf‖ := by
    rw [norm_div, norm_mul, norm_mul, hP, norm_div]
    field_simp
  have hq : ‖(aeval w G : ℂ) / aeval w Hf‖ ≠ 0 := norm_ne_zero_iff.2 (div_ne_zero hGw hHw)
  rw [hn, Real.log_mul hT.ne' hq, Real.log_mul hT.ne' (Eh.pos w hw).ne']
  ring

theorem decay_arith {N : ℕ} (hN : 0 < N) {Lf lh lg φ lC Bh Bφ : ℝ} (h1 : (N : ℝ) * Lf ≤ lC + lg)
    (h2 : |lh| ≤ Bh) (h3 : |φ| ≤ Bφ) :
    Lf - lh ≤ -(1 / (2 * (N : ℝ))) * (Real.exp 1 - 2 * (lg - φ)) +
      ((lC + Real.exp 1 / 2 + Bφ) / (N : ℝ) + Bh) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have e1 : Lf ≤ (lC + lg) / N := by
    rw [le_div_iff₀ hn]
    linarith
  have e2 : -(1 / (2 * (N : ℝ))) * (Real.exp 1 - 2 * (lg - φ)) + (lC + Real.exp 1 / 2 + Bφ) / N =
      (lC + lg) / N + (Bφ - φ) / N := by
    field_simp
    ring
  have e3 : 0 ≤ (Bφ - φ) / N := div_nonneg (by linarith [le_abs_self φ]) hn.le
  have e4 : -lh ≤ Bh := by linarith [neg_abs_le lh]
  linarith

theorem local_decay : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → (∀ y : R.X, aeval (R.lift y y) G ≠ (0 : ℂ) → aeval (R.lift y y) Hf ≠ (0 : ℂ) → π y ∈ S.open') → ∀ x₀ : R.X, aeval (R.lift x₀ x₀) Hf ≠ (0 : ℂ) → ∃ (V : Set R.X) (N : ℕ) (C : ℝ), IsOpen V ∧ x₀ ∈ V ∧ 0 < N ∧ ∀ y ∈ V, aeval (R.lift y y) Hf ≠ (0 : ℂ) ∧ (π y ∈ S.open' → aeval (R.lift y y) G ≠ (0 : ℂ) → Real.log ‖(aeval (R.lift y y) G : ℂ) / aeval (R.lift y y) Hf‖ - Real.log (Eh.h (R.lift y y)) ≤ -(1 / (2 * (N : ℝ))) * rW S.L S.s (π y) + C) := by
  intro K _ ι _ P J e R σ S π hπ Eh hEh dg dh G Hf hG hH hdeg hyp x₀ hx₀
  obtain ⟨j, hj⟩ := R.A.cover x₀
  obtain ⟨k, hk⟩ := S.A.cover (π x₀)
  have hz₀ : (R.A.chart j).symm (R.A.chart j x₀) = x₀ := (R.A.chart j).left_inv hj
  have hd₀ : (S.A.chart k).symm (S.A.chart k (π x₀)) = π x₀ := (S.A.chart k).left_inv hk
  have hcoord : ∀ p, AnalyticAt ℂ (fun z => R.lift x₀ ((R.A.chart j).symm z) p) (R.A.chart j x₀) := fun p =>
    R.holo x₀ p j _ ⟨(R.A.chart j).map_source hj, by
      show (R.A.chart j).symm (R.A.chart j x₀) ∈ R.U x₀
      rw [hz₀]; exact R.mem_U x₀⟩
  have hGa := analyticAt_aeval hcoord G
  have hHa := analyticAt_aeval hcoord Hf
  have hHc : ContinuousAt (fun y => (aeval (R.lift x₀ y) Hf : ℂ)) x₀ :=
    continuousAt_of_chart (R.A.chart j) hj hHa.continuousAt
  have hne : ∀ᶠ y in 𝓝 x₀, (aeval (R.lift x₀ y) Hf : ℂ) ≠ 0 := hHc.eventually_ne hx₀
  have hU : ∀ᶠ y in 𝓝 x₀, y ∈ R.U x₀ := (R.isOpen_U x₀).mem_nhds (R.mem_U x₀)
  have hS : ∀ᶠ y in 𝓝 x₀, y ∈ (R.A.chart j).source := (R.A.chart j).open_source.mem_nhds hj
  have hπc : ContinuousAt π x₀ := hπ.1.continuousAt
  have hπU : ∀ᶠ y in 𝓝 x₀, π y ∈ S.L.U (π x₀) :=
    hπc.eventually_mem ((S.L.isOpen_U _).mem_nhds (S.L.mem_U _))
  have hπk : ∀ᶠ y in 𝓝 x₀, π y ∈ (S.A.chart k).source :=
    hπc.eventually_mem ((S.A.chart k).open_source.mem_nhds hk)
  have tend : Tendsto (R.A.chart j).symm (𝓝 (R.A.chart j x₀)) (𝓝 x₀) := by
    have h := (R.A.chart j).continuousAt_symm ((R.A.chart j).map_source hj)
    rwa [ContinuousAt, hz₀] at h

  let f : (Fin e → ℂ) → ℂ := fun z =>
    (aeval (R.lift x₀ ((R.A.chart j).symm z)) G : ℂ) / aeval (R.lift x₀ ((R.A.chart j).symm z)) Hf
  let g : (Fin e → ℂ) → ℂ := fun z => S.s (π x₀) (π ((R.A.chart j).symm z))
  have hf : AnalyticAt ℂ f (R.A.chart j x₀) := hGa.div hHa (by simpa only [hz₀] using hx₀)
  have hg : AnalyticAt ℂ g (R.A.chart j x₀) := by
    have h1 : AnalyticAt ℂ ((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀) :=
      hπ.2 j k _ ⟨(R.A.chart j).map_source hj, by
        show π ((R.A.chart j).symm (R.A.chart j x₀)) ∈ (S.A.chart k).source
        rw [hz₀]; exact hk⟩
    have h2 : AnalyticAt ℂ (S.s (π x₀) ∘ (S.A.chart k).symm)
        (((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀)) := by
      have e1 : ((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀) = S.A.chart k (π x₀) := by
        simp only [Function.comp_apply, hz₀]
      rw [e1]
      exact S.sec.1 (π x₀) k _ ⟨(S.A.chart k).map_source hk, by
        show (S.A.chart k).symm (S.A.chart k (π x₀)) ∈ S.L.U (π x₀)
        rw [hd₀]; exact S.L.mem_U _⟩
    refine (h2.comp h1).congr ?_
    filter_upwards [tend.eventually hπk] with z hz
    simp only [Function.comp_apply, g, (S.A.chart k).left_inv hz]

  have hzero : ∀ᶠ z in 𝓝 (R.A.chart j x₀), g z = 0 → f z = 0 := by
    filter_upwards [tend.eventually hU, tend.eventually hπU, tend.eventually hne] with z h1 h2 h3 h0
    obtain ⟨t, ht, hlt⟩ := R.compat x₀ _ _ ⟨h1, R.mem_U ((R.A.chart j).symm z)⟩
    have hs := section_zero S.sec (x := π x₀) (x' := π ((R.A.chart j).symm z))
      ⟨h2, S.L.mem_U _⟩ h0
    have hHy : (aeval (R.lift ((R.A.chart j).symm z) ((R.A.chart j).symm z)) Hf : ℂ) ≠ 0 := by
      intro h00
      apply h3
      rw [hlt, aeval_scale hH, h00, mul_zero]
    have hGy : (aeval (R.lift ((R.A.chart j).symm z) ((R.A.chart j).symm z)) G : ℂ) = 0 := by
      by_contra hG0
      exact hyp _ hG0 hHy hs
    show (aeval (R.lift x₀ ((R.A.chart j).symm z)) G : ℂ) / _ = 0
    rw [hlt, aeval_scale hG, hGy, mul_zero, zero_div]
  obtain ⟨N, C₀, hN, hloj⟩ := GlobalTheory.T.lojasiewicz_inequality_analytic e f g _ hf hg hzero
  have hloj' : ∀ᶠ y in 𝓝 x₀, ‖f (R.A.chart j y)‖ ^ N ≤ C₀ * ‖g (R.A.chart j y)‖ :=
    ((R.A.chart j).continuousAt hj).eventually hloj

  have hφc : ContinuousAt (S.L.φ (π x₀)) (π x₀) :=
    continuousAt_of_chart (S.A.chart k) hk
      (((S.potL.1 (π x₀) k).continuousOn).continuousAt
        (((S.A.chart k).isOpen_inter_preimage_symm (S.L.isOpen_U _)).mem_nhds
          ⟨(S.A.chart k).map_source hk, by
            show (S.A.chart k).symm (S.A.chart k (π x₀)) ∈ S.L.U (π x₀)
            rw [hd₀]; exact S.L.mem_U _⟩))
  have hφb := eventually_abs_le (u := fun y => S.L.φ (π x₀) (π y)) (ContinuousAt.comp (g := S.L.φ (π x₀)) hφc hπc)
  have hℓ : ContinuousAt (fun y => R.lift x₀ y) x₀ :=
    continuousAt_pi.2 fun p => continuousAt_of_chart (R.A.chart j) hj (hcoord p).continuousAt
  have hmem : R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := (R.mem x₀ x₀ (R.mem_U x₀)).1
  have hhc : ContinuousAt Eh.h (R.lift x₀ x₀) :=
    (ContDiffOn.continuousOn hEh).continuousAt (isOpen_multicone.mem_nhds hmem)
  have hlogc : ContinuousAt (fun y => Real.log (Eh.h (R.lift x₀ y))) x₀ :=
    ContinuousAt.log (ContinuousAt.comp (g := Eh.h) hhc hℓ) (Eh.pos _ hmem).ne'
  have hhb := eventually_abs_le hlogc
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.1
    (hU.and (hS.and (hπU.and (hne.and (hloj'.and (hφb.and hhb))))))
  refine ⟨V, N, (Real.log (max C₀ 1) + Real.exp 1 / 2 + (|S.L.φ (π x₀) (π x₀)| + 1)) / (N : ℝ) +
    (|Real.log (Eh.h (R.lift x₀ x₀))| + 1), hVo, hxV, hN, fun y hy => ?_⟩
  obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := hV y hy
  obtain ⟨t, ht, hlt⟩ := R.compat x₀ y y ⟨y1, R.mem_U y⟩
  have hw : ∀ k, ∃ i, R.lift y y ⟨k, i⟩ ≠ 0 := (R.mem y y (R.mem_U y)).1
  have hHy : (aeval (R.lift y y) Hf : ℂ) ≠ 0 := by
    intro h00
    apply y4
    rw [hlt, aeval_scale hH, h00, mul_zero]
  refine ⟨hHy, fun hop hGy => ?_⟩
  have hs : S.s (π y) (π y) ≠ 0 := hop
  have hgne : S.s (π x₀) (π y) ≠ 0 := fun h0 => hs (section_zero S.sec ⟨y3, S.L.mem_U _⟩ h0)
  have hGl : (aeval (R.lift x₀ y) G : ℂ) ≠ 0 := by
    rw [hlt, aeval_scale hG]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)) hGy
  have hfy : f (R.A.chart j y) = (aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf := by
    simp only [f, (R.A.chart j).left_inv y2]
  have hgy : g (R.A.chart j y) = S.s (π x₀) (π y) := by
    simp only [g, (R.A.chart j).left_inv y2]
  rw [hfy, hgy] at y5
  have hfne : (aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf ≠ 0 := div_ne_zero hGl y4
  have key := log_ratio_scale Eh hG hH hdeg t ht (R.lift y y) hw hGy hHy
  rw [← hlt] at key
  rw [key, rW, logNormSec_eq S.sec y3 hgne]
  have hloglog : (N : ℝ) * Real.log ‖(aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf‖ ≤
      Real.log (max C₀ 1) + Real.log ‖S.s (π x₀) (π y)‖ := by
    have hC : 0 < max C₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hgp : 0 < ‖S.s (π x₀) (π y)‖ := norm_pos_iff.2 hgne
    have hle : ‖(aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf‖ ^ N ≤
        max C₀ 1 * ‖S.s (π x₀) (π y)‖ :=
      y5.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgp.le)
    have := Real.log_le_log (pow_pos (norm_pos_iff.2 hfne) N) hle
    rwa [Real.log_pow, Real.log_mul hC.ne' hgp.ne'] at this
  exact decay_arith hN hloglog y7 y6

end GlobalTheory.CompanionTheory.Ar.Small.Decay
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorSumIdentityBaseChange
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.MinorAny

theorem minorIJ_map {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S)
    (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · exact (map_zero f).symm

def gap {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) (S : Type) [CommRing S] [Algebra Ω S]
    (h : Matrix (Fin N) (Fin N) S) : S :=
  algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J -
    algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J

theorem gap_map {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) {S S' : Type} [CommRing S] [Algebra Ω S]
    [CommRing S'] [Algebra Ω S'] (f : S →ₐ[Ω] S') (h : Matrix (Fin N) (Fin N) S) :
    f (gap T c₀ c₁ coef u J S h) = gap T c₀ c₁ coef u J S' (h.map f.toRingHom) := by
  have hm : ∀ (M : Matrix (Fin N) (Fin N) S) (I J : Finset (Fin N)),
      f (minorIJ M I J) = minorIJ (M.map f.toRingHom) I J :=
    fun M I J => (minorIJ_map f.toRingHom M I J).symm
  have hT : (T.map (algebraMap Ω S) * h).map f.toRingHom = T.map (algebraMap Ω S') * h.map f.toRingHom := by
    rw [Matrix.map_mul, Matrix.map_map]
    congr 1
    congr 1
    funext x
    exact f.commutes x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gap, map_sub, map_mul, map_sum, AlgHom.commutes, hm, hT]

theorem minor_any : ∀ (Ω : Type) [Field Ω] [Infinite Ω] (N j : ℕ) (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω) (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)), (∀ h : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j h → c₀ * ∑ I, coef I * minorIJ (T * h) I J = c₁ * ∑ I, u I * minorIJ h I J) → ∀ (S : Type) [CommRing S] [Algebra Ω S] (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J = algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J := by
  intro Ω _ _ N j T c₀ c₁ coef u J hyp S _ _ h hh
  have hT : T.map (algebraMap Ω Ω) = T := Matrix.ext fun _ _ => rfl
  have key : ∀ M : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j M → gap T c₀ c₁ coef u J Ω M = 0 := by
    intro M hM
    simp only [gap, hT]
    exact sub_eq_zero.mpr (hyp M hM)
  let G : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) Ω) :=
    Matrix.of fun a b => if ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then X (a, b) else 0
  have hP : gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G = 0 := by
    apply MvPolynomial.funext
    intro x
    show aeval x (gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G) = aeval x 0
    rw [map_zero, gap_map]
    apply key
    intro a b hab
    simp only [G, Matrix.map_apply, Matrix.of_apply, if_neg hab, map_zero]
  have hG : G.map (aeval (fun p : Fin N × Fin N => h p.1 p.2)).toRingHom = h := by
    ext a b
    simp only [G, Matrix.map_apply, Matrix.of_apply]
    split_ifs with hab
    · simp [aeval_X]
    · rw [map_zero]
      exact (hh a b hab).symm
  have hz := congrArg (aeval (fun p : Fin N × Fin N => h p.1 p.2)) hP
  rw [gap_map, hG, map_zero] at hz
  simp only [gap] at hz
  exact sub_eq_zero.mp hz

end GlobalTheory.CompanionTheory.Ar.PB.MinorAny
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeBoundedMap
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.MapCompare

theorem main : ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ), Function.Injective φ → 0 < c → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) → (∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c) ∧ E.slopeMax ≤ E'.slopeMax + ((Real.log c / 2 : ℝ) : EReal) :=
  CoverDenseAlt.normDegree_le_of_metric_bounded_map

end GlobalTheory.CompanionTheory.Ar.MapCompare
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def v₀ (k₀ : K) (p : Σ k, ι k) : Σ o : Option K, ι (o.getD k₀) := ⟨some p.1, p.2⟩

def v₁ (k₀ : K) (p : Σ k, ι k) : Σ o : Option K, ι (o.getD k₀) :=
  if h : p.1 = k₀ then ⟨none, cast (congrArg ι h) p.2⟩ else ⟨some p.1, p.2⟩

theorem v₁_ne {k₀ : K} {p : Σ k, ι k} (h : p.1 ≠ k₀) : v₁ k₀ p = ⟨some p.1, p.2⟩ := dif_neg h

theorem v₁_self (k₀ : K) (m : ι k₀) : v₁ k₀ ⟨k₀, m⟩ = ⟨none, m⟩ := dif_pos rfl

def fstPt (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : (Σ k, ι k) → ℂ := z ∘ v₀ k₀

def sndPt (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : (Σ k, ι k) → ℂ := z ∘ v₁ k₀

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def normRhs (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (z₀ z₁ : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) : ℝ :=
  Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) *
      (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
        else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ +
    (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁))

def IsNormFn (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) {e : ℕ}
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (f : RW.X → ℝ) : Prop :=
  ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F →
    M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ (fstPt k₀ (RW.lift x x)) →
    SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 →
    (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) →
    f x = normRhs M τ a F z₀ z₁ h t

def IsWChart (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X)
    (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e)
    (F : FrameData ι Ψ N M.Ω M.blk) (H : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsCompatChart RW.A ψ ∧ M.IsFrame F ∧ (∀ i, σ i ≠ i₀) ∧
    (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) ∧
    (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) ψ.target) ∧
    ∀ x' ∈ ψ.source, (∀ τ', IsBlockDiag j (H τ' (ψ x')) ∧ (H τ' (ψ x')).det ≠ 0) ∧
      M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ (RW.lift x' x')))) ∧
      ∃ z₀ z₁ : (Σ k, ι k) → ℂ, SameOrbit z₀ (fstPt k₀ (RW.lift x' x')) ∧ SameOrbit z₁ (sndPt k₀ (RW.lift x' x')) ∧
        ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z₀ (H τ' (ψ x')) ∧
          ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z₁ (if τ' = τ then H τ (ψ x') * (1 + Matrix.single cb ca (ψ x' i₀)) else H τ' (ψ x'))

def IsWAtlas (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) : Prop :=
  HoloMap RW.A Rb.A pr ∧
    (∀ x, SameOrbit (Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) ∧
    ∀ x, ∃ ψ kb σ i₀ F H, x ∈ ψ.source ∧ IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H

def IsFibreChart {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N) (ca cb : Fin N)
    {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) : Prop :=
  ∃ (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X),
    (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) Un) ∧
    ContinuousOn bp Un ∧ (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) ∧
    (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s ∧ ∀ τ', IsBlockDiag j (H τ' w) ∧ (H τ' w).det ≠ 0) ∧
    (∀ w ∈ Un, ∀ r s : Fin 2, Gn w r s =
      minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca))
          (insert (![ca, cb] s) ((stepCols N j a).erase ca)) /
        minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) ∧
    (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∀ x₀, FA.Re.π x₀ = ΦYn z → ∃ z₀ : (Σ k, ι k) → ℂ,
      SameOrbit (FA.Re.R.lift x₀ x₀) z₀ ∧ SameOrbit (basePart M.blk z₀) (BM.Rb.lift (bp (Fin.tail z)) (bp (Fin.tail z))) ∧
      ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) z₀
        (if τ' = τ then H τ (Fin.tail z) * (1 + Matrix.single cb ca (z 0)) else H τ' (Fin.tail z))) ∧
    ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un →
      q 0 (ΦWn z) = ΦYn (Fin.cons (z 0) (Fin.tail (Fin.tail z))) ∧ q 1 (ΦWn z) = ΦYn (Fin.tail z)

theorem pullback_pullback {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (P : LocPot X)
    (f : Y → X) (g : Z → Y) (r : Z → X) (hf : Continuous f) (hg : Continuous g) (hr : Continuous r) (h : f ∘ g = r) :
    (P.pullback f hf).pullback g hg = P.pullback r hr := by
  subst h
  rfl

theorem orbit_symm {κ : Type} [Fintype κ] {ρ : κ → Type} {z z' : (Σ k, ρ k) → ℂ}
    (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  rw [inv_mul_cancel_left₀ (hc p.1)]

theorem orbit_trans {κ : Type} [Fintype κ] {ρ : κ → Type} {z z' z'' : (Σ k, ρ k) → ℂ}
    (h : SameOrbit z z') (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  rw [mul_assoc]

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginMultiplicityBound
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

theorem combLine_ref_a_eq_line_a : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)) (n₀ m : Option (RootIx D) → ℤ), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → (∀ r : RootIx D, (m (some r) : ℝ) = (Fx.kA * Fx.q' : ℕ) * fundCo (nu r.1) r.2) → m none = -(Fx.q' : ℤ) → (combLine Or.Re.ref m).a = (combLine (RM.line 1) n₀).a := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or nu n₀ m hn hn₀ hn₀' hm hm'
  funext k₁
  apply Int.cast_injective (α := ℝ)
  have hL : ∀ r : RootIx D, ((m (some r) * (Or.Re.ref (some r)).a k₁ : ℤ) : ℝ) =
      -(((Fx.kA * Fx.q' : ℕ) : ℝ) * (fundCo (nu r.1) r.2 * ∑ k ∈ Finset.Iic r.2, (RM.xdeg (r.1, k) k₁ : ℝ))) := by
    rintro ⟨τ, i⟩
    rw [Or.fund_deg τ i]
    push_cast
    rw [hm (τ, i)]
    simp only [Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum, Nat.cast_mul]
    ring
  have hR : ∀ r : RootIx D, ((n₀ (some r) * (RM.line 1 (some r)).a k₁ : ℤ) : ℝ) =
      -(((Fx.kA * Fx.q' : ℕ) : ℝ) * (nu r.1 r.2 * (RM.xdeg r k₁ : ℝ))) := by
    intro r
    have h1 : (RM.line 1 (some r)).a = RM.xdeg r := RM.x_deg 1 r
    rw [h1, hn₀ r]
    push_cast
    have := hn r
    push_cast at this
    rw [this]
    ring
  have hsum : ∑ r : RootIx D, ((m (some r) * (Or.Re.ref (some r)).a k₁ : ℤ) : ℝ) =
      ∑ r : RootIx D, ((n₀ (some r) * (RM.line 1 (some r)).a k₁ : ℤ) : ℝ) := by
    simp only [hL, hR, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    congr 2
    exact Finset.sum_congr rfl fun τ _ => sum_fundCo_mul_sum_Iic (nu τ) fun k => (RM.xdeg (τ, k) k₁ : ℝ)
  have hnone : (Or.Re.ref none).a k₁ = (RM.line 1 none).a k₁ := by
    rw [Or.ref_none.1]
    rfl
  simp only [combLine, Fintype.sum_option, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hm', hn₀', hnone]
  push_cast at hsum ⊢
  rw [hsum]

end GlobalTheory.CompanionTheory.Ar.Small.Fund
end
end

