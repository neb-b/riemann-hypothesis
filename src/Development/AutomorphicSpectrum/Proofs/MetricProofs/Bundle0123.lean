module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0020
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0115
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0110

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeHeightLimit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Local

variable {e : ℕ} {X : Type} [TopologicalSpace X] {I : Type} [Fintype I]

theorem holoOn_mono (A : FinHolAtlas e X) {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hs : V ⊆ U) :
    A.HoloOn V g :=
  fun j w hw => h j w ⟨hw.1, hs hw.2⟩

theorem continuousOn_of_holoOn (A : FinHolAtlas e X) {U : Set X} {s : X → I → ℂ}
    (hU : IsOpen U) (hs : ∀ p, A.HoloOn U fun y => s y p) : ContinuousOn s U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  refine ContinuousAt.continuousWithinAt (continuousAt_pi.2 fun p => ?_)
  have hw : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j y) ∈ U
      rw [(A.chart j).left_inv hj]; exact hy⟩
  have h1 : ContinuousAt ((fun y => s y p) ∘ (A.chart j).symm) (A.chart j y) :=
    (hs p j _ hw).continuousAt
  have h2 : ContinuousAt (A.chart j) y := (A.chart j).continuousAt hj
  have h3 : ContinuousAt (((fun y => s y p) ∘ (A.chart j).symm) ∘ A.chart j) y :=
    ContinuousAt.comp h1 h2
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(A.chart j).left_inv hy']

theorem log_norm_section_local (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {s : X → I → ℂ}
    (hs : ∀ p, A.HoloOn U fun y => s y p) {y₀ : X} (hy₀ : y₀ ∈ U) {T : (I → ℂ) → ℂ}
    (hT : AnalyticAt ℂ T (s y₀)) (hT0 : T (s y₀) ≠ 0) {Q : (I → ℂ) → Prop}
    (hQ : ∀ᶠ z in 𝓝 (s y₀), Q z) :
    ∃ U' : Set X, IsOpen U' ∧ y₀ ∈ U' ∧ U' ⊆ U ∧ (∀ y ∈ U', Q (s y)) ∧ ∃ G : X → ℂ, A.HoloOn U' G ∧
      ∀ y ∈ U', Real.log ‖T (s y)‖ = (G y).re := by
  set L : (I → ℂ) → ℂ := fun z => Complex.log (T z / T (s y₀)) with hL
  have hLa : AnalyticAt ℂ L (s y₀) := by
    refine (hT.div analyticAt_const hT0).clog ?_
    simp [hT0]
  have hev : ∀ᶠ z in 𝓝 (s y₀), AnalyticAt ℂ L z ∧ T z ≠ 0 ∧ Q z :=
    hLa.eventually_analyticAt.and ((hT.continuousAt.eventually_ne hT0).and hQ)
  obtain ⟨N, hNsub, hNo, hzN⟩ := mem_nhds_iff.1 hev
  have hc := continuousOn_of_holoOn A hU hs
  refine ⟨U ∩ s ⁻¹' N, hc.isOpen_inter_preimage hU hNo, ⟨hy₀, hzN⟩, Set.inter_subset_left,
    fun y hy => (hNsub hy.2).2.2, fun y => L (s y) + (Real.log ‖T (s y₀)‖ : ℂ), ?_, ?_⟩
  · intro j w hw
    have hsw : AnalyticAt ℂ (fun w => s ((A.chart j).symm w)) w :=
      analyticAt_pi_iff.2 fun p => hs p j w ⟨hw.1, hw.2.1⟩
    have hcomp : AnalyticAt ℂ (fun w => L (s ((A.chart j).symm w))) w :=
      AnalyticAt.comp (f := fun w => s ((A.chart j).symm w)) (hNsub hw.2.2).1 hsw
    exact hcomp.add analyticAt_const
  · intro y hy
    have hTy := (hNsub hy.2).2.1
    simp only [hL, Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hTy) (norm_ne_zero_iff.2 hT0)]
    ring

end Local

section Slots

variable {X : Type} [TopologicalSpace X] {e : ℕ}

theorem positionPot_lt (th Pn : LocPot X) (f : X → ℝ) {i : ℕ} {j : Fin e} (hj : (j : ℕ) < i) :
    positionPot th Pn f i j = th + LocPot.ofFun f := by
  simp [positionPot, hj]

theorem positionPot_ge (th Pn : LocPot X) (f : X → ℝ) {i : ℕ} {j : Fin e} (hj : ¬ (j : ℕ) < i) :
    positionPot th Pn f i j = Pn + LocPot.ofFun fun _ => 0 := by
  simp [positionPot, hj]

theorem add_ofFun_U (P : LocPot X) (u : X → ℝ) (x : X) :
    (P + LocPot.ofFun u).U x = P.U x ∩ Set.univ := rfl

theorem add_ofFun_φ (P : LocPot X) (u : X → ℝ) (x y : X) :
    (P + LocPot.ofFun u).φ x y = P.φ x y + u y := rfl

end Slots

section Vertical

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

theorem sum_log_vertFactor_local (D : ComponentData II Ψ K J Ω W) (M : XModel D) (F : Finset ℕ)
    (hF : ∀ p ∈ F, p ∈ D.S) {U : Set M.Xc} (hU : IsOpen U) {s : M.Xc → (Σ k, J k) → ℂ}
    (hs : ∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y)) (hh : ∀ p, M.atlas.HoloOn U fun y => s y p)
    {y₀ : M.Xc} (hy₀ : y₀ ∈ U) :
    ∃ U' : Set M.Xc, IsOpen U' ∧ y₀ ∈ U' ∧ U' ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U' G ∧
      ∀ y ∈ U', ∑ p ∈ F, Real.log (D.vertFactor p (s y)) = (G y).re := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨U, hU, hy₀, subset_rfl, fun _ => 0, fun j w _ => analyticAt_const, fun y _ => by simp⟩
  | insert p F hp ih =>
    obtain ⟨U₁, hU₁, hy₁, hs₁, G₁, hG₁, hre₁⟩ := ih fun q hq => hF q (Finset.mem_insert_of_mem hq)
    obtain ⟨T, hT, hT0, hev⟩ := GroundTheory.Heights₂.Heights.NineStatements.NbarLeviChartReg.vertFactor_local D
      (hF p (Finset.mem_insert_self p F)) (hs y₀ hy₀)
    obtain ⟨U₂, hU₂, hy₂, hs₂, hQ, G₂, hG₂, hre₂⟩ := log_norm_section_local M.atlas hU hh hy₀ hT hT0 hev
    refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hy₁, hy₂⟩, fun y hy => hs₁ hy.1, fun y => G₂ y + G₁ y, ?_, ?_⟩
    · intro j w hw
      exact (hG₂ j w ⟨hw.1, hw.2.2⟩).add (hG₁ j w ⟨hw.1, hw.2.1⟩)
    · intro y hy
      rw [Finset.sum_insert hp, hQ y hy.2 (hs y (hs₂ hy.2)), hre₂ y hy.2, hre₁ y hy.1, Complex.add_re]

end Vertical

theorem ptsIntegral_word_eq_mInt : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb Bm : HermLine J) (Pn : ReciprocityTheory.AnForm.M.LocPot M.Xc) (i : ℕ) (f G₀ : M.Xc → ℝ) (g : ((Σ k, J k) → ℂ) → ℝ), ReciprocityTheory.AnForm.M.IsPotential M.atlas Pn → (∀ x, ∀ y₀ ∈ (Pn).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pn).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, J k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Pn).φ x y' - (fun z => Real.log (Nb.h z)) (s y') = (G y').re) → M.atlas.SmoothOn S.R.Yo f → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → Real.log (Bm.h z) = Real.log (S.ref.h z) + f (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z)) → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → g z = G₀ (M.proj z)) → (∀ j, MeasureTheory.AEStronglyMeasurable (G₀ ∘ (M.atlas.chart j).symm) (MeasureTheory.volume.restrict (M.atlas.chart j).target)) → ReciprocityTheory.AnForm.M.MIntegrable M.atlas (positionPot S.R.th Pn f i) G₀ → ptsIntegral (mCoordIdeal D.y) (pot fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb) g = ReciprocityTheory.AnForm.M.mInt M.atlas (positionPot S.R.th Pn f i) G₀ := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B Nb Bm Pn i f G₀ g hPot hPn hf hBm hg hG₀ hInt
  obtain ⟨hYo, hnull, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part D.n M.Xc M.atlas S.R
  have hex : ∃ Q : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (D.n + 1) → ℂ), IsGoodProj (mCoordIdeal D.y) Q :=
    goodProjExists K J _ D.n D.arith
  have hnull' : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (S.R.Yoᶜ ∪ ∅)) = 0 := by
    intro j
    rw [Set.union_empty]
    exact hnull j
  have hN : IsPtsNull (mCoordIdeal D.y) D.n (∅ : Set ((Σ k, J k) → ℂ)) := fun _ _ => by simp
  have hsm : ∀ (j : Fin D.n) x, M.atlas.SmoothOn ((positionPot S.R.th Pn f i j).U x ∩ S.R.Yo)
      ((positionPot (e := D.n) S.R.th Pn f i j).φ x) := by
    intro j x a
    by_cases hj : (j : ℕ) < i
    · rw [positionPot_lt _ _ _ hj, add_ofFun_U]
      have s1 : (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' ((S.R.th.U x ∩ Set.univ) ∩ S.R.Yo) ⊆
          (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' S.R.th.U x := fun w hw => ⟨hw.1, hw.2.1.1⟩
      have s2 : (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' ((S.R.th.U x ∩ Set.univ) ∩ S.R.Yo) ⊆
          (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' S.R.Yo := fun w hw => ⟨hw.1, hw.2.2⟩
      exact ((S.R.th_pot.1 x a).mono s1).add ((hf a).mono s2)
    · rw [positionPot_ge _ _ _ hj, add_ofFun_U]
      have s1 : (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' ((Pn.U x ∩ Set.univ) ∩ S.R.Yo) ⊆
          (M.atlas.chart a).target ∩ (M.atlas.chart a).symm ⁻¹' Pn.U x := fun w hw => ⟨hw.1, hw.2.1.1⟩
      exact ((hPot.1 x a).mono s1).add contDiffOn_const
  have hloc : ∀ (j : Fin D.n), ∀ x, ∀ y₀ ∈ (positionPot (e := D.n) S.R.th Pn f i j).U x ∩ S.R.Yo,
      ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (positionPot (e := D.n) S.R.th Pn f i j).U x ∩ S.R.Yo ∧
        ∃ s : M.Xc → (Σ k, J k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧
          (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧
            ∀ y' ∈ U, (positionPot (e := D.n) S.R.th Pn f i j).φ x y' -
              (fun z => (1 : ℝ) * Real.log ((if (j : ℕ) < i then Bm else Nb).h z)) (s y') = (G y').re := by
    intro j x y₀ hy
    by_cases hj : (j : ℕ) < i
    · rw [positionPot_lt _ _ _ hj, add_ofFun_U] at hy
      rw [positionPot_lt _ _ _ hj, add_ofFun_U]
      simp only [if_pos hj, _root_.one_mul, add_ofFun_φ]
      obtain ⟨hyU, hyY⟩ := hy
      obtain ⟨U, hUo, hyU', hUs, s, hs, hh, G, hG, hre⟩ := S.th_ref x y₀ hyU.1
      obtain ⟨U₂, hU₂o, hy₂, hU₂s, G₂, hG₂, hre₂⟩ := sum_log_vertFactor_local D M (D.SB B)
        (fun p hp => (Finset.mem_filter.1 hp).1) (hUo.inter hYo) (s := s) (fun y hy => (hs y hy.1).1)
        (fun p => holoOn_mono _ (hh p) Set.inter_subset_left) ⟨hyU', hyY⟩
      refine ⟨U₂, hU₂o, hy₂, fun y hy => ⟨⟨hUs (hU₂s hy).1, trivial⟩, (hU₂s hy).2⟩, s,
        fun y hy => hs y (hU₂s hy).1, fun p => holoOn_mono _ (hh p) fun y hy => (hU₂s hy).1,
        fun y => G y - G₂ y, ?_, ?_⟩
      · intro a w hw
        exact (hG a w ⟨hw.1, (hU₂s hw.2).1⟩).sub (hG₂ a w hw)
      · intro y hy
        have hmem := hs y (hU₂s hy).1
        have hpY : M.proj (s y) ∈ S.R.Yo := by
          rw [hmem.2]
          exact (hU₂s hy).2
        have e1 := hBm (s y) hmem.1 hpY
        rw [hmem.2] at e1
        have e2 := hre y (hU₂s hy).1
        have e3 := hre₂ y hy
        rw [e1, Complex.sub_re]
        linarith
    · rw [positionPot_ge _ _ _ hj, add_ofFun_U] at hy
      rw [positionPot_ge _ _ _ hj, add_ofFun_U]
      simp only [if_neg hj, _root_.one_mul, add_ofFun_φ, add_zero]
      obtain ⟨hyU, hyY⟩ := hy
      obtain ⟨U, hUo, hyU', hUs, s, hs, hh, G, hG, hre⟩ := hPn x y₀ hyU
      exact ⟨U ∩ S.R.Yo, hUo.inter hYo, ⟨hyU', hyY⟩, fun y hy => ⟨hUs hy.1, hy.2⟩, s,
        fun y hy => hs y hy.1, fun p => holoOn_mono _ (hh p) Set.inter_subset_left, G,
        holoOn_mono _ hG Set.inter_subset_left, fun y hy => hre y hy.1⟩
  have hmain := _root_.GlobalTheory.CompanionTheory.Ar.Giv.push_chart_integrals K J (mCoordIdeal D.y) D.n M hex.choose S.R.Yo ∅ ∅ (fun _ => 1)
    (fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb) (positionPot S.R.th Pn f i) g G₀ D.arith hex.choose_spec
    hYo hnull' hN hsm hloc (fun z hz _ hY _ => hg z hz hY) hG₀
  have h := (hmain.2.2 hInt).2
  have hfun : (fun (j : Fin D.n) z => (1 : ℝ) * Real.log ((if (j : ℕ) < i then Bm else Nb).h z)) =
      pot fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb := by
    funext j z
    simp [pot]
  unfold ptsIntegral
  rw [dite_eq_left hex, ← hfun]
  exact h

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHolds
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.SignedConv

theorem zero_member {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X)
    (s : X → X → ℂ) (C₅ C t₁ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ)
    (hs : ∀ y, logNormSec L s y ≤ 0) (hC₅ : 0 ≤ C₅) (hC : 0 ≤ C) (ht₁ : 0 < t₁)
    (hte : t₁ ≤ Real.exp (-Real.exp 1)) :
    IsSingWeight A L s (LocPot.ofFun 0) 0 C₅ ∧
      IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) C t₁ ∧ IsRegFamilyC2 A s 0 (fun _ => 0) :=
  _root_.GlobalTheory.CompanionTheory.Ar.Giv.zeroMember_isRegFamily A Θ L s C₅ C t₁ hΘ hΘp hs hC₅ hC ht₁ hte

theorem eventually_isPsh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ)
    (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (hth : IsPotential A th)
    (hF : IsRegFamily A Θ L s th ph phT C t₀) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) ∧ IsPsh A (th + LocPot.ofFun (phT t) + Θ) :=
  GlobalTheory.T.regular_family_eventually_smooth_psh A Θ L s th ph phT C t₀ hΘ hΘp hth hF

theorem isPshOn_add_psh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X)
    (P : LocPot X) (f : X → ℝ) (Θ : LocPot X) (hU : IsOpen U) (hP : IsPotential A P)
    (hΘ : IsPotential A Θ) (hf : A.SmoothOn U f) (hPf : IsPshOn A U (P + LocPot.ofFun f))
    (hΘp : IsPsh A Θ) : IsPshOn A U (P + LocPot.ofFun f + Θ) :=
  GlobalTheory.T.psh_add_psh_potential_on_open A U P f Θ hU hP hΘ hf hPf hΘp

theorem expand_mInt {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X)
    (g : X → ℝ) (hU : IsOpen U) (hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0)
    (hP : ∀ i, IsPotential A (P i)) (hΘ : IsPotential A Θ) (hf : ∀ i, A.SmoothOn U (f i))
    (hT : ∀ T : Finset (Fin e), MIntegrable A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
      LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g) :
    MIntegrable A (fun i => P i + LocPot.ofFun (f i)) g ∧
      mInt A (fun i => P i + LocPot.ofFun (f i)) g = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        mInt A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g :=
  _root_.GlobalTheory.CompanionTheory.Metric.ExpandMInt.expand_mInt A U P f Θ g hU hnull hP hΘ hf hT

theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw; rw [levi_zero]
  · exact (h x j y hy w hw).le

theorem isPshOn_of_isPsh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (U : Set X) (P : LocPot X) (h : IsPsh A P) : IsPshOn A U P :=
  fun x j y hy w => h x j y ⟨hy.1, hy.2.1⟩ w

theorem smoothOn_of_smooth {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (U : Set X) (f : X → ℝ) (h : A.Smooth f) : A.SmoothOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.subset_univ U)))

theorem isSingWeight_abs {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (C₅ : ℝ)
    (hs : ∀ y, logNormSec L s y ≤ 0) (h : IsSingWeight A L s th ph C₅) :
    IsSingWeight A L s th ph |C₅| := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  obtain ⟨a, b⟩ := h4 y hy
  have hr : 1 ≤ Real.log (rW L s y) := by
    have h5 := rW_ge L s hs y
    have h6 := Real.log_le_log (Real.exp_pos 1) h5
    rwa [Real.log_exp] at h6
  have h7 := mul_nonneg (sub_nonneg.2 (le_abs_self C₅)) (le_trans zero_le_one hr)
  exact ⟨by nlinarith, b.trans (le_abs_self _)⟩

theorem chart_null {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X) (hS : IsSection A L s)
    (hSNC : IsSNC A L s m W) (j : Fin A.n) :
    volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜᶜ) = 0 := by
  rw [compl_compl]
  have hAn : A.IsAnalyticSubset (bdry s) := by
    intro x
    refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩
  have := analyticNull A (bdry s) hAn (LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC) j
  rwa [Set.inter_comm, (A.chart j).image_source_inter_eq'] at this

theorem convergenceSigned : ConvergenceSignedStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hΘp hL hS hSNC hs th ph phT C₅ C t₀ hSW hRF hC2 g gT C₆
    hgc hgb hlim
  have hΘpsh : IsPsh A Θ := isPsh_of_isPosPot A Θ hΘp
  have hUo : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl
  have hnull := chart_null A L s m W hS hSNC
  have hmem : ∀ T : Finset (Fin e),
      (∀ i, IsSingWeight A L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) |C₅|) ∧
      (∀ i, IsRegFamily A Θ L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0) |C|
        (min t₀ (Real.exp (-Real.exp 1)))) ∧
      (∀ i, IsRegFamilyC2 A s (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0)) := by
    intro T
    have hz : ∀ i : Fin e, IsSingWeight A L s (LocPot.ofFun 0) 0 |C₅| ∧
        IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) |C| (min t₀ (Real.exp (-Real.exp 1))) ∧
        IsRegFamilyC2 A s 0 (fun _ => 0) := fun i =>
      zero_member A Θ L s |C₅| |C| _ hΘ hΘp hs (abs_nonneg _) (abs_nonneg _)
        (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_right _ _)
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;> by_cases hi : i ∈ T <;>
      simp only [hi, ↓reduceIte]
    · exact isSingWeight_abs A L s _ _ _ hs (hSW i)
    · exact (hz i).1
    · exact isRegFamily_mono A Θ L s (th i) (ph i) (phT i) C t₀ |C| _ hΘ hΘpsh (hSW i).1 hs (hRF i)
        le_rfl (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_left _ _) (min_le_right _ _)
    · exact (hz i).2.1
    · exact hC2 i
    · exact (hz i).2.2
  have hconv := fun T : Finset (Fin e) => _root_.GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds A Θ L s m W hΘ hΘp hL hS hSNC hs
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0)
    (fun i t => if i ∈ T then phT i t else 0) |C₅| |C| _ (hmem T).1 (hmem T).2.1 (hmem T).2.2
    g gT C₆ hgc hgb hlim
  have hgcont : ContinuousOn g (bdry s)ᶜ := hlim.continuousOn (Eventually.of_forall hgc).frequently
  have hlimT := fun T : Finset (Fin e) => _root_.GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null A (bdry s)ᶜ
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0) Θ hUo hnull
    (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => ((hmem T).1 i).2.1)
    (fun i => isPshOn_add_psh A _ _ _ Θ hUo ((hmem T).1 i).1 hΘ ((hmem T).1 i).2.1
      ((hmem T).1 i).2.2.1 hΘpsh) g hgcont (hconv T).2.2.1
  have hexpL := expand_mInt A (bdry s)ᶜ th ph Θ g hUo hnull (fun i => (hSW i).1) hΘ
    (fun i => (hSW i).2.1) (fun T => (hlimT T).1)
  refine ⟨hexpL.1, ?_⟩
  rw [hexpL.2]
  have htend : Tendsto (fun t => ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
      ∫ y, gT t y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        mInt A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then ph i else 0) + Θ) g)) := by
    refine tendsto_finsetSum _ fun T _ => ?_
    rw [(hlimT T).2]
    exact ((hconv T).2.2.2.2).const_mul _
  refine htend.congr' ?_
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (∀ i, A.Smooth (phT i t)) ∧
      ∀ T : Finset (Fin e), (∀ i, A.Smooth (if i ∈ T then phT i t else 0) ∧
        IsPsh A ((if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) ∧
        Integrable (gT t) (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) := by
    refine (eventually_all.2 fun i => ?_).and (eventually_all.2 fun T => ?_)
    · exact (eventually_isPsh A Θ L s (th i) (ph i) (phT i) C t₀ hΘ hΘp (hSW i).1 (hRF i)).mono
        fun t ht => ht.1
    · refine (eventually_all.2 fun i => ?_).and (hconv T).2.2.2.1
      exact eventually_isPsh A Θ L s _ _ _ _ _ hΘ hΘp ((hmem T).1 i).1 ((hmem T).2.1 i)
  filter_upwards [hev] with t ht
  have hmt := fun T : Finset (Fin e) => _root_.GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null A (bdry s)ᶜ
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then phT i t else 0) Θ hUo hnull
    (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => smoothOn_of_smooth A _ _ ((ht.2 T).1 i).1)
    (fun i => isPshOn_of_isPsh A _ _ ((ht.2 T).1 i).2) (gT t) (hgc t) (ht.2 T).2
  rw [(expand_mInt A (bdry s)ᶜ th (fun i => phT i t) Θ (gT t) hUo hnull (fun i => (hSW i).1) hΘ
    (fun i => smoothOn_of_smooth A _ _ (ht.1 i)) (fun T => (hmt T).1)).2]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [(hmt T).2]

end GlobalTheory.CompanionTheory.Ar.Giv.SignedConv
end

