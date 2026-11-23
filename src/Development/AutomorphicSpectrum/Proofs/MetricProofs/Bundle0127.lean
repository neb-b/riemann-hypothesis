module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0124
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0142
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0031
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0048
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0125
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSheetSimpleNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open MeasureTheory CxInt CxComp

theorem cxSheetSimpleNull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) ∧
      ¬ cxSimple (conePts Q) Ψ w} = 0 := by
  intro K _ ι _ Q e Ψ hQ hΨ
  obtain ⟨d, hbd, hnull⟩ := cxGenericCount hQ Ψ hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (cxSimple_of_count hbd hgood.1 hgood.2 hw)

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EvCEqZeroIffOfSameOrbit
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Build

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem evC_torus {f : MRing ι} {b : K → ℕ} (hf : IsMultiHomog f b) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    evC (fun p => c p.1 * z p) f = (∏ k, c k ^ b k) * evC z f := by
  classical
  simp only [evC, eval_map]
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∏ p : Σ k, ι k, c p.1 ^ m p = ∏ k, c k ^ b k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ b k
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  simp only [mul_pow, Finset.prod_mul_distrib, h1]
  ring

theorem evC_eq_zero_iff_of_sameOrbit {f : MRing ι} {b : K → ℕ} (hf : IsMultiHomog f b)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : evC z f = 0 ↔ evC z' f = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  have h0 : ∏ k, c k ^ b k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  rw [evC_torus hf]
  simp [h0]

theorem evC_rename (v : (Σ k, ι k) → Σ k, ι' k) (z : (Σ k, ι' k) → ℂ) (f : MRing ι) :
    evC z (rename v f) = evC (fun p => z (v p)) f := by
  rw [evC, map_rename, eval_rename]
  rfl

theorem evC_mul (z : (Σ k, ι k) → ℂ) (f g : MRing ι) : evC z (f * g) = evC z f * evC z g := by
  simp [evC]

theorem sum_mapDomain {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : ∀ p, (v p).1 = κ p.1)
    [DecidableEq K'] (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf, hg]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  | single p n =>
    have hR : (∑ q : Σ k, ι k, if κ q.1 = k' then (Finsupp.single p n) q else 0) =
        if κ p.1 = k' then n else 0 := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq
        simp [Finsupp.single_apply, Ne.symm hq]
      · simp
    have hL : ∀ q : Σ k, ι' k, ∑ i, (Finsupp.single q n) ⟨k', i⟩ = if q.1 = k' then n else 0 := by
      rintro ⟨kq, iq⟩
      by_cases h : kq = k'
      · subst h
        simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, h]
    rw [Finsupp.mapDomain_single, hL, hR, hv]

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) {f : MRing ι}
    {b : K → ℕ} (hf : IsMultiHomog f b) : IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  classical
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [sum_mapDomain hb.2.2.1, Fintype.sum_sigma]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, Finset.sum_eq_single k]
    · simpa using hf m₀ hm₀ k
    · intro k₂ _ hne
      exact Finset.sum_eq_zero fun i _ => if_neg (hb.1.ne hne)
    · simp
  · rw [Function.extend_apply' _ _ _ hk]
    exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => if_neg fun h => hk ⟨k, h⟩

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m₁ h₁ k, hg m₂ h₂ k]

end Forms

section Sides

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]

theorem exists_bdry_form {P₁ : Ideal (MRing ι₁)} {D : ℕ} {σ : Type} {S : AnSys D σ} (Re : Realis S P₁)
    (h : AlgOver Re) : ∃ (γ : MRing ι₁) (c : K₁ → ℕ), IsMultiHomog γ c ∧ γ ∉ P₁ ∧
      ∀ x, Re.π x ∈ bdry S.s → evC (Re.R.lift x x) γ = 0 := by
  obtain ⟨K₀, _, ι₀, _, κ, v, U, lam, β, b, hb, -, hor, hβ, hn, hz⟩ := h
  refine ⟨rename v β, Function.extend κ b 0, isMultiHomog_rename hb hβ, hn, fun x hx => ?_⟩
  rw [evC_rename, ← evC_eq_zero_iff_of_sameOrbit hβ (hor x)]
  exact hz _ hx

theorem side {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} (hb : IsBlockMap κ₁ v₁) {P J : Ideal (MRing ι)}
    {D : ℕ} {σ : Type} {S : AnSys D σ} {P₁ : Ideal (MRing ι₁)} (Re : Realis S P₁) (e : imageZ v₁ P = P₁)
    (R : AnLogRes P J D) (har : IsArithVar P (D + 1)) (alg : AlgOver Re) :
    ∃ (π : R.X → S.X) (hπ : HoloMap R.A S.A π),
      (∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁) ∧
      (∀ a (ref' : HermLine ι), IsPullHerm κ₁ v₁ (Re.ref a) ref' →
        SamePot R.A Set.univ (potOf R ref') ((S.th a).pullback π hπ.1)) ∧
      (∀ a t, 0 < t → t ≤ S.t₀ → ∀ x, Real.log ((Re.line a t).h fun p => R.lift x x (v₁ p)) =
        Real.log ((Re.ref a).h fun p => R.lift x x (v₁ p)) + S.phT a t (π x)) := by
  subst e
  obtain ⟨π, hπ, h1, h2, h3, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Pull.realis_pullback K ι K₁ ι₁ κ₁ v₁ P J D σ S Re R hb har alg
  exact ⟨π, hπ, h1, h2, h3⟩

theorem evC_bdry {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} (hb : IsBlockMap κ₁ v₁) {P J : Ideal (MRing ι)}
    {D : ℕ} {σ : Type} {S : AnSys D σ} {P₁ : Ideal (MRing ι₁)} (Re : Realis S P₁) (e : imageZ v₁ P = P₁)
    (R : AnLogRes P J D) {π : R.X → S.X}
    (hπ : ∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁)
    {γ : MRing ι₁} {c : K₁ → ℕ} (hγ : IsMultiHomog γ c)
    (hz : ∀ x, Re.π x ∈ bdry S.s → evC (Re.R.lift x x) γ = 0) (x : R.X) (hx : π x ∈ bdry S.s) :
    evC (R.lift x x) (rename v₁ γ) = 0 := by
  have hmem : (fun p => R.lift x x (v₁ p)) ∈ mcPts P₁ :=
    e ▸ (_root_.GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap K₁ ι₁ K ι κ₁ v₁ hb).2.2.1 P _ (R.mem x x (R.mem_U x))
  obtain ⟨x₁, hx₁⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.resolution_onto_complex_points K₁ ι₁ P₁ _ D Re.R Re.arith _ hmem
  rw [evC_rename, ← evC_eq_zero_iff_of_sameOrbit hγ hx₁]
  exact hz x₁ (hπ x x₁ hx₁ ▸ hx)

end Sides

section Assemble

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

end Assemble

end GlobalTheory.CompanionTheory.Ar.Cmp.Build
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousMetricRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.Descent

open ReciprocityTheory.AnForm.M

section General
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem holoOn_continuousOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X}
    {f : X → ℂ} (hU : IsOpen U) (h : A.HoloOn U f) : ContinuousOn f U := by
  intro t ht
  obtain ⟨j, hj⟩ := A.cover t
  have h1 : AnalyticAt ℂ (f ∘ (A.chart j).symm) (A.chart j t) :=
    h j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using ht⟩
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) t :=
    ContinuousAt.comp h1.continuousAt ((A.chart j).continuousAt hj)
  have h3 : ((f ∘ (A.chart j).symm) ∘ A.chart j) =ᶠ[𝓝 t] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with u hu
    simp [(A.chart j).left_inv hu]
  exact (h2.congr h3).continuousWithinAt

theorem exists_continuous_descent {P : Ideal (MRing J)} {d : ℕ} (M : CxModel P d)
    (F : ((Σ k, J k) → ℂ) → ℝ) (hF : ContinuousOn F {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (hinv : ∀ (c : K → ℂ), (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, F (torusSmul c z) = F z) :
    ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts P, κ (M.proj z) = F z := by
  choose r hr hpr using M.surj
  have key : ∀ z ∈ mcPts P, F (r (M.proj z)) = F z := by
    intro z hz
    obtain ⟨c, hc, e⟩ := (M.fibre _ (hr _) z hz).1 (hpr _)
    calc F (r (M.proj z)) = F (torusSmul c (r (M.proj z))) := (hinv c hc _ (hr _)).symm
      _ = F z := by rw [← e]
  refine ⟨fun x => F (r x), ?_, key⟩
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hx, s, hs, hh⟩ := M.sections x
  have hsc : ContinuousOn s U := continuousOn_pi.2 fun p => holoOn_continuousOn hU (hh p)
  have hcomp : ContinuousOn (F ∘ s) U := hF.comp hsc fun y hy => (hs y hy).1.1
  refine (hcomp.continuousAt (hU.mem_nhds hx)).congr ?_
  filter_upwards [hU.mem_nhds hx] with y hy
  have h := key (s y) (hs y hy).1
  rw [(hs y hy).2] at h
  exact h.symm

theorem log_h_torusSmul (A : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h (torusSmul c z)) = (∑ k, (A.a k : ℝ) * Real.log ‖c k‖) + Real.log (A.h z) := by
  have h1 : A.h (torusSmul c z) = (∏ k, ‖c k‖ ^ A.a k) * A.h z := A.smul c z hc
  have h2 : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [h1, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => h2 k) (A.pos z hz).ne',
    Real.log_prod (fun k _ => h2 k)]
  simp only [Real.log_zpow]

theorem log_h_continuousOn {A : HermLine J} (hA : IsSmoothHerm A) :
    ContinuousOn (fun z => Real.log (A.h z)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  ContinuousOn.log hA.continuousOn fun z hz => (A.pos z hz).ne'

end General

theorem logDiff_descends : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb : HermLine J), IsSmoothHerm Nb → Nb.a = muTwDeg Hd B → ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), κ (M.proj z) = Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B Nb hNb hdeg
  have hA : ∀ p, ∃ A : HermLine J, p ∈ D.SB B → A.a = D.vdeg p ∧ IsSmoothHerm A ∧
      ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z := by
    intro p
    by_cases hp : p ∈ D.SB B
    · obtain ⟨A, h1, h2, -, h3⟩ :=
        (_root_.LevelTowerAlt.vertical_factor_smooth_line K J II Ψ Ω W D p (Finset.mem_of_mem_filter p hp)).1
      exact ⟨A, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨S.ref, fun h => absurd h hp⟩
  choose A hA using hA
  have hdegk : ∀ k, (Nb.a k : ℝ) = (S.ref.a k : ℝ) + ∑ p ∈ D.SB B, ((A p).a k : ℝ) := by
    intro k
    have href : S.ref.a = Hd.aMu := S.ref_deg
    have hs : ∑ p ∈ D.SB B, (A p).a k = ∑ p ∈ D.SB B, D.vdeg p k :=
      Finset.sum_congr rfl fun p hp => by rw [(hA p hp).1]
    have : Nb.a k = S.ref.a k + ∑ p ∈ D.SB B, (A p).a k := by
      rw [hdeg, href, hs]
      simp [muTwDeg, Finset.sum_apply]
    rw [this]
    push_cast
    rfl
  obtain ⟨κ, hκ, hκe⟩ := exists_continuous_descent M
    (fun z => Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log ((A p).h z))
    (((log_h_continuousOn hNb).sub (log_h_continuousOn S.ref_smooth)).sub
      (continuousOn_finsetSum _ fun p hp => log_h_continuousOn (hA p hp).2.1))
    (by
      intro c hc z hz
      have hb := hz.1
      simp only [log_h_torusSmul _ hc hb, Finset.sum_add_distrib]
      rw [Finset.sum_comm (s := D.SB B)]
      simp only [hdegk, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      ring)
  refine ⟨κ, hκ, fun z hz => ?_⟩
  rw [hκe z hz]
  congr 1
  exact Finset.sum_congr rfl fun p hp => by rw [(hA p hp).2.2 z hz]

end GlobalTheory.CompanionTheory.Ar.Cusp.Descent
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionSeventh
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem sameOrbit_fstPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (k₀ : K)
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun k => c (some k), fun k => hc _, ?_⟩
  funext p
  show z (v₀ k₀ p) = c (some p.1) * z' (v₀ k₀ p)
  rw [e]
  rfl

theorem sameOrbit_sndPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (k₀ : K)
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · by_cases hk : k = k₀
    · simpa [hk] using hc none
    · simpa [hk] using hc (some k)
  · funext p
    show z (v₁ k₀ p) = (if p.1 = k₀ then c none else c (some p.1)) * z' (v₁ k₀ p)
    rw [e]
    by_cases hk : p.1 = k₀
    · obtain ⟨k, m⟩ := p
      obtain rfl : k = k₀ := hk
      simp [v₁_self]
    · rw [if_neg hk, v₁_ne hk]

theorem null_w : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ l : Fin BM.q, IsNull RW.A {x | FA.pr (q 0 x) ∈ BM.O l ∧ (FA.pr (q 0 x) ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p = 0 ∨ FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p = 0)} := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hab hj hblk hca hcb RW q hq h0 h1 hinj l
  have hpr : HoloMap RW.A BM.Rb.A (FA.pr ∘ q 0) := Pr.holoMap_comp' (hq 0) FA.pr_holo
  have hdens := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_w K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hab hj hblk hca hcb RW q hq h0 h1 hinj l
  have hn0 := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell K ι Φ y Ψ N j M n BM (d + 2) RW.X RW.A RW.U
    (fun x y' => fstPt k₀ (RW.lift x y')) (FA.pr ∘ q 0) l hpr RW.isOpen_U RW.mem_U
    (fun x p => RW.holo x (v₀ k₀ p))
    (fun x y' hy => sameOrbit_fstPt k₀ (RW.compat x y' y' ⟨hy, RW.mem_U y'⟩))
    (fun x hx V hV hxV => by
      obtain ⟨x', hx', hb, hp⟩ := hdens x hx V hV hxV
      exact ⟨x', hx', hb, fun p => (hp p).1⟩)
  have hn1 := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell K ι Φ y Ψ N j M n BM (d + 2) RW.X RW.A RW.U
    (fun x y' => sndPt k₀ (RW.lift x y')) (FA.pr ∘ q 0) l hpr RW.isOpen_U RW.mem_U
    (fun x p => RW.holo x (v₁ k₀ p))
    (fun x y' hy => sameOrbit_sndPt k₀ (RW.compat x y' y' ⟨hy, RW.mem_U y'⟩))
    (fun x hx V hV hxV => by
      obtain ⟨x', hx', hb, hp⟩ := hdens x hx V hV hxV
      exact ⟨x', hx', hb, fun p => (hp p).2⟩)
  intro i
  refine measure_mono_null ?_ (measure_union_null (hn0 i) (hn1 i))
  rintro w ⟨hw, hw'⟩
  obtain ⟨hO, hs | ⟨p, hp | hp⟩⟩ := hw'
  · exact Or.inl ⟨hw, hO, Or.inl hs⟩
  · exact Or.inl ⟨hw, hO, Or.inr ⟨p, hp⟩⟩
  · exact Or.inr ⟨hw, hO, Or.inr ⟨p, hp⟩⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticBadLocusNull
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem null_off_bigCell_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q), IsNull FA.Re.R.A {x | FA.pr (FA.Re.π x) ∈ BM.O l ∧ (FA.pr (FA.Re.π x) ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x))) (FA.Re.R.lift x x) p = 0)} := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l
  exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell K ι Φ y Ψ N j M n BM _ FA.Re.R.X FA.Re.R.A FA.Re.R.U FA.Re.R.lift
    (FA.pr ∘ FA.Re.π) l (Pr.holoMap_comp' FA.Re.holo FA.pr_holo) (fun x => FA.Re.R.isOpen_U x)
    (fun x => FA.Re.R.mem_U x) (fun x p => FA.Re.R.holo x p)
    (fun x y' hy => FA.Re.R.compat x y' y' ⟨hy, FA.Re.R.mem_U y'⟩)
    (fun x hx V hV hxV => _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_r K ι Φ y Ψ N j M n d BM FA l x hx V hV hxV)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticPluckerColumnSwapStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_plucker_column_swap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → ∀ (l : Fin BM.q) (x₀ : FA.Re.R.X), FA.pr (FA.Re.π x₀) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FA.Re.R.lift x₀ x₀) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), SameOrbit (FA.Re.R.lift x₀ x₀) (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FC.Lca τ ca cb c a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptDescentGenericPoint
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem lie_generic_eigenspaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (x : (Σ k, J k) → Ω) (A : HodgeCpt Y S x) (F₀ : Type) [Field F₀] (ξ₀ : Spec (CommRingCat.of F₀) ⟶ Y.X) (ι : F₀ →+* Ω), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f ι → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module F₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j₁ : Li₀ →+ A.Li) (V₀ : CMType H ⊕ CMType H → Submodule F₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (A.M.pt (j₁ e)).left ≫ A.m.φ = spMap (dualMap ι) ≫ (M₀.pt e).left) ∧ IsExtOver ι j₁ ∧ (∀ s e, e ∈ V₀ s ↔ j₁ e ∈ A.Vgen s) ∧ ∀ s, LinearIndependent F₀ (b s) ∧ Submodule.span F₀ (Set.range (b s)) = V₀ s :=
  @PositivityTheory.Xgp.exists_flags_lie_compact_dominated

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem ptsIntegrable_of_resK :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → PtsIntegrableStatement :=
  fun h => GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists (_root_.GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK h)

end GlobalTheory.CompanionTheory.Ar.Giv
end

