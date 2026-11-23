module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicSectionOfPotential
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ContDiff

namespace SecPot

section General

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoOn_continuousOn' {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) :
    ContinuousOn f W := by
  intro z hz
  obtain ⟨j, hj⟩ := A.cover z
  have h1 : (A.chart j).symm (A.chart j z) = z := (A.chart j).left_inv hj
  have hu : A.chart j z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by rw [Set.mem_preimage, h1]; exact hz⟩
  have hc : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j z) := (h j _ hu).continuousAt
  have hc2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) z :=
    ContinuousAt.comp hc ((A.chart j).continuousAt hj)
  have hev : ((f ∘ (A.chart j).symm) ∘ (A.chart j)) =ᶠ[𝓝 z] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  exact (hc2.congr hev).continuousWithinAt

end General

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

structure LocSec (M : CxModel P d) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ) : Prop where
  isOpen : IsOpen U
  sec : ∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y
  holo : ∀ p, M.atlas.HoloOn U fun y => s y p

theorem locSec_sections (M : CxModel P d) (x : M.Xc) :
    LocSec M (M.sections x).choose (M.sections x).choose_spec.2.2.choose :=
  ⟨(M.sections x).choose_spec.1, (M.sections x).choose_spec.2.2.choose_spec.1,
    (M.sections x).choose_spec.2.2.choose_spec.2⟩

theorem smoothOn_log_sec {M : CxModel P d} {U : Set M.Xc} {s : M.Xc → (Σ k, ι k) → ℂ}
    (hs : LocSec M U s) {B : HermLine ι} (hB : IsSmoothHerm B) :
    M.atlas.SmoothOn U (fun y => Real.log (B.h (s y))) := by
  intro j y hy
  have hσ : ContDiffAt ℝ ∞ (fun y' => s ((M.atlas.chart j).symm y')) y :=
    contDiffAt_pi.2 fun p => ((hs.holo p j y hy).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hm := (hs.sec _ hy.2).1.1
  have hn : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (s ((M.atlas.chart j).symm y)) := by
    refine IsOpen.mem_nhds ?_ hm
    simp only [Set.setOf_forall, Set.setOf_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h1 : ContDiffAt ℝ ∞ (fun y' => Real.log (B.h (s ((M.atlas.chart j).symm y')))) y :=
    ((hB.contDiffAt hn).comp y hσ).log (B.pos _ hm).ne'
  exact h1.contDiffWithinAt

theorem exists_re_holo_sections {M : CxModel P d} {U U' : Set M.Xc} {s s' : M.Xc → (Σ k, ι k) → ℂ}
    (hs : LocSec M U s) (hs' : LocSec M U' s') (B : HermLine ι) {y₀ : M.Xc} (hy : y₀ ∈ U)
    (hy' : y₀ ∈ U') :
    ∃ W : Set M.Xc, IsOpen W ∧ y₀ ∈ W ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn W G ∧
      ∀ z ∈ W ∩ U ∩ U', Real.log (B.h (s z)) - Real.log (B.h (s' z)) = (G z).re := by
  classical
  have hz := (hs.sec y₀ hy).1
  have hz' := (hs'.sec y₀ hy').1
  choose i hi using hz'.1
  obtain ⟨c₀, hc₀, hcz⟩ := (M.fibre _ hz' _ hz).1 (by rw [(hs.sec y₀ hy).2, (hs'.sec y₀ hy').2])
  have hn0 : ∀ k, s y₀ ⟨k, i k⟩ ≠ 0 := fun k => by
    rw [hcz]
    exact mul_ne_zero (hc₀ k) (hi k)

  let r : K → ℂ := fun k => s y₀ ⟨k, i k⟩ / s' y₀ ⟨k, i k⟩
  have hr : ∀ k, r k ≠ 0 := fun k => div_ne_zero (hn0 k) (hi k)
  let q : K → M.Xc → ℂ := fun k z => s z ⟨k, i k⟩ / s' z ⟨k, i k⟩ / r k
  have hO : IsOpen (U ∩ U') := hs.isOpen.inter hs'.isOpen
  let W : Set M.Xc := {z | z ∈ U ∩ U' ∧ ∀ k, s' z ⟨k, i k⟩ ≠ 0 ∧ q k z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ∀ k, ContinuousAt (fun z => s z ⟨k, i k⟩) z := fun k =>
      ((holoOn_continuousOn' (hs.holo _)).mono Set.inter_subset_left).continuousAt (hO.mem_nhds hz.1)
    have hd : ∀ k, ContinuousAt (fun z => s' z ⟨k, i k⟩) z := fun k =>
      ((holoOn_continuousOn' (hs'.holo _)).mono Set.inter_subset_right).continuousAt (hO.mem_nhds hz.1)
    filter_upwards [hO.mem_nhds hz.1, eventually_all.mpr fun k => (hd k).eventually_ne (hz.2 k).1,
      eventually_all.mpr fun k => (((hn k).div (hd k) (hz.2 k).1).div_const _).eventually_mem
        (Complex.isOpen_slitPlane.mem_nhds (hz.2 k).2)] with w h1 h2 h3
    exact ⟨h1, fun k => ⟨h2 k, h3 k⟩⟩
  have hyW : y₀ ∈ W := by
    refine ⟨⟨hy, hy'⟩, fun k => ⟨hi k, ?_⟩⟩
    have : q k y₀ = 1 := div_self (hr k)
    rw [this]
    exact Complex.one_mem_slitPlane
  let G : M.Xc → ℂ := fun z => ∑ k, ((B.a k : ℝ) : ℂ) *
    (Complex.log (q k z) + ((Real.log ‖r k‖ : ℝ) : ℂ))
  refine ⟨W, hW, hyW, G, fun j u hu => ?_, fun z hz => ?_⟩
  · have hzW : (M.atlas.chart j).symm u ∈ W := hu.2
    have hterm : ∀ k, AnalyticAt ℂ (fun u' => ((B.a k : ℝ) : ℂ) *
        (Complex.log (q k ((M.atlas.chart j).symm u')) + ((Real.log ‖r k‖ : ℝ) : ℂ))) u := by
      intro k
      have hn : AnalyticAt ℂ (fun u' => s ((M.atlas.chart j).symm u') ⟨k, i k⟩) u :=
        hs.holo _ j u ⟨hu.1, hzW.1.1⟩
      have hd : AnalyticAt ℂ (fun u' => s' ((M.atlas.chart j).symm u') ⟨k, i k⟩) u :=
        hs'.holo _ j u ⟨hu.1, hzW.1.2⟩
      have hq : AnalyticAt ℂ (fun u' => q k ((M.atlas.chart j).symm u')) u :=
        (hn.div hd (hzW.2 k).1).div analyticAt_const (hr k)
      have hl : AnalyticAt ℂ (Complex.log ∘ fun u' => q k ((M.atlas.chart j).symm u')) u :=
        AnalyticAt.comp (f := fun u' => q k ((M.atlas.chart j).symm u'))
          (analyticAt_clog (hzW.2 k).2) hq
      exact analyticAt_const.mul (hl.add analyticAt_const)
    exact Finset.analyticAt_fun_sum _ fun k _ => hterm k
  · have hzW : z ∈ W := hz.1.1
    have hm := (hs.sec z hzW.1.1).1
    have hm' := (hs'.sec z hzW.1.2).1
    obtain ⟨c, hc, hcy⟩ := (M.fibre _ hm' _ hm).1
      (by rw [(hs.sec z hzW.1.1).2, (hs'.sec z hzW.1.2).2])
    have hpos : 0 < B.h (s' z) := B.pos _ hm'.1
    have hprod : (∏ k, ‖c k‖ ^ B.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    have hterm : ∀ k, Real.log ‖q k z‖ + Real.log ‖r k‖ = Real.log ‖c k‖ := by
      intro k
      have hck : s z ⟨k, i k⟩ = c k * s' z ⟨k, i k⟩ := by rw [hcy]; rfl
      have hqz : q k z = c k / r k := by
        simp only [q]
        rw [hck, mul_div_assoc, div_self (hzW.2 k).1, mul_one]
      rw [hqz, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc k)) (norm_ne_zero_iff.mpr (hr k))]
      ring
    have hsm : B.h (s z) = (∏ k, ‖c k‖ ^ B.a k) * B.h (s' z) := by
      rw [hcy]
      exact B.smul c _ hc
    rw [hsm, Real.log_mul hprod hpos.ne', add_sub_cancel_right,
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))]
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re,
      Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k, Real.log_zpow]

def potOfSections (M : CxModel P d) (B : HermLine ι) : LocPot M.Xc where
  U x := (M.sections x).choose
  isOpen_U x := (M.sections x).choose_spec.1
  mem_U x := (M.sections x).choose_spec.2.1
  φ x y := Real.log (B.h ((M.sections x).choose_spec.2.2.choose y))

end Model

end SecPot


open SecPot in
theorem exists_potential_of_smoothHerm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (B : HermLine ι), IsSmoothHerm B → ∃ Φ : LocPot M.Xc, IsPotential M.atlas Φ ∧ ∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (B.h z)) (s y') = (G y').re := by
  intro K _ ι _ P n M B hB
  refine ⟨potOfSections M B, ⟨fun x => smoothOn_log_sec (locSec_sections M x) hB, ?_⟩, ?_⟩
  · intro x x' y hy
    exact exists_re_holo_sections (locSec_sections M x) (locSec_sections M x') B hy.1 hy.2
  · intro x y₀ hy
    have hs := locSec_sections M x
    refine ⟨_, hs.isOpen, hy.1, fun z hz => ⟨hz, Set.mem_univ _⟩, _, hs.sec, hs.holo, fun _ => 0,
      fun j u _ => analyticAt_const, fun y' _ => ?_⟩
    simp [potOfSections]

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalMultihomogQuotientExists
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

namespace GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

theorem mem_ptsOver_of_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : z ∈ ptsOver ℂ P := by
  refine ⟨hz.1, fun f hf => ?_⟩
  have h := hz.2 f hf
  rw [eval_map] at h
  rw [aeval_def]
  simpa [algebraMap_int_eq] using h

end GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

namespace GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

theorem global_decay : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes (mCoordIdeal y) J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ ε : Ω, (∀ x : R.X, ∃ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg ∧ IsMultiHomog Hf dh ∧ (∀ k, (dg k : ℤ) = dh k + Eh.a k) ∧ aeval y G = ε * aeval y Hf ∧ aeval (R.lift x x) Hf ≠ (0 : ℂ)) → (∀ (x : R.X) (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → aeval y G = ε * aeval y Hf → aeval (R.lift x x) G ≠ (0 : ℂ) → aeval (R.lift x x) Hf ≠ (0 : ℂ) → π x ∈ S.open') → ∃ δ C : ℝ, 0 < δ ∧ ∀ x : R.X, π x ∈ S.open' → ∀ v : ℂ, HasVal y Eh.a ε (R.lift x x) v → v ≠ 0 → Real.log ‖v‖ - Real.log (Eh.h (R.lift x x)) ≤ -δ * rW S.L S.s (π x) + C := by
  intro K _ ι _ Ω _ y J e R σ S π hπ Eh hEh ε h1 h2
  choose dg dh G Hf hG hH hd hy hne using h1
  have loc := fun x₀ : R.X => _root_.GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay K ι (mCoordIdeal y) J e R σ S π hπ Eh hEh (dg x₀) (dh x₀)
    (G x₀) (Hf x₀) (hG x₀) (hH x₀) (hd x₀)
    (fun x a b => h2 x _ _ _ _ (hG x₀) (hH x₀) (hd x₀) (hy x₀) a b) x₀ (hne x₀)
  choose V N C hVo hV hN hb using loc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover V (fun x _ => (hVo x).mem_nhds (hV x))
  refine ⟨1 / (2 * (1 + ∑ x₀ ∈ t, (N x₀ : ℝ))), ∑ x₀ ∈ t, |C x₀|, by positivity, ?_⟩
  intro x hx v hv hv0
  obtain ⟨x₀, hx₀t, hxV⟩ : ∃ x₀ ∈ t, x ∈ V x₀ := by simpa using ht.2 (Set.mem_univ x)
  have hz : R.lift x x ∈ ptsOver ℂ (mCoordIdeal y) :=
    mem_ptsOver_of_mem_mcPts (R.mem x x (R.mem_U x))
  obtain ⟨hHf, hbd⟩ := hb x₀ x hxV
  have hrep := (_root_.GlobalTheory.CompanionTheory.Ar.Small.hasVal_read_of_rep K ι Ω y ℂ Eh.a ε (R.lift x x) v hz hv).1 _ _ _ _
    (hG x₀) (hH x₀) (hd x₀) (hy x₀)
  have hGne : aeval (R.lift x x) (G x₀) ≠ (0 : ℂ) := by
    rw [hrep]; exact mul_ne_zero hv0 hHf
  have hbd' := hbd hx hGne
  have hval : (aeval (R.lift x x) (G x₀) : ℂ) / aeval (R.lift x x) (Hf x₀) = v := by
    rw [hrep]; exact mul_div_cancel_right₀ v hHf
  rw [hval] at hbd'
  have hr : 0 ≤ rW S.L S.s (π x) := by
    have h0 := S.norm_le (π x)
    have h1 : 0 < Real.exp 1 := Real.exp_pos 1
    unfold rW
    linarith
  have hNpos : (0 : ℝ) < N x₀ := by exact_mod_cast hN x₀
  have hsum : (N x₀ : ℝ) ≤ ∑ a ∈ t, (N a : ℝ) :=
    Finset.single_le_sum (f := fun a => (N a : ℝ)) (fun a _ => Nat.cast_nonneg _) hx₀t
  have hδ : 1 / (2 * (1 + ∑ a ∈ t, (N a : ℝ))) ≤ 1 / (2 * (N x₀ : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hC : C x₀ ≤ ∑ a ∈ t, |C a| :=
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun a => |C a|) (fun a _ => abs_nonneg _) hx₀t)
  have hmul := mul_le_mul_of_nonneg_right hδ hr
  linarith

end GlobalTheory.CompanionTheory.Ar.Small.GlobDecay
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantLinearFunctional
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly

noncomputable section

lemma exists_perm_of_sum_single {d : ℕ} {τ τ' : Fin d → Option (Fin 3)}
    (h : ∑ t, Finsupp.single (τ t) (1 : ℕ) = ∑ t, Finsupp.single (τ' t) (1 : ℕ)) :
    ∃ π : Equiv.Perm (Fin d), ∀ t, τ' (π t) = τ t := by
  classical
  have hc : ∀ o : Option (Fin 3), Fintype.card {t // τ t = o} = Fintype.card {t // τ' t = o} := by
    intro o
    have h1 := congrArg (fun f => f o) h
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_boole, Nat.cast_id] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h1
  exact ⟨Equiv.ofFiberEquiv (fun o => Fintype.equivOfCardEq (hc o)), fun t => Equiv.ofFiberEquiv_map _ t⟩

lemma prod_X_eq_monomial {d : ℕ} (τ : Fin d → Option (Fin 3)) :
    (∏ t, (X (τ t) : MvPolynomial (Option (Fin 3)) ℝ)) =
      monomial (∑ t, Finsupp.single (τ t) (1 : ℕ)) 1 := by
  exact (monomial_sum_one (R := ℝ) Finset.univ fun t => Finsupp.single (τ t) 1).symm

lemma linear_form_add_eq_sum (n : Fin 3 → ℝ) (v : ℝ) :
    lin4 n + C v * X none =
      ∑ j : Option (Fin 3), C (Option.elim j v n) * (X j : MvPolynomial (Option (Fin 3)) ℝ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin4, lin3, map_sum, map_mul, rename_X, rename_C, Fintype.sum_option, Option.elim_none,
    Option.elim_some]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_functional : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
    ∃ L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ, ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)) := by
  classical
  intro d T H
  obtain ⟨Λ, hΛ, hsym⟩ := (PositivityTheory.Xgp.t_fib_mdisc d).2
  obtain ⟨M, hM⟩ : ∃ M : Option (Fin 3) → Matrix (Fin d) (Fin d) ℂ, M none = H ∧ ∀ i, M (some i) = T i :=
    ⟨fun j => Option.elim j H T, rfl, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (Option (Fin 3) →₀ ℕ) → ℂ, ∀ τ : Fin d → Option (Fin 3),
      g (∑ t, Finsupp.single (τ t) (1 : ℕ)) = (d.factorial : ℂ) * Λ (fun t => M (τ t)) := by
    refine ⟨fun m => if h : ∃ τ : Fin d → Option (Fin 3), ∑ t, Finsupp.single (τ t) (1 : ℕ) = m then
      (d.factorial : ℂ) * Λ (fun t => M (h.choose t)) else 0, fun τ => ?_⟩
    have h : ∃ τ' : Fin d → Option (Fin 3),
        ∑ t, Finsupp.single (τ' t) (1 : ℕ) = ∑ t, Finsupp.single (τ t) (1 : ℕ) := ⟨τ, rfl⟩
    simp only [dif_pos h]
    obtain ⟨π, hπ⟩ := exists_perm_of_sum_single h.choose_spec
    have e : (fun t => M (h.choose t)) = (fun t => M (τ t)) ∘ π :=
      funext fun t => by simp only [Function.comp_apply, hπ]
    rw [e, hsym]
  refine ⟨(basisMonomials (Option (Fin 3)) ℝ).constr ℝ g, fun c v => ?_⟩
  have hL : ∀ (m : Option (Fin 3) →₀ ℕ) (x : ℝ),
      (basisMonomials (Option (Fin 3)) ℝ).constr ℝ g (monomial m x) = (x : ℂ) * g m := by
    intro m x
    have hx : (monomial m x : MvPolynomial (Option (Fin 3)) ℝ) = x • basisMonomials (Option (Fin 3)) ℝ m := by
      simp only [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    rw [hx, map_smul, Module.Basis.constr_basis, Complex.real_smul]
  have hrow : ∀ t, (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H =
      ∑ j : Option (Fin 3), ((Option.elim j (v t) (c t) : ℝ) : ℂ) • M j := by
    intro t
    rw [Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some, hM.1, hM.2]
    exact add_comm _ _
  have hprod : (∏ t, (lin4 (c t) + C (v t) * X none) : MvPolynomial (Option (Fin 3)) ℝ) =
      ∑ r : Fin d → Option (Fin 3),
        monomial (∑ t, Finsupp.single (r t) (1 : ℕ)) (∏ t, Option.elim (r t) (v t) (c t)) := by
    simp only [linear_form_add_eq_sum]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod (C : ℝ →+* MvPolynomial (Option (Fin 3)) ℝ), prod_X_eq_monomial,
      C_mul_monomial, mul_one]
  simp only [hrow]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hΛ, MultilinearMap.map_sum, hprod, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, hL, hg, smul_eq_mul, Complex.ofReal_prod]
  simp only [RingHom.id_apply]
  ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantOneRowExpansion
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem pderiv_fin_prod {σ : Type*} (k : σ) : ∀ (d : ℕ) (f : Fin (d + 1) → MvPolynomial σ ℝ),
    pderiv k (∏ r, f r) = ∑ r, pderiv k (f r) * ∏ s, f (r.succAbove s) := by
  intro d
  induction d with
  | zero => intro f; simp
  | succ d ih =>
    intro f
    rw [Fin.prod_univ_succ, Derivation.leibniz, ih (fun i => f i.succ),
      Fin.sum_univ_succ (fun r => pderiv k (f r) * ∏ s, f (r.succAbove s))]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · simp only [Fin.succAbove_zero]
      ring
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [Fin.prod_univ_succ (fun s => f (r.succ.succAbove s))]
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
      ring

theorem pderiv_row_weight (c v : ℝ) : pderiv (some 0 : Option (Fin 2)) (rowW ![c, 0] v) = C c := by
  simp [rowW, pderiv_X, Pi.single_apply]

theorem eval_row_weight (n : Fin 3 → ℝ) (c v : ℝ) :
    evalW n n (rowW ![c, 0] v) = lin4 (fun i => c * n i) + C v * X none := by
  have h : lin4 (fun i => c * n i) = C c * lin4 n := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [lin4, lin3, map_sum, map_mul, rename_C, rename_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]
  simp [rowW, evalW, aeval_def, algebraMap_eq]

theorem extract_one : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (c : Fin (d + 1) → ℝ) (v : Fin (d + 1) → ℝ) (n : Fin 3 → ℝ) (e : ℂ),
      ((d + 1).factorial : ℂ) * mdisc (fun r => blk ((c r : ℂ) * e)
        ((∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H)) =
      e * L (evalW n n (pderiv (some 0) (∏ r, rowW ![c r, 0] (v r)))) := by
  intro d T H L hL c v n e
  have h1 := ((GlobalTheory.T.mixed_discriminant_cofactor_expansion d).1 (fun r => (c r : ℂ) * e)
    (fun r => (∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))
  refine h1.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pderiv_fin_prod, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h3 := hL (fun s i => c (r.succAbove s) * n i) (fun s => v (r.succAbove s))
  rw [h3, pderiv_row_weight, map_mul (evalW n n), map_prod (evalW n n)]
  simp only [eval_row_weight]
  have h4 : evalW n n (C (c r)) = C (c r) := by simp [evalW, aeval_def, algebraMap_eq]
  rw [h4, C_mul', map_smul, Complex.real_smul]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumSqCompBlockMap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem sum_sq_comp_blockMap {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]
    {Kk : Type} {ιk : Kk → Type} [∀ k, Fintype (ιk k)]
    {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hv : IsBlockMap κ v)
    (z : (Σ k, ι k) → ℂ) (k' : Kk) :
    ∑ m, ‖(z ∘ v) ⟨k', m⟩‖ ^ 2 = ∑ i, ‖z ⟨κ k', i⟩‖ ^ 2 := by
  obtain ⟨hκ, hvi, hblk, hsurj⟩ := hv
  have key : ∀ m : ιk k', ∃ i : ι (κ k'), v ⟨k', m⟩ = ⟨κ k', i⟩ := by
    intro m
    have h := hblk ⟨k', m⟩
    rcases hh : v ⟨k', m⟩ with ⟨c, i⟩
    rw [hh] at h
    simp only at h
    subst h
    exact ⟨i, rfl⟩
  choose g hg using key
  have hinj : Function.Injective g := by
    intro m m' hmm
    have h : v ⟨k', m⟩ = v ⟨k', m'⟩ := by rw [hg, hg, hmm]
    have h' := hvi h
    simpa using h'
  have hsur : Function.Surjective g := by
    intro i
    obtain ⟨⟨k'', m⟩, hp⟩ := hsurj ⟨κ k', i⟩ ⟨k', rfl⟩
    have h := hblk ⟨k'', m⟩
    rw [hp] at h
    have hk : k'' = k' := (hκ h).symm
    subst hk
    refine ⟨m, ?_⟩
    rw [hg] at hp
    simpa using hp
  have hbij : Function.Bijective g := ⟨hinj, hsur⟩
  rw [← hbij.sum_comp (fun i => ‖z ⟨κ k', i⟩‖ ^ 2)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Function.comp_apply, hg]

theorem fsHerm_h_blockMap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (a : K → ℤ) (z : (Σ k, ι k) → ℂ), IsBlockMap κ v → (∀ k, a k ≠ 0 → k ∈ Set.range κ) → (fsHerm ι a).h z = (fsHerm ιk fun k => a (κ k)).h (z ∘ v) := by
  intro K _ ι _ Kk _ ιk _ κ v a z hv ha
  rw [fsHerm_h, fsHerm_h]
  unfold refNorm
  symm
  refine Fintype.prod_of_injective κ hv.1 _ _ ?_ ?_
  · intro k hk
    have h0 : a k = 0 := by
      by_contra h
      exact hk (ha k h)
    simp [h0]
  · intro k'
    rw [sum_sq_comp_blockMap hv z k']

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

