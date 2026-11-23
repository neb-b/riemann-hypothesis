module

public import Mathlib
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.DenseNonvan
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenLatticesDifferentStatementHolds
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.EigenLatDifferent

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedAtlasSmoothPotentialLocal
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gradBound_of_local_bounds : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (B : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsAdaptedAtlas A B L s → ∀ ph : X → ℝ, A.SmoothOn (bdry s)ᶜ ph → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (V : Set X) (c : ℝ), IsCompatChart A ψ ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ ∀ x' ∈ V, x' ∉ bdry s → ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2)) → ∃ C₅, ∀ C, C₅ ≤ C → IsGradBound B L s ph C :=
  @PositivityTheory.Xgp.t_c_grad_atlas

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.ValRing

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isPrime_mCoordIdeal (z : (Σ k, ι k) → ℂ) : (mCoordIdeal z).IsPrime :=
  RingHom.ker_isPrime _

theorem eval_ne_zero_of_notMem {z : (Σ k, ι k) → ℂ} {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (hn : h ∉ mCoordIdeal z) :
    eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  intro h0
  refine hn (mem_mCoordIdeal_of_aeval_eq_zero z hh ?_)
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  simpa using h0

theorem aeval_ne_zero_of_notMem {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (hn : h ∉ mCoordIdeal z) : aeval x h ≠ 0 := fun h0 =>
  eval_ne_zero_of_notMem hh hn
    (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero x hh h0))

theorem exists_isValueAt {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    ∃ v, IsValueAt x s z v := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  exact ⟨_, d, g, h, hg, hh, aeval_ne_zero_of_notMem hz hh hn, heq,
    eval_ne_zero_of_notMem hh hn, rfl⟩

theorem isValueAt_add {x : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt x s z v) (hw : IsValueAt x t z w) : IsValueAt x (s + t) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := hw
  refine ⟨d + d', g * h' + g' * h, h * h', GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_add (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hg hh') ?_,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']
    exact GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_add (f := _), map_mul, heq, heq']; ring
  · simp only [map_mul]; exact mul_ne_zero hz0 hz0'
  · simp only [map_add (f := _), map_mul]
    field_simp

theorem regAt_mul {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s t : Ω}
    (hs : RegAt x (mCoordIdeal z) s) (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s * t) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  obtain ⟨d', g', h', hg', hh', hn', heq'⟩ := ht
  refine ⟨d + d', g * g', h * h', GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hg hg', GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hh hh',
    fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩
  rw [map_mul, map_mul, heq, heq']; ring

theorem regAt_add {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s t : Ω}
    (hs : RegAt x (mCoordIdeal z) s) (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s + t) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  obtain ⟨d', g', h', hg', hh', hn', heq'⟩ := ht
  refine ⟨d + d', g * h' + g' * h, h * h', GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_add (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hg hh') ?_,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hh hh',
    fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩
  · rw [add_comm d d']
    exact GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hg' hh
  · simp only [map_add (f := _), map_mul, heq, heq']; ring

theorem one_notMem_mCoordIdeal (z : (Σ k, ι k) → ℂ) : (1 : MRing ι) ∉ mCoordIdeal z :=
  (Ideal.ne_top_iff_one _).1 (isPrime_mCoordIdeal z).ne_top

theorem regAt_zero (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : RegAt x (mCoordIdeal z) 0 :=
  ⟨0, 0, 1, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_zero 0, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩

theorem regAt_one (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : RegAt x (mCoordIdeal z) 1 :=
  ⟨0, 1, 1, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_one, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩

theorem isValueAt_zero_self (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt x 0 z 0 :=
  ⟨0, 0, 1, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_zero 0, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_one, by simp, by simp, by simp, by simp⟩

end

theorem regAt_valAt_ring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal x) → RegAt x (mCoordIdeal z) 0 ∧ RegAt x (mCoordIdeal z) 1 ∧ valAt x 0 z = 0 ∧ valAt x 1 z = 1 ∧ ∀ s t : Ω, RegAt x (mCoordIdeal z) s → RegAt x (mCoordIdeal z) t → RegAt x (mCoordIdeal z) (s * t) ∧ RegAt x (mCoordIdeal z) (s + t) ∧ valAt x (s * t) z = valAt x s z * valAt x t z ∧ valAt x (s + t) z = valAt x s z + valAt x t z := by
  intro K _ ι _ Ω _ x z hz
  refine ⟨regAt_zero x z, regAt_one x z, valAt_eq hz (isValueAt_zero_self x z),
    valAt_eq hz (isValueAt_one_self x z), fun s t hs ht => ⟨regAt_mul hs ht, regAt_add hs ht, ?_, ?_⟩⟩
  · obtain ⟨v, hv⟩ := exists_isValueAt hz hs
    obtain ⟨w, hw⟩ := exists_isValueAt hz ht
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_mul hv hw)]
  · obtain ⟨v, hv⟩ := exists_isValueAt hz hs
    obtain ⟨w, hw⟩ := exists_isValueAt hz ht
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_add hv hw)]

end GlobalTheory.CompanionTheory.Ar.PB.ValRing
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicRealisationHolomorphicMap
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Pull

theorem realis_pullback : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (P J : Ideal (MRing ι)) (D : ℕ) (σ : Type) (S : AnSys D σ) (Re : Realis S (imageZ v₁ P)) (R : AnLogRes P J D), IsBlockMap κ₁ v₁ → IsArithVar P (D + 1) → AlgOver Re → ∃ (π : R.X → S.X) (hπ : HoloMap R.A S.A π), (∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁) ∧ (∀ a (ref' : HermLine ι), IsPullHerm κ₁ v₁ (Re.ref a) ref' → SamePot R.A Set.univ (potOf R ref') ((S.th a).pullback π hπ.1)) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → ∀ x, Real.log ((Re.line a t).h fun p => R.lift x x (v₁ p)) = Real.log ((Re.ref a).h fun p => R.lift x x (v₁ p)) + S.phT a t (π x)) ∧ ∃ (β : MRing ι) (b : K → ℕ), IsMultiHomog β b ∧ β ∉ P ∧ ∀ x, π x ∈ bdry S.s → evC (R.lift x x) β = 0 :=
  @PositivityTheory.UnitarySelfGeneration.r_pull

end GlobalTheory.CompanionTheory.Ar.Pull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticOfImmersionComposition
section
namespace GlobalTheory.CompanionTheory.Metric.Rigid

theorem analyticAt_of_comp_immersion {e : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (F : (Fin e → ℂ) → Fin e → ℂ) (ψ : (Fin e → ℂ) → V)
    (H : (Fin e → ℂ) → V) (y₀ : Fin e → ℂ) (hψ : AnalyticAt ℂ ψ (F y₀))
    (hker : (fderiv ℂ ψ (F y₀)).ker = ⊥) (hH : AnalyticAt ℂ H y₀) (hF : ContinuousAt F y₀)
    (hEq : ∀ᶠ y in nhds y₀, ψ (F y) = H y) : AnalyticAt ℂ F y₀ := by
  classical
  obtain ⟨P₀, hP₀⟩ := ((fderiv ℂ ψ (F y₀) : (Fin e → ℂ) →L[ℂ] V) :
    (Fin e → ℂ) →ₗ[ℂ] V).exists_leftInverse_of_injective hker
  let P : V →L[ℂ] (Fin e → ℂ) := LinearMap.toContinuousLinearMap P₀
  have hPL : P.comp (fderiv ℂ ψ (F y₀)) = ContinuousLinearMap.id ℂ _ := by
    ext1 v
    exact LinearMap.congr_fun hP₀ v
  have hψd : HasFDerivAt ψ (fderiv ℂ ψ (F y₀)) (F y₀) := hψ.differentiableAt.hasFDerivAt
  have hgd : HasFDerivAt (fun x => P (ψ x))
      ((ContinuousLinearEquiv.refl ℂ (Fin e → ℂ) : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ))) (F y₀) := by
    have h1 := P.hasFDerivAt.comp (F y₀) hψd
    rw [hPL] at h1
    simpa using h1
  have hga : AnalyticAt ℂ (fun x => P (ψ x)) (F y₀) := (P.analyticAt _).comp hψ
  have hgc : ContDiffAt ℂ (⊤ : WithTop ℕ∞) (fun x => P (ψ x)) (F y₀) := hga.contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hφa := (hgc.to_localInverse hgd hn).analyticAt
  have hleft := (hgc.hasStrictFDerivAt' hgd hn).eventually_left_inverse
  have hH0 : ψ (F y₀) = H y₀ := hEq.self_of_nhds
  have hev : (fun y => hgc.localInverse hgd hn (P (H y))) =ᶠ[nhds y₀] F := by
    filter_upwards [hF.tendsto.eventually hleft, hEq] with y h1 h2
    rw [← h2]
    exact h1
  have hcomp : AnalyticAt ℂ (fun y => hgc.localInverse hgd hn (P (H y))) y₀ := by
    have h0 : AnalyticAt ℂ (hgc.localInverse hgd hn) (P (H y₀)) := by
      rw [← hH0]
      exact hφa
    have hPH : AnalyticAt ℂ (fun y => P (H y)) y₀ := (P.analyticAt (H y₀)).comp hH
    exact h0.comp_of_eq hPH rfl
  exact hcomp.congr hev

end GlobalTheory.CompanionTheory.Metric.Rigid
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def bvec {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (b : BM.Rb.X) :
    (Σ k, baseIdx ι M.blk k) → ℂ :=
  fun q => BM.Rb.lift b b q / BM.Rb.lift b b ⟨q.1, (BM.F l).c q.1⟩

def flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : (Σ k, ι k) → ℂ := fun q =>
  if hk : ∀ p, M.blk p ≠ some q.1 then b ⟨⟨q.1, hk⟩, q.2⟩ else
    ∑ I, valAt M.x (F.u q I) b * minorIJ (h (not_forall.1 hk).choose.1) I (stepCols N j (not_forall.1 hk).choose.2)

theorem basePart_flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : basePart M.blk (flagPt M F b h) = b := by
  funext q
  obtain ⟨⟨k, hk⟩, m⟩ := q
  exact dif_pos hk

theorem flagPt_step (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) (m : ι k) :
    flagPt M F b h ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p.1) I (stepCols N j p.2) := by
  have hk : ¬ ∀ p', M.blk p' ≠ some k := fun h' => h' p hp
  simp only [flagPt]
  rw [dite_eq_right hk]
  have key : ∀ p' : Ψ × Fin N, M.blk p' = some k →
      (∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p'.1) I (stepCols N j p'.2))
        = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p.1) I (stepCols N j p.2) := by
    intro p' hp'
    rw [M.blk_inj _ _ k hp' hp]
  exact key (not_forall.1 hk).choose (not_not.1 (not_forall.1 hk).choose_spec)

theorem exactAt_flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : ∀ k, b ⟨k, F.c k⟩ = 1) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) :
    ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F p (flagPt M F b h) (h p.1) := by
  refine ⟨fun k => by rw [basePart_flagPt]; exact hb k, fun k hp m => ?_⟩
  rw [basePart_flagPt]
  exact flagPt_step M F b h hp m

def wVec (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (t : ℂ) :
    (Σ o : Option K, ι (o.getD k₀)) → ℂ
  | ⟨some k, m⟩ => flagPt M F b h ⟨k, m⟩
  | ⟨none, m⟩ => ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) b *
      minorIJ (h τ * (1 + Matrix.single cb ca t)) I (stepCols N j a)

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (z : (Σ k, ι k) → ℂ) (p : Ψ × Fin N) : ℂ :=
  (M.blk p).elim 1 fun k => ∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * z ⟨k, m⟩

abbrev CIdx (Ψ : Type) (N j : ℕ) (τ : Ψ) (ca cb : Fin N) : Type := {q : LowIdx Ψ N j // q.1 ≠ (τ, cb, ca)}

def Lc (τ : Ψ) (ca cb : Fin N) (c : CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) : Matrix (Fin N) (Fin N) ℂ := fun r s =>
  if h : (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) ∧ (τ', r, s) ≠ (τ, cb, ca) then
    c ⟨⟨(τ', r, s), h.1⟩, h.2⟩ else if r = s then 1 else 0

def Lca (τ : Ψ) (ca cb : Fin N) (c : CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) : Ψ → Matrix (Fin N) (Fin N) ℂ :=
  Function.update (Lc τ ca cb c) τ (Lc τ ca cb c τ * (1 + Matrix.single cb ca a))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BiholomorphicLiftSystem
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop

theorem not_mem_mcPts_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  have h := hz.2 1 Submodule.mem_top
  simp at h

theorem fderiv_injective_of_leftInv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {τ : E → F} {σ : F → E} {a : E}
    (hτ : DifferentiableAt ℂ τ a) (hσ : DifferentiableAt ℂ σ (τ a))
    (h : σ ∘ τ =ᶠ[nhds a] id) : Function.Injective (fderiv ℂ τ a) := by
  have h1 : fderiv ℂ (σ ∘ τ) a = (fderiv ℂ σ (τ a)).comp (fderiv ℂ τ a) :=
    fderiv_comp a hσ hτ
  have h2 : fderiv ℂ (σ ∘ τ) a = ContinuousLinearMap.id ℂ E := by
    rw [h.fderiv_eq]; exact fderiv_id
  intro u v huv
  have hu : (fderiv ℂ (σ ∘ τ) a) u = u := by rw [h2]; rfl
  have hv : (fderiv ℂ (σ ∘ τ) a) v = v := by rw [h2]; rfl
  rw [← hu, ← hv, h1]
  simp [huv]

theorem differentiableAt_affCoord {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (x : R.X) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x x ⟨k, p k⟩ ≠ 0) (k : Fin R.A.n) (hk : x ∈ (R.A.chart k).source) :
    DifferentiableAt ℂ (fun w => affCoord p (R.lift x ((R.A.chart k).symm w)))
      (R.A.chart k x) := by
  have hmem : R.A.chart k x ∈ (R.A.chart k).target ∩ (R.A.chart k).symm ⁻¹' R.U x :=
    ⟨(R.A.chart k).map_source hk, by
      simpa only [Set.mem_preimage, (R.A.chart k).left_inv hk] using R.mem_U x⟩
  rw [differentiableAt_pi]
  intro q
  have hn : AnalyticAt ℂ ((fun y => R.lift x y q) ∘ (R.A.chart k).symm) (R.A.chart k x) :=
    R.holo x q k _ hmem
  have hd : AnalyticAt ℂ ((fun y => R.lift x y ⟨q.1, p q.1⟩) ∘ (R.A.chart k).symm)
      (R.A.chart k x) := R.holo x ⟨q.1, p q.1⟩ k _ hmem
  have hne : ((fun y => R.lift x y ⟨q.1, p q.1⟩) ∘ (R.A.chart k).symm) (R.A.chart k x) ≠ 0 := by
    simp only [Function.comp, (R.A.chart k).left_inv hk]
    exact hp q.1
  exact (hn.div hd hne).differentiableAt

theorem isLiftSys_of_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} (hJ : J = ⊤) {e : ℕ} (R : AnLogRes P J e) {X : Type}
    [TopologicalSpace X] (A : FinHolAtlas e X) (g : X → R.X) (h : R.X → X)
    (hgh : ∀ y, g (h y) = y) (hhg : ∀ x, h (g x) = x) (hg : HoloMap A R.A g)
    (hh : HoloMap R.A A h) :
    IsLiftSys A P (fun x => g ⁻¹' R.U (g x)) (fun x y => R.lift (g x) (g y)) := by
  subst hJ
  refine ⟨fun x => (R.isOpen_U (g x)).preimage hg.1, fun x => R.mem_U (g x),
    fun x p => holoOn_comp hg (R.holo (g x) p), fun x y hy => R.mem _ _ hy,
    fun x x' y hy => R.compat _ _ _ hy, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy⟩ := R.surj z hz (not_mem_mcPts_top z)
    exact ⟨h y, by simpa only [hgh] using hy⟩
  · intro x x' hs
    have := R.inj (g x) (g x') (not_mem_mcPts_top _) hs
    rw [← hhg x, ← hhg x', this]
  · intro x p hp j hj
    obtain ⟨k, hk⟩ := R.A.cover (g x)
    set a := A.chart j with ha
    set c := R.A.chart k with hc
    have hax : a.symm (a x) = x := a.left_inv hj
    have hcx : c.symm (c (g x)) = g x := c.left_inv hk
    set τ : (Fin e → ℂ) → (Fin e → ℂ) := c ∘ g ∘ a.symm with hτdef
    set σ : (Fin e → ℂ) → (Fin e → ℂ) := a ∘ h ∘ c.symm with hσdef
    have hτx : τ (a x) = c (g x) := by simp only [hτdef, Function.comp, hax]
    have hτ : AnalyticAt ℂ τ (a x) := hg.2 j k (a x)
      ⟨a.map_source hj, show g (a.symm (a x)) ∈ c.source by rw [hax]; exact hk⟩
    have hσ : AnalyticAt ℂ σ (c (g x)) := hh.2 k j (c (g x))
      ⟨c.map_source hk, show h (c.symm (c (g x))) ∈ a.source by rw [hcx, hhg]; exact hj⟩

    have hcont : ContinuousAt (g ∘ a.symm) (a x) :=
      hg.1.continuousAt.comp (a.continuousAt_symm (a.map_source hj))
    have hnear : ∀ᶠ y in nhds (a x), g (a.symm y) ∈ c.source ∧ y ∈ a.target := by
      refine (hcont.eventually_mem (c.open_source.mem_nhds ?_)).and
        (a.open_target.mem_nhds (a.map_source hj))
      simpa only [Function.comp, hax] using hk
    have hleft : σ ∘ τ =ᶠ[nhds (a x)] id := by
      filter_upwards [hnear] with y hy
      simp only [hσdef, hτdef, Function.comp, c.left_inv hy.1, hhg, id, a.right_inv hy.2]
    have hinj := fderiv_injective_of_leftInv hτ.differentiableAt
      (by rw [hτx]; exact hσ.differentiableAt) hleft
    have hF := differentiableAt_affCoord R (g x) p hp k hk
    have himm := R.immersion (g x) (not_mem_mcPts_top _) p hp k hk
    set F : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
      fun w => affCoord p (R.lift (g x) ((R.A.chart k).symm w)) with hFdef
    have hcomp : (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) =ᶠ[nhds (a x)] F ∘ τ := by
      filter_upwards [hnear] with y hy
      simp only [hFdef, hτdef, Function.comp, ← hc, c.left_inv hy.1]
    have hder : fderiv ℂ (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) (a x) =
        (fderiv ℂ F (c (g x))).comp (fderiv ℂ τ (a x)) := by
      rw [hcomp.fderiv_eq, fderiv_comp (a x) (by rw [hτx]; exact hF) hτ.differentiableAt, hτx]
    show (fderiv ℂ (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) (a x)).ker = ⊥
    rw [hder, eq_bot_iff]
    intro v hv
    have h1 : (fderiv ℂ F (c (g x))) ((fderiv ℂ τ (a x)) v) = 0 := by simpa using hv
    have h2 : (fderiv ℂ τ (a x)) v ∈ (fderiv ℂ F (c (g x))).ker := by simpa using h1
    rw [himm] at h2
    have h3 : (fderiv ℂ τ (a x)) v = 0 := by simpa using h2
    have h4 : v = 0 := hinj (h3.trans (map_zero _).symm)
    simp [h4]

end GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianBlockCombination
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.AnForm.A

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def tailCL (d : ℕ) : (Fin (d + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

theorem tailCL_coe (d : ℕ) : (⇑(tailCL d) : (Fin (d + 1) → ℂ) → (Fin d → ℂ)) = Fin.tail := by
  funext z i
  rfl

theorem jacC_tailCL (d : ℕ) (z : Fin (d + 1) → ℂ) (a : Fin d) (k : Fin (d + 1)) :
    jacC (⇑(tailCL d)) z a k = if a.succ = k then 1 else 0 := by
  have h := ContinuousLinearMap.fderiv (𝕜 := ℂ) (x := z) (tailCL d)
  simp only [jacC, h]
  simp [tailCL, Pi.single_apply, eq_comm]

theorem hessC_comp_tail (d : ℕ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p : ℂ)
    (hα : ContDiffAt ℝ 2 α y) :
    hessC (fun z : Fin (d + 1) → ℂ => α (Fin.tail z)) (Fin.cons p y) = blk 0 (hessC α y) := by
  have ht : (tailCL d) (Fin.cons p y : Fin (d + 1) → ℂ) = y := by
    rw [tailCL_coe]; exact Fin.tail_cons _ _
  have h := hessC_comp α (⇑(tailCL d)) (Fin.cons p y : Fin (d + 1) → ℂ)
    ((tailCL d).analyticAt _) (by rw [ht]; exact hα)
  have hfun : α ∘ ⇑(tailCL d) = fun z : Fin (d + 1) → ℂ => α (Fin.tail z) := by
    rw [tailCL_coe]; rfl
  rw [hfun, ht] at h
  rw [h]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  all_goals
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, jacC_tailCL, blk,
      Fin.succ_ne_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem hessC_row_fibre : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p e : ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (s v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p y) → ContDiffAt ℝ 2 α y → hessC f (Fin.cons p y) = blk e B →
    hessC (fun z : Fin (d + 1) → ℂ => s * f z + v * α (Fin.tail z)) (Fin.cons p y) =
    blk ((s : ℂ) * e) ((s : ℂ) • B + (v : ℂ) • hessC α y) := by
  intro d f α y p e B s v hf hα hB
  have ht : (Fin.tail (Fin.cons p y : Fin (d + 1) → ℂ) : Fin d → ℂ) = y := Fin.tail_cons _ _
  have htail : ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => α (Fin.tail z))
      (Fin.cons p y : Fin (d + 1) → ℂ) := by
    have hα' : ContDiffAt ℝ 2 α ((tailCL d) (Fin.cons p y : Fin (d + 1) → ℂ)) := by
      rw [tailCL_coe, ht]; exact hα
    have hl : ContDiffAt ℝ 2 (⇑((tailCL d).restrictScalars ℝ))
        (Fin.cons p y : Fin (d + 1) → ℂ) := ((tailCL d).restrictScalars ℝ).contDiff.contDiffAt
    have := ContDiffAt.comp (g := α) (f := ⇑((tailCL d).restrictScalars ℝ))
      (Fin.cons p y : Fin (d + 1) → ℂ) hα' hl
    have hfun : α ∘ ⇑((tailCL d).restrictScalars ℝ) = fun z : Fin (d + 1) → ℂ => α (Fin.tail z) := by
      funext z
      simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [tailCL_coe]
    rwa [hfun] at this
  rw [ReciprocityTheory.AnForm.M.hessC_add' (fun z => s * f z) (fun z => v * α (Fin.tail z)) _
    (contDiffAt_const.mul hf) (contDiffAt_const.mul htail),
    ReciprocityTheory.AnForm.M.hessC_const_mul' s f, ReciprocityTheory.AnForm.M.hessC_const_mul' v (fun z => α (Fin.tail z)), hB, hessC_comp_tail d α y p hα]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [blk]

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenLatticesDifferentStatementHoldsStatement
section
open NumberField GroundTheory.Heights₂.Heights.NineStatements
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_lattices_different_statement_holds : GroundTheory.Heights₂.Heights.NineStatements.EigenLatDifferent.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigLat.eigenLat_eq_diffLat | exact GlobalTheory.CompanionTheory.Ar.EigLat.eigenLat_eq_diffLat | (intros; apply GlobalTheory.CompanionTheory.Ar.EigLat.eigenLat_eq_diffLat <;> assumption)
end

