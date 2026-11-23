module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0082
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0020
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0025
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0084
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFrameMetricNearPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor

section Holo

variable {e : ℕ} {S : Type} [TopologicalSpace S]

theorem holoOn_mono (A : FinHolAtlas e S) {U V : Set S} {f : S → ℂ} (h : A.HoloOn V f) (hU : U ⊆ V) :
    A.HoloOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hU))

theorem holoOn_const (A : FinHolAtlas e S) (U : Set S) (c : ℂ) : A.HoloOn U fun _ => c := fun _ _ _ =>
  analyticAt_const

theorem holoOn_mul (A : FinHolAtlas e S) {U : Set S} {f g : S → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun w => f w * g w := fun j u hu => (hf j u hu).mul (hg j u hu)

theorem holoOn_zpow (A : FinHolAtlas e S) {U : Set S} {f : S → ℂ} (hf : A.HoloOn U f)
    (h0 : ∀ w ∈ U, f w ≠ 0) (n : ℤ) : A.HoloOn U fun w => f w ^ n := fun j u hu =>
  (hf j u hu).zpow (h0 _ hu.2)

theorem holoOn_prod (A : FinHolAtlas e S) {U : Set S} {κ : Type} (s : Finset κ) {f : κ → S → ℂ}
    (hf : ∀ i ∈ s, A.HoloOn U (f i)) : A.HoloOn U fun w => ∏ i ∈ s, f i w := by
  induction s using Finset.induction_on with
  | empty => simpa using holoOn_const A U 1
  | insert i s hi ih =>
    have h := holoOn_mul A (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.prod_insert hi] using h

theorem holoOn_minor (A : FinHolAtlas e S) {U : Set S} {N : ℕ} {H : S → Matrix (Fin N) (Fin N) ℂ}
    (hH : ∀ r s, A.HoloOn U fun w => H w r s) (I J : Finset (Fin N)) :
    A.HoloOn U fun w => minorIJ (H w) I J := by
  have h := StepW.ValHolo.holoOn_eval A (b := fun w (q : Fin N × Fin N) => H w q.1 q.2) (fun q => hH q.1 q.2)
    (minorIJ (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J)
  have e : (fun w => minorIJ (H w) I J) = fun w => eval (fun q : Fin N × Fin N => H w q.1 q.2)
      (map (Int.castRingHom ℂ)
        (minorIJ (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J)) := by
    funext w
    let f : MvPolynomial (Fin N × Fin N) ℤ →+* ℂ :=
      (eval fun q : Fin N × Fin N => H w q.1 q.2).comp (map (Int.castRingHom ℂ))
    have hm : (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)).map f = H w := by
      ext r s
      simp [f]
    have := minorIJ_map f (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J
    rw [hm] at this
    exact this
  rw [e]
  exact h

theorem prod_local (A : FinHolAtlas e S) {V : Set S} {y₀ : S} {N : ℕ} (hV : IsOpen V) (hy : y₀ ∈ V)
    (g : Fin N → S → ℂ) (n : Fin N → ℤ)
    (key : ∀ i, ∃ W : Set S, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ V ∧ A.HoloOn W (g i) ∧ ∀ w ∈ W, g i w ≠ 0) :
    ∃ V' : Set S, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i, g i w ^ n i) ∧
      ∀ w ∈ V', ∏ i, g i w ^ n i ≠ 0 := by
  choose W hW hyW hWV hh h0 using key
  have hsub : ∀ i, V ∩ ⋂ i, W i ⊆ W i := fun i => Set.inter_subset_right.trans (Set.iInter_subset _ i)
  refine ⟨V ∩ ⋂ i, W i, hV.inter (isOpen_iInter_of_finite hW), ⟨hy, Set.mem_iInter.2 hyW⟩,
    Set.inter_subset_left, ?_, ?_⟩
  · exact holoOn_prod A _ fun i _ =>
      holoOn_zpow A (holoOn_mono A (hh i) (hsub i)) (fun w hw => h0 i w (hsub i hw)) (n i)
  · exact fun w hw => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (h0 i w (hsub i hw))

end Holo

theorem minor_w_ne {N j : ℕ} (hj : j ≤ N) (i : Fin N) (hi : (i : ℕ) + 1 = j) {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : minorIJ T (wIdx N j) (wIdx N j) ≠ 0 := by
  have h := FrameChange.detFac_ne_zero hj i hT hd
  rw [detFac, if_pos hi.ge] at h
  exact left_ne_zero_of_mul h

theorem minor_om_ne {N j : ℕ} (hj : j ≤ N) (i : Fin N) (hi : (i : ℕ) + 1 = N) {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : minorIJ T (omIdx N j) (omIdx N j) ≠ 0 := by
  have h := FrameChange.detFac_ne_zero hj i hT hd
  rw [detFac, if_pos hi] at h
  exact right_ne_zero_of_mul h

theorem val_ne {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (h0 : s ≠ 0)
    (hs : RegAt x (mCoordIdeal z) s) (hi : RegAt x (mCoordIdeal z) s⁻¹) : valAt x s z ≠ 0 := by
  intro e
  have h := (reg_mul hz hs hi).2
  rw [mul_inv_cancel₀ h0, e, zero_mul] at h
  exact one_ne_zero (((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.1).symm.trans h)

theorem improper_factor : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (V : Set X) (y₀ : X) (zb : X → (Σ k, baseIdx ι M.blk k) → ℂ) (Hm : X → Matrix (Fin N) (Fin N) ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) (a : Fin N), IsOpen V → y₀ ∈ V → (∀ q, A.HoloOn V fun w => zb w q) → (∀ w ∈ V, zb w ∈ mcPts (mCoordIdeal M.x)) → (∀ w ∈ V, M.GoodAt F (mCoordIdeal (zb w))) → (∀ r s, A.HoloOn V fun w => Hm w r s) → (∀ w ∈ V, IsBlockDiag j (Hm w) ∧ (Hm w).det ≠ 0) → ∃ V' : Set X, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ∧ ∀ w ∈ V', (∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M e X _ A V y₀ zb Hm F τ a hV hy hzb hpt hgood hHm hdiag
  refine prod_local A hV hy (fun i w => if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) *
    (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1)
      else minorIJ (Hm w) (omIdx N j) (omIdx N j))) (fun i => xiCoef τ a (τ, i)) fun i => ?_
  by_cases hp : IsProperStep N j i
  · refine ⟨V, hV, hy, subset_rfl, ?_, fun w _ => ?_⟩
    · simp only [if_pos hp]
      exact holoOn_const A V 1
    · simp only [if_pos hp]
      exact one_ne_zero
  · have hnone : M.blk (τ, i) = none := (M.blk_none (τ, i)).2 hp
    obtain ⟨W, hW, hyW, hWV, hval⟩ := StepW.ValHolo.holoOn_valAt _ _ M.Ω M.x (F.υ (τ, i)) e X A V zb y₀ hV hy hzb hpt
      ((hgood y₀ hy).2.2 _ hnone).2.1
    have hm : A.HoloOn W fun w => (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1)
        else minorIJ (Hm w) (omIdx N j) (omIdx N j)) := by
      have hH : ∀ r s, A.HoloOn W fun w => Hm w r s := fun r s => holoOn_mono A (hHm r s) hWV
      by_cases h1 : (i : ℕ) + 1 = j
      · by_cases h2 : (a : ℕ) < j
        · simp only [if_pos h1, if_pos h2]
          exact holoOn_minor A hH _ _
        · simp only [if_pos h1, if_neg h2]
          exact holoOn_const A W 1
      · simp only [if_neg h1]
        exact holoOn_minor A hH _ _
    refine ⟨W, hW, hyW, hWV, ?_, fun w hw => ?_⟩
    · simp only [if_neg hp]
      exact holoOn_mul A hval hm
    · simp only [if_neg hp]
      have hwV := hWV hw
      have hv : valAt M.x (F.υ (τ, i)) (zb w) ≠ 0 :=
        val_ne (hpt w hwV) ((hgood w hwV).2.2 _ hnone).1 ((hgood w hwV).2.2 _ hnone).2.1
          ((hgood w hwV).2.2 _ hnone).2.2
      refine mul_ne_zero hv ?_
      by_cases h1 : (i : ℕ) + 1 = j
      · by_cases h2 : (a : ℕ) < j
        · simp only [if_pos h1, if_pos h2]
          exact minor_w_ne M.j_le i h1 (hdiag w hwV).1 (hdiag w hwV).2
        · simp only [if_pos h1, if_neg h2]
          exact one_ne_zero
      · simp only [if_neg h1]
        have h3 : (i : ℕ) + 1 = N := by
          by_contra h3
          exact hp ⟨h1, h3⟩
        exact minor_om_ne M.j_le i h3 (hdiag w hwV).1 (hdiag w hwV).2

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsomorphicLinesPotentialDifference
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.OneModel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
  GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open scoped ContDiff

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_pair_ne {P : Ideal (MRing ι)} {f g : MRing ι} (h : UnitRatio P f g) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : ∃ u v : MRing ι, u * f - v * g ∈ P ∧ evC z u ≠ 0 ∧ evC z v ≠ 0 := by
  let ρ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hprime : (RingHom.ker ρ).IsPrime := RingHom.ker_isPrime ρ
  have hle : P ≤ RingHom.ker ρ := fun q hq => hz.2 q hq
  have hrel : IsRelevant (RingHom.ker ρ) := fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun hm => hi ?_⟩
    simpa [ρ] using (RingHom.mem_ker.1 hm)
  obtain ⟨u, v, hu, hv, huv⟩ := h.2.2 _ hprime hle hrel
  exact ⟨u, v, huv, fun h0 => hu (RingHom.mem_ker.2 h0), fun h0 => hv (RingHom.mem_ker.2 h0)⟩

theorem log_line_of_orbit {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (a : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) (x : Re.R.X) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ho : SameOrbit (Re.R.lift x x) z) :
    Real.log ((Re.line a t).h z) = Real.log ((Re.ref a).h z) + S.phT a t (Re.π x) := by
  obtain ⟨c, hc, e⟩ := ho
  have h := Re.line_eq a t h0 h1 x
  rw [e, (Re.line a t).smul c z hc, (Re.ref a).smul c z hc, Re.line_deg] at h
  have hp : (∏ k, ‖c k‖ ^ (Re.ref a).a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [Real.log_mul hp ((Re.line a t).pos z hz).ne', Real.log_mul hp ((Re.ref a).pos z hz).ne'] at h
  linarith

theorem samePot_line {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (c : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    SamePot Re.R.A Set.univ (potOf Re.R (Re.line c t)) ((S.potT c t).pullback Re.π Re.holo.1) := by
  intro x _
  obtain ⟨V, hV, hxV, G, hG, hVG⟩ := Re.ref_pot c x (Set.mem_univ x)
  refine ⟨V ∩ Re.R.U x, hV.inter (Re.R.isOpen_U x), ⟨hxV, Re.R.mem_U x⟩, G, ?_, ?_⟩
  · intro j
    exact (hG j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  · rintro y ⟨hyV, hyU⟩
    have hm := Re.R.mem x y hyU
    have ho : SameOrbit (Re.R.lift y y) (Re.R.lift x y) := Re.R.compat y x y ⟨Re.R.mem_U y, hyU⟩
    have e1 := log_line_of_orbit Re c t h0 h1 y _ hm.1 ho
    have e2 : Real.log ((Re.ref c).h (Re.R.lift x y)) - (S.th c).φ (Re.π x) (Re.π y) = (G y).re := hVG y hyV
    show Real.log ((Re.line c t).h (Re.R.lift x y)) -
      ((S.th c).φ (Re.π x) (Re.π y) + S.phT c t (Re.π y)) = (G y).re
    linarith

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (Q.isOpen_U x)
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ Q.U x
      rw [(A.chart j).left_inv hj]
      exact Q.mem_U x⟩
  exact ((h.1 x j).contDiffAt (hopen.mem_nhds hmem)).of_le (by
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    exact h2)

theorem continuous_of_smooth {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {f : X → ℝ}
    (h : A.Smooth f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ :=
    ⟨(A.chart j).map_source hj, Set.mem_univ _⟩
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ) := by
    simpa using (A.chart j).open_target
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (h j).continuousOn.continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp h1 ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem step_eq (hR : RatRStatement) (hB : ResBridgeStatement) (hG : GoodProjExistsStatement) (hA : AvoidStatement)
    (II : IntersectionSystem) (hI : IsIntersectionFamily (II K ι)) {P : Ideal (MRing ι)} {D : ℕ} {τ : Type}
    {S : AnSys D τ} (Re : Realis S P) (a₁ a₂ : τ) (f g : MRing ι) (d : S.X → ℝ)
    (hiso : IsLineIso P (Re.ref a₁).a (Re.ref a₂).a f g) (hd : S.A.Smooth d)
    (hlog : ∀ x, ∀ u v : MRing ι, u * f - v * g ∈ P → evC (Re.R.lift x x) u ≠ 0 →
      d (Re.π x) = Real.log (‖evC (Re.R.lift x x) v‖ / ‖evC (Re.R.lift x x) u‖ *
        (Re.ref a₂).h (Re.R.lift x x) / (Re.ref a₁).h (Re.R.lift x x)))
    (u : Fin D → τ) (t : ℝ) (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    II K ι P (D + 1) (Fin.snoc (fun j => Re.line (u j) t) (Re.line a₁ t)) -
        II K ι P (D + 1) (Fin.snoc (fun j => Re.line (u j) t) (Re.line a₂ t)) =
      Re.deg * mInt S.A (fun j => S.potT (u j) t) (fun x => S.phT a₁ t x - S.phT a₂ t x - d x) := by
  have hl₁ := Re.line_smooth a₁ t h0 h1
  have hl₂ := Re.line_smooth a₂ t h0 h1
  have hIso : IsLineIso P (Re.line a₁ t).a (Re.line a₂ t).a f g := by
    rw [Re.line_deg, Re.line_deg]
    exact hiso
  obtain ⟨w, hw, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.defect_exists_smooth K ι P Re.J D Re.R (Re.line a₁ t) (Re.line a₂ t) f g Re.arith.2.1 hIso hl₁ hl₂
  have h := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.inter_sub_eq_neg_mInt hR hB hG hA K ι (II K ι) hI P Re.J D Re.R (fun j => Re.line (u j) t) (Re.line a₁ t)
    (Re.line a₂ t) f g w Re.arith (fun j => Re.line_smooth _ t h0 h1) hl₁ hl₂ hIso hw
  rw [h]
  have hval : ∀ x, w (Re.R.lift x x) = -(S.phT a₁ t (Re.π x) - S.phT a₂ t (Re.π x) - d (Re.π x)) := by
    intro x
    have hz := Re.R.mem x x (Re.R.mem_U x)
    obtain ⟨p, q, hpq, hp, hq⟩ := exists_pair_ne hiso.2 hz
    have e0 := hw _ hz p q hpq hp
    have e1 := hlog x p q hpq hp
    have r₁ := Re.line_eq a₁ t h0 h1 x
    have r₂ := Re.line_eq a₂ t h0 h1 x
    have hc : 0 < ‖evC (Re.R.lift x x) q‖ / ‖evC (Re.R.lift x x) p‖ :=
      div_pos (norm_pos_iff.2 hq) (norm_pos_iff.2 hp)
    have l₁ := (Re.line a₁ t).pos _ hz.1
    have l₂ := (Re.line a₂ t).pos _ hz.1
    have f₁ := (Re.ref a₁).pos _ hz.1
    have f₂ := (Re.ref a₂).pos _ hz.1
    rw [Real.log_div (mul_pos hc l₂).ne' l₁.ne', Real.log_mul hc.ne' l₂.ne'] at e0
    rw [Real.log_div (mul_pos hc f₂).ne' f₁.ne', Real.log_mul hc.ne' f₂.ne'] at e1
    linarith
  have hpot : ∀ j, IsPotential S.A (S.potT (u j) t) := fun j =>
    isPotentialAdd S.A _ _ (S.sing (u j)).1 (isPotential_ofFun S.A _ ((S.reg (u j)).2.2 t h0 h1).1)
  have hcont : Continuous fun x => -(S.phT a₁ t x - S.phT a₂ t x - d x) :=
    (((continuous_of_smooth S.A ((S.reg a₁).2.2 t h0 h1).1).sub
      (continuous_of_smooth S.A ((S.reg a₂).2.2 t h0 h1).1)).sub (continuous_of_smooth S.A hd)).neg
  have hcongr := (GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot D Re.R.X Re.R.A Set.univ
    (fun j => potOf Re.R (Re.line (u j) t)) (fun j => (S.potT (u j) t).pullback Re.π Re.holo.1)
    (fun x => w (Re.R.lift x x))
    ((fun x => -(S.phT a₁ t x - S.phT a₂ t x - d x)) ∘ Re.π)
    (by simp [IsNull]) (fun j => samePot_line Re (u j) t h0 h1)
    (fun j x _ => isC2At_of_isPotential Re.R.A (isPotentialPullback S.A Re.R.A Re.π Re.holo _ (hpot j)) x)
    (fun x _ => hval x)).1
  rw [hcongr, degreeFormula S.A Re.R.A Re.π Re.holo Re.deg Re.br Re.degree (fun j => S.potT (u j) t) hpot _ hcont,
    mInt_neg_integrand]
  ring

theorem cmp_one : Inputs → AvoidStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (σ : Type) (S : AnSys D (σ ⊕ σ)) (Re : Realis S P) (f g : σ → MRing ι) (d : σ → S.X → ℝ), (∀ a, IsLineIso P (Re.ref (Sum.inl a)).a (Re.ref (Sum.inr a)).a (f a) (g a)) → (∀ a, S.A.Smooth (d a)) → (∀ a, ∀ y ∈ S.open', S.ph (Sum.inl a) y = S.ph (Sum.inr a) y + d a y) → (∀ a x, ∀ u v : MRing ι, u * f a - v * g a ∈ P → evC (Re.R.lift x x) u ≠ 0 → d a (Re.π x) = Real.log (‖evC (Re.R.lift x x) v‖ / ‖evC (Re.R.lift x x) u‖ * (Re.ref (Sum.inr a)).h (Re.R.lift x x) / (Re.ref (Sum.inl a)).h (Re.R.lift x x))) → ∀ w : Fin (D + 1) → σ, Tendsto (fun t => Re.num II t (fun j => Sum.inl (w j)) - Re.num II t (fun j => Sum.inr (w j))) (𝓝[>] 0) (𝓝 0) := by
  intro hIn hA II hII K _ ι _ P D σ S Re f g d hiso hd hph hlog w
  have hI : IsIntersectionFamily (II K ι) := hII.1 K ι
  have ht : 0 < S.t₀ := (S.reg (Sum.inl (w 0))).1
  have hdeg : (Re.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re.deg_pos.ne'
  have hstep : ∀ i : Fin (D + 1), Tendsto (fun t =>
      Re.num II t (fun j => if j < i then Sum.inr (w j) else Sum.inl (w j)) -
        Re.num II t (fun j => if j ≤ i then Sum.inr (w j) else Sum.inl (w j))) (𝓝[>] 0) (𝓝 0) := by
    intro i
    let c : Fin (D + 1) → σ ⊕ σ := fun j => if j < i then Sum.inr (w j) else Sum.inl (w j)
    let c' : Fin (D + 1) → σ ⊕ σ := fun j => if j ≤ i then Sum.inr (w j) else Sum.inl (w j)
    let u : Fin D → σ ⊕ σ := fun j => c (i.succAbove j)
    have hT := _root_.GlobalTheory.CompanionTheory.Ar.PB.an_two_weights_close hIn.convergenceSigned D σ S d hd hph (w i) u
    refine hT.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT ht] with t ht'
    have h0 := ht'.1
    have h1 := ht'.2
    have hci : c i = Sum.inl (w i) := by simp [c]
    have hci' : c' i = Sum.inr (w i) := by simp [c']
    have hcc : ∀ j : Fin D, c' (i.succAbove j) = u j := by
      intro j
      have hne : i.succAbove j ≠ i := Fin.succAbove_ne i j
      have hiff : i.succAbove j ≤ i ↔ i.succAbove j < i := ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩
      simp only [c', u, c, hiff]
    have s₁ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.movePositionToLast K ι (II K ι) hI P D (fun j => Re.line (c j) t) i Re.arith
      (fun j => Re.line_smooth _ t h0 h1)
    have s₂ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.movePositionToLast K ι (II K ι) hI P D (fun j => Re.line (c' j) t) i Re.arith
      (fun j => Re.line_smooth _ t h0 h1)
    simp only [hci, hci', hcc] at s₁ s₂
    have hs := step_eq hIn.ratR (_root_.GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds) GlobalTheory.CompanionTheory.Ar.Link.goodProjExistsStatement_holds hA II hI Re
      (Sum.inl (w i)) (Sum.inr (w i)) (f (w i)) (g (w i)) (d (w i)) (hiso (w i)) (hd (w i)) (hlog (w i)) u t h0 h1
    show mInt S.A _ _ = Re.num II t c - Re.num II t c'
    simp only [Realis.num]
    rw [s₁, s₂, ← sub_div, hs, mul_div_cancel_left₀ _ hdeg]
  have hsum := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) => hstep i
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr fun t => ?_
  exact (_root_.GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions (σ ⊕ σ) (D + 1) (Re.num II t) _ _).symm

end GlobalTheory.CompanionTheory.Ar.Cmp.OneModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalFrameOfTwistGeneration
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

theorem frames_at_point : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] {κ : Type} (x : κ → Ω) (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) (m n r : ℕ) (V : Submodule Ω E)
    (φ : Fin n → Module.Dual Ω E) (cc : Fin r → E) (hV : L.IsVB r V) (hli : LinearIndependent Ω cc)
    (hsp : Submodule.span Ω (Set.range cc) = V) (hG : IsTwistGen ξ x L m φ) (P : Cpt ξ) (c₁ : κ)
    (hc : InChart ξ x c₁ P),
    ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin n) (Fin r) Ω) (B : Matrix (Fin r) (Fin n) Ω),
      T.det ≠ 0 ∧ Matrix.of (fun j a => φ j (cc a)) * T = (x c₁ ^ m) • C ∧ B * C = 1 ∧
        (∀ j a, C j a ∈ regAt ξ P) ∧ ∀ a j, B a j ∈ regAt ξ P := by
  intro X Ω _ ξ E _ _ κ x L m n r V φ cc hV hli hsp hG P c₁ hc
  obtain ⟨U, hPU, b, hbV, hfr⟩ := (show L.IsVBOn Set.univ r V from hV) P (Set.mem_univ _)
  have hbP : L.IsFrameAt b P := hfr P (Set.mem_univ _) hPU
  obtain ⟨B, hBreg, hCreg, hBC⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse X Ω ξ E κ x L m n r φ hG P c₁ hc b hbP
  have hmem : ∀ a, ∃ t : Fin r → Ω, ∑ l, t l • cc l = b a := by
    intro a
    have hba : b a ∈ Submodule.span Ω (Set.range cc) := by
      rw [hsp, ← hbV]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 hba
  choose t ht using hmem
  refine ⟨Matrix.of fun l a => t a l, Matrix.of (fun j a => φ j (b a) / x c₁ ^ m), B, ?_, ?_, hBC, ?_, hBreg⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hli_b := hbP.1
    rw [Fintype.linearIndependent_iff] at hli_b
    have hcol : ∀ l, ∑ a, t a l * v a = 0 := fun l => by
      simpa [Matrix.mulVec, dotProduct] using congrFun hv l
    have hsum : ∑ a, v a • b a = 0 := by
      calc ∑ a, v a • b a = ∑ a, v a • ∑ l, t a l • cc l := by simp only [ht]
        _ = ∑ l, (∑ a, t a l * v a) • cc l := by
          simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]
        _ = 0 := by simp [hcol]
    exact hv0 (funext fun a => hli_b v hsum a)
  · ext j a
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : ∑ l, φ j (cc l) * t a l = φ j (b a) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← ht a, map_sum]
      simp only [map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [h1]
    by_cases hx : x c₁ ^ m = 0
    · exfalso
      have h2 := congrFun (congrFun hBC a) a
      simp [Matrix.mul_apply, hx, Matrix.one_apply] at h2
    · field_simp
  · intro j a
    exact hCreg j a

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelMonomialWeightProductStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_monomial_weight_product : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (Φ : Type) [Field Φ] (y : K₀ ⊕ StepIx Ψ p q → Φ), (∀ k, y k ≠ 0) → ∀ (τ : Ψ) (i : Fin (p + q)), (∀ h1 : (i : ℕ) < p, ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (((i : ℕ) + 1) * m (.inl τ)) / y (.inr ⟨.inl τ, ⟨i, h1⟩⟩)) ∧ (∀ h1 : p ≤ (i : ℕ), ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (p * m (.inl τ) + ((i : ℕ) - p + 1) * m (.inr τ)) / ((if h0 : 0 < p then y (.inr ⟨.inl τ, ⟨p - 1, by show _ < p; omega⟩⟩) else 1) * y (.inr ⟨.inr τ, ⟨(i : ℕ) - p, by have := i.2; show _ < q; omega⟩⟩))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial.step_monomial | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial.step_monomial | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial.step_monomial <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NzEqNzOfAndPos
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NzCase

theorem nz_eq_nzOf_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) (r : ℕ) (y : Fin r → Λ), IsCMFam σ → IsIsoSub R.form I → (∀ a, y a ∈ I) → LinearIndependent (𝓞 E) y → (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 → R.nz σ I = R.nzOf σ I y ∧ 0 < R.nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ I r y hσ hI hy hli hidx
  by_cases hbot : I = ⊥
  · subst hbot
    have hy0 : ∀ a, y a = 0 := fun a => by simpa using hy a
    have hr : r = 0 := by
      by_contra h
      exact hli.ne_zero (⟨0, Nat.pos_of_ne_zero h⟩ : Fin r) (hy0 _)
    subst hr
    have hno : ¬ ∃ r v, IsNzFamily (⊥ : Submodule (𝓞 E) Λ) r v := by
      rintro ⟨ρ, v, h1, hv, hl, -⟩
      exact hl.ne_zero (⟨0, h1⟩ : Fin ρ) (by simpa using hv ⟨0, h1⟩)
    have hnz : R.nz σ (⊥ : Submodule (𝓞 E) Λ) = 1 := by
      simp only [RiemLat.nz]
      exact dif_neg hno
    have hof : R.nzOf σ (⊥ : Submodule (𝓞 E) Λ) y = 1 := by
      have hs : Submodule.span (𝓞 E) (Set.range y) = ⊥ := by
        simp [Set.range_eq_empty]
      simp [RiemLat.nzOf, hs]
    rw [hnz, hof]
    exact ⟨rfl, one_pos⟩
  · have hr : 1 ≤ r := by
      by_contra h
      have hr0 : r = 0 := by omega
      subst hr0
      have hs : Submodule.span (𝓞 E) (Set.range y) = ⊥ := by
        simp [Set.range_eq_empty]
      have hb : (⊥ : Submodule (𝓞 E) Λ).toAddSubgroup = ⊥ := rfl
      rw [hs, hb, AddSubgroup.relIndex_bot_left] at hidx
      haveI : Finite I.toAddSubgroup := Nat.finite_of_card_ne_zero hidx
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      haveI := R.free
      have hfin : IsOfFinAddOrder (⟨x, hx⟩ : I.toAddSubgroup) := isOfFinAddOrder_of_finite _
      obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hfin
      have hnx' : n • x = 0 := congrArg Subtype.val hnx
      have hzx : (n : ℤ) • x = 0 := by rw [natCast_zsmul]; exact hnx'
      exact hx0 ((smul_eq_zero.1 hzx).resolve_left (by exact_mod_cast hn.ne'))
    have hfam : IsNzFamily I r y := ⟨hr, hy, hli, hidx⟩
    have h := (_root_.LevelTowerAlt.isotropic_submodule_nonzero_family E g Λ Ψ R σ I hσ hI hbot).2 r y hfam
    exact ⟨h.1, h.2.1⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.NzCase
end

