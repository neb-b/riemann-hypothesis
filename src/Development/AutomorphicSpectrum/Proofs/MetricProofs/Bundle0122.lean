module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralTendstoOffDivisor
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0021
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0119

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentOrbitEquality
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

section Minors

variable {N : ℕ}

theorem minor_self_of_lowerUni {L : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) (C : Finset (Fin N)) :
    minorIJ L C C = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl, Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => hL.1 _
  · intro a b hab
    exact hL.2 _ _ ((C.orderEmbOfFin rfl).strictMono hab)

theorem minor_insert_of_lowerUni {L : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) {C : Finset (Fin N)} {s r : Fin N}
    (hs : s ∈ C) (hmax : ∀ a ∈ C, a ≤ s) (hr : s < r) : minorIJ L (insert r (C.erase s)) C = L r s := by
  have hrn : r ∉ C.erase s := fun h => absurd (hmax r (Finset.mem_of_mem_erase h)) (not_le.2 hr)
  have hcard : (insert r (C.erase s)).card = C.card := by
    rw [Finset.card_insert_of_notMem hrn, Finset.card_erase_of_mem hs]
    have := Finset.card_pos.2 ⟨s, hs⟩
    omega
  unfold minorIJ
  rw [dite_eq_left hcard]
  set e := C.orderEmbOfFin rfl with he
  have hmem : ∀ i, e i ∈ C := fun i => Finset.orderEmbOfFin_mem C rfl i
  obtain ⟨m, hm⟩ : ∃ m, e m = s := by
    have : s ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]
      exact hs
    exact this
  have hle : ∀ i, i ≤ m := fun i => e.le_iff_le.1 (by rw [hm]; exact hmax _ (hmem i))
  let f : Fin C.card → Fin N := fun i => if i = m then r else e i
  have hf_ne : ∀ i, i ≠ m → f i = e i := fun i h => if_neg h
  have hf_m : f m = r := if_pos rfl
  have hmono : StrictMono f := by
    intro a b hab
    have ham : a ≠ m := fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab)
    rw [hf_ne a ham]
    by_cases hb : b = m
    · rw [hb, hf_m]
      exact lt_of_le_of_lt (hmax _ (hmem a)) hr
    · rw [hf_ne b hb]
      exact e.strictMono hab
  have hin : ∀ i, f i ∈ insert r (C.erase s) := by
    intro i
    by_cases hi : i = m
    · rw [hi, hf_m]
      exact Finset.mem_insert_self _ _
    · rw [hf_ne i hi]
      refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h => hi ?_, hmem i⟩)
      exact e.injective (h.trans hm.symm)
  have hfe : f = (insert r (C.erase s)).orderEmbOfFin hcard := Finset.orderEmbOfFin_unique hcard hin hmono
  rw [← hfe, Matrix.det_of_lowerTriangular]
  · rw [Finset.prod_eq_single m]
    · rw [Matrix.submatrix_apply, hf_m, hm]
    · intro i _ hi
      rw [Matrix.submatrix_apply, hf_ne i hi]
      exact hL.1 _
    · intro h
      exact absurd (Finset.mem_univ m) h
  · intro a b hab
    have hab' : a < b := hab
    have ham : a ≠ m := fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab')
    rw [Matrix.submatrix_apply, hf_ne a ham]
    exact hL.2 _ _ (e.strictMono hab')

end Minors

theorem flag_uniq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ L L' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → (∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ')) → SameOrbit (FC.flagPt M (BM.F l) (FC.bvec BM l b) L) (FC.flagPt M (BM.F l) (FC.bvec BM l b) L') → L = L' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb L L' hL hL' ho
  obtain ⟨hβ, hg, -, -⟩ := bvec_good K ι Φ y Ψ N j M n BM l b hb
  obtain ⟨c, -, ez⟩ := ho
  have hjN := M.j_le
  have key : ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → ∃ a : ℂ, ∀ I,
      minorIJ (L τ') I (stepCols N j i) = a * minorIJ (L' τ') I (stepCols N j i) := by
    intro τ' i hi
    obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
      Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    refine ⟨c k, fun I => ?_⟩
    have h0 := FibreCount.plucker_inj M (BM.isFrame l) hβ hg hk
      (fun I => minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i))
      (fun I hI => by
        show minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i) = 0
        rw [FibreCount.minor_off_step hjN hi (hL τ').1 hI, FibreCount.minor_off_step hjN hi (hL' τ').1 hI]
        ring)
      (fun m => by
        have x := congrFun ez ⟨k, m⟩
        simp only at x
        rw [flagPt_step M (BM.F l) _ L hk m, flagPt_step M (BM.F l) _ L' hk m] at x
        simp only [mul_sub, Finset.sum_sub_distrib]
        rw [x, Finset.mul_sum, sub_eq_zero]
        exact Finset.sum_congr rfl fun _ _ => by ring) I
    exact sub_eq_zero.1 h0
  have ent : ∀ (τ' : Ψ) (i : Fin N) (s r : Fin N), IsProperStep N j i → s ∈ stepCols N j i →
      (∀ a ∈ stepCols N j i, a ≤ s) → s < r → L τ' r s = L' τ' r s := by
    intro τ' i s r hi hs hmax hr
    obtain ⟨a, ha⟩ := key τ' i hi
    have h1 := ha (stepCols N j i)
    rw [minor_self_of_lowerUni (hL τ').2, minor_self_of_lowerUni (hL' τ').2, mul_one] at h1
    have h2 := ha (insert r ((stepCols N j i).erase s))
    rw [minor_insert_of_lowerUni (hL τ').2 hs hmax hr, minor_insert_of_lowerUni (hL' τ').2 hs hmax hr, ← h1,
      one_mul] at h2
    exact h2
  funext τ'
  ext r s
  rcases lt_trichotomy s r with hsr | hsr | hsr
  · have hsr' : (s : ℕ) < r := hsr
    by_cases hblk : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)
    · by_cases hs : (s : ℕ) < N - j
      · have hr : (r : ℕ) < N - j := hblk.2 hs
        refine ent τ' ⟨s + j, by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr
        · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_neg (by omega)]
          omega
        · intro a ha
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [if_neg (by omega)] at ha
          exact Fin.le_def.2 (by omega)
      · have hr : ¬ (r : ℕ) < N - j := fun h => hs (hblk.1 h)
        have hrN := r.2
        refine ent τ' ⟨s - (N - j), by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr
        · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_pos (by omega)]
          omega
        · intro a ha
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [if_pos (by omega)] at ha
          exact Fin.le_def.2 (by omega)
    · rw [(hL τ').1 r s hblk, (hL' τ').1 r s hblk]
  · rw [hsr, (hL τ').2.1, (hL' τ').2.1]
  · rw [(hL τ').2.2 r s hsr, (hL' τ').2.2 r s hsr]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralLimitOnModel
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem continuous_of_atlasSmooth {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    have := (hf j).continuousOn
    simpa [Set.preimage_univ, Set.inter_univ] using this
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    (h1.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).comp
      ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

theorem tendsto_ptsIntegral_of_chart_conv : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas) (Θ : LocPot M.Xc) (Pp : Fin n → LocPot M.Xc) (f : Fin n → M.Xc → ℝ) (fT : Fin n → ℝ → M.Xc → ℝ) (G : M.Xc → ℝ) (GT : ℝ → M.Xc → ℝ) (C : ℝ) (L : ℝ → Fin n → HermLine ι) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ), IsArithVar P (n + 1) → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → (∀ i, IsPotential M.atlas (Pp i)) → (∀ i, M.atlas.SmoothOn R.Yo (f i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, M.atlas.Smooth (fT i t) ∧ IsPsh M.atlas (Pp i + LocPot.ofFun (fT i t) + Θ) ∧ ∀ x ∈ R.Yo, |fT i t x| ≤ C + C * Real.log (R.r x) ∧ fT i t x ≤ C) → (∀ i, ∀ j, ∀ K' ⊆ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fT i t ∘ (M.atlas.chart j).symm) (f i ∘ (M.atlas.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm)) (fderiv ℝ (f i ∘ (M.atlas.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm))) (fderiv ℝ (fderiv ℝ (f i ∘ (M.atlas.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (GT t) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i x, ∀ y₀ ∈ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G' : M.Xc → ℂ, M.atlas.HoloOn U G' ∧ ∀ y' ∈ U, (Pp i + LocPot.ofFun (fT i t)).φ x y' - Real.log ((L t i).h (s y')) = (G' y').re) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ mcPts P, g t z = GT t (M.proj z)) → ∃ l : ℝ, Tendsto (fun t => ptsIntegral P (pot (L t)) (g t)) (𝓝[>] 0) (𝓝 l) := by
  intro K _ ι _ P n M R Θ Pp f fT G GT C L g hV hΘ hΘp hP hf hfT hconv hGT hGc hrel hg
  classical
  by_cases hQ : ∃ Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ), IsGoodProj P Q
  · have hYo := (_root_.GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part n M.Xc M.atlas R).1
    have hmeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable M.Xc ℝ (borel M.Xc) _ (R.Yo.indicator (GT t)) ∧
        ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x) := by
      filter_upwards [hGT] with t ht
      refine ⟨?_, ht.2⟩
      letI : MeasurableSpace M.Xc := borel M.Xc
      haveI : BorelSpace M.Xc := ⟨rfl⟩
      exact (continuous_of_atlasSmooth ht.1).measurable.indicator hYo.measurableSet
    obtain ⟨-, hint, hlim⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.mixed_integral_tendsto_of_C2_off_divisor n M.Xc M.atlas R Θ hΘ hΘp Pp f fT G GT C hP hf hfT hconv
      hmeas hGc
    refine ⟨_, hlim.congr' ?_⟩
    filter_upwards [hint, hfT, hGT, hrel, hg] with t hit hft hgt hrt hgt'
    have hpush := _root_.GlobalTheory.CompanionTheory.Ar.Giv.push_chart_integrals K ι P n M hQ.choose Set.univ ∅ ∅ (fun _ => 1) (L t)
      (fun i => Pp i + LocPot.ofFun (fT i t)) (g t) (GT t) hV hQ.choose_spec isOpen_univ
      (fun j => by simp)
      (fun Ψ _ => by simp)
      (fun i x => by
        intro j
        have h1 := (hP i).1 x j
        have h2 := (hft i).1 j
        have h3 := h1.add (h2.mono (fun y hy => ⟨hy.1, Set.mem_univ _⟩))
        refine (h3.mono ?_).congr ?_
        · rintro y ⟨hy, hy'⟩
          exact ⟨hy, hy'.1.1⟩
        · intro y _
          rfl)
      (fun i x y₀ hy₀ => by
        obtain ⟨U, hU, hyU, hUs, s, hs, hsp, G', hG', hrel'⟩ := hrt i x y₀ hy₀
        exact ⟨U, hU, hyU, hUs, s, hs, hsp, G', hG', fun y' hy' => by
          simpa using hrel' y' hy'⟩)
      (fun z hz _ _ _ => hgt' z hz)
      (fun j => ((continuous_of_atlasSmooth hgt.1).comp_continuousOn
        (M.atlas.chart j).continuousOn_symm).aestronglyMeasurable (M.atlas.chart j).open_target.measurableSet)
    have h3 := (hpush.2.2 hit).2
    have hpot : (fun i z => (fun _ : Fin n => (1 : ℝ)) i * Real.log ((L t i).h z)) = pot (L t) := by
      funext i z
      simp [pot]
    rw [hpot] at h3
    rw [ptsIntegral, dite_eq_left hQ, h3]
  · refine ⟨0, ?_⟩
    have : (fun t => ptsIntegral P (pot (L t)) (g t)) = fun _ => (0 : ℝ) := by
      funext t
      rw [ptsIntegral, dite_eq_right hQ]
    rw [this]
    exact tendsto_const_nhds

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelPointsIntegrableStatementHolds
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree

section Transfer

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem modelChart_injOn (χ φ : OpenPartialHomeomorph X (Fin e → ℂ)) :
    Set.InjOn (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source) := by
  intro u hu u' hu' h
  have h1 : χ.symm u = χ.symm u' := φ.injOn hu.2 hu'.2 h
  have h2 := congrArg χ h1
  rwa [χ.right_inv hu.1, χ.right_inv hu'.1] at h2

theorem modelChart_null (χ φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : AnalyticOnNhd ℂ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source)) (E : Set X)
    (hE : volume (χ.target ∩ χ.symm ⁻¹' E) = 0) :
    volume (φ.target ∩ φ.symm ⁻¹' (E ∩ χ.source)) = 0 := by
  have hd : DifferentiableOn ℝ (φ ∘ χ.symm)
      (χ.target ∩ χ.symm ⁻¹' φ.source ∩ χ.symm ⁻¹' E) :=
    (hσ.differentiableOn.restrictScalars ℝ).mono Set.inter_subset_left
  have h0 : volume (χ.target ∩ χ.symm ⁻¹' φ.source ∩ χ.symm ⁻¹' E) = 0 :=
    measure_mono_null (t := χ.target ∩ χ.symm ⁻¹' E) (fun u hu => ⟨hu.1.1, hu.2⟩) hE
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd h0
  refine measure_mono_null ?_ himg
  rintro y ⟨hy, hyE, hyχ⟩
  refine ⟨χ (φ.symm y), ⟨⟨χ.map_source hyχ, ?_⟩, ?_⟩, ?_⟩
  · show χ.symm (χ (φ.symm y)) ∈ φ.source
    rw [χ.left_inv hyχ]; exact φ.map_target hy
  · show χ.symm (χ (φ.symm y)) ∈ E
    rw [χ.left_inv hyχ]; exact hyE
  · simp [χ.left_inv hyχ, φ.right_inv hy]

theorem modelChart_integrableOn (χ φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : AnalyticOnNhd ℂ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source)) (v : X → ℝ)
    (hv : ∀ Q ⊆ χ.target, IsCompact Q → IntegrableOn (fun y => v (χ.symm y)) Q)
    {Q : Set (Fin e → ℂ)} (hQ : IsCompact Q) (hQs : Q ⊆ φ.target ∩ φ.symm ⁻¹' χ.source) :
    IntegrableOn (fun y => v (φ.symm y)) Q := by
  have hSo : IsOpen (χ.target ∩ χ.symm ⁻¹' φ.source) :=
    χ.isOpen_inter_preimage_symm φ.open_source
  have hρc : ContinuousOn (χ ∘ φ.symm) Q :=
    χ.continuousOn.comp (φ.continuousOn_symm.mono fun y hy => (hQs hy).1) fun y hy => (hQs hy).2
  have hQ' : IsCompact ((χ ∘ φ.symm) '' Q) := hQ.image_of_continuousOn hρc
  have hQS : (χ ∘ φ.symm) '' Q ⊆ χ.target ∩ χ.symm ⁻¹' φ.source := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨χ.map_source (hQs hy).2, ?_⟩
    show χ.symm (χ (φ.symm y)) ∈ φ.source
    rw [χ.left_inv (hQs hy).2]; exact φ.map_target (hQs hy).1
  have himg : (φ ∘ χ.symm) '' ((χ ∘ φ.symm) '' Q) = Q := by
    rw [Set.image_image]
    refine Set.ext fun y => ⟨?_, fun hy => ⟨y, hy, ?_⟩⟩
    · rintro ⟨y', hy', rfl⟩
      simpa [χ.left_inv (hQs hy').2, φ.right_inv (hQs hy').1] using hy'
    · simp [χ.left_inv (hQs hy).2, φ.right_inv (hQs hy).1]
  have hσR : AnalyticOnNhd ℝ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source) :=
    hσ.restrictScalars
  have hder : ∀ u ∈ (χ ∘ φ.symm) '' Q,
      HasFDerivWithinAt (φ ∘ χ.symm) (fderiv ℝ (φ ∘ χ.symm) u) ((χ ∘ φ.symm) '' Q) u :=
    fun u hu => ((hσR u (hQS hu)).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  have hinj : Set.InjOn (φ ∘ χ.symm) ((χ ∘ φ.symm) '' Q) := (modelChart_injOn χ φ).mono hQS
  have hcont : ContinuousOn (fun u => |(fderiv ℝ (φ ∘ χ.symm) u).det|) ((χ ∘ φ.symm) '' Q) := by
    have h1 : ContinuousOn (fderiv ℝ (φ ∘ χ.symm)) (χ.target ∩ χ.symm ⁻¹' φ.source) :=
      (hσR.fderiv).continuousOn
    exact (ContinuousLinearMap.continuous_det.comp_continuousOn (h1.mono hQS)).abs
  have hint := (hv _ (fun u hu => (hQS hu).1) hQ').continuousOn_mul hcont hQ'
  rw [← himg]
  refine (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hQ'.measurableSet hder
    hinj _).2 ?_
  refine hint.congr_fun (fun u hu => ?_) hQ'.measurableSet
  have hu := hQS hu
  simp only [smul_eq_mul, Function.comp_apply, φ.left_inv hu.2]

theorem modelChart_integrableOn_cover {n : ℕ} (χ : Fin n → OpenPartialHomeomorph X (Fin e → ℂ))
    (φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : ∀ k, AnalyticOnNhd ℂ (φ ∘ (χ k).symm) ((χ k).target ∩ (χ k).symm ⁻¹' φ.source))
    (hcov : ∀ x, ∃ k, x ∈ (χ k).source) (v : X → ℝ)
    (hv : ∀ k, ∀ Q ⊆ (χ k).target, IsCompact Q → IntegrableOn (fun y => v ((χ k).symm y)) Q) :
    LocallyIntegrableOn (fun y => v (φ.symm y)) φ.target := by
  intro y hy
  obtain ⟨k, hk⟩ := hcov (φ.symm y)
  have hWo : IsOpen (φ.target ∩ φ.symm ⁻¹' (χ k).source) :=
    φ.isOpen_inter_preimage_symm (χ k).open_source
  obtain ⟨Q, hQn, hQs, hQc⟩ := local_compact_nhds (hWo.mem_nhds ⟨hy, hk⟩)
  exact ⟨Q, mem_nhdsWithin_of_mem_nhds hQn, modelChart_integrableOn (χ k) φ (hσ k) v (hv k) hQc hQs⟩

theorem modelChart_null_cover {n : ℕ} (χ : Fin n → OpenPartialHomeomorph X (Fin e → ℂ))
    (φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : ∀ k, AnalyticOnNhd ℂ (φ ∘ (χ k).symm) ((χ k).target ∩ (χ k).symm ⁻¹' φ.source))
    (hcov : ∀ x, ∃ k, x ∈ (χ k).source) (E : Set X)
    (hE : ∀ k, volume ((χ k).target ∩ (χ k).symm ⁻¹' E) = 0) :
    volume (φ.target ∩ φ.symm ⁻¹' E) = 0 := by
  refine measure_mono_null (t := ⋃ k, φ.target ∩ φ.symm ⁻¹' (E ∩ (χ k).source)) ?_
    (measure_iUnion_null fun k => modelChart_null (χ k) φ (hσ k) E (hE k))
  rintro y ⟨hy, hyE⟩
  obtain ⟨k, hk⟩ := hcov (φ.symm y)
  exact Set.mem_iUnion.2 ⟨k, hy, hyE, hk⟩

end Transfer

theorem modelPtsIntegrable : ModelPtsIntegrable.Statement := by
  intro K _ ι _ P e M n ψ L c N E v g hV hL hN hψ hcov hE hv hg Ψ hΨ
  obtain ⟨Φ₀, hΦ₀, hloc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.exists_potential_of_smoothHerm K ι P e M L hL
  have hΦ : IsPotential M.atlas (Φ₀.rsmul c) := isPotentialRsmul M.atlas c Φ₀ hΦ₀
  have hli : ∀ j, LocallyIntegrableOn (fun y => v ((M.atlas.chart j).symm y))
      (M.atlas.chart j).target := fun j =>
    modelChart_integrableOn_cover ψ (M.atlas.chart j) (fun k => (hψ k j).2) hcov v hv
  have hint : ∀ j, ∀ Q ⊆ (M.atlas.chart j).target, IsCompact Q →
      IntegrableOn (fun y => v ((M.atlas.chart j).symm y)) Q := fun j Q hQ hQc =>
    (hli j).integrableOn_compact_subset hQ hQc
  have hnull : ∀ j, volume ((M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' ((Set.univ : Set M.Xc)ᶜ ∪ E)) = 0 := fun j => by
    simpa using modelChart_null_cover ψ (M.atlas.chart j) (fun k => (hψ k j).2) hcov E hE
  have hMI : MIntegrable M.atlas (fun _ : Fin e => Φ₀.rsmul c) v := fun j Q hQ hQc =>
    (hint j Q hQ hQc).mul_continuousOn
      ((locDensCont M.atlas _ (fun _ => hΦ) j).mono hQ) hQc
  refine ((_root_.GlobalTheory.CompanionTheory.Ar.Giv.push_chart_integrals K ι P e M Ψ Set.univ E N (fun _ => c) (fun _ => L)
    (fun _ => Φ₀.rsmul c) g v hV hΨ isOpen_univ hnull hN ?_ ?_ ?_ ?_).2.2 hMI).1
  · exact fun _ x j => (hΦ.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  · intro _ x y₀ hy₀
    obtain ⟨U, hUo, hyU, hUs, s, hs, hsh, G, hG, hGe⟩ := hloc x y₀ hy₀
    refine ⟨U, hUo, hyU, hUs, s, hs, hsh, fun z => (c : ℂ) * G z, holoOn_mul M.atlas hG c,
      fun y' hy' => ?_⟩
    have h1 : Φ₀.φ x y' - Real.log (L.h (s y')) = (G y').re := hGe y' hy'
    show c * Φ₀.φ x y' - c * Real.log (L.h (s y')) = ((c : ℂ) * G y').re
    rw [Complex.re_ofReal_mul, ← h1]
    ring
  · exact fun z hz hzN _ hzE => hg z hz hzN hzE
  · exact fun j => (hli j).aestronglyMeasurable

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimChartComponents
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)

theorem chartComponents_dim : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsCxVar Q e → ∀ J ∈ chartComponents (conePts Q) σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  intro K _ _ ι _ Q e m σ i hQ J hJ
  have hmin : J ∈ (setSegChartIdeal (conePts Q) σ i).minimalPrimes :=
    mem_chartComponents.mp hJ
  have hhom : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  exact segChart_dim hQ.2.1.1 hhom hQ.2.2 σ i hmin

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

