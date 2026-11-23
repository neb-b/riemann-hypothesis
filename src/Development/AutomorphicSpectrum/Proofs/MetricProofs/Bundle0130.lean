module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeNonsimpleFibresEqZero
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreDensityIndependentProjection
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0105
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0019
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.EvalFam
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralDensityIndependentProjection
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep

theorem cx_fibre_finite : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → ∀ y, (setFibre (conePts Q) Ψ y).Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | exact GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite <;> assumption)

theorem cx_posDens_aemeasurable : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    AEMeasurable (cxPosDens (conePts Q) Ψ (pot L) g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable <;> assumption)

theorem cx_simple_null : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) ∧
      ¬ cxSimple (conePts Q) Ψ w} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cxSheetSimpleNull | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cxSheetSimpleNull | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cxSheetSimpleNull <;> assumption)

theorem cxPosDens_split {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {Q : Ideal (MRingOver ℂ ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (E : ℕ → Set ((Σ k, ι k) → ℂ))
    (y : Fin e → ℂ) (hfin : (setFibre (conePts Q) Ψ y).Finite) (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) → ∀ z ∈ conePts Q, segre z = w → ∃ k, z ∈ E k) :
    ENNReal.ofReal (cxPosDens (conePts Q) Ψ φ g y) =
      ∑' k, ENNReal.ofReal (cxPosDens (conePts Q) Ψ φ ((E k).indicator g) y) := by
  classical
  unfold cxPosDens
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hT0 : ∀ (g' : ((Σ k, ι k) → ℂ) → ℝ) w, 0 ≤ max (setSheetDensity (conePts Q) Ψ φ g' y w) 0 :=
    fun _ _ => le_max_right _ _
  have hpt : ∀ w ∈ hfin.toFinset, ENNReal.ofReal (max (setSheetDensity (conePts Q) Ψ φ g y w) 0) =
      ∑' k, ENNReal.ofReal (max (setSheetDensity (conePts Q) Ψ φ ((E k).indicator g) y w) 0) := by
    intro w hw
    have hw' : w ∈ setFibre (conePts Q) Ψ y := hfin.mem_toFinset.mp hw
    by_cases hs : ∃ γ, IsSetSheet (conePts Q) Ψ y w γ
    · have hz : hs.choose y ∈ conePts Q := hs.choose_spec.2.self_of_nhds.2.1
      obtain ⟨k₀, hk₀⟩ := hcov w hw' hs _ hz hs.choose_spec.1
      rw [tsum_eq_single k₀]
      · simp only [setSheetDensity, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : hs.choose y ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [setSheetDensity, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [setSheetDensity, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 g w), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 _ w)).symm

theorem cx_posPart_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) g y) =
      ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) g y) := by
  intro K _ ι _ Q e Ψ Ψ' L g hP hΨ hΨ' hLs hg hg0
  classical

  set Inv : Set ((Σ k, ι k) → ℂ) → Prop := fun S => ∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    ((fun p => c p.1 * z' p) ∈ S ↔ z' ∈ S) with hInv

  set Gd : ((Σ k, ι k) → ℂ) → Prop := fun z => z ∈ conePts Q ∧
    cxSimple (conePts Q) Ψ ((Ψ (segre z) 0)⁻¹ • segre z) ∧
    cxSimple (conePts Q) Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) with hGd
  have key : ∀ z, ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ Inv W ∧ (Gd z → z ∈ W) ∧
      ∀ E, MeasurableSet E → Inv E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) (E.indicator g) y) =
          ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) (E.indicator g) y) := by
    intro z
    by_cases hz : Gd z
    · obtain ⟨W, hW, hzW, hWi, hWE⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Pub.CxPosLocal.cxPosPart_local K ι Q e Ψ Ψ' L g z hP hΨ hΨ' hLs hg hg0 hz.1 hz.2.1 hz.2.2
      exact ⟨W, hW, hWi, fun _ => hzW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun _ _ _ => Iff.rfl, fun h => absurd h hz, fun E _ _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [cxPosDens, setSheetDensity]
  choose W hWo hWi hzW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨f, hf⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set ((Σ k, ι k) → ℂ) := disjointed (fun k => W (f k)) with hE
  have hEm : ∀ k, MeasurableSet (E k) := MeasurableSet.disjointed fun k => (hWo (f k)).measurableSet
  have hEW : ∀ k, E k ⊆ W (f k) := disjointed_subset _
  have hEd : Pairwise (Function.onFun Disjoint E) := disjoint_disjointed _
  have hEi : ∀ k, Inv (E k) := by
    intro k c z' hc
    simp only [hE, disjointed_eq_inter_compl, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      hWi _ c z' hc]
  have hgE : ∀ k (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (E k).indicator g (fun p => c p.1 * z' p) = (E k).indicator g z' := by
    intro k c z' hc
    simp only [Set.indicator_apply, hEi k c z' hc, hg0 c z' hc]
  have hcov : ∀ z, Gd z → ∃ k, z ∈ E k := by
    intro z hq
    have : z ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨z, hzW z hq⟩
    obtain ⟨i, hiT, hzi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range f := hf ▸ Set.mem_insert_of_mem 0 hiT
    have : z ∈ ⋃ k, E k := by
      rw [hE, iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hzi⟩
    exact Set.mem_iUnion.1 this

  have hae : ∀ B B' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsSetGoodProj (conePts Q) B → IsSetGoodProj (conePts Q) B' →
      (∀ z ∈ conePts Q, cxSimple (conePts Q) B ((B (segre z) 0)⁻¹ • segre z) →
        cxSimple (conePts Q) B' ((B' (segre z) 0)⁻¹ • segre z) → ∃ k, z ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) g y) =
        ∑' k, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) ((E k).indicator g) y) := by
    intro B B' hB hB' hc
    have hnull := measure_union_null (cx_simple_null K ι Q e B hP hB) (_root_.GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null K ι Q e B B' hP hB hB')
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    refine cxPosDens_split _ _ E y (cx_fibre_finite K ι Q e B hP hB y) hEd fun w hw hs z hz hzw => ?_
    have hw1 : B w 0 = 1 := by
      obtain ⟨_, _, _, h⟩ := hw
      rw [h]
      rfl
    have hs1 : cxSimple (conePts Q) B w := by
      by_contra hn
      exact hy (Or.inl ⟨w, hw, hs, hn⟩)
    have hs2 : cxSimple (conePts Q) B' ((B' w 0)⁻¹ • w) := by
      by_contra hn
      exact hy (Or.inr ⟨w, hw, hs1, hn⟩)
    subst hzw
    refine hc z hz ?_ hs2
    rwa [hw1, inv_one, one_smul]
  have hint : ∀ B : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsSetGoodProj (conePts Q) B →
      (∀ᵐ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) g y) =
        ∑' k, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) ((E k).indicator g) y)) →
      ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) g y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) ((E k).indicator g) y) := by
    intro B hB h2
    rw [lintegral_congr_ae h2, lintegral_tsum fun k =>
      (cx_posDens_aemeasurable K ι Q e B L _ hP hB hLs (hg.indicator (hEm k)) (hgE k)).ennreal_ofReal]
  rw [hint Ψ hΨ (hae Ψ Ψ' hΨ hΨ' fun z hz h1 h2 => hcov z ⟨hz, h1, h2⟩),
    hint Ψ' hΨ' (hae Ψ' Ψ hΨ' hΨ fun z hz h1 h2 => hcov z ⟨hz, h2, h1⟩)]
  exact tsum_congr fun k => hWE (f k) (E k) (hEm k) (hEi k) (hEW k)

end GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerBoundHeightOnBoundary
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.lowerBound_height_on_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal x) ∩ mcPts bd) : Set (mcPts (mCoordIdeal x))) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → ∃ (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Rb.X), IsPotential Rb.A L ∧ IsSection Rb.A L s ∧ IsSNC Rb.A L s m W ∧ (∀ p, logNormSec L s p ≤ 0) ∧ (∀ p, p ∈ bdry s ↔ Rb.lift p p ∈ mcPts bd) ∧ ∀ p p', SameOrbit (Rb.lift p' p') (fun q => starRingEnd ℂ (Rb.lift p p q)) → rW L s p' = rW L s p := by
  intro K _ J _ Ω _ _ x n bd hsnc harith _ htor hconj
  obtain ⟨I, hIh, hIle, hIsnc, hIeq⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.exists_homogIdeal x n bd hsnc harith htor
  obtain ⟨Rb, nb, W, hloc⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.exists_res x n I harith hIh hIle hIsnc
  rw [hIeq] at hloc
  obtain ⟨L, s, h1, h2, h3, h4, h5, h6⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.assemble Rb (mcPts (mCoordIdeal x) ∩ mcPts bd)
      (fun z hz c hc => htor z hz c hc) (fun z hz => hconj z hz) nb W hloc
  refine ⟨Rb, L, s, nb, fun _ => 1, W, h1, h2, h3, h4, fun p => ?_, h6⟩
  rw [h5 p]
  exact ⟨fun hp => hp.2, fun hp => ⟨Rb.mem p p (Rb.mem_U p), hp⟩⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem ratR_of_resK :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement :=
  fun h => GroundTheory.Heights₂.Heights.Inter.RatR.proof (ptsIntegrable_of_resK h)

end GlobalTheory.CompanionTheory.Ar.Giv
end

