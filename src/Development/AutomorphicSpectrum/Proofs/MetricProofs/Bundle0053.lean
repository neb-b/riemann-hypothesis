module

public import Mathlib
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
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartSet (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def chartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (chartSet S σ i)

def chartComponents (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Finset (Ideal (MvPolynomial (Fin m) ℂ)) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) ℂ)
    (chartIdeal S σ i)).toFinset

omit [∀ k, Fintype (ι k)] in
theorem mem_chartComponents {S : Set ((Σ k, ι k) → ℂ)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} :
    J ∈ chartComponents S σ i ↔ J ∈ (chartIdeal S σ i).minimalPrimes :=
  Set.Finite.mem_toFinset _

def chartSection [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) : MvPolynomial (Fin m) ℂ :=
  aeval (fun q : Σ k, ι k => (X (σ.symm (Function.update i q.1 q.2)) : MvPolynomial (Fin m) ℂ)) s

def domCell (i : (k : K) → ι k) : Set ((Σ k, ι k) → ℂ) :=
  {z | ∀ i', ‖segre z i'‖ ≤ ‖segre z i‖}


open Classical in
def absLogNorm (A : HermLine ι) (s : MRingOver ℂ ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 then |logNormC A s z| else 0

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NullSetImageUnderHoloMap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.NullImage

theorem isNull_image_of_holoMap : ∀ (e : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X) (Z : Set Y),
    HoloMap B A h → IsNull B Z → IsNull A (h '' Z) := by
  intro e X Y _ _ A B h Z hh hZ k
  have key : ∀ j, volume ((A.chart k ∘ h ∘ (B.chart j).symm) ''
      (((B.chart j).target ∩ (B.chart j).symm ⁻¹' Z) ∩
        ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source)))) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null Set.inter_subset_left (hZ j))
    intro z hz
    exact (((hh.2 j k z hz.2).differentiableAt.restrictScalars ℝ).differentiableWithinAt)
  refine measure_mono_null ?_ (measure_iUnion_null key)
  rintro w ⟨hw, y, hy, hyw⟩
  obtain ⟨j, hj⟩ := B.cover y
  have hsymm : (B.chart j).symm (B.chart j y) = y := (B.chart j).left_inv hj
  have hsrc : h y ∈ (A.chart k).source := by
    rw [hyw]
    exact (A.chart k).map_target hw
  refine Set.mem_iUnion.2 ⟨j, B.chart j y, ⟨⟨(B.chart j).map_source hj, ?_⟩,
    ⟨(B.chart j).map_source hj, ?_⟩⟩, ?_⟩
  · simpa [hsymm] using hy
  · simpa [hsymm] using hsrc
  · simp only [Function.comp_apply, hsymm, hyw]
    exact (A.chart k).right_inv hw

end GlobalTheory.CompanionTheory.Ar.PB.NullImage
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.OrbitChartTransitionAnalytic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem exists_analyticAt_leftInverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] {f : E → F} {u : E} (hf : AnalyticAt ℂ f u)
    (hk : (fderiv ℂ f u : E →ₗ[ℂ] F).ker = ⊥) :
    ∃ Λ : F → E, AnalyticAt ℂ Λ (f u) ∧ ∀ᶠ v in 𝓝 u, Λ (f v) = v := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  let L : F →L[ℂ] E := LinearMap.toContinuousLinearMap g
  have hLf : ∀ x, L (fderiv ℂ f u x) = x := fun x => by
    have := LinearMap.congr_fun hg x
    simpa [L] using this
  let h : E → E := fun v => L (f v)
  have hh : AnalyticAt ℂ h u := (L.analyticAt (f u)).comp hf
  have hd : fderiv ℂ h u = ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) := by
    have h1 : HasFDerivAt h (L.comp (fderiv ℂ f u)) u := L.hasFDerivAt.comp u hf.differentiableAt.hasFDerivAt
    rw [h1.fderiv]
    ext x
    simp [hLf]
  have hs : HasStrictFDerivAt h ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) u := by
    have := hh.hasStrictFDerivAt
    rwa [hd] at this
  have hsrc : u ∈ (hs.toOpenPartialHomeomorph h).source := hs.mem_toOpenPartialHomeomorph_source
  have hcoe : ((hs.toOpenPartialHomeomorph h : OpenPartialHomeomorph E E) : E → E) = h :=
    hs.toOpenPartialHomeomorph_coe
  have han : AnalyticAt ℂ (hs.toOpenPartialHomeomorph h).symm (h u) := by
    have := (hs.toOpenPartialHomeomorph h).analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ E) hsrc
      (by rw [hcoe]; exact hh) (by rw [hcoe]; exact hd)
    rwa [hcoe] at this
  refine ⟨fun y => (hs.toOpenPartialHomeomorph h).symm (L y), ?_, ?_⟩
  · exact AnalyticAt.comp (f := fun y => L y) (g := (hs.toOpenPartialHomeomorph h).symm) han (L.analyticAt (f u))
  · filter_upwards [(hs.toOpenPartialHomeomorph h).open_source.mem_nhds hsrc] with v hv
    have := (hs.toOpenPartialHomeomorph h).left_inv hv
    rwa [hcoe] at this

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem affCoord_congr_sameOrbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

theorem OrbitChart.analyticAt_affCoord {P : Ideal (MRing ι)} {e : ℕ} (C : OrbitChart P e) {w : Fin e → ℂ}
    (hw : w ∈ C.D) (p : (k : K) → ι k) (hp : ∀ k, C.φ w ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun w' => affCoord p (C.φ w')) w := by
  rw [analyticAt_pi_iff]
  intro q
  exact (C.holo q w hw).div (C.holo ⟨q.1, p q.1⟩ w hw) (hp q.1)

end

theorem OrbitChart.analyticOnNhd_transition (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (C₁ C₂ : OrbitChart P e) :
    AnalyticOnNhd ℂ (fun w => C₂.ρ (C₁.φ w)) {w | w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O} := by
  rintro w₀ ⟨hw₀, hO₀⟩
  obtain ⟨O', hO'o, hO'⟩ := C₂.O_open
  have hcont : ContinuousAt C₁.φ w₀ := continuousAt_pi.2 fun q => (C₁.holo q w₀ hw₀).continuousAt
  have hS : ∀ᶠ w in 𝓝 w₀, w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O := by
    have h1 : ∀ᶠ w in 𝓝 w₀, w ∈ C₁.D := C₁.isOpen_D.mem_nhds hw₀
    have h2 : ∀ᶠ w in 𝓝 w₀, C₁.φ w ∈ O' :=
      hcont (hO'o.mem_nhds (by rw [hO'] at hO₀; exact hO₀.1))
    filter_upwards [h1, h2] with w a b
    exact ⟨a, by rw [hO']; exact ⟨b, C₁.mem w a⟩⟩
  have hTc : ContinuousAt (fun w => C₂.ρ (C₁.φ w)) w₀ := by
    have h1 : Tendsto C₁.φ (𝓝 w₀) (𝓝[C₂.O] (C₁.φ w₀)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcont, hS.mono fun _ h => h.2⟩
    exact (C₂.ρ_cont _ hO₀).tendsto.comp h1
  choose p hp using (C₁.mem w₀ hw₀).1
  have hu₀ : C₂.ρ (C₁.φ w₀) ∈ C₂.D := C₂.ρ_mem _ hO₀
  have horb := C₂.φ_ρ _ hO₀
  have hne : ∀ k, C₂.φ (C₂.ρ (C₁.φ w₀)) ⟨k, p k⟩ ≠ 0 := by
    obtain ⟨c, hc, hz⟩ := horb
    intro k
    rw [hz]
    exact mul_ne_zero (hc k) (hp k)
  have hA₂ := C₂.analyticAt_affCoord hu₀ p hne
  have hA₁ := C₁.analyticAt_affCoord hw₀ p hp
  obtain ⟨Λ, hΛ, hΛl⟩ := exists_analyticAt_leftInverse hA₂ (C₂.immersion _ hu₀ p hne)
  have hval : affCoord p (C₂.φ (C₂.ρ (C₁.φ w₀))) = affCoord p (C₁.φ w₀) := affCoord_congr_sameOrbit p horb
  have hΛ' : AnalyticAt ℂ Λ (affCoord p (C₁.φ w₀)) := by
    have := hΛ
    simp only [hval] at this
    exact this
  have hcomp : AnalyticAt ℂ (fun w => Λ (affCoord p (C₁.φ w))) w₀ :=
    AnalyticAt.comp (f := fun w => affCoord p (C₁.φ w)) (g := Λ) hΛ' hA₁
  refine hcomp.congr ?_
  filter_upwards [hS, hTc.eventually hΛl] with w hw hl
  rw [← hl, affCoord_congr_sameOrbit p (C₂.φ_ρ _ hw.2)]

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.OrthogonalFlagDegreeComparison
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.FlagPair

theorem iSup_part_degree_rank {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K}
    {Ψ : Type} [Fintype Ψ] {j k : ℕ} (A : FlagPair E Ψ j k) (h : A.IsOrthFull) :
    E.normDegree (⨆ a, A.part a) =
        ∑ τ, E.normDegree (A.W τ).top + ∑ τ, E.normDegree (A.S τ).top ∧
      E.rank (⨆ a, A.part a) = Module.finrank (𝓞 K) E.carrier := by
  unfold GlobalTheory.CompanionTheory.Ar.FlagPair.IsOrthFull at h
  obtain ⟨hort, hcard⟩ := h
  obtain ⟨hdeg, hrk⟩ := _root_.GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup K E (Ψ ⊕ Ψ) A.part hort
  refine ⟨?_, ?_⟩
  · rw [hdeg, Fintype.sum_sum_type]
    rfl
  · have hW : ∀ τ, E.rank (A.part (Sum.inl τ)) = j := fun τ => by
      show E.rank ((A.W τ).F (Fin.last j)) = j
      rw [(A.W τ).rank (Fin.last j), Fin.val_last]
    have hS : ∀ τ, E.rank (A.part (Sum.inr τ)) = k := fun τ => by
      show E.rank ((A.S τ).F (Fin.last k)) = k
      rw [(A.S τ).rank (Fin.last k), Fin.val_last]
    rw [hrk, Fintype.sum_sum_type, ← hcard]
    simp only [hW, hS, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring

theorem two_sum_neg_degree_W : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ j k), A.IsOrthFull →
    -E.normDegree ⊤ - ∑ τ, A.flatDeg τ ≤ 2 * ∑ τ, -E.normDegree (A.W τ).top ∧
      ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ ⨆ a, A.part a) →
        2 * ∑ τ, -E.normDegree (A.W τ).top ≤
          -E.normDegree ⊤ - ∑ τ, A.flatDeg τ +
            Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  intro K _ _ E Ψ _ j k A h
  obtain ⟨hdeg, hrk⟩ := iSup_part_degree_rank A h
  obtain ⟨hle, hge⟩ := _root_.GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds K E (⨆ a, A.part a) hrk
  have hflat : ∑ τ, A.flatDeg τ =
      ∑ τ, E.normDegree (A.W τ).top - ∑ τ, E.normDegree (A.S τ).top := by
    simp only [GlobalTheory.CompanionTheory.Ar.FlagPair.flatDeg, Finset.sum_sub_distrib]
  rw [hdeg] at hle
  refine ⟨?_, ?_⟩
  · rw [hflat, Finset.sum_neg_distrib]
    linarith
  · intro d hd hsub
    have hb := hge d hd hsub
    rw [hdeg] at hb
    rw [hflat, Finset.sum_neg_distrib]
    linarith

end GlobalTheory.CompanionTheory.Ar.FlagPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationBijectiveDegreeOne
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem realis_bijective_of_degree_one : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), Re.deg = 1 → Re.br = ∅ → Function.Bijective Re.π := by
  intro K _ ι _ D σ S P Re h1 h2
  have hd := Re.degree
  rw [h1, h2] at hd
  obtain ⟨g, hgl, hgr, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one S.A Re.R.A Re.π Re.holo hd
  exact Function.bijective_iff_has_inverse.2 ⟨g, hgl, hgr⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothMinorOfSmoothMatrix
section
noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.MinorSmooth

theorem contDiffOn_finsetProd {e : ℕ} {Un : Set (Fin e → ℂ)} {ι : Type} (s : Finset ι)
    (f : ι → (Fin e → ℂ) → ℂ)
    (h : ∀ i ∈ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ∏ i ∈ s, f i w) Un := by
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffOn_const : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Fin e → ℂ => (1 : ℂ)) Un)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem contDiffOn_det {e : ℕ} {Un : Set (Fin e → ℂ)} {σ : Type} [Fintype σ] [DecidableEq σ]
    (m : (Fin e → ℂ) → Matrix σ σ ℂ)
    (h : ∀ a b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => m w a b) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (m w).det) Un := by
  have hdet : (fun w => (m w).det) =
      fun w => ∑ τ : Equiv.Perm σ, ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ i, m w (τ i) i := by
    funext w
    exact Matrix.det_apply' _
  rw [hdet]
  exact ContDiffOn.sum fun τ _ => contDiffOn_const.mul
    (contDiffOn_finsetProd Finset.univ (fun i w => m w (τ i) i) fun i _ => h _ _)

theorem contDiffOn_minorIJ (N e : ℕ) (Un : Set (Fin e → ℂ))
    (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N))
    (h : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => A w r s) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => minorIJ (A w) I J) Un := by
  by_cases hc : I.card = J.card
  · have hm : (fun w => minorIJ (A w) I J) =
        fun w => ((A w).submatrix (I.orderEmbOfFin hc) (J.orderEmbOfFin rfl)).det := by
      funext w
      rw [minorIJ, dite_eq_left hc]
    rw [hm]
    exact contDiffOn_det _ fun a b => h _ _
  · have hm : (fun w => minorIJ (A w) I J) = fun _ => (0 : ℂ) := by
      funext w
      rw [minorIJ, dite_eq_right hc]
    rw [hm]
    exact contDiffOn_const

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.MinorSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnCompositionWithAnalyticMap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_comp_of_analytic_in_charts :
    ∀ (e n : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas n X) (Un : Set (Fin e → ℂ))
      (bp : (Fin e → ℂ) → X) (W : Set X) (f : X → ℝ), IsOpen Un → ContinuousOn bp Un →
      (∀ k, AnalyticOnNhd ℂ (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source)) →
      (∀ w ∈ Un, bp w ∈ W) → A.SmoothOn W f →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ bp) Un := by
  intro e n X _ A Un bp W f hUn hbp hana hW hf w hw
  obtain ⟨k, hk⟩ := A.cover (bp w)
  have hV : IsOpen (Un ∩ bp ⁻¹' (A.chart k).source) :=
    hbp.isOpen_inter_preimage hUn (A.chart k).open_source
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source) :=
    ((hana k).contDiffOn hV.uniqueDiffOn).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ (A.chart k).symm)
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W) := hf k
  have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((f ∘ (A.chart k).symm) ∘ (A.chart k ∘ bp))
      (Un ∩ bp ⁻¹' (A.chart k).source) := by
    refine h2.comp h1 ?_
    intro x hx
    refine ⟨(A.chart k).map_source hx.2, ?_⟩
    show (A.chart k).symm (A.chart k (bp x)) ∈ W
    rw [(A.chart k).left_inv hx.2]
    exact hW x hx.1
  have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source) := by
    refine h3.congr ?_
    intro x hx
    simp only [Function.comp_apply, (A.chart k).left_inv hx.2]
  exact (h4.contDiffAt (hV.mem_nhds ⟨hw, hk⟩)).contDiffWithinAt

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepFactorNeZero
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem minor_ne_zero_of_support {N : ℕ} {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) {I : Finset (Fin N)}
    (hs : ∀ k c, c ∈ I → k ∉ I → h k c = 0) : minorIJ h I I ≠ 0 := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (isUnit_iff_ne_zero.2 hd)
  have hH : (hᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * h).PosDef := by
    rw [Matrix.mul_one]
    exact Matrix.PosDef.conjTranspose_mul_self h (Matrix.mulVec_injective_of_isUnit hu)
  have hq := SchurCalc.minor_pos hH I
  rw [SchurCalc.minor_gram (G := 1) (fun k c hc hk => Matrix.one_apply_ne (fun e => hk (e ▸ hc))) hs] at hq
  intro e
  simp [e] at hq

theorem facOf_ne_zero (N j : ℕ) (a i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) (hh : IsBlockDiag j h)
    (hd : h.det ≠ 0) : facOf N j a h i ≠ 0 := by
  unfold facOf
  split_ifs
  · exact minor_ne_zero_of_support hd (MinorCalc.support_wIdx hh)
  · exact one_ne_zero
  · exact minor_ne_zero_of_support hd (MinorCalc.support_omIdx hh)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoByTwoMinorGramIdentity
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem xiCoef_self {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a i : Fin N) :
    xiCoef τ a (τ, i) = xiCoef () a ((), i) := by
  simp [xiCoef]

theorem xiCoef_ne {Ψ : Type} [DecidableEq Ψ] {N : ℕ} {τ τ' : Ψ} (h : τ' ≠ τ) (a i : Fin N) :
    xiCoef τ a (τ', i) = 0 := by
  simp [xiCoef, h]

theorem xi_sum_potentials : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (a b ca cb : Fin N) (Gf hf : Ψ → Matrix (Fin N) (Fin N) ℂ) (u : Ψ × Fin N → ℝ) (t : ℂ) (G₂ : Matrix (Fin 2) (Fin 2) ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (Gf τ) → (Gf τ).PosDef → IsBlockDiag j (hf τ) → (hf τ).det ≠ 0 → (∀ r s : Fin 2, G₂ r s = minorIJ ((hf τ)ᴴ * Gf τ * hf τ) (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) / minorIJ ((hf τ)ᴴ * Gf τ * hf τ) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) → ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) = xiPot G₂ t - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (hf τ) i‖) + u (τ, i)) := by
  intro Ψ _ _ N j τ a b ca cb Gf hf u t G₂ hj hb hcase hca hcb hG hGp hh hdet hG₂
  obtain ⟨G₃, -, e3, key⟩ := norm_three_steps N j a b ca cb (Gf τ) (hf τ) hj hb hcase hca hcb hG hGp hh hdet
  have hGG : G₃ = G₂ := Matrix.ext fun r s => (e3 r s).trans (hG₂ r s).symm
  subst hGG
  have hsum : ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) =
      ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (blockPot j i (Gf τ) (hf τ * (1 + Matrix.single cb ca t)) - u (τ, i)) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · simp
    · intro τ' _ hne
      simp [xiCoef_ne hne]
    · simp
  rw [hsum, ← key t, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [xiCoef_self]
  simp only [facOf]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

