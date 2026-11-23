module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPullbackCompatible
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem pb_indep_cover : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k', ι' k') → Ω) (S' : AnSys D σ) (Re' : Realis S' (mCoordIdeal y)) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')), IsBlockMap κ v → imageZ v (mCoordIdeal y) = P → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsPullHerm κ v (Re.line a t) (Re'.line a t)) → Re'.deg = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * Re.deg → Re'.PB II = Re.PB II := by
  intro II hII K _ ι _ D σ _ S P Re K' _ ι' _ Ω _ _ y S' Re' κ v hbl hP hpull hdeg
  have hr0 : IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 := by
    intro h
    have hd := Re'.deg_pos
    rw [hdeg, h, zero_mul] at hd
    exact lt_irrefl 0 hd
  have hr : ((IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hr0
  have harith : IsArithVar (imageZ v (mCoordIdeal y)) (D + 1) := by
    rw [hP]
    exact Re.arith
  have key : ∀ w : Fin (D + 1) → σ, Re'.limNum II w = Re.limNum II w := by
    intro w
    have ht0 : 0 < S.t₀ := (S.reg (w 0)).1
    have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ S.t₀ := by
      filter_upwards [Ioo_mem_nhdsGT ht0] with t ht using ht.2.le
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    have heq : (fun t => Re'.num II t w) =ᶠ[𝓝[>] (0 : ℝ)] (fun t => Re.num II t w) := by
      filter_upwards [hpull, hle, hpos] with t hpt hle' hpos'
      have hPF := hII.2.2.1 K ι K' ι' κ v Ω y (D + 1) (fun j => Re.line (w j) t)
        (fun j => Re'.line (w j) t) hbl Re'.arith harith
        (fun j => Re.line_smooth (w j) t hpos' hle') (fun j => hpt (w j))
      rw [hP] at hPF
      show (II K' ι' (mCoordIdeal y) (D + 1) fun j => Re'.line (w j) t) / (Re'.deg : ℝ)
        = (II K ι P (D + 1) fun j => Re.line (w j) t) / (Re.deg : ℝ)
      rw [hPF, hdeg]
      push_cast
      exact mul_div_mul_left _ _ hr
    unfold Realis.limNum Filter.limUnder
    rw [Filter.map_congr heq]
  unfold Realis.PB
  rw [show Re'.limNum II = Re.limNum II from funext key]

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TailLogBoundLocalIntegrable
section
open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.Metric.LocTail

theorem tailLog_on_compact_of_chart {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Yo : Set X) (r : X → ℝ) (Φ : Fin e → LocPot X) (CE : ℝ)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hr : ∀ x ∈ Yo, 1 ≤ r x)
    (hdens : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A Φ j y)
    (hT : GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A Yo r Φ CE)
    (j : Fin A.n) (S : Set (Fin e → ℂ)) (hSt : S ⊆ (A.chart j).target) (hSc : IsCompact S)
    (R₀ : ℝ) (hR₀ : Real.exp 1 ≤ R₀) :
    IntegrableOn (fun y => (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
      (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y) S ∧
    ∫ y in S, (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
      (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y ≤
      CE * Real.log R₀ ^ (e + 1) / R₀ := by
  classical
  obtain ⟨hI, hB⟩ := hT R₀ hR₀
  set h : X → ℝ := (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
    (fun x => Real.log (r x)) with hdef
  have hIS := hI j S hSt hSc
  refine ⟨hIS, ?_⟩
  have hh0 : ∀ x, 0 ≤ h x := by
    intro x
    refine Set.indicator_nonneg (fun x hx => ?_) x
    exact Real.log_nonneg (hr x hx.1)
  have hhYo : ∀ x, x ∉ Yo → h x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (by exact fun hm => hx hm.1) _
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  set ch := A.chart j with hch
  set Z : Set X := ch.symm '' S with hZ
  set g : X → ℝ := Z.indicator h with hgdef
  have hg0 : ∀ x, x ∉ ch.source → g x = 0 := by
    intro x hx
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨y, hy, rfl⟩
    exact hx (ch.map_target (hSt hy))
  set F : (Fin e → ℂ) → ℝ := fun y => h (ch.symm y) * locDens A Φ j y with hF
  have hgF : ∀ z ∈ ch.target, g (ch.symm z) * locDens A Φ j z = S.indicator F z := by
    intro z hz
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS, hgdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hzS)]
    · have hnZ : ch.symm z ∉ Z := by
        rintro ⟨y, hy, hyz⟩
        exact hzS ((ch.symm.injOn (by simpa using hSt hy) (by simpa using hz) hyz) ▸ hy)
      rw [Set.indicator_of_notMem hzS, hgdef, Set.indicator_of_notMem hnZ, zero_mul]
  have hFint : IntegrableOn (S.indicator F) ch.target :=
    ((integrable_indicator_iff hSm).2 hIS).integrableOn
  have hint : IntegrableOn (fun z => g (ch.symm z) * locDens A Φ j z) ch.target :=
    hFint.congr_fun (fun z hz => (hgF z hz).symm) ch.open_target.measurableSet
  have hne : Nonempty (ChartPartition A) := existsPartition A
  obtain ⟨hgt, hgI⟩ := integralWith_localize_support A hne.some Φ hΦ j g hg0 hint
  have hSint : ∫ z in ch.target, g (ch.symm z) * locDens A Φ j z = ∫ y in S, F y := by
    rw [setIntegral_congr_fun ch.open_target.measurableSet hgF,
      setIntegral_indicator hSm, Set.inter_eq_right.2 hSt]
  have hle : integralWith A hne.some Φ g ≤ integralWith A hne.some Φ h := by
    unfold integralWith
    refine Finset.sum_le_sum fun k _ => ?_
    refine setIntegral_mono_on (hgt k) (integrableOn_weight A hne.some Φ h hI k)
      (A.chart k).open_target.measurableSet fun y hy => ?_
    by_cases hx : (A.chart k).symm y ∈ Yo
    · have hd := hdens k y hy hx
      have hχ := hne.some.nonneg k ((A.chart k).symm y)
      have hgh : g ((A.chart k).symm y) ≤ h ((A.chart k).symm y) :=
        Set.indicator_le_self' (fun x _ => hh0 x) _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgh hχ) hd
    · have h1 : h ((A.chart k).symm y) = 0 := hhYo _ hx
      have h2 : g ((A.chart k).symm y) = 0 := by
        rw [hgdef]
        by_cases hz : (A.chart k).symm y ∈ Z
        · rw [Set.indicator_of_mem hz, h1]
        · rw [Set.indicator_of_notMem hz]
      rw [h1, h2]
  calc ∫ y in S, F y = integralWith A hne.some Φ g := by rw [hgI, hSint]
    _ ≤ integralWith A hne.some Φ h := hle
    _ = mInt A Φ h := by
      unfold mInt
      rw [dite_eq_left hne]
    _ ≤ _ := hB

end GlobalTheory.CompanionTheory.Metric.LocTail
end

