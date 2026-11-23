module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CompactPartIntegralsTendsto
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyRegularizationBound
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem maMeasure_bdry_eq_zero {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hS : IsSection A L s) (hSNC : IsSNC A L s m W)
    (Φ : Fin e → LocPot X) : maMeasure A Φ (bdry s) = 0 := by
  have hB := LeviFormBoundaryTopology.isClosed_bdry hS
  have hAn : A.IsAnalyticSubset (bdry s) := by
    intro x
    refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩
  have hInt : interior (bdry s) = ∅ := LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC
  unfold maMeasure
  split_ifs with h
  · simp only [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hT := (A.chart j).open_target.measurableSet
    rw [Measure.map_apply_of_aemeasurable (((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac
      (withDensity_absolutelyContinuous _ _)) hB.measurableSet]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' hT]
    have := analyticNull A (bdry s) hAn hInt j
    rw [Set.inter_comm, (A.chart j).image_source_inter_eq'] at this
    rwa [Set.inter_comm]
  · simp

theorem tail_lintegral_le_of_eventually {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (hL : IsPotential A L) (hS : IsSection A L s) (Φ : Fin e → LocPot X)
    (ΦT : ℝ → Fin e → LocPot X)
    (hc : ∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ))
    (hpot : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (ΦT t i))
    (hunif : ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K →
      TendstoUniformlyOn (fun t => locDens A (ΦT t) j) (locDens A Φ j) (𝓝[>] 0) K)
    (g : X → ℝ) (hgm : Measurable g) (hgc : ContinuousOn g (bdry s)ᶜ)
    (R B : ℝ)
    (hg1 : ∀ y ∉ bdry s, R ≤ rW L s y → 0 ≤ g y)
    (hB : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (g y)
      ∂maMeasure A (ΦT t) ≤ ENNReal.ofReal B) :
    ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (g y) ∂maMeasure A Φ ≤
      ENNReal.ofReal B := by
  have hU : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl
  obtain ⟨hbm, hrm⟩ := TailBoundAlt.bdry_rW_meas A L s hL hS
  let Es : ℕ → Set X := fun N => ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) ∩ {y | rW L s y ≤ (N : ℝ)}
  have hun : (bdry s)ᶜ ∩ {y | R ≤ rW L s y} = ⋃ N, Es N := by
    ext y
    constructor
    · intro h
      obtain ⟨N, hN⟩ := exists_nat_ge (rW L s y)
      exact Set.mem_iUnion.2 ⟨N, h, hN⟩
    · intro h
      obtain ⟨N, hN⟩ := Set.mem_iUnion.1 h
      exact hN.1
  have hmono : Monotone Es := fun a b hab y hy =>
    ⟨hy.1, show rW L s y ≤ (b : ℝ) from
      le_trans (show rW L s y ≤ (a : ℝ) from hy.2) (Nat.cast_le.2 hab)⟩
  rw [hun, setLIntegral_iUnion_of_directed _ hmono.directed_le]
  refine iSup_le fun N => ?_
  have hEm : MeasurableSet (Es N) :=
    (hbm.compl.inter (measurableSet_le measurable_const hrm)).inter
      (measurableSet_le hrm measurable_const)
  have hKU : {y | y ∉ bdry s ∧ rW L s y ≤ (N : ℝ)} ⊆ (bdry s)ᶜ := fun y hy => hy.1
  have hEK : Es N ⊆ {y | y ∉ bdry s ∧ rW L s y ≤ (N : ℝ)} := fun y hy => ⟨hy.1.1, hy.2⟩
  obtain ⟨-, hint, hlim⟩ := compact_part_integrals_tendsto A (bdry s)ᶜ Φ ΦT hU hc hpot hunif g
    (fun _ => g) (fun _ => hgc)
    (fun u hu x _ => ⟨Set.univ, Filter.univ_mem,
      Eventually.of_forall fun t y _ => refl_mem_uniformity hu⟩)
    _ (Es N) (isCompact_rW_sublevel A L s hL hS (N : ℝ)) hKU hEm hEK
  have hnn : ∀ μ : Measure X, 0 ≤ᵐ[μ.restrict (Es N)] g := fun μ =>
    (ae_restrict_iff' hEm).2 (Eventually.of_forall fun y hy => hg1 y hy.1.1 hy.1.2)
  have hle : ∫ y in Es N, g y ∂maMeasure A Φ ≤ max B 0 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [hB] with t ht
    rw [integral_eq_lintegral_of_nonneg_ae (hnn _) hgm.aestronglyMeasurable,
      ← ENNReal.toReal_ofReal']
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((lintegral_mono_set (show Es N ⊆ (bdry s)ᶜ ∩ {y | R ≤ rW L s y} from
        fun _ hy => hy.1)).trans ht)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.mono_set hEK) (hnn _)]
  refine (ENNReal.ofReal_le_ofReal hle).trans (le_of_eq ?_)
  rcases le_total B 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

theorem limit_measure_tail : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) → IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) ∧ ∃ K : ℝ, ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  intro hTB e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR hC2
  obtain ⟨K, t₁, ht₁, -, hT⟩ :=
    tail_uniform hTB A Θ L s m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR
  have hB := LeviFormBoundaryTopology.isClosed_bdry hS
  obtain ⟨-, hrm⟩ := TailBoundAlt.bdry_rW_meas A L s hL hS
  have hrc := (rW_open A L s hL hS).1
  have hge := rW_ge L s hnorm
  have hc := locDens_add_ofFun_continuousOn A (bdry s)ᶜ th ph Θ hB.isOpen_compl
    (fun i => (hW i).1) hΘ (fun i => (hW i).2.1)
  have hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, A.Smooth (phT i t) := eventually_all.2 fun i => by
    filter_upwards [Ioc_mem_nhdsGT (hR i).1] with t ht
    exact ((hR i).2.2 t ht.1 ht.2).1
  have hunif := conv_dens A Θ s th ph phT hB hΘ (fun i => (hW i).1) (fun i => (hW i).2.1) hsm hC2
  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioc 0 t₁ := Ioc_mem_nhdsGT ht₁
  have hpot : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (th i + LocPot.ofFun (phT i t) + Θ) := by
    filter_upwards [hbd] with t ht
    exact fun i => ((hT (fun _ => t) fun _ => ht).1 i).1
  have tail1 : ∀ R : ℝ, Real.exp 1 ≤ R →
      maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) ≤
        ENNReal.ofReal (K * Real.log R / R) := by
    intro R hRe
    have h := tail_lintegral_le_of_eventually A L s hL hS
      (fun i => th i + LocPot.ofFun (ph i) + Θ) (fun t i => th i + LocPot.ofFun (phT i t) + Θ)
      hc hpot hunif (fun _ => 1) measurable_const continuousOn_const
      R (K * Real.log R / R)
      (fun _ _ _ => zero_le_one) (by
        filter_upwards [hbd] with t ht
        have h1 := ((hT (fun _ => t) fun _ => ht).2 R hRe).1
        simp only [ENNReal.ofReal_one, lintegral_const, one_mul, Measure.restrict_apply,
          MeasurableSet.univ, Set.univ_inter]
        exact (measure_mono (show (bdry s)ᶜ ∩ {y | R ≤ rW L s y} ⊆
          bdry s ∪ {y | R ≤ rW L s y} from fun _ hy => Or.inr hy.2)).trans h1)
    simpa using h
  have tail : ∀ R : ℝ, Real.exp 1 ≤ R →
      maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤
        ENNReal.ofReal (K * Real.log R / R) := by
    intro R hRe
    refine (measure_mono (t := bdry s ∪ ((bdry s)ᶜ ∩ {y | R ≤ rW L s y})) ?_).trans
      ((measure_union_le _ _).trans ?_)
    · rintro y (hy | hy)
      · exact Or.inl hy
      · by_cases hb : y ∈ bdry s
        · exact Or.inl hb
        · exact Or.inr ⟨hb, hy⟩
    · rw [maMeasure_bdry_eq_zero A L s m W hS hSNC, zero_add]
      exact tail1 R hRe
  refine ⟨⟨?_⟩, K, fun R hRe => ⟨tail R hRe, ?_⟩⟩
  · refine lt_of_le_of_lt ((measure_mono fun y _ => Or.inr (hge y)).trans (tail _ le_rfl))
      ENNReal.ofReal_lt_top
  · refine tail_lintegral_le_of_eventually A L s hL hS
      (fun i => th i + LocPot.ofFun (ph i) + Θ) (fun t i => th i + LocPot.ofFun (phT i t) + Θ)
      hc hpot hunif (fun y => Real.log (rW L s y)) hrm.log ?_
      R _ ?_ ?_
    · exact hrc.log fun y hy => ((Real.exp_pos 1).trans_le (hge y)).ne'
    · intro y _ _
      exact Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (hge y))
    · filter_upwards [hbd] with t ht
      exact ((hT (fun _ => t) fun _ => ht).2 R hRe).2

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PrimesBelowParams
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages GlobalTheory.CompanionTheory.Ar.Cmp

variable {m : ℕ}

theorem algebraMap_locRing_eq_zero_of_mem {I : Ideal (MvPolynomial (Fin m) ℂ)} (t : Fin m → ℂ)
    {h : MvPolynomial (Fin m) ℂ} (hh : h ∈ I) : algebraMap _ (locRing I t) h = 0 := by
  have halg : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) h =
      Ideal.Quotient.mk _ (algebraMap _ (locPt t) h) := rfl
  rw [halg, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hh

theorem map_ptIdeal_eq_maximalIdeal {I : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    (hI : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_algebraMap_locRing_iff I t hI]
    simpa using RingHom.mem_ker.mp hg
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have hbu := (isUnit_algebraMap_locRing_iff I t hI b).mpr hb
    have ha : a ∈ ptIdeal t := by
      refine RingHom.mem_ker.mpr ?_
      by_contra hne
      have hau := (isUnit_algebraMap_locRing_iff I t hI a).mpr hne
      rw [← hab] at hau
      exact ((IsLocalRing.mem_maximalIdeal _).mp hx) (isUnit_of_mul_isUnit_left hau)
    obtain ⟨v, hv⟩ := hbu.exists_right_inv
    have : x = algebraMap _ (locRing I t) a * v := by
      rw [← hab, mul_assoc, hv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

theorem chPrime_le_of_mem {I 𝔮 : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    {f : MvPolynomial (Fin m) ℂ} (h𝔮 : 𝔮.IsPrime) (hI𝔮 : I ≤ 𝔮) (h𝔮t : 𝔮 ≤ ptIdeal t)
    (hf : f ∈ 𝔮) : chPrime I t f ≤ 𝔮 := by
  intro g hg
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hg)
  obtain ⟨a₀, b₀, hb₀, hab⟩ := exists_mk_locRing I t a
  have hz : algebraMap _ (locRing I t) (b₀ * g - a₀ * f) = 0 := by
    rw [map_sub, map_mul, map_mul, ← ha, ← hab]
    ring
  obtain ⟨s, hs, hsI⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t hz
  have hmem : (s * b₀) * g ∈ 𝔮 := by
    have h1 := 𝔮.add_mem (hI𝔮 hsI) (𝔮.mul_mem_left (s * a₀) hf)
    have h2 : s * (b₀ * g - a₀ * f) + s * a₀ * f = (s * b₀) * g := by ring
    rwa [h2] at h1
  refine (h𝔮.mem_or_mem hmem).resolve_left fun hc => ?_
  have := RingHom.mem_ker.mp (h𝔮t hc)
  rw [map_mul] at this
  exact mul_ne_zero hs hb₀ this

theorem primes_below_params : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∀ i ∈ Jf, (SncRes.Par.chPrime I t (r i)).IsPrime ∧ I ≤ SncRes.Par.chPrime I t (r i) ∧ SncRes.Par.chPrime I t (r i) ≤ ptIdeal t ∧ Dc ≤ SncRes.Par.chPrime I t (r i) ∧ r i ∈ SncRes.Par.chPrime I t (r i) ∧ (∀ j ∈ Jf, j ≠ i → r j ∉ SncRes.Par.chPrime I t (r i)) ∧ ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → r i ∈ 𝔮 → SncRes.Par.chPrime I t (r i) ≤ 𝔮 := by
  intro m e I Dc t r Jf hIDc hI hreg hdim hspan hDc i hi
  haveI := hreg
  haveI : IsDomain (locRing I t) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hmax := map_ptIdeal_eq_maximalIdeal hI
  have hspan' : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      IsLocalRing.maximalIdeal (locRing I t) := hspan.trans hmax
  have hprime : ∀ l, Prime (algebraMap _ (locRing I t) (r l)) :=
    prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm
  have hnassoc := (regular_params_spec (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm).2
  have hIt : I ≤ ptIdeal t := fun h hh => RingHom.mem_ker.mpr (hI h hh)
  have hRi : r i ∈ chPrime I t (r i) := Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
  have hle : chPrime I t (r i) ≤ ptIdeal t := by
    intro g hg
    have hg' : algebraMap _ (locRing I t) g ∈ Ideal.span {algebraMap _ (locRing I t) (r i)} :=
      Ideal.mem_comap.mp hg
    have hsub : Ideal.span {algebraMap _ (locRing I t) (r i)} ≤ IsLocalRing.maximalIdeal (locRing I t) := by
      rw [Ideal.span_singleton_le_iff_mem, ← hspan']
      exact Ideal.subset_span ⟨i, rfl⟩
    have hnu := (IsLocalRing.mem_maximalIdeal _).mp (hsub hg')
    refine RingHom.mem_ker.mpr ?_
    by_contra hne
    exact hnu ((isUnit_algebraMap_locRing_iff I t hI g).mpr hne)
  have hpr : (chPrime I t (r i)).IsPrime := by
    haveI : (Ideal.span {algebraMap _ (locRing I t) (r i)}).IsPrime :=
      (Ideal.span_singleton_prime (hprime i).ne_zero).mpr (hprime i)
    exact Ideal.comap_isPrime _ _
  have hIle : I ≤ chPrime I t (r i) := by
    intro h hh
    refine Ideal.mem_comap.mpr ?_
    rw [algebraMap_locRing_eq_zero_of_mem t hh]
    exact Ideal.zero_mem _
  refine ⟨hpr, hIle, hle, (hDc _ hpr hIle hle).mpr ⟨i, hi, hRi⟩, hRi, ?_, ?_⟩
  · intro j _ hji hj
    have hd : algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) (r j) :=
      Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hj)
    exact hnassoc i j (Ne.symm hji) ((hprime i).associated_of_dvd (hprime j) hd)
  · intro 𝔮 h𝔮 hI𝔮 h𝔮t hr
    exact chPrime_le_of_mem h𝔮 hI𝔮 h𝔮t hr

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularSystemOfParametersLocalRing
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

variable {m : ℕ}

theorem algebraMap_locRing_eq_zero_of_mem (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    {a : MvPolynomial (Fin m) ℂ} (ha : a ∈ I) : algebraMap _ (locRing I t) a = 0 := by
  have halg : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a =
      Ideal.Quotient.mk _ (algebraMap _ (locPt t) a) := rfl
  rw [halg, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ ha

theorem map_ptIdeal_eq_maximalIdeal (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hp : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_algebraMap_locRing_iff I t hp, not_not]
    exact RingHom.mem_ker.mp ha
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have hbu := (isUnit_algebraMap_locRing_iff I t hp b).mpr hb
    have hxn : ¬ IsUnit x := hx
    have ha : eval t a = 0 := by
      by_contra hne
      have hau := (isUnit_algebraMap_locRing_iff I t hp a).mpr hne
      rw [← hab] at hau
      exact hxn (isUnit_of_mul_isUnit_left hau)
    obtain ⟨u, hu⟩ := hbu
    have hx' : x = algebraMap _ (locRing I t) a * ↑u⁻¹ := by
      rw [← hab, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [hx']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr ha))

theorem exists_den_of_mem_map (I D : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (hID : I ≤ D)
    (hp : ∀ h ∈ I, eval t h = 0) {f : MvPolynomial (Fin m) ℂ}
    (hf : algebraMap _ (locRing I t) f ∈ Ideal.map (algebraMap _ (locRing I t)) D) :
    ∃ s, eval t s ≠ 0 ∧ s * f ∈ D := by
  have key : ∀ x ∈ Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) D,
      ∃ a ∈ D, ∃ b, eval t b ≠ 0 ∧ x * algebraMap _ (locRing I t) b = algebraMap _ (locRing I t) a := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ∃ a ∈ D, ∃ b, eval t b ≠ 0 ∧
      x * algebraMap _ (locRing I t) b = algebraMap _ (locRing I t) a) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, ha, 1, by simp, by simp⟩
    · exact ⟨0, D.zero_mem, 1, by simp, by simp⟩
    · rintro x y _ _ ⟨a, ha, b, hb, hab⟩ ⟨c, hc, d, hd, hcd⟩
      refine ⟨a * d + c * b, D.add_mem (D.mul_mem_right _ ha) (D.mul_mem_right _ hc), b * d,
        by simpa using ⟨hb, hd⟩, ?_⟩
      simp only [map_add (f := _), map_mul, ← hab, ← hcd]
      ring
    · rintro c x _ ⟨a, ha, b, hb, hab⟩
      obtain ⟨u, v, hv, huv⟩ := exists_mk_locRing I t c
      refine ⟨u * a, D.mul_mem_left _ ha, v * b, by simpa using ⟨hv, hb⟩, ?_⟩
      simp only [smul_eq_mul, map_mul, ← hab, ← huv]
      ring
  obtain ⟨a, ha, b, hb, hab⟩ := key _ hf
  have h0 : algebraMap _ (locRing I t) (f * b - a) = 0 := by
    rw [map_sub, map_mul, hab, sub_self]
  obtain ⟨s, hs, hsm⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
  refine ⟨s * b, by simpa using ⟨hs, hb⟩, ?_⟩
  have : s * b * f = s * (f * b - a) + s * a := by ring
  rw [this]
  exact D.add_mem (hID hsm) (D.mul_mem_left _ ha)

theorem radical_span_prod_eq {O ι : Type*} [CommRing O] [IsDomain O] (R : ι → O) (J : Finset ι)
    (hpr : ∀ i, Prime (R i)) (hna : ∀ i j, i ≠ j → ¬ Associated (R i) (R j)) :
    (Ideal.span {∏ i ∈ J, R i}).radical = Ideal.span {∏ i ∈ J, R i} := by
  classical
  apply le_antisymm _ Ideal.le_radical
  rintro g ⟨n, hn⟩
  rw [Ideal.mem_span_singleton] at hn ⊢
  have hdiv : ∀ i ∈ J, R i ∣ g := fun i hi =>
    (hpr i).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem R hi).trans hn)
  clear hn
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    obtain ⟨c, rfl⟩ := ih fun i hi => hdiv i (Finset.mem_insert_of_mem hi)
    have hac := hdiv a (Finset.mem_insert_self _ _)
    rcases (hpr a).dvd_or_dvd hac with h | h
    · exfalso
      obtain ⟨j, hj, hd⟩ := (Prime.exists_mem_finset_dvd (hpr a) h)
      have hne : a ≠ j := fun e => ha (e ▸ hj)
      exact hna a j hne (((hpr a).dvd_prime_iff_associated (hpr j)).mp hd)
    · obtain ⟨d, rfl⟩ := h
      exact ⟨d, by ring⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

theorem exists_den_prod_params : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ h : MvPolynomial (Fin m) ℂ, eval t h ≠ 0 ∧ h * ∏ l ∈ Jf, r l ∈ Dc.radical ∧ ∀ g ∈ Dc.radical, h * g ∈ Ideal.span {∏ l ∈ Jf, r l} ⊔ I := by
  classical
  intro m e I Dc t r Jf hID hp hreg hdim hspan hprime
  haveI := hreg
  haveI : IsDomain (locRing I t) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  set alg : MvPolynomial (Fin m) ℂ →+* locRing I t := algebraMap _ (locRing I t) with halg
  set R : Fin e → locRing I t := fun l => alg (r l) with hR
  have hspan' : Ideal.span (Set.range R) = IsLocalRing.maximalIdeal (locRing I t) := by
    rw [← map_ptIdeal_eq_maximalIdeal I t hp]
    exact hspan
  have hpr : ∀ i, Prime (R i) := prime_of_regular_params R hspan' hdim.symm
  have hna := (regular_params_spec R hspan' hdim.symm).2
  set Q : MvPolynomial (Fin m) ℂ := ∏ l ∈ Jf, r l with hQ
  have hPQ : alg Q = ∏ l ∈ Jf, R l := map_prod alg _ _

  have hpr2 : ∀ 𝔓 : Ideal (locRing I t), 𝔓.IsPrime →
      (Ideal.map alg Dc ≤ 𝔓 ↔ alg Q ∈ 𝔓) := by
    intro 𝔓 h𝔓
    have hq1 : (Ideal.comap alg 𝔓).IsPrime := Ideal.comap_isPrime alg 𝔓
    have hq2 : I ≤ Ideal.comap alg 𝔓 := fun a ha => by
      rw [Ideal.mem_comap, halg, algebraMap_locRing_eq_zero_of_mem I t ha]
      exact 𝔓.zero_mem
    have hq3 : Ideal.comap alg 𝔓 ≤ ptIdeal t := fun a ha => by
      by_contra hne
      have hu := (isUnit_algebraMap_locRing_iff I t hp a).mpr fun h => hne (RingHom.mem_ker.mpr h)
      exact h𝔓.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    rw [Ideal.map_le_iff_le_comap, hprime _ hq1 hq2 hq3, hPQ, Ideal.IsPrime.prod_mem_iff]
    rfl
  have hrad : (Ideal.map alg Dc).radical = Ideal.span {alg Q} := by
    rw [hPQ, ← radical_span_prod_eq R Jf hpr hna, ← hPQ, Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
    congr 1
    ext 𝔓
    simp only [Set.mem_setOf_eq, Ideal.span_singleton_le_iff_mem]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(hpr2 𝔓 h2).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hpr2 𝔓 h2).mpr h1, h2⟩⟩

  obtain ⟨h', hh', hQrad⟩ : ∃ h', eval t h' ≠ 0 ∧ h' * Q ∈ Dc.radical := by
    have h1 : alg Q ∈ (Ideal.map alg Dc).radical := by
      rw [hrad]; exact Ideal.mem_span_singleton_self _
    obtain ⟨N, hN⟩ := h1
    rw [← map_pow] at hN
    obtain ⟨s, hs, hsm⟩ := exists_den_of_mem_map I Dc t hID hp hN
    refine ⟨s, hs, N + 1, ?_⟩
    have : (s * Q) ^ (N + 1) = s ^ N * Q * (s * Q ^ N) := by ring
    rw [this]
    exact Dc.mul_mem_left _ hsm

  have hone : ∀ g ∈ Dc.radical, ∃ hg, eval t hg ≠ 0 ∧ hg * g ∈ Ideal.span {Q} ⊔ I := by
    rintro g ⟨n, hn⟩
    have h1 : alg g ∈ (Ideal.map alg Dc).radical :=
      ⟨n, by rw [← map_pow]; exact Ideal.mem_map_of_mem _ hn⟩
    rw [hrad, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t c
    have h0 : algebraMap _ (locRing I t) (g * b - Q * a) = 0 := by
      change alg (g * b - Q * a) = 0
      have hab' : c * alg b = alg a := hab
      rw [map_sub, map_mul, map_mul, hc, ← hab']
      ring
    obtain ⟨s, hs, hsm⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
    refine ⟨s * b, by simpa using ⟨hs, hb⟩, ?_⟩
    have : s * b * g = s * (g * b - Q * a) + Q * (s * a) := by ring
    rw [this, add_comm]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right hsm)

  obtain ⟨S, hS⟩ : Dc.radical.FG := IsNoetherian.noetherian _
  have hSm : ∀ g, g ∈ S → ∃ hg, eval t hg ≠ 0 ∧ hg * g ∈ Ideal.span {Q} ⊔ I := fun g hg =>
    hone g (hS ▸ Submodule.subset_span hg)
  choose! f hf0 hf1 using hSm
  set H : MvPolynomial (Fin m) ℂ := ∏ g ∈ S, f g with hH
  have hH0 : eval t H ≠ 0 := by
    rw [hH, map_prod]
    exact Finset.prod_ne_zero_iff.mpr hf0
  have hHS : Dc.radical ≤
      Submodule.comap (LinearMap.mulLeft (MvPolynomial (Fin m) ℂ) H) (Ideal.span {Q} ⊔ I) := by
    rw [← hS]
    refine Submodule.span_le.mpr fun g hg => ?_
    obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem f hg
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    rw [hH, hw, mul_comm (f g) w, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hf1 g hg)
  refine ⟨h' * H, by simpa using ⟨hh', hH0⟩, ?_, fun g hg => ?_⟩
  · have : h' * H * Q = H * (h' * Q) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hQrad
  · have h1 := hHS hg
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at h1
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ h1

end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

end
end

