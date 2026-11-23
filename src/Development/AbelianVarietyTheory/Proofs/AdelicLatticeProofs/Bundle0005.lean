module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RayInvariantContinuousEqOne
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem exists_near_one_mod_ideal (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (hm : m ≠ ⊥) : ∃ C : ℝ, ∀ z : mixedSpace K, ∃ β : 𝓞 K, β - 1 ∈ m ∧
      ‖z - mixedEmbedding K β‖ ≤ C := by
  set N : ℕ := Ideal.absNorm m with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; exact fun h => hm (Ideal.absNorm_eq_zero_iff.mp h)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  refine ⟨(N : ℝ) * ∑ i, ‖latticeBasis K i‖, fun z => ?_⟩
  set w : mixedSpace K := (N : ℝ)⁻¹ • (z - 1) with hw
  have hmem := (ZSpan.floor (latticeBasis K) w).2
  obtain ⟨a, ha⟩ := (mem_span_latticeBasis K).mp hmem
  refine ⟨1 + (N : 𝓞 K) * a, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact m.mul_mem_right _ (Ideal.absNorm_mem m)
  · have ha' : mixedEmbedding K (a : K) = (ZSpan.floor (latticeBasis K) w : mixedSpace K) := ha
    have h1 : z - mixedEmbedding K ((1 + (N : 𝓞 K) * a : 𝓞 K) : K)
        = (N : ℝ) • ZSpan.fract (latticeBasis K) w := by
      rw [ZSpan.fract_apply, ← ha', smul_sub, hw, smul_inv_smul₀ hNR]
      simp only [map_add (f := _), map_one, map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      ring
    rw [h1, _root_.norm_smul, Real.norm_natCast]
    exact mul_le_mul_of_nonneg_left (ZSpan.norm_fract_le _ _) (Nat.cast_nonneg _)

theorem eq_one_of_homogeneous_of_eq_one_on_class :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (φ : mixedSpace K → ℂ), m ≠ ⊥ → ContinuousOn φ {x | mixedEmbedding.norm x ≠ 0} → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → φ (mixedEmbedding K β) = 1) → ∀ x, mixedEmbedding.norm x ≠ 0 → φ x = 1 := by
  intro K _ _ m φ hm hc hh h1 x hx
  obtain ⟨C, hC⟩ := exists_near_one_mod_ideal K m hm
  choose β hβm hβ using hC
  set y : ℕ → mixedSpace K := fun n =>
    ((n : ℝ) + 1)⁻¹ • mixedEmbedding K (β (((n : ℝ) + 1) • x)) with hy
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hlim : Filter.Tendsto y Filter.atTop (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * C) Filter.atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have : x - y n = ((n : ℝ) + 1)⁻¹ •
        (((n : ℝ) + 1) • x - mixedEmbedding K (β (((n : ℝ) + 1) • x))) := by
      rw [smul_sub, inv_smul_smul₀ (hpos n).ne']
    rw [norm_sub_rev, this, _root_.norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hpos n)).le, one_div]
    exact mul_le_mul_of_nonneg_left (hβ _) (inv_pos.mpr (hpos n)).le
  have hopen : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
  have hca : ContinuousAt φ x := hc.continuousAt (hopen.mem_nhds hx)
  have hev : ∀ᶠ n in Filter.atTop, φ (y n) = 1 := by
    filter_upwards [hlim.eventually (hopen.mem_nhds hx)] with n hn
    have hne : β (((n : ℝ) + 1) • x) ≠ 0 := by
      intro h0
      apply hn
      simp [hy, h0]
    simp only [hy]
    rw [hh _ _ (inv_pos.mpr (hpos n))]
    exact h1 _ hne (hβm _)
  have h2 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds (φ x)) := hca.tendsto.comp hlim
  have h3 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  exact tendsto_nhds_unique h2 h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SummableGaussianCoset
section
open scoped ContDiff

namespace GlobalTheory.GaussCoset

theorem exp_le_inv_pow {c : ℝ} (hc : 0 < c) (R : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-c * t ^ 2 + R * t) ≤
      ((n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c))) * t⁻¹ ^ n := by
  have hsq : 0 ≤ (2 * c * t - (R + 1)) ^ 2 / (4 * c) := by positivity
  have hid : (2 * c * t - (R + 1)) ^ 2 / (4 * c) =
      (R + 1) ^ 2 / (4 * c) - t - (-c * t ^ 2 + R * t) := by
    field_simp
    ring
  have h1 : Real.exp (-c * t ^ 2 + R * t) ≤
      Real.exp ((R + 1) ^ 2 / (4 * c)) * Real.exp (-t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-t) ≤ (n.factorial : ℝ) * t⁻¹ ^ n := by
    have hpos : 0 < t ^ n / (n.factorial : ℝ) := by positivity
    have hle : t ^ n / (n.factorial : ℝ) ≤ Real.exp t := Real.pow_div_factorial_le_exp t ht.le n
    rw [Real.exp_neg, inv_pow, ← div_eq_mul_inv, ← inv_div]
    exact inv_anti₀ hpos hle
  calc Real.exp (-c * t ^ 2 + R * t)
      ≤ Real.exp ((R + 1) ^ 2 / (4 * c)) * Real.exp (-t) := h1
    _ ≤ Real.exp ((R + 1) ^ 2 / (4 * c)) * ((n.factorial : ℝ) * t⁻¹ ^ n) := by gcongr
    _ = ((n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c))) * t⁻¹ ^ n := by ring

theorem summable_lattice {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] {c : ℝ} (hc : 0 < c)
    (R : ℝ) (x : V) :
    Summable fun z : L => Real.exp (-c * ‖(z : V) - x‖ ^ 2 + R * ‖(z : V) - x‖) := by
  have hmaj := (ZLattice.summable_norm_sub_inv_pow L (Module.finrank ℤ L + 1)
    (Nat.lt_succ_self _) x).mul_left
      (((Module.finrank ℤ L + 1).factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c)))
  refine Summable.of_norm_bounded_eventually hmaj ?_
  have hfin : {z : L | (z : V) = x}.Finite := by
    apply Set.Subsingleton.finite
    intro a ha b hb
    exact Subtype.ext (ha.trans hb.symm)
  filter_upwards [hfin.compl_mem_cofinite] with z hz
  have hne : (z : V) ≠ x := hz
  have hpos : 0 < ‖(z : V) - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_le_inv_pow hc R (Module.finrank ℤ L + 1) hpos

theorem discrete_of_finite {V : Type} [NormedAddCommGroup V] (L : AddSubgroup V)
    (h : {v : V | v ∈ L ∧ ‖v‖ ≤ 1}.Finite) : DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hU : IsOpen (Metric.ball (0 : V) 1 ∩ ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ) :=
    Metric.isOpen_ball.inter (h.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hset : ({0} : Set L) = Subtype.val ⁻¹' (Metric.ball (0 : V) 1 ∩
      ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ) := by
    ext z
    constructor
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simp
    · rintro ⟨h1, h2⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      have h1' : ‖(z : V)‖ < 1 := by simpa using h1
      apply h2
      refine ⟨⟨z.2, h1'.le⟩, ?_⟩
      intro hz0
      apply hne
      simpa using hz0
  rw [hset]
  exact hU.preimage continuous_subtype_val

theorem summable_gaussian_coset : ∀ (G V : Type) [AddCommGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (Γ U : AddSubgroup G), (∀ g ∈ Γ, p g = 0 → g = 0) → (∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U ∧ ‖p g‖ ≤ R}.Finite) → ∀ (c : ℝ), 0 < c → ∀ (R : ℝ) (w : G) (y : V), Summable fun g : Γ => Set.indicator (U : Set G) (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w) := by
  intro G V _ _ _ _ p Γ U hinj hfin c hc R w y
  by_cases hS : ∃ g₀ : Γ, (g₀ : G) + w ∈ U
  swap
  · simp only [not_exists] at hS
    have hzero : (fun g : Γ => Set.indicator (U : Set G)
        (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w)) = 0 := by
      funext g
      exact Set.indicator_of_notMem (hS g) _
    rw [hzero]
    exact summable_zero
  obtain ⟨g₀, hg₀⟩ := hS
  obtain ⟨L, hL⟩ : ∃ L : Submodule ℤ V, ∀ v, v ∈ L ↔ v ∈ (Γ ⊓ U).map p :=
    ⟨((Γ ⊓ U).map p).toIntSubmodule, fun _ => Iff.rfl⟩
  have hfin1 : {v : V | v ∈ L.toAddSubgroup ∧ ‖v‖ ≤ 1}.Finite := by
    refine ((hfin 1).image p).subset ?_
    rintro v ⟨hv, hv1⟩
    rw [Submodule.mem_toAddSubgroup, hL] at hv
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.mp hv
    obtain ⟨hgΓ, hgU⟩ := AddSubgroup.mem_inf.mp hg
    exact ⟨g, ⟨hgΓ, hgU, hv1⟩, rfl⟩
  have : DiscreteTopology L := discrete_of_finite L.toAddSubgroup hfin1
  let S := {g : Γ // (g : G) + w ∈ U}
  have hmem : ∀ s : S, p ((s.1 : G) - g₀) ∈ L := by
    intro s
    rw [hL]
    refine AddSubgroup.mem_map_of_mem p (AddSubgroup.mem_inf.mpr ⟨Γ.sub_mem s.1.2 g₀.2, ?_⟩)
    have hd := U.sub_mem s.2 hg₀
    rwa [add_sub_add_right_eq_sub] at hd
  let φ : S → L := fun s => ⟨p ((s.1 : G) - g₀), hmem s⟩
  have hφ : Function.Injective φ := by
    intro s t hst
    have h1 : p ((s.1 : G) - g₀) = p ((t.1 : G) - g₀) := congrArg Subtype.val hst
    have h2 : p ((s.1 : G) - t.1) = p ((s.1 : G) - g₀) - p ((t.1 : G) - g₀) := by
      rw [← map_sub]
      congr 1
      abel
    rw [h1, sub_self] at h2
    have h3 := hinj _ (Γ.sub_mem s.1.2 t.1.2) h2
    exact Subtype.ext (Subtype.ext (sub_eq_zero.mp h3))
  let F : Γ → ℝ := fun g => Set.indicator (U : Set G)
    (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w)
  show Summable F
  have hL' : Summable fun z : L =>
      Real.exp (-c * ‖(z : V) - -(p g₀ + y)‖ ^ 2 + R * ‖(z : V) - -(p g₀ + y)‖) :=
    summable_lattice L hc R _
  have hcomp : Summable (F ∘ (Subtype.val : S → Γ)) := by
    have heq : F ∘ (Subtype.val : S → Γ) = (fun z : L =>
        Real.exp (-c * ‖(z : V) - -(p g₀ + y)‖ ^ 2 + R * ‖(z : V) - -(p g₀ + y)‖)) ∘ φ := by
      funext s
      have hshift : ((φ s : L) : V) - -(p g₀ + y) = p (s.1 : G) + y := by
        show p ((s.1 : G) - g₀) - -(p g₀ + y) = p (s.1 : G) + y
        rw [map_sub]
        abel
      simp only [Function.comp_apply, F]
      rw [Set.indicator_of_mem (show (s.1 : G) + w ∈ (U : Set G) from s.2), hshift]
    rw [heq]
    exact hL'.comp_injective hφ
  refine (Function.Injective.summable_iff Subtype.val_injective ?_).mp hcomp
  intro g hg
  have hnot : (g : G) + w ∉ (U : Set G) := fun h => hg ⟨⟨g, h⟩, rfl⟩
  exact Set.indicator_of_notMem hnot _

end GlobalTheory.GaussCoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationAlgebraMapEqCount
section
open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

namespace GlobalTheory.AdicValuationCountFactors

variable {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem valuation_algebraMap_eq_count {r : R} (hr : r ≠ 0) :
    v.valuation K (algebraMap R K r) =
      WithZero.exp (-FractionalIdeal.count K v (spanSingleton R⁰ (algebraMap R K r))) := by
  have hJ : Ideal.span {r} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hr
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v hr,
    ← coeIdeal_span_singleton, count_coe K v hJ]

theorem valuation_eq_exp_neg_count {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v (spanSingleton R⁰ x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have haK : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ha0
  have hs : spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) =
      spanSingleton R⁰ (algebraMap R K a) * (spanSingleton R⁰ (algebraMap R K b))⁻¹ := by
    rw [div_eq_mul_inv, ← spanSingleton_mul_spanSingleton, spanSingleton_inv]
  rw [hs, count_mul K v (spanSingleton_ne_zero_iff.2 haK) (inv_ne_zero (spanSingleton_ne_zero_iff.2 hbK)),
    count_inv, map_div₀, valuation_algebraMap_eq_count (K := K) v ha0,
    valuation_algebraMap_eq_count (K := K) v hb0, ← WithZero.exp_sub]
  congr 1
  ring

end GlobalTheory.AdicValuationCountFactors
end

