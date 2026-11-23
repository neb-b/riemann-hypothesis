module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
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
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataProperties
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.Regular (RegChartData)

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem isClosed_coordDiv (S : Finset (Fin e)) : IsClosed (coordDiv S) := by
  have h : coordDiv S = ⋃ i ∈ S, {z : Fin e → ℂ | z i = 0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact isClosed_biUnion_finset fun i _ => isClosed_eq (continuous_apply i) continuous_const

theorem volume_coordDiv_eq_zero (S : Finset (Fin e)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ (S : Set (Fin e)),
      ((LinearMap.ker (LinearMap.proj i : (Fin e → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin e → ℂ)) : Set (Fin e → ℂ)) := by
    ext z
    simp [coordDiv]
  rw [h, measure_biUnion_null_iff S.countable_toSet]
  intro i _
  apply Measure.addHaar_submodule
  intro htop
  have hmem : (Pi.single i (1 : ℂ) : Fin e → ℂ) ∈ LinearMap.ker (LinearMap.proj i : (Fin e → ℂ) →ₗ[ℝ] ℂ) := by
    rw [htop]
    exact Submodule.mem_top
  simp at hmem

theorem exists_mem_source (R : RegChartData A) (x : X) : ∃ j, x ∈ (R.chart j).source := by
  obtain ⟨j, hj⟩ := R.cover x
  exact ⟨j, R.closure_mid j (subset_closure (R.closure_inner j (subset_closure hj)))⟩

theorem isOpen_Yo (R : RegChartData A) : IsOpen R.Yo := by
  have h : R.Yo = ⋃ j, (R.chart j).source ∩ (R.chart j) ⁻¹' (coordDiv (R.S j))ᶜ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := exists_mem_source R x
      exact ⟨j, hj, (R.mem_Yo j x hj).1 hx⟩
    · rintro ⟨j, hj, hc⟩
      exact (R.mem_Yo j x hj).2 hc
  rw [h]
  exact isOpen_iUnion fun j => (R.chart j).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl

theorem volume_compl_Yo (R : RegChartData A) (j : Fin A.n) :
    volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ) = 0 := by
  have hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ ⊆
      ⋃ k, ((A.chart j) ∘ (R.chart k).symm) ''
        (((R.chart k).target ∩ (R.chart k).symm ⁻¹' (A.chart j).source) ∩ coordDiv (R.S k)) := by
    rintro y ⟨hyT, hyY⟩
    have hxs : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hyT
    obtain ⟨k, hk⟩ := exists_mem_source R ((A.chart j).symm y)
    have hxc : R.chart k ((A.chart j).symm y) ∈ coordDiv (R.S k) := by
      by_contra h
      exact hyY ((R.mem_Yo k _ hk).2 h)
    refine Set.mem_iUnion.mpr ⟨k, R.chart k ((A.chart j).symm y), ⟨⟨(R.chart k).map_source hk, ?_⟩, hxc⟩, ?_⟩
    · show (R.chart k).symm (R.chart k ((A.chart j).symm y)) ∈ (A.chart j).source
      rw [(R.chart k).left_inv hk]
      exact hxs
    · show (A.chart j) ((R.chart k).symm (R.chart k ((A.chart j).symm y))) = y
      rw [(R.chart k).left_inv hk, (A.chart j).right_inv hyT]
  refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
  apply MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
  · exact (((R.compat k j).2.differentiableOn).restrictScalars ℝ).mono Set.inter_subset_left
  · exact measure_mono_null Set.inter_subset_right (volume_coordDiv_eq_zero _)

theorem continuousOn_r (R : RegChartData A) : ContinuousOn R.r R.Yo := by
  intro x hx
  obtain ⟨k, hk⟩ := exists_mem_source R x
  have hxc : R.chart k x ∉ coordDiv (R.S k) := (R.mem_Yo k x hk).1 hx
  have hUo : IsOpen ((R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ) :=
    (R.chart k).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl
  have hxU : x ∈ (R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ := ⟨hk, hxc⟩
  have hg : ContinuousOn (fun y : Fin e → ℂ => Real.exp 1 + R.f k y + ∑ i ∈ R.S k, Real.log (‖y i‖ ^ 2)⁻¹)
      ((R.chart k).target \ coordDiv (R.S k)) := by
    refine ContinuousOn.add (continuousOn_const.add ((R.f_smooth k).continuousOn.mono Set.sdiff_subset)) ?_
    refine continuousOn_finsetSum _ fun i hi => ?_
    have hne : ∀ y ∈ (R.chart k).target \ coordDiv (R.S k), ‖y i‖ ^ 2 ≠ 0 := by
      intro y hy
      have hyi : y i ≠ 0 := fun h0 => hy.2 (show ∃ i' ∈ R.S k, y i' = 0 from ⟨i, hi, h0⟩)
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hyi)
    exact (((continuous_apply i).norm.pow 2).continuousOn.inv₀ hne).log fun y hy => inv_ne_zero (hne y hy)
  have heq : Set.EqOn R.r ((fun y : Fin e → ℂ => Real.exp 1 + R.f k y + ∑ i ∈ R.S k, Real.log (‖y i‖ ^ 2)⁻¹) ∘ R.chart k)
      ((R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ) := by
    intro z hz
    have h1 := R.r_chart k (R.chart k z) ⟨(R.chart k).map_source hz.1, hz.2⟩
    rw [(R.chart k).left_inv hz.1] at h1
    exact h1
  have hcont := hg.comp (s := (R.chart k).source ∩ (R.chart k) ⁻¹' (coordDiv (R.S k))ᶜ)
    ((R.chart k).continuousOn.mono Set.inter_subset_left)
    (fun _ hz => ⟨(R.chart k).map_source hz.1, hz.2⟩)
  exact ((hcont.congr heq).continuousAt (hUo.mem_nhds hxU)).continuousWithinAt

theorem eventually_not_le_of_not_mem_Yo (R : RegChartData A) {x : X} (hx : x ∉ R.Yo) (l : ℝ) :
    ∀ᶠ z in 𝓝 x, ¬ (z ∈ R.Yo ∧ R.r z ≤ l) := by
  obtain ⟨k, hk⟩ := exists_mem_source R x
  have hxc : R.chart k x ∈ coordDiv (R.S k) := by
    by_contra h
    exact hx ((R.mem_Yo k x hk).2 h)
  obtain ⟨i, hi, hi0⟩ : ∃ i ∈ R.S k, R.chart k x i = 0 := hxc
  obtain ⟨B, hB⟩ := R.f_bdd
  have hca : ContinuousAt (fun z => ‖R.chart k z i‖ ^ 2) x :=
    ((continuous_apply i).continuousAt.comp ((R.chart k).continuousAt hk)).norm.pow 2
  have h0 : ‖R.chart k x i‖ ^ 2 < Real.exp (-(l - Real.exp 1 + B)) := by
    rw [hi0, norm_zero]
    simp [Real.exp_pos]
  have h1 : ∀ᶠ z in 𝓝 x, ‖R.chart k z i‖ ^ 2 < Real.exp (-(l - Real.exp 1 + B)) :=
    Filter.Tendsto.eventually hca (gt_mem_nhds h0)
  have h2 : ∀ᶠ z in 𝓝 x, z ∈ (R.chart k).source := (R.chart k).open_source.mem_nhds hk
  filter_upwards [h1, h2] with z hz1 hz2
  rintro ⟨hzY, hzr⟩
  have hzc : R.chart k z ∉ coordDiv (R.S k) := (R.mem_Yo k z hz2).1 hzY
  have hyT : R.chart k z ∈ (R.chart k).target := (R.chart k).map_source hz2
  have hr := R.r_chart k (R.chart k z) ⟨hyT, hzc⟩
  rw [(R.chart k).left_inv hz2] at hr
  have hball : ‖R.chart k z‖ < 1 := by simpa using R.target_subset k hyT
  have hne : ∀ i' ∈ R.S k, R.chart k z i' ≠ 0 := fun i' hi' h0 =>
    hzc (show ∃ i'' ∈ R.S k, R.chart k z i'' = 0 from ⟨i', hi', h0⟩)
  have hterm : ∀ i' ∈ R.S k, 0 ≤ Real.log (‖R.chart k z i'‖ ^ 2)⁻¹ := by
    intro i' hi'
    apply Real.log_nonneg
    have hp : 0 < ‖R.chart k z i'‖ := norm_pos_iff.mpr (hne i' hi')
    have hlt : ‖R.chart k z i'‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm _ i') hball
    exact (one_le_inv₀ (by positivity)).mpr (by nlinarith)
  have hsum : Real.log (‖R.chart k z i‖ ^ 2)⁻¹ ≤ ∑ i' ∈ R.S k, Real.log (‖R.chart k z i'‖ ^ 2)⁻¹ :=
    Finset.single_le_sum hterm hi
  have hp : 0 < ‖R.chart k z i‖ ^ 2 := by
    have := norm_pos_iff.mpr (hne i hi)
    positivity
  have hlog : Real.log (‖R.chart k z i‖ ^ 2) < -(l - Real.exp 1 + B) := (Real.log_lt_iff_lt_exp hp).mpr hz1
  rw [Real.log_inv] at hsum
  have hf := (abs_le.mp (hB k _ hyT)).1
  linarith

theorem isCompact_sublevel [CompactSpace X] (R : RegChartData A) (l : ℝ) :
    IsCompact {x | x ∈ R.Yo ∧ R.r x ≤ l} := by
  refine IsClosed.isCompact (isOpen_compl_iff.mp (isOpen_iff_eventually.mpr fun x hx => ?_))
  by_cases hY : x ∈ R.Yo
  · have hlt : l < R.r x := not_le.mp fun h => hx ⟨hY, h⟩
    have hcont : ContinuousAt R.r x := (continuousOn_r R).continuousAt ((isOpen_Yo R).mem_nhds hY)
    filter_upwards [Filter.Tendsto.eventually hcont (lt_mem_nhds hlt)] with z hz
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_le]
    exact fun _ => hz
  · exact eventually_not_le_of_not_mem_Yo R hY l

theorem regData_open_part : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A),
    IsOpen R.Yo ∧ (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ) = 0) ∧
      ContinuousOn R.r R.Yo ∧ ∀ ℓ : ℝ, IsCompact {x | x ∈ R.Yo ∧ R.r x ≤ ℓ} := by
  intro e X _ _ _ A R
  exact ⟨isOpen_Yo R, volume_compl_Yo R, continuousOn_r R, isCompact_sublevel R⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RowProductFirstDerivative
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem prod_fin_ite_lt {R : Type*} [CommMonoid R] (a b : R) (m N : ℕ) (h : m ≤ N) :
    (∏ r : Fin N, (if (r : ℕ) < m then a else b)) = a ^ m * b ^ (N - m) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < m then a else b) (m + j),
    Finset.prod_range_add]
  have h1 : (∏ x ∈ Finset.range m, (if x < m then a else b)) = a ^ m := by
    rw [Finset.prod_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx))]
    simp
  have h2 : (∏ x ∈ Finset.range j, (if m + x < m then a else b)) = b ^ j := by
    rw [Finset.prod_congr rfl (fun x _ => if_neg (by omega))]
    simp
  rw [h1, h2, Nat.add_sub_cancel_left]

theorem rowW_ite (c : Prop) [Decidable c] :
    rowW ![if c then 1 else 0, 0] (if c then 0 else 1) =
      if c then (X (some 0) : MvPolynomial (Option (Fin 2)) ℝ) else X none := by
  split_ifs <;> simp [rowW]

theorem evalW_X_some_zero (n₀ n₁ : Fin 3 → ℝ) :
    evalW n₀ n₁ (X (some 0)) = rename some (lin3 n₀) := by
  simp [evalW, lin4]

theorem evalW_X_none (n₀ n₁ : Fin 3 → ℝ) :
    evalW n₀ n₁ (X none) = X none := by
  simp [evalW]

theorem evalW_pderiv_prod_rowW : ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ n : Fin 3 → ℝ,
    evalW n n (pderiv (some 0) (∏ r : Fin (d + 1),
      rowW ![if (r : ℕ) < 2 * k - 1 then 1 else 0, 0] (if (r : ℕ) < 2 * k - 1 then 0 else 1))) =
    C (2 * (k : ℝ) - 1) * rename some (lin3 n ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k) := by
  intro d k hk hkd n
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have hm : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  have hm2 : 2 * (t + 1) - 2 = 2 * t := by omega
  have hj : d + 2 - 2 * (t + 1) = d + 1 - (2 * t + 1) := by omega
  have hprod : (∏ r : Fin (d + 1),
      rowW ![if (r : ℕ) < 2 * (t + 1) - 1 then 1 else 0, 0]
        (if (r : ℕ) < 2 * (t + 1) - 1 then 0 else 1)) =
      X (some 0) ^ (2 * t + 1) * X none ^ (d + 1 - (2 * t + 1)) := by
    simp only [rowW_ite, hm]
    exact prod_fin_ite_lt _ _ _ _ (by omega)
  rw [hprod, hm2, hj, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow]
  have hne : (none : Option (Fin 2)) ≠ some 0 := by simp
  simp only [pderiv_X_self, pderiv_X_of_ne hne, smul_eq_mul, smul_zero, zero_add, mul_zero,
    add_zero, mul_one, Nat.add_sub_cancel, nsmul_eq_mul]
  simp only [map_mul, map_pow, map_natCast, evalW_X_some_zero, evalW_X_none]
  have hc : (C (2 * ((t + 1 : ℕ) : ℝ) - 1) : MvPolynomial (Option (Fin 3)) ℝ) =
      ((2 * t + 1 : ℕ) : MvPolynomial (Option (Fin 3)) ℝ) := by
    rw [← map_natCast (C : ℝ →+* MvPolynomial (Option (Fin 3)) ℝ)]
    congr 1
    push_cast
    ring
  rw [hc]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SamePotBlock
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA

namespace BlockPot

theorem continuousAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X}
    {g : X → ℂ} (hg : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have an := hg j (A.chart j x) ⟨(A.chart j).map_source hj, by
    simpa only [Set.mem_preimage, (A.chart j).left_inv hj] using hx⟩
  have c : ContinuousAt (fun y => (g ∘ (A.chart j).symm) (A.chart j y)) x :=
    ContinuousAt.comp (f := A.chart j) an.continuousAt ((A.chart j).continuousAt hj)
  refine c.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp only [Function.comp_apply, (A.chart j).left_inv hy]

theorem holoOn_comp {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {S : Set X}
    {g : X → ℂ} (hg : A.HoloOn S g) : B.HoloOn (h ⁻¹' S) (fun y => g (h y)) := by
  intro j u hu
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm u))
  have hτ : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) u := hh.2 j k u ⟨hu.1, hk⟩
  have hgu : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart j).symm) u) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      simpa only [Function.comp_apply, Set.mem_preimage, (A.chart k).left_inv hk] using hu.2⟩
  refine (hgu.comp hτ).congr ?_
  filter_upwards [((B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hh.1)).mem_nhds
    ⟨hu.1, hk⟩] with y' hy'
  simp only [Function.comp_apply, (A.chart k).left_inv hy'.2]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K' → K} {v : (Σ k, ι' k) → Σ k, ι k}

theorem sum_block (hb : IsBlockMap κ v) (z : (Σ k, ι k) → ℂ) (k : K') :
    ∑ i, ‖z ⟨κ k, i⟩‖ ^ 2 = ∑ m, ‖z (v ⟨k, m⟩)‖ ^ 2 := by
  obtain ⟨hκ, hv, h1, h2⟩ := hb
  have hS : (Finset.univ.image fun i : ι (κ k) => (⟨κ k, i⟩ : Σ k, ι k)) =
      Finset.univ.image fun m : ι' k => v ⟨k, m⟩ := by
    ext q
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨⟨k', m⟩, hp⟩ := h2 ⟨κ k, i⟩ ⟨k, rfl⟩
      have hk : k' = k := hκ (by simpa [hp] using (h1 ⟨k', m⟩).symm)
      subst hk
      exact ⟨m, hp⟩
    · rintro ⟨m, rfl⟩
      rcases hq : v ⟨k, m⟩ with ⟨a, b⟩
      have : a = κ k := by simpa [hq] using h1 ⟨k, m⟩
      subst this
      exact ⟨b, rfl⟩
  have e1 := Finset.sum_image (s := Finset.univ) (g := fun i : ι (κ k) => (⟨κ k, i⟩ : Σ k, ι k))
    (f := fun q => ‖z q‖ ^ 2) (fun a _ b _ hab => by simpa using hab)
  have e2 := Finset.sum_image (s := Finset.univ) (g := fun m : ι' k => v ⟨k, m⟩)
    (f := fun q => ‖z q‖ ^ 2) (fun a _ b _ hab => by simpa using hv hab)
  rw [← e1, hS, e2]

theorem refNorm_block (hb : IsBlockMap κ v) {a : K → ℤ} (ha : ∀ k, k ∉ Set.range κ → a k = 0)
    (z : (Σ k, ι k) → ℂ) : refNorm a z = refNorm (fun k => a (κ k)) (z ∘ v) := by
  unfold refNorm
  symm
  refine Fintype.prod_of_injective κ hb.1 _ _ (fun k hk => ?_) (fun k => ?_)
  · simp [ha k hk]
  · simp only [Function.comp_apply]
    rw [sum_block hb z k]

theorem orbit_near {P J : Ideal (MRing ι)} {P' J' : Ideal (MRing ι')} {e e' : ℕ} (R : AnLogRes P J e)
    (R' : AnLogRes P' J' e') (h : R.X → R'.X) (hb : IsBlockMap κ v)
    (hO : ∀ x, SameOrbit (R'.lift (h x) (h x)) (R.lift x x ∘ v)) {x y : R.X} (hy : y ∈ R.U x)
    (hy' : h y ∈ R'.U (h x)) :
    ∃ c : K' → ℂ, (∀ k, c k ≠ 0) ∧ ∀ p, R'.lift (h x) (h y) p = c p.1 * R.lift x y (v p) := by
  obtain ⟨c₁, hc₁, e₁⟩ := R'.compat (h x) (h y) (h y) ⟨hy', R'.mem_U _⟩
  obtain ⟨c₂, hc₂, e₂⟩ := hO y
  obtain ⟨c₃, hc₃, e₃⟩ := R.compat x y y ⟨hy, R.mem_U _⟩
  refine ⟨fun k => c₁ k * c₂ k * (c₃ (κ k))⁻¹, fun k => mul_ne_zero (mul_ne_zero (hc₁ k) (hc₂ k))
    (inv_ne_zero (hc₃ _)), fun p => ?_⟩
  have f₁ := congrFun e₁ p
  have f₂ := congrFun e₂ p
  have f₃ := congrFun e₃ (v p)
  have f₃' : R.lift x y (v p) = c₃ (κ p.1) * R.lift y y (v p) := by
    rw [← hb.2.2.1 p]
    exact f₃
  have hc : c₃ (κ p.1) ≠ 0 := hc₃ _
  simp only [Function.comp_apply] at f₂
  rw [f₁, f₂, f₃']
  field_simp

theorem samePot_block (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K']
    (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K' → K) (v : (Σ k, ι' k) → Σ k, ι k) (P J : Ideal (MRing ι))
    (P' J' : Ideal (MRing ι')) (e e' : ℕ) (R : AnLogRes P J e) (R' : AnLogRes P' J' e') (h : R.X → R'.X)
    (hh : HoloMap R.A R'.A h) (a : K → ℤ) (hb : IsBlockMap κ v) (ha : ∀ k, k ∉ Set.range κ → a k = 0)
    (hO : ∀ x, SameOrbit (R'.lift (h x) (h x)) (R.lift x x ∘ v)) :
    SamePot R.A Set.univ (potOf R (fsHerm ι a)) ((potOf R' (fsHerm ι' fun k => a (κ k))).pullback h hh.1) := by
  intro x _
  have hxU : x ∈ R.U x := R.mem_U x
  have hxU' : h x ∈ R'.U (h x) := R'.mem_U _

  obtain ⟨cx, hcx, ex⟩ := orbit_near R R' h hb hO hxU hxU'
  have hm : ∀ k : K', ∃ m : ι' k, R.lift x x (v ⟨k, m⟩) ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := (R.mem x x hxU).1 (κ k)
    obtain ⟨⟨k', m⟩, hp⟩ := hb.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    have hk : k' = k := hb.1 (by simpa [hp] using (hb.2.2.1 ⟨k', m⟩).symm)
    subst hk
    exact ⟨m, by rw [hp]; exact hi⟩
  choose m hm using hm

  let den : K' → R.X → ℂ := fun k y => R.lift x y (v ⟨k, m k⟩)
  let num : K' → R.X → ℂ := fun k y => R'.lift (h x) (h y) ⟨k, m k⟩
  let rat : K' → R.X → ℂ := fun k y => num k y / den k y / cx k
  have hdenH : ∀ k, R.A.HoloOn (R.U x) (den k) := fun k => R.holo x _
  have hnumH : ∀ k, R.A.HoloOn (h ⁻¹' R'.U (h x)) (num k) := fun k =>
    holoOn_comp hh (R'.holo (h x) ⟨k, m k⟩)
  have hdenC : ∀ k, ContinuousAt (den k) x := fun k => continuousAt_of_holoOn (hdenH k) hxU
  have hnumC : ∀ k, ContinuousAt (num k) x := fun k => continuousAt_of_holoOn (hnumH k) hxU'
  have hratC : ∀ k, ContinuousAt (rat k) x := fun k =>
    ((hnumC k).div (hdenC k) (hm k)).div continuousAt_const (hcx k)
  have hrat1 : ∀ k, rat k x = 1 := by
    intro k
    have := ex ⟨k, m k⟩
    have h1 : den k x ≠ 0 := hm k
    have h2 := hcx k
    simp only [rat, num, den] at h1 ⊢
    rw [this]
    field_simp
  have hev : ∀ᶠ y in 𝓝 x, y ∈ R.U x ∧ h y ∈ R'.U (h x) ∧ ∀ k, den k y ≠ 0 ∧ rat k y ∈ Complex.slitPlane := by
    have e1 : ∀ᶠ y in 𝓝 x, y ∈ R.U x := (R.isOpen_U x).mem_nhds hxU
    have e2 : ∀ᶠ y in 𝓝 x, h y ∈ R'.U (h x) := ((R'.isOpen_U (h x)).preimage hh.1).mem_nhds hxU'
    have e3 : ∀ᶠ y in 𝓝 x, ∀ k, den k y ≠ 0 ∧ rat k y ∈ Complex.slitPlane := by
      refine eventually_all.2 fun k => ((hdenC k).eventually_ne (hm k)).and ?_
      exact (hratC k).eventually_mem (Complex.isOpen_slitPlane.mem_nhds (by
        simpa only [hrat1 k] using Complex.one_mem_slitPlane))
    exact e1.and (e2.and e3)
  obtain ⟨V, hVs, hVo, hxV⟩ := mem_nhds_iff.1 hev
  refine ⟨V, hVo, hxV, fun y => -∑ k, (a (κ k) : ℂ) * (Complex.log (rat k y) + (Real.log ‖cx k‖ : ℂ)), ?_, ?_⟩
  · intro j u hu
    obtain ⟨hy1, hy2, hy3⟩ := hVs hu.2
    have hd : ∀ k, AnalyticAt ℂ (fun u => den k ((R.A.chart j).symm u)) u := fun k =>
      hdenH k j u ⟨hu.1, hy1⟩
    have hn : ∀ k, AnalyticAt ℂ (fun u => num k ((R.A.chart j).symm u)) u := fun k =>
      hnumH k j u ⟨hu.1, hy2⟩
    have hr : ∀ k, AnalyticAt ℂ (fun u => rat k ((R.A.chart j).symm u)) u := fun k =>
      ((hn k).div (hd k) (hy3 k).1).div analyticAt_const (hcx k)
    have hl : ∀ k, AnalyticAt ℂ (fun u => (a (κ k) : ℂ) * (Complex.log (rat k ((R.A.chart j).symm u)) +
        (Real.log ‖cx k‖ : ℂ))) u := fun k =>
      analyticAt_const.mul (((hr k).clog (hy3 k).2).add analyticAt_const)
    exact (Finset.analyticAt_fun_sum Finset.univ fun k _ => hl k).neg
  · intro y hy
    obtain ⟨hy1, hy2, hy3⟩ := hVs hy
    obtain ⟨c, hc, ec⟩ := orbit_near R R' h hb hO hy1 hy2
    have hw : R'.lift (h x) (h y) = torusSmul c (R.lift x y ∘ v) := by
      funext p
      simpa [torusSmul] using ec p
    have hrat : ∀ k, rat k y = c k / cx k := by
      intro k
      have h1 : den k y ≠ 0 := (hy3 k).1
      have h2 := ec ⟨k, m k⟩
      simp only [rat, num, den] at h1 ⊢
      rw [h2]
      field_simp
    have hpos : 0 < refNorm a (R.lift x y) := refNorm_pos a (R.mem x y hy1).1
    have hprod : (∏ k, ‖c k‖ ^ a (κ k)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have hL : Real.log (refNorm (fun k => a (κ k)) (R'.lift (h x) (h y))) =
        (∑ k, (a (κ k) : ℝ) * Real.log ‖c k‖) + Real.log (refNorm a (R.lift x y)) := by
      rw [hw, refNorm_smul, ← refNorm_block hb ha, Real.log_mul hprod hpos.ne', Real.log_prod]
      · simp only [Real.log_zpow]
      · exact fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have hG : (-∑ k, (a (κ k) : ℂ) * (Complex.log (rat k y) + (Real.log ‖cx k‖ : ℂ))).re =
        -∑ k, (a (κ k) : ℝ) * Real.log ‖c k‖ := by
      rw [Complex.neg_re, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have hck := norm_ne_zero_iff.2 (hc k)
      have hcxk := norm_ne_zero_iff.2 (hcx k)
      have hcast : ((a (κ k) : ℤ) : ℂ) = (((a (κ k) : ℤ) : ℝ) : ℂ) := by push_cast; rfl
      rw [hrat k, hcast, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
        Real.log_div hck hcxk]
      ring
    show Real.log (refNorm a (R.lift x y)) - Real.log (refNorm (fun k => a (κ k)) (R'.lift (h x) (h y))) = _
    rw [hL, hG]
    ring

end BlockPot

end GlobalTheory.CompanionTheory.Ar.PB.FA
end
end

