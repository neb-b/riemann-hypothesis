module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EntireAntilinearLatticePeriodsConst
section
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

theorem eq_zero_of_norm_real_mul_le {c : ℂ} {C : ℝ} (h : ∀ r : ℝ, ‖(r : ℂ) * c‖ ≤ C) : c = 0 := by
  by_contra hc
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h0 : 0 ≤ C := (norm_nonneg _).trans (h 0)
  have key := h ((C + 1) / ‖c‖)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) hpos.le), div_mul_cancel₀ _ hpos.ne'] at key
  linarith

theorem entire_sub_conj_bounded_const {φ : ℂ → ℂ} {b : ℂ} {C : ℝ} (hφ : Differentiable ℂ φ)
    (h : ∀ s, ‖φ s - (starRingEnd ℂ) s * b‖ ≤ C) : b = 0 ∧ ∀ s, φ s = φ 0 := by

  have hshift : ∀ a s, φ (s + a) - φ s = φ a - φ 0 := by
    intro a
    have hd : Differentiable ℂ (fun s => φ (s + a) - φ s) :=
      (hφ.comp (differentiable_id.add_const a)).sub hφ
    have hbd : Bornology.IsBounded (Set.range (fun s => φ (s + a) - φ s)) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨2 * C + ‖(starRingEnd ℂ) a * b‖, ?_⟩
      rintro _ ⟨s, rfl⟩
      show ‖φ (s + a) - φ s‖ ≤ _
      have e : φ (s + a) - φ s = ((φ (s + a) - (starRingEnd ℂ) (s + a) * b)
          - (φ s - (starRingEnd ℂ) s * b)) + (starRingEnd ℂ) a * b := by
        rw [map_add (f := _)]; ring
      rw [e]
      calc _ ≤ ‖(φ (s + a) - (starRingEnd ℂ) (s + a) * b) - (φ s - (starRingEnd ℂ) s * b)‖
            + ‖(starRingEnd ℂ) a * b‖ := norm_add_le _ _
        _ ≤ (‖φ (s + a) - (starRingEnd ℂ) (s + a) * b‖ + ‖φ s - (starRingEnd ℂ) s * b‖)
            + ‖(starRingEnd ℂ) a * b‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by linarith [h (s + a), h s]
    intro s
    simpa [zero_add] using hd.apply_eq_apply_of_bounded hbd s 0

  have hderiv : ∀ s, deriv φ s = deriv φ 0 := by
    intro s
    have e1 : (fun x => φ (x + s)) = fun x => φ x + (φ s - φ 0) := by
      funext x
      linear_combination hshift s x
    have e2 := congrArg (fun f => deriv f 0) e1
    simp only [deriv_comp_add_const, deriv_add_const, zero_add] at e2
    exact e2

  obtain ⟨β, hlin⟩ : ∃ β : ℂ, ∀ s, φ s = φ 0 + β * s := by
    refine ⟨deriv φ 0, fun s => ?_⟩
    have hd : Differentiable ℂ (fun s => φ s - deriv φ 0 * s) :=
      hφ.sub (differentiable_id.const_mul _)
    have hz : ∀ x, deriv (fun s => φ s - deriv φ 0 * s) x = 0 := by
      intro x
      have hx : HasDerivAt (fun s => φ s - deriv φ 0 * s) (deriv φ x - deriv φ 0 * 1) x :=
        (hφ x).hasDerivAt.sub ((hasDerivAt_id' x).const_mul _)
      rw [hx.deriv, hderiv x]
      ring
    have := is_const_of_deriv_eq_zero hd hz s 0
    linear_combination this

  have hB : ∀ s, ‖β * s - (starRingEnd ℂ) s * b‖ ≤ C + ‖φ 0‖ := by
    intro s
    have e : β * s - (starRingEnd ℂ) s * b = (φ s - (starRingEnd ℂ) s * b) - φ 0 := by
      rw [hlin s]; ring
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith [h s])
  have h1 : β - b = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB r
    rw [Complex.conj_ofReal] at hr
    calc ‖(r : ℂ) * (β - b)‖ = ‖β * (r : ℂ) - (r : ℂ) * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h2 : Complex.I * (β + b) = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB (r * Complex.I)
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I] at hr
    calc ‖(r : ℂ) * (Complex.I * (β + b))‖
        = ‖β * ((r : ℂ) * Complex.I) - (r : ℂ) * -Complex.I * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h3 : β + b = 0 := (mul_eq_zero.mp h2).resolve_left Complex.I_ne_zero
  have hβ : β = 0 := by linear_combination (h1 + h3) / 2
  refine ⟨by linear_combination (h3 - h1) / 2, fun s => ?_⟩
  rw [hlin s, hβ, zero_mul, add_zero]

theorem entire_antilinear_periods_const :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v →
        (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) →
        t = 0 ∧ ∀ z, v z = v 0 := by
  intro g Λ hdisc hspan v t hv hper
  have : IsZLattice ℝ Λ := ⟨hspan⟩

  have hcont : Continuous (fun z => v z - t ⬝ᵥ star z) :=
    hv.continuous.sub (continuous_const.dotProduct continuous_star)
  have hperw : ∀ z w, w ∈ Λ → (fun z => v z - t ⬝ᵥ star z) (z + w) = (fun z => v z - t ⬝ᵥ star z) z := by
    intro z w hw
    simp only
    rw [hper ⟨w, hw⟩ z, star_add, dotProduct_add]
    ring
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (IsZLattice.isCompact_range_of_periodic Λ _ hcont hperw).isBounded

  have hline : ∀ d : Fin g → ℂ, t ⬝ᵥ star d = 0 ∧ ∀ s : ℂ, v (s • d) = v 0 := by
    intro d
    have hd : Differentiable ℂ (fun s : ℂ => v (s • d)) :=
      hv.comp (differentiable_id.smul_const d)
    have hb : ∀ s : ℂ, ‖v (s • d) - (starRingEnd ℂ) s * (t ⬝ᵥ star d)‖ ≤ M := by
      intro s
      have e : (starRingEnd ℂ) s * (t ⬝ᵥ star d) = t ⬝ᵥ star (s • d) := by
        rw [star_smul, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
      rw [e]
      exact hM _ ⟨s • d, rfl⟩
    obtain ⟨h1, h2⟩ := entire_sub_conj_bounded_const hd hb
    exact ⟨h1, fun s => by simpa using h2 s⟩
  refine ⟨?_, fun z => by simpa using (hline z).2 1⟩
  funext i
  have hi := (hline (Pi.single i 1)).1
  rw [← Pi.single_star, star_one, dotProduct_single, mul_one] at hi
  simpa using hi

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsClopenEqualizer
section
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.ClopenEqualizer

theorem exists_isClopen_equalizer {P C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (a b : P ⟶ C)
    (h : a ≫ c = b ≫ c) :
    ∃ (U : Set P), IsClopen U ∧ ∀ (T : Scheme.{0}) (y : T ⟶ P), y ≫ a = y ≫ b ↔ Set.range y ⊆ U := by
  let d := pullback.diagonal c
  let l : P ⟶ pullback c c := pullback.lift a b h
  haveI : IsOpenImmersion d := inferInstance
  haveI : IsClosedImmersion d := inferInstance
  let j : pullback l d ⟶ P := pullback.fst l d
  have hj : j ≫ a = j ≫ b := by
    have h0 : j ≫ l = pullback.snd l d ≫ d := pullback.condition
    have h1 := congrArg (· ≫ pullback.fst c c) h0
    have h2 := congrArg (· ≫ pullback.snd c c) h0
    simp [l, d, pullback.lift_fst, pullback.lift_snd] at h1 h2
    rw [h1, h2]
  refine ⟨Set.range j, ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩, ?_⟩
  intro T y
  constructor
  · intro hy
    have e : y ≫ l = (y ≫ a) ≫ d := by
      apply pullback.hom_ext
      · simp [l, d, pullback.lift_fst]
      · simp [l, d, hy, pullback.lift_snd]
    have e2 : pullback.lift y (y ≫ a) e ≫ j = y := pullback.lift_fst _ _ _
    rintro _ ⟨t, rfl⟩
    refine ⟨pullback.lift y (y ≫ a) e t, ?_⟩
    rw [← Scheme.Hom.comp_apply, e2]
  · intro hy
    rw [← IsOpenImmersion.lift_fac j y hy, Category.assoc, Category.assoc, hj]

end GlobalTheory.ClopenEqualizer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothPeriodicPartitionOfUnity
section
open Complex Matrix
open scoped ContDiff BigOperators Real Topology Pointwise Manifold

namespace GlobalTheory.PeriodicPartition

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem _root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) :
    LocallyFinite fun l : Λ => Function.support fun z : E => φ (z + l) := by
  intro x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  have hclosed : IsClosed (Λ : Set E) :=
    (Λ.toAddSubgroup).isClosed_of_discreteTopology
  have hfin : ((tsupport φ - Metric.closedBall x 1) ∩ (Λ : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (hφ.isBounded.sub Metric.isBounded_closedBall) hclosed
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  rintro l ⟨z, hz, hzb⟩
  refine ⟨?_, l.2⟩
  have hmem := Set.sub_mem_sub (subset_tsupport φ (show z + (l : E) ∈ Function.support φ from hz)) hzb
  rwa [add_sub_cancel_left] at hmem


open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem _root_.GlobalTheory.PeriodicPartition.exists_finite_subcover (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {κ : Type} (V : κ → Set E) (hV : ∀ k, IsOpen (V k))
    (hper : ∀ k (l : Λ) z, z ∈ V k → z + l ∈ V k) (hcov : ∀ z, ∃ k, z ∈ V k) :
    ∃ t : Finset κ, ∀ z, ∃ k ∈ t, z ∈ V k := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let b' := b.ofZLatticeBasis ℝ Λ
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b')) :=
    (ZSpan.fundamentalDomain_isBounded b').isCompact_closure
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hV (fun z _ => Set.mem_iUnion.2 (hcov z))
  refine ⟨t, fun z => ?_⟩
  obtain ⟨k, hk, hz⟩ := Set.mem_iUnion₂.1 (ht (subset_closure (ZSpan.fract_mem_fundamentalDomain b' z)))
  have hmem : (ZSpan.floor b' z : E) ∈ Λ := by
    exact (b.ofZLatticeBasis_span ℝ Λ).le (ZSpan.floor b' z).2
  refine ⟨k, hk, ?_⟩
  simpa [ZSpan.fract_apply] using hper k ⟨_, hmem⟩ _ hz

end GlobalTheory.PeriodicPartition

namespace GlobalTheory

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem hasFiniteSupport_lattice_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) (z : E) :
    Function.HasFiniteSupport fun l : Λ => φ (z + l) :=
  (_root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ).point_finite z

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem contDiff_finsum_of_locallyFinite_support {ι : Type} {f : ι → E → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hlf : LocallyFinite fun i => Function.support (f i)) :
    ContDiff ℝ ∞ fun x => ∑ᶠ i, f i x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨s, hs⟩ := finsum_eventually_eq_sum hlf x
  exact (ContDiff.sum fun i _ => hf i).contDiffAt.congr_of_eventuallyEq hs

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem contDiff_finsum_lattice_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) (hs : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ fun z => ∑ᶠ l : Λ, φ (z + l) :=
  contDiff_finsum_of_locallyFinite_support (fun l => hs.comp (contDiff_id.add contDiff_const))
    (_root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ)

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem finsum_lattice_translate_add (Λ : Submodule ℤ E) (φ : E → ℝ) (l : Λ) (z : E) :
    ∑ᶠ m : Λ, φ (z + l + m) = ∑ᶠ m : Λ, φ (z + m) := by
  rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : Λ => φ (z + m))]
  simp [add_assoc]

open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
open scoped Pointwise in
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem tsupport_finsum_lattice_translate_subset (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (φ : E → ℝ) (hφ : HasCompactSupport φ) (U : Set E) (hU : tsupport φ ⊆ U)
    (hper : ∀ (l : Λ) z, z ∈ U → z + l ∈ U) :
    tsupport (fun z => ∑ᶠ l : Λ, φ (z + l)) ⊆ U := by
  have hlf := _root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ
  have h1 : Function.support (fun z => ∑ᶠ l : Λ, φ (z + l)) ⊆
      ⋃ l : Λ, Function.support fun z => φ (z + l) := by
    intro z hz
    by_contra h
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at h
    exact hz (by simp [h])
  intro z hz
  have hz' := closure_mono h1 hz
  rw [hlf.closure_iUnion] at hz'
  obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hz'
  have hl' : z + l ∈ tsupport φ := tsupport_comp_subset_preimage φ (continuous_add_const (l : E)) hl
  simpa using hper (-l) _ (hU hl')


open Complex Matrix in
open scoped ContDiff BigOperators Real Topology Manifold in
theorem _root_.GlobalTheory.exists_smooth_periodic_partition_of_unity :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → ∃ (s : Finset ι) (ρ : ι → (Fin g → ℂ) → ℝ), (∀ i, ContDiff ℝ ∞ (ρ i) ∧ (∀ (l : Λ) z, ρ i (z + l) = ρ i z) ∧ tsupport (ρ i) ⊆ U i) ∧ ∀ z, ∑ i ∈ s, ρ i z = 1 := by
  intro g Λ hdisc hspan ι U hU hper hcov
  haveI := hdisc
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.PeriodicPartition.exists_finite_subcover Λ
    (fun x : Fin g → ℂ => {z | ∃ l : Λ, z + (l : Fin g → ℂ) ∈ Metric.ball x 1})
    (fun x => by
      have hset : {z | ∃ l : Λ, z + (l : Fin g → ℂ) ∈ Metric.ball x 1} =
          ⋃ l : Λ, (· + (l : Fin g → ℂ)) ⁻¹' Metric.ball x 1 := by
        ext z; simp
      rw [hset]
      exact isOpen_iUnion fun l => Metric.isOpen_ball.preimage (continuous_add_const _))
    (fun x l z ⟨m, hm⟩ => ⟨m - l, by
      have hzm : z + (l : Fin g → ℂ) + ((m - l : Λ) : Fin g → ℂ) = z + m := by push_cast; abel
      rw [hzm]
      exact hm⟩)
    (fun z => ⟨z, 0, by simp⟩)
  let β : (Fin g → ℂ) → (Fin g → ℂ) → ℝ := fun x => ⇑(⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump x)
  let θ : (Fin g → ℂ) → ℝ := fun z => ∑ x ∈ t, β x z
  have hθs : ContDiff ℝ ∞ θ := ContDiff.sum fun x _ => ContDiffBump.contDiff _
  have hθc : HasCompactSupport θ := by
    have hθeq : θ = ∑ x ∈ t, β x := by
      funext z
      simp [θ, Finset.sum_apply]
    rw [hθeq]
    exact HasCompactSupport.finset_sum fun x _ => ContDiffBump.hasCompactSupport _
  have hθn : ∀ z, 0 ≤ θ z := fun z => Finset.sum_nonneg fun x _ => ContDiffBump.nonneg _
  have hθ1 : ∀ x ∈ t, ∀ y ∈ Metric.ball x 1, 1 ≤ θ y := by
    intro x hx y hy
    have h := Finset.single_le_sum (f := fun x => β x y) (fun x _ => ContDiffBump.nonneg _) hx
    have h1 : β x y = 1 := ContDiffBump.one_of_mem_closedBall _ (Metric.ball_subset_closedBall hy)
    show 1 ≤ ∑ x ∈ t, β x y
    linarith
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin g → ℂ) isClosed_univ U hU
    (fun z _ => Set.mem_iUnion.2 (hcov z))
  have hps : ∀ i, ContDiff ℝ ∞ (p i) := fun i => contMDiff_iff_contDiff.1 (p i).contMDiff
  have hsfin := p.locallyFinite.finite_nonempty_inter_compact hθc
  let s := hsfin.toFinset
  have hkey : ∀ y, θ y * ∑ i ∈ s, p i y = θ y := by
    intro y
    by_cases hy : θ y = 0
    · simp [hy]
    · have hsum : ∑ᶠ i, p i y = ∑ i ∈ s, p i y := by
        apply finsum_eq_sum_of_support_subset
        intro i hi
        simp only [s, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
        exact ⟨y, hi, subset_tsupport _ hy⟩
      rw [← hsum, p.sum_eq_one (Set.mem_univ y), mul_one]
  let a : ι → (Fin g → ℂ) → ℝ := fun i z => θ z * p i z
  have has : ∀ i, ContDiff ℝ ∞ (a i) := fun i => hθs.mul (hps i)
  have hac : ∀ i, HasCompactSupport (a i) := fun i => hθc.mul_right
  have hat : ∀ i, tsupport (a i) ⊆ U i := fun i => tsupport_mul_subset_right.trans (hp i)
  let Θ : (Fin g → ℂ) → ℝ := fun z => ∑ᶠ l : Λ, θ (z + l)
  have hΘpos : ∀ z, 0 < Θ z := by
    intro z
    obtain ⟨x, hx, l, hl⟩ := ht z
    exact lt_of_lt_of_le one_pos ((hθ1 x hx _ hl).trans
      (single_le_finsum l (hasFiniteSupport_lattice_translate Λ θ hθc z) fun m => hθn _))
  have hΘs : ContDiff ℝ ∞ Θ := contDiff_finsum_lattice_translate Λ θ hθc hθs
  refine ⟨s, fun i z => (∑ᶠ l : Λ, a i (z + l)) / Θ z, fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (contDiff_finsum_lattice_translate Λ (a i) (hac i) (has i)).div hΘs fun z => (hΘpos z).ne'
  · intro l z
    simp only [Θ]
    rw [finsum_lattice_translate_add, finsum_lattice_translate_add]
  · show tsupport (fun z => (∑ᶠ l : Λ, a i (z + l)) / Θ z) ⊆ U i
    have hfun : (fun z => (∑ᶠ l : Λ, a i (z + l)) / Θ z) =
        fun z => (∑ᶠ l : Λ, a i (z + l)) * (Θ z)⁻¹ := by
      ext z; rw [div_eq_mul_inv]
    rw [hfun]
    exact tsupport_mul_subset_left.trans
      (tsupport_finsum_lattice_translate_subset Λ (a i) (hac i) (U i) (hat i) (hper i))
  · intro z
    show ∑ i ∈ s, (∑ᶠ l : Λ, a i (z + l)) / Θ z = 1
    rw [← Finset.sum_div, div_eq_one_iff_eq (hΘpos z).ne',
      ← finsum_sum_comm s (fun (l : Λ) i => a i (z + l))
        (fun i _ => hasFiniteSupport_lattice_translate Λ (a i) (hac i) z)]
    apply finsum_congr
    intro l
    simp only [a]
    rw [← Finset.mul_sum]
    exact hkey _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemMapKerOfOneTmulEqZeroOfFlat
section
open scoped TensorProduct

namespace GlobalTheory

theorem mem_map_ker_of_one_tmul_eq_zero_of_flat (B C k : Type) [CommRing B] [CommRing C]
    [Algebra B C] [Module.Flat B C] [Field k] [Algebra B k] (c : C)
    (h : (1 : k) ⊗ₜ[B] c = 0) :
    c ∈ (RingHom.ker (algebraMap B k)).map (algebraMap B C) := by
  classical
  set I : Ideal B := RingHom.ker (algebraMap B k) with hI
  let f : (B ⧸ I) →ₗ[B] k :=
    Submodule.liftQ I (Algebra.linearMap B k) (fun a ha => by simpa [hI] using ha)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun a ha => by simpa [hI] using ha)
  have hinj : Function.Injective (f.rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hx : (Ideal.Quotient.mk I 1) ⊗ₜ[B] c = 0 := by
    apply hinj
    have h1 : f (Ideal.Quotient.mk I 1) = 1 := by
      show Submodule.liftQ I (Algebra.linearMap B k) _ (Submodule.Quotient.mk 1) = 1
      rw [Submodule.liftQ_apply, Algebra.linearMap_apply, map_one]
    rw [LinearMap.rTensor_tmul, map_zero, h1]
    exact h
  have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul C I) hx
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, map_zero, one_smul,
    Submodule.Quotient.mk_eq_zero] at hq
  rw [Ideal.smul_top_eq_map] at hq
  exact hq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialMapMaximalIdealIsPrime
section
open scoped TensorProduct

namespace GlobalTheory

theorem valuationRing_exists_dvd_all {O ι : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    (f : ι → O) (s : Finset ι) (hs : s.Nonempty) : ∃ i ∈ s, ∀ j ∈ s, f i ∣ f j := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, by simp, by simp⟩
  | cons a s ha hs ih =>
    obtain ⟨i, hi, h⟩ := ih
    rcases ValuationRing.dvd_total (f a) (f i) with h1 | h1
    · refine ⟨a, by simp, fun j hj => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact dvd_rfl
      · exact h1.trans (h j hj)
    · refine ⟨i, by simp [hi], fun j hj => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact h1
      · exact h j hj

theorem mvPolynomial_map_maximalIdeal_isPrime (O : Type) [CommRing O] [IsLocalRing O] (g : ℕ) :
    ((IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)).IsPrime := by
  have h : (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)
      = RingHom.ker (MvPolynomial.map (σ := Fin g) (IsLocalRing.residue O)) := by
    ext F
    rw [MvPolynomial.mem_map_C_iff, RingHom.mem_ker, MvPolynomial.ext_iff]
    simp only [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      IsLocalRing.residue_eq_zero_iff]
  rw [h]
  exact RingHom.ker_isPrime _

theorem mvPolynomial_exists_content (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] (g : ℕ)
    (F : MvPolynomial (Fin g) O) (hF : F ≠ 0) :
    ∃ (π : O) (F' : MvPolynomial (Fin g) O), F = MvPolynomial.C π * F' ∧
      F' ∉ (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) := by
  obtain ⟨i, hi, h⟩ := valuationRing_exists_dvd_all (fun m => F.coeff m) F.support
    (MvPolynomial.support_nonempty.2 hF)
  have hd : MvPolynomial.C (F.coeff i) ∣ F := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro m
    by_cases hm : m ∈ F.support
    · exact h m hm
    · rw [MvPolynomial.notMem_support_iff.1 hm]
      exact dvd_zero _
  obtain ⟨F', hF'⟩ := hd
  refine ⟨F.coeff i, F', hF', fun hmem => ?_⟩
  have h1 := MvPolynomial.mem_map_C_iff.1 hmem i
  have h2 : F.coeff i = F.coeff i * F'.coeff i := by
    conv_lhs => rw [hF', MvPolynomial.coeff_C_mul]
  have h3 : F'.coeff i = 1 :=
    (mul_left_cancel₀ (MvPolynomial.mem_support_iff.1 hi) ((mul_one _).trans h2)).symm
  rw [h3] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem mvPolynomial_content_valuationRing :
    ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] (g : ℕ), ((IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)).IsPrime ∧ (∀ F : MvPolynomial (Fin g) O, F ≠ 0 → ∃ (π : O) (F' : MvPolynomial (Fin g) O), F = MvPolynomial.C π * F' ∧ F' ∉ (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)) ∧ ∀ (π : O) (u F : MvPolynomial (Fin g) O), u ∉ (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) → MvPolynomial.C π ∣ u * F → MvPolynomial.C π ∣ F := by
  intro O _ _ _ g
  have hp := mvPolynomial_map_maximalIdeal_isPrime O g
  refine ⟨hp, mvPolynomial_exists_content O g, fun π u F hu hdvd => ?_⟩
  by_cases hF : F = 0
  · rw [hF]; exact dvd_zero _
  obtain ⟨π', F', rfl, hF'⟩ := mvPolynomial_exists_content O g F hF
  have huF : u * F' ∉ (IsLocalRing.maximalIdeal O).map
      (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) := fun h => (hp.mem_or_mem h).elim hu hF'
  rw [MvPolynomial.mem_map_C_iff, not_forall] at huF
  obtain ⟨m, hm⟩ := huF
  have hunit : IsUnit ((u * F').coeff m) := by
    by_contra hn
    exact hm ((IsLocalRing.mem_maximalIdeal _).2 hn)
  have h1 : π ∣ π' * (u * F').coeff m := by
    have := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).1 hdvd m
    rwa [mul_left_comm, MvPolynomial.coeff_C_mul] at this
  have h2 : π ∣ π' := (hunit.dvd_mul_right).1 h1
  exact Dvd.dvd.mul_right (map_dvd _ h2) _

end GlobalTheory
end

