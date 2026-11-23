module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

@[expose] public section

open Matrix Set
open scoped ComplexOrder MatrixOrder
namespace GlobalTheory

section

open Filter Metric Function
open scoped Topology

theorem differentiableOn_intervalIntegral_comp_clm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) {h : E → ℂ}
    (hh : DifferentiableOn ℂ h U) {L : ℝ → E →L[ℂ] E} (hL : Continuous L)
    (hLU : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (L s) U U) :
    DifferentiableOn ℂ (fun z => ∫ s in (0 : ℝ)..1, h (L s z)) U := by
  intro z₀ hz₀
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨K, hK, hKU, hc⟩ := local_compact_nhds (hU.mem_nhds hz₀)
  have hA : Continuous fun p : E × ℝ => L p.2 p.1 := (hL.comp continuous_snd).clm_apply continuous_fst
  have hM : MapsTo (fun p : E × ℝ => L p.2 p.1) (U ×ˢ Icc 0 1) U := fun p hp => hLU _ hp.2 hp.1
  have h1 : ContinuousOn (fun p : E × ℝ => h (L p.2 p.1)) (U ×ˢ Icc 0 1) :=
    hh.continuousOn.comp hA.continuousOn hM
  have h2 : ContinuousOn (fun p : E × ℝ => (fderiv ℂ h (L p.2 p.1)).comp (L p.2)) (U ×ˢ Icc 0 1) :=
    ((SCV.differentiableOn_fderiv hU hh).continuousOn.comp hA.continuousOn hM).clm_comp
      (hL.comp continuous_snd).continuousOn
  have hI : Set.uIoc (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  have h3 : ∀ z ∈ U, ContinuousOn (fun s => h (L s z)) (Icc 0 1) := fun z hz =>
    h1.comp (Continuous.prodMk_right z).continuousOn fun s hs => ⟨hz, hs⟩
  obtain ⟨C, hC⟩ := (hc.prod isCompact_Icc).exists_bound_of_continuousOn
    (h2.mono (prod_mono hKU Subset.rfl))
  refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (F := fun z s => h (L s z)) (F' := fun z s => (fderiv ℂ h (L s z)).comp (L s))
    (bound := fun _ => C) hK ?_ ?_ ?_ ?_ ?_ ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [hU.mem_nhds hz₀] with z hz
    exact ((h3 z hz).mono hI).aestronglyMeasurable measurableSet_uIoc
  · exact ContinuousOn.intervalIntegrable_of_Icc zero_le_one (h3 z₀ hz₀)
  · exact ((h2.comp (Continuous.prodMk_right z₀).continuousOn fun s hs => ⟨hz₀, hs⟩).mono
      hI).aestronglyMeasurable measurableSet_uIoc
  · exact Eventually.of_forall fun s hs z hz => hC (z, s) ⟨hz, hI hs⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun s hs z hz =>
      (hh.differentiableAt (hU.mem_nhds (hLU s (hI hs) (hKU hz)))).hasFDerivAt.comp z
        (L s).hasFDerivAt

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℝ}


omit [Fintype ι] in
theorem update_mem_polydisc {z : ι → ℂ} (hz : z ∈ univ.pi fun j => ball (0 : ℂ) (r j)) {i : ι}
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) (r i)) : update z i t ∈ univ.pi fun j => ball (0 : ℂ) (r j) := by
  intro j _
  rcases eq_or_ne j i with rfl | hj
  · simpa using ht
  · simpa [hj] using hz j trivial

theorem exists_eq_coord_mul_of_vanishing {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (univ.pi fun j => ball 0 (r j))) (i : ι)
    (h0 : ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), f (update z i 0) = 0) :
    ∃ g : (ι → ℂ) → ℂ, DifferentiableOn ℂ g (univ.pi fun j => ball 0 (r j)) ∧
      ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), f z = z i * g z := by
  have hU : IsOpen (univ.pi fun j => ball (0 : ℂ) (r j)) :=
    isOpen_set_pi finite_univ fun _ _ => isOpen_ball
  let e : ι → ℂ := Pi.single i 1
  let L : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ) := fun s =>
    ContinuousLinearMap.id ℂ _ + ((s : ℂ) - 1) • (ContinuousLinearMap.proj i).smulRight e
  have hL : ∀ s z, L s z = z + ((s : ℂ) - 1) • z i • e := fun s z => rfl
  have hL' : ∀ (s : ℝ) z, L s z = update z i (s * z i) := by
    intro s z
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp [hL, e]; ring
    · simp [hL, e, hj]
  have hLU : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (L s) (univ.pi fun j => ball (0 : ℂ) (r j))
      (univ.pi fun j => ball (0 : ℂ) (r j)) := by
    intro s hs z hz
    rw [hL']
    refine update_mem_polydisc hz ?_
    have := hz i trivial
    rw [mem_ball_zero_iff] at this ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans_lt this
  have hLc : Continuous L := by fun_prop
  have hd := SCV.differentiableOn_fderiv_apply hU hf e
  refine ⟨_, differentiableOn_intervalIntegral_comp_clm hU hd hLc hLU, fun z hz => ?_⟩
  have hc : ContinuousOn (fun s => fderiv ℂ f (L s z) e) (Icc 0 1) :=
    hd.continuousOn.comp (hLc.clm_apply continuous_const).continuousOn fun s hs => hLU s hs hz
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => f (L s z))]
  · simp [hL', h0 z hz]
  · intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 : HasDerivAt (fun t : ℂ => z + (t - 1) • z i • e) (z i • e) s := by
      simpa using (((hasDerivAt_id (s : ℂ)).sub_const 1).smul_const (z i • e)).const_add z
    have h2 : HasFDerivAt f (fderiv ℂ f (L s z)) (z + ((s : ℂ) - 1) • z i • e) :=
      (hf.differentiableAt (hU.mem_nhds (hLU s hs hz))).hasFDerivAt
    have h3 := (h2.comp_hasDerivAt (s : ℂ) h1).comp_ofReal
    rw [map_smul, smul_eq_mul] at h3
    exact h3
  · exact ContinuousOn.intervalIntegrable_of_Icc zero_le_one (continuousOn_const.mul hc)

end

end GlobalTheory
