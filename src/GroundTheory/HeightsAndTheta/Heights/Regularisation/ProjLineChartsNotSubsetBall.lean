module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0003

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli regMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts BoundedPshData pointReg pointCharts pointAtlas)

local notation "RegChartDataA" => GroundTheory.Heights₂.Heights.Regular.RegChartData

noncomputable section

theorem isClosed_coordDiv {D : ℕ} (S : Finset (Fin D)) : IsClosed (coordDiv S) := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact isClosed_biUnion_finset fun i _ => isClosed_singleton.preimage (continuous_apply i)

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem isOpen_Yo_regular (R : RegChartDataA A) : IsOpen R.Yo := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  obtain ⟨j, hj⟩ := R.cover x
  have hs : x ∈ (R.chart j).source := R.mid_subset_source j (R.inner_subset_mid j hj)
  exact ⟨(R.chart j).source ∩ R.chart j ⁻¹' (coordDiv (R.S j))ᶜ,
    fun y hy => (R.mem_Yo j y hy.1).2 hy.2,
    (R.chart j).isOpen_inter_preimage (isClosed_coordDiv _).isOpen_compl, hs,
    (R.mem_Yo j x hs).1 hx⟩

namespace RegChartData

def ofRegular [CompactSpace X] (R : RegChartDataA A) (om : LocPot X) (om_pot : IsPotential A om)
    (om_pos : IsPosPot A om) : RegChartData A where
  toRegCharts := RegCharts.ofPotentialCharts R.toPotentialCharts om om_pot om_pos
  Yo := R.Yo
  isOpen_Yo := isOpen_Yo_regular R
  S := R.S
  mem_Yo_iff j z hz := by
    have h := R.mem_Yo j _ ((R.chart j).map_target hz)
    rwa [(R.chart j).right_inv hz] at h
  r := R.r
  f := R.f
  f_cont j := (R.f_smooth j).continuousOn
  f_bdd j := ⟨R.f_bdd.choose, R.f_bdd.choose_spec j⟩
  r_chart j z hz := by
    refine (R.r_chart j z hz).trans ?_
    simp only [Real.log_inv, Finset.sum_neg_distrib]
    ring
  one_le_r := R.one_le_r
  φ := R.ph
  φ_smooth := R.ph_smooth
  psh := R.u_psh
  C := |R.Clog| + |R.Cph| + |R.Cgrad|
  φ_le x hx := (R.ph_le x hx).trans
    (by linarith [le_abs_self R.Cph, abs_nonneg R.Clog, abs_nonneg R.Cgrad])
  le_φ x hx := by
    have h1 := R.ph_ge x hx
    have h2 : 0 ≤ Real.log (R.r x) := Real.log_nonneg (R.one_le_r x hx)
    have h3 : R.Clog ≤ |R.Clog| + |R.Cph| + |R.Cgrad| := by
      linarith [le_abs_self R.Clog, abs_nonneg R.Cph, abs_nonneg R.Cgrad]
    nlinarith
  grad j z hz := by
    have hYo : (R.chart j).symm z ∈ R.Yo :=
      (R.mem_Yo j _ ((R.chart j).map_target hz.1)).2 (by rw [(R.chart j).right_inv hz.1]; exact hz.2)
    have hr : 1 ≤ R.r ((R.chart j).symm z) := R.one_le_r _ hYo
    have hC0 : 0 ≤ |R.Clog| + |R.Cph| + |R.Cgrad| := by positivity
    have hCg : |R.Cgrad| ≤ |R.Clog| + |R.Cph| + |R.Cgrad| := by
      linarith [abs_nonneg R.Clog, abs_nonneg R.Cph]
    have hpos : 0 ≤ R.r ((R.chart j).symm z) ^ R.Cgrad := Real.rpow_nonneg (by linarith) _
    have h1 : R.Cgrad * R.r ((R.chart j).symm z) ^ R.Cgrad ≤
        (|R.Clog| + |R.Cph| + |R.Cgrad|) * R.r ((R.chart j).symm z) ^ (|R.Clog| + |R.Cph| + |R.Cgrad|) :=
      calc R.Cgrad * R.r ((R.chart j).symm z) ^ R.Cgrad
          ≤ (|R.Clog| + |R.Cph| + |R.Cgrad|) * R.r ((R.chart j).symm z) ^ R.Cgrad :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCg) hpos
        _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hr ((le_abs_self _).trans hCg)) hC0
    exact (R.grad_le j z hz).trans (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)

end RegChartData

namespace BoundedThPsh

end BoundedThPsh

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
