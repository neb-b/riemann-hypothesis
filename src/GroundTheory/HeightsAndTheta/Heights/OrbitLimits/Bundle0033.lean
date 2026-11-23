module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0030

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosDensIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsPosDensIntegrable.proof (hMass : PtsSemiPosMassFinite.Statement) : PtsPosDensIntegrable.Statement := by
  intro K _ ι _ P e Ψ L g hP hΨ hL hg
  classical
  obtain ⟨M, hMb⟩ := PtsPosDens.exists_bound hg
  choose T hTs hTp hLTp using fun j => Inter.SemiPosTwist.proof Inter.TorusInvLevi.proof K ι (L j) (hL j)
  set N : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => ((L j).tensor (T j)).tensor (T j) with hNdef
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j =>
    ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hL j) (hTs j)
  have hNs : ∀ j, IsSmoothHerm (N j) := fun j => ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hLT j) (hTs j)
  have hNp : ∀ j, Inter.IsSemiPosHerm (N j) := fun j =>
    PtsPosDens.isSemiPosHerm_tensor (hLT j) (hTs j) (hLTp j) (hTp j)
  have hfinM := hMass K ι P e Ψ N hP hΨ hNs hNp
  have hfib := fibreFinite K ι P e Ψ hP hΨ
  set C : ℝ := max M 0 * 3 ^ e with hCdef
  have hC : 0 ≤ C := by positivity

  have key : ∀ y w, max (sheetDensity P Ψ (pot L) g y w) 0 ≤
      C * max (sheetDensity P Ψ (pot N) (fun _ => 1) y w) 0 := by
    intro y w
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · rw [dite_eq_left hγ, dite_eq_left hγ]
      have hS := hγ.choose_spec
      have hab : |maDensity (fun j y' => pot L j (hγ.choose y')) y| ≤
          3 ^ e * maDensity (fun j y' => pot N j (hγ.choose y')) y :=
        Inter.PointsAbsIntegrable.abs_maDensity_le hL hTs hTp hLTp hS
      have hmc : hγ.choose y ∈ mcPts P := hS.2.self_of_nhds.2.1
      have hgb : |g (hγ.choose y)| ≤ max M 0 := (hMb _ hmc.1).trans (le_max_left _ _)
      have hn : 0 ≤ maDensity (fun j y' => pot N j (hγ.choose y')) y :=
        nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hab) (by positivity)
      calc max (g (hγ.choose y) * maDensity (fun j y' => pot L j (hγ.choose y')) y) 0
          ≤ |g (hγ.choose y) * maDensity (fun j y' => pot L j (hγ.choose y')) y| :=
            max_le (le_abs_self _) (abs_nonneg _)
        _ = |g (hγ.choose y)| * |maDensity (fun j y' => pot L j (hγ.choose y')) y| := abs_mul _ _
        _ ≤ max M 0 * (3 ^ e * maDensity (fun j y' => pot N j (hγ.choose y')) y) :=
            mul_le_mul hgb hab (abs_nonneg _) (le_max_right _ _)
        _ = C * max (1 * maDensity (fun j y' => pot N j (hγ.choose y')) y) 0 := by
            rw [one_mul, max_eq_left hn, hCdef]
            ring
    · rw [dite_eq_right hγ, dite_eq_right hγ, max_self, mul_zero]

  have hpt : ∀ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y) ≤
      ENNReal.ofReal C * ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) := by
    intro y
    rw [← ENNReal.ofReal_mul hC]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold ptsPosDens
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfib y), finsum_mem_eq_finite_toFinset_sum _ (hfib y),
      Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => key y w
  have hnn : ∀ y, 0 ≤ ptsPosDens P Ψ (pot L) g y := fun y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _
  refine ⟨PtsPosDens.aestronglyMeasurable hP hΨ hL hg, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  calc ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y)
      ≤ ∫⁻ y, ENNReal.ofReal C * ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) := lintegral_mono hpt
    _ = ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinM

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PotFinCons
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem pot_fin_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem PoincareLelongRegularised.proof (hInt : PtsIntegrableStatement)
    (hMeas : GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.Statement) : PoincareLelongRegularised.Statement := by
  intro K _ ι _ P n L A B s hP hL hA hB _ hs
  obtain ⟨a, ha, hsa, hsP⟩ := id hs
  have hM : ∀ j, IsSmoothHerm ((Fin.cons B L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) := fun j =>
    Fin.cases (by simpa using hB) (fun i => by simpa using hL i) j
  have hlim := GroundTheory.Heights₂.Heights.Inter.PtsRegLimit.proof hInt
    (GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.proof hInt hMeas) K ι P (n + 1) (Fin.cons B L) A s
    ⟨a, ha, hsa⟩ hP hM hA hsP
  rw [pot_fin_cons] at hlim
  have hg : ∀ ε, (fun z => Real.log ((GroundTheory.Heights₂.Heights.Inter.regLine A s ⟨a, ha, hsa⟩ ε).h z)) =
      regLog A s ε := by
    intro ε
    funext z
    rw [GroundTheory.Heights₂.Heights.Inter.log_regLine_h]
    rfl
  simpa only [hg] using hlim

end GroundTheory.Heights₂.Heights.Targets
end

