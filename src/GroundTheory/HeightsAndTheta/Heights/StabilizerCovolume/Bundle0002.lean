module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.EigenLatDifferent
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.BRegWeightLevi
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {a : K → ℤ}
  {w : ((Σ k, ι k) → ℂ) → ℝ}

theorem BoundedRegularisationSetting.eventually_closedBall_subset (S : BoundedRegularisationSetting M Xo a w) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (S.B.mid j),
      closedBall (S.B.chart j x) t ⊆ (S.B.chart j).target := by
  refine Filter.eventually_all.2 fun j => ?_
  have hc : IsCompact (closure (S.B.mid j)) := isClosed_closure.isCompact
  have himg : IsCompact (S.B.chart j '' closure (S.B.mid j)) :=
    hc.image_of_continuousOn ((S.B.chart j).continuousOn.mono (S.B.closure_mid j))
  have hsub : S.B.chart j '' closure (S.B.mid j) ⊆ (S.B.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (S.B.chart j).map_source (S.B.closure_mid j hx)
  obtain ⟨δ, hδ, hδs⟩ := himg.exists_cthickening_subset_open (S.B.chart j).open_target hsub
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht x hx
  exact (closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((cthickening_mono ht.2.le _).trans hδs)

theorem BoundedRegularisationSetting.eventually_chartLevi (S : BoundedRegularisationSetting M Xo a w) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.bregWeight t) ∧
      ∀ k : Fin S.B.N, ∀ x ∈ S.B.mid k, ∀ v : Fin d → ℂ,
        -(4 * S.Cη * S.e1 t) * ‖v‖ ^ 2 ≤
          levi (S.B.chartFun (S.bregWeight t) k) (S.B.chart k x) v := by
  filter_upwards [self_mem_nhdsWithin, S.eventually_closedBall_subset, hS.compare] with t ht hball hcmp
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht (S.e1_ge t ht)
  exact GroundTheory.Heights₂.Heights.Regular.BoundedGlue.proof M.Xc d M.atlas S.B S.ρ S.η S.Cη t (S.e1 t)
    S.cutoff ht hε hball hcmp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.DifferentLatIndex
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

def DifferentLatIndex.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] (K : Type) [Field K] [NumberField K]
    (N : ℕ) (I : Submodule (𝓞 Em) (Fin N → Em)) (ρ : ℕ) (v : Fin ρ → Fin N → Em), IsNzFamily I ρ v →
    ∀ s : Em →+* K,
      genIndex (diffLat s I).toAddSubgroup (familyLat s v).toAddSubgroup =
        ((familyIndex I v : ℝ) / |(discr Em : ℝ)| ^ ρ) ^ ((Module.finrank ℚ K : ℝ) / Module.finrank ℚ Em)

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PhiISemipositive
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree Metric
open ReciprocityTheory.AnForm.A (IsPsh)
open scoped Matrix ComplexOrder

section Gram

variable {k : ℕ}

variable {ρ m : Type} [Fintype ρ] [Fintype m]

end Gram

section Psh

variable {d : ℕ}

theorem isPsh_congr' {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (h : Set.EqOn φ ψ U)
    (hφ : IsPsh U φ) : IsPsh U ψ := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in nhdsWithin z U, φ x < y := hφ.1 z hz y (by show φ z < y; rw [h hz]; exact hy)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
    rwa [← h hxU]
  · have hs : Set.EqOn (fun ζ : ℂ => φ (z + ζ • w)) (fun ζ => ψ (z + ζ • w)) (sphere 0 |(1 : ℝ)|) :=
      fun ζ hζ => h (hd ζ (by simp at hζ; rw [hζ]))
    obtain ⟨h1, h2⟩ := hφ.2 z w hd
    refine ⟨(circleIntegrable_congr hs).1 h1, ?_⟩
    have hz : z ∈ U := by simpa using hd 0 (by simp)
    rw [← Real.circleAverage_congr_sphere hs, ← h hz]
    exact h2

theorem isPsh_add_re_add_const {U : Set (Fin d → ℂ)} (hU : IsOpen U) {φ : (Fin d → ℂ) → ℝ} (hφ : IsPsh U φ)
    {G : (Fin d → ℂ) → ℂ} (hG : DifferentiableOn ℂ G U) (c : ℝ) :
    IsPsh U (fun w => φ w + (G w).re + c) := by
  have hcont : ContinuousOn (fun w => (G w).re) U := Complex.continuous_re.comp_continuousOn hG.continuousOn
  refine ⟨(hφ.1.add hcont.upperSemicontinuousOn).add upperSemicontinuousOn_const, fun z w hd => ?_⟩
  obtain ⟨hint, hle⟩ := hφ.2 z w hd
  have hmap : Continuous fun ζ : ℂ => z + ζ • w := continuous_const.add (continuous_id.smul continuous_const)
  have hdiff : DifferentiableOn ℂ (fun ζ : ℂ => G (z + ζ • w)) (closedBall 0 1) := by
    intro ζ hζ
    have hζU : z + ζ • w ∈ U := hd ζ (by simpa using hζ)
    have hGa : DifferentiableAt ℂ G (z + ζ • w) := hG.differentiableAt (hU.mem_nhds hζU)
    have hl : DifferentiableAt ℂ (fun ζ : ℂ => z + ζ • w) ζ :=
      (differentiableAt_const _).add (differentiableAt_id.smul_const w)
    exact (hGa.comp ζ hl).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun ζ : ℂ => G (z + ζ • w)) (ball 0 |(1 : ℝ)|) := by
    rw [abs_one]
    exact hdiff.diffContOnCl_ball subset_rfl
  have hmean : Real.circleAverage (fun ζ : ℂ => G (z + ζ • w)) 0 1 = G z := by
    have := hdc.circleAverage
    simpa using this
  have hcs : ContinuousOn (fun ζ : ℂ => G (z + ζ • w)) (sphere 0 1) :=
    hdiff.continuousOn.mono sphere_subset_closedBall
  have hciG : CircleIntegrable (fun ζ : ℂ => G (z + ζ • w)) 0 1 := hcs.circleIntegrable zero_le_one
  have hciR : CircleIntegrable (fun ζ : ℂ => (G (z + ζ • w)).re) 0 1 :=
    (Complex.continuous_re.comp_continuousOn hcs).circleIntegrable zero_le_one
  have hre : Real.circleAverage (fun ζ : ℂ => (G (z + ζ • w)).re) 0 1 = (G z).re := by
    have := ContinuousLinearMap.circleAverage_comp_comm Complex.reCLM hciG
    rw [hmean] at this
    simpa [Function.comp_def] using this
  have hci2 : CircleIntegrable (fun ζ : ℂ => φ (z + ζ • w) + (G (z + ζ • w)).re) 0 1 := hint.add hciR
  refine ⟨hci2.add (circleIntegrable_const c 0 1), ?_⟩
  have e1 := Real.circleAverage_fun_add hci2 (circleIntegrable_const c 0 1)
  have e2 := Real.circleAverage_fun_add hint hciR
  show φ z + (G z).re + c ≤ Real.circleAverage (fun ζ : ℂ => φ (z + ζ • w) + (G (z + ζ • w)).re + c) 0 1
  rw [e1, e2, hre, Real.circleAverage_const]
  linarith

end Psh

section Hodge

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

end Hodge

end GroundTheory.Heights₂.Heights.NineStatements
end
end

