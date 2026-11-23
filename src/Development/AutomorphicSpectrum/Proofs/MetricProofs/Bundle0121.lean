module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFourth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0111
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0119
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviChartRegularityStatementHolds

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalIntegrability
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead

theorem chart_reads : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, pPhi M F keep v bl h ε w ∈ pO M Rb keep v F kb V r h ∧ pRho M Rb keep v F kb r h ε (pPhi M F keep v bl h ε w) = w := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc w hw
  obtain ⟨hflag, hbase, hread⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc w hw
  obtain ⟨z, hz, hzv, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc w hw
  obtain ⟨hκ, -, hF, hBC, hr, -, hh⟩ := hc
  have hwV : pB ε w ∈ V := hw
  obtain ⟨hzb, -, hG, horb⟩ := hBC.2.2.2.2 _ hwV
  have hV : pB ε w ∈ (Rb.A.chart kb).target := hBC.2.1 hwV
  have hr1 : r (bl (pB ε w)) = (Rb.A.chart kb).symm (pB ε w) :=
    Rb.inj _ _ (fun hc => by simpa using hc.2 1 Submodule.mem_top) (orbit_trans (hr _ hzb) (orbit_symm horb))
  set φ := pPhi M F keep v bl h ε w with hφ
  have hMm : φ ∈ mcPts (mCoordIdeal (y ∘ v)) := by
    rw [← hzv]
    exact CPts.comp_mem_mcPts hκ (RingHom.id Φ) (x := y ∘ v) rfl hz
  have hL : ∀ τ, IsLowerUni (pMat keep (pL ε w) τ) := fun τ => WMan.Read.lowMat_lowerUni _ τ
  have hminor : ∀ (p : Ψ × Fin N) (k : K), keep p → M.blk p = some k → ∀ J : Finset (Fin N),
      twMinor M F (bl (pB ε w)) p.2 k (h p.1)⁻¹ (upV v φ) J =
        minorIJ (pMat keep (pL ε w) p.1) J (stepCols N j p.2) := fun p k hp hk J => by
    have := WMan.Read.twMinor_eq M hF hzb hG hk (hflag p.1).1 (hread p k hp hk) (h p.1)⁻¹ J
    rwa [show pH keep h ε p.1 w = h p.1 * pMat keep (pL ε w) p.1 from rfl,
      Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.2 (hh p.1).2)] at this
  refine ⟨⟨hMm, ?_, ?_, ?_⟩, ?_⟩
  · rw [hbase, hr1]
    exact (Rb.A.chart kb).map_target hV
  · rw [hbase, hr1, (Rb.A.chart kb).right_inv hV]
    exact hwV
  · intro p k hp hk
    rw [hbase, hminor p k hp hk, WMan.Read.minor_self_of_lowerUni (hL p.1)]
    exact one_ne_zero
  · funext i
    obtain ⟨s, rfl⟩ := ε.surjective i
    unfold pRho
    rw [Equiv.symm_apply_apply]
    rcases s with l | q
    · show Rb.A.chart kb (r (pBase M v φ)) l = w (ε (Sum.inl l))
      rw [hbase, hr1, (Rb.A.chart kb).right_inv hV]
      rfl
    · show pRead M F keep (pBase M v φ) h (upV v φ) q.1.1.1 q.1.1.2.1 q.1.1.2.2 = w (ε (Sum.inr q))
      obtain ⟨hkeep, hpr, hbS, haS, hent⟩ := GlobalTheory.T.pMat_stepCols_entry Ψ N j keep q M.j_le
      obtain ⟨hval, hzero⟩ := hent (pL ε w)
      obtain ⟨k, hk⟩ : ∃ k, M.blk (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) = some k := by
        rcases e' : M.blk (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) with _ | k
        · exact absurd hpr ((M.blk_none _).1 e')
        · exact ⟨k, rfl⟩
      obtain ⟨hsgn, hsgn0⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead.minor_replace N (pMat keep (pL ε w) q.1.1.1)
        (stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2)) q.1.1.2.1 q.1.1.2.2 (hL _) haS hbS q.1.2.1 hzero
      have e1 := hminor _ k hkeep hk
      rw [hbase]
      unfold pRead
      rw [hk]
      show twMinor M F (bl (pB ε w)) (pStep j keep q.1.1.1 q.1.1.2.2) k (h q.1.1.1)⁻¹ (upV v φ) _ /
        (_ * twMinor M F (bl (pB ε w)) (pStep j keep q.1.1.1 q.1.1.2.2) k (h q.1.1.1)⁻¹ (upV v φ) _) = _
      rw [e1, e1, hsgn, WMan.Read.minor_self_of_lowerUni (hL _), mul_one, mul_div_cancel_left₀ _ hsgn0, hval]
      rfl

end GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameLUMinorValue
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead

theorem isProperStep_stepOf {N j : ℕ} (hj : j ≤ N) {a' b' : Fin N} (hba : b' < a')
    (hs : (a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) : IsProperStep N j (stepOf N j b') := by
  have ha := a'.2
  have hb := b'.2
  have hba' : (b' : ℕ) < a' := hba
  simp only [IsProperStep, stepOf]
  split_ifs with h
  · constructor <;> omega
  · constructor <;> omega

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (hh : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ' : Ψ) (a' b' : Fin N) (z : (Σ k, ι k) → ℂ) (A L U : Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → IsBlockDiag j A → (hh τ')⁻¹ * A = L * U → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c ∈ stepCols N j (stepOf N j b'), U c c ≠ 0) → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → (∀ k, M.blk (τ', stepOf N j b') = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j (stepOf N j b'))) → lowRead M F zb hh z τ' a' b' = L a' b' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F zb hh τ' a' b' z A L U hF hzb hG hA hLU hLb hLu hUb hUt hUd
    hba hs hz
  have hj := M.j_le
  have hP : IsProperStep N j (stepOf N j b') := isProperStep_stepOf hj hba hs
  obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', stepOf N j b') = some k := by
    cases h : M.blk (τ', stepOf N j b') with
    | none => exact absurd hP ((M.blk_none _).1 h)
    | some k => exact ⟨k, rfl⟩
  obtain ⟨α, hα, hzα⟩ := hz k hk
  have hT : ∀ J, twMinor M F zb (stepOf N j b') k (hh τ')⁻¹ z J =
      α * (minorIJ L J (stepCols N j (stepOf N j b')) *
        minorIJ U (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b'))) := by
    intro J
    rw [_root_.GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead.main K ι Φ y Ψ N j M F zb (τ', stepOf N j b') k A (hh τ')⁻¹ z α J hF hzb hG hk
      hA hzα, hLU, MinorCalc.minorIJ_mul_of_support L U J (stepCols N j (stepOf N j b'))
      (MinorCalc.support_stepCols (i := stepOf N j b') hj U hUb hUt)]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.lower_unipotent_minor_formula N j L a' b' hj hLb hLu hba hs
  have hUne : minorIJ U (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) ≠ 0 := by
    rw [MinorCalc.minorIJ_self_of_triangular U hUt]
    exact Finset.prod_ne_zero_iff.2 hUd
  unfold lowRead
  simp only [hk, Option.elim_some]
  rw [hT, hT, h1, h2, one_mul, mul_div_mul_left _ _ hα, mul_div_assoc, div_self hUne, mul_one]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsWeightedHomogeneousOfIsMultiHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open GoodChartModel Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (blkW weight_blkW segMono eval_segMono psiPoly eval_psiPoly
  comp_mul_homog diag_of_homog)

section Rel

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isWeightedHomogeneous_of_isMultiHomog [DecidableEq K] {s : MRingOver ℂ ι} {a : K → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : IsWeightedHomogeneous (blkW ι) s a := by
  intro d hd
  funext k
  rw [weight_blkW]
  exact hs d (mem_support_iff.2 hd) k

theorem cone_homog [DecidableEq K] {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) :
    Q.IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkW ι)) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  refine Ideal.homogeneous_span _ _ ?_
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_of_isMultiHomog ha)⟩

theorem cone_segre_rel {e : ℕ} {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ)
    (i : (k : K) → ι k) :
    ∃ r : ℕ, 0 < r ∧ ∃ G : Fin (e + 1) → MvPolynomial ((k : K) → ι k) ℂ,
      (∀ j, (G j).totalDegree ≤ r - 1) ∧
      ∀ z ∈ conePts Q, segre z i ^ r = ∑ j, Ψ (segre z) j * eval (segre z) (G j) := by
  classical
  have hsegMono (a : (k : K) → ι k) : IsWeightedHomogeneous (blkW ι) (segMono ι a) (fun _ => 1) := by
    have hprod := IsWeightedHomogeneous.prod (w := blkW ι) Finset.univ
      (fun k => (X ⟨k, a k⟩ : MvPolynomial (Σ k, ι k) ℂ))
      (fun k => blkW ι ⟨k, a k⟩) (fun k _ => isWeightedHomogeneous_X ℂ _ _)
    unfold segMono
    convert hprod using 1
    funext k
    simp [blkW, Finset.sum_apply, Pi.single_apply]
  have hpsiPoly (j : Fin (e + 1)) : IsWeightedHomogeneous (blkW ι) (psiPoly Ψ j) (fun _ => 1) := by
    unfold psiPoly
    exact IsWeightedHomogeneous.sum _ _ _ fun a _ => (hsegMono a).C_mul _
  set I := Q ⊔ Ideal.span (Set.range (psiPoly Ψ)) with hI
  have hrad : segMono ι i ∈ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    have hae : ∀ p : MvPolynomial (Σ k, ι k) ℂ, aeval x p = eval x p :=
      fun _ => rfl
    rw [hae]
    by_contra h
    rw [eval_segMono, ReciprocityTheory.ChartRestriction.G.Geo.segre, ← ne_eq, Finset.prod_ne_zero_iff] at h
    have hxm : x ∈ conePts Q := ⟨fun k => ⟨i k, h k (Finset.mem_univ _)⟩, fun f hf => by
      have := hx _ (Ideal.mem_sup_left hf : f ∈ I)
      rwa [hae] at this⟩
    refine hΨ x hxm (funext fun j => ?_)
    have := hx _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩) : psiPoly Ψ j ∈ I)
    rwa [hae, eval_psiPoly] at this
  obtain ⟨r0, hr0⟩ := hrad
  have hmem : segMono ι i ^ (r0 + 1) ∈ I := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hr0
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hb
  let D : K → ℕ := fun _ => r0
  let comp := weightedHomogeneousComponent (R := ℂ) (blkW ι) (D + fun _ => 1)
  have hpow : IsWeightedHomogeneous (blkW ι) (segMono ι i ^ (r0 + 1)) (D + fun _ => 1) := by
    have := (hsegMono i).pow (r0 + 1)
    convert this using 1
    funext k; simp [D]
  have hcomp := congrArg comp hab
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, weightedHomogeneousComponent_eq_self hpow] at hcomp
  simp only [comp, comp_mul_homog (hpsiPoly _)] at hcomp
  have hcd : ∀ j, ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ r0 ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z (weightedHomogeneousComponent (blkW ι) D (c j)) =
        eval (segre z) G :=
    fun j => diag_of_homog r0 (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  choose G hG hGz using hcd
  refine ⟨r0 + 1, Nat.succ_pos _, G, fun j => by simpa using hG j, fun z hz => ?_⟩
  have h0 := congrArg (eval z) hcomp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), hz.2 _ (weightedHomogeneousComponent_mem_of_mem _ _ (cone_homog hP) ha _),
    zero_add, map_sum, map_pow, eval_segMono] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hGz, eval_psiPoly, mul_comm]

theorem cone_pow_mem {Q : Ideal (MRingOver ℂ ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : setChartIdeal (conePts Q) σ Ψ ≤ J) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := cone_segre_rel hP Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine hJ ?_
    rw [setChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hz1, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, Gx, map_sub, map_add (f := _), map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
      GroundTheory.Heights₂.Heights.GoodChartModel.eval_linPoly, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, map_sub, map_add (f := _), map_sum, hX, h0, zero_add,
      homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (GroundTheory.Heights₂.Heights.GoodChartModel.homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

theorem cxChartModel {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} (hQ : CxInt.IsCxVar Q e) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ) :
    zeroSet (setChartIdeal (conePts Q) σ Ψ) = setChartSet (conePts Q) σ Ψ ∧
      ∀ J ∈ (setChartIdeal (conePts Q) σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) ∧ IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  obtain ⟨hK, ⟨hQp, hQh, -⟩, hdimQ⟩ := hQ
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQh
  refine ⟨chart_zeroSet hR σ Ψ, fun J hJ => ?_⟩
  have hdim := chart_dim hQp hR hdimQ σ Ψ hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := cone_pow_mem hR hΨ hJ.1.2 a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨hdim, ⟨FiniteProjHomInjective.proof m e J _ hJ.1.1 hdim hfin, hfin⟩⟩

end Rel

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionOfPotentialOnModel
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem isCompatChart_atlas {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) (j : Fin A.n) :
    IsCompatChart A (A.chart j) :=
  fun k => ⟨A.holo k j, A.holo j k⟩

theorem potential_pos_of_section :
    ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D) (Φ : LocPot M.Xc), IsPotential M.atlas Φ → (∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (D.A'.h z)) (s y') = (G y').re) → IsPosPot M.atlas Φ := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D M Φ hΦ hloc x j y hy v hv
  classical
  set e := M.atlas.chart j with he
  have hcompat : IsCompatChart M.atlas e := isCompatChart_atlas M.atlas j
  have hsrc : e.symm y ∈ e.source := e.map_target hy.1
  obtain ⟨U, hUo, hyU, hUsub, s, hs, hsh, G, hG, hrel⟩ := hloc x (e.symm y) ⟨hy.2, trivial⟩
  set V : Set (Fin D.n → ℂ) := e.target ∩ e.symm ⁻¹' U with hV
  have hVo : IsOpen V := e.isOpen_inter_preimage_symm hUo
  have hyV : y ∈ V := ⟨hy.1, hyU⟩
  have hVn : V ∈ 𝓝 y := hVo.mem_nhds hyV
  set τ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (e.symm u) with hτdef
  have hτ : AnalyticOnNhd ℂ τ V := fun u hu => analyticAt_pi_iff.2 fun p => hsh p j u hu
  have hg : AnalyticAt ℂ (G ∘ e.symm) y := hG j y hyV
  have hτmem : ∀ u ∈ V, τ u ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (τ u) = e.symm u := fun u hu => hs _ hu.2
  have hz : τ y ∈ mcPts (mCoordIdeal D.y) := (hτmem y hyV).1
  have hpz : M.proj (τ y) = e.symm y := (hτmem y hyV).2
  have hτy : AnalyticAt ℂ τ y := hτ y hyV
  set w := fderiv ℂ τ y v with hwdef

  set L : ℂ → Fin D.n → ℂ := fun σ => y + σ • v with hL
  have hLd : HasDerivAt L v 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    simp only [id, one_smul] at h
    exact h
  have hL0 : L 0 = y := by simp [hL]
  have hLn : ∀ᶠ σ in 𝓝 (0 : ℂ), L σ ∈ V :=
    hLd.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hVn)
  set γ : ℂ → (Σ k, ι k) → ℂ := fun σ => τ (L σ) with hγdef
  have hγ0 : γ 0 = τ y := by simp [hγdef, hL0]
  have hγw : HasDerivAt γ w 0 :=
    (hτy.differentiableAt.hasFDerivAt).comp_hasDerivAt_of_eq (0 : ℂ) hLd hL0.symm

  have htan : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) (τ y) w := by
    intro f hf
    have hder := hasDerivAt_eval_comp (map (Int.castRingHom ℂ) f) hγw
    rw [hγ0] at hder
    have hzero : (fun σ => eval (γ σ) (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hLn] with σ hσ
      exact (hτmem _ hσ).1.2 f hf
    exact hder.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero)

  have hnt : ∀ c : K → ℂ, w ≠ torusSmul c (τ y) := by
    intro c hwc
    obtain ⟨W, hWo, hzW, F, hFd, hF⟩ :=
      projHoloLocal II Ψ K ι Ω E D M e hcompat (τ y) hz (by rw [hpz]; exact hsrc)
    have hFz : HasFDerivAt F (fderiv ℂ F (τ y)) (τ y) :=
      (hFd.differentiableAt (hWo.mem_nhds hzW)).hasFDerivAt
    have hFγ : HasFDerivAt F (fderiv ℂ F (τ y)) (γ 0) := hγ0 ▸ hFz
    have hWγ : ∀ᶠ σ in 𝓝 (0 : ℂ), γ σ ∈ W :=
      hγw.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hγ0 ▸ hzW))
    have h1 : fderiv ℂ F (τ y) w = v := by
      refine (hFγ.comp_hasDerivAt (0 : ℂ) hγw).unique (hLd.congr_of_eventuallyEq ?_)
      filter_upwards [hLn, hWγ] with σ hσ hσW
      rw [Function.comp_apply, ← (hF (γ σ) ⟨hσW, (hτmem _ hσ).1⟩).2, (hτmem _ hσ).2, e.right_inv hσ.1]
    set δ : ℂ → (Σ k, ι k) → ℂ := fun σ => torusSmul (fun k => Complex.exp (σ * c k)) (τ y) with hδ
    have hδ0 : δ 0 = τ y := by
      funext p
      simp [hδ, torusSmul]
    have hδd : HasDerivAt δ (torusSmul c (τ y)) 0 := by
      refine hasDerivAt_pi.2 fun p => ?_
      have h := (((hasDerivAt_id (0 : ℂ)).mul_const (c p.1)).cexp).mul_const (τ y p)
      simpa [hδ, torusSmul] using h
    have hδmem : ∀ σ, δ σ ∈ mcPts (mCoordIdeal D.y) := fun σ =>
      ComponentDataEquivalence.mcPts_torus D.arith.2.1.2.1 hz fun k => Complex.exp_ne_zero _
    have hδproj : ∀ σ, M.proj (δ σ) = M.proj (τ y) := fun σ =>
      ((M.fibre (τ y) hz (δ σ) (hδmem σ)).2 ⟨_, fun k => Complex.exp_ne_zero _, rfl⟩).symm
    have hWδ : ∀ᶠ σ in 𝓝 (0 : ℂ), δ σ ∈ W :=
      hδd.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hδ0 ▸ hzW))
    have h2 : fderiv ℂ F (τ y) (torusSmul c (τ y)) = 0 := by
      have hFz' : HasFDerivAt F (fderiv ℂ F (τ y)) (δ 0) := hδ0 ▸ hFz
      refine (hFz'.comp_hasDerivAt (0 : ℂ) hδd).unique
        ((hasDerivAt_const (0 : ℂ) (e (M.proj (τ y)))).congr_of_eventuallyEq ?_)
      filter_upwards [hWδ] with σ hσW
      rw [Function.comp_apply, ← (hF (δ σ) ⟨hσW, hδmem σ⟩).2, hδproj σ]
    exact hv (h1.symm.trans (hwc ▸ h2))

  have hO : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (τ y) :=
    MuRegSmooth.isOpen_blocks.mem_nhds hz.1
  have hlogA : ContDiffAt ℝ 2 (fun z => Real.log (D.A'.h z)) (τ y) :=
    ((D.A'_pos.1.contDiffAt hO).of_le (WithTop.coe_le_coe.2 le_top)).log (D.A'.pos _ hz.1).ne'
  have hc1 : ContDiffAt ℝ 2 ((fun z => Real.log (D.A'.h z)) ∘ τ) y :=
    hlogA.comp y (hτy.restrictScalars.contDiffAt (n := 2))
  have hc2 : ContDiffAt ℝ 2 (fun u => ((G ∘ e.symm) u).re) y := by
    have h := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y
      (hg.restrictScalars.contDiffAt (n := 2))
    simpa only [Function.comp_def, Complex.reCLM_apply] using h
  have hev : (Φ.φ x ∘ e.symm) =ᶠ[𝓝 y]
      fun u => ((fun z => Real.log (D.A'.h z)) ∘ τ) u + (1 : ℝ) * ((G ∘ e.symm) u).re := by
    filter_upwards [hVn] with u hu
    have := hrel _ hu.2
    simp only [Function.comp_apply, one_mul, hτdef]
    linarith
  have hpos := D.A'_pos.2 (τ y) hz w htan hnt
  rw [levi_congr hev, levi_add_smul 1 hc1 hc2, levi_re_analytic hg, levi_comp v hτy hlogA]
  rw [mul_zero, add_zero]
  exact hpos

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

