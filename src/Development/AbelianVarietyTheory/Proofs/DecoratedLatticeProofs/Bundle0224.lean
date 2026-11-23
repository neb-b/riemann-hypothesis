module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0207
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeasurableSetTwistPlaceChainStepDatumMatrixSuppo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

theorem measurableSet_suppQ : ∀ (D : D7) (v : FinPl D) (a b r : ℕ),
    MeasurableSet (GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r) := by
  intro D v a b r
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv D.host.F v)
  haveI : OpensMeasurableSpace (Matrix (Fin b) (Fin a) (Fv D.host.F v)) :=
    inferInstanceAs (OpensMeasurableSpace (Fin b → Fin a → Fv D.host.F v))
  have hentry : ∀ i j, Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have htop : Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => topL r x := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    unfold topL
    by_cases h : i.val < b ∧ j.val < a
    · simp only [dif_pos h]; exact hentry _ _
    · simp only [dif_neg h]; exact continuous_const
  have hdet : Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => (topL r x).det :=
    htop.matrix_det
  have hball : IsOpen {y : Fv D.host.F v | Valued.v y < 1} := by
    simpa using Valued.isOpen_ball (Fv D.host.F v) 1
  have hsph : IsOpen {y : Fv D.host.F v | Valued.v y = 1} := by
    simpa using Valued.isOpen_sphere (Fv D.host.F v) (r := 1) one_ne_zero
  have hcb : IsOpen {y : Fv D.host.F v | Valued.v y ≤ 1} := by
    simpa using Valued.isOpen_closedBall (Fv D.host.F v) (r := 1) one_ne_zero
  have h1 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | IsUnit (topL r x).det} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | IsUnit (topL r x).det} =
        (fun x => (topL r x).det) ⁻¹' {0}ᶜ := by
      ext x; simp [isUnit_iff_ne_zero]
    rw [this]
    exact (isOpen_compl_singleton.preimage hdet).measurableSet
  have h2 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | Valued.v (topL r x).det = 1} :=
    (hsph.preimage hdet).measurableSet
  have h3 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) |
      ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} =
        ⋂ i, ⋂ j, (fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j) ⁻¹' {y | Valued.v y ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
        HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => (hcb.preimage (hentry i j)).measurableSet
  have h4 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) |
      ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
        ⋂ i, ⋂ j, {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : r ≤ i.val ∧ j.val < r
    · have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
          (fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j) ⁻¹' {y | Valued.v y < 1} := by
        ext x; simp [hij.1, hij.2]
      rw [this]
      exact (hball.preimage (hentry i j)).measurableSet
    · have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
          Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h h'
        exact absurd ⟨h, h'⟩ hij
      rw [this]
      exact MeasurableSet.univ
  have : suppQ (a := a) (b := b) v r =
      {x | IsUnit (topL r x).det} ∩ {x | Valued.v (topL r x).det = 1} ∩
        {x | ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} ∩
        {x | ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
    ext x
    simp only [suppQ, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [this]
  exact ((h1.inter h2).inter h3).inter h4

end GlobalTheory.NrmVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulStkRowsZeroDiag
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

open Matrix

variable {D : D7}

theorem Tm_mul_stackRows_gram (A : HSp D) (μ : D.host.E) :
    Tm A μ * stackRows A.gram 0 = stackRows 1 1 := by
  have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
  rw [Tm, stackRows, submatrix_mul_equiv, fromCols_mul_fromRows, Matrix.mul_zero, add_zero]
  show (stackRows A.gram⁻¹ A.gram⁻¹ * A.gram).submatrix id id = stackRows 1 1
  rw [submatrix_id_id]
  show stkRows A.gram⁻¹ A.gram⁻¹ * A.gram = stkRows 1 1
  rw [stkRows_mul, nonsing_inv_mul _ hG]

theorem mul_stkRows_zero_diag {n : ℕ} (F : Mx D (n + n) (n + n))
    (hF : ∀ i j : Fin n, F (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) =
      F (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)))
    (X : Mx D n n) :
    ∃ β : Mx D n n, F ⬝ (stkRows X 0 : Mx D (n + n) n) = stkRows β β := by
  refine ⟨(F ⬝ (stkRows X 0 : Mx D (n + n) n)).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id, ?_⟩
  ext a j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective a
  simp only [stkRows, Matrix.submatrix_apply, id, Equiv.symm_apply_apply]
  rcases s with s | s
  · simp only [Matrix.fromRows_apply_inl, Matrix.submatrix_apply, id]
  · simp only [Matrix.fromRows_apply_inr, Matrix.submatrix_apply, id, Matrix.mul_apply]
    rw [← finSumFinEquiv.sum_comp, ← finSumFinEquiv.sum_comp]
    simp only [Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hF]

theorem exists_siegel_mul_Tm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ Fr : GL (Fin (A.rank + A.rank)) (AE D), adj Fr.1 * gA (dblSp A) * Fr.1 = incA D μ • rat (Jst D A.rank) → (∀ i j : Fin A.rank, Fr.1 (finSumFinEquiv (Sum.inr i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank)) = Fr.1 (finSumFinEquiv (Sum.inl i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank))) → ∃ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = Fr.1 := by
  intro D A μ hμ Fr hFr hdiag
  obtain ⟨hgram, hdet, -⟩ := _root_.GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  have hTT : Tm A μ * (Tm A μ)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hTT' : (Tm A μ)⁻¹ * Tm A μ = 1 := nonsing_inv_mul _ hdet
  have hU : adj (Fr.1 * rat (Tm A μ)⁻¹) * (gA (dblSp A) * (Fr.1 * rat (Tm A μ)⁻¹)) = gA (dblSp A) := by
    have h1 : rat ((Tm A μ)⁻¹ᴴ * ((Tm A μ)ᴴ * (dblSp A).gram * Tm A μ) * (Tm A μ)⁻¹) = rat (dblSp A).gram := by
      congr 1
      rw [show (Tm A μ)⁻¹ᴴ * ((Tm A μ)ᴴ * (dblSp A).gram * Tm A μ) * (Tm A μ)⁻¹ =
          (Tm A μ * (Tm A μ)⁻¹)ᴴ * (dblSp A).gram * (Tm A μ * (Tm A μ)⁻¹) by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc], hTT, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rw [hgram, rat_mul, rat_mul, rat_smul, ← hFr, rat_conjTranspose,
      show rat (dblSp A).gram = gA (dblSp A) from rfl] at h1
    rw [adj_mul]
    simp only [Matrix.mul_assoc] at h1 ⊢
    exact h1
  have hS : (Fr.1 * rat (Tm A μ)⁻¹ : Mx D (A.rank + A.rank) (A.rank + A.rank)) ⬝
      (stkRows 1 1 : Mx D (A.rank + A.rank) A.rank) = Fr.1 ⬝ (stkRows (gA A) 0 : Mx D (A.rank + A.rank) A.rank) := by
    rw [show (stkRows 1 1 : Mx D (A.rank + A.rank) A.rank) = rat (stackRows 1 1) by rw [rat_stackRows, rat_one],
      ← Tm_mul_stackRows_gram A μ, rat_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (rat (Tm A μ)⁻¹), ← rat_mul, hTT',
      rat_one, Matrix.one_mul, rat_stackRows, rat_zero]
    rfl
  obtain ⟨β, hβ⟩ := mul_stkRows_zero_diag Fr.1 hdiag (gA A)
  refine ⟨⟨ofMat (dblSp A) _ hU, mem_siegelOf.2 (keepsDiag_of_mul_stkRows_one (β := β) (hS.trans hβ))⟩, ?_⟩
  show (Fr.1 * rat (Tm A μ)⁻¹) * rat (Tm A μ) = Fr.1
  rw [Matrix.mul_assoc, ← rat_mul, hTT', rat_one, Matrix.mul_one]

end GlobalTheory.StdUnn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralFinitelyManyCellsWeightedSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CellInt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

def dcos (R K : Subgroup G) (q : G) : Set G := {g | ∃ r ∈ R, ∃ k ∈ K, g = r * q * k}

theorem dcos_eq_of_mem {R K : Subgroup G} {q h : G} (hh : h ∈ dcos R K q) : dcos R K h = dcos R K q := by
  obtain ⟨r, hr, k, hk, rfl⟩ := hh
  ext g
  constructor
  · rintro ⟨r', hr', k', hk', rfl⟩
    exact ⟨r' * r, R.mul_mem hr' hr, k * k', K.mul_mem hk hk', by group⟩
  · rintro ⟨r', hr', k', hk', rfl⟩
    exact ⟨r' * r⁻¹, R.mul_mem hr' (R.inv_mem hr), k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', by group⟩

def cellSet (R K : Subgroup G) (q h : G) : Set R := {r | q⁻¹ * ((r : G) * h) ∈ K}

theorem isOpen_cellSet {R K : Subgroup G} (hK : IsOpen (K : Set G)) (q h : G) : IsOpen (cellSet R K q h) :=
  (continuous_const.mul (continuous_subtype_val.mul continuous_const)).isOpen_preimage _ hK

theorem isCompact_cellSet {R K : Subgroup G} (hR : IsClosed (R : Set G)) (hK : IsCompact (K : Set G)) (q h : G) :
    IsCompact (cellSet R K q h) := by
  have h1 : IsCompact ((fun x : G => q⁻¹ * (x * h)) ⁻¹' (K : Set G)) :=
    ((Homeomorph.mulRight h).trans (Homeomorph.mulLeft q⁻¹)).isCompact_preimage.2 hK
  exact hR.isClosedEmbedding_subtypeVal.isCompact_preimage h1

theorem cellSet_of_mem {R K : Subgroup G} {q h : G} (r0 : R) (k0 : G) (hk0 : k0 ∈ K) (hh : h = r0 * q * k0) :
    cellSet R K q h = (fun r => r * r0) ⁻¹' cellSet R K q q := by
  ext r
  simp only [cellSet, Set.mem_preimage, Set.mem_setOf_eq, Subgroup.coe_mul, hh]
  constructor
  · intro hr
    have := K.mul_mem hr (K.inv_mem hk0)
    convert this using 1; group
  · intro hr
    have := K.mul_mem hr hk0
    convert this using 1; group

theorem cellSet_eq_empty {R K : Subgroup G} {q h : G} (hh : h ∉ dcos R K q) : cellSet R K q h = ∅ :=
  Set.eq_empty_of_forall_notMem fun r hr =>
    hh ⟨(r : G)⁻¹, R.inv_mem r.2, q⁻¹ * ((r : G) * h), hr, by group⟩


open Classical in
theorem isQuotientIntegral_indicator_doubleCoset (R K : Subgroup G) (hR : IsClosed (R : Set G)) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (ρ : Measure R) (μ : Measure G) [ρ.IsHaarMeasure] [ρ.IsInvInvariant]
    [μ.IsHaarMeasure] (q : G) :
    IsQuotIntL1 ρ μ (fun g => if g ∈ dcos R K q then 1 else 0)
      (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ) := by
  classical
  have hRI : ρ.IsMulRightInvariant := by rw [← Measure.inv_eq_self ρ]; infer_instance
  set c : ℂ := ((((ρ (cellSet R K q q)).toReal)⁻¹ : ℝ) : ℂ) with hc
  set A : Set G := (fun x => q⁻¹ * x) ⁻¹' (K : Set G) with hA
  have hAo : IsOpen A := (continuous_const.mul continuous_id).isOpen_preimage _ hKo
  have hAc : IsCompact A := (Homeomorph.mulLeft q⁻¹).isCompact_preimage.2 hKc
  have hAμ : μ A = μ K := measure_preimage_mul μ q⁻¹ _
  have hS0 : ρ (cellSet R K q q) ≠ 0 := (isOpen_cellSet hKo q q).measure_ne_zero ρ ⟨1, by simp [cellSet]⟩
  have hSt : ρ (cellSet R K q q) ≠ ⊤ := ((isCompact_cellSet hR hKc q q).measure_lt_top (μ := ρ)).ne
  have e : ∀ h, (fun r : R => A.indicator (fun _ => c) ((r : G) * h)) = (cellSet R K q h).indicator fun _ => c := by
    intro h; funext r; simp only [Set.indicator_apply, hA, cellSet, Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe]
  refine ⟨A.indicator fun _ => c, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrableOn_const hAc.measure_lt_top.ne).integrable_indicator hAo.measurableSet
  · rw [e h]
    exact (integrableOn_const ((isCompact_cellSet hR hKc q h).measure_lt_top (μ := ρ)).ne).integrable_indicator
      (isOpen_cellSet hKo q h).measurableSet
  · rw [e h, integral_indicator (isOpen_cellSet hKo q h).measurableSet, setIntegral_const]
    show (if h ∈ dcos R K q then (1 : ℂ) else 0) = ρ.real (cellSet R K q h) • c
    by_cases hh : h ∈ dcos R K q
    · rw [if_pos hh]
      obtain ⟨r0, hr0, k0, hk0, rfl⟩ := hh
      rw [cellSet_of_mem ⟨r0, hr0⟩ k0 hk0 rfl, measureReal_def, measure_preimage_mul_right, hc, Complex.real_smul,
        ← Complex.ofReal_mul, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hS0, hSt⟩), Complex.ofReal_one]
    · rw [if_neg hh, cellSet_eq_empty hh]
      simp
  · rw [integral_indicator hAo.measurableSet, setIntegral_const, measureReal_def, hAμ, hc, Complex.real_smul, ← Complex.ofReal_mul, div_eq_mul_inv]

theorem quotient_integral_finset_sum {R : Subgroup G} {ρ : Measure R} {μ : Measure G} {ι : Type} (s : Finset ι)
    (g : ι → G → ℂ) (z : ι → ℂ) (hs : ∀ i ∈ s, IsQuotIntL1 ρ μ (g i) (z i)) :
    IsQuotIntL1 ρ μ (fun h => ∑ i ∈ s, g i h) (∑ i ∈ s, z i) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun h => ∑ i ∈ (∅ : Finset ι), g i h) = 0 := by funext h; simp
    rw [e, Finset.sum_empty]
    exact IsQuotIntL1.zero
  · intro a s ha ih hs
    have := (hs a (Finset.mem_insert_self a s)).add (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha]
    convert this using 1
    funext h
    simp [Finset.sum_insert ha]

end GlobalTheory.CellInt


open GlobalTheory.CellInt in
theorem GlobalTheory.CellInt.quotInt_finiteCells : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G), IsClosed (R : Set G) → IsCompact (K : Set G) → IsOpen (K : Set G) → ∀ (ρ : Measure R) (μ : Measure G), ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → μ.IsMulRightInvariant → ∀ T : Finset G, ∃ (T' : Finset G) (w : G → ℂ), T' ⊆ T ∧ ∀ f : G → ℂ, (∀ r ∈ R, ∀ g, f (r * g) = f g) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ g, f g ≠ 0 → ∃ q ∈ T, ∃ r ∈ R, ∃ k ∈ K, g = r * q * k) → IsQuotIntL1 ρ μ f (∑ q ∈ T', w q * f q) := by
  intro G _ _ _ _ _ _ _ _ R K hR hKc hKo ρ μ hρ hρi hμ hμr T
  classical
  obtain ⟨u, hus, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn (f := dcos R K) (T : Set G)
    (T.image (dcos R K)) (by rw [Finset.coe_image]; exact Set.surjOn_image _ _)
  refine ⟨u, fun q => (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ), Finset.coe_subset.1 hus,
    fun f hfR hfK hsupp => ?_⟩
  have hinv : ∀ q h, h ∈ dcos R K q → f h = f q := by
    rintro q h ⟨r, hr, k, hk, rfl⟩
    rw [mul_assoc, hfR r hr, hfK k hk]
  have key : ∀ h, f h = ∑ q ∈ u, f q * (if h ∈ dcos R K q then 1 else 0) := by
    intro h
    by_cases hex : ∃ q0 ∈ u, h ∈ dcos R K q0
    · obtain ⟨q0, hq0, hh⟩ := hex
      rw [Finset.sum_eq_single q0 (fun q hq hne => ?_) (fun h' => absurd hq0 h'), if_pos hh, mul_one, hinv q0 h hh]
      rw [if_neg, mul_zero]
      intro hq'
      exact hne (hinj hq hq0 ((dcos_eq_of_mem hq').symm.trans (dcos_eq_of_mem hh)))
    · rw [Finset.sum_eq_zero fun q hq => by rw [if_neg fun hh => hex ⟨q, hq, hh⟩, mul_zero]]
      by_contra hne
      obtain ⟨q, hq, r, hr, k, hk, hh⟩ := hsupp h hne
      have hm : dcos R K q ∈ u.image (dcos R K) := himg ▸ Finset.mem_image_of_mem _ hq
      obtain ⟨q', hq', he⟩ := Finset.mem_image.1 hm
      exact hex ⟨q', hq', by rw [he]; exact ⟨r, hr, k, hk, hh⟩⟩
  have hS := quotient_integral_finset_sum u (fun q h => f q * if h ∈ dcos R K q then 1 else 0)
    (fun q => (((μ (K : Set G)).toReal / (ρ (cellSet R K q q)).toReal : ℝ) : ℂ) * f q) fun q _ => by
      have := (isQuotientIntegral_indicator_doubleCoset R K hR hKc hKo ρ μ q).smul (f q)
      convert this using 1
      · ring
  convert hS using 1
  exact funext key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntertwinerValuesKFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ItKFin

theorem inclT_mapFactor {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Module.End ℂ (M.sm τ)) (A : M.H τ →ₗ[ℂ] M.H τ) (hg : ∀ w, ((g w : M.sm τ) : M.H τ) = A w) (y : SmT M) :
    inclT M (GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ g y) =
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ A) (inclT M y) := by
  rw [inclT, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
    ← PiTensorProduct.map_comp]
  congr 2
  funext ρ
  by_cases e : ρ = τ
  · subst e
    ext w
    simp [hg]
  · ext w
    simp [e]

theorem itKFin : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ P v, It P v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) := by
  intro D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt P v
  obtain ⟨χS, χT, hWD, hexp⟩ := hW
  have hp : ptOf ψ θ M M' f = ⇑(pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f) := rfl
  have hA : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∃ P' : PolF D W.rank V.rank, P'.totalDegree ≤ P.totalDegree ∧
      inclT M (It P' v) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M (It P v)) := by
    intro τ h hh
    obtain ⟨a, b, -, -, hc⟩ := GlobalTheory.CompactFockAction.compactFockAll D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ
      (aS τ) (aT τ) hθ hWD (hexp τ).1 (hexp τ).2 ⟨hf.theta, hf.vac⟩ hf.ne
    have h1 : (1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) ∈ Formalism.REAL.Kset (M'.ε τ) := ⟨one_mem _, by simp⟩
    have := hc h hh 1 h1 P
    have e1 : (Fr.ofModel M').elt θ τ 1 = 1 := by
      have hd' := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
      show atTau θ W τ ((M'.fr τ)⁻¹ * 1 * M'.fr τ) = 1
      rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hd']
      exact GlobalTheory.PointAtPlaceHom.atTau_one hθ W τ
    rw [e1, ptF_ofModel, hp, ← map_smul, ← hp] at this
    refine ⟨_, ?_, hIt.eqK τ _ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ (GlobalTheory.Chain.IoLift.frame_mem M τ hh)) P _ this.symm v⟩
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _)
  have hJ := fun τ => (Formalism.REAL.maximal_compact_facts _ (M.ε τ)).1
  have hsm : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ w ∈ M.sm τ, (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) w ∈ M.sm τ :=
    fun τ h hh w hw => (GlobalTheory.MultGelf.mem_sm M τ).2 (GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
      ((GlobalTheory.MultGelf.mem_sm M τ).1 hw) (hJ τ h hh))
  let fK : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), Module.End ℂ (M.sm τ) := fun τ h hh =>
    (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ).restrict (hsm τ h hh)
  have hconj : ∀ τ (h : Matrix (Fin V.rank) (Fin V.rank) ℂ), M.fr τ * ((M.fr τ)⁻¹ * h * M.fr τ) * (M.fr τ)⁻¹ = h :=
    fun τ h => by
      have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hact : ∀ τ h (hh : h ∈ Formalism.REAL.Kset (M.ε τ)) (y : SmT M),
      inclT M (GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ h hh) y) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M y) := by
    intro τ h hh y
    rw [inclT_mapFactor M τ _ (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) (fun w => rfl)]
    simp only [actT, DSModel.rep, hconj]
  have hx := GlobalTheory.Chain.IoLift.mem_range_map_subtype_of_contr D.what₂.Tau (fun τ => M.sm τ)
    (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).comap (M.sm τ).subtype) (It P v) fun τ L hL => by
      show IsKFin (M.ε τ) (M.σ τ) ((L (It P v) : M.sm τ) : M.H τ)
      let E : Submodule ℂ (SmT M) := (MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (It.flip v)
      have hle : Submodule.span ℂ ((fun k => M.σ τ k ((L (It P v) : M.sm τ) : M.H τ)) '' Formalism.REAL.Kset (M.ε τ)) ≤
          (E.map L).map (M.sm τ).subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨k, hk, rfl⟩
        obtain ⟨P', hP', e⟩ := hA τ k hk
        have e2 : It P' v = GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ k hk) (It P v) :=
          (tensorLaw D V S M).inj (by rw [e, hact τ k hk])
        have e3 := LinearMap.congr_fun (hL (fK τ k hk)) (It P v)
        simp only [LinearMap.comp_apply] at e3
        refine ⟨L (It P' v), ⟨It P' v, ⟨P', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP', rfl⟩, rfl⟩, ?_⟩
        rw [e2, e3]
        rfl
      have hσ := (M.ds τ).2.2.1
      refine ⟨_, Submodule.finiteDimensional_of_le hle, Submodule.subset_span ⟨1, ⟨one_mem _, by simp⟩, ?_⟩,
        fun g hg w hw => ?_⟩
      · simp only [hσ.1.1]; rfl
      · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (M.σ τ g : M.H τ →ₗ[ℂ] M.H τ) _)).2 ?_ hw)
        rintro _ ⟨k, hk', rfl⟩
        refine Submodule.subset_span ⟨g * k, Formalism.REAL.Kset_mul _ hg hk', ?_⟩
        simp only [hσ.1.2 g (hJ τ g hg) k (hJ τ k hk')]; rfl
  obtain ⟨z, hz⟩ := hx
  rw [← hz]
  clear hz
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r n =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun τ => (n τ : M.sm τ), fun τ => Submodule.subset_span (n τ).2, rfl⟩)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

end GlobalTheory.ItKFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.CentreRight

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom
open Formalism.MainNotions.StandardLattice (infMat)

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem rTr_mem_fin {u : GA D V} (hu : u ∈ GfC V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V u φ ∈ SmFun θ V := by
  intro n τs Xs hX g
  have := hφ n τs Xs hX (g * u)
  convert this using 2 with t
  unfold rTr
  rw [mul_assoc, mul_assoc, comm_of_mem V (list_prod_mem fun a ha => ?_) hu]
  obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
  exact atTau_mem V _ _

theorem rTr_mul (u a : GA D V) (φ : GA D V → ℂ) : rTr V (u * a) φ = rTr V u (rTr V a φ) := by
  funext g
  simp only [rTr, mul_assoc]

theorem decomp (hθ : IsInfFam θ) (x : GA D V) : ∃ u ∈ GfC V, ∃ a, IsRealPt θ a ∧ x = u * a := by
  obtain ⟨u, hu, a, ha, e⟩ := Formalism.IndefR.TopMult.ga_decomp x
  exact ⟨u, hu, a, ⟨ha, GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a⟩, e⟩

theorem rTr_mem_all (hθ : IsInfFam θ) (x : GA D V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V x φ ∈ SmFun θ V := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul]
  exact rTr_mem_fin hu (rTr_mem hθ ha hφ)

theorem gelf_rTr_all (hθ : IsInfFam θ) (x : GA D V) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    gelf θ V τ k (rTr V x φ) = rTr V x (gelf θ V τ k φ) := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul, rTr_mul, GlobalTheory.Mem.FinTranslate.gelf_rTr hu, gelf_rTr hθ ha τ k hφ]

end GlobalTheory.RegSch.CentreRight

end
end

