module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompOfIsTraceClass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLineTriple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

open GlobalTheory.WeilM

namespace GlobalTheory.ArchLineCont

theorem continuous_apply : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    ∀ (f : SInf F (Fin a × Fin (a + a'))) (x : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F), Continuous fun t => T t f x := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ T hAct f x
  classical
  let κ := Fin a × Fin (a + a')
  let g₀ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1
  have hg₀ : g₀ ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  let r₀ : (κ → AF F) → ℂ := fun y => g₀ (fun i => (y i).2)
  have htens : ∀ h : SInf F κ, tens (evI F) (⇑h) r₀ = pureA F (⇑h) g₀ := fun h => rfl
  have hRest : ∀ h : SInf F κ, Rest (evI F) (⇑h) r₀ := by
    intro h
    refine ⟨fun y z hz => ?_, ?_⟩
    · have h2 : ∀ i, (z i).2 = 0 := by
        intro i
        have hu := hz ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) (by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _)
        have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun hu i)
        rwa [one_mul] at h1
      show g₀ (fun i => (y i + z i).2) = g₀ (fun i => (y i).2)
      congr 1
      funext i
      show (y i).2 + (z i).2 = (y i).2
      rw [h2 i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨h, g₀, hg₀, rfl⟩
  let xh : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), (0 : FiniteAdeleRing (𝓞 F) F))
  let l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj xh
  have hxh : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (xh i).1) = x := by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i)
  have hg0 : g₀ (fun i => (xh i).2) = 1 := by
    have hm : (fun i => (xh i).2) ∈ GlobalTheory.SchANonzero.intPts F κ := fun i _ v => by
      show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
      exact zero_mem (v.adicCompletionIntegers F)
    simp only [g₀, Set.indicator_of_mem hm, Pi.one_apply]
  have hl : l ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨g (fun i => (xh i).2) • ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun h => ?_⟩
    show pureA F (⇑h) g xh = _
    simp only [pureA, hxh, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
    exact mul_comm _ _
  have hφ : pureA F (⇑f) g₀ ∈ (adeleClass F).sp κ := Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩
  have hc := hT.weil.2.2 l hl _ hφ
  have key : (fun t : ℝ => T t f x) =
      (fun p => l (om p (pureA F (⇑f) g₀))) ∘ (fun t : ℝ => ((1 : UA σ G.V.J), γ (Multiplicative.ofAdd t))) := by
    funext t
    have e := hAct t f r₀ (hRest f)
    rw [htens, htens] at e
    simp only [Function.comp_apply]
    rw [e]
    show _ = pureA F _ g₀ xh
    simp only [pureA, hxh, hg0, mul_one]
  rw [key]
  exact hc.comp (continuous_const.prodMk (hγ.1.comp continuous_ofAdd))

end GlobalTheory.ArchLineCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgHasType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

variable {n : ℕ}

theorem mul_inv_mem_UH {G G₀ A B : Mx n} (hB : IsUnit B) (hA : Aᴴ * G * A = G₀) (hB' : Bᴴ * G * B = G₀) :
    A * B⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have h := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hB)
  show (A * B⁻¹)ᴴ * G * (A * B⁻¹) = G
  calc (A * B⁻¹)ᴴ * G * (A * B⁻¹) = (B⁻¹)ᴴ * (Aᴴ * G * A) * B⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by rw [hA, ← hB']; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h]; simp

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}

def uIso (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) : H ≃ₗᵢ[ℂ] H :=
  { toFun := σ a
    invFun := σ b
    map_add' := map_add _
    map_smul' := map_smul _
    left_inv := fun w => by
      show σ b (σ a w) = w
      rw [← sigma_mul hσ hb ha, hba, sigma_one hσ]
    right_inv := fun w => by
      show σ a (σ b w) = w
      rw [← sigma_mul hσ ha hb, hab, sigma_one hσ]
    norm_map' := hσ.2.1 a ha }

theorem uIso_apply (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) (w : H) : uIso hσ ha hb hab hba w = σ a w := rfl

end GlobalTheory.KFinCuspAvgType

end

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

end GlobalTheory.KFinCuspAvgType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOperatorsVanishingRadicalIntegralsUnitary
section
noncomputable section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

namespace GlobalTheory.CuspidalOpAssembly

section Compress

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem trace_comp_comp_of_comp_eq_id (S : K →L[ℂ] H) (P : H →L[ℂ] K) (hPS : ∀ y, P (S y) = y)
    {T : K →L[ℂ] K} (hT : IsTraceClass T) : trace (S ∘L T ∘L P) = trace T := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := hT
  have e : S ∘L (∑ i, B i ∘L C i) ∘L P = ∑ i, (S ∘L B i) ∘L (C i ∘L P) := by
    ext x; simp
  have t : ∀ i, trace ((S ∘L B i) ∘L (C i ∘L P)) = trace (B i ∘L C i) := fun i => by
    rw [trace_comp_comm ((hB i).comp_left S) ((hC i).comp_right P), trace_comp_comm (hB i) (hC i)]
    congr 1
    ext x; simp [hPS]
  have h1 : HasSum (fun j => ⟪stdBasis (H := H) j, (S ∘L (∑ i, B i ∘L C i) ∘L P) (stdBasis (H := H) j)⟫_ℂ)
      (∑ i, trace (B i ∘L C i)) := by
    rw [e]
    simpa only [ContinuousLinearMap.sum_apply, inner_sum, t] using
      hasSum_sum fun i (_ : i ∈ Finset.univ) =>
        hasSum_trace_comp (stdBasis (H := H)) ((hB i).comp_left S) ((hC i).comp_right P)
  have h2 : HasSum (fun j => ⟪stdBasis (H := K) j, (∑ i, B i ∘L C i) (stdBasis (H := K) j)⟫_ℂ) (∑ i, trace (B i ∘L C i)) := by
    simpa only [ContinuousLinearMap.sum_apply, inner_sum] using
      hasSum_sum fun i (_ : i ∈ Finset.univ) => hasSum_trace_comp (stdBasis (H := K)) (hB i) (hC i)
  exact h1.tsum_eq.trans h2.tsum_eq.symm

end Compress

theorem cuspidalOperators : GlobalTheory.Published.CuspTraceClass → ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant], CuspidalOperators V μ := by
  intro hCT D V μ _ _ f hf h1 h2
  have c := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have m1 : GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition.MapsIntoCusp V μ f := _root_.GlobalTheory.RopCusp.ropG_mem_L2cusp D V μ f hf h1
  have m2 : GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition.MapsIntoCusp V μ (starFn f) :=
    _root_.GlobalTheory.RopCusp.ropG_mem_L2cusp D V μ (starFn f) (GlobalTheory.Orb.starFn_mem_ccAd hf) h2
  have hd := GlobalTheory.CuspSpectrum.traceIsDiagonal (μ := μ) hCT hf m2
  have hk := fun (F : DividedPowerChartLift V μ) (x : GA D V) =>
    GlobalTheory.AutomorphicL2KernelIntegral.convR_eq_integral_kernelQ (GA D V) (GQ V) μ f c.1 c.2 F x
  obtain ⟨t1, t2, t3⟩ := _root_.GlobalTheory.CuspTraceSum.hasSum_mCusp_repTrace hCT D V μ f hf
  have etr : trace (RopG V μ f) = trace (RcuspOp V μ f) := by
    rw [GlobalTheory.TraceDiagonal.RopG_eq_comp c.1 c.2 m2]
    exact trace_comp_comp_of_comp_eq_id _ _
      (fun y => Submodule.orthogonalProjection_mem_subspace_eq_self y) (hCT D V μ f hf)
  refine ⟨m1, fun F hF => ?_, hd.1, fun F p => ?_, fun F => ?_, hd.2.1, hd.2.2, fun c' => ?_, t1, t2, etr ▸ t3⟩
  · rw [GlobalTheory.TraceDiagonal.RopG_eq_comp c.1 c.2 m2]
    simp [Submodule.orthogonalProjection_eq_zero_iff.2 hF]
  · induction p using Quotient.inductionOn with
    | h x => exact (hk F x).1
  · refine ae_quotMeasure_iff.2 ?_
    filter_upwards [(AutomorphicL2Pointwise.lift_Rop_eq_convR (GA D V) (GQ V) μ f
      (c.1.integrable_of_hasCompactSupport c.2) F).2] with x hx
    exact hx.trans (hk F x).2
  · exact GlobalTheory.CuspSpectrum.multIn_L2cusp_lt (GlobalTheory.Published.cuspDiscreteDecomposition_of_traceClass hCT D V μ) c'.rep.isIrr

end GlobalTheory.CuspidalOpAssembly

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DSGapData

theorem two_mul_rkR_le {n : ℕ} (ε : Fin n → Bool) : 2 * GlobalTheory.Count.rkR ε ≤ n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  delta GlobalTheory.Count.rkR
  omega

theorem rank_bound (n q : ℕ) (hq : 2 * q ≤ n) :
    120 * (n : ℝ) * ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (n : ℝ) ^ 4 := by
  rcases Nat.eq_zero_or_pos q with h0 | h0
  · subst h0
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero]
    positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h0
  have hq2 : (2 : ℝ) * q ≤ n := by exact_mod_cast hq
  have hn : (2 : ℝ) ≤ n := by linarith
  have e : ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hq1 (show (3 : ℝ) / 2 ≤ 2 by norm_num)
    simpa using this
  have h1 : 4 * (q : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have h2 : 120 * (n : ℝ) * ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (n : ℝ) * (q : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ 120 * n := by positivity
    exact mul_le_mul_of_nonneg_left e this
  have h3 : 120 * (n : ℝ) * (q : ℝ) ^ 2 ≤ 30 * (n : ℝ) ^ 3 := by nlinarith
  have h4 : 30 * (n : ℝ) ^ 3 ≤ 100 * (n : ℝ) ^ 4 := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ n by linarith) 3]
  linarith

theorem big_bound (n q : ℕ) (hq : 2 * q ≤ n) :
    40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ 100 * (n : ℝ) ^ 4 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    have : q = 0 := by omega
    subst this; simp
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h0
  have hqn : (q : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : q ≤ n ^ 2 := by nlinarith
    exact_mod_cast this
  have hs : Real.sqrt q ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, hqn⟩
  have h1 : 40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ 40 * (n : ℝ) ^ 2 * n :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h2 : 40 * (n : ℝ) ^ 2 * n ≤ 100 * (n : ℝ) ^ 4 := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ n by linarith) 3]
  linarith

theorem gap_numeric' {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    GlobalTheory.Count.rkR ε = 0 ∨ 8 * Real.sqrt (GlobalTheory.Count.rkR ε) * (0 + 4 * n * GlobalTheory.Count.rkR ε) < h := by
  rcases Nat.eq_zero_or_pos (GlobalTheory.Count.rkR ε) with h0 | h0
  · exact Or.inl h0
  right
  have hq : (0 : ℝ) < GlobalTheory.Count.rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by
    have := two_mul_rkR_le ε
    exact_mod_cast (show 0 < n by omega)
  have e : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) = Real.sqrt (GlobalTheory.Count.rkR ε) * GlobalTheory.Count.rkR ε := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hq.ne']
    norm_num
  rw [e] at hh
  have hp : 0 < (n : ℝ) * (Real.sqrt (GlobalTheory.Count.rkR ε) * GlobalTheory.Count.rkR ε) := by positivity
  nlinarith

theorem lamAt_gap {D : D7} (hH : HostHyp D) (τ : D.what₂.Tau) (i : ℕ) :
    ∀ j, i < j → j < D.R.r →
      100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) i - Formalism.L2.NTheta.lamAt (D.hc τ) j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro hij hj
    have g := hH.gapR τ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · have := ih h (by omega)
      have h0 : (0 : ℚ) ≤ 100 * (D.R.r : ℚ) ^ 4 := by positivity
      linarith
    · subst h; exact g

theorem isHCParam_cast {n m : ℕ} (h : n = m) (lam : Fin m → ℝ) (hl : Formalism.QuantumDeterminants.IsHCParam lam) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin n => lam (Fin.cast h i)) := by
  subst h; simpa using hl

theorem dsData_gap_integrable : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D), HostHyp D → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  intro D X hH
  have hn : (X.B.I.n : ℝ) = (D.R.r : ℝ) := by exact_mod_cast X.n_eq

  have hds : GlobalTheory.Count.IsDSData X.B X.dv := by
    intro v
    have e : X.B.lam v = fun i => Formalism.MainNotions.S.lamS D.R (D.hc (X.pl v)) (Fin.cast X.n_eq i) := funext (X.lam_eq v)
    refine ⟨?_, X.ds v, X.low v, ?_⟩
    · rw [e]
      exact isHCParam_cast X.n_eq _ (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc (X.pl v)))
    · obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ (X.ds v) 1 one_pos
      rw [ENNReal.coe_one, one_smul] at hd
      have hw : X.B.w v ≠ 0 := by
        intro h0
        have h1 := (X.low v).1
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      have e2 : X.dv v = d := Formalism.L2.SG.Pf.RowDictPf.fdegOf_eq hd hw
      rw [e2]
      exact hd

  have hgap : GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
    intro v a b hab
    have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (by rw [Fin.ext h])
    have hlam (i : Fin X.B.I.n) :
        X.B.lam v i = (Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) i : ℝ) := by
      rw [X.lam_eq]
      delta Formalism.MainNotions.S.lamS Formalism.L2.NTheta.lamAt
      simp only [Fin.val_cast]
      split_ifs <;> simp
    rw [hlam a, hlam b]
    rcases lt_or_gt_of_ne hne with h | h
    · have g := lamAt_gap hH (X.pl v) a b h (by have := b.2; have := X.n_eq; omega)
      have g' : (100 * (D.R.r : ℝ) ^ 4) ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) a : ℚ) : ℝ) -
          ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) b : ℚ) : ℝ) := by exact_mod_cast g
      exact le_abs.2 (Or.inl g')
    · have g := lamAt_gap hH (X.pl v) b a h (by have := a.2; have := X.n_eq; omega)
      have g' : (100 * (D.R.r : ℝ) ^ 4) ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) b : ℚ) : ℝ) -
          ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) a : ℚ) : ℝ) := by exact_mod_cast g
      exact le_abs.2 (Or.inr (by linarith))

  have hh : ∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      100 * (D.R.r : ℝ) ^ 4 := by
    intro v
    rw [← hn]
    exact rank_bound _ _ (two_mul_rkR_le _)
  have hbig : GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) := by
    intro v
    rw [← hn]
    exact big_bound _ _ (two_mul_rkR_le _)

  have hD := GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hloc : GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) :=
    GlobalTheory.Dec.locDec_of_decGap_gapGe hD X.B X.dv _ hds hgap hh
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj X.B X.dv _ hds hloc
  have hI := hint 0 le_rfl fun v => gap_numeric' _ _ (hh v)
  have hph : Integrable (GlobalTheory.Count.ph X.B X.dv) (GlobalTheory.Dec.muInf X.B.I) := by
    refine hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    simpa using hle g
  have hph' : Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) := hph
  exact ⟨hds, hloc, hbig, hh, hph', GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X hph'⟩

end GlobalTheory.DSGapData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulOfStableGraph
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem eq_smul_of_stable_graph : ∀ (D : D7) (X : HSp D) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi), IsIrred X Pi rf rl → Module.rank ℂ Pi ≤ Cardinal.aleph0 → ∀ S : Submodule ℂ (Pi × Pi), (∀ g ∈ GfC X, ∀ x ∈ S, (rf g x.1, rf g x.2) ∈ S) → (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, (rl τ Y x.1, rl τ Y x.2) ∈ S) → (∀ x : Pi, ((x, 0) : Pi × Pi) ∈ S → x = 0) → (∀ y : Pi, ((0, y) : Pi × Pi) ∈ S → y = 0) → (∀ x : Pi, ∃ y : Pi, ((x, y) : Pi × Pi) ∈ S) → ∃ c : ℂ, c ≠ 0 ∧ ∀ x y : Pi, ((x, y) : Pi × Pi) ∈ S → y = c • x := by
  intro D X Pi rf rl hirr hrank S hf hl h1 h2 hon
  classical
  haveI : Nontrivial Pi := hirr.1
  choose t ht using hon
  have huniq : ∀ x y, ((x, y) : Pi × Pi) ∈ S → t x = y := by
    intro x y hxy
    have h0 : (((0 : Pi), t x - y) : Pi × Pi) ∈ S := by
      have := S.sub_mem (ht x) hxy
      simpa using this
    exact sub_eq_zero.1 (h2 _ h0)
  let T : Module.End ℂ Pi :=
    { toFun := t
      map_add' := fun a b => huniq _ _ (by simpa using S.add_mem (ht a) (ht b))
      map_smul' := fun r a => by
        simp only [RingHom.id_apply]
        exact huniq _ _ (by simpa using S.smul_mem r (ht a)) }
  have hTf : ∀ g ∈ GfC X, ∀ x, T (rf g x) = rf g (T x) := fun g hg x => huniq _ _ (hf g hg _ (ht x))
  have hTl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x, T (rl τ Y x) = rl τ Y (T x) := fun τ Y hY x => huniq _ _ (hl τ Y hY _ (ht x))
  obtain ⟨c, hc⟩ := GlobalTheory.LocGL.exists_not_isUnit_sub hrank T
  set A := T - algebraMap ℂ (Module.End ℂ Pi) c with hA
  have hAx : ∀ x, A x = T x - c • x := fun x => by simp [hA]
  have hAf : ∀ g ∈ GfC X, ∀ x, A (rf g x) = rf g (A x) := by
    intro g hg x; rw [hAx, hAx, hTf g hg, map_sub, map_smul]
  have hAl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x, A (rl τ Y x) = rl τ Y (A x) := by
    intro τ Y hY x; rw [hAx, hAx, hTl τ Y hY, map_sub, map_smul]
  have hA0 : A = 0 := by
    rcases hirr.2 (LinearMap.ker A)
        (fun g hg x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hAf g hg, hx, map_zero])
        (fun τ Y hY x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hAl τ Y hY, hx, map_zero]) with hk | hk
    · rcases hirr.2 (LinearMap.range A)
          (fun g hg x hx => by obtain ⟨z, rfl⟩ := hx; exact ⟨rf g z, hAf g hg z⟩)
          (fun τ Y hY x hx => by obtain ⟨z, rfl⟩ := hx; exact ⟨rl τ Y z, hAl τ Y hY z⟩) with hr | hr
      · exact LinearMap.range_eq_bot.1 hr
      · exact absurd ((Module.End.isUnit_iff _).2 ⟨LinearMap.ker_eq_bot.1 hk, LinearMap.range_eq_top.1 hr⟩) hc
    · exact LinearMap.ker_eq_top.1 hk
  have hTc : ∀ x, t x = c • x := fun x => by
    have := congrArg (fun f : Module.End ℂ Pi => f x) hA0
    simp only [hAx, LinearMap.zero_apply] at this
    exact sub_eq_zero.1 this
  refine ⟨c, ?_, fun x y hxy => by rw [← huniq x y hxy, hTc]⟩
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : Pi)
  exact hx (h1 x (by simpa [hTc] using ht x))

end GlobalTheory.SquareAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLineStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f (D f) := by
  first | exact @GlobalTheory.HeisDeriv.exists_actsD_heisLine | exact GlobalTheory.HeisDeriv.exists_actsD_heisLine | (intros; apply GlobalTheory.HeisDeriv.exists_actsD_heisLine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfInvariantFormIsotropicAverageNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_halfInvariantForm_isotropicAverage_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ e, IsSplitIdem D e → ∃ ℓ' : (WO V' W → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO V' W, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ V' W f → ℓ' (heisO ψ V' W u f) = ℓ' f) ∧ ∃ f, IsThetaFunO ψ V W f ∧ avgForm ψ V V' W C B μ 𝓨 K e ℓ' f ≠ 0 := by
  first | exact @GlobalTheory.HalfAverage.avgForm_ne_zero | exact GlobalTheory.HalfAverage.avgForm_ne_zero | (intros; apply GlobalTheory.HalfAverage.avgForm_ne_zero <;> assumption)
end

