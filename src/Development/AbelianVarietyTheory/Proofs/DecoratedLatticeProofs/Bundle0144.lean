module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselQuot

theorem besGrp_quotient : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ), B.μR.IsHaarMeasure ∧ IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ (∃ Ω : Set (GA D B.V), IsCompact Ω ∧ ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) ∧ ∃ 𝓢 : Set (besGrp B.d B.o), IsFundamentalDomain ((GQ B.V).subgroupOf (besGrp B.d B.o)) 𝓢 B.μR ∧ B.μR 𝓢 < ⊤ ∧ ∀ F : GA D B.V → ℂ, ContinuousOn F (besGrp B.d B.o : Set (GA D B.V)) → (∀ γ ∈ GQ B.V ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o, F (γ * s) = F s) → IntegrableOn (fun s : besGrp B.d B.o => F s) 𝓢 B.μR ∧ ∫ s in 𝓢, F s ∂B.μR = ∫ a in B.vA.𝓕, ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν ∂B.vA.μ := by
  intro D ρ B
  obtain ⟨-, hcl, hHaar⟩ := GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L ρ B.d B.o B.vN.ν B.vN.𝓝 B.vN.unit
  have hμR : B.μR.IsHaarMeasure := hHaar B.vA.μ B.vA.haar
  obtain ⟨hsc, hNcl, hnorm, huniq, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨⟨KN, hKN, hKNcov⟩, -⟩ :=
    GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V ρ B.d.e (GlobalTheory.MixPer.isIsoSub_e B.d)
  obtain ⟨KA, hKA, hKAcov⟩ := B.cpt
  have hγA : ∀ γ ∈ GQ B.A, embA B.d B.o γ ∈ GQ B.V := fun γ hγ => by
    have h1 := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
    simpa using h1
  set Ω : Set (GA D B.V) := (fun p : GA D B.V × GA D B.A => p.1 * embA B.d B.o p.2) '' ((Subtype.val '' KN) ×ˢ KA) with hΩ
  have hΩc : IsCompact Ω :=
    ((hKN.image continuous_subtype_val).prod hKA).image (continuous_fst.mul (hsc.comp continuous_snd))
  have hΩsub : Ω ⊆ (besGrp B.d B.o : Set (GA D B.V)) := by
    rintro _ ⟨⟨_, a⟩, ⟨⟨k, hk, rfl⟩, -⟩, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right ⟨a, rfl⟩)
  have hcov : ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω := by
    intro s hs
    obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o s).1 hs
    obtain ⟨γA, hγAQ, hγAK⟩ := hKAcov a
    have hn1 : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ ∈ flagN B.d := hnorm n hn γA
    obtain ⟨γN, hγN, k, hk, he⟩ := hKNcov ⟨_, hn1⟩
    have he' : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ = γN.1 * k.1 := congrArg Subtype.val he
    have hk1 : k.1 = γN.1⁻¹ * (embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹) := eq_inv_mul_of_mul_eq he'.symm
    have hQ : γN.1⁻¹ * embA B.d B.o γA ∈ GQ B.V :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hγN)) (hγA γA hγAQ)
    have hR : γN.1⁻¹ * embA B.d B.o γA ∈ besGrp B.d B.o :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left γN.2)) (Subgroup.mem_sup_right ⟨γA, rfl⟩)
    refine ⟨γN.1⁻¹ * embA B.d B.o γA, Subgroup.mem_inf.2 ⟨hQ, hR⟩, ?_⟩
    refine ⟨(k.1, γA * a), ⟨⟨k, hk, rfl⟩, hγAK⟩, ?_⟩
    simp only [hk1, map_mul]
    group
  have hcovA : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ k ∈ KA, g = γ * k := fun g => by
    obtain ⟨γ, hγ, hk⟩ := hKAcov g
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, γ * g, hk, by group⟩
  have := B.vA.haar
  have hFfin : B.vA.μ B.vA.𝓕 < ⊤ :=
    GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ B.A) hKA hcovA B.vA.μ B.vA.fund
  have hNfin : B.vN.ν B.vN.𝓝 < ⊤ := by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top
  obtain ⟨𝓡, hfd, hint⟩ := GlobalTheory.Unf.semiFd_iterated D B.V B.A (flagN B.d) (embA B.d B.o) hsc hNcl hnorm huniq hrat B.vA
    B.vN.ν B.vN.𝓝 B.vN.unit.1 B.vN.unit.2.1 hμR
  have : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hFfin.ne
  have : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hNfin.ne
  refine ⟨hμR, hcl, ⟨Ω, hΩc, hcov⟩, 𝓡, ?_, ?_, ?_⟩
  · rw [← Subgroup.inf_subgroupOf_right]; exact hfd
  · have h1 := (hint (fun _ => (1 : ℂ)) measurable_const).1.2 (integrable_const _)
    exact ((integrableOn_const_iff).1 h1).resolve_left (by simp)
  · intro F hF hinv
    classical
    set F' : GA D B.V → ℂ := (besGrp B.d B.o : Set (GA D B.V)).piecewise F 0 with hF'
    have hF'm : Measurable F' := hF.measurable_piecewise continuousOn_const hcl.measurableSet
    obtain ⟨C, hC⟩ := hΩc.exists_bound_of_continuousOn (hF.mono hΩsub)
    have hb : ∀ x, ‖F' x‖ ≤ max C 0 := by
      intro x
      by_cases hx : x ∈ (besGrp B.d B.o : Set (GA D B.V))
      · obtain ⟨γ, hγ, hγx⟩ := hcov x hx
        rw [hF', Set.piecewise_eq_of_mem _ _ _ hx, ← hinv γ hγ x hx]
        exact (hC _ hγx).trans (le_max_left _ _)
      · rw [hF', Set.piecewise_eq_of_notMem _ _ _ hx]; simp
    have hAC : AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 fun h n => F' (n.1 * embA B.d B.o h) := by
      refine Integrable.of_bound ?_ (max C 0) (Filter.Eventually.of_forall fun p => hb _)
      exact (hF'm.comp ((continuous_subtype_val.comp continuous_snd).mul
        (hsc.comp continuous_fst)).measurable).aestronglyMeasurable
    have hpt : ∀ r : ↥(flagN B.d ⊔ (embA B.d B.o).range), F' r = F r := fun r => Set.piecewise_eq_of_mem _ _ _ r.2
    have hpt2 : ∀ a (n : flagN B.d), F' (n.1 * embA B.d B.o a) = F (n.1 * embA B.d B.o a) := fun a n =>
      Set.piecewise_eq_of_mem _ _ _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨a, rfl⟩))
    obtain ⟨hi1, hi2⟩ := hint F' hF'm
    have e1 : (fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F' r) =
        fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F r := funext hpt
    have e2 : (fun a => ∫ n in B.vN.𝓝, F' (n.1 * embA B.d B.o a) ∂B.vN.ν) =
        fun a => ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν := funext fun a => by simp only [hpt2]
    refine ⟨?_, ?_⟩
    · have h3 := hi1.2 hAC
      rw [e1] at h3
      exact h3
    · have h3 := hi2 hAC
      rw [e1, e2] at h3
      exact h3

end GlobalTheory.BesselQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainKernelBoundAtEmbeddingAnyLevelPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainKernel_bound_at_embedding_anyLevelPrime : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ i j, j = i + 1 → i < N.R.m → ∀ (L : Submodule (𝓞 X.E) (Sp X.E (N.R.N i))) (fr : Frs X.E (N.R.N i) (rowSG Pr sel mu)) (L' : Submodule (𝓞 X.E) (Sp X.E (N.R.N j))) (fr' : Frs X.E (N.R.N j) (rowSG Pr sel mu)), IsSdLat L → IsSdLat L' → ∀ Ξ : HomE X.E (N.R.N i) (N.R.N j) → X.K, SmallDatum (Sall sel mu u) L L' (Pr.T u * (Pr.g 0 * Pr.g 1)) Ξ (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), CoefOpLe ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) (W.lamTrue u i) (W.lamTrue u j) (kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) L fr L' fr' Ξ) (Real.exp (kernelBound_sq N δ (Pr.T u) CK j (fun z => logOmAt B cD M ρ (s.iT (pl z))) (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1))  := by
  first | exact @GlobalTheory.Core.Ht2.KernelS.kernel_le_sharp | exact GlobalTheory.Core.Ht2.KernelS.kernel_le_sharp | (intros; apply GlobalTheory.Core.Ht2.KernelS.kernel_le_sharp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharTieTrueCols
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem charTie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.CharTie (numDatumOfParameters (I.rec7 l Z) L) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (Pr := B.primes X) B.wts I.Ch I.glob I.sel := by
  intro B X I h l Z L
  exact ⟨h.ch_ok, rfl, rfl, ⟨I.C.eta, h.ch_tied⟩, h.weil, h.sel_ok⟩

end GlobalTheory.CoreHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapEqZeroOfTranslatedEvalAeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), IsInfFam θ → (∀ τ, (v₀ τ : M.H τ) ≠ 0) → ∀ T ∈ MultT θ M J χ, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 → T = 0 := by
  intro D X h θ S M J χ t v₀ _ hv₀ T hTm hae
  let T' : MMap M := PiTensorProduct.lift.symm T
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hTm
  have hT := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ T').1 hT'm
  have hval : T' v₀ = T (PiTensorProduct.tprod ℂ v₀) := by
    simp [T', PiTensorProduct.lift_symm]
  have hf := (hT.aut v₀).cont
  have hleft := (hT.aut v₀).left
  let ι : GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA := iotaX X h
  have hQ : ∀ γ ∈ X.B.I.GFset, ι.symm γ ∈ GQ (D.sp.Y 0) := by
    intro γ hγ
    refine (Formalism.IndefR.RationalEmbedding.iota_rat D (ι.symm γ)).2 ?_
    show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact GlobalTheory.TranslatedEvalInj.castGA_symm_mem _ γ hγ
  let φ : X.B.I.GA → ℂ := fun x => T' v₀ (ι.symm x * t)
  have hφ : ∀ x, φ x = T' v₀ (ι.symm (x * ι t)) := fun x => by
    simp only [φ, map_mul, ContinuousMulEquiv.symm_apply_apply]
  have hφc : Continuous φ := by
    have e : φ = fun x => T' v₀ (ι.symm (x * ι t)) := funext hφ
    rw [e]
    exact hf.comp (ι.symm.continuous.comp (continuous_mul_const _))
  have hφi : ∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y := by
    intro γ hγ y
    show T' v₀ (ι.symm (γ * y) * t) = T' v₀ (ι.symm y * t)
    rw [map_mul, mul_assoc]
    exact hleft _ (hQ γ hγ) _
  have hae' : φ =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] 0 := by
    have e : φ = evS X h t (T (PiTensorProduct.tprod ℂ v₀)) := by
      funext x; simp only [φ, evS, hval]; rfl
    rw [e]; exact hae
  have hz := GlobalTheory.TranslatedEvalInj.eq_zero_of_ae_fund X.B.I X.B.μf X.B.fund_spec hφc hφi hae'
  have hv : T' v₀ = 0 := by
    funext g
    have e := hz (ι (g * t⁻¹))
    simpa [φ] using e
  have hT0 : T' = 0 := GlobalTheory.TranslatedEvalInj.eq_zero_of_value hT v₀ hv₀ hv
  have : T = PiTensorProduct.lift T' := (PiTensorProduct.lift.apply_symm_apply T).symm
  rw [this, hT0, map_zero]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteRightTranslateFiniteA
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.RTr

theorem cuspFormsArchimedeanKFinite_rightTranslate_finite : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ → ∀ k ∈ GfC A,
    ∀ u ∈ A0 θ A cA, rTr A k u ∈ A0 θ A cA :=
  fun _ _ _ _ hθ _ hk _ hu => rTr_fin_mem_cuspForms hθ Kinf_le hu hk

end GlobalTheory.Core.Rk.RTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMem
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.CuspConj

theorem isKFinite_conj {G : Type} [Group G] {K : Subgroup G} {Φ : G → ℂ} (h : GlobalTheory.Doubling.IsKFinite K Φ) :
    GlobalTheory.Doubling.IsKFinite K fun g => conj (Φ g) := by
  unfold GlobalTheory.Doubling.IsKFinite GlobalTheory.Doubling.kSpan at *
  refine GlobalTheory.Mem.AutConj.finiteDimensional_span_star h ?_
  rintro f ⟨k, hk, rfl⟩
  refine ⟨k, hk, ?_⟩
  funext g
  show star (conj (Φ (g * k))) = Φ (g * k)
  rw [starRingEnd_apply, star_star]

theorem conj_comp_mem_A0 : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ →
    ∀ u ∈ GlobalTheory.Cusp.A0 θ A cA, (fun g => conj (u g)) ∈ GlobalTheory.Cusp.A0 θ A cA := by
  intro D θ A cA hθ u hu
  have hu' : u ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A := hu
  show (fun g => conj (u g)) ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hu'
  obtain ⟨hs, hk⟩ := mem_autForms.1 h1
  refine Submodule.mem_inf.2 ⟨mem_autForms.2 ⟨?_, isKFinite_conj hk⟩, conj_mem_cuspCont h2⟩
  exact GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ A u hs

end GlobalTheory.Core.Rk.CuspConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.RapidDecay.cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay :=
  GlobalTheory.Grow.cuspRapidDecay_of_bound _root_.GlobalTheory.CuspGeo.cuspDecayBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesTestDataOfNoncompactGaps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

private theorem isHCParam_comp_fin_cast {n m : ℕ} (h : n = m) {f : Fin m → ℝ} (hf : Formalism.QuantumDeterminants.IsHCParam f) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin n => f (Fin.cast h i)) := by
  subst h
  exact hf

theorem isHCParam_lam_of_setting {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : InfinitePlace X.B.I.F) :
    Formalism.QuantumDeterminants.IsHCParam (X.B.lam v) := by
  rw [show X.B.lam v = _ from funext (X.lam_eq v)]
  exact isHCParam_comp_fin_cast X.n_eq (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc (X.pl v)))

private theorem card_filter_true_add_card_filter_false {n : ℕ} (ε : Fin n → Bool) :
    (Finset.univ.filter fun a : Fin n => ε a = true).card +
      (Finset.univ.filter fun a : Fin n => ε a = false).card = n := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h1 : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem two_mul_rkR_le {n : ℕ} (ε : Fin n → Bool) : 2 * GlobalTheory.Count.rkR ε ≤ n := by
  have h1 : GlobalTheory.Count.rkR ε ≤ (Finset.univ.filter fun a : Fin n => ε a = true).card := min_le_left _ _
  have h2 : GlobalTheory.Count.rkR ε ≤ (Finset.univ.filter fun a : Fin n => ε a = false).card := min_le_right _ _
  have h3 := card_filter_true_add_card_filter_false ε
  omega

private theorem natCast_rpow_three_halves_le_sq (q : ℕ) : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
    positivity
  · have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    calc (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = (q : ℝ) ^ 2 := Real.rpow_two _

private theorem mul_rpow_three_halves_le_pow_four (q n : ℕ) (h : 2 * q ≤ n) :
    120 * (n : ℝ) * ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero]
    positivity
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hq2 : 2 * (q : ℝ) ≤ n := by exact_mod_cast h
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hsq : 4 * (q : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (n : ℝ) * (q : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (natCast_rpow_three_halves_le_sq q) (by positivity)
      _ ≤ 30 * (n : ℝ) ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hsq hn0]
      _ ≤ 100 * (n : ℝ) ^ 4 := by
          nlinarith [mul_le_mul_of_nonneg_left (show (30 : ℝ) ≤ 100 * n by linarith) (pow_nonneg hn0 3)]

theorem rkR_bound {n : ℕ} (ε : Fin n → Bool) :
    120 * (n : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (n : ℝ) ^ 4 :=
  mul_rpow_three_halves_le_pow_four _ _ (two_mul_rkR_le ε)

private theorem mul_sq_mul_sqrt_le_pow_four (q n : ℕ) (h : 2 * q ≤ n) :
    40 * (n : ℝ) ^ 2 * Real.sqrt (q : ℝ) ≤ 100 * (n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [Nat.cast_zero, Real.sqrt_zero, mul_zero]
    positivity
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hq2 : 2 * (q : ℝ) ≤ n := by exact_mod_cast h
    have hs : Real.sqrt (q : ℝ) ≤ q := by
      have h' := Real.sqrt_le_sqrt (show (q : ℝ) ≤ (q : ℝ) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at h'
    calc 40 * (n : ℝ) ^ 2 * Real.sqrt (q : ℝ) ≤ 40 * (n : ℝ) ^ 2 * q :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 20 * (n : ℝ) ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hq2 (sq_nonneg (n : ℝ))]
      _ ≤ 100 * (n : ℝ) ^ 4 := by
          nlinarith [mul_le_mul_of_nonneg_left (show (20 : ℝ) ≤ 100 * n by linarith) (pow_nonneg hn0 3)]

theorem rkR_bound_sqrt {n : ℕ} (ε : Fin n → Bool) :
    40 * (n : ℝ) ^ 2 * Real.sqrt (GlobalTheory.Count.rkR ε) ≤ 100 * (n : ℝ) ^ 4 :=
  mul_sq_mul_sqrt_le_pow_four _ _ (two_mul_rkR_le ε)

theorem seeData_of_gap : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  intro D X hg
  have hDS : GlobalTheory.Count.IsDSData X.B X.dv := fun v =>
    ⟨isHCParam_lam_of_setting X v, X.ds v, X.low v, GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X v⟩
  have hb : ∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      100 * (D.R.r : ℝ) ^ 4 := by
    intro v
    have e : (X.B.I.n : ℝ) = (D.R.r : ℝ) := by exact_mod_cast X.n_eq
    calc _ ≤ 100 * (X.B.I.n : ℝ) ^ 4 := rkR_bound (X.B.I.ε v)
      _ = 100 * (D.R.r : ℝ) ^ 4 := by rw [e]
  have hL : GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) :=
    GlobalTheory.Dec.locDec_of_decGap_gapGe (GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap)
      X.B X.dv _ hDS hg hb
  have hI : Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) :=
    (GlobalTheory.Dec.ProjCuspGap.projector_rank_cuspidal X.B X.dv _ hDS hg hb).1
  have hH : GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) := by
    unfold GlobalTheory.Dec.HBig
    intro v
    have e : (X.B.I.n : ℝ) = (D.R.r : ℝ) := by exact_mod_cast X.n_eq
    calc _ ≤ 100 * (X.B.I.n : ℝ) ^ 4 := rkR_bound_sqrt (X.B.I.ε v)
      _ = 100 * (D.R.r : ℝ) ^ 4 := by rw [e]
  exact ⟨hDS, hL, hH, hb, hI, GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X hI⟩

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightEqOneLatticeStabilizerComponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem hgt_one_components : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → (∀ v, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v k = 1) ∧ (∀ κ ∈ GfC V, ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w κ = 1) ∧ ∀ b ∈ GinfC V, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b = 1 := by
  intro D V Λ hΛ
  haveI : Submodule.IsFullLattice D.host.E Λ := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ
  refine ⟨fun v k hk => ?_, fun κ hκ w => ?_, fun b hb v => ?_⟩
  · have hK := (GlobalTheory.Doubling.ioH_mem_KFin (L := Λ) (GlobalTheory.Doubling.gram_hdbl V) (g := k) (g' := 1)).2 ⟨hk, one_mem _⟩
    have := GlobalTheory.Doubling.hgtH_of_mem (GlobalTheory.Doubling.continuous_absEv v) (GlobalTheory.Doubling.isCompact_KFin v) hK
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV
    exact_mod_cast this
  · exact GlobalTheory.AdelicU.mem_finPts_iff_forall.1 hκ w
  · exact GlobalTheory.AdelicU.mem_infPts_iff_forall.1 hb v

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutions
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.MajFrame

theorem exists_maj_cart : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → ∃ a : GL (Fin A.rank) (AE D), IsMaj A a ∧ ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1 := by
  intro D θ A sA hθ hs
  obtain ⟨a, ha, -, hfs⟩ := GlobalTheory.Doubling.exists_isMaj_frameInv_eq hθ hs
  refine ⟨a, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (GlobalTheory.Doubling.isMaj_iff hθ).1 ha τ
  rw [← hfs τ, GlobalTheory.Doubling.frameInv]
  have : (compAt θ τ a.1)ᴴ * (gramAt D A τ * (compAt θ τ a.1 * (compAt θ τ a.1)ᴴ * gramAt D A τ)) * compAt θ τ a.1 =
      ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) := by
    simp only [Matrix.mul_assoc]
  rw [this, hε, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp

end GlobalTheory.Core.Rk.MajFrame
end
end

