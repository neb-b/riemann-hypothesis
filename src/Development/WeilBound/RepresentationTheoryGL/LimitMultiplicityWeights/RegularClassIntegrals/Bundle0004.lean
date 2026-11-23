module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Bundle0003
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ArchUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DBridge
section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem bridge : Bridge := by
  intro D V r X Y hW j
  rw [NA_frameFlag]
  rfl

end MainStatements.WeightKernel.Dec

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DDecay
section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

namespace DDecay

theorem tsum_eq (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r)
    (hB : NA (frameFlag (isIsoFrame_firstCols hW j)) = unipRad D.sp.cm.sig V.gram (pre X j))
    (g : GA D V → ℂ) :
    ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν) =
      ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := by
  have hS : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)) =
      rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) : Set (GF V)) := by
    rw [← Subgroup.coe_map, map_unipRat, hB]; rfl
  calc ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν)
      = ∑' b : (rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) :
          Set (GF V))), g b := (tsum_image g (ratEmb_injective _ _).injOn).symm
    _ = ∑' c : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)),
          g (Set.equivOfEq hS c) := (Equiv.tsum_eq (Set.equivOfEq hS) (fun b => g b)).symm
    _ = ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := rfl

end DDecay

theorem decay : Core → Bridge → Decay := by
  intro hCore hBridge D V r X Y hW c hc j f hf hU C W hC hW'
  obtain ⟨A, hA⟩ := hCore D V r X Y hW c hc j
  have hB := hBridge D V r X Y hW j
  have hV : Van (unipRad D.sp.cm.sig V.gram (pre X j)) f := by
    have h0 : Van (NA (frameFlag (isIsoFrame_firstCols hW j))) f := fun ν _ x y => (hU ν x y).2
    rw [hB] at h0
    exact h0
  refine ⟨A, fun m => ?_⟩
  obtain ⟨B, hBd⟩ := hA m f hf hV C W hC hW'
  refine ⟨B, fun t ht a ha x hx y hy => ?_⟩
  have h1 := hBd t ht a ha x hx y hy
  have h2 : ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm,
      f (x * (a⁻¹ * rat V ν * a) * y) = nsum (NF D.sp.cm.sig V.gram (pre X j)) f (x * a⁻¹) (a * y) := by
    rw [nsum, ← DDecay.tsum_eq D V r X Y hW j hB (fun g => f (x * a⁻¹ * g * (a * y)))]
    congr 1; funext ν; congr 1; group
  rw [h2]
  exact h1

end MainStatements.WeightKernel.Dec
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DLevel
section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem level_of_mem {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, b, hb, rfl⟩ := hx
    obtain ⟨V, hV, hVb⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨V.comap (projFin σ J), hV.preimage (continuous_projFin σ J), fun k hk hkf g => ?_⟩
    show a (projInf σ J (g * k)) * b (projFin σ J (g * k)) = a (projInf σ J g) * b (projFin σ J g)
    rw [map_mul, map_mul, mem_finPts.1 hkf, mul_one, (hVb _ hk _).2]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨V, hV, h'⟩ := hy
    exact ⟨U ⊓ V, hU.inter hV, fun k hk hkf g => by
      simp only [Pi.add_apply, h k hk.1 hkf g, h' k hk.2 hkf g]⟩
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hkf g => by simp only [Pi.smul_apply, h k hk hkf g]⟩

end MainStatements.WeightKernel.Dec.DLevel

theorem MainStatements.WeightKernel.Dec.level : MainStatements.WeightKernel.Dec.Level := by
  intro F E _ _ _ _ _ σ _ n J _ f hf
  exact MainStatements.WeightKernel.Dec.DLevel.level_of_mem hf

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DVariationb
section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem variation : Variation := by
  intro F E _ _ _ _ _ σ hCM n J hJ k C hC f hf hfs hV z g e he
  have := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  have hc : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipRad σ J C) := GlobalTheory.UAut.cocompact_unipRad hCM hJ hC
  have hcl : IsClosed (unipRad σ J C : Set (GAd σ J)) :=
    GlobalTheory.UAut.unipFlag_const (σ := σ) (J := J) C 0 ▸ GlobalTheory.UAut.isClosed_unipFlag hJ (sigma_sigma hCM) hC _
  let ν : Measure (unipRad σ J C) := Measure.haar
  have h𝓕 := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)) ν
  have hfin : ν (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ≠ ⊤ := hc.measure_ne_top h𝓕
  have hpos : ν (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  let h : unipRad σ J C → ℂ := fun m => f (z * m * g)
  have hcont : Continuous h := by fun_prop
  let T := (Homeomorph.mulLeft z).trans (Homeomorph.mulRight g)
  have hK : IsCompact (T ⁻¹' tsupport f) := T.isCompact_preimage.2 hfs
  have hsupp : HasCompactSupport h :=
    HasCompactSupport.intro' (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK)
      ((isClosed_tsupport f).preimage (T.continuous.comp continuous_subtype_val))
      fun x hx => image_eq_zero_of_notMem_tsupport (f := f) (x := z * (x : GAd σ J) * g) hx
  have hint : Integrable h ν := hcont.integrable_of_hasCompactSupport hsupp
  have hV0 : ∫ m, h m ∂ν = 0 := hV ν z g
  let F' : (ratPts σ J).subgroupOf (unipRad σ J C) → unipRad σ J C → ℂ := fun γ x => h (γ • x)
  have hmeas : ∀ γ, AEStronglyMeasurable (F' γ) (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    fun γ => (hcont.comp (continuous_const_smul γ)).aestronglyMeasurable
  have hlin : ∑' γ, ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ‖F' γ x‖ₑ ∂ν ≠ ⊤ := by
    have hl : ∫⁻ x, ‖h x‖ₑ ∂ν = ∑' γ, ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ‖F' γ x‖ₑ ∂ν := by
      rw [h𝓕.lintegral_eq_tsum' (fun x => ‖h x‖ₑ), ← (Equiv.inv _).tsum_eq]; simp [F']
    rw [← hl]; exact hint.2.ne
  have e1 : ∫ m, h m ∂ν = ∑' γ, ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), F' γ x ∂ν := by
    rw [h𝓕.integral_eq_tsum' h hint, ← (Equiv.inv _).tsum_eq]; simp [F']
  have e2 := integral_tsum hmeas hlin
  have hΨ : ∀ x : unipRad σ J C, ∑' γ, F' γ x = nsum (NF σ J C) f z ((x : GAd σ J) * g) := fun x => by
    let eq : (ratPts σ J).subgroupOf (unipRad σ J C) ≃ NF σ J C :=
      { toFun := fun γ => ⟨γ.1.1, γ.2, γ.1.2⟩, invFun := fun ν => ⟨⟨ν.1, ν.2.2⟩, ν.2.1⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [nsum, ← eq.tsum_eq]
    congr 1; funext γ
    show f (z * ((γ • x : unipRad σ J C) : GAd σ J) * g) = _
    rw [Subgroup.smul_def]; simp [eq, mul_assoc]
  have hzero : ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)),
      nsum (NF σ J C) f z ((x : GAd σ J) * g) ∂ν = 0 := by
    simp_rw [← hΨ]; rw [e2]; exact e1.symm.trans hV0
  have hae : ∀ᵐ x ∂(ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))),
      HasSum (fun γ => F' γ x) (∑' γ, F' γ x) := by
    have h1 : ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ∑' γ, ‖F' γ x‖ₑ ∂ν ≠ ⊤ := by
      rw [lintegral_tsum (fun γ => (hmeas γ).enorm)]; exact hlin
    filter_upwards [ae_lt_top' (AEMeasurable.tsum fun γ => (hmeas γ).enorm) h1] with x hx
    have hs : Summable fun γ => ‖F' γ x‖₊ :=
      ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa [enorm_eq_nnnorm] using hx.ne)
    exact (Summable.of_norm (NNReal.summable_coe.2 hs)).hasSum
  have hΨm : AEStronglyMeasurable (fun x : unipRad σ J C => ∑' γ, F' γ x)
      (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s => by first
        | exact Finset.aestronglyMeasurable_fun_sum s fun γ _ => hmeas γ
        | exact Finset.aestronglyMeasurable_sum s fun γ _ => hmeas γ) hae
  haveI : IsFiniteMeasure (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    isFiniteMeasure_restrict.2 hfin
  have hΨi : IntegrableOn (fun x : unipRad σ J C => nsum (NF σ J C) f z ((x : GAd σ J) * g))
      (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ν := by
    refine Integrable.of_bound (C := e + ‖nsum (NF σ J C) f z g‖) ?_ (.of_forall fun x => ?_)
    · simpa only [hΨ] using hΨm
    · have := he x x.2
      calc _ = ‖(nsum (NF σ J C) f z ((x : GAd σ J) * g) - nsum (NF σ J C) f z g) + nsum (NF σ J C) f z g‖ := by
              rw [sub_add_cancel]
        _ ≤ _ := (norm_add_le _ _).trans (by linarith)
  have key : ν.real (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) • nsum (NF σ J C) f z g =
      ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)),
        (nsum (NF σ J C) f z g - nsum (NF σ J C) f z ((x : GAd σ J) * g)) ∂ν := by
    rw [integral_sub (integrable_const _) hΨi, hzero, setIntegral_const, sub_zero]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := ν) hfin.lt_top
    (f := fun x : unipRad σ J C => nsum (NF σ J C) f z g - nsum (NF σ J C) f z ((x : GAd σ J) * g)) (C := e)
    (fun x _ => by rw [norm_sub_rev]; exact he x x.2)
  rw [← key, norm_smul, Real.norm_of_nonneg measureReal_nonneg] at hb
  have hp : 0 < ν.real (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) := ENNReal.toReal_pos hpos hfin
  nlinarith [norm_nonneg (nsum (NF σ J C) f z g)]

end MainStatements.WeightKernel.Dec
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.NcardBiUnionLe
section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DBase

theorem ncard_biUnion_le' {α ι : Type*} (I : Finset ι) (S : ι → Set α) (h : ∀ i ∈ I, (S i).Finite) :
    (⋃ i ∈ I, S i).ncard ≤ ∑ i ∈ I, (S i).ncard := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert j I hj ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hj]
    refine (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) _)

end MainStatements.WeightKernel.Dec.DBase

namespace MainStatements.WeightKernel.Dec
open DBase

theorem base : Base := by
  intro D V r X Y hW c hc
  obtain ⟨V₀, hV₀c, hV₀n⟩ := exists_compact_mem_nhds (1 : GA D V)
  have hC₀ : IsCompact (V₀⁻¹ * V₀) := hV₀c.inv.mul hV₀c
  obtain ⟨A, B₀, hAB⟩ := _root_.GlobalTheory.CompanionTheory.TorusCount.torus_count D V r X Y hW c hc _ hC₀
  refine ⟨A, fun Γ hΓ f hf hfs C W hC hW' => ?_⟩
  set K : Set (GA D V) := C⁻¹ * tsupport f * W⁻¹ with hK
  have hKc : IsCompact K := (hC.inv.mul hfs.isCompact).mul hW'.inv
  have hint : interior V₀ ∈ nhds (1 : GA D V) := interior_mem_nhds.2 hV₀n
  obtain ⟨I, hI⟩ := hKc.elim_finite_subcover (fun g : K => (g : GA D V) • interior V₀)
    (fun g => isOpen_interior.smul _) (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩,
      ⟨1, mem_of_mem_nhds hint, by simp⟩⟩)
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfs
  refine ⟨max M 0 * I.card * max B₀ 0, fun t ht a ha x hx y hy => ?_⟩
  obtain ⟨hfin₀, hcnt₀⟩ := hAB t ht a ha
  set S₀ := {δ : GF V | a⁻¹ * rat V δ * a ∈ V₀⁻¹ * V₀}
  set S : K → Set (GF V) := fun g => {δ : GF V | a⁻¹ * rat V δ * a ∈ (g : GA D V) • V₀}
  have hS : ∀ g, (S g).Finite ∧ (S g).ncard ≤ S₀.ncard := by
    intro g
    rcases (S g).eq_empty_or_nonempty with h | ⟨δ₀, hδ₀⟩
    · rw [h]; simp
    have hmap : ∀ δ ∈ S g, δ₀⁻¹ * δ ∈ S₀ := by
      intro δ hδ
      obtain ⟨u, hu, hu'⟩ := hδ
      obtain ⟨u₀, hu₀, hu₀'⟩ := hδ₀
      refine ⟨u₀⁻¹, Set.inv_mem_inv.2 hu₀, u, hu, ?_⟩
      simp only [smul_eq_mul] at hu' hu₀'
      have e : a⁻¹ * rat V (δ₀⁻¹ * δ) * a = (a⁻¹ * rat V δ₀ * a)⁻¹ * (a⁻¹ * rat V δ * a) := by
        simp [map_mul, map_inv, mul_assoc]
      rw [e, ← hu', ← hu₀']; group
    have hinj : Set.InjOn (fun δ => δ₀⁻¹ * δ) (S g) := fun _ _ _ _ h => mul_left_cancel h
    have hf1 : (S g).Finite := Set.Finite.of_finite_image (hfin₀.subset (by
      rintro _ ⟨δ, hδ, rfl⟩; exact hmap δ hδ)) hinj
    exact ⟨hf1, Set.ncard_le_ncard_of_injOn _ hmap hinj hfin₀⟩
  set T := {δ : GF V | a⁻¹ * rat V δ * a ∈ K}
  have hTsub : T ⊆ ⋃ g ∈ I, S g := by
    intro δ hδ
    obtain ⟨g, hg, hmem⟩ := Set.mem_iUnion₂.1 (hI hδ)
    exact Set.mem_iUnion₂.2 ⟨g, hg, Set.smul_set_mono interior_subset hmem⟩
  have hUfin : (⋃ g ∈ I, S g).Finite := Set.Finite.biUnion I.finite_toSet fun g _ => (hS g).1
  have hTfin : T.Finite := hUfin.subset hTsub
  have hTcnt : (T.ncard : ℝ) ≤ I.card * max B₀ 0 * (∏ i, max (t i) 1) ^ A := by
    have h1 : T.ncard ≤ I.card * S₀.ncard := by
      refine (Set.ncard_le_ncard hTsub hUfin).trans ((ncard_biUnion_le' I S fun g _ => (hS g).1).trans ?_)
      simpa using Finset.sum_le_sum (s := I) fun g _ => (hS g).2
    have hP : 0 ≤ (∏ i, max (t i) 1) ^ A :=
      pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) A
    calc (T.ncard : ℝ) ≤ I.card * S₀.ncard := by exact_mod_cast h1
      _ ≤ I.card * (max B₀ 0 * (∏ i, max (t i) 1) ^ A) := by
          gcongr
          exact hcnt₀.trans (by gcongr; exact le_max_left _ _)
      _ = _ := by ring

  set g : Γ → ℂ := fun ν => f (x * a⁻¹ * ν * (a * y)) with hg
  have hsupp : ∀ ν : Γ, g ν ≠ 0 → ∃ δ ∈ T, rat V δ = ν := by
    intro ν hν
    obtain ⟨δ, hδ⟩ : (ν : GA D V) ∈ (ratEmb D.sp.cm.sig V.gram).range :=
      (range_ratEmb D.sp.cm.sig V.gram).symm ▸ hΓ ν.2
    refine ⟨δ, ?_, hδ⟩
    have hs : x * a⁻¹ * ν * (a * y) ∈ tsupport f := subset_tsupport _ hν
    show a⁻¹ * rat V δ * a ∈ K
    refine ⟨x⁻¹ * (x * a⁻¹ * ν * (a * y)), ⟨x⁻¹, Set.inv_mem_inv.2 hx, _, hs, rfl⟩, y⁻¹,
      Set.inv_mem_inv.2 hy, ?_⟩
    show _ = _
    rw [show rat V δ = ν from hδ]; group
  have hsf : (Function.support g).Finite := by
    refine (hTfin.image (rat V)).preimage (Subtype.val_injective.injOn) |>.subset ?_
    intro ν hν
    obtain ⟨δ, hδ, e⟩ := hsupp ν hν
    exact ⟨δ, hδ, e⟩
  have hcard : (hsf.toFinset.card : ℝ) ≤ T.ncard := by
    have : (Function.support g).ncard ≤ T.ncard := by
      have h2 : (Function.support g).ncard ≤ (rat V '' T).ncard :=
        Set.ncard_le_ncard_of_injOn Subtype.val (fun ν hν => by
          obtain ⟨δ, hδ, e⟩ := hsupp ν hν; exact ⟨δ, hδ, e⟩) Subtype.val_injective.injOn (hTfin.image _)
      exact h2.trans (Set.ncard_image_le hTfin)
    rw [Set.ncard_eq_toFinset_card _ hsf] at this
    exact_mod_cast this
  show ‖∑' ν : Γ, g ν‖ ≤ _
  rw [tsum_eq_sum (s := hsf.toFinset) (fun ν hν => by simpa using hν)]
  have hP : 0 ≤ (∏ i, max (t i) 1) ^ A :=
    pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) A
  calc ‖∑ ν ∈ hsf.toFinset, g ν‖ ≤ ∑ ν ∈ hsf.toFinset, ‖g ν‖ := norm_sum_le _ _
    _ ≤ ∑ _ν ∈ hsf.toFinset, max M 0 := Finset.sum_le_sum fun ν _ => (hM _).trans (le_max_left _ _)
    _ = hsf.toFinset.card * max M 0 := by simp
    _ ≤ T.ncard * max M 0 := by gcongr
    _ ≤ (I.card * max B₀ 0 * (∏ i, max (t i) 1) ^ A) * max M 0 := by gcongr
    _ = _ := by ring

end MainStatements.WeightKernel.Dec
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PCuspAny
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing GlobalTheory.Proof.parabolic_and_constant_term
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem MainStatements.WeightKernel.cuspAny : MainStatements.WeightKernel.CuspAny := by
  intro D V hodd T U hNoFixed μf hμf ff hff fa hA 𝔉 hP
  have := hμf
  have hH := (GlobalTheory.T.typeHypothesis_forms_agree D V T hNoFixed).1
  obtain ⟨a, ha0, ha2, hpar⟩ := parabolicAtSplitPlaces D V hodd T 𝔉 hP
  obtain ⟨v, hv⟩ := hH a ha0 (by omega)
  obtain ⟨h, hh, e⟩ := hff.2.1 v
  have hF := hff.isFinFamily
  have he := (T.frame v).idem_mem (μf v.1) (T.τ v)
  refine _root_.GlobalTheory.TestConstTerm.unipIntegralsVanish_tensor D V 𝔉 fa ff hA hF v.1 fun ν _ x y => ?_
  exact (_root_.GlobalTheory.LocConst.unip_integral_vanish D V T v a ha0 (by omega) hv 𝔉 (hpar v).1 (μf v.1) _ (conv_mem_SB he hh) (ff v.1) (Or.inr e)
    ν x y).2

end
end

