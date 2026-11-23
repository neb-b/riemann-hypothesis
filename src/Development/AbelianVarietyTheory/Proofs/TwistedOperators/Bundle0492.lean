module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuous
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
noncomputable section

namespace GlobalTheory.ArchFamilyCont

theorem continuous_family : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ (f : SInf F (Fin n × Fin d)) y, Continuous fun t => T t f y) ∧
    ∀ (μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure → ∀ f φ : SInf F (Fin n × Fin d),
      Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW γ hγ T hT
  classical
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hc : IsContOn (adeleClass F) om := hW.2.2
  have hline : Continuous fun t : ℝ => ((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) :=
    continuous_const.prodMk (hγ.1.comp continuous_ofAdd)
  have key : ∀ t (f : SInf F (Fin n × Fin d)),
      om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R) = tens (evI F) ⇑(T t f) R :=
    fun t f => hT t f R (hR f)
  have hRl : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, R (liftV y) = R 0 := by
    intro y
    have hat : At (evI F) (liftV y) := by
      intro u hu
      have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
      funext i
      show u * liftV y i = 0
      exact Prod.ext (show u.1 * _ = 0 by rw [hu1, zero_mul]) (show u.2 * 0 = 0 from mul_zero _)
    have := (hR 0).1 0 (liftV y) hat
    simpa using this
  have hev : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, (fun i => evI F (liftV y i)) = y := by
    intro y; funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = y i
    exact RingEquiv.apply_symm_apply _ _
  have hfin : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, (fun i => (liftV y i).2) = 0 := by
    intro y; funext i; rfl
  have htl : ∀ (f : SInf F (Fin n × Fin d)) y, tens (evI F) ⇑f R (liftV y) = f y * R 0 := by
    intro f y
    show f (fun i => evI F (liftV y i)) * R (liftV y) = _
    rw [hev, hRl]
  refine ⟨fun f y => ?_, fun μ hμ f φ => ?_⟩
  ·
    let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (liftV y)
    have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
      intro g _
      refine ⟨g 0 • ((BoundedContinuousFunction.evalCLM ℂ y).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f' => ?_⟩
      show pureA F (⇑f') g (liftV y) = _
      simp only [pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
      have e1 := hev y
      have e2 := hfin y
      simp only [evI] at e1
      rw [e1, e2, mul_comm]
    have h1 := hc l hl _ (hR f).2
    have h2 : Continuous fun t : ℝ => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) := h1.comp hline
    have h3 : (fun t : ℝ => T t f y) = fun t => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) / R 0 := by
      funext t
      rw [key]
      show _ = tens (evI F) ⇑(T t f) R (liftV y) / R 0
      rw [htl, mul_div_cancel_right₀ _ hR0]
    rw [h3]
    exact h2.div_const _
  ·
    haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := inferInstance
    haveI : μ.HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
    let Tφ : SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
      (innerSL ℂ (φ.toLp 2 μ)).comp (SchwartzMap.toLpCLM ℂ ℂ 2 μ)
    have hTφ : ∀ g : SInf F (Fin n × Fin d), Tφ g = ∫ x, g x * starRingEnd ℂ (φ x) ∂μ := by
      intro g
      show inner ℂ (φ.toLp 2 μ) (g.toLp 2 μ) = _
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [SchwartzMap.coeFn_toLp φ 2 μ, SchwartzMap.coeFn_toLp g 2 μ] with x hx1 hx2
      rw [hx1, hx2, RCLike.inner_apply, mul_comm]
    let cL : SInf F (Fin n × Fin d) →ₗ[ℂ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) :=
      { toFun := fun g => ⇑g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective cL := fun a b h => DFunLike.coe_injective h
    let eq := LinearEquiv.ofInjective cL hinj
    obtain ⟨L, hL⟩ := LinearMap.exists_extend (Tφ.toLinearMap ∘ₗ eq.symm.toLinearMap)
    have hLc : ∀ g : SInf F (Fin n × Fin d), L ⇑g = Tφ g := by
      intro g
      have := LinearMap.congr_fun hL (eq g)
      simp at this
      exact this
    let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := L ∘ₗ LinearMap.funLeft ℂ ℂ liftV
    have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
      intro g _
      refine ⟨g 0 • Tφ, fun f' => ?_⟩
      have e : (LinearMap.funLeft ℂ ℂ liftV (pureA F (⇑f') g) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
          = ⇑(g 0 • f') := by
        funext x
        have e1 := hev x
        have e2 := hfin x
        simp only [evI] at e1
        simp only [LinearMap.funLeft_apply, Function.comp_apply, pureA, SchwartzMap.smul_apply, smul_eq_mul]
        rw [e1, e2, mul_comm]
      show L (LinearMap.funLeft ℂ ℂ liftV (pureA F (⇑f') g)) = _
      rw [e, hLc, map_smul]
      rfl
    have h1 := hc l hl _ (hR f).2
    have h2 : Continuous fun t : ℝ => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) := h1.comp hline
    have h3 : (fun t : ℝ => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) =
        fun t => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) / R 0 := by
      funext t
      rw [key]
      have e : (LinearMap.funLeft ℂ ℂ liftV (tens (evI F) ⇑(T t f) R) :
          (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = ⇑(R 0 • T t f) := by
        funext x
        simp only [LinearMap.funLeft_apply, Function.comp_apply, SchwartzMap.smul_apply, smul_eq_mul]
        rw [htl, mul_comm]
      show _ = L (LinearMap.funLeft ℂ ℂ liftV (tens (evI F) ⇑(T t f) R)) / R 0
      rw [e, hLc, map_smul, smul_eq_mul, hTφ, mul_div_cancel_left₀ _ hR0]
    rw [h3]
    exact h2.div_const _

end GlobalTheory.ArchFamilyCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPointPureTensorKeepsFiniteFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchPure

theorem acts_arch_of_weil {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hW : M.IsWeil ψ χX χW om)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J) (hh : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F))
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) :
    ∃ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, h)) f f₁ := by
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW
  set T := om (1, h) with hTdef
  have hpres : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun Φ hΦ => hS.pres (1, h) Φ hΦ
  have hcomm := GlobalTheory.ArchLocality.comm_fin M ψ χX χW om hW h hh
  obtain ⟨r₀, hr₀1, hr₀⟩ := GlobalTheory.ArchLocality.ref_fun (F := F) (Fin n × Fin d)
  set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F)
    (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ with hΦ₀
  have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.ArchLocality.res_arch (T Φ₀) (hpres Φ₀ hm₀)
  refine ⟨f₁, fun r hr => ?_⟩
  funext y
  set u : AF F := (0, 1) with hu
  have hu0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F u = 0 := GlobalTheory.ArchLocality.evI_fin
  have htr : ∀ Ψ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
      T (fun w => Ψ (w + u • (-y))) = fun w => T Ψ (w + u • (-y)) := by
    intro Ψ hΨ
    have e := hcomm u hu0 (-y) 0 Ψ hΨ
    have hs0 : ∀ G : (Fin n × Fin d → AF F) → ℂ,
        GlobalTheory.WeilM.schr ψ (u • (-y), u • (0 : Fin n × Fin d → AF F)) G = fun w => G (w + u • (-y)) := by
      intro G; funext w; simp [GlobalTheory.WeilM.schr]
    rw [hs0, hs0] at e
    exact e
  set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F)
    (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := r y • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ :=
    Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hz2 : ∀ z : Fin n × Fin d → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → ∀ i, (z i).2 = 0 := by
    intro z hz i
    have := congrArg Prod.snd (congrFun (hz u hu0) i)
    change (u * z i).2 = (0 : AF F).2 at this
    have e : (u * z i).2 = (z i).2 := one_mul _
    rw [e] at this
    exact this
  have hvan : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((y + z + u • (-y)) i)) =
        fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.ArchLocality.evI_add, GlobalTheory.ArchLocality.evI_mul,
        hu0, zero_mul, add_zero]
    have e3 : r₀ (y + z + u • (-y)) = 1 := by
      refine hr₀1 _ fun i => ?_
      change ((y i + z i) + u * -(y i)).2 = 0
      change (y i).2 + (z i).2 + 1 * -(y i).2 = 0
      rw [hz2 z hz i]
      ring
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
    rw [e2, e3, e1]
    ring
  have h0 := GlobalTheory.ArchLocality.fibre ψ hψ T hcomm (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have hy0 : y + u • (-y) = fun i =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (y i)), 0) : AF F) := by
    funext i
    refine Prod.ext ?_ ?_
    · change (y i).1 + 0 * -(y i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [RingEquiv.symm_apply_apply]
      ring
    · change (y i).2 + 1 * -(y i).2 = 0
      ring
  have h2 : T Φ₂ y = r y * f₁ (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (y i)) := by
    rw [hΦ₂, map_smul, htr Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hy0, hf₁]
  rw [h0, h2]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  ring

theorem pure_arch : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F), ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ c : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      om (1, g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure c φ := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ hM hW g hg f φ hSB hvac
  obtain ⟨c, hc⟩ := acts_arch_of_weil M ψ χX χW om hψ hW g hg f
  refine ⟨c, ?_⟩
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  set r : (Fin n × Fin d → AF F) → ℂ :=
    fun x => ∏ᶠ v, φ v fun i => evFin F v (x i) with hr
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F)
      (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r := by
    refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hz0 : ∀ v i, evFin F v (z i) = 0 := by
      intro v i
      set u : AF F := (0, 1) with hu
      have h1 := congrFun (hz u GlobalTheory.ArchLocality.evI_fin) i
      have h2 : evFin F v u = 1 := map_one (evFin F v)
      have h3 := congrArg (evFin F v) h1
      simp only [Pi.zero_apply, map_zero] at h3
      change evFin F v (u * z i) = 0 at h3
      rw [map_mul, h2, one_mul] at h3
      exact h3
    simp only [hr, Pi.add_apply, map_add (f := _), hz0, add_zero]
  exact hc r hRest

end GlobalTheory.ArchPure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFiniteness
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.AvgCoeff

open MeasureTheory

theorem exists_finset_sep {K : Type} (S : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ S] :
    ∃ T : Finset K, ∀ s ∈ S, (∀ t ∈ T, s t = 0) → s = 0 := by
  classical
  let f : Finset K → Submodule ℂ S := fun T =>
    ⨅ t ∈ T, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) t).comp S.subtype)
  obtain ⟨T, -, hT⟩ := (measure fun T => Module.finrank ℂ (f T)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨T, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
  have hmem : ∀ T' : Finset K, ∀ u : S, u ∈ f T' ↔ ∀ t ∈ T', (u : K → ℂ) t = 0 := fun T' u => by
    simp [f, Submodule.mem_iInf]
  have hle : f (insert t T) ≤ f T := fun u hu =>
    (hmem T u).2 fun t' ht' => (hmem _ u).1 hu t' (Finset.mem_insert_of_mem ht')
  have hlt : f (insert t T) < f T := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 : (⟨s, hs⟩ : S) ∈ f T := (hmem T _).2 h0
    rw [← heq] at h1
    exact ht ((hmem _ _).1 h1 t (Finset.mem_insert_self t T))
  exact hT (insert t T) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem integral_mem {K K' : Type} [MeasurableSpace K'] (μ : Measure K') (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (F : K' → K → ℂ) (hF : ∀ k', F k' ∈ S)
    (hi : ∀ k, Integrable (fun k' => F k' k) μ) : (fun k => ∫ k', F k' k ∂μ) ∈ S := by
  obtain ⟨T, hT⟩ := exists_finset_sep S
  let R : S →ₗ[ℂ] (T → ℂ) := LinearMap.pi fun t : T => (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) (t : K)).comp S.subtype
  have hker : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun u hu => Subtype.ext ?_
    refine hT u u.2 fun t ht => ?_
    have := congrFun hu ⟨t, ht⟩
    simpa [R] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hker
  let b := Pi.basisFun ℂ T
  have hexp : ∀ s ∈ S, s = ∑ t : T, s t • ((L (b t) : S) : K → ℂ) := by
    intro s hs
    have h1 : (⟨s, hs⟩ : S) = L (R ⟨s, hs⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨s, hs⟩ = ∑ t : T, s t • b t := by
      conv_lhs => rw [← b.sum_repr (R ⟨s, hs⟩)]
      simp [R, b]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum] at h1
    have h3 := congrArg (fun u : S => (u : K → ℂ)) h1
    simpa [Submodule.coe_sum, map_smul] using h3
  have : (fun k => ∫ k', F k' k ∂μ) = ∑ t : T, (∫ k', F k' t ∂μ) • ((L (b t) : S) : K → ℂ) := by
    funext k
    have hk : ∀ k', F k' k = ∑ t : T, F k' t * ((L (b t) : S) : K → ℂ) k := fun k' => by
      conv_lhs => rw [hexp (F k') (hF k')]
      simp [Finset.sum_apply]
    simp_rw [hk]
    rw [integral_finsetSum (f := fun (t : T) k' => F k' t * ((L (b t) : S) : K → ℂ) k) Finset.univ
      fun t _ => (hi t).mul_const _]
    simp [Finset.sum_apply, integral_mul_const]
  rw [this]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (L (b t)).2

theorem coeffSpan_finiteDimensional {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  first
  | exact @_root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan
  | exact _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan
  | (apply _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan ..)

theorem coeffSpan_mulRight {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) (k' : K)
    {f : K → ℂ} (hf : f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) : (fun k => f (k * k')) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (GlobalTheory.Published.AutFin.coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (· * k')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ℓ, w, rfl⟩
    exact Submodule.subset_span ⟨ℓ, ρ k' w, funext fun k => by simp [LinearMap.funLeft, map_mul]⟩
  exact this hf

end GlobalTheory.AvgCoeff

namespace GlobalTheory.CuspKFin

open Formalism.REAL GlobalTheory.Published.AutFin GlobalTheory.AvgCoeff

theorem kFinAt_avg_of_kFinAt : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ),
    IsAutFunSm θ N.V ψ → ∀ (τ τ' : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ') → ℂ),
    GlobalTheory.TypeSum.KFinFun (N.M.ε τ') e → GlobalTheory.CuspKFin.KFinAt θ N τ ψ →
    GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ' (N.M.ε τ') (N.M.fr τ') e ψ) := by
  intro D θ hθ N ψ hψ τ τ' e he hK
  obtain ⟨W, i1, i2, i3, ρ, hρc, hρ⟩ := hK
  refine ⟨W, i1, i2, i3, ρ, hρc, fun x => ?_⟩
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := coeffSpan_finiteDimensional ρ
  have hec : Continuous e := by
    obtain ⟨F, -, heF, hc, -⟩ := he
    exact hc e heF
  have hAc : Continuous fun k' : Formalism.REAL.KG (N.M.ε τ') => atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ').comp_continuous GlobalTheory.SeriesToClosure.continuous_conjK
      fun k => conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k
  have hmem : ∀ k' : Formalism.REAL.KG (N.M.ε τ'), (fun k => ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ'))) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
    intro k'
    by_cases h : τ' = τ
    · subst h
      have h2 := coeffSpan_mulRight ρ k' (hρ x)
      convert h2 using 2 with k
      rw [mul_assoc]
      congr 2
      simp only [kAt]
      rw [← GlobalTheory.SeriesToClosure.at_mul hθ (N.M.fr_unit τ') (N.M.fr_gram τ')
        (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k)) (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k'))]
      rfl
    · have hc : ∀ k, kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k * atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') =
          atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k := fun k =>
        GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ τ' (Ne.symm h) _
          (conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k) _ (conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k')
      have h2 := hρ (x * atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ'))
      convert h2 using 2 with k
      rw [mul_assoc, hc, ← mul_assoc]
  have hcont : ∀ k, Continuous fun k' : Formalism.REAL.KG (N.M.ε τ') => e k' * ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ')) := fun k =>
    hec.mul (hψ.cont.comp (continuous_const.mul hAc))
  have key := GlobalTheory.AvgCoeff.integral_mem (muK (N.M.ε τ')) (GlobalTheory.Published.AutFin.coeffSpan ρ)
    (fun k' k => e k' * ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ')))
    (fun k' => Submodule.smul_mem _ (e k') (hmem k')) (fun k => GlobalTheory.ExpansionAverage.integrable_K (hcont k))
  exact key

end GlobalTheory.CuspKFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartzStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w),
    M.IsGood ψ → GlobalTheory.TripleAssembly.darbAlg M ψ τ ≤ GlobalTheory.WeilM.schA F (Fin n × Fin d) := by
  first | exact @GlobalTheory.TripleAssembly.darbAlg_le_schA | exact GlobalTheory.TripleAssembly.darbAlg_le_schA | (intros; apply GlobalTheory.TripleAssembly.darbAlg_le_schA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepIntertwinerChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.LastStepExists

theorem exists_lastStep_intertwiner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsChainW → R.ex_ItX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hLev hFam hMod hW
  obtain ⟨-, It, hIt⟩ := GlobalTheory.T.definite_lastStep_real_intertwiner D G Pl0 T A Ks R hLev hFam hMod hW.ωX hW.vX
  exact ⟨It, fun t => hIt t⟩

end GlobalTheory.Twist.LastStepExists
end

