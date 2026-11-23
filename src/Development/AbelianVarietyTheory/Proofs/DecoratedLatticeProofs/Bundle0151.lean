module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfPartEqZero
section
namespace I195MixedCoordinates_41a545e47d405c9816345b57

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_41a545e47d405c9816345b57

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixHalf

variable {D : D7}

theorem infPart_eq_zero {e : AE D} (he : IsSplitIdem D e) {z : AE D} (hz : cA D e * z = z) : infPart D z = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨β, rfl, -⟩, h3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have he' : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have h4 : (e + cA D e) * cA D e = cA D e := by rw [add_mul, h2, he', zero_add]
  rw [← hz, ← h4, h3, map_mul, map_mul, h0, zero_mul, zero_mul]

theorem map_infPart_mul {l m n : ℕ} {x : Mx D l m} (hx : x.map (infPart D) = 0) (y : Mx D m n) :
    (x ⬝ y).map (infPart D) = 0 := by
  rw [Matrix.map_mul, hx, Matrix.zero_mul]

theorem symplO_extX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ) (w : WO S T) :
    symplO S T (d.extX T x) w = symplO S T (d.extX T x) (d.extY T (w ⬝ d.jY)) := by
  unfold symplO
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY,
    HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY, Matrix.mul_one, Matrix.mul_zero, pairS, hO_eq_trace S₀, trace_zero]

theorem rank_qX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.qX.rank = ρ := by
  refine le_antisymm (by simpa using Matrix.rank_le_height d.qX) ?_
  have h : d.qX * d.e = 1 := d.e'e
  have := Matrix.rank_mul_le_left d.qX d.e
  rwa [h, Matrix.rank_one, Fintype.card_fin] at this

theorem mixS_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ f, IsThetaFunO ψ S T f → (∃ U : AddSubgroup (Mx D T.rank ρ), IsOpen (U : Set (Mx D T.rank ρ)) ∧ ∀ u ∈ U, (∀ i j, cA D e * u i j = u i j) → ∀ x, (_root_.I195MixedCoordinates_41a545e47d405c9816345b57.source d) T ψ μ 𝓕 f (x + u) = (_root_.I195MixedCoordinates_41a545e47d405c9816345b57.source d) T ψ μ 𝓕 f x) ∧ ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → (_root_.I195MixedCoordinates_41a545e47d405c9816345b57.source d) T ψ μ 𝓕 f x ≠ 0 → x ∈ K := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he f hf
  obtain ⟨hX, hY, -⟩ := _root_.GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d ⟨μ, 𝓕, hμ⟩ f hf
  obtain ⟨U, hU, hl⟩ := hf.level
  have hhalf : ∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → x.map (infPart D) = 0 := fun x hx => by
    ext i j; exact infPart_eq_zero he (hx i j)
  have cX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  have cY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  refine ⟨⟨U.comap (d.extX T), hU.preimage cX, fun u hu hu' x => ?_⟩, ?_⟩
  · have := hX x u
    rw [hl _ hu (map_infPart_mul (hhalf u hu') _)] at this
    exact this.symm
  · let r : WO S T →+ Mx D T.rank ρ :=
      { toFun := fun w => w ⬝ d.jY, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
    have cr : Continuous r := continuous_id.matrix_mul continuous_const
    obtain ⟨K, hK, hmem⟩ := GlobalTheory.IsoMeanAnnih.finPart_mem_compact D S T T.rank ρ 1 d.qX
      (by rw [Matrix.rank_one, Fintype.card_fin]) (rank_qX d) ψ hψ (U.comap ((d.extY T).comp r))
      (hU.preimage (cY.comp cr))
    obtain ⟨g, hg, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
    have hs : Continuous fun b : Af D.host.F ⊗[D.host.F] D.host.E => (g.symm (0, b) : AE D) :=
      hc.comp (continuous_const.prodMk continuous_id)
    refine ⟨(fun y => y.map fun b => (g.symm (0, b) : AE D)) '' K, hK.image (continuous_id.matrix_map hs),
      fun x hx h0 => ⟨x.map (finPart D), hmem x fun u hu hu' => ?_, ?_⟩⟩
    · have h1 := hY x (u ⬝ d.jY)
      rw [hl (d.extY T (u ⬝ d.jY)) hu (map_infPart_mul (map_infPart_mul hu' _) _)] at h1
      have h2 : GlobalTheory.IsoMean.emb S T 1 d.qX x = d.extX T x := by
        change (rat (1 : Matrix (Fin T.rank) (Fin T.rank) D.host.E) ⬝ x : Mx D T.rank ρ) ⬝ d.pX = x ⬝ d.pX
        rw [rat_one, Matrix.one_mul]
      rw [h2, symplO_extX]
      have h3 : (ψ (symplO S T (d.extX T x) (d.extY T (u ⬝ d.jY))) - 1) • (_root_.I195MixedCoordinates_41a545e47d405c9816345b57.source d) T ψ μ 𝓕 f x = 0 := by
        rw [sub_smul, one_smul]; exact sub_eq_zero.2 h1.symm
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right h0)
    · ext i j
      simp only [Matrix.map_apply]
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext ((infPart_eq_zero he (hx i j)).symm.trans (hg _).1.symm) (hg _).2.symm

end GlobalTheory.MixHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InnerPoincareSeriesEqSetIntegralUnfolding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.MainNotions.LeviCoordinates in
theorem GlobalTheory.Core.Mi.inner_pser_eq_setIntegral : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (Dt Fs : Set X.B.I.GA), IsReps X u Dt → InHH X u hK → IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∀ T : Cu X u hK, IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) → ∀ (f : X.B.I.GA → ℂ) (φ : L2X X), RowFun X f → (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f → ⟪star φ, PuFun X u hK Dt T⟫_ℂ = ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) := by
  intro D X u hK Dt Fs hD hin hFs T hPI f φ hf hφf
  have := X.B.sf
  have := X.B.haar
  have := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  have := Formalism.L2.SG.Pf.muf_right X
  have := rr_muA_sigmaFinite X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  have := rr_muA_right X.B.I X.B.μf
  have hPP := Formalism.L2.SG.PoincareInHH.Cut.phProps_closed X u hK (Formalism.L2.SG.Pf.ksetSplit_holds X u)
    (Formalism.L2.SG.Pf.unipotent_in_level X u) (Formalism.L2.SG.Pf.ratLevi_holds X u) (Formalism.L2.SG.Pf.psiProd_holds X u)
  have hFD := rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have hS : Srat X u ≤ rr_GF X.B.I := inf_le_left
  have hDc : Dt.Countable :=
    (Set.countable_coe_iff.1 (inferInstance : Countable (rr_GF X.B.I))).mono hD.1
  have := hDc.to_subtype
  have hSc : Countable (Srat X u) := Function.Injective.countable (Subgroup.inclusion_injective hS)
  have hSinv : SMulInvariantMeasure (Srat X u) X.B.I.GA (X.B.I.muA X.B.μf) := ⟨fun s A _ => by
      show (X.B.I.muA X.B.μf) ((fun y => (s : X.B.I.GA) * y) ⁻¹' A) = (X.B.I.muA X.B.μf) A
      exact measure_preimage_mul _ (s : X.B.I.GA) A⟩
  have hPm : Measurable (Ph X u hK T) := (hPP T).1
  have hPinv : ∀ s ∈ Srat X u, ∀ y, Ph X u hK T (s * y) = Ph X u hK T y := (hPP T).2.1
  have hfm : Measurable f := hf.cont.measurable
  obtain ⟨C, hC⟩ := hf.bdd
  have hfinv : ∀ γ ∈ rr_GF X.B.I, ∀ y, f (γ * y) = f y := fun γ hγ y => hf.left γ hγ y
  have hginv : ∀ (s : Srat X u) (x : X.B.I.GA),
      (fun x => f x * Ph X u hK T x) ((s : X.B.I.GA) * x) = (fun x => f x * Ph X u hK T x) x := by
    intro s x
    show f (s * x) * Ph X u hK T (s * x) = f x * Ph X u hK T x
    rw [hfinv s (hS s.2) x, hPinv s s.2 x]
  have hF' : IsFundamentalDomain (Srat X u) (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund) (X.B.I.muA X.B.μf) :=
    rr_isFD (Formalism.L2.SG.Pf.InHHLeaf.rr_FD_union hFD (Srat X u) hS Dt hD hDc)
  have hgFs : IntegrableOn (fun x => f x * Ph X u hK T x) Fs (X.B.I.muA X.B.μf) :=
    Integrable.bdd_mul (c := C) hPI hfm.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have hgFs' := (hFs.integrableOn_iff hF' hginv).1 hgFs
  have e1 : ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∫ x in (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund), f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) :=
    hFs.setIntegral_eq hF' (f := fun x => f x * Ph X u hK T x) hginv
  have hU : (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund) = ⋃ δ : Dt, (fun y => (δ : X.B.I.GA) * y) '' X.B.fund := by
    rw [Set.biUnion_eq_iUnion]
  have hmeas : ∀ δ : Dt, MeasurableSet ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) := by
    intro δ; rw [Formalism.L2.SG.Pf.InHHLeaf.img_mul]; exact hFD.meas.preimage (measurable_const_mul _)
  have hdisj : Pairwise (Function.onFun (AEDisjoint (X.B.I.muA X.B.μf))
      fun δ : Dt => (fun y => (δ : X.B.I.GA) * y) '' X.B.fund) := by
    intro δ δ' hne
    show X.B.I.muA X.B.μf (((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) ∩ ((fun y => (δ' : X.B.I.GA) * y) '' X.B.fund)) = 0
    have hsub : ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) ∩ ((fun y => (δ' : X.B.I.GA) * y) '' X.B.fund) ⊆
        (fun y => (δ' : X.B.I.GA) * y) '' ((fun y => ((δ' : X.B.I.GA)⁻¹ * δ) * y) '' X.B.fund ∩ X.B.fund) := by
      rintro _ ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx⟩⟩
      simp only at hxx
      refine ⟨x', ⟨⟨x, hx, ?_⟩, hx'⟩, hxx⟩
      show (δ' : X.B.I.GA)⁻¹ * δ * x = x'
      rw [show x' = (δ' : X.B.I.GA)⁻¹ * ((δ' : X.B.I.GA) * x') by group, hxx]; group
    refine measure_mono_null hsub ?_
    have hγ : (δ' : X.B.I.GA)⁻¹ * δ ∈ rr_GF X.B.I := (rr_GF X.B.I).mul_mem ((rr_GF X.B.I).inv_mem (hD.1 δ'.2)) (hD.1 δ.2)
    have hne' : (δ' : X.B.I.GA)⁻¹ * δ ≠ 1 := by
      intro h1
      apply hne
      apply Subtype.ext
      rw [← mul_one (δ' : X.B.I.GA), ← h1]; group
    rw [Formalism.L2.SG.Pf.InHHLeaf.img_mul, measure_preimage_mul]
    exact hFD.disj _ hγ hne'
  have e2 : ∫ x in (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund), f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∑' δ : Dt, ∫ x in (fun y => (δ : X.B.I.GA) * y) '' X.B.fund, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) := by
    rw [hU] at hgFs' ⊢
    exact integral_iUnion_ae (fun δ => (hmeas δ).nullMeasurableSet) hdisj hgFs'
  have e3 : ∀ δ : Dt, ∫ x in (fun y => (δ : X.B.I.GA) * y) '' X.B.fund, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∫ y in X.B.fund, f y * Ph X u hK T ((δ : X.B.I.GA) * y) ∂(X.B.I.muA X.B.μf) := by
    intro δ
    have hpre : (fun y => (δ : X.B.I.GA) * y) ⁻¹' ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) = X.B.fund :=
      Set.preimage_image_eq _ (mul_right_injective (δ : X.B.I.GA))
    have h2 := (measurePreserving_mul_left (X.B.I.muA X.B.μf) (δ : X.B.I.GA)).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft (δ : X.B.I.GA)) (fun x => f x * Ph X u hK T x)
      ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund)
    rw [hpre] at h2
    rw [← h2]
    refine setIntegral_congr_fun hFD.meas fun y _ => ?_
    show f ((δ : X.B.I.GA) * y) * Ph X u hK T ((δ : X.B.I.GA) * y) = f y * Ph X u hK T ((δ : X.B.I.GA) * y)
    rw [hfinv _ (hD.1 δ.2) y]
  have hbound : ∑' δ : Dt, ∫⁻ y in X.B.fund, ‖f y * Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) ≠ ⊤ := by
    have hle : ∀ δ : Dt, ∫⁻ y in X.B.fund, ‖f y * Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) ≤
        ENNReal.ofReal C * ∫⁻ y in X.B.fund, ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) := by
      intro δ
      rw [← lintegral_const_mul (f := fun y => ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ) _ (hPm.comp (measurable_const_mul _)).enorm]
      refine lintegral_mono fun y => ?_
      rw [enorm_mul]
      refine mul_le_mul' ?_ le_rfl
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC y)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_mul_left, ← lintegral_tsum (f := fun (δ : Dt) y => ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ) (fun δ => (hPm.comp (measurable_const_mul _)).enorm.aemeasurable),
      Formalism.L2.SG.Pf.InHHLeaf.unfold_lint hFD (Srat X u) hS Dt hD Fs hFs (fun w => ‖Ph X u hK T w‖ₑ) hPm.enorm
        (fun s hs y => by simp only [hPinv s hs y])]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPI.2.ne
  have e4 : ∫ y in X.B.fund, f y * Pser X u hK Dt T y ∂(X.B.I.muA X.B.μf) =
      ∑' δ : Dt, ∫ y in X.B.fund, f y * Ph X u hK T ((δ : X.B.I.GA) * y) ∂(X.B.I.muA X.B.μf) := by
    have hfun : (fun y => f y * Pser X u hK Dt T y) = fun y => ∑' δ : Dt, f y * Ph X u hK T ((δ : X.B.I.GA) * y) := by
      funext y
      show f y * ∑' δ : Dt, Ph X u hK T ((δ : X.B.I.GA) * y) = _
      rw [tsum_mul_left]
    rw [hfun]
    exact integral_tsum (fun δ => (hfm.mul (hPm.comp (measurable_const_mul _))).aestronglyMeasurable) hbound
  have hm := (hin T Dt hD).2.2.1
  have eL : ⟪star φ, PuFun X u hK Dt T⟫_ℂ = ∫ y in X.B.fund, f y * Pser X u hK Dt T y ∂(X.B.I.muA X.B.μf) := by
    have e0 : PuFun X u hK Dt T = hm.toLp (Pser X u hK Dt T) := dif_pos hm
    rw [e0, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_star φ, hm.coeFn_toLp, hφf] with a h1 h2 h3
    rw [h1, h2, Pi.star_apply, h3, RCLike.inner_apply]
    rw [mul_comm]
    congr 1
    first
      | exact Complex.conj_conj (f a)
      | simp [Complex.star_def]
  rw [eL, e4, e1, e2]
  exact tsum_congr fun δ => (e3 δ).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableUnitaryQuotientHeightPowMulRapidlyDecr
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem integrable_quotHeight_pow_mul_norm_of_rapidDec : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (u : GA D A → ℂ), GlobalTheory.Grow.RapidDec A u → ∀ N : ℕ, Integrable (fun q : AutQ A => GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖) (autMeasure A m) := by
  intro D A m hm u hu N
  haveI := hm
  have : BorelSpace (GA D A) := ⟨rfl⟩
  set f : GA D A → ℝ := fun g => GlobalTheory.Grow.quotHeight A g ^ N * ‖u g‖ with hf
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) f := fun γ hγ g => by
    simp only [f, GlobalTheory.Grow.quotHeight_left A hγ, hu.left hγ]
  have hfc : Continuous f := ((GlobalTheory.Grow.continuous_quotHeight A).pow N).mul hu.continuous.norm
  have e : (fun q : AutQ A => GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖) = GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f := rfl
  rw [e]
  have hfd : IsFundamentalDomain (GQ A) (GlobalTheory.AutomorphicL2Unitary.stdDom (GQ A)) m := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ m
  haveI : IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.autMeasure A m) := ⟨by
    rw [GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hfd]
    exact GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol A m _ hm hfd⟩
  obtain ⟨C, hC⟩ := hu.decay N
  have hmeas : Measurable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f) := by
    refine measurable_from_quotient.2 ?_
    have h' : (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f ∘ Quotient.mk'') = f := funext fun g => hL.descend_mk g
    rw [h']
    exact hfc.measurable
  refine Integrable.of_bound hmeas.aestronglyMeasurable C (.of_forall fun q => ?_)
  have hq : 0 ≤ GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f q :=
    mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos A _).le N) (norm_nonneg _)
  rw [Real.norm_of_nonneg hq]
  show GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖ ≤ C
  rw [mul_comm]
  exact hC _

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqSetIntegralFundamentalDomain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem integral_autMeasure_eq_setIntegral : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (X : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) X ν → ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → AEStronglyMeasurable F ν → ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) F q ∂(GlobalTheory.AutomorphicL2Unitary.autMeasure V ν) = ∫ g in X, F g ∂ν := by
  intro D V ν X hν hX F hF _
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F := hF
  rw [GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTranslate
section
namespace I195MixedCoordinates_35474aefd184915ecb24a8bf

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_35474aefd184915ecb24a8bf

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HalfInvariance

theorem integral_translate {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure] (F : G → ℂ) (a : G) :
    ∫ x, F (x + a) ∂ν = ∫ x, F x ∂ν := by
  simp_rw [add_comm _ a]
  exact integral_add_left_eq_self (μ := ν) F a


set_option maxHeartbeats 1000000 in
theorem half_avg_heis_inv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S₀ T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S₀ T f → ℓ₀ (heisO ψ S₀ T u f) = ℓ₀ f) → ∀ H : AddSubgroup (Mx D T.rank ρ), (∀ x, x ∈ H ↔ ∀ i j, cA D e * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure], ∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 (heisO ψ S T u f) x.1) ∂ν = ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 f x.1) ∂ν := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hℓ₀ H hH _ _ ν _ u hu f hf
  have hee : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA]; exact he.2.1
  have horth : ∀ {x y : WO S T}, IsHalf (cA D e) x → IsHalf (cA D e) y → symplO S T x y = 0 :=
    fun hx hy => GlobalTheory.SplitScalar.symplO_eq_zero S T hee hx hy
  have hhalfR : ∀ {m n k : ℕ} {t : Mx D m n} (M : Matrix (Fin n) (Fin k) (AE D)), IsHalf (cA D e) t →
      IsHalf (cA D e) (HMul.hMul t M : Mx D m k) := fun M ht i j => by
    simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, ht i _]

  set a : Mx D T.rank ρ := (d.coordS T u).1 with ha_def
  set w : WO S₀ T := (d.coordS T u).2.1 with hw_def
  set b : Mx D T.rank ρ := (d.coordS T u).2.2 with hb_def
  have hu_eq : u = d.extX T a + d.ext0 T w + d.extY T b := ((d.coordS T).symm_apply_apply u).symm
  have ha : IsHalf (cA D e) a := hhalfR _ hu
  have hw : IsHalf (cA D e) w := hhalfR _ hu
  have hb : IsHalf (cA D e) b := hhalfR _ hu
  have hXa : IsHalf (cA D e) (d.extX T a) := hhalfR _ ha
  have hYb : IsHalf (cA D e) (d.extY T b) := hhalfR _ hb
  have h0w : IsHalf (cA D e) (d.ext0 T w) := hhalfR _ hw
  have hth : ∀ {g : WO S T → ℂ}, IsThetaFunO ψ S T g → ∀ v, IsThetaFunO ψ S T (heisO ψ S T v g) :=
    fun hg v => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg v
  set g₂ := heisO ψ S T (d.extY T b) f with hg₂
  set g₁ := heisO ψ S T (d.ext0 T w) g₂ with hg₁
  have hg₂t : IsThetaFunO ψ S T g₂ := hth hf _
  have hg₁t : IsThetaFunO ψ S T g₁ := hth hg₂t _
  have hsplit : heisO ψ S T u f = heisO ψ S T (d.extX T a) g₁ := by
    have hsum : IsHalf (cA D e) (d.ext0 T w + d.extY T b) := fun i j => by
      simp only [Matrix.add_apply, mul_add, h0w i j, hYb i j]
    rw [hu_eq, add_assoc, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth hXa hsum),
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth h0w hYb)]
  let v : VolM D T.rank ρ := ⟨μ, 𝓕, hμ⟩
  have key : ∀ x : H, ℓ₀ ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 (heisO ψ S T u f) x.1) = ℓ₀ ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 f (x + ⟨a, (hH a).2 ha⟩).1) := by
    intro x
    have hx : IsHalf (cA D e) x.1 := (hH x.1).1 x.2
    have hxa : IsHalf (cA D e) (x.1 + a) := fun i j => by
      simp only [Matrix.add_apply, mul_add, hx i j, ha i j]
    obtain ⟨c1, -, -, -, -⟩ := _root_.GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v g₁ hg₁t
    obtain ⟨-, -, c3, -, -⟩ := _root_.GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v g₂ hg₂t
    obtain ⟨-, c2, -, -, -⟩ := _root_.GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v f hf
    have e1 : (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 (heisO ψ S T u f) x.1 = (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 g₁ (x.1 + a) := by
      rw [hsplit]; exact c1 x.1 a
    have e2 : (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 g₁ (x.1 + a) = heisO ψ S₀ T w ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 g₂ (x.1 + a)) := c3 (x.1 + a) w
    have e3 : (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 g₂ (x.1 + a) = (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 f (x.1 + a) := by
      have hc2 : (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 (heisO ψ S T (d.extY T b) f) (x.1 + a) = ψ (symplO S T (d.extX T (x.1 + a)) (d.extY T b)) • (_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 f (x.1 + a) := c2 (x.1 + a) b
      rw [hg₂, hc2, horth (show IsHalf (cA D e) (d.extX T (x.1 + a)) from hhalfR _ hxa) hYb,
        AddChar.map_zero_eq_one, one_smul]
    have hmt : IsThetaFunO ψ S₀ T ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 g₂ (x.1 + a)) :=
      GlobalTheory.MixValues.mixS_theta D ψ hψ S S₀ T ρ d μ 𝓕 hμ g₂ hg₂t (x.1 + a)
    rw [e1, e2, hℓ₀ w hw _ hmt, e3]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  exact integral_translate ν (fun x : H => ℓ₀ ((_root_.I195MixedCoordinates_35474aefd184915ecb24a8bf.source d) T ψ μ 𝓕 f x.1)) _

end GlobalTheory.HalfInvariance
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactFiniteAdelicSubgroupIntegralOpen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem isCompact_of_integral_open (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) (K : Subgroup (GA D V)) (hKf : K ≤ GfC V)
    (hKi : ∀ k ∈ K, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v)
    (hU : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ K) :
    IsCompact (K : Set (GA D V)) := by
  haveI : Submodule.IsFullLattice D.host.E Λ :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ
  obtain ⟨U, hUo, hUK⟩ := hU
  have hGf : IsClosed ((GfC V : Subgroup (GA D V)) : Set (GA D V)) := by
    rw [GlobalTheory.AdelicU.GfC_eq]; exact GlobalTheory.AdelicU.isClosed_finPts _ _

  have hopen : IsOpen ((K.subgroupOf (GfC V)) : Set (GfC V)) := by
    refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) ?_ ?_
    · intro x hx
      exact Subgroup.mem_subgroupOf.2 (hUK _ (Subgroup.mem_subgroupOf.1 hx) x.2)
    · exact hUo.preimage continuous_subtype_val
  have hcl : IsClosed ((K.subgroupOf (GfC V)) : Set (GfC V)) := Subgroup.isClosed_of_isOpen _ hopen
  have hKcl : IsClosed (K : Set (GA D V)) := by
    have h := hcl.trans hGf
    convert h using 1
    ext g
    constructor
    · intro hg; exact ⟨⟨g, hKf hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact Subgroup.mem_subgroupOf.1 hx
  refine (GlobalTheory.AdelicU.isCompact_levelFin D.sp.cm.sig V.gram Λ).of_isClosed_subset hKcl ?_
  intro k hk
  refine GlobalTheory.AdelicU.mem_levelFin.2 ⟨?_, hKi k hk⟩
  have := hKf hk
  rw [GlobalTheory.AdelicU.GfC_eq] at this
  exact this

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.RedOne

theorem redFn_eq_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (PP : Pl D.host.E), Lev.finE V g ∈ Formalism.L2.DIV.St β → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V g) = 1 := by
  intro D V β g PP hS h1
  classical
  exact GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS
    (fun v hv => by rw [Finset.mem_singleton] at hv; subst hv; exact h1) (Finset.mem_singleton_self _)

end GlobalTheory.ChainOnto.RedOne
end

