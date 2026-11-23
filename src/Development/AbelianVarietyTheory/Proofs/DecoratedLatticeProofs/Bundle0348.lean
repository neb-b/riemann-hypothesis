module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0330
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFlatMapIndepUnfoldingStep
section
namespace I195MixedCoordinates_5d92264ce36df39087fad987

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_5d92264ce36df39087fad987

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlatIndep

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem mixT_indep_quasi {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {μ μ' : Measure (Mx D ρ S.rank)}
    {𝓕 𝓕' : Set (Mx D ρ S.rank)} (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) (hμ' : IsCovolOne (ratMx D ρ S.rank) μ' 𝓕')
    {f : WO S T → ℂ} (hq : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) :
    (_root_.I195MixedCoordinates_5d92264ce36df39087fad987.target d) S ψ μ' 𝓕' f = (_root_.I195MixedCoordinates_5d92264ce36df39087fad987.target d) S ψ μ 𝓕 f := by
  funext y w₀
  refine covolOne_integral_eq hμ hμ' _ ?_
  intro γ hγ ξ
  change heisO ψ S T (d.incX S (γ + ξ)) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 =
    heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0
  obtain ⟨δ, hδ⟩ : d.incX S γ ∈ ratMx D _ _ := ratMx_mul (rat_mem _) hγ
  have h := hq δ (d.incX S ξ + d.incAdj S y + d.inc0 S w₀)
  rw [show ratW T S δ = d.incX S γ from hδ] at h
  rw [HypDec.integrandT_eq, HypDec.integrandT_eq, map_add (d.incX S), add_assoc (d.incX S γ), add_assoc (d.incX S γ), h,
    ← mul_assoc, ← AddChar.map_add_eq_mul]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.symplOH_incX_incX,
    HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, zero_add, add_zero]
  rw [add_comm (symplOH S T (d.incX S γ) _), add_neg_cancel_right]

theorem evalAt_indep {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {μS μS' : Measure (Mx D W.rank ρ)} {𝓕S 𝓕S' : Set (Mx D W.rank ρ)}
    {μT μT' : Measure (Mx D σ V₀.rank)} {𝓕T 𝓕T' : Set (Mx D σ V₀.rank)}
    (hS : IsCovolOne (ratMx D W.rank ρ) μS 𝓕S) (hS' : IsCovolOne (ratMx D W.rank ρ) μS' 𝓕S')
    (hT : IsCovolOne (ratMx D σ V₀.rank) μT 𝓕T) (hT' : IsCovolOne (ratMx D σ V₀.rank) μT' 𝓕T')
    {Ψ : WO V W → ℂ} (hΨ : IsThetaFunO ψ V W Ψ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) :
    evalAt ψ dV dW μS' 𝓕S' μT' 𝓕T' Ψ x y = evalAt ψ dV dW μS 𝓕S μT 𝓕T Ψ x y := by
  change dW.mixT V₀ ψ μT' 𝓕T' (dV.mixS W ψ μS' 𝓕S' Ψ x) y =
    dW.mixT V₀ ψ μT 𝓕T (dV.mixS W ψ μS 𝓕S Ψ x) y
  rw [dV.mixS_indep hS hS' hΨ]
  exact congrFun (mixT_indep_quasi dW hT hT' (GlobalTheory.MixModel.Check.mixS_quasi dV μS 𝓕S hΨ x)) y

theorem flatAt_indep {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {μS μS' : Measure (Mx D W.rank ρ)} {𝓕S 𝓕S' : Set (Mx D W.rank ρ)}
    {μT μT' : Measure (Mx D σ V₀.rank)} {𝓕T 𝓕T' : Set (Mx D σ V₀.rank)}
    (hS : IsCovolOne (ratMx D W.rank ρ) μS 𝓕S) (hS' : IsCovolOne (ratMx D W.rank ρ) μS' 𝓕S')
    (hT : IsCovolOne (ratMx D σ V₀.rank) μT 𝓕T) (hT' : IsCovolOne (ratMx D σ V₀.rank) μT' 𝓕T')
    (νU : Measure (UX D ρ)) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) {Ψ : WO V W → ℂ} (hΨ : IsThetaFunO ψ V W Ψ) :
    flatAt ψ dV dW μS' 𝓕S' μT' 𝓕T' νU x y Ψ = flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y Ψ := by
  funext w
  unfold flatAt flatFun
  simp only [evalAt_indep dV dW hS hS' hT hT' hΨ]

theorem volU_eq {ρ : ℕ} (v v' : VolU D ρ) : v.ν = v'.ν :=
  (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.1 _ _ v.unit v'.unit

theorem flat_indep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s s' : StepBF ψ B J) f, IsThetaFunO ψ B.V J.W f → flatBF s f = flatBF s' f) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s s' : StepFB ψ J B) f, IsThetaFunO ψ J.W B.V f → flatFB s f = flatFB s' f := by
  intro D ψ
  refine ⟨fun ρ B J s s' f hf => ?_, fun σ J B s s' f hf => ?_⟩
  · unfold flatBF GlobalTheory.MixPer.flat
    rw [volU_eq s.vU s'.vU]
    exact flatAt_indep _ _ s'.vS.covol s.vS.covol s'.vT.covol s.vT.covol _ _ _ hf
  · unfold flatFB GlobalTheory.MixPer.flatLast
    rw [volU_eq s.vU s'.vU]
    exact flatAt_indep _ _ s'.vS.covol s.vS.covol s'.vT.covol s.vT.covol _ _ _ hf

end GlobalTheory.FlatIndep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainStepExactInnerProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.ExactNS

variable {D : D7}

theorem petersson_conj (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (X : Set (GA D V))
    (hX : IsFundamentalDomain (GQ V) X ν)
    (f g : GA D V → ℂ) (hf : ∀ γ ∈ GQ V, ∀ h, f (γ * h) = f h) (hg : ∀ γ ∈ GQ V, ∀ h, g (γ * h) = g h) :
    GlobalTheory.Cusp.petersson V ν (fun h => conj (f h)) (fun h => conj (g h)) = conj (Lift.pet ν X f g) := by
  haveI := hν
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (fun h => conj (f h) * conj (conj (g h))) := fun γ hγ h => by
    simp only [hf γ hγ, hg γ hγ]
  change ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => conj (f h) * conj (conj (g h))) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _
  rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]
  unfold Lift.pet
  rw [← integral_conj]
  simp only [map_mul]

theorem up_conj {c : Com D} {s s' : PiLocalization₂ D} {w : Twist D} {k : ℕ} (p : Step c s s') (hp : IsStep w (k + 1) p)
    (hν : s.ν.IsHaarMeasure) (hX : IsFundamentalDomain (GQ s.V) s.fd s.ν) (φ : PolF D s'.V.rank s.V.rank)
    (F : GA D s.V → ℂ) (hF : ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g) :
    GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) = fun h => conj (p.up φ F h) := by
  haveI := hν
  funext h
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := hp.theta φ
  have hθl : ∀ γ ∈ GQ s.V, ∀ g, thetaKO p.ω (γ * g) h (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro γ hγ g
    have e : ((γ * g, h) : GA D s.V × GA D s'.V) = (γ, 1) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut γ hγ 1 (one_mem _) _ (hp.weil.om_pres _ _ hΦ)
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) (fun g => thetaKO p.ω g h (p.pt φ) * conj (F g)) := fun γ hγ x => by
    simp only [hθl γ hγ, hF γ hγ]
  simp only [GlobalTheory.Core.Rk.IP.up, Step.up]
  change ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ s.V) _ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ s.V) s.ν = _
  rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]
  rw [← integral_conj]
  simp only [map_mul, Complex.conj_conj]

theorem up_leftInv {c : Com D} {s s' : PiLocalization₂ D} {w : Twist D} {k : ℕ} (p : Step c s s') (hp : IsStep w (k + 1) p)
    (φ : PolF D s'.V.rank s.V.rank) (F : GA D s.V → ℂ) : ∀ γ ∈ GQ s'.V, ∀ h, p.up φ F (γ * h) = p.up φ F h := by
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := hp.theta φ
  have hθr : ∀ g, ∀ γ ∈ GQ s'.V, ∀ h, thetaKO p.ω g (γ * h) (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro g γ hγ h
    have e : ((g, γ * h) : GA D s.V × GA D s'.V) = (1, γ) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut 1 (one_mem _) γ hγ _ (hp.weil.om_pres _ _ hΦ)
  intro γ hγ h
  simp only [Step.up, hθr _ γ hγ]

theorem stepExactNS : ∀ D : D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D → SoftQ D → QPeel D → LevInt D → StepExactNS D := by
  intro D hHF hSoft hPeel hLev hgap c w hw k hk s s' hs hs' p hp ipD ip hMet m X hmX mR hmR φ v hRC u₁ u₂ B hB hQ hNS l hl
  have hc : c.Is := hw.com
  obtain ⟨hr, -, hsF⟩ := id hs
  obtain ⟨hr', -, hs'F⟩ := id hs'
  have hv : PiTensorProduct.tprod ℂ v ∈ s.KF := Submodule.subset_span ⟨v, hRC.1, rfl⟩
  by_cases h0 : PiTensorProduct.tprod ℂ v = 0
  · have hz : ∀ g, zReal p m X φ v g = 0 := by
      intro g
      have hp0 := hMet.pure v v
      simp only [h0, map_zero, LinearMap.zero_apply] at hp0
      obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 hp0.symm
      have h0τ : ((v τ : s.M.sm τ) : s.M.H τ) = 0 := inner_self_eq_zero.1 hτ
      simp only [zReal]
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [h0τ, inner_zero_left])]
      simp
    simp [h0, hz, Step.up, Lift.pet]
  have hF₁ : PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v) ≠ 0 := fun h =>
    hB.1 ((hSoft c w hw k hk.le s hs).2.2.1 u₁ _ h0 h)
  have hparF : ParFun c s (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) B := hB.2 _ hF₁
  have hFlat := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw k hk.le s hs hr
  obtain ⟨cA, a, hcA, hcart, hJ, hmaj, hmaj_eq, hA0⟩ := GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc k hk.le _ hsF
  obtain ⟨-, -, -, hcartB, -, -, -, -⟩ := GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc (k + 1) hk _ hs'F
  obtain ⟨hwitt, htwo⟩ := GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split D c (k + 1) _ hk hs'F
  obtain ⟨hfock, -, hunrT⟩ := _root_.GlobalTheory.ChainTw.fock_sph_tw D hgap c w hw k hk s s' hs hs' p hp
  set F₁ := PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v) with hF₁def
  set F₂ := PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v) with hF₂def
  have hu1 : (fun g => conj (F₁ g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 ⟨u₁.1, hFlat u₁.2⟩ _ hv
  have hu2 : (fun g => conj (F₂ g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 ⟨u₂.1, hFlat u₂.2⟩ _ hv
  have hrk0 : s.V.rank = D.R.rankY k := hsF.rank
  have hrk1 : s'.V.rank = D.R.rankY (k + 1) := hs'F.rank
  have hr1 : 1 ≤ s.V.rank := by
    rw [hrk0]; simp only [Ranks.rankY, Ranks.r]; have := D.R.two_le_m; omega
  have ht2 : 2 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hrk : s'.V.rank = s.V.rank + D.R.t := by rw [hrk1, hrk0]; simp only [Ranks.rankY]; ring
  have hPair : GlobalTheory.Core.Rk.IP.Pair c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
      m X :=
    { setting := ⟨hr1, by omega, hrk, hc.inf, hsF.sigOK, hcA, hcart, hcartB, hJ⟩
      maj := hmaj
      maj_eq := hmaj_eq
      weil := hp.weil
      covol := hmX }
  have hUnr : GlobalTheory.Core.Rk.IP.Unram c.ψ s.V s'.V (c.chT (k + 1)) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) :=
    ⟨hsF.selfDual, hs'F.selfDual, fun w _ h2 => htwo w h2, hunrT, (hfock φ).2.1, (hfock φ).2.1⟩
  have hsph : GlobalTheory.Core.Rk.IP.SphFun s.V s.Λ c.S (fun g => conj (F₂ g)) := by
    obtain ⟨-, hoffS, -⟩ := GlobalTheory.ChainOnto.LevelFacts.levFacts D c hc k hk.le _ hsF
    have hT := (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 (hFlat u₂.2))
    intro v' hv' κ hκ g
    obtain ⟨hκL, hκχ⟩ := hoffS v' hv' κ hκ
    have e : F₂ = PiTensorProduct.lift.symm (u₂ : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v := by
      rw [PiTensorProduct.lift_symm]; rfl
    simp only [e]
    have hlev := hT.lev v _ hκL g
    rw [hκχ, one_mul] at hlev
    exact congrArg (starRingEnd ℂ) hlev
  have hIM : IsMajOf c s a := ⟨hmaj, hmaj_eq⟩
  obtain ⟨s₁, hs₁, hLI⟩ := hLev hgap c w hw k hk s s' hs hs' p hp ipD ip hMet m X hmX mR hmR φ v hRC a hIM
  obtain ⟨hLint, hLeq⟩ := hLI u₁ u₂
  have hint : ∃ z : ℝ, z < (D.R.t : ℝ) / 2 ∧ IntegrableOn (GlobalTheory.Core.Rk.IP.integrand p.ω s.ν m X s.Λ a (p.pt φ)
      (p.pt φ) (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) z) (GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S) s.ν := by
    refine ⟨max s₁ ((D.R.t : ℝ) / 2 - 1 / 2), max_lt hs₁ (by linarith), ?_⟩
    exact (hPeel hgap c w hw k hk s s' hs hs' p hp m X hmX a hIM u₁ u₂ φ hQ _ hv _ hv _
      (lt_of_lt_of_le (by linarith) (le_max_right _ _)) (hLint _ (le_max_left _ _))).1
  have hPt := hPeel hgap c w hw k hk s s' hs hs' p hp m X hmX a hIM u₁ u₂ φ hQ _ hv _ hv ((D.R.t : ℝ) / 2)
    (by linarith) (hLint _ hs₁.le)
  obtain ⟨-, -, -, hval⟩ := hHF c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
    m X hPair ht2 (Or.inr hwitt) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) (hfock φ).1 (hfock φ).1 hUnr s.ν s'.ν hsF.haar hs'F.haar
    _ hu1 _ hu2 B hparF hsph hNS hint
  have key := hval l hl
  have hsZ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (((D.R.t : ℝ) / 2 : ℝ) : ℂ) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, hrk]; push_cast; ring
  have hI : ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) g ∂s.ν =
      locQ c w k * ((∫ g, zReal p m X φ v g ∂mR) * conj (ip u₁ u₂)) := by
    rw [← hLeq, ← hPt.2 rfl]
    change _ = ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, flatInt p m X a φ F₁ F₂ (((D.R.t : ℝ) / 2 : ℝ) : ℂ) g ∂s.ν
    congr 1
    funext g
    rw [← hsZ]
    exact (GlobalTheory.Core.Rk.IP.integrand_sZero (A := s.V) (B := s'.V) p.ω s.ν m X s.Λ a (p.pt φ) (p.pt φ) _ _ g).symm
  have hFl : ∀ F : GA D s.V → ℂ, (fun g => conj (F g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA →
      ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g := fun F hF γ hγ g => by
    simpa using congrArg (starRingEnd ℂ) (hF.1.1.left γ hγ g)
  rw [ExactNS.up_conj p hp hsF.haar hsF.fund φ F₁ (hFl F₁ hu1), ExactNS.up_conj p hp hsF.haar hsF.fund φ F₂ (hFl F₂ hu2),
    ExactNS.petersson_conj s'.V s'.ν hs'F.haar s'.fd hs'F.fund _ _ (ExactNS.up_leftInv p hp φ F₁)
      (ExactNS.up_leftInv p hp φ F₂), hI] at key
  have key' := congrArg (starRingEnd ℂ) key
  rw [Complex.conj_conj] at key'
  change Lift.pet s'.ν s'.fd _ _ = _
  rw [key']
  simp only [dS, map_mul, Complex.conj_conj]
  ring

end GlobalTheory.ChainTw.ExactNS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftDatumIsNonzeroFockVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftFockVac

theorem levVec_fockVac : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → l2 μ 𝓧 f f ≠ 0 ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧ ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) f := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ
  have hθf := (GlobalTheory.FinZeta.levVec_vacFin R F i t σ s P cμ cη m ω BW f₀ f c io h).1
  obtain ⟨hC, -, -, -, -, hW, -, hlv, -, -, -⟩ := h
  obtain ⟨⟨hψ, hv⟩, e, he, hth⟩ := hlv
  have hinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hinf' : infPart D (cA D (cA D e)) = 0 := by
    rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.PlaceVec.idemSum_infPart he
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hr : (Wc D i).rank ≤ (Vc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)
  have hf0 : f ≠ 0 := by
    have h00 : f₀ ≠ 0 := by
      rintro rfl
      obtain ⟨⟨p, hp⟩, h2⟩ := hv.norm
      have := h2 p hp
      simp [nrm2] at this
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
    rw [hall Tm hTm]
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
    have hee : e * e = e := ho.idem
    obtain ⟨-, hFS, -⟩ := hC.lev.βV i
    obtain ⟨-, hFT, -⟩ := hC.lev.βW i
    have hSB := GlobalTheory.FinZeta.isSBHalf_levDatum D _ _ _ _ _ _ (R.datWp i P) (R.Q t) m _ e hS hT hFS hFT he
    refine GlobalTheory.PlaceModelInj.placeModel_ne_zero D R.ψ _ _ _ _ (cA D e) f₀ _ Tm hψ hS hT ho.conj.idem
      (by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he.2]) hinf hTm h00 hSB ?_
    obtain ⟨x, hx, hx'⟩ := GlobalTheory.AdjDatumNe.exists_half_frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) hee
      (GlobalTheory.AdjDatumNe.rectOne _ _ _)
    obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
    have hint : IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) := by
      rw [hx']; exact GlobalTheory.AdjDatumNe.isIntM_smul_rectOne hi _ _
    have hred : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t,
        redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _ := by
      intro PP hPP
      rw [hx', GlobalTheory.AdjDatumNe.redM_smul_rectOne hi PP (hres PP hPP)]
      rfl
    intro hz
    have := congrFun hz x
    rw [if_pos ⟨hx, hint⟩, GlobalTheory.PlaceDatum.omegaG_congr _ m _ (fun PP => GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _)
      fun PP hP => hred PP (Finset.mem_union_left _ hP),
      GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ (y' := fun PP => GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _)
      fun PP hP => hred PP (Finset.mem_union_right _ hP)] at this
    exact mul_ne_zero (GlobalTheory.Chain.StepVac.omegaG_rectOne hr _ m) (GlobalTheory.Chain.StepVac.omegaQ_rectOne le_rfl hr _ m _) this
  refine ⟨?_, hθf, fun τ => GlobalTheory.RawLift.isCartanInv_one_of_onb (hC.models.BV i τ), fun τ => ?_⟩
  · have h1 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hW.std hθf hf0 hμ
    have e1 : l2 μ 𝓧 f f = GlobalTheory.RawLift.thetaIP μ 𝓧 f f := by
      show (∫ w in 𝓧, f w * starRingEnd ℂ (f w) ∂μ) = ∫ w in 𝓧, star (f w) * f w ∂μ
      congr 1
      funext w
      rw [mul_comm]
      rfl
    rw [e1]
    exact h1
  · exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hv.inf hinf hinf' hth hv.theta hθf (hv.fock τ)

end GlobalTheory.LiftFockVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairDefinitePlaceCharacterDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftPair_definite_place_character_data : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), (∃ cA a, Defin R.θ (Vc D i) cA a) ∧ Places (Vc D i) (R.βV i) (R.Pg ∪ R.Q t) ∧ under (R.Pg ∪ R.Q t) = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t ∧ GlobalTheory.LFun.UnrOff (F := D.host.F) (E := D.host.E) (chiV R i t) (↑(under (D := D) (R.Pg ∪ R.Q t))) ∧ (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) ∧ (Wc D i).SigOK ∧ (Wc D i).rank = D.R.r ∧ 0 < D.R.r ∧ (Vc D i).rank = D.R.r + D.R.t ∧ D.R.r + 5 ≤ D.R.t ∧ R.ΛV i = GlobalTheory.AdelicU.frameLat (Vc D i) ∧ R.ΛW i = GlobalTheory.AdelicU.frameLat (Wc D i) := by
  exact @GlobalTheory.DownPair.pair_data
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySupportedSplitPlacesEqProdLocalParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitDecomp

open GlobalTheory.SplitCut GlobalTheory.FinPl

variable {D : D7}

theorem real_idem_mul (y : AE D) (hy : infPart D y = 0) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * y = 0 := by
  refine key_gen (Module.finBasis D.host.F D.host.E) _ y fun k => ?_
  have h1 : fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) = 0 := by
    rw [← GlobalTheory.InfZeroFinSum.repr_map_id (Module.finBasis D.host.F D.host.E) (fstA D.host.F) y k]
    have : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) y = 0 := hy
    rw [this, map_zero, Finsupp.zero_apply]
  refine baseAdele_ext_infinite_finite ?_ ?_
  · rw [map_mul, h1, mul_zero, map_zero]
  · rw [map_mul, map_zero]
    exact zero_mul _

theorem entry_memAt (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpAt V P) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ idAt D P := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idAt D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idAt D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V g i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2


set_option maxHeartbeats 800000 in
open GlobalTheory.LocWeil.PlaceIdem in
theorem prod_of_grpAt : ∀ (D : D7) (V : HSp D) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ g ∈ GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v), ∃ h : Fin n → GA D V, (∀ i, SuppAt (q i).e V (h i)) ∧ g = ((List.finRange n).map h).prod := by
  intro D V n k _ _ _ _ q hv g hg
  set E : Fin n → AE D := fun i => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (q i).v) with hEdef
  have hE : ∀ i, (q i).e + cA D (q i).e = E i := fun i => by
    obtain ⟨ε, hε, h⟩ := (q i).above
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ i, E i * E i = E i := fun i => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ i, cA D (E i) = E i := fun i => cA_algebraMap _
  have hEo : ∀ i i', i ≠ i' → E i * E i' = 0 := fun i i' hii => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hii (hv h)), map_zero]
  choose h hh using fun i => cut_exists V g (E i) (hEE i) (hEc i)
  set M := mt V g with hM
  refine ⟨h, fun i a b => ?_, ?_⟩
  · rw [hE i, hh i]
    exact idempotent_mul_cut_sub_one_entry _ (hEE i) M a b
  · apply mt_injective
    rw [mt_list_prod V h E M hh hEo _ (List.nodup_finRange n)]
    have hsum : ((List.finRange n).map E).sum = ∑ i, E i := (Fin.sum_univ_def E).symm
    rw [hsum]
    refine exists_widePullback_of_iteratedLine _ M fun a b => ?_
    have hm := entry_memAt V _ g hg a b
    unfold idAt at hm
    obtain ⟨hinf, hoff⟩ := Ideal.mem_inf.mp hm
    rw [Ideal.mem_iInf] at hoff
    have h1 := key (fun i => (q i).v) hv ((M - 1) a b) (fun u hu =>
      (RingHom.mem_ker).mp (hoff ⟨u, fun ⟨i, hi⟩ => hu ⟨i, hi.symm⟩⟩))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_one, map_sum] at h1
    have h2 := real_idem_mul ((M - 1) a b) ((RingHom.mem_ker).mp hinf)
    have h3 : (1 - ∑ i, E i) = (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) - ∑ i, E i) +
        algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) := by ring
    rw [h3, add_mul, h1, h2, add_zero]

end GlobalTheory.SplitDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeCharAtUniformizerIdeleEqValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedHeckeChar_at_uniformizerIdele_eq_value : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ χ : (AE D)ˣ →* Circle, GlobalTheory.LFun.UnrAt (F := D.host.F) χ PP → Circle.toUnits (χ x) = GlobalTheory.LFun.val (F := D.host.F) χ PP := by
  first | exact @GlobalTheory.LocUnifVal.value_eq_val | exact GlobalTheory.LocUnifVal.value_eq_val | (intros; apply GlobalTheory.LocUnifVal.value_eq_val <;> assumption)
end

