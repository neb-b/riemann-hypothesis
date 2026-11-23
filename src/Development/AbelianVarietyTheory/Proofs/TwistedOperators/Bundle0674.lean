module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTuplesOneOrbitModUniformizerPower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiAnnihilatorPieceCompactOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0652
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarTraceConjEqConstMulKernelImage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0671

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentEqKappaLatticePoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LineComp

theorem star_smul_mem_span : ∀ (D : D7) (n : ℕ) (I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), D.host.AAbar * I ≤ D.host.AA * J → ∀ a ∈ D.host.AA, ∀ s ∈ idLat I Λ, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat J Λ, y = a' • s'} := by
  intro D n I J Λ hIJ a ha s hs
  have hsa : star a ∈ D.host.AAbar := by
    have e : star a = D.host.conj a := by
      first
      | exact GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.bridge_star_holds D.R D.host a
      | exact Formalism.BasicNotions.Examples₂.star_eq_conj D.host a
      | (apply D.host.φ₀.injective
         have h1 : D.host.φ₀ (D.host.conj a) = starRingEnd ℂ (D.host.φ₀ a) := Formalism.HC.HostAx.conjE_apply _ _ _
         rw [h1]
         haveI := D.host.isCMField_hostE
         exact IsCMField.complexEmbedding_complexConj _ _ _)
    rw [e]; exact Formalism.L2.Pj.conj_mem_AAbar D ha
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, y, hy, rfl⟩ := hx
    have hm : star a * c ∈ (D.host.AA * J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      hIJ (FractionalIdeal.mul_mem_mul hsa hc)
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hm
    rw [smul_smul]
    have key : ∀ z ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) * (J : Submodule (𝓞 D.host.E) D.host.E)),
        z • y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat J Λ, y = a' • s'} := by
      intro z hz
      induction hz using Submodule.mul_induction_on' with
      | mem_mul_mem a' ha' j hj =>
        exact Submodule.subset_span ⟨a', ha', j • y, Submodule.subset_span ⟨j, hj, y, hy, rfl⟩, by rw [smul_smul]⟩
      | add x x' _ _ ihx ihy => rw [add_smul]; exact Submodule.add_mem _ ihx ihy
    exact key _ hm
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem stairRatio_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (σ : ℕ), D.host.AAbar * (G.pl.stA sc ^ (σ + 2) * (G.pl.stAbar sc ^ (σ + 2))⁻¹) ≤ D.host.AA * (G.pl.stA sc ^ (σ + 1) * (G.pl.stAbar sc ^ (σ + 1))⁻¹ * shiftId G) := by
  intro D T L sc G σ
  have hA : (D.host.AAbar : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h] at h1
    simp at h1
  refine le_of_eq ?_
  simp only [shiftId, Places.stA, Places.stAbar, GridData.modul]
  generalize D.host.AA = a at *
  generalize D.host.AAbar = b at *
  generalize ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = n
  generalize ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = m
  rw [pow_succ (a * n⁻¹) (σ + 1), pow_succ (b * m⁻¹) (σ + 1), mul_inv (_ ^ (σ + 1)), mul_inv b, inv_inv]
  calc b * ((a * n⁻¹) ^ (σ + 1) * (a * n⁻¹) * (((b * m⁻¹) ^ (σ + 1))⁻¹ * (b⁻¹ * m)))
      = (b * b⁻¹) * (a * ((a * n⁻¹) ^ (σ + 1) * ((b * m⁻¹) ^ (σ + 1))⁻¹ * (m * n⁻¹))) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hA, one_mul]

theorem main : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀,
    ∃ w ∈ lineLat F ρ, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 = (F.lnk ρ).κ _ w := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  refine ⟨_, ?_, (_root_.GlobalTheory.KapAdjLine.kap_starAdj D hq T L μ0 hL sc G W M hM F hF ρ _).symm⟩
  cases ρ with
  | zero => exact _root_.GlobalTheory.LineZero.adj_mem_lineLat D hq T L μ0 hL sc G W M hM F hF h u hu
  | succ σ =>
    exact _root_.GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO D _ _ _ _ _ _ (star_smul_mem_span D _ _ _ _ (stairRatio_le G σ)) _
      (_root_.GlobalTheory.AscFin.BoxBF.lineComp_mem_latO D hq T L μ0 hL sc G W M hM F hF (σ + 1) h u hu)

end GlobalTheory.LineComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepOrbitAtBadPlaceEqCongruenceTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.CosetBF

theorem besselOrbit_at_badPlace_eq_congruenceTranslate : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), ∀ (u : UX D ρ), ∀ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a) → ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) k ⬝ xZero (F.dJ ρ h) - mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1)) := by
  intro D hQ T L μ0 hL sc G W M hM F hF ρ h v hv g hg u a ha hoff
  cases ρ with
  | zero =>
    exact ⟨1, one_mem _, one_mem _, fun i j => j.elim0⟩
  | succ σ =>
    obtain ⟨k, _, _, _, _, p, β, ι, ι', s, t, hpv, hidem, hlat, hι, hι', hdisj, hX, hΦ, hA⟩ :=
      _root_.GlobalTheory.AscFin.FrameBF.frame_bf D hQ T L μ0 hL sc G W M hM F hF σ h v hv
    obtain ⟨ha1, ha2⟩ := hA a ha
    subst hpv
    obtain ⟨k₀, hk₀, hoff'⟩ := _root_.GlobalTheory.AscFin.OneOrbitAt.one_orbit D k p _ σ β (xZero (F.dJ (σ + 1) h)) ι ι' s t (G.pl.depth sc p.v)
      (G.pl.depth_pos sc _) hι hι' (fun a b hab => absurd hab (hdisj a b)) hX hΦ g hg u a ha1 ha2 hoff
    have hsd : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
      (G.sp.V_is (2 * (σ + 1) + 1) 0 (by omega) (by omega) (Nat.zero_le _)).sd
    refine ⟨β.gl _, _root_.GlobalTheory.LevFrame.gl_mem_lev D hQ T L μ0 hL sc G W M hM (.grid (2 * (σ + 1) + 1) 0) hsd p.v hv k p rfl hidem _ β hlat k₀ hk₀, ?_, hoff'⟩
    exact ((GlobalTheory.FrameAt.frame_facts D k p _ _ β).1 _).2 ⟨_, rfl⟩

end GlobalTheory.CosetBF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiMixedPiecesAdmissible
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PcBF

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem symplO_neg_right' (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = - symplO S T x y := by
  have := symplO_add_right' S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right'] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem ann_of_mem {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (Γ Γ' : AddSubgroup (WO V W)) {a' : Mx D W.rank ρ}
    (ha' : a' ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₂) :
    ∀ a ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₁, ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1 := by
  intro a ha
  induction ha' using AddSubgroup.closure_induction with
  | mem b hb => exact hb.2 a ha
  | zero => rw [map_zero, symplO_zero_right', AddChar.map_zero_eq_one]
  | add b c _ _ hb hc => rw [map_add (f := _), symplO_add_right', AddChar.map_add_eq_mul, hb, hc, one_mul]
  | neg b _ hb => rw [map_neg, symplO_neg_right', AddChar.map_neg_eq_inv, hb, inv_one]

end GlobalTheory.PcBF

namespace GlobalTheory.PcBF

theorem pieces_bf : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (pcBF W F ρ h).Is (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ ∧ Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  set_option maxHeartbeats 0 in
    intro D hD T L μ0 hL sc G W M hM F hF ρ h
    refine ⟨⟨_root_.GlobalTheory.AscFin.finLat_pcBF_A₁ D hD T L μ0 hL sc G W M hM F hF ρ h, ⟨?_, (_root_.GlobalTheory.AnnPiece.pcBF_A₂_compact_open D hD T L μ0 hL sc G W M hM F hF ρ h).1, (_root_.GlobalTheory.AnnPiece.pcBF_A₂_compact_open D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
      (_root_.GlobalTheory.BesselPieceB.finLat_pcBF_B D hD T L μ0 hL sc G W M hM F hF ρ h).1, (_root_.GlobalTheory.BesselPieceB.finLat_pcBF_B D hD T L μ0 hL sc G W M hM F hF ρ h).2, ?_, ?_,
      (_root_.GlobalTheory.PcBFDual.dualB D hD T L μ0 hL sc G W M hM F hF ρ h).1, (_root_.GlobalTheory.PcBFDual.dualB D hD T L μ0 hL sc G W M hM F hF ρ h).2,
      _root_.GlobalTheory.AscFin.UniBF.psiUni_pcBF D hD T L μ0 hL sc G W M hM F hF ρ h, (_root_.GlobalTheory.AscFin.CorePiece.core_fin_vac D hD T L μ0 hL sc G W M hM F hF ρ h).1, (_root_.GlobalTheory.AscFin.CorePiece.core_fin_vac D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
      _root_.GlobalTheory.AscFin.pcBF_splits D hD T L μ0 hL sc G W M hM F hF ρ h⟩
    · intro a' ha'
      induction ha' using AddSubgroup.closure_induction with
      | mem b hb => exact hb.1
      | zero => intro i j; simp only [Matrix.zero_apply]; exact zero_mem _
      | add b c _ _ hb hc => intro i j; simp only [Matrix.add_apply]; exact add_mem (hb i j) (hc i j)
      | neg b _ hb => intro i j; simp only [Matrix.neg_apply]; exact neg_mem (hb i j)
    · intro a ha
      exact ⟨fun h1 a' h2 => ann_of_mem _ _ _ _ _ h2 a h1, _root_.GlobalTheory.AscFin.BidualLattice.bidual_pcBF D hD T L μ0 hL sc G W M hM F hF ρ h a ha⟩
    · intro a' ha'
      exact ⟨fun h2 a h1 => ann_of_mem _ _ _ _ _ h2 a h1, fun H => AddSubgroup.subset_closure ⟨ha', fun a h1 => H a h1⟩⟩

end GlobalTheory.PcBF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainPreStepsExistOfDepthCongruence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate

namespace GlobalTheory.CoreOnto.PreSteps

theorem preOK (hDF : DepFixed) : PreOK := by
  intro D hQ hS T L μ0 hL sc hc G W Mv hM i hi r r' hr hr' v M M'
  obtain ⟨hth, -, -, hbij, hmeas, hweil⟩ := _root_.GlobalTheory.ExchPf.exchLaw D W.ψ (G.V (.core i)) (G.V (.core (i + 1))) W.ψ_std
  have hom := W.om_is (.core i) (show i + 1 ≤ D.R.m by omega)
  obtain ⟨hcS, hcT⟩ := G.chr_core (i := i) (by omega)
  rw [hcS, hcT] at hom
  obtain ⟨ω, hω, hωx⟩ := hweil _ _ _ hom
  obtain ⟨x₀, hx₀⟩ := _root_.GlobalTheory.OntoModPf.ontoModEx D hQ T L μ0 hL sc G W Mv hM i hi
  obtain ⟨f, hvac, hsph, hcos⟩ := _root_.GlobalTheory.CoreOnto.datumEx D hQ T L μ0 hL sc G W Mv hM i hi r r' hr hr' _ _ (r.mod M) (r'.mod M') x₀ hx₀.1
  have hRL := (_root_.GlobalTheory.ReLatPf.reLatLaw_holds D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r'
  have hinj : Function.Injective (exch (G.V (.core i)) (G.V (.core (i + 1)))) := by
    intro F₁ F₂ h
    funext w
    obtain ⟨x, rfl⟩ := hbij.2 w
    exact congrFun h x
  refine ⟨ω, f, ⟨(hRL.2 _ _ ω).2 hω, fun τ => ?_, hvac, hsph, ?_, ?_⟩, hωx, fun φ => (hcos φ).1⟩
  · show GlobalTheory.EvenOnto.UpPair (sLen D - 1) (Node.par D sc.cGap (.core i) τ) (Node.par D sc.cGap (.core (i + 1)) τ)
      (-(cen D sc.cGap τ (D.R.m - i) : ℚ)) (-(cen D sc.cGap τ (D.R.m - i) : ℚ))
    rw [hc]
    exact _root_.GlobalTheory.CoreOntoPar.parOK_core D hS i hi τ
  · intro φ κ hκ κ' hκ'
    have hD := (hcos φ).1
    have hthF := (hth _).2 hD.1
    exact hinj ((hωx _ hthF κ κ').symm.trans (hDF D hQ T L μ0 hL sc G W Mv hM i hi (.core i) (Or.inr rfl) _ hD κ hκ κ' hκ'))
  · intro m X hX φ g hg hgb
    by_contra hne
    apply hgb
    have hD := (hcos φ).1
    have hthF := (hth _).2 hD.1
    obtain ⟨m', X', hX', heq⟩ := hmeas m X hX
    have hne' : (∫ w in X', W.om (.core i) (1, g) (exch (G.V (.core i)) (G.V (.core (i + 1)))
        (GlobalTheory.Chain.ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ)) w *
        conj (exch (G.V (.core i)) (G.V (.core (i + 1)))
          (GlobalTheory.Chain.ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ) w) ∂m') ≠ 0 := by
      have h1 := hωx _ hthF g 1
      rw [map_one] at h1
      rw [h1, ← heq]
      exact hne
    have hsd := (G.sp.P_is i (by omega)).sd
    have hstab : ∀ w ∉ G.pl.S0, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram w g ∈
        GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (G.Λ (.core i)) w := by
      intro w hw
      have h0 := hg w hw
      have h1 : GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram w g ∈
          GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (GlobalTheory.AdelicU.frameLat r.sp) w := h0
      have hΛ : GlobalTheory.AdelicU.frameLat r.sp = scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) (G.Λ (.core i)) := hr
      rw [hΛ, (_root_.GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual D (G.V (.core i)) (G.Λ (.core i)) hsd i).2.1 w] at h1
      exact h1
    have hfin := _root_.GlobalTheory.CosSupport.cosSupp D hQ T L μ0 hL sc G W Mv hM i hi x₀ hx₀ _ (hcos φ) m' X' hX' g hstab hne'
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (G.V (.core i))).1 g
    refine ⟨⟨a, ha⟩, k, Subgroup.mem_inf.2 ⟨hk, ?_⟩, rfl⟩
    have ha' : Lev.finE (G.V (.core i)) a = 1 := by
      have h : finHom (G.V (.core i)) a = 1 := ha
      show Formalism.UG.bc (Lev.swapAE D) (finHom (G.V (.core i)) a) = 1
      rw [h, map_one]
    show Lev.finE (G.V (.core i)) k ∈ G.levCong (.core i)
    rw [map_mul, ha', one_mul] at hfin
    exact hfin

end GlobalTheory.CoreOnto.PreSteps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsProdSinglePlacePiecesOfSuppAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceCut

theorem idem_mul {D : D7} {e e' : AE D} {w w' : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') : (w = w' → e * e' = e) ∧ (w ≠ w' → e * e' = 0) := by
  have i0 : infPart D e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) h).1
  have a1 : GlobalTheory.RowRep.piAt w e = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h).1
  have a2 : ∀ u, u ≠ w → GlobalTheory.RowRep.piAt u e = 0 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h).2
  have b1 : GlobalTheory.RowRep.piAt w' e' = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h').1
  have b2 : ∀ u, u ≠ w' → GlobalTheory.RowRep.piAt u e' = 0 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h').2
  have i1 : infPart D (e * e') = 0 :=
    ((infPart D).map_mul e e').trans ((congrArg (· * infPart D e') i0).trans (zero_mul _))
  refine ⟨fun hw => ae_ext (i1.trans i0.symm) fun u => ?_, fun hw => ae_ext (i1.trans (infPart D).map_zero.symm) fun u => ?_⟩
  · change GlobalTheory.RowRep.piAt u (e * e') = GlobalTheory.RowRep.piAt u e
    rw [RingHom.map_mul]
    by_cases hu : u = w
    · subst hu; subst hw; rw [b1, mul_one]
    · rw [a2 u hu, zero_mul]
  · change GlobalTheory.RowRep.piAt u (e * e') = GlobalTheory.RowRep.piAt u 0
    rw [RingHom.map_mul, RingHom.map_zero]
    by_cases hu : u = w
    · subst hu; rw [b2 u hw, mul_zero]
    · rw [a2 u hu, zero_mul]

theorem mul_conj_zero {R ι : Type} [CommRing R] (c : R →+* R) (P : Finset ι) (a : ι → R)
    (h1 : ∀ i ∈ P, a i * a i = a i) (h2 : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → a i * a j = 0)
    (h0 : (∑ i ∈ P, a i) * c (∑ i ∈ P, a i) = 0) : ∀ i ∈ P, ∀ j ∈ P, a i * c (a j) = 0 := by
  have k : ∀ i ∈ P, a i * ∑ j ∈ P, a j = a i := fun i hi => by
    rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => h2 i hi j hj (Ne.symm hji)) (fun h => absurd hi h), h1 i hi]
  intro i hi j hj
  rw [← k i hi, ← k j hj, map_mul, mul_mul_mul_comm, h0, mul_zero]

theorem add_mul_self_eq_of_orthogonal_idempotents {R : Type} [CommRing R] {a b : R} (h1 : a * a = a) (h2 : b * b = b) (h3 : a * b = 0) :
    (a + b) * (a + b) = a + b := by linear_combination h1 + h2 + 2 * h3

theorem add_mul_add_eq_zero_of_pairwise_products_zero {R : Type} [CommRing R] {a b a' b' : R} (h1 : a * a' = 0) (h2 : b * b' = 0) (h3 : a * b' = 0)
    (h4 : a' * b = 0) : (a + b) * (a' + b') = 0 := by linear_combination h1 + h2 + h3 + h4

theorem map_cut {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} {a b : R} (h1 : f a = 1) (h0 : a * b = 0)
    (M : Matrix (Fin n) (Fin n) R) :
    ((a + b) • M + (1 - (a + b)) • (1 : Matrix (Fin n) (Fin n) R)).map f = M.map f := by
  have hb : f b = 0 := by
    have := congrArg f h0
    rwa [map_mul, h1, one_mul, map_zero] at this
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, h1, hb]
  ring


set_option maxHeartbeats 800000 in
theorem exists_prod_pieces : ∀ {D : D7} (V : HSp D) (P : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ w ∈ P, Formalism.L2.NTheta.IsIdemAt (es w) w) → (∑ w ∈ P, es w) * cA D (∑ w ∈ P, es w) = 0 → ∀ r : GA D V, SuppAt (∑ w ∈ P, es w) V r → ∃ h : P → GA D V, (∀ w, SuppAt (es w.1) V (h w)) ∧ (∀ w, (mt V (h w)).map (GlobalTheory.RowRep.piAt w.1) = (mt V r).map (GlobalTheory.RowRep.piAt w.1)) ∧ r = (Finset.univ.toList.map h).prod := by
  intro D V P es hes h0 r hr
  have h1 : ∀ w ∈ P, es w * es w = es w := fun w hw => (idem_mul (hes w hw) (hes w hw)).1 rfl
  have h2 : ∀ w ∈ P, ∀ w' ∈ P, w ≠ w' → es w * es w' = 0 := fun w hw w' hw' => (idem_mul (hes w hw) (hes w' hw')).2
  have h3 := mul_conj_zero (cA D) P es h1 h2 h0
  let E : P → AE D := fun w => es w.1 + cA D (es w.1)
  have hEE : ∀ w, E w * E w = E w := fun w =>
    add_mul_self_eq_of_orthogonal_idempotents (h1 _ w.2) (by rw [← RingHom.map_mul, h1 _ w.2]) (h3 _ w.2 _ w.2)
  have hEc : ∀ w, cA D (E w) = E w := fun w => by
    show cA D (es w.1 + cA D (es w.1)) = es w.1 + cA D (es w.1)
    rw [RingHom.map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    have := h2 _ w.2 _ w'.2 fun h => hww (Subtype.ext h)
    exact add_mul_add_eq_zero_of_pairwise_products_zero this (by rw [← RingHom.map_mul, this, RingHom.map_zero]) (h3 _ w.2 _ w'.2) (h3 _ w'.2 _ w.2)
  choose h hh using fun w => GlobalTheory.SplitCut.cut_exists V r (E w) (hEE w) (hEc w)
  refine ⟨h, fun w i j => ?_, fun w => ?_, ?_⟩
  · rw [hh w]
    exact GlobalTheory.SplitCut.idempotent_mul_cut_sub_one_entry _ (hEE w) _ i j
  · rw [hh w]
    have a1 : GlobalTheory.RowRep.piAt w.1 (es w.1) = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes _ w.2)).1
    exact map_cut (GlobalTheory.RowRep.piAt w.1) a1 (h3 _ w.2 _ w.2) _
  · apply GlobalTheory.SplitCut.mt_injective
    have hsum : (Finset.univ.toList.map E).sum = (∑ w ∈ P, es w) + cA D (∑ w ∈ P, es w) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_map_toList, map_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_coe_sort P fun w => es w + cA D (es w)
    rw [GlobalTheory.SplitCut.mt_list_prod V h E (mt V r) hh hEo _ (Finset.nodup_toList _), hsum]
    refine GlobalTheory.SplitCut.exists_widePullback_of_iteratedLine _ _ fun i j => ?_
    rw [sub_mul, one_mul, hr i j, sub_self]

end GlobalTheory.PlaceCut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVacuumBasePointFamilyEveryTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowBase

theorem exists_isBase : Big fun ch => ∀ t, ∃ b, IsBase t ch.S.B b := by
  refine GlobalTheory.RowReal.big_mono ?_ (Big.and _root_.GlobalTheory.RowRep.rep_at _root_.GlobalTheory.RowLocBig.exists_hasLoc_big)
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch ⟨hrep, hloc⟩ t
  classical
  let β0 : CosFam ch.G t := fun _ _ => DoubleCoset.mk _ _ 1
  obtain ⟨b', hb'⟩ := (hrep 1 t).1 β0
  have H : ∀ j, ∃ x : GA D (ch.G.V (.grid D.R.m j)),
      (j ∈ idx D → ∃ δ, IsTilt ch.G j δ ∧ IsFinOf δ x) ∧ (j ∉ idx D → x = 1) := by
    intro j
    by_cases hj : j ∈ idx D
    · have hle : j ≤ D.R.m := by have := GlobalTheory.RowRep.idx_le hj; omega
      obtain ⟨δ, -, hδ, -⟩ := hb'.2 j hj hle
      obtain ⟨x, hx⟩ := GlobalTheory.RowRep.exists_isFinOf _ δ
      exact ⟨x, fun _ => ⟨δ, hδ, hx⟩, fun h => absurd hj h⟩
    · exact ⟨1, fun h => absurd h hj, fun _ => rfl⟩
  choose f hf using H
  obtain ⟨r, hr⟩ := hloc t 0 (Nat.zero_le _) (fun w => (stair (locGrid ch.G t w.1) (unifAt w.1) (cosExp ch.G w.1) 0)⁻¹)
  refine ⟨Function.update f 0 r, ?_, ?_, ?_⟩
  · rw [Function.update_self]; exact hr
  · intro j hj
    have h0 : j ≠ 0 := by have := GlobalTheory.RowRep.idx_le hj; omega
    rw [Function.update_of_ne h0]
    exact (hf j).1 hj
  · intro j h0 hj
    rw [Function.update_of_ne h0]
    exact (hf j).2 hj

end GlobalTheory.RowBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePointsRowPeriodConjLevelFubini
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.CellMass

theorem cell_fubini : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ j ∈ idx D,
    ∀ ρ : Measure ((rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))))) (ν : Measure (GfC (ch.G.V (.top j)))),
      0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : GfC (ch.G.V (.grid D.R.m j)),
        ρ.real {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} =
          κ * la.real {n | b⁻¹ * n.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} * ν.real (prSet ch.G j b) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro j hj ρ hρ
  obtain ⟨-, -, -, h4, h5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.grid D.R.m j))
  obtain ⟨-, -, -, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.top j))
  obtain ⟨c1, c2, c3, c4, c5, π, σ, hπ, hσ, hπσ, hker, hpr⟩ := _root_.GlobalTheory.CellMass.rowGrp_finite_semidirect ch j hj
  obtain ⟨κ, la, ν, hκ, hla, hν, h⟩ := _root_.GlobalTheory.RowFubini.haar_trace_conj_eq _ _ _ π σ c1 c2 c3 c4 c5 hπ hσ hπσ hker ρ hρ
  exact ⟨κ, la, ν, hκ, hla, hν, fun b => by rw [hpr b]; exact h b⟩

end GlobalTheory.CellMass
end
end

