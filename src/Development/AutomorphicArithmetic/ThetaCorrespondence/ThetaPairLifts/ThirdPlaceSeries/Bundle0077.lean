module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdaptEx
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp.Adapt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
section Point
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
end GlobalTheory.BigOn.Exp.Adapt
open GlobalTheory.BigOn.Exp.Adapt in
theorem GlobalTheory.BigOn.Exp.adaptEx_alt : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm CH _ _ => ⟨0, fun x hx _ i p _ hm w _ j => adapt_at p w j hm⟩⟩⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdaptFBOfNormalFramesStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_scalar_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP), ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.FinPl.AdaptFB (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).ψ ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).J j (σ + 1) h) ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).B (j + 1 + 1) σ (idx_step h)) (N₁ (j + 1)) ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).x (j + 1)).L (N₁ (j + 1 + 1)) (M₁ (j + 1 + 1) σ (idx_step h)) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @_root_.GlobalTheory.Fam.adaptFB_of_normalFrames_alt | exact _root_.GlobalTheory.Fam.adaptFB_of_normalFrames_alt | (intros; apply _root_.GlobalTheory.Fam.adaptFB_of_normalFrames_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorPairs
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
namespace GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem anchor_pairs_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → PuNZ D → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → ∀ u, (∀ φ, ∃ C, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ) ∧ (∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ C, ∃ b, _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b) ∧ ∃ (φ : D.what₂.Mu u) (C : _) (b : ℂ), ∃ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ ∧ _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b ∧ b ≠ 0 := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB hPu z hzf hzc v hv u
  obtain ⟨-, hInf, -, hMatch, -, -⟩ := _root_.GlobalTheory.T.bottom_hypothesis_matching_central_alt W hB
  have hEv := _root_.GlobalTheory.Core.Mi.evalAll_rows hDS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)
    (z * (show GA D (D.sp.Y 0) from W.Q.tS)) v (by simp) hInf hB.gap hB.idE (hMatch z hzf hzc) hv
  obtain ⟨⟨j, hjbij, hj⟩, -⟩ := hEv
  have hF := hB.fin
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  have hpair : ∀ (Tm : MultT W.Q.Rl.θ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)) (C : Cu W.S.X u W.S.Y.hK),
      _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (Tm.1 (PiTensorProduct.tprod ℂ v)) C
        ⟪((j Tm : HHX W.S.X) : L2X W.S.X), PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) C⟫_ℂ := by
    intro Tm C
    unfold _root_.GlobalTheory.MiTop.IsPairing'
    let g : L2X W.S.X := ((j Tm : HHX W.S.X) : L2X W.S.X)
    have hg : (g : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] fun x => star (evS W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (Tm.1 (PiTensorProduct.tprod ℂ v)) x) := hj Tm
    refine ⟨star g, ?_, ?_⟩
    · have h1 : ((star g : L2X W.S.X) : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] star (g : W.S.X.B.I.GA → ℂ) := MeasureTheory.Lp.coeFn_star g
      refine h1.trans ((hg.fun_comp star).trans (Filter.EventuallyEq.of_eq ?_))
      funext x
      exact star_star _
    · rw [star_star]
  refine ⟨fun φ => ?_, fun T hT C => ⟨_, hpair ⟨T, hT⟩ C⟩, ?_⟩
  · obtain ⟨C, hC⟩ := (W.S.bij u).2 (D.eMu u φ).1 (hram (D.eMu u φ).2)
    exact ⟨C, hC⟩
  · obtain ⟨φr, hφr⟩ := hPu u
    let x := (D.s_Cu u).symm ⟨φr.1, φr.2.1⟩
    let C : Cu W.S.X u W.S.Y.hK := (W.S.hI hF).eCu u x
    have hpin := W.S.colPin hF u x
    have hC : _root_.GlobalTheory.MiTop.IsColumnForm W u C ((D.eMu u).symm φr) := by
      show Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK C = _
      rw [LinearEquiv.apply_symm_apply, ← Formalism.L2.SG.ColDict.colDict_apply W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)]
      have hpin' : Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u) C = D.s_Cu u x := hpin
      rw [hpin', LinearEquiv.apply_symm_apply]
    let P : HHX W.S.X := (Formalism.L2.SG.PackageTie2.sOf hF).Pu u C
    have hP : P ≠ 0 := by
      have e := (W.S.hI hF).Pu_eq u x
      intro h0
      apply hφr
      have : (W.S.hI hF).eHH (D.s.Pu u x) = 0 := e.trans h0
      exact (LinearIsometryEquiv.map_eq_zero_iff _).1 this
    obtain ⟨Tm, hTm⟩ := hjbij.2 P
    refine ⟨(D.eMu u).symm φr, C, _, Tm.1, Tm.2, hC, hpair Tm C, ?_⟩
    rw [hTm]
    have hPv : ((P : HHX W.S.X) : L2X W.S.X) = PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) C := rfl
    rw [hPv]
    refine inner_self_ne_zero.2 ?_
    rw [← hPv]
    exact fun h => hP (Subtype.ext h)
end GlobalTheory.MiTop
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsHLtGStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parOf_height_lt_genus_at_pts : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) a, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).h < ((Fm.D x i).host.g a : ℝ) := by
  first | exact @_root_.GlobalTheory.ExpTie.atPts_h_lt_g_alt | exact _root_.GlobalTheory.ExpTie.atPts_h_lt_g_alt | (intros; apply _root_.GlobalTheory.ExpTie.atPts_h_lt_g_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLamPrime_at_all_points : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) τ, Formalism.IndefR.Bridge.IsLamPrime (D := Fm.D x i) (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
  first | exact @_root_.GlobalTheory.LiftWeightForced.atPts_alt | exact _root_.GlobalTheory.LiftWeightForced.atPts_alt | (intros; apply _root_.GlobalTheory.LiftWeightForced.atPts_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutSt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameAut
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame
section Op
variable (K : Type) [CommRing K] (n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)
end Op
end GlobalTheory.FrameAut
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL
namespace GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
def AutStAlt : Prop := _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => AutAt p j P W w
end GlobalTheory.FrameAut
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadWStOf
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BadWOn
open Module GlobalTheory.BadCount GlobalTheory.TwistedRepresentationEmbedding GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
set_option maxHeartbeats 1000000 in
theorem badW_of_del_bound_of_T_bound (p : PtAt ex Csz) (i : Fin D.R.m) (T : ℕ) (del : ℝ) (hGr : GlobalTheory.GLq.Green) (hRows : p.PointConditions')
    (hRec : RecTies p) (hmod : ModelAt p i T) (hr : 100 ≤ D.R.r) (hA : TieAdmG D)
    (hg : ∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k ∧ 4 * (3 * (D.R.f : ℝ) / (D.host.g k : ℝ) + 23 * (D.R.f : ℝ) *
      Real.log (D.host.g k : ℝ) / Real.sqrt (D.host.g k : ℝ) + 2 * (D.R.f : ℝ) * (D.R.m : ℝ) *
      (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log (D.R.r : ℝ)) / ((D.host.g k : ℝ) - 1)) +
      (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ)))) ≤ del)
    (hsT : 2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (D.R.r * D.R.r / 4)) + 2 ≤ T) : BadW p i del := by
  classical
  obtain ⟨C, hCf, hact, M, ka, ρ, σ, f, hpull, hequiv, hli, hspan, hlev, hcard, hcase⟩ := hmod
  obtain ⟨lam, ψ, hW, hlam, hhalf⟩ := _root_.GlobalTheory.T.exists_whittaker_lam_psi_half_unip D L hT Gi Gl Kc Y cX ex Csz p hRows
  obtain ⟨-, hHex⟩ := _root_.GlobalTheory.BadCount.Inh.exists_whit_half D ψ hW.1
  choose Hh hHh using hHex
  let e : p.P.Gp ≃* G0g D.nd := p.R.eG.trans p.cG
  let π : p.P.Gp →* G0g D.nd := e.toMonoidHom
  let ιs : G0g D.nd →* p.P.Gp := e.symm.toMonoidHom
  let P : Subgroup (G0g D.nd) := p.P.P0.map π
  let P' : Subgroup p.P.Gp := P.comap π
  have hle : P' ≤ p.P.P0 := fun g hg => (Subgroup.mem_map_iff_mem e.injective).1 hg
  have hge : p.P.P0 ≤ P' := fun g hg => (Subgroup.mem_map_iff_mem e.injective).2 hg
  have hbot : LevelHyp (GlobalTheory.ShareOn.sub M ⊥) := hlev ⊥ ⟨0, fun g hg v => by
    rw [Subgroup.mem_bot] at hg
    subst hg
    intro a b
    simp only [map_one]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Matrix.one_apply_ne (ne_of_gt h)
    · subst h; exact Matrix.one_apply_eq a⟩
  have hP'lev : LevelHyp (GlobalTheory.ShareOn.sub M P') := by
    obtain ⟨k, hk⟩ := hhalf
    exact hlev P' ⟨k, fun g hg v => hk g (hle hg) v⟩
  have hHlev : ∀ k, LevelHyp (GlobalTheory.ShareOn.sub M ((Hh k).comap π)) := fun k => hlev _ ⟨k + 1, fun g hg v =>
    ((hHh k (π g)).1 hg) ⟨k + 1, v⟩ (by simp)⟩
  have hsOf : GlobalTheory.ShareOn.sOf M ≤ T := by
    have key : ∀ a b : ℕ, a * (b - a) * 4 ≤ b * b := by
      intro a b
      rcases le_total a b with h | h
      · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [Nat.add_sub_cancel_left]
        nlinarith [sq_nonneg ((a : ℤ) - q)]
      · rw [Nat.sub_eq_zero_of_le h]; simp
    have hq : M.p0 * (D.R.r - M.p0) ≤ D.R.r * D.R.r / 4 := (Nat.le_div_iff_mul_le (by norm_num)).2 (key _ _)
    have hX : M.dimX ≤ D.R.f * (D.R.r * D.R.r / 4) := by
      unfold TwoLevels.dimX; rw [hcard]; exact Nat.mul_le_mul_left _ hq
    unfold GlobalTheory.ShareOn.sOf
    have := Nat.mul_le_mul_left (50 * D.R.r ^ 2) hX
    omega
  have hc : (M.p0 = 0 ∨ M.p0 = D.R.r) ∨ (0 < M.p0 ∧ M.p0 < D.R.r ∧ GlobalTheory.ShareOn.ArchOn M ka T ∧
      GlobalTheory.ShareOn.sOf M ≤ T ∧ LevelHyp (GlobalTheory.ShareOn.sub M ⊥)) := by
    rcases hcase with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3, hsOf, hbot⟩
  let A := p.R.toRealDat.FW i
  let N := p.R.toRealDat.nW i
  let ρK : Representation D.what₂.LL p.P.Gp (Fin N → D.what₂.LL) := GlobalTheory.TwistedRepresentationEmbedding.twist A.ρ A.chi⁻¹
  let χM : p.P.Gp →* ℂˣ := (Units.map σ.toMonoidHom).comp A.chi⁻¹
  let ρM : Representation ℂ p.P.Gp (M.cusp ka) := GlobalTheory.TwistedRepresentationEmbedding.twist ρ χM
  let ρE : Representation ℂ p.P.Gp (Fin N → ℂ) := GlobalTheory.TwistedRepresentationEmbedding.repE D.what₂.embLL ρK
  have hequivM : ∀ g v, ρM g (f v) = f (ρK g v) := by
    intro g v
    rw [GlobalTheory.TwistedRepresentationEmbedding.twist_apply, GlobalTheory.TwistedRepresentationEmbedding.twist_apply, hequiv, map_smulₛₗ]
    rfl
  have hequivE : ∀ g v, ρE g (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (ρK g v) := fun g v => GlobalTheory.TwistedRepresentationEmbedding.repE_embV _ _ _ _
  let ψ0' : P' →* D.what₂.LLˣ := p.P.ψ0⁻¹.comp (Subgroup.inclusion hle)
  let lamM : P' →* ℂˣ := (Units.map σ.toMonoidHom).comp ψ0'
  let lamb : P' →* ℂˣ := lam.comp (π.subgroupComap P)
  have hemb : ∀ k, ∃ n : ℕ, EmbReg ρE ((Hh k).comap π) n ∧
      (n : ℝ) * Nat.card ((Hh k).comap π) ≤ 2 * Nat.card P' * finrank ℂ (eig ρM P' lamM) := by
    intro k
    obtain ⟨n, hn, hb⟩ := model_bound M ka ρM T (GlobalTheory.TwistedRepresentationEmbedding.isPullRep_twist hpull χM) hc _ P' (hHlev k) hP'lev lamM
    exact ⟨n, _root_.GlobalTheory.BadCount.embReg_of_baseChange D.what₂.LL _ _ p.P.Gp N ρK σ D.what₂.embLL ρM ρE f (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) hli hspan
      (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _) hequivM hequivE _ n hn, hb⟩
  choose n hnE hnb using hemb
  have alg : ∀ (u w : D.what₂.LLˣ) (x y : Fin N → D.what₂.LL), y = ((u * w : D.what₂.LLˣ) : D.what₂.LL) • x ↔
      ((u⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • y - ((w : D.what₂.LLˣ) : D.what₂.LL) • x = 0 := by
    intro u w x y
    rw [sub_eq_zero]
    constructor
    · rintro rfl
      rw [smul_smul, ← Units.val_mul, inv_mul_cancel_left]
    · intro h
      rw [Units.val_mul, mul_smul, ← h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let aK : P' → (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL) := fun γ =>
    ρK γ - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • LinearMap.id
  have haK : ∀ γ F, aK γ F = (((A.chi γ)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • A.ρ γ F -
      ((p.P.ψ0⁻¹ ⟨γ, hle γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL) • F := fun γ F => rfl
  have hsp : spType p.R.toRealDat p.F.lv2 i = ⨅ γ : P', LinearMap.ker (aK γ) := by
    ext F
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    change F ∈ A.typeP p.P.P0 p.P.ψ0⁻¹ ↔ _
    rw [Formalism.IndefR.Arith.FormsL.mem_typeP]
    constructor
    · intro h γ
      rw [haK]
      exact (alg _ _ _ _).1 (h ⟨γ, hle γ.2⟩)
    · intro h q
      have := h ⟨q, hge q.2⟩
      rw [haK] at this
      exact (alg _ _ _ _).2 this
  have dM : finrank ℂ (eig ρM P' lamM) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hsp]
    refine _root_.GlobalTheory.BadCount.finrank_iInf_ker_semilinear D.what₂.LL (M.cusp ka) P' σ N f hli hspan aK (fun γ => ρM γ - ((lamM γ : ℂˣ) : ℂ) • LinearMap.id) ?_
    intro γ v
    show _ = f (ρK γ v - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • v)
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hequivM]
    rfl
  have hlamb : ∀ γ : P', ((lamb γ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) :=
    fun γ => hlam ⟨γ, hle γ.2⟩ γ.2
  have haE : ∀ (γ : P') v, (ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))
      (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (aK γ v) := by
    intro γ v
    show _ = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (ρK γ v - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • v)
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hequivE, hlamb]
  have dE : finrank ℂ (eig ρE P' lamb) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hsp]
    exact _root_.GlobalTheory.BadCount.finrank_iInf_ker_semilinear D.what₂.LL (Fin N → ℂ) P' D.what₂.embLL N (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _) aK
      (fun γ => ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id) haE
  haveI : Fintype (G0g D.nd) := Fintype.ofEquiv p.P.Gp e.toEquiv
  have hsumE : Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0 =
      ∑ g : p.P.Gp, D.ntypes.e0.coeff (e g) • ρE g := by
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype D.ntypes.e0.coeff (fun a b => b • (ρE.comp ιs) a) (fun a => zero_smul ℂ _)]
    exact (Fintype.sum_equiv e.toEquiv (fun g => D.ntypes.e0.coeff (e g) • ρE g)
      (fun h => D.ntypes.e0.coeff h • (ρE.comp ιs) h) (fun g => by simp [ιs])).symm
  obtain ⟨-, -, -, hid, -, -⟩ := p.grpRecPin
  have hE0 : ∀ v, Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0 (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) =
      GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (eGood p.R.toRealDat i v) := by
    intro v
    have hG : eGood p.R.toRealDat i v = ∑ g : p.P.Gp, (idemOf p.P.A3.A.X).coeff g • ρK g v := by
      show ((∑ g, ((idemOf p.P.A3.A.X).coeff g * ((A.chi g)⁻¹ : D.what₂.LLˣ)) • A.ρ g :
        (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL)) v) = _
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [LinearMap.smul_apply, mul_smul]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsumE, LinearMap.sum_apply, hG, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, hequivE, map_smulₛₗ, hid]
  let aO : Option P' → (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL) := fun o =>
    o.elim (eGood p.R.toRealDat i) aK
  let aO' : Option P' → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := fun o =>
    o.elim (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) (fun γ => ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id)
  have dBad : finrank ℂ (eig ρE P' lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) :
      Submodule ℂ (Fin N → ℂ)) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i ⊓
      LinearMap.ker (eGood p.R.toRealDat i) : Submodule D.what₂.LL (Fin N → D.what₂.LL)) := by
    have h1 : (eig ρE P' lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) :
        Submodule ℂ (Fin N → ℂ)) = ⨅ o, LinearMap.ker (aO' o) := by
      rw [iInf_option, inf_comm]; rfl
    have h2 : (spType p.R.toRealDat p.F.lv2 i ⊓ LinearMap.ker (eGood p.R.toRealDat i) :
        Submodule D.what₂.LL (Fin N → D.what₂.LL)) = ⨅ o, LinearMap.ker (aO o) := by
      rw [iInf_option, inf_comm, hsp]; rfl
    rw [h1, h2]
    refine _root_.GlobalTheory.BadCount.finrank_iInf_ker_semilinear D.what₂.LL (Fin N → ℂ) (Option P') D.what₂.embLL N (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _)
      aO aO' ?_
    rintro (_ | γ) v
    · exact hE0 v
    · exact haE γ v
  have hsplit : IsSplit π ιs := ⟨fun g => e.apply_symm_apply g, fun g γ h => by
    have hγ : γ = 1 := e.injective (h.trans e.map_one.symm)
    subst hγ; simp⟩
  let ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ := fun k =>
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    ZMod.stdAddChar
  have hψ₀ : ∀ k, ψ₀ k ≠ 1 := by
    intro k h
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    haveI : Fact (1 < D.host.g k) := ⟨(D.host.g_prime k).one_lt⟩
    have := ZMod.isPrimitive_stdAddChar (D.host.g k) (one_ne_zero)
    rw [AddChar.mulShift_one] at this
    exact this h
  have hbd : ∀ k, (n k : ℝ) * Nat.card ((Hh k).comap π) ≤
      2 * Nat.card (P.comap π) * finrank ℂ (eig ρE (P.comap π) lamb) := by
    intro k; rw [dE, ← dM]; exact hnb k
  obtain ⟨S, hSbad, hineq⟩ := _root_.GlobalTheory.BadCount.bad_part_le_locShare D p.P.Gp (Fin N → ℂ) π ιs hsplit ρE P lam ψ hW lamb (fun γ => rfl) Hh hHh n 2
    hnE hbd ψ₀ hψ₀
  have hadm := _root_.GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation hGr D hRec.eSer
  have hloc : ∀ k, 4 * locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k) ≤ del := fun k =>
    le_trans (by linarith [_root_.GlobalTheory.PropWU.propW_eUk D ψ₀ hψ₀ hadm hA hr (fun k => (hg k).1) k (S k) (hSbad k)]) (hg k).2
  rw [dBad, dE] at hineq
  unfold GlobalTheory.ShareOn.BadW
  have h0 := hloc 0
  have h1 := hloc 1
  have hd : (0 : ℝ) ≤ finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := Nat.cast_nonneg _
  refine hineq.trans ?_
  nlinarith
end Point
theorem badWSt_of_greenCuspidal_of_modelSt (hG : GlobalTheory.Published.GreenCuspidal) (hM : _root_.GlobalTheory.ShareOn.ModelStatement) : _root_.GlobalTheory.ShareOn.BadWeightStatement := by
  have hGr := hG.green
  refine Closed.imp ((hM.and _root_.GlobalTheory.BadNumOnto.badShare_numbers_onto).and _root_.GlobalTheory.HodgeMultNum.hodgeMult_le_TO) ?_
  rintro eps Fm CH - ⟨⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩, ⟨x3, hx3⟩⟩
  refine ⟨max x1 (max x2 x3), fun x hx hle ι p hp hMore r hr hown i => ?_⟩
  have h1 : x1 ≤ x := (le_max_left _ _).trans hle
  have h2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have h3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨hr100, hA, -, hg⟩ := hx2 x hx h2 ι
  exact _root_.GlobalTheory.BadWOn.badW_of_del_bound_of_T_bound p i _ _ hGr hp hMore.2.2 (hx1 x hx h1 ι p hp hMore r hr hown i) hr100 hA hg (hx3 x hx h3 ι)
end GlobalTheory.BadWOn
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanExHolds
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem canEx_holds_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalExists :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ _ _ p _ _ w _ j => canEx_at p w j⟩⟩⟩
end GlobalTheory.BigOn.Exp
end
end
end

