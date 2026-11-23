module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsAtSmallPlace
public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.MeasureFailsForLargeConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0069
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0436
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatAtOfRows
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField
namespace GlobalTheory.CovTop
open GlobalTheory.BigTop Formalism.IndefR.FWT
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem ratAt_of_rows_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') (ht : RecTied D L) : RatAt p i :=
  GlobalTheory.T.integralForms_eq_span_integralRationalForms _ _ _ _ _ _ _ _ (p.fw.ks i) (fun u f hf => rho_mem_WK p i u f hf) (_root_.GlobalTheory.T.chi_mul_psi_inv_mem_range_algebraMap p i hp ht)
end GlobalTheory.CovTop
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
end Point
def KerOfAtAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => KerOf p w j
def TraceAt' : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => TraceOf p w j
def KernelRationalAt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => KerRat p w j
def LatticeInclusionAt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => LatIo p w j
def ReadComparisonAt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => ReadCmp p w j
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfSmall
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
namespace GlobalTheory.FrameRead
open Formalism.IndefR.Bridge
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Core
variable {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {l : ℕ} [Fact l.Prime]
end Core
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
theorem reads_of_small_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => SmallAt p j P w → ReadsAt p j P W w := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ j P W hD _ w _ _ _ _ => ?_⟩⟩
  choose cs hcs using hD.lam
  exact ⟨false, fun τ => -cs τ, fun e0 io ev bs rk Lf _ kap chi hC hbs =>
    reads_rank p j w W.lam cs hcs e0 io ev bs rk Lf kap chi hC hbs⟩
end GlobalTheory.FrameRead
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealEqOfColOKStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realEq_of_colOK' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.ColOK → RealEq f.t := by
  first | exact @_root_.GlobalTheory.Fam.realEq_of_colOK_alt | exact _root_.GlobalTheory.Fam.realEq_of_colOK_alt | (intros; apply _root_.GlobalTheory.Fam.realEq_of_colOK_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecAtOfGramAtStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_recursion_of_gram_bound : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive := by
  first | exact @_root_.GlobalTheory.CovTop.liftRecursive_of_gram | exact _root_.GlobalTheory.CovTop.liftRecursive_of_gram | (intros; apply _root_.GlobalTheory.CovTop.liftRecursive_of_gram <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelOfLinks
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem rel_of_links_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u), (∀ t, (f.t t).Is) → MainX f.t → _root_.GlobalTheory.MiTop.LinkVanishes f d → _root_.GlobalTheory.MiTop.LinkTailCondition f → _root_.GlobalTheory.MiTop.LinkDescends f → _root_.GlobalTheory.MiTop.LinkSurjective f → _root_.GlobalTheory.MiTop.LinkCommutes f → _root_.GlobalTheory.MiTop.FamilyRatioCondition f → _root_.GlobalTheory.MiTop.FamilyServedCondition W → ∃ (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (c : W.P.T → ℂ), 0 < r ∧ (∀ φ, ‖U φ‖ = r * ‖φ‖) ∧ _root_.GlobalTheory.MiTop.UnitCoefficients W c ∧ d.Rel U c := by
  intro D L hT Gi Gl Kc Yd cX ex W u f d hIs hMain hZ hTail hDown hOnto hComm hRat hServ
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨n, hn⟩ : ∃ n, 2 * n + 2 = D.R.m := ⟨a - 1, by omega⟩
  have h : 2 * n + 2 * 0 + 2 = D.R.m := by omega
  have h₀ : 0 + 2 * n + 2 = D.R.m := by omega
  have hN : 2 * (n + 1) = D.R.m := by omega
  obtain ⟨S, r, s, hr, hS, hs, hcomm⟩ := hComm (n + 1) hN
  have hBot : ∀ t, (f.t t).cBot ≠ 0 := fun t =>
    Finset.prod_ne_zero_iff.mpr (fun j hj => (hIs t).cI j (Finset.mem_range.mp hj))
  have hTop : ∀ t, (f.t t).cTop (n + 1) ≠ 0 := fun t => (hRat (n + 1) hN t).1
  refine ⟨(S.symm : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u), r⁻¹, fun t => (f.t t).cTop (n + 1) * s / (f.t t).cBot,
    inv_pos.mpr hr, ?_, ?_, ?_⟩
  · intro φ
    have e := hS (S.symm φ)
    simp only [LinearEquiv.apply_symm_apply] at e
    simp only [LinearEquiv.coe_coe]
    rw [e, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  · refine ⟨fun t => div_ne_zero (mul_ne_zero (hTop t) hs) (hBot t), ?_⟩
    intro w k hk
    refine _root_.GlobalTheory.Fam.vw_eq_zero_of_unitRatio D.what₂.LL D.what₂.embLL w (_root_.GlobalTheory.MiTop.qPrime_alt W (W.Q.Rl.mu w)) _ _ (hRat (n + 1) hN (W.Q.Rl.mu w)).2
      (fun p hp hb => hServ w p hp hb) k ?_
    rw [hk]
    have a1 := hTop (W.Q.Rl.mu w)
    have a2 := hTop W.P.A3.A.μ0
    have b1 := hBot (W.Q.Rl.mu w)
    have b2 := hBot W.P.A3.A.μ0
    field_simp
  · intro T hT0
    obtain ⟨G₀, hG₀⟩ := hOnto n h T hT0
    refine ⟨fun φ₀ => (f.t W.P.A3.A.μ0).cTop (n + 1) * (f.t W.P.A3.A.μ0).tail (2 * (n + 1)) hN
      ((f.t W.P.A3.A.μ0).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))) G₀ / (f.t W.P.A3.A.μ0).cBot, ?_⟩
    intro φ₀ φ t F F' hFF α α' hrel y v
    obtain ⟨G, hG1, hGd⟩ := hDown n h t F'
    let sB : Bool → W.P.T := fun b => Bool.rec t W.P.A3.A.μ0 b
    let xB : Bool → D.what₂.Mu u := fun b => Bool.rec (S.symm φ) (S.symm φ₀) b
    let aB : Bool → ℂ := fun b => Bool.rec (α' / (f.t t).cBot) (α / (f.t W.P.A3.A.μ0).cBot) b
    let FB : ∀ b, (f.t (sB b)).CT := fun b => Bool.rec (motive := fun b => (f.t (sB b)).CT) G G₀ b
    have key := hMain n h h₀ Bool sB aB (fun b => _root_.GlobalTheory.MiTop.col0_alt f (sB b) (xB b)) FB
      (fun b => ((hZ n h₀ (sB b) (xB b)).1))
    rw [Fintype.sum_bool] at key
    have top : aB true * (f.t (sB true)).cTop (n + 1) * (f.t (sB true)).tail (2 * (n + 1)) h
          ((f.t (sB true)).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f (sB true) (xB true))) (FB true) +
        aB false * (f.t (sB false)).cTop (n + 1) * (f.t (sB false)).tail (2 * (n + 1)) h
          ((f.t (sB false)).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f (sB false) (xB false))) (FB false) = 0 := by
      have e1 := hcomm t (S.symm φ) G
      rw [LinearEquiv.apply_symm_apply] at e1
      have e2 := hTail (n + 1) hN t φ F F' hFF G hG1
      change α / (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).cTop (n + 1) * (f.t W.P.A3.A.μ0).tail (2 * (n + 1)) hN
          ((f.t W.P.A3.A.μ0).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))) G₀ +
        α' / (f.t t).cBot * (f.t t).cTop (n + 1) * (f.t t).tail (2 * (n + 1)) hN ((f.t t).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f t (S.symm φ))) G = 0
      rw [e1, e2]
      beta_reduce at hrel
      linear_combination hrel
    have bot := key top y v
    rw [Fintype.sum_bool] at bot
    have z1 := (hZ n h₀ W.P.A3.A.μ0 (S.symm φ₀)).2
      ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)) y v
    have z2 := (hZ n h₀ t (S.symm φ)).2 ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)) y v
    change α / (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))
        ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)) y v +
      α' / (f.t t).cBot * (f.t t).cBot * (f.t t).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f t (S.symm φ))
        ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)) y v = 0 at bot
    rw [z1, z2] at bot
    have d1 : ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)).1 = T := hG₀
    have d2 : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = _root_.GlobalTheory.MiTop.rowFormOfTuple W t F' := hGd
    rw [d1, d2, div_mul_cancel₀ _ (hBot _), div_mul_cancel₀ _ (hBot _)] at bot
    simpa only [LinearEquiv.coe_coe] using bot
end GlobalTheory.MiTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResSEqOfFlagStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_level_integral_twist_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)), κ ∈ rowJ W.S.X W.Q.instEq → ∀ (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, (∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u' (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))))) = toEAf D ei • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))))) → Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  first | exact @_root_.GlobalTheory.CongFlag.resS_eq_of_flag_alt | exact _root_.GlobalTheory.CongFlag.resS_eq_of_flag_alt | (intros; apply _root_.GlobalTheory.CongFlag.resS_eq_of_flag_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBigStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_parameter_estimates_at_pts : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ X' A : ℝ, Formalism.CohomologicalDescent.LargeParameterEstimates.Rows (GlobalTheory.ExpTie.parOf (Fm.L x i) j) X' A ∧ Formalism.CohomologicalDescent.LargeParameterEstimates.Big (GlobalTheory.ExpTie.parOf (Fm.L x i) j).L (GlobalTheory.ExpTie.parOf (Fm.L x i) j).x X' A := by
  first | exact @_root_.GlobalTheory.ExpTie.rows_big_alt | exact _root_.GlobalTheory.ExpTie.rows_big_alt | (intros; apply _root_.GlobalTheory.ExpTie.rows_big_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScalarOfReading
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.Exp
section ScalarGeneric
variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}
variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))
end ScalarGeneric
set_option maxHeartbeats 4000000 in
theorem scalar_of_reading_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun Fm x hx i p w j ρ hρ ν _ => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ (z : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ⊗[(Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)] (Fm.D x i).nexp.Fm ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) (n : ℕ) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL) (κ : ℂ) (N : ℕ),
    (∀ k, y k ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _))) → IsUnit ((N : ℕ) : (Fm.ex x hx i).nch.Oe w) → (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) →
    rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = κ • ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) →
    ∃ b : (Fm.ex x hx i).nch.Oe w, rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (b * a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by
  unfold _root_.GlobalTheory.BigOn.Exp.CanonicalFits _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j ρ hρ ν rd hfit hcan => ?_⟩⟩⟩
  intro e he1 he2 z n a y κ N hy hN hint hz
  have hν : ν ≠ 0 := hfit.2.1.1
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν hν hU hW (Z.vec j) hK
  have hL : ∀ c : (Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w),
      e (algebraMap _ (FractionRing ((Fm.ex x hx i).nch.Oe w)) c) =
        ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)),
      IsScalarTower.algebraMap_apply _ ((Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w)) ((Fm.ex x hx i).nch.Oe w),
      he2, hρ.ek_e]
    rfl
  set R := readExt (rdAt p w j hρ ν) e hL with hRdef
  have hRinj : Function.Injective R := readExt_injective _ e hL hF
  have hinc : ∀ z, R (incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w)
      ((Fm.ex x hx i).nch.k' w) z) = rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
    | tmul c f =>
      rw [rdK_tmul, ← he2]
      rfl
  have hgen : ∀ f : NX.FmK p.Sx ((j : ℕ) + 1), R (rd ((p.nexp.fi j).e (Subtype.val f))) =
      ν⁻¹ • adForm (R2 p) j ((p.nexp.fi j).e (Subtype.val f)) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun f => by
    rw [hcan f, hRdef, readExt_tmul, map_one, one_smul]
    erw [realRd_tmul]
    erw [map_one, mul_one]
    rfl
  have hA0 : adForm (R2 p) j 0 (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0 := by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ 0) (p.v₀ j _) = 0
    rw [map_zero, map_zero]
    rfl
  have hAadd : ∀ u v, adForm (R2 p) j (u + v) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) + adForm (R2 p) j v (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u v => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (u + v)) (p.v₀ j _) = _
    rw [map_add (f := _), map_add (f := _)]
    rfl
  have hs : sg0 (Fm.D x i) p.P.A3.A = (Fm.D x i).what₂.embLL := sgAt_mk _ (R2 p).hv0
  have hAsmul : ∀ (c : (Fm.D x i).what₂.LL) u, adForm (R2 p) j (c • u) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      (Fm.D x i).what₂.embLL c • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun c u => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (c • u)) (p.v₀ j _) = _
    rw [LinearMap.map_smulₛₗ, map_smul]
    exact congrArg (fun s : ℂ => s • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A))) (DFunLike.congr_fun hs c)
  have hrd : ∀ u ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)),
      R (rd u) = ν⁻¹ • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨f, hf, rfl⟩ := hu
      exact hgen ⟨f, hf⟩
    | zero =>
      erw [LinearMap.map_zero rd]
      rw [AddMonoidHom.map_zero R]
      erw [hA0]
      rw [smul_zero]
    | add u v _ _ hu hv =>
      erw [LinearMap.map_add rd]
      rw [AddMonoidHom.map_add R, hu, hv]
      erw [hAadd]
      rw [smul_add]
    | smul c u _ hu =>
      erw [LinearMap.map_smulₛₗ rd]
      rw [hRdef, readExt_smul, ← hRdef, hu, he1]
      erw [hAsmul]
      rw [smul_comm]
  have hS : R (∑ k, a k • rd (y k)) = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k) (rd (y k)), hRdef, readExt_smul, ← hRdef,
      hrd _ (hy k), mul_smul]
  have hRHS : ∀ b : ((Fm.ex x hx i).nch.Oe w), ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (b * a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) b) •
      ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun b => by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, smul_smul, mul_assoc]
  by_cases hT0 : ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0
  · exact ⟨0, by rw [hRHS, hz, hT0, smul_zero, smul_zero]⟩
  · obtain ⟨b₀, hb₀⟩ := readExt_scalar_mem_range _ e hL hF
      (incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) z)
      (∑ k, a k • rd (y k)) κ (by rw [hinc, hS, hz]) (by rwa [hS])
    obtain ⟨m, hmI⟩ := hint
    obtain ⟨b, hb⟩ := exists_algebraMap_eq_of_isIntegral e b₀ N hN m (by rwa [hb₀])
    exact ⟨b, by rw [hRHS, hz, hb, hb₀]⟩
end GlobalTheory.BigOn.Exp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootAltBis
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
def ScaleRootAltBis : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P ≠ 0 →
    ∃ n : ℕ, n ≠ 0 ∧ ν' ^ n = ν ^ n
def CoordinateRangeCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν μ : ℂ), ν ≠ 0 →
  ∀ f f', f ≠ 0 → rdAt p w j hρ ν f' = μ • rdAt p w j hρ ν f →
    ∃ u, ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) u = μ
end GlobalTheory.BigOn.Exp
end
end
end

