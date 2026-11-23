module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGKSubmoduleISupGelfandJointEigenspaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.GKEigen

theorem isGKSub_iSup_eigen : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ C : Finset (D.what₂.Tau × ℕ → ℂ), GlobalTheory.CuspGK.IsGKSub θ M (⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h}) := by
  intro D θ V S M hθ ψ hψ C
  have hG : GlobalTheory.CuspGK.IsGKSub θ M (GlobalTheory.CuspGK.gkGen θ M ψ) := by
    constructor
    · intro τ g hg f hf
      exact Submodule.mem_sInf.2 fun A hA => hA.2.k τ g hg f (Submodule.mem_sInf.1 hf A hA)
    · intro τ X hX f hf
      exact Submodule.mem_sInf.2 fun A hA => hA.2.lie τ X hX f (Submodule.mem_sInf.1 hf A hA)
  have hsm : ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf =>
    (GlobalTheory.KTypeAdm.isAutFunSm_of_mem_gkGen θ M hθ hψ f hf).smooth
  set T : Set (GA D V → ℂ) := ⋃ c ∈ C,
    {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h} with hTdef
  have hspan : (⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h}) =
      Submodule.span ℂ T := by
    rw [hTdef, Submodule.span_iUnion₂]
  rw [hspan]
  have hTG : T ⊆ GlobalTheory.CuspGK.gkGen θ M ψ := by
    intro h hh
    rw [hTdef, Set.mem_iUnion₂] at hh
    obtain ⟨c, _, hh, _⟩ := hh
    exact hh
  have hSG : Submodule.span ℂ T ≤ GlobalTheory.CuspGK.gkGen θ M ψ := Submodule.span_le.2 hTG
  have hTk : ∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ h ∈ T, rTr V (atTau θ V τ g) h ∈ T := by
    intro τ g hg h hh
    rw [hTdef, Set.mem_iUnion₂] at hh ⊢
    obtain ⟨c, hc, hhG, he⟩ := hh
    refine ⟨c, hc, hG.k τ g hg h hhG, fun i => ?_⟩
    rw [GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ _ i.1 i.2 (hsm h hhG), he i]
    rfl
  have hTl : ∀ τ, ∀ X ∈ lieAt V τ, ∀ h ∈ T, Rder θ V τ X h ∈ T := by
    intro τ X hX h hh
    rw [hTdef, Set.mem_iUnion₂] at hh ⊢
    obtain ⟨c, hc, hhG, he⟩ := hh
    refine ⟨c, hc, hG.lie τ X hX h hhG, fun i => ?_⟩
    rw [GlobalTheory.CuspLie.gelf_Rder hθ hX (hsm h hhG) i.1 i.2, he i, GlobalTheory.Mem.AutSpace.Rder_smul]
  refine ⟨fun τ g hg f hf => ?_, fun τ X hX f hf => ?_⟩
  · induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hTk τ g hg x hx)
    | zero => exact (Submodule.span ℂ T).zero_mem
    | add x y _ _ hx hy => exact (Submodule.span ℂ T).add_mem hx hy
    | smul a x _ hx => exact (Submodule.span ℂ T).smul_mem a hx
  · induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hTl τ X hX x hx)
    | zero =>
      rw [Formalism.IndefR.Mult.rder_zero θ V τ X]
      exact (Submodule.span ℂ T).zero_mem
    | add x y hx' hy' hx hy =>
      rw [GlobalTheory.Mem.AutSpace.Rder_add (hsm x (hSG hx')) (hsm y (hSG hy')) hX]
      exact (Submodule.span ℂ T).add_mem hx hy
    | smul a x _ hx =>
      rw [GlobalTheory.Mem.AutSpace.Rder_smul]
      exact (Submodule.span ℂ T).smul_mem a hx

end GlobalTheory.GKEigen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.RatMoveJets

def RatCoord {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : GfC V)
    (U : Matrix.unitaryGroup (Fin V.rank) D.host.E) : Prop :=
  ∃ γ ∈ GQ V, finHom V γ = finHom V (g : GA D V) ∧
    Formalism.L2.Theta.mt V γ = (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (incA D)

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc}

def srcU : ∀ p : GlobalTheory.ChiGrid.Pair T, Matrix.unitaryGroup (Fin (G.V p.small).rank) D.host.E →
    Matrix.unitaryGroup (Fin (G.V p.big).rank) D.host.E → Matrix.unitaryGroup (Fin (G.pS p).rank) D.host.E
  | .chi _ _, _, U' => U'
  | .mu _ _ _, U, _ => U
  | .core _, _, U' => U'
  | .top _ _, U, _ => U

def tgtU : ∀ p : GlobalTheory.ChiGrid.Pair T, Matrix.unitaryGroup (Fin (G.V p.small).rank) D.host.E →
    Matrix.unitaryGroup (Fin (G.V p.big).rank) D.host.E → Matrix.unitaryGroup (Fin (G.pT p).rank) D.host.E
  | .chi _ _, U, _ => U
  | .mu _ _ _, _, U' => U'
  | .core _, U, _ => U
  | .top _ _, _, U' => U'

end

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetTh (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big)
    (Θ : VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ) : Prop :=
  ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ)

theorem jetKap_iff (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ) :
    GlobalTheory.MovedKappaEx.JetKap ch p x y κ ↔ JetTh ch p x y (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ)
      (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ)
        (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) :=
  Iff.rfl

end

end GlobalTheory.RatMoveJets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFinAtZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.CuspKFin

variable {D : D7}

def KFinAt (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (ψ : GA D N.V → ℂ) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
    (ρ : Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) W),
    GlobalTheory.Published.AutFin.IsContRep ρ ∧ GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) ρ ψ

end GlobalTheory.CuspKFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteOfMemGKModuleGeneratedByStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_of_mem_gKModuleGeneratedBy : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ GlobalTheory.KTypeProj.KStable θ M W) →
    ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧
      GlobalTheory.KTypeProj.KStable θ M Y := by
  first | exact @GlobalTheory.GKGenKFin.kFinite_of_mem_gkGen | exact GlobalTheory.GKGenKFin.kFinite_of_mem_gkGen | (intros; apply GlobalTheory.GKGenKFin.kFinite_of_mem_gkGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatHatStabOfHatL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.RowMovedLat

open Matrix

variable {D : D7}

theorem negGA_mem_GfC (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem latHat_stab_of_hatL (V : HSp D) (g : GA D V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      (Formalism.IndefR.Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt V g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
  have key : (fun i => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
      ((((Formalism.L2.Theta.mt V g).map (finPart D)).mulVec y) i)) =
      (Formalism.IndefR.Lev.finE V g).val *ᵥ (fun i => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (y i)) := by
    have hf : (Formalism.IndefR.Lev.finE V g).val = ((Formalism.L2.Theta.mt V g).map (finPart D)).map (Formalism.IndefR.Lev.swapAE D) := by
      ext i j
      rfl
    rw [hf]
    ext i
    exact RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) _ y i
  refine (GlobalTheory.SplitFrameColumn.latHat_iff_hatL Λ y).trans ((h _).trans ?_)
  refine Iff.symm ((GlobalTheory.SplitFrameColumn.latHat_iff_hatL Λ _).trans ?_)
  exact Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) key)

end GlobalTheory.RowMovedLat

namespace GlobalTheory.RowMovedLat

theorem moved_pair_stab : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le →
    (G.toPair (.chi j D.R.m) 1 (moved S j k)).1 ∈ GfC (G.pS (.chi j D.R.m)) ∧
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latS (.chi j D.R.m) : Set (Fin (G.pS (.chi j D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ (G.toPair (.chi j D.R.m) 1 (moved S j k)).1).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latS (.chi j D.R.m) : Set (Fin (G.pS (.chi j D.R.m)).rank → D.host.E))) ∧
    (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 ∈ GfC (G.pT (.chi (j + 1) D.R.m)) ∧
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latT (.chi (j + 1) D.R.m) : Set (Fin (G.pT (.chi (j + 1) D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latT (.chi (j + 1) D.R.m) : Set (Fin (G.pT (.chi (j + 1) D.R.m)).rank → D.host.E))) := by
  intro D T L sc G W U S t _ j hj k hk
  have hG : moved S j k ∈ GfC (G.V (.grid (j + 1) D.R.m)) :=
    (((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u (.grid (j + 1) D.R.m) : FinPt G (.grid (j + 1) D.R.m))).2
  have hst := latHat_stab_of_hatL _ (moved S j k) _ (moved_keeps_std S j hj k hk)
  exact ⟨negGA_mem_GfC _ hG, hst, hG, hst⟩

end GlobalTheory.RowMovedLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaProjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eq_zero_of_no_lift (R : RealDat D A Ks) (hW : R.models_HW) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g : G) (hn : ¬ ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ) (x : (R.HW i σ).H) : x = 0 := by
  have hL : actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) = 0 := by
    ext F h
    show actG0 _ _ _ _ F h = 0
    rw [GlobalTheory.ProjComm.levelGroupAction_eq_zero_of_no_lift hn F]
    rfl
  have h1 : (R.HW i σ).e (R.gW i σ g x) = 0 := by
    rw [hg i σ g x, hL]
    ext v h
    rfl
  have h2 : R.gW i σ g x = 0 := (hW i σ).1 (by rw [h1, map_zero])
  have h3 := congrArg (R.gW i σ g⁻¹) h2
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at h3

theorem realDatum_coeffFlagLevelCharacter_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (κ : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ = 1 := by
  classical
  unfold levChi Formalism.L2.DIV.levFn
  simp [flagL, withP, LevCh.datWp, datY, Formalism.L2.DIV.ext1, Formalism.L2.DIV.LevelP.full]
  exact dite_eq_right_iff.mpr fun _ => rfl

theorem left_abs {H Gf W : Type} [Group H] [Group Gf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (Γ : Subgroup H)
    (p : H →* Gf) (ρ : H →* Module.End ℂ W) (f : Gf → W) (J : Subgroup Gf) (χ : J →* ℂˣ)
    (hy : f ∈ Bridge.AdForms (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) (γ : H) (hγ : γ ∈ Γ) (h : H) :
    ρ (γ * h)⁻¹ (f (p (γ * h))) = ρ h⁻¹ (f (p h)) := by
  have h1 : f (p γ * p h) = ρ γ (f (p h)) := by
    have h0 : f (p γ * p h * 1) = ((χ 1 : ℂˣ) : ℂ) • ρ γ (f (p h)) := hy ⟨γ, hγ⟩ (p h) 1
    simpa using h0
  rw [map_mul p, h1, mul_inv_rev, map_mul ρ, Module.End.mul_apply, ← Module.End.mul_apply (ρ γ⁻¹), ← map_mul ρ,
    inv_mul_cancel, map_one, Module.End.one_apply]

theorem shift_abs {H Gf W : Type} [Group H] [Group Gf] [AddCommGroup W] [Module ℂ W]
    (p : H →* Gf) (ρ : H →* Module.End ℂ W) (κ : H) (hκ : ρ κ⁻¹ = 1) (a : ℂ) (ha : a ≠ 0) (f f' : Gf → W)
    (hy : ∀ h, f' h = a⁻¹ • f (h * p κ)) (h : H) :
    ρ h⁻¹ ((a • f') (p h)) = ρ (h * κ)⁻¹ (f (p (h * κ))) := by
  rw [Pi.smul_apply, hy, smul_smul, mul_inv_cancel₀ ha, one_smul, map_mul p, mul_inv_rev, map_mul ρ,
    Module.End.mul_apply, hκ, Module.End.one_apply]

theorem ext_left {V : HSp D} (c : CoefA V) (f : Bridge.Gf V → c.W) (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ)
    (hy : f ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) J χ)
    (γ : GA D V) (hγ : γ ∈ GQ V) (h : GA D V) : c.ext f (γ * h) = c.ext f h := by
  show c.ρ (γ * h)⁻¹ (f ((finHom V).rangeRestrict (γ * h))) = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h))
  exact left_abs (GQ V) (finHom V).rangeRestrict c.ρ f J χ hy γ hγ h

theorem ext_shift {V : HSp D} (c : CoefA V) (hc : c.Is) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0)
    (f f' : Bridge.Gf V → c.W) (hy : ∀ h, f' h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (h : GA D V) :
    c.ext (a • f') h = c.ext f (h * κ) := by
  show c.ρ h⁻¹ ((a • f') ((finHom V).rangeRestrict h)) = c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ)))
  exact shift_abs (finHom V).rangeRestrict c.ρ κ (hc.1 _ (inv_mem hκ)) a ha f f' hy h

theorem extV_left (R : RealDat D A Ks) (hV : R.models_HV) (i : Fin D.R.m) (t : T0) (y : (R.HV i t).H)
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) : R.extV i t y (γ * h) = R.extV i t y h := by
  have h3 := LinearMap.mem_range_self (R.HV i t).e y
  rw [(hV i t).2.1] at h3
  show (R.cV i).ext ((R.HV i t).e y) (γ * h) = (R.cV i).ext ((R.HV i t).e y) h
  exact ext_left (R.cV i) _ _ _ h3 γ hγ h

theorem extV_shift (R : RealDat D A Ks) (hc : R.models_cV) (i : Fin D.R.m) (t : T0) (κ : GA D (Vc D i))
    (hκ : κ ∈ GfC (Vc D i)) (c : ℂ) (hc0 : c ≠ 0) (y y' : (R.HV i t).H)
    (hy : ∀ h, (R.HV i t).e y' h = c⁻¹ • (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ)) (h : GA D (Vc D i)) :
    R.extV i t (c • y') h = R.extV i t y (h * κ) := by
  show (R.cV i).ext ((R.HV i t).e (c • y')) h = (R.cV i).ext ((R.HV i t).e y) (h * κ)
  rw [map_smul]
  exact ext_shift (R.cV i) (hc i) κ hκ c hc0 _ _ hy h

theorem integral_shift (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (g0 : G0 L.Pg L.r)
    (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (𝓕 : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) 𝓕 ν) (f : GA D V → ℂ) (hf : ∀ γ ∈ GQ V, ∀ h, f (γ * h) = f h)
    (hi : IntegrableOn f 𝓕 ν) : ∫ h in 𝓕, f (h * κ) ∂ν = ∫ h in 𝓕, f h ∂ν := by
  obtain ⟨htg, hlc, hsc, -, hbo, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  obtain ⟨-, -, -, hct⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  obtain ⟨hK, hlift⟩ := GlobalTheory.ParahoricCompact.isCompact_flag_and_lift V β L
  haveI := htg
  haveI := hlc
  haveI := hsc
  haveI := hbo
  haveI := hct
  haveI := hν
  have hmap := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup ν _ hK κ (hlift g0 κ hκ)
  exact (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) ν 𝓕 hfd κ hmap f hf hi).2

theorem thetaLift_shift {G' H' S' Sinf TK Tau : Type} [Group G'] [Group H'] [MeasurableSpace H']
    [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
    {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Sinf → S'} {io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf}
    {B : Submodule ℂ (H' → Tau)} {thP : B →ₗ[ℂ] (TK →ₗ[ℂ] (G' → ℂ))} (hP : Lift.IsThetaP ν 𝓕 th pt io B thP)
    (Γ : Subgroup H') (k : H') (k' : G') (c : ℂ) (hc : c ≠ 0)
    (hsh : ∀ f : H' → ℂ, (∀ γ ∈ Γ, ∀ h, f (γ * h) = f h) → IntegrableOn f 𝓕 ν →
      ∫ h in 𝓕, f (h * k) ∂ν = ∫ h in 𝓕, f h ∂ν)
    (hl : ∀ P, ∀ γ ∈ Γ, ∀ g h, th g (γ * h) (pt P) = th g h (pt P))
    (hr : ∀ P g h, th (g * k') (h * k) (pt P) = c⁻¹ * th g h (pt P))
    (f f' : B) (hf : ∀ γ ∈ Γ, ∀ h, (f : H' → Tau) (γ * h) = (f : H' → Tau) h)
    (hf' : ∀ h, ((c • f' : B) : H' → Tau) h = (f : H' → Tau) (h * k)) (e : TK) (g : G') :
    thP f' e g = thP f e (g * k') := by
  have hA : thP f e (g * k') = ∫ h in 𝓕, th (g * k') h (pt (io e ((f : H' → Tau) h))) ∂ν :=
    hP.eq f e (g * k')
  have hB : thP (c • f') e g = ∫ h in 𝓕, th g h (pt (io e (((c • f' : B) : H' → Tau) h))) ∂ν :=
    hP.eq (c • f') e g
  have hF := hsh (fun h => th (g * k') h (pt (io e ((f : H' → Tau) h))))
    (fun γ hγ h => by
      rw [hf γ hγ h]
      exact hl _ γ hγ _ _)
    (hP.integ f e (g * k'))
  rw [hA, ← hF]
  simp only [hr]
  rw [integral_const_mul]
  have hfk : ∀ h, (f : H' → Tau) (h * k) = ((c • f' : B) : H' → Tau) h := fun h => (hf' h).symm
  simp only [hfk]
  rw [← hB, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem thF_type (R : RealDat D A Ks) (hm : R.thP_thF_mem) (i : Fin D.R.m) (t : T0) (y : (R.HV i t).H)
    (v : (R.MW i (sg0 D A)).Vec) : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (R.thF i t y v) := by
  intro κ hκ h
  have hmem : R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) := hm i t y
  exact (GlobalTheory.mult_value_left_cont_level R.θ _ _ _ _ hmem v).2.2 κ hκ h

theorem finiteGroup_acts_by_lift_translation_principalType (R : RealDat D A Ks) (i : Fin D.R.m) (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i))
    (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') (f : GA D (Wc D i) → ℂ)
    (hT : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) f) (x : GA D (Wc D i)) :
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 f x = f (x * κ') := by
  have hex : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ := ⟨κ', hκ'⟩
  have hchi : ∀ k, levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := by
    intro k
    classical
    unfold levChi Formalism.L2.DIV.levFn
    simp [LevCh.datWp, datY, Formalism.L2.DIV.ext1, Formalism.L2.DIV.LevelP.triv]
    exact dite_eq_right_iff.mpr fun _ => rfl
  have hmem := lift_div_mem hκ' hex.choose_spec
  have hfl : flag1L (R.datWp i R.triv) = R.datWp i R.triv := rfl
  rw [hfl] at hmem
  have hx := hT _ hmem (x * κ')
  rw [hchi, one_mul, ← mul_assoc, mul_inv_cancel_right] at hx
  show actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) g0 f x = f (x * κ')
  unfold actG0
  rw [dite_eq_left hex, realDatum_coeffFlagLevelCharacter_eq_one, inv_one, one_mul]
  exact hx

end GlobalTheory.ThetaProjEquiv

end
end

