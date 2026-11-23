module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AddCharThetaLawRearrangementIdentity
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.MainNotions.N IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NJoin.Inh

section Frame

variable {D : D7} {V : HSp D} {n : ℕ} (P : RowPsi V n)

variable (c : CoefA V)

variable (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank)

variable {W : Type} [AddCommGroup W] [Module ℂ W] (e : c.W ≃ₗ[ℂ] W)

variable (hc : ∀ h ∈ GfC V, c.ρ h = 1) (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ D.host.E n) W)
  (rat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V (P.ψ h))
  (wt : ∀ (h : ReciprocityTheory.Aut.GQ D.host.E n), ∀ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V (P.ψ h) →
    ∀ v, e (c.ρ γ v) = ρ h (e v))
include hc rat wt


end Frame

section Algebraic

open MvPolynomial ReciprocityTheory.Aut
open scoped Matrix

variable {ι : Type} [Fintype ι] {n : ℕ}

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

end Algebraic

section Weight

variable {D : D7}

theorem rat_unit {V : HSp D} (hg : V.gram = 1) (h : Formalism.AUTREP.GAf D.host.E V.rank) :
    h ∈ ReciprocityTheory.Aut.GQ D.host.E V.rank ↔
      ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V ((GlobalTheory.StdFrameModel.unitPsi hg).ψ h) := by
  have hfin : finHom V ((GlobalTheory.StdFrameModel.unitPsi hg).ψ h) = Formalism.UG.bc (GlobalTheory.StdFrameModel.sw D).symm.toRingHom h.1 :=
    (GlobalTheory.StdFrameModel.exists_lift hg h).choose_spec.2
  have hU : ∀ x : GL (Fin V.rank) D.host.E, x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank ↔
      x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    intro x
    change x.1 * ReciprocityTheory.Aut.conjT _ x.1 = 1 ↔ Formalism.UG.cT _ x.1 * V.gram * x.1 = V.gram
    rw [hg, Matrix.mul_one, mul_eq_one_comm]
    rfl
  rw [hfin]
  constructor
  · rintro ⟨x, hx, e⟩
    have hx' := (hU x).1 hx
    have hm : Formalism.UG.bc (incA D) x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
      have h0 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1 = V.gram := hx'
      have h2 := congrArg (fun M => Matrix.map M (incA D)) h0
      simp only [Matrix.map_mul] at h2
      exact h2
    refine ⟨⟨_, hm⟩, ⟨x, hx', rfl⟩, ?_⟩
    have e' : h.1 = _ := e.symm
    rw [e']
    ext i j
    change (sndA D.host.F 1) ⊗ₜ[D.host.F] (x.1 i j) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x.1 i j)
    rw [map_one]
  · rintro ⟨γ, ⟨x, hx, e⟩, e2⟩
    refine ⟨x, (hU x).2 hx, ?_⟩
    ext i j
    have e3 := congrArg (fun g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.1 i j) e2
    have e4 : (finHom V γ).1 i j = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x.1 i j) := by
      have e' : γ.1 = _ := e.symm
      change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (γ.1.1 i j) = _
      rw [e']
      change (sndA D.host.F 1) ⊗ₜ[D.host.F] (x.1 i j) = _
      rw [map_one]
    simp only [e4] at e3
    apply (GlobalTheory.StdFrameModel.sw D).symm.injective
    exact e3

variable {V : HSp D} (c : CoefA V)

end Weight

section Agreement

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : RealAt D cf nch tp)

end Agreement

section Reading

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {cf : CharFrame D} {nch : NChoice D}


end Reading

section Record

open Formalism.MainNotions Formalism.L2.Rows

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.SPer (Dcf Zs)} {Zscf : Indef.DefSub P.A3.fam3.amb3 → Indef.IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : RealT Rc P Dcf Spf Zscf S Ks}

end Record

end GlobalTheory.NJoin.Inh

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
section
noncomputable section

namespace GlobalTheory.NRows

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

structure Hypotheses₂ : Prop where
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  bern : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  geo : GlobalTheory.Published.GeometricLemma
  unl : GlobalTheory.Published.UnlinkedProductIrreducible
  mp : GlobalTheory.Published.DepthZeroJacquetInjective
  howe : GlobalTheory.Published.HoweDualityGL
  js : GlobalTheory.Published.JacquetShalika
  fin : GlobalTheory.Published.AutomorphicFormsFiniteGL
  temp : GlobalTheory.Published.CohomologicalCsdTempered
  gal : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal
  car : GlobalTheory.Published.LocalGlobalAboveL
  clo : GlobalTheory.Published.RegularAlgebraicPurity
  art : GlobalTheory.Published.GlobalArtinReciprocity
  chA : GlobalTheory.Published.HeckeLAdicCharacterAbove
  chP : GlobalTheory.Published.HeckeLAdicParameterAbove
  berger : GlobalTheory.Published.DeRhamPotSemistable
  cheb : GlobalTheory.Published.ChebotarevDegreeOne

structure RowsB (D : D7) : Prop where
  rowSize : RowSize D
  a3 : SumRepresentations.adm3 D
  a4 : SumRepresentations.ArchimedeanSignatureMatching D
  thetaOne : ThetaOne D

structure RowsC (D : D7) : Prop where
  c4b : JointOccurrenceCondition D
  rho : GlobalDatumResidualRepCondition D
  dz : GlobalDatumDepthZeroCondition D
  parUp : ∀ i, ParUpRec D.nd D.naut i
  downMem : ∀ i, DownMemRec D.nd D.naut i
  goodPart : ∀ i, GoodPartRec D.nd D.naut i

def LamUsed (D : D7) : Prop :=
  ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → ∀ j : Fin D.R.m, LamPos D μ (j.1 + 1)

def GoodIdempotentFixesLocalisationForms (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ' : D.ntypes.Par), ∀ F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ',
    D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F

def GoodIdempotentReadsAsGoodTypeProjector {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) : Prop :=
  ∀ μ (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1)) y,
    X.R.extV j (X.tupT μ) y = X.fn hμ j f →
      (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f = f ↔ GlobalTheory.DownLift.GoodVt X.R j (X.tupT μ) y)

structure Tied (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Type 1 where
  P : GlobalTheory.NPin.Pin hL D
  X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp
  agree : GlobalTheory.NJoin.Agree X P.M P.rep
  e0read : GoodIdempotentReadsAsGoodTypeProjector X

structure Named {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) : Prop where
  hypO : SumRepresentations.hypO D
  c1 : GlobalDatumCompatibility D
  bc : SphericalInertData.Conclusion1 D
  lam : LamUsed D
  isot : SumRepresentations.adm8 D
  ser : GlobalTheory.TypeLeaf.SerLoc D
  typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ T.X.R j t

structure Inputs (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Type 1 extends toRowSideFamily : Tied hL D where
  named : Named toRowSideFamily

theorem LamUsed.at {D : D7} (h : LamUsed D) {μ} (hμ : μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : LamPos D μ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h μ hμ ⟨k, by omega⟩

theorem LamUsed.loc {D : D7} (h : LamUsed D) (i : D.nd.Loc) : LamPos D (D.nd.mu i) (D.nd.j i) :=
  h.at (Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩)
    (D.nd.j_range i).1 (D.nd.j_range i).2

theorem goodIdempotentFixes_of_onlySeriesOfLabelActs {D : D7} (h : GlobalTheory.TypeLeaf.SerLoc D) : GoodIdempotentFixesLocalisationForms D := fun i σ' F hF hg =>
  (PlaceLabelTeichmuller.idempotent_action_on_forms D (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i)) σ' F fun k v f hf => h i σ' k v f F hF hf).1 hg

namespace Inputs

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (I : Inputs hL D)
include I

theorem hypO : SumRepresentations.hypO D := I.named.hypO

theorem c1 : GlobalDatumCompatibility D := I.named.c1

theorem bc : SphericalInertData.Conclusion1 D := I.named.bc

theorem lam : LamUsed D := I.named.lam

theorem isot : SumRepresentations.adm8 D := I.named.isot

theorem ser : GlobalTheory.TypeLeaf.SerLoc D := I.named.ser

theorem typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ I.X.R j t := I.named.typeNZ


end Inputs

end GlobalTheory.NRows

end
end

