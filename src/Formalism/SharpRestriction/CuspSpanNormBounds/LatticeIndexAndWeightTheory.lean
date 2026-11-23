module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.ThetaLiftIndependence.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

noncomputable section

open NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.LatticeIndexAndWeightTheory

export Formalism.MainNotions.S.UnitaryVolumeMass (KTwoParameterConditions Kpp)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Hyps

variable (D : D7) (large₂ : SizeData₂ D)

end Hyps

def IsInertiaCyclotomicGeneratorElement {D : D7} {u u' : D.what₂.Word} (t : D.s.Term u u') : Prop :=
  D.s.relevant t ∧ D.s.Gterm t = 0 ∧ ¬ D.s.isId t

section TermObj

variable {D : D7} (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u')

def Iof : Submodule D.host.E (hS D).V := Isp (X.fl t).fl (X.fl' t).fl

def OrthogonalComplementV0 : Submodule D.host.E (hS D).V := perpS (hS D) (Xplus (X.fl t) ⊔ Xplus (X.fl' t))

def jOf : ℕ := D.R.rS - Module.finrank D.host.E (Iof X t)

def NDl (l : ℕ) : ℝ := (Nloc (ddS D) D.R.rS l (Dl (X.fl t).fl (X.fl' t).fl l) : ℝ)

def DelJ : ℝ := NDl X t (jOf X t)

def ends : Finset ℕ := blockEnds (X.fl t).fl (X.fl' t).fl (jOf X t)

def sg (H1 : ℝ) (τ : D.what₂.Tau) : ℝ :=
  (ends X t).fold max 1 (fun l =>
    absReal D.host.rdE (embS D τ) D.R.rS l (Dl (X.fl t).fl (X.fl' t).fl l) / (2 * H1) ^ (2 * D.R.rS))

def FrameHyp : Prop :=
  (X.fl t).fl.e = D.sp.hypE ∧ (X.fl t).fl.z = D.zmOf u ∧ IsRowLat D (X.fl t).fl (X.abelian₂ t) ∧
    FrameOK D (X.abelian₂ t) (X.fl' t)

end TermObj

def NF {D : D7} (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') : Prop :=
  ∃ j : ℕ, j ≤ D.R.rS ∧ (u = u' → 1 ≤ j) ∧
    (∀ a : ℕ, (∃ x ∈ Iof X t, x ≠ 0 ∧ (X.fl t).fl.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ D.R.rS)) ∧
    (∀ a : ℕ, (∃ x ∈ Iof X t, x ≠ 0 ∧ (X.fl' t).fl.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ D.R.rS)) ∧
    (∃ c : D.host.E, (X.fl' t).fl.z - c • (X.fl t).fl.z ∈ Xsp (X.fl t) ⊔ Xsp (X.fl' t) ∧
      c * star c * ((Tu D u : ℕ) : D.host.E) = ((Tu D u' : ℕ) : D.host.E)) ∧
    Dl (X.fl t).fl (X.fl' t).fl j ≠ 0 ∧
    (OrthogonalComplementV0 X t ⊓ Xsp (X.fl t) = Iof X t ∧ OrthogonalComplementV0 X t ⊔ Xsp (X.fl t) = (X.fl t).fl.XplusPerp) ∧
    (OrthogonalComplementV0 X t ⊓ Xsp (X.fl' t) = Iof X t ∧ OrthogonalComplementV0 X t ⊔ Xsp (X.fl' t) = (X.fl' t).fl.XplusPerp)

section Datum

variable {D : D7} (X : TermTie D) {u u' : D.what₂.Word}

def SameDC {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T') : Prop :=
  ∃ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT,
    (∀ a : Fin D.R.rS, σ (F.fl.e a) - F.fl.e a ∈ Xflag F a.val) ∧ σ F.fl.z - F.fl.z ∈ Xsp F ∧
    (∀ a : Fin D.R.rS, σ (F₁.fl.e a) - F₂.fl.e a ∈ Xflag F₂ a.val) ∧ σ F₁.fl.z - F₂.fl.z ∈ Xsp F₂

def TermInj (u : D.what₂.Word) : Prop :=
  ∀ t t' : D.s.Term u u, X.abelian₂ t = X.abelian₂ t' → TEqv D (X.abelian₂ t) (X.fl t) (X.fl' t) (X.fl' t') → t = t'

def NormOK (u : D.what₂.Word) : Prop :=
  (∀ p : D.s.Pair u u, X.wRow p = Formalism.MainNotions.S.wRow D (X.fl (D.s.pfst p)).fl (X.abelian₂ (D.s.pfst p))) ∧
  ∀ t : D.s.Term u u, IsInertiaCyclotomicGeneratorElement t → ∃ p : D.s.Pair u u, D.s.pfst p = t ∧ D.s.psnd p = t ∧
    X.beta p = LinearEquiv.refl D.host.E (hS D).V ∧
    D.s.pval p = ((Formalism.MainNotions.S.wRow D (X.fl t).fl (X.abelian₂ t) * hsNormSq (X.Jt t) : ℝ) : ℂ)

def IndW (D : D7) (σ : (hS D).V ≃ₗ[D.host.E] (hS D).V) (h : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : Prop :=
  ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (h w) ∈ Submodule.span D.host.E (Set.range D.sp.hypE)

def AmpOK : Prop :=
  (∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), (X.fl t).fl.e = D.sp.hypE ∧ (X.fl t).fl.z = D.zmOf u) ∧
  ∃ (ρ : ∀ u : D.what₂.Word, ((D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) → (X.Hpi u →L[ℂ] X.Hpi u))
    (δ : ∀ u u' : D.what₂.Word, D.s.Term u u' → ((hS D).V ≃ₗ[D.host.E] (hS D).V)),
    (∀ u, ρ u 1 = ContinuousLinearMap.id ℂ (X.Hpi u) ∧
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ρ u (h * h') = (ρ u h).comp (ρ u h')) ∧
    (∀ u (K : Submodule ℂ (X.Hpi u)), (∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ x ∈ K, ρ u h x ∈ K) → K = ⊥ ∨ K = ⊤) ∧
    (∀ u u', u ≠ u' → ∀ P : X.Hpi u' →L[ℂ] X.Hpi u,
      (∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, (ρ u h).comp P = P.comp (ρ u' h)) → P = 0) ∧
    (∀ u u' (t : D.s.Term u u'), δ u u' t ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT ∧
      (∀ a, δ u u' t (D.sp.hypE a) = (X.fl' t).fl.e a) ∧ δ u u' t (D.zmOf u') = (X.fl' t).fl.z) ∧
    (∀ u u' (t : D.s.Term u u'), ∀ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT,
      (∀ x ∈ Xplus (X.fl t) ⊔ Xplus (X.fl' t), σ x = x) →
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
        IndW D σ h → IndW D ((δ u u' t)⁻¹ * σ * δ u u' t) h' → (ρ u h).comp (X.Jt t) = (X.Jt t).comp (ρ u' h')) ∧
    ∀ u (t : D.s.Term u u), IsInertiaCyclotomicGeneratorElement t → NF X t → ∀ x ∈ OrthogonalComplementV0 X t, δ u u t x - x ∈ Xsp (X.fl' t)

def TieOK (u : D.what₂.Word) : Prop :=
  (∀ t : D.s.Term u u, FrameHyp X t) ∧ TermInj X u ∧ NormOK X u ∧ AmpOK X

end Datum

section Terms

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

end Terms

section Size

variable (D : D7) (large₂ : SizeData₂ D)

end Size

section Mass

variable (D : D7) (large₂ : SizeData₂ D)

end Mass

section Targets

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

end Targets

section Packet

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

end Packet

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))

end Family

end Formalism.MainNotions.LatticeIndexAndWeightTheory

end
