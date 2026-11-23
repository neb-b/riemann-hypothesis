module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Unlinked (s : Multiset (IrrGL (k := k))) : Prop := ∀ y ∈ s, ∀ z ∈ s, y ≠ z.nu 1

def PlainTor (x : IrrGL (k := k)) : Prop := ∃ s, HasSupport x.rep s ∧ (∀ y ∈ s, y.1 = 1) ∧ Unlinked s

def Plain (x : IrrGL (k := k)) : Prop := PlainTor x ∨ (x.IsCusp ∧ UpperTheory.Zero.LLC.GoodCusp x)

def chars {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) : Multiset (IrrGL (k := k)) :=
  Finset.univ.val.map fun j => IrrGL.ofChar (ξ j) (hξ j)

end Classes

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def satWD {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (a : ℕ) (B : Multiset ℂˣ) : WD h :=
  (WD.lpUnr (h := h) (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpTw ((1 - (a : ℝ)) / 2)

variable [IsCMField E]

def PlainAt (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ → Plain (IrrGL.of σ.ρ σ.smooth σ.irred)

inductive Sph
  | unr | dR | crys | phi

def SphAt (c : Sph) (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E))
    (B : Multiset ℂˣ) : Prop :=
  match c with
  | .unr => ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)
  | .dR => ClauseAt .dR π ι r w
  | .crys => ClauseAt .crys π ι r w
  | .phi => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (satWD h a B).charPol g

def SphericalLevelCondition (s : Level) (c : Sph) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w →
    ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B → SphAt c π ι r w B

def Core : Prop := Ex .csd ∧ ∀ c, SphericalLevelCondition .csd c

def CoreAll : Prop := Ex .all ∧ ∀ c, SphericalLevelCondition .all c

def CharLift {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    (π : CuspSub K a) (P : CuspSub M a) : Prop :=
  IsLift π P ∧ ∀ (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver v.asIdeal]
    (τ : SmIrr (GL (Fin a) (v.adicCompletion K))) (T : SmIrr (GL (Fin a) (u.adicCompletion M))), π.IsLocComp v τ → P.IsLocComp u T →
    ∀ (ξ : Fin a → ((v.adicCompletion K)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport τ.ρ (chars ξ hξ) →
      HasSupport T.ρ (chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j))

def ToralGal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ →
    ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) σ,
      π.IsLocComp w σ →
    ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)),
      HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) →
    ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
      (wdOf h hl ι r).mono0 ∧ ∀ g : Weil h, (wdOf h hl ι r).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))

structure Inputs : Prop where

  js : GlobalTheory.Published.JacquetShalikaRigidity

  gk : GlobalTheory.Published.GelfandKazhdanDual

  adm : GlobalTheory.Published.IrreducibleAdmissibleGL

  len : GlobalTheory.Published.StandardFunctorsFiniteLength

  exh : GlobalTheory.Published.LanglandsExhaustionGL

  zel : GlobalTheory.Published.ZelevinskyPolynomialRing

  gen : GlobalTheory.Published.GenericUnitaryDualGL

  ac : GlobalTheory.Published.ArthurClozelStrongTC

  acs : GlobalTheory.Published.ArthurClozelStrongSupp

  loc : GlobalTheory.Published.ArthurClozelLocalSC

  hk : GlobalTheory.Published.HeckeLAdicCharacterAbove

  alg : GlobalTheory.Published.AlgebraicCharacterWD

  pst : GlobalTheory.Published.DeRhamPotSemistable

end GlobalTheory.RoadU

end
