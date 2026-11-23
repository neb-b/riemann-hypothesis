module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.HeckeIntertwinersInert
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Polynomial
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev plF (PP : Pl D.host.E) : HeightOneSpectrum (𝓞 D.host.F) := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def IsInertPl (PP : Pl D.host.E) : Prop :=
  Formalism.UG.IsInertAt D.host.F D.host.E (plF PP) PP

def LocAt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) : Prop :=
  ∀ v', v' ≠ v →
    ((x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (evalV D.host.F v') (AlgHom.id D.host.F D.host.E)) = 1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev levX (R : RealDat D A Ks) (t : T) : Subgroup (Bridge.Gf D.sp.X') := (levEnv D.sp.X' R.βX (R.datXt t)).J

def IsInertDC (R : RealDat D A Ks) (t : T) (PP : Pl D.host.E) (x : Bridge.Gf D.sp.X') (B : Finset (Bridge.Gf D.sp.X')) : Prop :=
  IsInertPl PP ∧ PP ∉ R.Sb ∧ PP ∉ R.Q t ∧ LocAt D.sp.X' (plF PP) x ∧ (∀ b ∈ B, LocAt D.sp.X' (plF PP) b) ∧
    Bridge.IsDC (levX R t) x B

abbrev InertIx (R : RealDat D A Ks) (t : T) : Type :=
  {a : Pl D.host.E × Bridge.Gf D.sp.X' × Finset (Bridge.Gf D.sp.X') // IsInertDC R t a.1 a.2.1 a.2.2}

section Fam

variable (R : RealDat D A Ks) {I : T → Type} (lab : ∀ t, I t → InertIx R t)
  (hE : ∀ t, (A.ok t × ℕ) ⊕ I t → Module.End ℂ R.HE.H)

end Fam

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.InertLocalIndices
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField Polynomial
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.InertLocalIndices

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def InertOver (v : HeightOneSpectrum (𝓞 D.host.F)) (P : Formalism.L2.DIV.Pl D.host.E) : Prop :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal = P.asIdeal

def LocAt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) : Prop :=
  ∀ v' : HeightOneSpectrum (𝓞 D.host.F), v' ≠ v →
    (Units.val (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))).map
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v') (AlgHom.id D.host.F D.host.E)) = 1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (R : RealDat D A Ks)

end GlobalTheory.IndefiniteRowSideFullHecke.InertLocalIndices

end
end

