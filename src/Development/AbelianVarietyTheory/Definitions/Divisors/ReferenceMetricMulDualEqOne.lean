module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0039

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

namespace GlobalTheory.Mean4O

section Met

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

abbrev PolOf (x : ToroidalCompactificationData s) (Φ : s.Flag) : Type := PolDat s Φ (metsOf x Φ) (refMet x Φ)

def metTrue (x : ToroidalCompactificationData s) (Φ : s.Flag) (P : PolOf x Φ) : MetIn Φ where
  hm := metsOf x Φ
  h0 := refMet x Φ
  r := rFlag x Φ
  ab := P.ab
  dir := P.dir
  reg := P.reg

end Met

namespace Setup

variable {D : D7} (O : Setup D)

structure CoreWith (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) : Prop where
  met : O.met = metTrue x O.Φ P
  Mb : O.Mb = mbarOf P
  bd : IsBdOf x O.L O.B
  fl : O.fl = flBetti O.s O.Φ O.L

def Core : Prop := ∃ (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P

namespace CoreWith

variable {O} {x : ToroidalCompactificationData O.s} {P : PolOf x O.Φ} (h : O.CoreWith x P)
include h

end CoreWith

namespace Core

variable {O} (h : O.Core) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ)
include h

end Core

end Setup

end GlobalTheory.Mean4O
