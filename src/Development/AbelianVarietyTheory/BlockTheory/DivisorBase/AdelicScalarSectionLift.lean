module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LogFactorialIndices.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}




variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Adelic

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def level (F : Face D A) : Option Bool → LevelP R.Pg D.R.r ℂ
  | none => R.triv
  | some b => R.levL F b (sg0 D A)


def PrimeToHost : Prop :=
  ∀ PP ∈ R.Pg, ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

end Adelic

section Geometric

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

variable (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

end Geometric

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift

end
