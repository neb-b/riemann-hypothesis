module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def UnitOff (N : ℕ) (u : ℂ) : Prop :=
  u ≠ 0 ∧ ∃ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ n * u) ∧ IsIntegral ℤ ((N : ℂ) ^ n * u⁻¹)

def normQ (Q : Finset (Pl D.host.E)) : ℕ := ∏ PP ∈ Q, Nat.card (kP PP)

section Series

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)


end Series

section Pinned

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m)

def Pinned : Prop :=
  GlobalTheory.Hk3.Core R F ∧ TieIn T R κ v₀ ∧ OMPins T R κ v₀ O i ∧ PhaseTie T R κ v₀ O ph i ∧ QGuard R

end Pinned

section Checks

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

end
