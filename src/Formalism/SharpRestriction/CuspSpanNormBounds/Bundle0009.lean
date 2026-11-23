module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
public import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeIndexAndWeightTheory
public import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.AdmissibleBoundsFromSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
section
noncomputable section

namespace Formalism.MainNotions.PX

section GroupS0

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Exp (D : D7) : Prop := ∀ u u' : D.what₂.Word, KExpansion D.s u u' ∧ KAbsConv D.s u u'

def GDr (D : D7) (X : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.Gterm t ≠ 0 →
    Dl (X.fl t).fl (X.fl' t).fl (D.R.rS + 1) ≠ 0 ∧
    (Dl (X.fl t).fl (X.fl' t).fl D.R.rS ≠ 0 → ∀ τ, 0 < (embS D τ (Lat.Gval (X.fl t) (X.fl' t))).re)

section Family

variable {eps : ℝ} (Fm : FamP eps)

def RanksF (C0 Cg cb Cu cT CT : ℝ) : Prop := LocalBesselAndTopKernel.FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT

end Family

end GroupS0

section GroupS1

open Formalism.MainNotions.S

end GroupS1

section GroupS5

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryVolumeMass Formalism.MainNotions.S.Bridge

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def StdHypS (Cg cb Cu cT CT C0 Ch Cβ : ℝ) : Prop :=
  ∀ Cs Cs', OwnEv Fm fun C' Cl x i => StdOfHyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ

def TFrame (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
    ∀ w, 1 ≤ Tr (Fm.D x i) w * kaS (Fm.D x i) ^ (2 * (Fm.D x i).R.rS)

end GroupS5

end Formalism.MainNotions.PX

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.TrD
section
open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

variable {k r : ℕ}

def trD (L : LocBessel k r) (κ τ : ℝ) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1) : LocBessel k r where
  ε := L.ε
  lam := L.lam
  hlam := L.hlam
  z := (τ : ℂ) • L.z
  z' := (τ : ℂ) • L.z'
  hz := hz
  hz' := hz'
  u := L.u
  u' := L.u'
  Hs := L.Hs
  σ := L.σ
  hσ := L.hσ
  Wp := L.Wp
  π := fun x => L.π (cjI k r κ τ x)
  hπ := hπ
  Wq := L.Wq
  π' := fun x => L.π' (cjI k r κ τ x)
  hπ' := hπ'
  c := (κ : ℂ) * L.c
  μW := L.μW.map (cjT k r κ τ)
  μW' := L.μW'.map (cjT k r κ τ)
  hμW := hμW
  hμW' := hμW'
  κN := κN₁

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

