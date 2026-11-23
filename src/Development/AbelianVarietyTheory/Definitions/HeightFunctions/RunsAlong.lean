module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.Bundle0002

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta
open Formalism.L2.Host (CharFrame HChar)
open GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Plug

section Record

variable {D : D7}

structure Tied (EX : ErrX D) (J : CoreJ D) (C : CharFrame D) : Prop where
  lawsJ : LawsJ J
  core : CorePin J.toCore C.P.pb
  field : FieldTies D C
  half : HalfAt EX C


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure CF (D : D7) : Type 1 where
  J : CoreJ D
  C : CharFrame D

end Record

def CoreSlot (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
    (t : RowsT K w Z Wt p0), 𝒮.Rx K B f T w Z Wt p0 t → CorePin t.r.z.core.toCore f.P.pb

def cfOf {𝒮 : Slots} {K : Ctx} (p : WPt 𝒮 K) : CF (p.w.D p.Z) := ⟨p.x.what₂.r.z.core, Fr.at (p.w.st p.Z) p.f⟩

end GlobalTheory.Plug

end
