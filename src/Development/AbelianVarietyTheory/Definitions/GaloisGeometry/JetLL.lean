module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.HermitianForms.Bundle0005

@[expose] public section

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms NumberField

def IsVal {ι Yv : Type} [Fintype ι] {n : ℕ} (fr : Yv → ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) {k : Type} [Field k]
    (σ : k →+* ℂ) (f : Yv → ℂ) : Prop :=
  ∃ P ∈ Formalism.L2.DIV.VV k lam, f = evG fr (fun τ => (lam τ).detShift) σ P

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

end GlobalTheory.KerJ
