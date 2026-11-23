module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0014

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RunDepth.Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}

section General

variable (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) [StarRing (𝓞 D.host.E)]
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}

variable {T EX Tp hK} {O : OnObj S P oc} {ι : Bs.J → ℕ}

theorem b_eq (h : RunTie T EX Tp hK O ι) : O.b = L.sc.b := by
  unfold OnObj.b OnObj.xe Scale.b Scale.L
  rw [h.x_eq, h.eps_eq]

end General

end GlobalTheory.RunDepth.Model
