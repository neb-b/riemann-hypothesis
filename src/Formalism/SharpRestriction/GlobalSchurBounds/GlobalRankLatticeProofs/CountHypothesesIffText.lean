module

public import Formalism.SharpRestriction.GlobalSchurBounds.AdmittedWeylDimension
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset Formalism.MainNotions.S

theorem stab_transfer {H : Type} [Group H] (P R U : Subgroup H) (y : P)
    (hs : R ⊓ U.map (MulAut.conj (y : H)).toMonoidHom = ⊥) (γ : R.subgroupOf P) (κ : U.subgroupOf P)
    (e : (γ : P) * y = y * κ) : γ = 1 := by
  have h1 : ((γ : P) : H) ∈ R ⊓ U.map (MulAut.conj (y : H)).toMonoidHom := by
    refine ⟨γ.2, ⟨((κ : P) : H), κ.2, ?_⟩⟩
    have e' := congrArg Subtype.val e
    simp only [Subgroup.coe_mul] at e'
    show (y : H) * ((κ : P) : H) * (y : H)⁻¹ = _
    rw [← e']
    group
  rw [hs] at h1
  exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.1 h1))

end Formalism.MainNotions.StandardLattice
