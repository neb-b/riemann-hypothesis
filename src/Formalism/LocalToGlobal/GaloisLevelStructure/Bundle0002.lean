module

public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalToGlobal.GaloisLevelStructure.NGalTied

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GaloisLevelStructure.LevelQ
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.L2

variable {D : D7} {C : Host.CharFrame D} {nch : NChoice D}

theorem qPl_tup (Tp : Host.TupTied D C nch) (μ : D.what₂.Tup) (j : Fin D.R.m) :
    qPl D (Tp.tup μ j) = {v | v ∉ gPl D ∧ ∃ w : PlE D.host, NG.OverPl w v ∧ ¬ (Tp.xi μ).UnrAt w} := by
  ext v
  simp only [qPl, Set.mem_ofPred_eq, Host.TupTied.tup]
  refine and_congr_right fun hv => exists_congr fun w => and_congr_right fun hw => not_congr ?_
  have hm : (C.mu0 j).UnrAt w := by
    refine (C.isMu0 j).unr w fun k hk => hv ?_
    simp only [gPl, Set.mem_ofPred_eq]
    exact ⟨w, hw, k, hk⟩
  constructor
  · intro h x hx
    have hx' := h x hx
    change (C.mu0 j).loc w x * (Tp.xi μ).loc w x = 1 at hx'
    rw [hm x hx, one_mul] at hx'
    exact hx'
  · intro h x hx
    change (C.mu0 j).loc w x * (Tp.xi μ).loc w x = 1
    rw [hm x hx, h x hx, one_mul]

end Formalism.L2
end
end

-- bundled from Formalism.LocalToGlobal.GaloisLevelStructure.LinkChar
section
namespace Formalism.L2

def NGalTied.TupLink {D : Formalism.BasicNotions.D7} (G : NGalTied D) {C : Host.CharFrame D} {nch : Formalism.BasicNotions.NChoice D}
    (Tp : Host.TupTied D C nch) : Prop :=
  G.tup = Tp.tup

end Formalism.L2
end

