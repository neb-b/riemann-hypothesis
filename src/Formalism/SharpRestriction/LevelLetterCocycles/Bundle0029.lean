module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.TeichOnto
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module IsLocalRing

def TeichOnto (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ a : ZMod p, a ≠ 0 → ∃ j : DeltaT p, PadicInt.toZMod (j.1 : ℤ_[p]) = a

def ComplMax : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ),
    (p : O) ∈ maximalIdeal O → (p : O) ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O →
      IsAdicComplete (maximalIdeal O) O

def zpEquiv {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) : ℤ_[p] ≃+* ℤ_[q] := by
  subst h
  exact RingEquiv.refl _

def ιZrec {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    ℤ_[(P.PD K).p] →+* ↥(OL LL) :=
  (algebraMap ℤ_[l] ↥(OL LL)).comp (zpEquiv (P.PD_p K)).toRingHom

def UTieRec (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
    ∃ uZ : ℤ_[((D.loc l).PD K).p]ˣ, ((uZ : ℤ_[((D.loc l).PD K).p]) - 1).valuation = 1 ∧
      ιZrec (D.loc l) K LL uZ = (((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL))

end Formalism.MainNotions.N.Ln03
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def DownSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelFR D HW → DownSlotProposition D HW

def UpSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelFR D HW → UpSlotProposition D HW

def MixedSlotOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → DdRFull D → DiRank D HW F Cm → modelFR D HW → MixedSlotProposition D HW

end Formalism.MainNotions.N.Ln34

end
end

