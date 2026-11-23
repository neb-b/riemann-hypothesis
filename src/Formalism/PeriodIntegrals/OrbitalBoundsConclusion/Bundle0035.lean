module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.PrvFOfOrbitLetterBounds
public import Mathlib
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitSumCount.SizeGe
public import Formalism.PeriodIntegrals.Bundle0023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Places

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbBoundF
section
theorem PI.OrbBoundF : ∀ (D : Formalism.BasicNotions.D7) (L : Formalism.BasicNotions.SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (K : Formalism.MainNotions.G.Consts) (ce : Formalism.BasicNotions.ErrC) (E : Formalism.MainNotions.OrbitPlaces.Ent D) (C6 C : ℝ), Formalism.MainNotions.OrbitPlaces.OrbitLetterBoundsAll C6 C → Formalism.MainNotions.OrbitPlaces.Shape D L X E → Formalism.MainNotions.OrbitPlaces.CLarge C6 C K ce → Formalism.MainNotions.OrbitPlaces.OrbitValuationBound E X K ce :=
  PI.OrbBoundFW.prvF_of_orbitLetterBounds
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumOrbC
section
theorem PI.SumOrbC : ∀ (D : Formalism.BasicNotions.D7) (L : Formalism.BasicNotions.SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (K : Formalism.MainNotions.G.Consts) (ce : Formalism.BasicNotions.ErrC) (E : Formalism.MainNotions.OrbitPlaces.Ent D) (C6 C : ℝ), Formalism.MainNotions.OrbitPlaces.Shape D L X E → Formalism.MainNotions.OrbitPlaces.CLarge C6 C K ce → Formalism.MainNotions.OrbitPlaces.ValuationSumBound E L ce C :=
  fun D L X K ce E C6 C hS hC => SumOrbCW.sumOrbC D L X K ce E C6 C hS hC
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SzConstantTerm
section
theorem sz_constant_term : PI.SzCt.SzCt :=
  PI.SzCt.UnitaryGroupMassFormula.szCt_of PI.SzCt.UnitaryGroupMassFormula.rowA PI.SzCt.UnitaryGroupMassFormula.rowB PI.SzCt.UnitaryGroupMassFormula.rowC
    PI.SzCt.UnitaryGroupMassFormula.sizeFacts PI.SzCt.UnitaryGroupMassFormula.placeFacts
end

