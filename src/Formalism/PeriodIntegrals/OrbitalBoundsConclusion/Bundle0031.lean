module

public import Formalism.PeriodIntegrals.Bundle0022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupHaar.RootHaarMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.OrbitsAddAtConjugate
public import Formalism.PeriodIntegrals.Bundle0023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.OrbitRestriction
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarRelationReflexive.IsScalarRefl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.SizeDel
public import Development.AutomorphicArithmetic.OrbitLabellings.SzEatIFree
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.TermStableHolds

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRootHaar
section
theorem amplifier_root_haar : PI.AmpRootH.RootHaar := PI.AmpRootHaarW.rootHaar_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbAddOne
section
theorem PI.OrbAddOne : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddAtConjugate E :=
  PI.OrbJet.AO.orbitsAddAtConjugate
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbRestr
section
theorem PI.OrbRestr : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestriction E :=
  PI.OrbJet.OrbW.orbitRestriction
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalRelRepFree
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scalar_rep_free (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalRelRepFree.ScalarRepFree D u u' := by
  intro F0 Λ hrow x y y' hrel hsc
  obtain ⟨n, hn, m, hm, hfr, hzt⟩ := hrel
  exact PI.UnitaryGroupMassFormula.ScalRelRepFree.scalRel_move Λ hrow.1.1 _ _ (lf D F0) x.1.1 y.1.1 y'.1.1 n m
    ⟨hrow.2.1.2.2.1, y.1.2.1, hn, hm, hfr, hzt⟩ hsc

end
end
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SzEatI
section
theorem sz_eat_identity : PI.SzEatI.SzEatI := UpperTheory.G2.szEatI_of_stepA PI.SzEatI.W.stepA
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermCarrierStable
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_carrier_stable (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermStable D u u' :=
  PI.TCS.termStable_holds D u u'
end

