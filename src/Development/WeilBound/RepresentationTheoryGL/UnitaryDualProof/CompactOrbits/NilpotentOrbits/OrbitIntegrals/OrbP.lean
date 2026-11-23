module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CompactPowers.ExistsPowSmulMemOfIsCompact
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.IdempotentFibres.TraceNeZeroOfIdem
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ImportsAlt
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.NabsPow
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.SupportedComposition.ProjectionOfOrbitClosure
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.StepModPf

@[expose] public section

namespace PositivityTheory.RgUd.T.Nil.Orb.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem orbP [CharZero k] : OrbP (k := k) :=
  Oasm.orbP_of k (Ozn.zNClosed (k := k)) (Ofib.fibZN (k := k)) (BReps.reps k) (BStep.stepMod_pf k) (BModbound.modBound k)

end PositivityTheory.RgUd.T.Nil.Orb.Final
