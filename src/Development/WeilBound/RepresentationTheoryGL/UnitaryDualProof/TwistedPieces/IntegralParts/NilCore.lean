module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.SuppCongr
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.OrbQ
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.FibreQuotientHolds
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.BaseVanishing.VanOf
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.BezoutHypotheses.ContinuousHom

@[expose] public section

namespace PositivityTheory.RgUd.TP.Nil.Final

open PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nilCore (hT : TraceForm k) (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : NilCore k :=
  PositivityTheory.RgUd.TP.Nil.Asm.nilCore_of k (PositivityTheory.RgUd.TP.Nil.Four.fourQ k) (PositivityTheory.RgUd.TP.Nil.Orb.orbQ k)
    (PositivityTheory.RgUd.TP.Nil.Fib2.fibQ k) (PositivityTheory.RgUd.TP.Nil.Base.baseQ k) hT hU

end PositivityTheory.RgUd.TP.Nil.Final
