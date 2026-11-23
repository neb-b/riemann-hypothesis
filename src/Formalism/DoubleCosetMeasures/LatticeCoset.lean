module

public import Formalism.DoubleCosetMeasures.Statement
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.Bundle0001
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LowUniMulVecELast
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MulInvBlockDiagApplySameBlock
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.ExistsContinuousLowerUpperEntry
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.Bundle0002
public import Formalism.DoubleCosetMeasures.StatementZ
public import Formalism.DoubleCosetMeasures.StatementV
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MeasureUniformizerMatrixSetMulCard

@[expose] public section

namespace Formalism.DoubleCosetMeasures.Final

open Formalism.DoubleCosetMeasures

theorem intTwoSided : Formalism.DoubleCosetMeasures.IntTwoSided := Formalism.DoubleCosetMeasures.P.intTwoSided
theorem simpleAdd : Formalism.DoubleCosetMeasures.SimpleAdd := Formalism.DoubleCosetMeasures.P.simpleAdd
theorem intInv : Formalism.DoubleCosetMeasures.IntInv := Formalism.DoubleCosetMeasures.P.intInv
theorem isoInv : Formalism.DoubleCosetMeasures.IsoInv := Formalism.DoubleCosetMeasures.P.isoInv
theorem isoFinite : Formalism.DoubleCosetMeasures.IsoFinite := Formalism.DoubleCosetMeasures.P.isoFinite
theorem bbFinite : Formalism.DoubleCosetMeasures.BBFinite := Formalism.DoubleCosetMeasures.P.bbFinite_of intTwoSided intInv isoInv simpleAdd
theorem bbNorm : Formalism.DoubleCosetMeasures.BBNorm := Formalism.DoubleCosetMeasures.P.bbNorm_of bbFinite
theorem phaseWellDef : Formalism.DoubleCosetMeasures.PhaseWellDef := Formalism.DoubleCosetMeasures.P.phaseWellDef
theorem suppCompact : Formalism.DoubleCosetMeasures.SuppCompact := Formalism.DoubleCosetMeasures.P.suppCompact
theorem lemmaUSplit : Formalism.DoubleCosetMeasures.LemmaUSplit := Formalism.DoubleCosetMeasures.P.lemmaUSplit
theorem glRed : Formalism.DoubleCosetMeasures.GLRed := Formalism.DoubleCosetMeasures.P.glRed
theorem volII : Formalism.DoubleCosetMeasures.VolII := Formalism.DoubleCosetMeasures.P.volII
theorem volJadd : Formalism.DoubleCosetMeasures.VolJadd := Formalism.DoubleCosetMeasures.P.volJadd

end Formalism.DoubleCosetMeasures.Final
