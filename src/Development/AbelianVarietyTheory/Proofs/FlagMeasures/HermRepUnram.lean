module

public import Mathlib
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0382
public import Formalism.HermitianLattices.Bundle0003

@[expose] public section

namespace GlobalTheory

theorem hermRepUnram : Formalism.HermitianLattices.Ext.L3.HermRepUnram := _root_.GlobalTheory.BinaryRep.represents_totallyPositive

instance : Fact (Formalism.HermitianLattices.Ext.L3.HermRepUnram) := ⟨hermRepUnram⟩

end GlobalTheory
