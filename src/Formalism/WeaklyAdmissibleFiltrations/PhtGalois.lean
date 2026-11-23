module

public import Formalism.WeaklyAdmissibleFiltrations.Bundle0001
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Bundle0001
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Bundle0002
public import Formalism.CoboundaryTransfers.StatementAPI
public import Formalism.CoboundaryTransfers.WachBridges
public import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

namespace Formalism.WeaklyAdmissibleFiltrations

theorem pht_galois : CobF ∧ TorsFreeT ∧ CocyclesFunctorial ∧ ImFLe ∧ TrivCrys ∧ ExLattice ∧ ExPD ∧ WachCol :=
  ⟨finiteCocycles_properties.1, finiteCocycles_properties.2.1, finiteCocycles_properties.2.2.1, finiteCocycles_properties.2.2.2, trivialIsCrystalline_holds,
    existsStableLattice_holds, existsPeriodRingData_holds, cokernelLengthEqWach_holds⟩

end Formalism.WeaklyAdmissibleFiltrations
