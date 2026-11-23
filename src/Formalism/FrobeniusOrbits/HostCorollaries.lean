module

public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Bundle0001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Bundle0002
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrderOfSignGroupDvdTwo
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
public import Mathlib
public import Formalism.FrobeniusOrbits.HostThickExists
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ExistsOpenNormalOrderOf
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrdUnimod
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.NcardEqTwoIff
public import Formalism.FrobeniusOrbits.Bundle0001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum

@[expose] public section

namespace Formalism.FrobeniusOrbits.Final

open Formalism.FrobeniusOrbits

theorem conj : HostConj := hostConj_of hostGalois hostGalSpec
theorem real : HostReal := hostReal_of hostGalois hostGalSpec conj
theorem f1 : TwoPowerCyclotomicLayerRealSubfieldCharacterization := real_subfield_of_galois_spec hostGalSpec
theorem cmType : HostCMType := hostCMType_of hostGalois hostGalSpec
theorem frob : HostFrob := hostFrob_of hostGalois hostGalSpec
theorem splitK : HostSplitK := hostSplitK_of (hostFrob_of hostGalois hostGalSpec)
theorem efgTwo : HostEFGTwo := hostEFGTwo_of hostInertia hostDecomp

theorem host_field :
    HostExample ∧ HostGroup ∧ HostOrders ∧ HostRecip ∧ HostFixed ∧ HostGalois ∧ HostGalSpec ∧
    HostConj ∧ HostReal ∧ TwoPowerCyclotomicLayerRealSubfieldCharacterization ∧ HostMu ∧ HostFrob ∧ HostInertia ∧ HostUnramEF ∧
    HostDecomp ∧ HostDecompConj ∧ HostEFGTwo ∧ HostSplitK ∧ HostCMType :=
  ⟨hostExample, hostGroup, hostOrders, hostRecip, hostFixed, hostGalois, hostGalSpec, conj, real, f1, hostMu,
    frob, hostInertia, hostUnramEF, hostDecomp, hostDecompConj, efgTwo, splitK, cmType⟩

end Formalism.FrobeniusOrbits.Final
