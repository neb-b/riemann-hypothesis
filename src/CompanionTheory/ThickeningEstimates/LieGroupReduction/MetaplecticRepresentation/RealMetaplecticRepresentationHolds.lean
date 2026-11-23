module

public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.Bundle0001
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticUnipotentBlockSecondDiag
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.Bundle0003
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.Bundle0002

@[expose] public section

open CompanionTheory.ThKR.Mp in
theorem CompanionTheory.ThKR.realMetaplecticRepresentation_holds : GlobalTheory.Published.RealMetaplecticRepresentation :=
  realMetaplectic_of_forall fun l _ _ _ =>
    have hS : SecEx l := secEx_of mkElt nrmUp
    have hO : Surj l := surj_of ddNe hS
    have hN : NearOne l := nearOne_of hS ker secDer
    have hC : Cover l := cover_of topG hO ker hS secDer
    ⟨topG, hC, hO, ker, smooth_of topG hN secDer, onePar_of topG hC hN secDer⟩
