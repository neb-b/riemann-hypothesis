module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallinePointsSaturatedOrdinaryIdealArtinian
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatedOrdIdealPointsIsLCrystalline

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem ideal_cuts_crystalline_locus : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)),
    GlobalTheory.OrdLoc.PtsCr D U (GlobalTheory.OrdLoc.IY D U) ∧ GlobalTheory.OrdLoc.CrPts D U (GlobalTheory.OrdLoc.IY D U) := by
  intro hP l _ O _ _ _ _ _ _ _ D U
  exact ⟨_root_.GlobalTheory.OrdLoc.ptsCr_IY hP D U, _root_.GlobalTheory.OrdLoc.crPts_IY hP D U⟩

end GlobalTheory.OrdLoc
