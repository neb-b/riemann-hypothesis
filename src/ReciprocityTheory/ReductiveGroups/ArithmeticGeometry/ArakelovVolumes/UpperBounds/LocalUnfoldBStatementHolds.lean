module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivCoreUpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0023

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem localUnfoldBStatement_holds : LocalUnfoldBStatement (E := E) :=
  LUB.localUnfoldB_of lu_holds

theorem ontoWeightStatement_holds : OntoWeightStatement (E := E) :=
  OW.ontoWeight_of localUnfoldBStatement_holds

theorem divCoreStatement_holds : DivCoreStatement (E := E) :=
  divCore_up_of ontoWeightStatement_holds upDiv_holds DivStartStatement_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
