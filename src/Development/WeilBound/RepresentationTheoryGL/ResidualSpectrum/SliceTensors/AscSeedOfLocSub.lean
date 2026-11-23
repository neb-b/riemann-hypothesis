module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0019
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSlice
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0016
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0012
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0018
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0014
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0013
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.CharZeroCompletion
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

@[expose] public section

namespace PositivityTheory.Rg.Rs

theorem ascAll_holds : AscAll := by
  exact ascAll_of_rest (slice_of dict_holds finTr_holds) pr_holds indMap_holds
    (stringStep_of PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity PositivityTheory.AdelicQuotientData.jacquetShalika.2 infInd2_holds infAsc_holds
      satInd2_holds satAsc_holds satHerm_holds gap_holds)

theorem ascSeed_of_locSub (h : LocSub) : AscSeed := by
  exact ⟨ascAll_holds, C3.clause3Asc_holds h locDual_holds⟩

end PositivityTheory.Rg.Rs
