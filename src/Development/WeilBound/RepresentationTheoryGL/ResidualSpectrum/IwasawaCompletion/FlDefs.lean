module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.LeviMaps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3.Fl

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def wPart (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : GA E N →* GL (Fin N) (w.adicCompletion E) :=
  Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E))

abbrev iota (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : GL (Fin N) (w.adicCompletion E) →* GA E N :=
  (finGL E N).comp (locGL E N w)

def awayPart (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) (g : GA E N) : GA E N :=
  g * (iota N w (wPart N w g))⁻¹

end PositivityTheory.Rg.Rs.C3.Fl

end
