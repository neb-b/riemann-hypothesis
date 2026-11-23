module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.TwistedFlags.OneMemOffK
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl)
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec eulerFac seg)
open Formalism.UG (qV IsUnifV dosetInd)

namespace GlobalTheory.CompanionTheory.Ipf.Val

section Local

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev Cv : Type := v.adicCompletion K

end Local

section Adelic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FinZeta (projV embV Kv Gv)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsIdemOf IsProjAt rdA grpCo frCo)
open GlobalTheory.CompanionTheory.Ipf.Loc (FPl)

variable {D : D7}

end Adelic

end GlobalTheory.CompanionTheory.Ipf.Val

end
