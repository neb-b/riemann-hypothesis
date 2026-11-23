module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfFfX
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LocalOmegaVolumeUnique
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0031

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVLocU_holds : OmVLocU X ψ := fun v a Y =>
  PI.OmLocU.Done.omLocU_closed X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) a Y

theorem omVBadT_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  PI.OmVg.omVBadT_of_ffX X u' ψ (Formalism.L2.SG.Pf.NcX.OmVSt.omega_standard_holds X ψ) (Formalism.L2.SG.Pf.NcX.OmVSt.omega_lattice_holds X)
    (OmW.omVGram_holds X u') PI.OmVe.Top.fFInertB_holds PI.OmVe.Top.fFSplitB_holds

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVZGram : OmVGram X u' := Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.omVGram_holds X u'

theorem omVZDet : OmVDet X u' := Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.omVDet_holds X u'

theorem omVZLocU : OmVLocU X ψ := Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omVLocU_holds X ψ

theorem omVZ_holdsX : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  omV_of X u' ψ (omega_standard_holds X ψ) (omega_lattice_holds X) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.omVSD_holdsX X)
    (omega_unramified_holds X) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.omVPrim_holdsX X u') (omVZGram X u') (omVZDet X u')
    (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc.omVScale_holdsX X u' ψ) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omVBadT_holdsX X u' ψ)
    (omVZLocU X ψ)

end Formalism.L2.SG.Pf.NcX.OmVSt

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem omV_holdsX {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  Formalism.L2.SG.Pf.NcX.OmVSt.omVZ_holdsX X u' ψ

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ
