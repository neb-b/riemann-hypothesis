module

public import Mathlib
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
public import Development.WeilBound.CoreStatements.PeriodRingComparison.AinfAlgebraMaps.CAAlgebraMapGOC
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.Bundle0001

@[expose] public section

noncomputable section
open GroundTheory.PAdicHodge
namespace Cmp6
variable (l : ℕ) [Fact l.Prime]

theorem cA_frob_ainf (w : Reformulated.AutPerF.Ainf l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.frob l (OC l) (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) w)) =
      ACris.phi (K := ℂ_[l]) (p := l) (cA l (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) w)) := by
  rw [Reformulated.AutPerF.Acris.frob_algebraMap, cA_algebraMap, cA_algebraMap]
  have h : Formalism.Per6.ainfMap l (WittVector.frobenius w) =
      WittVector.frobenius (Formalism.Per6.ainfMap l w) := by
    ext n
    simp [Formalism.Per6.ainfMap, WittVector.map_coeff, WittVector.coeff_frobenius_charP]
  rw [ACris.phi_algebraMap]
  exact congrArg (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)) h

theorem cA_frob (x : Reformulated.AutPerF.Acris l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.frob l (OC l) x) = ACris.phi (K := ℂ_[l]) (p := l) (cA l x) := by
  have h : (cA l).toRingHom.comp (Reformulated.AutPerF.Acris.frob l (OC l)) =
      (ACris.phi (K := ℂ_[l]) (p := l)).comp (cA l).toRingHom := by
    refine Reformulated.AutPerF.Acris.hom_ext fun a => ?_
    have := zero_ext l
      (F := ((cA l).toRingHom.comp (Reformulated.AutPerF.Acris.frob l (OC l))).comp
        (algebraMap (Reformulated.AutPerF.AcrisZero l (OC l)) (Reformulated.AutPerF.Acris l (OC l))))
      (G := ((ACris.phi (K := ℂ_[l]) (p := l)).comp (cA l).toRingHom).comp
        (algebraMap (Reformulated.AutPerF.AcrisZero l (OC l)) (Reformulated.AutPerF.Acris l (OC l))))
      (fun w => by
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply]
        exact cA_frob_ainf l w) a
    simpa only [RingHom.comp_apply] using this
  exact RingHom.congr_fun h x

end Cmp6
