module

public import Mathlib
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective

@[expose] public section

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem untilt_tiltMap (x : Reformulated.AutPerF.Tilt l (OC l)) :
    PreTilt.untilt (Formalism.Per6.tiltMap l x) = e l (PreTilt.untilt x) := by
  rw [← tiltMap_eq]
  exact Reformulated.AutPerF.Tilt.untilt_map (e l).toRingHom x

theorem untilt_epsilon_eq_one : PreTilt.untilt (PositivityTheory.LocInh.εO l) = (1 : OC l) := by
  apply (e l).injective
  rw [← untilt_tiltMap, PositivityTheory.LocInh.εO, PositivityTheory.LocInh.tiltMap_tiltInv, map_one]
  exact untilt_epsilon

def eps0 : Reformulated.AutPerF.tateModule l (OC l) := ⟨PositivityTheory.LocInh.εO l, untilt_epsilon_eq_one l⟩

theorem tiltMap_epsilon : Formalism.Per6.tiltMap l (eps0 l).1 = epsilon l := (PositivityTheory.LocInh.tiltMap_tiltInv l _)

theorem epsilon_isPrimitive : Reformulated.AutPerF.IsPrimitive (eps0 l) := by
  unfold Reformulated.AutPerF.IsPrimitive
  intro h
  have hne : PreTilt.untilt ((frobeniusEquiv (PreTilt (NC l) l) l).symm (epsilon l)) ≠ 1 := by
    rw [epsilon, AInf.frobeniusEquiv_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible]
    intro h
    exact rootSeq_one_ne_one (congrArg Subtype.val h)
  apply hne
  have h1 : Formalism.Per6.tiltMap l ((frobeniusEquiv (Reformulated.AutPerF.Tilt l (OC l)) l).symm (eps0 l).1) =
      (frobeniusEquiv (PreTilt (NC l) l) l).symm (epsilon l) := by
    rw [RingHom.map_frobeniusEquiv_symm, tiltMap_epsilon]
  rw [← h1, untilt_tiltMap, h, map_one]

end Cmp6
