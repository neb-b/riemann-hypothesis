module

public import Mathlib
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcrisPlusHomAlgebraMap
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Bundle0002
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.Bundle0001
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
public import Development.WeilBound.CoreStatements.PeriodRingComparison.AinfAlgebraMaps.CAAlgebraMapGOC

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcFrob
section
noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem bcris_hom_ext_acris {B : Type} [CommRing B] {f g : Reformulated.AutPerF.Bcris l (OC l) →+* B}
    (h : ∀ x : Reformulated.AutPerF.Acris l (OC l),
      f (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l)) x) =
        g (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l)) x)) : f = g := by
  apply Reformulated.AutPerF.Bcris.hom_ext
  intro z
  have h2 : f.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))) =
      g.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))) := by
    apply Reformulated.AutPerF.BcrisPlus.hom_ext
    intro y
    exact h y
  exact RingHom.congr_fun h2 z

theorem cBc_frob_of
    (hφ : ∀ x, cA l (Reformulated.AutPerF.Acris.frob l (OC l) x) =
      ACris.phi (K := ℂ_[l]) (p := l) (cA l x))
    (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (Reformulated.AutPerF.Bcris.frob l (OC l) b) = Formalism.Per6.φB l (cBc l b) := by
  have h : (cBc l).toRingHom.comp (Reformulated.AutPerF.Bcris.frob l (OC l)) =
      (Formalism.Per6.φB l).comp (cBc l).toRingHom :=
    bcris_hom_ext_acris l fun x => by
      change cBc l (Reformulated.AutPerF.Bcris.frob l (OC l) _) = Formalism.Per6.φB l (cBc l _)
      rw [Reformulated.AutPerF.Bcris.frob_algebraMap_acris, cBc_algebraMap, cBc_algebraMap, hφ]
      exact (PositivityTheory.LocInh.φB_cB (cA l x)).symm
  exact RingHom.congr_fun h b

theorem cBc_aB (a : Reformulated.AutPerF.Ainf l (OC l)) :
    cBc l (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))
      (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) a)) =
      Formalism.Per6.aB l a := by
  rw [cBc_algebraMap, cA_algebraMap]
  exact (PositivityTheory.LocInh.frob_aB_apply a).symm

theorem algebraMap_ainf_eq_zA (z : ℤ_[l]) :
    algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z = Formalism.Per6.zA l z := rfl

theorem cBc_zB (z : ℤ_[l]) :
    cBc l (algebraMap ℚ_[l] (Reformulated.AutPerF.Bcris l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zB l z := by
  have h : algebraMap ℤ_[l] (Reformulated.AutPerF.Acris l (OC l)) z =
      algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l))
        (algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z) := rfl
  rw [Reformulated.AutPerF.Bcris.algebraMap_padicInt, h, cBc_aB, algebraMap_ainf_eq_zA, Formalism.Per6.zB,
    RingHom.comp_apply]

end Cmp6
end
end

-- bundled from Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcrisLogTeichmullerEqT
section
noncomputable section

open GroundTheory.PAdicHodge
open Formalism.BasicNotions.Loc (GQ)

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem cBc_gal (g : GQ l) (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g) b) =
      Formalism.Per6.σB g (cBc l b) := by
  have key : ((cBc l).toRingHom.comp
      (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g))).comp
        (cBc l).symm.toRingHom = Formalism.Per6.σB g :=
    PositivityTheory.LocInh.bcris_hom_ext fun y => by
      change cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g)
        ((cBc l).symm (Formalism.Per6.cB l y))) = _
      rw [cBc_symm_cB, Reformulated.AutPerF.Bcris.map_algebraMap_acris (gOC l g) (Reformulated.AutPerF.toRingHom_injective g),
        cBc_algebraMap, cA_map_gal,
        RingEquiv.apply_symm_apply]
      exact (PositivityTheory.LocInh.σB_cB g y).symm
  have h := RingHom.congr_fun key (cBc l b)
  change cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g)
    ((cBc l).symm (cBc l b))) = _ at h
  rwa [RingEquiv.symm_apply_apply] at h

theorem cBc_smul (g : GQ l) (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (g • b) = Formalism.Per6.σB g (cBc l b) :=
  cBc_gal l g b

end Cmp6
end
end

