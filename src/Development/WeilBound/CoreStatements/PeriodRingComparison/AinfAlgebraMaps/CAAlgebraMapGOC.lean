module

public import Mathlib
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective

@[expose] public section

noncomputable section

open GroundTheory.PAdicHodge
open Formalism.BasicNotions.Loc (GQ)

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

def gOC (g : GQ l) : OC l →+* OC l := MulSemiringAction.toRingHom (GQ l) (OC l) g

theorem smul_cp_eq (g : GQ l) (y : ℂ_[l]) : g • y = galCp (Formalism.Per6.toBot g) y := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_const_smul g) (continuous_galCp _)) fun a => ?_
  rw [Reformulated.AutPerF.padicComplex_smul_coe, galCp_coe]
  rfl

theorem coe_gOC (g : GQ l) (x : OC l) :
    ((gOC l g x : OC l) : ℂ_[l]) = galCp (Formalism.Per6.toBot g) (x : ℂ_[l]) :=
  smul_cp_eq l g x

theorem tiltMap_gOC (g : GQ l) : Reformulated.AutPerF.Tilt.map l (gOC l g) = PositivityTheory.LocInh.galT g := by
  refine RingHom.ext fun x => ?_
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (Reformulated.AutPerF.Tilt.map l (gOC l g) x) =
    PreTilt.coeff n (PositivityTheory.LocInh.galT g x)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  have h1 := PositivityTheory.LocInh.frob_coeff_tiltMap x n y hy.symm
  have h2 : PreTilt.coeff n (PositivityTheory.LocInh.galT g x) = (Formalism.Per6.modPEquiv l).symm
      (modPMap (galCp (Formalism.Per6.toBot g) : ℂ_[l] →+* ℂ_[l]) (AInf.norm_galCp_toRingHom (Formalism.Per6.toBot g))
        (PreTilt.coeff n (Formalism.Per6.tiltMap l x))) := rfl
  rw [h2, h1, modPMap_mk]
  rw [Reformulated.AutPerF.Tilt.coeff_map, ← hy, Ideal.quotientMap_mk]
  apply congrArg
  apply Subtype.ext
  exact coe_gOC l g y

theorem ainfMap_gOC (g : GQ l) (a : Reformulated.AutPerF.Ainf l (OC l)) :
    Formalism.Per6.ainfMap l (Reformulated.AutPerF.Ainf.map l (gOC l g) a) =
      Formalism.Per6.toBot g • Formalism.Per6.ainfMap l a := by
  rw [Reformulated.AutPerF.Ainf.map, tiltMap_gOC]
  refine WittVector.ext fun n => ?_
  rw [AInf.gal_smul_coeff]
  exact PositivityTheory.LocInh.tiltMap_tiltInv l _

theorem cA_algebraMap_gOC (g : GQ l) (w : Reformulated.AutPerF.Ainf l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.map l (gOC l g) (algebraMap _ (Reformulated.AutPerF.Acris l (OC l)) w)) =
      ACris.galCris (Formalism.Per6.toBot g) (cA l (algebraMap _ (Reformulated.AutPerF.Acris l (OC l)) w)) := by
  rw [Reformulated.AutPerF.Acris.map_algebraMap, cA_algebraMap, cA_algebraMap, ainfMap_gOC,
    ← ACris.gal_smul_algebraMap, ACris.gal_smul_def]

theorem zero_ext {F G : Reformulated.AutPerF.AcrisZero l (OC l) →+* ACris.ACris ℂ_[l] l}
    (h : ∀ w : Reformulated.AutPerF.Ainf l (OC l), F (algebraMap _ _ w) = G (algebraMap _ _ w))
    (a : Reformulated.AutPerF.AcrisZero l (OC l)) : F a = G a := by
  obtain ⟨⟨w, _, k, rfl⟩, hw⟩ := IsLocalization.surj
    (Submonoid.powers (l : Reformulated.AutPerF.Ainf l (OC l))) (a : Reformulated.AutPerF.AinfInv l (OC l))
  have ha : a * (l : Reformulated.AutPerF.AcrisZero l (OC l)) ^ k = algebraMap _ _ w := by
    apply Subtype.ext
    simpa using hw
  have e : F a * (l : ACris.ACris ℂ_[l] l) ^ k = G a * (l : ACris.ACris ℂ_[l] l) ^ k := by
    calc F a * (l : ACris.ACris ℂ_[l] l) ^ k = F (a * (l : Reformulated.AutPerF.AcrisZero l (OC l)) ^ k) := by
          rw [map_mul, map_pow, map_natCast]
      _ = G (a * (l : Reformulated.AutPerF.AcrisZero l (OC l)) ^ k) := by rw [ha, h]
      _ = G a * (l : ACris.ACris ℂ_[l] l) ^ k := by rw [map_mul, map_pow, map_natCast]
  apply ACris.iota_injective (K := ℂ_[l]) (p := l)
  refine ((IsPerfectoidField.isUnit_natCast_p_bDeRhamPlus (K := ℂ_[l]) l).pow k).mul_right_cancel ?_
  have e' := congrArg (ACris.iota ℂ_[l] l) e
  rwa [map_mul, map_mul, map_pow, map_natCast] at e'

theorem cA_map_gal (g : GQ l) (x : Reformulated.AutPerF.Acris l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.map l (gOC l g) x) = ACris.galCris (Formalism.Per6.toBot g) (cA l x) := by
  have key : (cA l).toRingHom.comp (Reformulated.AutPerF.Acris.map l (gOC l g)) =
      (ACris.galCris (Formalism.Per6.toBot g)).comp (cA l).toRingHom := by
    refine Reformulated.AutPerF.Acris.hom_ext fun a => ?_
    refine zero_ext l (F := ((cA l).toRingHom.comp (Reformulated.AutPerF.Acris.map l (gOC l g))).comp
      (algebraMap _ _)) (G := ((ACris.galCris (Formalism.Per6.toBot g)).comp (cA l).toRingHom).comp
      (algebraMap _ _)) (fun w => ?_) a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← IsScalarTower.algebraMap_apply]
    exact cA_algebraMap_gOC l g w
  exact RingHom.congr_fun key x

end Cmp6
