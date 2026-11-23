module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0114
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProof
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0151
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0006
public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0007

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

theorem objC_true {Q : Par → PtProp} (h : ObjCP Q) : DC.ObjC (fun _ _ _ _ _ _ _ _ _ => True) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch hch
  refine ⟨x0, fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  obtain ⟨p, e1, e2, e3, e4, e5, -⟩ := h s R H q0 a b M c u0 d1 d2 d3 d4 (by rw [← b2] at d5; exact d5) d0 d6 d7 d8 d9
  exact ⟨p, e1, e2, e3, e4, e5, trivial⟩

theorem recS (QO : Par → ∀ D : D7, Obj D → Prop) (cT : ℝ → ℝ → ℝ) (hR : DC.MinkDiv → RecExP (fun κ => DQ.withQD (QO κ)))
    (hM : DC.MinkDiv) : ExD (clsP QO) cT := by
  intro la G hla hH
  have hS : SmallPrimeOne := GlobalTheory.EX.smallPrimeOne_of_primesRel GlobalTheory.Lin.primesRel_holds
  have hO := _root_.GlobalTheory.Fc.objCP_of_recExP _ GlobalTheory.EX.normPrimes_and_levelPrime_unconditional.2 (hR hM)
  have hW : DC.HostWW la G.req := hostWW _ la _ hla (hostQ hS la G hH) (objC_true hO) _root_.GlobalTheory.EX.G4.wClosed
  exact designS (fun κ => ptO (DQ.withQD (QO κ))) cT la G hla hM (kitS _ la G hW hO)

end UpperTheory.Top
