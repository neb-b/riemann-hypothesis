module

public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
public import Formalism.HermitianCurvature.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.Bundle0003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.Bundle0001

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.WignerShift

theorem update_eq_uPlus (u : ℕ → ℝ) (l n₀ : ℕ) :
    Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ)) = uPlus u l n₀ := by
  funext i
  unfold uPlus
  rw [Function.update_apply]
  split_ifs with h
  · rw [h]
  · rfl

theorem update_eq_uMinus (u : ℕ → ℝ) (l n₀ : ℕ) :
    Function.update u l (u l - (n₀ : ℝ)) = uMinus u l n₀ := by
  funext i
  unfold uMinus
  rw [Function.update_apply]
  split_ifs with h
  · rw [h]
  · rfl

theorem wigExists : WigExists := by
  intro k r z z' Wq _ _ _ π' u l n₀ b hz hz' hT hT' hπ hdec hl1 hlk hgap hb3 hb
  have hreg := _root_.GlobalTheory.CompanionTheory.TypeGaps.gap_eq_nat_add_one Wq k r z' π' u hz' hT' hπ hdec
  have h1 := abs_le.mp (hb l (Finset.mem_Icc.mpr ⟨hl1, hlk.le⟩))
  have h2 := abs_le.mp (hb (l + 1) (Finset.mem_Icc.mpr ⟨by omega, hlk⟩))
  have hn : (n₀ : ℝ) ≤ b := by linarith [h1.2, h2.1]
  obtain ⟨Vp, iP1, iP2, iP3, Vm, familyMassRatio, familyMassSecondLine, iM3, πp, πm, Ap, Am, hπp, hπm, hAp, hAm, hlow⟩ :=
    GlobalTheory.WigSh.exists_shifted_types_lower_bound Wq k r z' π' u l n₀ b hz' hT' hπ hreg hl1 hlk hgap hb hn
      (by linarith)
  rw [update_eq_uPlus] at hπp
  rw [update_eq_uMinus] at hπm
  exact ⟨{
    Wqp := Vp
    Wqm := Vm
    πp := πp
    πm := πm
    Ap := fun g => Ap (GlobalTheory.WigSh.omg k r z z' g)
    Am := fun g => Am (GlobalTheory.WigSh.omg k r z z' g)
    typeP := hπp
    typeM := hπm
    polyP := _root_.GlobalTheory.CompanionTheory.WigOmgPoly.polyOp_wigMap_omg Wq Vp k r z z' π' πp n₀ Ap hz hT hz' hT' hAp
    polyM := _root_.GlobalTheory.CompanionTheory.WigOmgPoly.polyOp_wigMap_omg Wq Vm k r z z' π' πm n₀ Am hz hT hz' hT' hAm
    equivP := GlobalTheory.T.wigEquiv_of_wigMap_of_isCRepOn Wq Vp k r z z' π' πp n₀ Ap hz hT hz' hT' hAp hπp.2.1
    equivM := GlobalTheory.T.wigEquiv_of_wigMap_of_isCRepOn Wq Vm k r z z' π' πm n₀ Am hz hT hz' hT' hAm hπm.2.1
    upperP := _root_.GlobalTheory.CompanionTheory.WigAtOmega.wigUpper_omg Wq Vp k r z z' π' πp n₀ Ap hz hT hz' hT' hAp
    upperM := _root_.GlobalTheory.CompanionTheory.WigAtOmega.wigUpper_omg Wq Vm k r z z' π' πm n₀ Am hz hT hz' hT' hAm
    lower := _root_.GlobalTheory.CompanionTheory.WigLowerOmg.wigLower_omg Wq Vp Vm k r z z' b n₀ Ap Am hz hT hz' hT' hlow }⟩

end GlobalTheory.CompanionTheory.WignerShift
