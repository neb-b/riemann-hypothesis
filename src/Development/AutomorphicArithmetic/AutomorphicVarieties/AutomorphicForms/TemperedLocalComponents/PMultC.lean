module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0194
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong

@[expose] public section

theorem UpperTheory.V.Af.cuspMultOneGL :
    GlobalTheory.Published.CuspidalMultiplicityOne := by
  intro E _ _ _ a π π' h
  have hi : π.Iso π' := Quotient.exact h
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  apply UpperTheory.V.Af.strongMultOneC E a π π'
  filter_upwards [GlobalTheory.CuspRep.AeFix.eventually_mem_fixed E a π ⟨φ, hφ⟩] with w hw
  obtain ⟨B, hB⟩ := GlobalTheory.CuspRep.UnrSat.exists_hasSatGL_locRep UpperTheory.V.Af.formsFiniteGL E a π w
    ((Submodule.ne_bot_iff _).2 ⟨_, hw, fun e => h0 (congrArg Subtype.val e)⟩)
  exact ⟨B, hB, hi.hasSatGL hB⟩
