module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.redZero_of :
    RedZero := by
  intro Q q _ _ hqQ i
  obtain ⟨f, hf_nat, hf_gen⟩ := GlobalTheory.EtC.RedExists.twRed_sec Q q hqQ i
  refine ⟨f, hf_nat, ?_⟩
  intro U a
  apply (_root_.GlobalTheory.EtC.sec_ext_glue (ZMod q) _ U).1
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U _ _ ((GlobalTheory.T.tateTwist_sections_locally_generated Q i).1 U a) ?_
  intro V g h
  rw [SemiMap.nat, ← map_res, ← map_res, hf_nat]
  rcases h with h | ⟨ζ, c, h⟩
  · rw [h]
    simp only [Sec.map, map_zero]
  · rw [h]
    have key := GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i V ζ (GlobalTheory.EtC.RedExists.powPrim hqQ ζ) rfl
    simp only [GlobalTheory.EtC.resGen] at key
    simp only [Sec.map, map_nsmul, map_zsmul] at key ⊢
    rw [key, hf_gen V ζ (GlobalTheory.EtC.RedExists.powPrim hqQ ζ) rfl]
