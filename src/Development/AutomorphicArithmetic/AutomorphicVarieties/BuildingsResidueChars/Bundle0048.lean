module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0022
public import Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalSpanRangeOfColumnsMem

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgebraicModuleOfVanishingBlock
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private def carry {M : Type} [AddCommGroup M] [Module ℂ M] (W Z : Submodule ℂ M) : Submodule ℂ (Module.End ℂ M) where
  carrier := {T | ∀ x ∈ W, T x ∈ Z}
  add_mem' h1 h2 x hx := Z.add_mem (h1 x hx) (h2 x hx)
  zero_mem' _ _ := Z.zero_mem
  smul_mem' c _ h x hx := Z.smul_mem c (h x hx)

theorem UpperTheory.algebraic_module_of_vanishing_block :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), S ≤ NInv K (r + s) r → Centre S → ∀ (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ), AlgMod S (Van K r s) (archCapBlock D (e1 r s) τ u) ∧ AlgMod S (Van K r s) (archCapBlock D (e2 r s) τ u) := by
  intro K _ _ r s S hS hC ι _ D τ u
  have hrel : Formalism.REAL.GlRel (gen D (lam K (r + s)) τ) :=
    (UpperTheory.gen_glRelations_and_commute_of_isLie _ ι (r + s) _ D (lam K (r + s)) (isLie_lam K (r + s))).1 τ
  have hW : ∀ p q, ∀ x ∈ NInv K (r + s) r, gen D (lam K (r + s)) τ p q x ∈ NInv K (r + s) r := fun p q =>
    gen_mem D (lam K (r + s)) τ p q (carry (NInv K (r + s) r) (NInv K (r + s) r))
      fun y x hx => UpperTheory.uAction_mem_unipotentInvariant K (r + s) r _ x hx
  have hZ : ∀ (p : Fin r) (q : Fin s), ∀ x ∈ NInv K (r + s) r,
      gen D (lam K (r + s)) τ (Fin.castAdd s p) (Fin.natAdd r q) x ∈ Van K r s := fun p q =>
    gen_mem D (lam K (r + s)) τ _ _ (carry (NInv K (r + s) r) (Van K r s))
      fun y x hx => UpperTheory.archExp_single_unipotent_embedding K r s p q y x hx
  have hq : ∀ v, AlgMod S ⊥ (Formalism.REAL.qdet (gen D (lam K (r + s)) τ) v) := fun v => by
    refine UpperTheory.algMod_bot_of_mem_adjoin_commuting _ S (uAction '' ((isExpLieAlgebra K (r + s)).centerU : Set (UEnv K (r + s)))) ?_ ?_ _
      (UpperTheory.qdet_generates_universalEnveloping_centre K (r + s) ι D τ v)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact Zc_comm (uAction_mem_Zc hx) (uAction_mem_Zc hy)
    · rintro _ ⟨z, hz, rfl⟩
      exact hC z hz
  exact UpperTheory.algMod_quantumDet_leviBlocks_of_parabolic _ r s (gen D (lam K (r + s)) τ) hrel (NInv K (r + s) r) (Van K r s) S hS hW hZ hq u
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.isAutomorphicForm_of_bdd_submodule :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → ∀ φ ∈ S, IsAutomorphicForm φ.1 := by
  intro K _ _ n S hS φ hφ
  obtain ⟨V, hV, hVφ⟩ := UpperTheory.exists_finiteDimensional_compact_translates_of_level_types K n S hS.level hS.types
  refine ⟨hS.left φ hφ, ⟨φ.2, ?_⟩, ?_, ?_, hS.growth φ hφ⟩
  · intro g
    obtain ⟨L, hL, hLφ⟩ := hS.level
    filter_upwards [hL.mem_nhds L.one_mem] with y hy
    exact hLφ φ hφ y hy g
  · exact UpperTheory.finiteDimensional_span_range_of_columns_mem (Reduction.maxCompact (K := K) (n := n)) _
      (fun k g => (φ : AdelicGLn.AdelicGL K n → ℂ) (g * k)) V hV (fun g => hVφ φ hφ g)
  · exact UpperTheory.isZFinite_of_centre_span K n φ (hS.mono ((Submodule.span_singleton_le_iff_mem _ _).mpr hφ)).centre
end

