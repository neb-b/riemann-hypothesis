module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.UpCycOf

@[expose] public section

open NumberField UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd GlobalTheory.CuspRep GlobalTheory.GalOfCusp Formalism.ConjugateSelfDual ReciprocityTheory.Gal

private theorem contTwist {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {n : ℕ} {r : Γ →* GL (Fin n) k} {χ : Γ →* kˣ} (hr : Continuous r) (hχ : Continuous χ) :
    Continuous (tw r χ) := by
  have h : Continuous fun s => ((tw r χ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    simp only [tw_val]
    exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hr)
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  have e : (fun s => (((tw r χ s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      (fun s => ((tw r χ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ∘ fun s => s⁻¹ := by
    funext s
    simp only [Function.comp_apply, map_inv]
  rw [e]
  exact h.comp continuous_inv
