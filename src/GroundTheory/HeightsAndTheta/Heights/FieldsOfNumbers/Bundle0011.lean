module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleSupport
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DivCycleSupport.proof : DivCycleSupport.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hdim c f hf hfP W hW
  have h : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hW (by rw [divCycle, dite_eq_right h])
  obtain ⟨hmin, hrel⟩ := h
  have hWh : IsMultiHomogIdeal W := (Bridge.isMultiHomogIdeal_iff W).mpr
    (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
      ((Bridge.isMultiHomogIdeal_iff P).mp hP.multiHomog) ((Bridge.isMultiHomog_iff f c).mp hf) hmin)
  refine ⟨⟨hmin.1.1, hWh, hrel⟩, ?_⟩
  have := hP.isPrime
  have hPd : ringKrullDim (MRing ι F ⧸ P) = ((Fintype.card K + n + 1 : ℕ) : WithBot ℕ∞) := by
    apply relDim_map_injective (K := K)
    change relDim P = _
    rw [hdim]
    show (((n + 1 : ℕ) : ℤ) : WithBot (WithTop ℤ)) =
      ((((Fintype.card K + n + 1 : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ))
    congr 1
    push_cast
    ring
  have key : ringKrullDim (MRing ι F ⧸ W) + 1 = ringKrullDim (MRing ι F ⧸ P) :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_quot_minimal_add_one hfP hmin (fun h => by
      rw [hPd] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
  rw [hPd] at key
  have hWd := ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key
  rw [relDim_of_ringKrullDim_eq W _ hWd]
  show ((((Fintype.card K + n : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) =
    (((n : ℕ) : ℤ) : WithBot (WithTop ℤ))
  congr 1
  push_cast
  ring

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameHilbFn
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem map_comap_renameEquiv {F : Type u} [Field F] {S K' : Type} {κ : S → Type}
    {ι' : K' → Type} (σ : (Σ s, κ s) ≃ (Σ k', ι' k')) (P : Ideal (MRing ι' F)) :
    (P.comap (rename σ)).map (renameEquiv F σ) = P := by
  have h : P.comap (rename σ) = P.comap (renameEquiv F σ) := rfl
  rw [h]
  exact Ideal.map_comap_of_surjective _ (renameEquiv F σ).surjective P

theorem RenameHilbFn.proof : RenameHilbFn.Statement.{u} := by
  intro F _ S K' _ _ κ ι' E σ hσ P m
  have h := Relabel.hilbFn_map_rename E σ hσ (P.comap (rename σ)) (m ∘ E.symm)
  rw [map_comap_renameEquiv σ P] at h
  rw [h]
  congr 1
  funext s
  simp

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForwardLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivPushForwardLocal.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a : MRing (fun k => ι' (j k)) F), IsMultiHomog a c →
    a ∉ contractPrime j P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    ∀ M : Ideal (MRing ι' F) → ℤ,
      (∀ W' (hW' : IsMultiProjPrime W'), contractPrime j W' = W →
        haveI := hW'.isPrime
        M W' = relDeg j W') →
      (∀ W', contractPrime j W' ≠ W → M W' = 0) →
      haveI := hP'.isPrime
      cycEval M (divCycle P' (rename (blockIncl j ι') a)) =
        relDeg j P' * divCycle (contractPrime j P') a W

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

