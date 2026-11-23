module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AssocSetApplyOfPointwise
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix

namespace GlobalTheory.Et.Rel

structure RActPre (X : Scheme.{0}) (Γ : Type) [Group Γ] where

  P : (Over X)ᵒᵖ ⥤ Type

  act : Γ → (P ⟶ P)
  act_one : act 1 = 𝟙 P
  act_mul : ∀ g h, act (g * h) = act g ≫ act h

variable {X : Scheme.{0}} (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

section
variable {E} (Q : RActPre X Γ) (ξ : Γ →* GL ι E)

end

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

end GlobalTheory.Et.Rel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableModel
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

section Transfer

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

end Transfer

section Semistable

variable (O : Type) [CommRing O] (ϖ : O) (m r : ℕ)

abbrev ssModel : Type :=
  MvPolynomial (Fin m) O ⧸ Ideal.span (Set.singleton ((∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ))

theorem isStrictlySemistable_model (h1 : 1 ≤ r) (h2 : r ≤ m) :
    IsStrictlySemistable ϖ (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))) := by
  intro x
  refine ⟨⊤, isAffineOpen_top _, trivial, m, r, h1, h2, (Scheme.ΓSpecIso (CommRingCat.of (ssModel O ϖ m r))).inv.hom,
    RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _), ?_⟩
  have h : (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))).appTop =
      (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))).appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE _
  rw [← h, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end Semistable

section MuTest

end MuTest

end GlobalTheory.Et

end
end

