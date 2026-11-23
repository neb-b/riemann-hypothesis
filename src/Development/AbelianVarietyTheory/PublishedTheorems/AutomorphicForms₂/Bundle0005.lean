module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.Published

namespace AutFinGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def forms (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (c : (E →+* ℂ) → ℂ → ℂ) : Set (Sm E a) :=
  {φ | IsAutForm φ ∧ (∀ k ∈ L, finRep E a k φ = φ) ∧
    (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ AutFin.coeffSpan ρ) ∧
    ∀ τ u, cap τ u φ = c τ u • φ}

end AutFinGL

def AutomorphicFormsFiniteGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) →
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W),
    AutFin.IsContRep ρ →
  ∀ c : (E →+* ℂ) → ℂ → ℂ, FiniteDimensional ℂ (Submodule.span ℂ (AutFinGL.forms L ρ c))

namespace AutFinGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem type_of_map {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W)
    (T : W →ₗ[ℂ] Sm E a) (hT : ∀ k w, T (ρ k w) = cptRep E a k (T w)) (w : W) (g : GA E a) :
    (fun k : Kinf E a => (cptRep E a k (T w)).1 g) ∈ AutFin.coeffSpan ρ :=
  Submodule.subset_span ⟨(LinearMap.proj g).comp ((Sm E a).subtype.comp T), w,
    funext fun k => (congrFun (congrArg Subtype.val (hT k w)) g).symm⟩

end AutFinGL

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FiniteDimensionalCoeffSpan
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.Published.AutFin.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem isAtTau_unique (hθ : IsInfFam θ) {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {x y : GA D V}
    (hx : IsAtTau θ V τ g x) (hy : IsAtTau θ V τ g y) : x = y := by
  refine ((GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V).2.2.1 x hx.1 y hy.1 fun τ' => ?_
  by_cases c : τ' = τ
  · subst c; rw [hx.2.1, hy.2.1]
  · rw [hx.2.2 _ c, hy.2.2 _ c]

end GlobalTheory.Published.AutFin.Model

end
end

