module

public import Mathlib
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

@[expose] public section

noncomputable section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms
open scoped Classical

namespace UpperTheory.Gal.W2.Seed

structure Loc (X M : Type) [Group X] [Group M] where
  pr : X →* M
  loc : M →* X
  pr_loc : ∀ x, pr (loc x) = x
  comm : ∀ x g, pr g = 1 → loc x * g = g * loc x

variable {X M M' : Type} [Group X] [Group M] [Group M']

def Loc.Fact (L : Loc X M) (K : Subgroup X) (Kw : Subgroup M) : Prop := (∀ x ∈ Kw, L.loc x ∈ K) ∧ ∀ g ∈ K, L.pr g ∈ Kw

def Loc.Apart (L : Loc X M) (L' : Loc X M') : Prop := (∀ x, L.pr (L'.loc x) = 1) ∧ ∀ x, L'.pr (L.loc x) = 1

def tyFn (J : Subgroup M) (ψ : J →* ℂˣ) (g : M) : ℂ := if h : g ∈ J then (((ψ ⟨g, h⟩)⁻¹ : ℂˣ) : ℂ) else 0

structure TyLev (X M : Type) [Group X] [Group M] where
  L : Loc X M
  K : Subgroup X
  K₀ : Subgroup X
  J : Subgroup M
  ψ : J →* ℂˣ
  fact : L.Fact K J
  le : K₀ ≤ K
  ker : ∀ k ∈ K₀, ∀ h, ψ ⟨L.pr k, h⟩ = 1
  idx : K₀.relIndex K ≠ 0
  cms : IsCommensurated K₀

namespace TyLev

variable (T : TyLev X M)

def tf (h : X) (g : X) : ℂ := ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ * tyFn T.J T.ψ (T.L.pr g) * dosetInd ℂ T.K h g

def admitted (f : X → ℂ) : Prop :=
  f ∈ Hecke ℂ T.K₀ ∧ (∀ g, f g ≠ 0 → T.L.pr g ∈ T.J) ∧ ∀ (j : T.J) g, f (g * T.L.loc j) = (((T.ψ j)⁻¹ : ℂˣ) : ℂ) * f g

def IsTy {V : Type} [AddCommGroup V] [Module ℂ V] (Φ : X → V) : Prop :=
  ∀ k (hk : k ∈ T.K) g, Φ (g * k) = ((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩ : ℂˣ) : ℂ) • Φ g

def Cen (z : X) : Prop := (∀ g, z * g = g * z) ∧ T.L.pr z = 1

end TyLev

def hop {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V] (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V)
    (F : H → ℂ) : Module.End ℂ (forms ι K ξ) := if h : ∃ T, IsHecke ι K ξ F T then h.choose else 0

def TfAdm : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (h : X), T.L.pr h = 1 →
  T.admitted (T.tf h) ∧ (∀ k (hk : k ∈ T.K) g, T.tf h (k * g) = (((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩)⁻¹ : ℂˣ) : ℂ) * T.tf h g ∧
    T.tf h (g * k) = (((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩)⁻¹ : ℂˣ) : ℂ) * T.tf h g)

def ConvSupp : Prop := ∀ (X : Type) [Group X] (K : Subgroup X) (f f' : X → ℂ) (g : X), conv K f f' g ≠ 0 →
  ∃ x y, f x ≠ 0 ∧ f' y ≠ 0 ∧ g = x * y

def TfAct : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ (t : M') (z : X), T.Cen z → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), T.IsTy Φ →
  ∀ g, hAct T.K₀ (T.tf (L'.loc t * z)) Φ g = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Φ (g * z * L'.loc x.out)

def TfCen : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (z : X), T.Cen z →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), T.IsTy Φ → ∀ g, hAct T.K₀ (T.tf z) Φ g = Φ (g * z)

def TfIdem : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (h : X), T.L.pr h = 1 →
  (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), (∀ k ∈ T.K₀, ∀ g, Φ (g * k) = Φ g) → T.IsTy (hAct T.K₀ (T.tf h) Φ)) ∧
  conv T.K₀ (T.tf h) (T.tf 1) = T.tf h ∧ conv T.K₀ (T.tf 1) (T.tf h) = T.tf h

def TfMulCen : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (h z : X), T.L.pr h = 1 → T.Cen z →
  conv T.K₀ (T.tf z) (T.tf h) = T.tf (h * z) ∧ conv T.K₀ (T.tf h) (T.tf z) = T.tf (h * z)

def TfMulL : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ (t : M') (r : X), T.L.pr r = 1 → L'.pr r = 1 →
  conv T.K₀ (T.tf (L'.loc t)) (T.tf r) = T.tf (L'.loc t * r)

def TfMulR : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ (t : M') (r : X), T.L.pr r = 1 → L'.pr r = 1 →
  conv T.K₀ (T.tf r) (T.tf (L'.loc t)) = T.tf (L'.loc t * r)

def TfLoc : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ (t t' : M') (g : X),
  conv T.K₀ (T.tf (L'.loc t)) (T.tf (L'.loc t')) g =
    T.tf 1 (g * (L'.loc (L'.pr g))⁻¹) * conv Kw (dosetInd ℂ Kw t) (dosetInd ℂ Kw t') (L'.pr g)

def ConvRing : Prop := ∀ (X : Type) [Group X] (K : Subgroup X), IsCommensurated K → ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K,
  conv K f f' ∈ Hecke ℂ K ∧ ∀ f'' ∈ Hecke ℂ K, conv K (conv K f f') f'' = conv K f (conv K f' f'')

def TfComm : Prop := ∀ (X M M' M'' : Type) [Group X] [Group M] [Group M'] [Group M''] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ z z' : X, T.Cen z → T.Cen z' → ∀ t : M',
  (∀ (L'' : Loc X M'') (t' : M''), T.L.Apart L'' → L'.Apart L'' →
    conv T.K₀ (T.tf (L'.loc t * z)) (T.tf (L''.loc t' * z')) = conv T.K₀ (T.tf (L''.loc t' * z')) (T.tf (L'.loc t * z))) ∧
  ∀ t' : M', conv Kw (dosetInd ℂ Kw t) (dosetInd ℂ Kw t') = conv Kw (dosetInd ℂ Kw t') (dosetInd ℂ Kw t) →
    conv T.K₀ (T.tf (L'.loc t * z)) (T.tf (L'.loc t' * z')) = conv T.K₀ (T.tf (L'.loc t' * z')) (T.tf (L'.loc t * z))

def ExtP : Prop := ∀ (Γ X X₂ V : Type) [Group Γ] [Group X] [Group X₂] [AddCommGroup V] [Module ℂ V] (ι : Γ →* X × X₂)
  (K : Subgroup X) (K₂ : Subgroup X₂) (ξ : Representation ℂ Γ V) (φ : X → V),
  (∀ γ, (ι γ).2 ∈ K₂ → ∀ g, φ ((ι γ).1 * g) = ξ γ (φ g)) → (∀ k ∈ K, ∀ g, φ (g * k) = φ g) →
  ∃ Φ : forms ι (K.prod K₂) ξ, (∀ g, (Φ : X × X₂ → V) (g, 1) = φ g) ∧
    ∀ g₂ : X₂, (∀ g, (Φ : X × X₂ → V) (g, g₂) = 0) ∨ ∃ γ, ∀ g, (Φ : X × X₂ → V) (g, g₂) = ξ γ (φ ((ι γ).1⁻¹ * g))

end UpperTheory.Gal.W2.Seed
