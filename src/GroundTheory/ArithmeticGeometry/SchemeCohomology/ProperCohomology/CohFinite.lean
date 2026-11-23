module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ExistsGeneratingSectionsTwist

@[expose] public section

set_option maxSynthPendingDepth 3

namespace GroundTheory.Arith.SchemeCoh

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe c236Ext c236Scheme

private noncomputable def H.linearMapV436 {X : Scheme.{c236Scheme}}
    [HasExt.{c236Ext} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{c236Scheme})]
    (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
    {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    Sheaf.H.{c236Ext} (modulesAb F) n →ₗ[A] Sheaf.H.{c236Ext} (modulesAb G) n where
  toFun := Sheaf.H.map.{c236Ext} (modulesAbMap φ) n
  map_add' := map_add _
  map_smul' a x := by
    change Sheaf.H.map.{c236Ext} (modulesAbMap φ) n (a • x) =
      a • Sheaf.H.map.{c236Ext} (modulesAbMap φ) n x
    rw [H.smul_def, H.smul_def, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
      ← modulesAbMap_comp, ← modulesAbMap_comp, smulHom_comp]

end

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits Abelian

universe w' u

noncomputable section

variable {X : Scheme.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]

def FiniteH (F : X.Modules) : Prop :=
  ∀ p : ℕ, Module.Finite A (Sheaf.H.{w'} (modulesAb F) p)

variable {A}

theorem FiniteH.of_iso {F G : X.Modules} (e : F ≅ G) (hF : FiniteH.{w'} A F) :
    FiniteH.{w'} A G := fun p =>
  have := hF p
  have eH : Sheaf.H.{w'} (modulesAb F) p ≃ₗ[A] Sheaf.H.{w'} (modulesAb G) p :=
    ((H.moduleFunctor.{w'} A p).mapIso e).toLinearEquiv
  Module.Finite.equiv eH

lemma H.map_zero_injective {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{u})]
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) [Mono f] :
    Function.Injective (Sheaf.H.map.{w'} f 0) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  obtain ⟨y, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  rw [Sheaf.H.map_apply, Sheaf.H.map_apply, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀] at hxy
  rw [(cancel_mono f).1 ((Ext.mk₀_bijective _ _).1 hxy)]

variable [IsNoetherianRing A]

theorem FiniteH.of_shortExact₂ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : FiniteH.{w'} A S.X₁) (h₃ : FiniteH.{w'} A S.X₃) : FiniteH.{w'} A S.X₂ := fun p =>
  have := h₁ p
  have := h₃ p
  finite_of_exact_noetherian (H.linearMapV436 A S.f p) (H.linearMapV436 A S.g p)
    fun y hy => H.exact₂ (shortExact_abSC hS) y hy

theorem FiniteH.of_shortExact₁ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₂ : FiniteH.{w'} A S.X₂) (h₃ : FiniteH.{w'} A S.X₃) : FiniteH.{w'} A S.X₁ := by
  intro p
  have := h₂ p
  have hS' := shortExact_abSC hS
  cases p with
  | zero =>
    have : Mono (abSC S).f := hS'.mono_f
    refine finite_of_exact_noetherian (0 : (Fin 0 → A) →ₗ[A] _) (H.linearMapV436 A S.f 0) ?_
    intro y hy
    refine ⟨0, ?_⟩
    rw [LinearMap.zero_apply]
    exact (H.map_zero_injective.{w'} (abSC S).f (hy.trans (map_zero _).symm)).symm
  | succ p =>
    have := h₃ p
    let δ : Sheaf.H.{w'} (modulesAb S.X₃) p →ₗ[A]
        Sheaf.H.{w'} (modulesAb S.X₁) (p + 1) :=
      { toFun := H.δ hS' p (p + 1) rfl
        map_add' := map_add _
        map_smul' := fun a x => by
          let r := algebraMap A Γ(X, ⊤) a
          let α : abSC S ⟶ abSC S :=
            { τ₁ := modulesAbMap (smulHom S.X₁ r)
              τ₂ := modulesAbMap (smulHom S.X₂ r)
              τ₃ := modulesAbMap (smulHom S.X₃ r)
              comm₁₂ := smulAbRingHom_comp S.f r
              comm₂₃ := smulAbRingHom_comp S.g r }
          exact H.δ_naturality hS' hS' α p (p + 1) rfl x }
    refine finite_of_exact_noetherian δ (H.linearMapV436 A S.f (p + 1)) ?_
    intro x hx
    change ∃ y, H.δ hS' p (p + 1) rfl y = x
    exact H.exact₁ hS' rfl x hx

end

end GroundTheory.Arith.SchemeCoh
