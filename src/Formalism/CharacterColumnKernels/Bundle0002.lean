module

public import Formalism.CharacterColumnKernels.StatementN

@[expose] public section

-- bundled from Formalism.CharacterColumnKernels.CharacterColumnKernelPairSetVariant
section
open Finset Classical

noncomputable section

namespace Formalism.NG

section Cochains
variable {O : Type*} [CommRing O] {D : Type*} [Group D] {M : Type*} [AddCommGroup M] [Module O M]

def coD0 (ρ : Representation O D M) : M →ₗ[O] (D → M) where
  toFun v g := ρ g v - v
  map_add' v w := by ext g; simp only [map_add (f := _), Pi.add_apply]; abel
  map_smul' c v := by ext g; simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]

def coB1 (ρ : Representation O D M) : Submodule O (D → M) := LinearMap.range (coD0 ρ)

def characterColumnKernelSet (ρ : Representation O D M) : Set (D → M) :=
  {c | ∀ g h, c (g * h) = c g + ρ g (c h)}

def characterColumnKernelPairSetVariant (ρ : Representation O D M) : Set (D → D → M) :=
  {c | ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0}

end Cochains

def cup1 {O D M₁ M₂ N : Type*} [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁]
    [AddCommGroup M₂] [Module O M₂] [AddCommGroup N] [Module O N]
    (ρ₂ : Representation O D M₂) (β : M₁ →ₗ[O] M₂ →ₗ[O] N) (a : D → M₁) (b : D → M₂) :
    D → D → N :=
  fun g h => β (a g) (ρ₂ g (b h))

def IsEquivPairing {O D M₁ M₂ N : Type*} [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁]
    [AddCommGroup M₂] [Module O M₂] [AddCommGroup N] [Module O N]
    (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (ρN : Representation O D N)
    (β : M₁ →ₗ[O] M₂ →ₗ[O] N) : Prop :=
  ∀ g m n, β (ρ₁ g m) (ρ₂ g n) = ρN g (β m n)

def IsEquivMap {O D M M' : Type*} [CommRing O] [Group D] [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (ρ : Representation O D M) (ρ' : Representation O D M')
    (f : M →ₗ[O] M') : Prop :=
  ∀ g m, f (ρ g m) = ρ' g (f m)

def colD {A T' K V G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [SMulCommClass A K V]
    (r : G →* A) (χ : G →* T'ˣ) (D : Subgroup G) : V →ₗ[K] (D → V) where
  toFun v g := ((((χ g)⁻¹ : T'ˣ) : T') • r g) • v - v
  map_add' v w := by ext g; simp only [smul_add, Pi.add_apply]; abel
  map_smul' c v := by ext g; simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, smul_comm]

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.StatOntoLattice
section
open Polynomial

noncomputable section

namespace Formalism.NG

universe u

def StatBurnside : Prop :=
  ∀ (k A V : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [FiniteDimensional k V], IsSimpleModule A V →
    (∀ φ : V →ₗ[A] V, ∃ c : k, ∀ v, φ v = c • v) →
    Function.Surjective (fun a : A => DistribSMul.toLinearMap k V a)

def StatSplitAlg : Prop :=
  ∀ (T : Type u) [CommRing T] (P : T[X]), P.Monic →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (rr : Fin P.natDegree → T'),
      Module.Free T T' ∧ Module.Finite T T' ∧ Module.finrank T T' = P.natDegree.factorial ∧
      P.map (algebraMap T T') = ∏ i, (X - C (rr i)) ∧
      Algebra.adjoin T (Set.range rr) = ⊤ ∧
      ∀ (B : Type u) [CommRing B] [Algebra T B] (a : Fin P.natDegree → B),
        P.map (algebraMap T B) = ∏ i, (X - C (a i)) →
        ∃! φ : T' →ₐ[T] B, ∀ i, φ (rr i) = a i

def StatSplitFibre : Prop :=
  ∀ (T T' K : Type*) [CommRing T] [CommRing T'] [Algebra T T'] [Field K] (P : T[X]), P.Monic →
    ∀ (rr : Fin P.natDegree → T'), P.map (algebraMap T T') = ∏ i, (X - C (rr i)) →
      Algebra.adjoin T (Set.range rr) = ⊤ →
    ∀ (b : Module.Basis (Fin P.natDegree.factorial) T T') (x : T →+* K) (a : Fin P.natDegree → K),
      Function.Injective a → P.map x = ∏ i, (X - C (a i)) →
      ∀ c : Fin P.natDegree.factorial → K,
        (∀ φ : T' →+* K, φ.comp (algebraMap T T') = x → ∑ k, c k * φ (b k) = 0) → c = 0

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.StatementBC
section
open Finset

noncomputable section

namespace Formalism.NG

def StatVccBaseChange : Prop :=
  ∀ (O O' : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'] (e : ℕ),
    (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y) →
    ∀ (X : Type*) (T : Subalgebra O (X → O)) (T' : Subalgebra O' (X → O')),
      (T' : Set (X → O')) = Submodule.span O' ((fun f : X → O => algebraMap O O' ∘ f) '' (T : Set (X → O))) →
    ∀ (Z : Set X) (x : X), vcc T' Z x = e * vcc T Z x

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.StatementNG
section
open Finset

noncomputable section

namespace Formalism.NG

def LocalSubalgebraEtaBound : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type*) [Finite X]
    (T : Subalgebra O (X → O)) [IsLocalRing T], (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    ∀ (V : Type*) [AddCommGroup V] [Module (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
      [Module O V] [IsScalarTower O (FractionRing O) V]
      (act : T →+* Module.End (FractionRing O) V), (⨆ x, Vx T act x) = ⊤ →
    ∀ L : Submodule O V, L.FG → Submodule.span (FractionRing O) (L : Set V) = ⊤ →
      (∀ f : T, ∀ v ∈ L, act f v ∈ L) →
    ∀ (Z Zg : Finset X), Zg ⊆ Z → ∀ (a : Module.End (FractionRing O) V) (A : ℤ),
      (∀ v ∈ L, a v ∈ L) → (∀ f : T, a * act f = act f * a) →
      (∀ x ∈ Zg, ∀ v ∈ Vx T act x, a v = (A : FractionRing O) • v) →
      (∀ x ∈ Z, x ∉ Zg → ∀ v ∈ Vx T act x, a v = 0) →
    ∀ B : X → ℕ∞, (∀ x ∈ Zg, vcc T (Z : Set X) x ≤ B x) →
      Module.length O (CongMod T act L (Zg : Set X)) ≤
        ∑ x ∈ Zg, (Module.finrank (FractionRing O) (Vx T act x) : ℕ∞) *
          (B x + IsDiscreteValuationRing.addVal O (A : O))

end Formalism.NG
end
end

