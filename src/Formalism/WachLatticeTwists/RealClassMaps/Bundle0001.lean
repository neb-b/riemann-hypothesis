module

public import Formalism.WachLatticeTwists.SplitClassesAll.Statement
public import Formalism.WachLatticeTwists.RealClassMaps.Statement
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Bundle0001
public import Formalism.WachLatticeTwists.Statement

@[expose] public section

-- bundled from Formalism.WachLatticeTwists.RealClassMaps.RealClassMapTheorem
section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)

abbrev decs (Ek : Type) {Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω] (Aw : ℕ → ValuationSubring Ω) (w : ℕ) :
    Subgroup (Ω ≃ₐ[Ek] Ω) :=
  (Aw w).decompositionSubgroup Ek

def IsCycG (ℓ : ℕ) {Ek Ω O : Type} [Field Ek] [Field Ω] [Algebra Ek Ω] [CommRing O] (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) : Prop :=
  ∀ (g : Ω ≃ₐ[Ek] Ω) (n : ℕ) (ζ : Ω), ζ ^ (ℓ ^ n) = 1 →
    ∃ a : ℕ, g ζ = ζ ^ a ∧ ((ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(ℓ : O) ^ n}

section Defs
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace A]

def InRhoFixReal (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) [∀ w, TopologicalSpace (D w)] (j : ℕ → ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    {L : Type} [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    {V : Type} [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    (iL : L →ₗ[O] V) (qV : V →ₗ[O] M)
    (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))))
    (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) (D (colIdx l))))
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type} (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    {VT VT' : ℕ → Type}
    [∀ w, AddCommGroup (VT w)] [∀ w, Module O (VT w)] [∀ w, TopologicalSpace (VT w)]
    [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul O (VT w)]
    [∀ w, AddCommGroup (VT' w)] [∀ w, Module O (VT' w)] [∀ w, TopologicalSpace (VT' w)]
    [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul O (VT' w)]
    (Dat : ∀ w, LatData O (D w) (VT w) (VT' w))
    (uD : ∀ w, M ≃ₗ[O] (VT w ⧸ (Dat w).T))
    (huD : ∀ w g m, uD w (resRep (uRep O (M := M) r χ) (D w) g m) = (Dat w).ρA g (uD w m))
    (vD : ∀ w, T₂ ≃ₗ[O] (Dat w).T')
    (Fs Im : ∀ w, Submodule O (H1 (Dat w).ρTl')) : Prop :=
  (∀ (a : A) v x, tens (a • v) x = a • tens v x) ∧
  (∀ m : M, e₁ • m = m → ∃ x, m = tens v₁ x) ∧
  (∀ l (z : coZ1s (resRep (uRep O (M := M) r χ) (D (colIdx l)))) (x : Fin (j (colIdx l)) → KO O),
    (∀ g : D (colIdx l), (z : D (colIdx l) → M) g = ∑ a, tens (κ l a g) (x a)) →
    Submodule.mkQ _ z ∈ F (colIdx l)) ∧
  ((∀ (a : A) v, iL (a • v) = a • iL v) ∧ (∀ (a : A) v, qV (a • v) = a • qV v) ∧
    (∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = qV (x • iL v)) ∧
    Function.Injective iL ∧ Function.Surjective qV ∧ LinearMap.ker qV = LinearMap.range iL ∧
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range iL) ∧
    ∀ l, (∀ a (g : D (colIdx l)), (κz l a : D (colIdx l) → L) g = κ l a g) ∧
      (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff l → z ∈ Ff l) ∧
      (∀ a, Submodule.mkQ _ (κz l a) ∈ Ff l) ∧
      (∀ z ∈ Ff l, ∃ (b : Fin (j (colIdx l)) → O) (c : O), c ≠ 0 ∧
        c • (z - ∑ a, b a • (Submodule.mkQ _ (κz l a) :
          H1z (resRep (uRep O (M := L) r χ) (D (colIdx l))))) = 0) ∧
      (∀ (b : Fin (j (colIdx l)) → O) (c : O), c ≠ 0 →
        c • ∑ a, b a • (Submodule.mkQ _ (κz l a) :
          H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))) = 0 → b = 0)) ∧
  (∀ w ∈ what₂, HcG ≤ (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))).comap
    (resH1 (uRep O (M := M) r χ) (D w))) ∧
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ g b, inc (ρ₁ g b) = ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (inc b * r g⁻¹))) ∧
  IsEquivMap ρ₁ ρ₂ π ∧ (∀ b m, γ (π b) m = lam (inc b • m)) ∧
  (∀ w ∈ what₂, InRowReal r χ E (D w) ρ₁ inc π (Dat w) (vD w) (Fs w) (Im w)) ∧
  Module.length O ↥((HcG ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s

end Defs

section Defs2
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

end Defs2


end Formalism.RepresentationBoundsCohomology.FIN
end
end

-- bundled from Formalism.WachLatticeTwists.RealClassMaps.StatClassMapReal
section
open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

section Defs
variable {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']

def zcRow (D : LatData O Γ VT VT') {T₂ : Type} [AddCommGroup T₂] [Module O T₂] (v : T₂ ≃ₗ[O] D.T') :
    Submodule O (Γ → T₂) :=
  (Z1 D.ρTl').comap (v.toLinearMap.compLeft Γ)

def gRow (D : LatData O Γ VT VT') {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [TopologicalSpace T₁]
    [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O Γ T₁) (π : T₁ →ₗ[O] T₂) (v : T₂ ≃ₗ[O] D.T')
    (hc : Continuous fun t => v (π t)) (he : ∀ g t, v (π (ρ₁ g t)) = D.ρTl' g (v (π t))) :
    H1 ρ₁ →ₗ[O] H1 D.ρTl' :=
  mapH1 ρ₁ D.ρTl' (v.toLinearMap ∘ₗ π) hc he

end Defs

def StatKRowRange : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (G : Type) [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (M : Type) [AddCommGroup M] [Module O M] (ρM : Representation O G M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)), IsOpen (D.T : Set VT) →
    LinearMap.range (kRow D ρM u hu) = lcH1 ρM

def StatResLC : Prop :=
  ∀ (O G M : Type) [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (Dw : Subgroup G),
    lcH1 ρ ≤ (lcH1 (resRep ρ Dw)).comap (resH1 ρ Dw)

def StatPsiCont : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (A : Type) [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
    (Y : Submodule A A), PadicCoeff p O → IsFGTop O A → ∀ ψ : Y →ₗ[O] KO O, Continuous ψ

end Formalism.RepresentationBoundsCohomology.FIN
end
end

