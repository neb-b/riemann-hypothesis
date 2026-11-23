module

public import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Bundle0001

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

def BKIn {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {X : Type} [AddCommGroup X] [Module O X] (Hc : Submodule O X)
    {HV Cs HV' : Type}
    [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
    [IsScalarTower O (FractionRing O) HV]
    [AddCommGroup Cs] [Module O Cs]
    [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
    [IsScalarTower O (FractionRing O) HV']
    (q : HV →ₗ[O] Hc) (j' : Cs →ₗ[O] HV') (pr : Hc →ₗ[O] Cs →ₗ[O] KO O)
    (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
    (HfV : Submodule (FractionRing O) HV) (HfV' : Submodule (FractionRing O) HV')
    (F : Submodule O X) (Fs : Submodule O Cs) : Prop :=
  Module.Finite O Cs ∧
  (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) ∧
  (∀ f : HV' →ₗ[FractionRing O] FractionRing O, ∃ a, ∀ b, pair a b = f b) ∧
  (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) ∧
  (∀ x : Hc, (∀ t, pr x t = 0) → x = 0) ∧
  F = ((HfV.restrictScalars O).map q).map Hc.subtype ∧ Fs = (HfV'.restrictScalars O).comap j'

section Defs
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type*} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def InRowRhoNoBK (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type*} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂)
    (γ : T₂ →ₗ[O] M →ₗ[O] KO O)
    (Hc : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw)))
    {Cs : Type*} [AddCommGroup Cs] [Module O Cs] (cls : (Dw → T₂) → Cs)
    (pr : Hc →ₗ[O] Cs →ₗ[O] KO O) (Fs Im : Submodule O Cs) : Prop :=
  ∃ (C₁ : (Dw → T₁) → Prop) (CN2 : (Dw → Dw → Ymod r χ E) → Prop)
    (CN : (Dw → Ymod r χ E) → Prop) (CA : (Dw → A) → Prop) (CP : (Dw → KO O) → Prop),
    (∀ a, C₁ a → CN2 (fun g h => inc (a g) • (uElt r χ (g : G) • yY r χ E (h : G)))) ∧
    (∀ a, C₁ a → CA (fun g => -(inc (a g) * (uElt r χ (g : G) * E)))) ∧
    (∀ (ψ : Ymod r χ E →ₗ[O] KO O) f, CN f → CP (fun g => ψ (f g))) ∧
    (∀ z ∈ characterColumnKernelPairSetVariant (twRep (ε.comp Dw.subtype) (Ymod r χ E)), CN2 z →
      (∃ f, CA f ∧ ∀ g h, ((z g h : Ymod r χ E) : A) =
        ((ε (g : G) : Oˣ) : O) • f h - f (g * h) + f g) →
      ∃ c, CN c ∧ ∀ g h, z g h = ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g) ∧
    (∀ (a : Dw → T₁) (b : coZ1s (resRep (uRep O (M := M) r χ) Dw))
      (hb : Submodule.mkQ _ b ∈ Hc), a ∈ characterColumnKernelSet (resRep ρ₁ Dw) → C₁ a →
      (∃ c, CP c ∧ ∀ g h : Dw, γ (π (a g)) (uElt r χ (g : G) • (b : Dw → M) h) =
        ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g) →
      pr ⟨Submodule.mkQ _ b, hb⟩ (cls (fun g => π (a g))) = 0) ∧
    (∀ x ∈ Im, ∃ a ∈ characterColumnKernelSet (resRep ρ₁ Dw), C₁ a ∧ x = cls (fun g => π (a g))) ∧
    Im ≤ Fs

end Defs

end Formalism.RepresentationBoundsCohomology.JT
