module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.CoindRetract

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

def adj : restr φ ⊣ coind φ :=
  Adjunction.restrictFullyFaithful
    ((ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (liftHom φ)).whiskerRight (Scheme.{0}ᵒᵖ))
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _) (Iso.refl _) (Iso.refl _)

instance restr_faithful : (restr φ).Faithful :=
  show (sheafCompose (Scheme.etaleTopology.{0}) (ModuleCat.restrictScalars.{1} (liftHom φ))).Faithful from inferInstance

instance coind_preservesMono : (coind φ).PreservesMonomorphisms := by
  haveI : (coind φ).IsRightAdjoint := (adj φ).isRightAdjoint
  infer_instance

theorem coind_retract (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I] :
    ∃ (J : Shv R) (_ : Injective J) (i : I ⟶ (coind φ).obj J) (r : (coind φ).obj J ⟶ I), i ≫ r = 𝟙 I := by
  let J := Injective.under ((restr φ).obj I)
  let i : I ⟶ (coind φ).obj J := (adj φ).unit.app I ≫ (coind φ).map (Injective.ι ((restr φ).obj I))
  haveI : Mono i := mono_comp _ _
  exact ⟨J, inferInstance, i, Injective.factorThru (𝟙 I) i, Injective.comp_factorThru _ _⟩

end GlobalTheory.EtC.CoindRetract
