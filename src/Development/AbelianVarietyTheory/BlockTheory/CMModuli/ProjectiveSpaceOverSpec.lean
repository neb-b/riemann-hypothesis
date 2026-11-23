module

public import Mathlib

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

attribute [local instance] MvPolynomial.gradedAlgebra

def IsIndEtale {A S : Type} [CommRing A] [CommRing S] (φ : A →+* S) : Prop :=
  MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale) (CommRingCat.ofHom φ)

def IsStrictHenselisation {A S : Type} [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S]
    (φ : A →+* S) : Prop :=
  HenselianLocalRing S ∧ IsSepClosed (ResidueField S) ∧ IsLocalHom φ ∧ IsIndEtale φ

theorem isStrictHenselisation_real_complex : IsStrictHenselisation (algebraMap ℝ ℂ) := by
  refine ⟨inferInstance, ?_, inferInstance, ?_⟩
  · have e : ℂ ≃+* ResidueField ℂ := RingEquiv.ofBijective (residue ℂ)
      ⟨(residue ℂ).injective, residue_surjective⟩
    haveI : IsAlgClosed (ResidueField ℂ) := IsAlgClosed.of_ringEquiv ℂ _ e
    infer_instance
  · refine MorphismProperty.le_ind _ _ ?_
    change (algebraMap ℝ ℂ).Etale
    rw [RingHom.etale_algebraMap]
    haveI : Algebra.FormallyEtale ℝ ℂ := Algebra.FormallyEtale.of_isSeparable ℝ ℂ
    haveI : Algebra.FinitePresentation ℝ ℂ :=
      (Algebra.FinitePresentation.of_finiteType).1 inferInstance
    exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec
