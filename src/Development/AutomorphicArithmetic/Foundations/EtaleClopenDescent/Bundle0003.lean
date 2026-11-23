module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AugmentationMapBijective
section
open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC GlobalTheory.EtC.PrimLoc

theorem UpperTheory.Cb.augmentation_map_bijective :
    LateralTheory.E.AugBijPf.Root := by
  intro q U hq
  rcases subsingleton_or_nontrivial Γ(U, ⊤) with hA | hA
  · exact ⟨U, 𝟙 U, inferInstance, fun u => ⟨u, rfl⟩, ⟨⟨0, hq, Subsingleton.elim _ _⟩⟩⟩
  have hq0 : NeZero q := ⟨by rintro rfl; simp at hq⟩
  let B := AdjoinRoot (cyclotomic q Γ(U, ⊤))
  let φ : CommRingCat.of Γ(U, ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap _ B)
  have he : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr (cyc_etale q hq))
  have hs : Surjective (Spec.map φ) :=
    ⟨adjoinRoot_surj _ (cyclotomic.monic q _)
      (by simp [natDegree_cyclotomic, Nat.totient_pos, Nat.pos_of_ne_zero hq0.out, hq0.out])⟩
  refine ⟨pullback U.toSpecΓ (Spec.map φ), pullback.fst _ _, inferInstance, ?_, ?_⟩
  · intro u
    exact (Surjective.surj (f := pullback.fst U.toSpecΓ (Spec.map φ))) u
  · exact ⟨Prim.map ((pullback.snd U.toSpecΓ (Spec.map φ)).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) (cyc_root q hq)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistFinitary
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem UpperTheory.Cb.tateTwist_finitary :
    ∀ (q : ℕ) (i : ℤ), Finitary (R := ZMod q) (tw q i) := by
  intro q i
  exact GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary (ZMod q) (twF q i) (GlobalTheory.T.tateTwistRingFunctor_preservesFilteredColimits q i)
end

