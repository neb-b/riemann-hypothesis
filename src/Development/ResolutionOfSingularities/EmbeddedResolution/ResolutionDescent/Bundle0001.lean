module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebra
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StandardSmoothLift

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceGlobalSections
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceIsoSpecMvPolynomial (k : Type u) [Field k] (v : Type u) :
    affineSpaceIndexedBy k v ≅ Spec (CommRingCat.of (MvPolynomial v k)) :=
  AffineSpace.SpecIso v (CommRingCat.of k)

def mvPolynomialToGlobalSections (k : Type u) [Field k] (v : Type u) :
    MvPolynomial v k →+* Γ(affineSpaceIndexedBy k v, ⊤) :=
  ((affineSpaceIsoSpecMvPolynomial k v).hom.appTop).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv).hom

def globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Γ(affineSpaceIndexedBy k v, ⊤) →+* MvPolynomial v k :=
  ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom).hom.comp
    ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop).hom

private theorem appTop_inv_hom_apply {X Y : Scheme.{u}} (e : X ≅ Y) (s : Γ(Y, ⊤)) :
    e.inv.appTop (e.hom.appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
  simp

private theorem appTop_hom_inv_apply {X Y : Scheme.{u}} (e : X ≅ Y) (s : Γ(X, ⊤)) :
    e.hom.appTop (e.inv.appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.hom_inv_id]
  simp

private theorem mvPolynomialToGlobalSections_apply (k : Type u) [Field k] (v : Type u)
    (p : MvPolynomial v k) :
    mvPolynomialToGlobalSections k v p =
      (affineSpaceIsoSpecMvPolynomial k v).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := rfl

private theorem globalSectionsToMvPolynomial_apply (k : Type u) [Field k] (v : Type u)
    (s : Γ(affineSpaceIndexedBy k v, ⊤)) :
    globalSectionsToMvPolynomial k v s =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl

theorem leftInverse_globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Function.LeftInverse ⇑(globalSectionsToMvPolynomial k v) ⇑(mvPolynomialToGlobalSections k v) := by
  intro p
  rw [mvPolynomialToGlobalSections_apply, globalSectionsToMvPolynomial_apply, appTop_inv_hom_apply]
  simp

theorem rightInverse_globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Function.RightInverse ⇑(globalSectionsToMvPolynomial k v) ⇑(mvPolynomialToGlobalSections k v) := by
  intro s
  rw [globalSectionsToMvPolynomial_apply, mvPolynomialToGlobalSections_apply, Iso.hom_inv_id_apply,
    appTop_hom_inv_apply]

def mvPolynomialEquivGlobalSections (k : Type u) [Field k] (v : Type u) :
    MvPolynomial v k ≃+* Γ(affineSpaceIndexedBy k v, ⊤) where
  toFun := mvPolynomialToGlobalSections k v
  invFun := globalSectionsToMvPolynomial k v
  left_inv := leftInverse_globalSectionsToMvPolynomial k v
  right_inv := rightInverse_globalSectionsToMvPolynomial k v
  map_mul' := map_mul (mvPolynomialToGlobalSections k v)
  map_add' := map_add (mvPolynomialToGlobalSections k v)

theorem mvPolynomialEquivGlobalSections_apply (k : Type u) [Field k] (v : Type u) (p : MvPolynomial v k) :
    mvPolynomialEquivGlobalSections k v p =
      (affineSpaceIsoSpecMvPolynomial k v).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := rfl

theorem mvPolynomialEquivGlobalSections_symm_apply (k : Type u) [Field k] (v : Type u)
    (s : Γ(affineSpaceIndexedBy k v, ⊤)) :
    (mvPolynomialEquivGlobalSections k v).symm s =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl

private theorem affineSpaceIsoSpecMvPolynomial_inv_appTop_coord (k : Type u) [Field k] (v : Type u) (i : v) :
    (affineSpaceIsoSpecMvPolynomial k v).inv.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv (MvPolynomial.X i) := by
  rw [AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord]

@[simp]
theorem mvPolynomialEquivGlobalSections_X (k : Type u) [Field k] (v : Type u) (i : v) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.X i) = AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  rw [mvPolynomialEquivGlobalSections_apply, ← affineSpaceIsoSpecMvPolynomial_inv_appTop_coord k v i, appTop_hom_inv_apply]

@[simp]
theorem mvPolynomialEquivGlobalSections_symm_coord (k : Type u) [Field k] (v : Type u) (i : v) :
    (mvPolynomialEquivGlobalSections k v).symm (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      MvPolynomial.X i := by
  rw [← mvPolynomialEquivGlobalSections_X k v i, RingEquiv.symm_apply_apply]

theorem mvPolynomialEquivGlobalSections_C (k : Type u) [Field k] (v : Type u) (c : k) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.C c) =
      (affineSpaceIndexedByToSpec k v).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  rw [mvPolynomialEquivGlobalSections_apply]
  have h2 : (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial v k)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial v k))).appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have key : (affineSpaceIsoSpecMvPolynomial k v).inv.appTop
      ((affineSpaceIndexedByToSpec k v).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv (MvPolynomial.C c) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    simp
    rw [← CommRingCat.comp_apply, ← h2, CommRingCat.comp_apply]
    simp
  rw [← key, appTop_hom_inv_apply]

theorem mvPolynomialEquivGlobalSections_basicOpen (k : Type u) [Field k] (v : Type u) (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (Spec (CommRingCat.of (MvPolynomial v k))).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := by
  rw [mvPolynomialEquivGlobalSections_apply, Scheme.preimage_basicOpen]
  rfl

theorem mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum (k : Type u) [Field k] (v : Type u)
    (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (PrimeSpectrum.basicOpen p : Opens (PrimeSpectrum (MvPolynomial v k))) := by
  rw [mvPolynomialEquivGlobalSections_basicOpen, basicOpen_eq_of_affine]

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebraStandardSmooth
section
universe u

namespace FunctorialResolution.EmbeddedResolution

variable {R : Type u} [CommRing R] {σ τ : Type u}

noncomputable section

abbrev graphJacobianMinorDet [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ) :
    GraphAlgebra f :=
  graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det

abbrev GraphAlgebraAway [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ) : Type u :=
  Localization.Away (graphJacobianMinorDet f v)

theorem isUnit_algebraMap_graphJacobianMinorDet [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    IsUnit (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v) (graphJacobianMinorDet f v)) :=
  IsLocalization.map_units (M := Submonoid.powers (graphJacobianMinorDet f v)) (GraphAlgebraAway f v)
    ⟨graphJacobianMinorDet f v, Submonoid.mem_powers _⟩

theorem isUnit_algebraMap_jacobian_graphPreSubmersive [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    IsUnit (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)
      (graphPreSubmersivePresentation f v hv).jacobian) := by
  rw [graphPreSubmersivePresentation_jacobian, map_mul, map_pow, map_neg, map_one]
  exact ((isUnit_one.neg).pow _).mul (isUnit_algebraMap_graphJacobianMinorDet f v)

private def graphAlgebraAwayLocalizationPresentation [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Algebra.SubmersivePresentation (GraphAlgebra f) (GraphAlgebraAway f v) Unit Unit :=
  Algebra.SubmersivePresentation.localizationAway (S := GraphAlgebraAway f v) (r := graphJacobianMinorDet f v)

private def graphAlgebraAwayPreSubmersivePresentation [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.PreSubmersivePresentation (MvPolynomial τ R) (GraphAlgebraAway f v) (Unit ⊕ σ) (Unit ⊕ τ) :=
  Algebra.PreSubmersivePresentation.comp (graphAlgebraAwayLocalizationPresentation f v).toPreSubmersivePresentation
    (graphPreSubmersivePresentation f v hv)

private theorem isUnit_jacobian_presentation_graphAlgebraAway [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    IsUnit (graphAlgebraAwayPreSubmersivePresentation f v hv).jacobian := by
  rw [graphAlgebraAwayPreSubmersivePresentation,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.smul_def]
  exact (isUnit_algebraMap_jacobian_graphPreSubmersive f v hv).mul (graphAlgebraAwayLocalizationPresentation f v).jacobian_isUnit

private def graphAlgebraAwaySubmersivePresentation [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.SubmersivePresentation (MvPolynomial τ R) (GraphAlgebraAway f v)
      (Unit ⊕ Fin (Fintype.card σ)) (Unit ⊕ Fin (Fintype.card τ)) :=
  Algebra.SubmersivePresentation.reindex
    { toPreSubmersivePresentation := graphAlgebraAwayPreSubmersivePresentation f v hv
      jacobian_isUnit := isUnit_jacobian_presentation_graphAlgebraAway f v hv }
    (Equiv.sumCongr (Equiv.refl Unit) (Fintype.equivFin σ).symm)
    (Equiv.sumCongr (Equiv.refl Unit) (Fintype.equivFin τ).symm)

theorem isStandardSmooth_graphAlgebraAway [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.IsStandardSmooth (MvPolynomial τ R) (GraphAlgebraAway f v) := by
  constructor
  exact ⟨Unit ⊕ Fin (Fintype.card σ), Unit ⊕ Fin (Fintype.card τ), inferInstance, inferInstance,
    ⟨graphAlgebraAwaySubmersivePresentation f v hv⟩⟩

end

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StandardSmoothLiftRelativeDimension
section
universe u

open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution

namespace StandardSmoothLift

section

variable {S R B : Type u} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite ι] [Finite σ]
  (hsurj : Function.Surjective (algebraMap S R))
  (P : Algebra.SubmersivePresentation R B ι σ)

theorem liftedSubmersivePresentation_dimension :
    (liftedSubmersivePresentation hsurj P).dimension = P.dimension := by
  have hu : Nat.card Unit = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_unit]
  have h1 : Nat.card (Unit ⊕ ι) = Nat.card ι + 1 := by
    rw [Nat.card_sum, hu]
    omega
  have h2 : Nat.card (Unit ⊕ σ) = Nat.card σ + 1 := by
    rw [Nat.card_sum, hu]
    omega
  show Nat.card (Unit ⊕ ι) - Nat.card (Unit ⊕ σ) = Nat.card ι - Nat.card σ
  rw [h1, h2]
  omega

end

end StandardSmoothLift

section

variable (S R B : Type u) [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] [Algebra S B] [IsScalarTower S R B]

theorem exists_lift_of_isStandardSmoothOfRelativeDimension (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r R B]
    (hsurj : Function.Surjective (algebraMap S R)) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra S B') (f : B' →ₐ[S] B),
      Algebra.IsStandardSmoothOfRelativeDimension r S B' ∧ Function.Surjective f ∧
        ∃ e : (R ⊗[S] B') ≃ₐ[R] B, ∀ b' : B', e (1 ⊗ₜ[S] b') = f b' := by
  have hinst : Algebra.IsStandardSmoothOfRelativeDimension r R B := ‹_›
  obtain ⟨ι, σ, hσ, hι, P, hdim⟩ := hinst.out
  have : Finite ι := hι
  have : Finite σ := hσ
  refine ⟨StandardSmoothLift.LiftedAlgebra hsurj P, inferInstance, inferInstance,
    StandardSmoothLift.liftedAlgebraHom hsurj P, ?_,
    StandardSmoothLift.liftedAlgebraHom_surjective hsurj P,
    StandardSmoothLift.baseChangeEquiv hsurj P,
    StandardSmoothLift.baseChangeEquiv_one_tmul hsurj P⟩
  exact ⟨⟨Unit ⊕ ι, Unit ⊕ σ, inferInstance, inferInstance,
    StandardSmoothLift.liftedSubmersivePresentation hsurj P,
    (StandardSmoothLift.liftedSubmersivePresentation_dimension hsurj P).trans hdim⟩⟩

end

end FunctorialResolution.EmbeddedResolution
end

