module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceProduct
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ExtendCoordinatesToAffineSpace
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def specHomOfGlobalSections (A : Scheme.{u}) [AlgebraicGeometry.IsAffine A] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') : Spec B' ⟶ A :=
  Spec.map σ ≫ A.isoSpec.inv

@[simp]
theorem specHomOfGlobalSections_appTop (A : Scheme.{u}) [AlgebraicGeometry.IsAffine A]
    {B' : CommRingCat.{u}} (σ : Γ(A, ⊤) ⟶ B') (s : Γ(A, ⊤)) :
    (specHomOfGlobalSections A σ).appTop s = (Scheme.ΓSpecIso B').inv (σ s) := by
  have hcomp : specHomOfGlobalSections A σ ≫ A.isoSpec.hom = Spec.map σ := by
    simp [specHomOfGlobalSections]
  have h : (Scheme.ΓSpecIso Γ(A, ⊤)).hom ≫ (specHomOfGlobalSections A σ).appTop
      = (Spec.map σ).appTop := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, hcomp]
  have h3 : (specHomOfGlobalSections A σ).appTop = σ ≫ (Scheme.ΓSpecIso B').inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(A, ⊤)).hom, Scheme.ΓSpecIso_inv_naturality,
      Iso.hom_inv_id_assoc]
    exact h
  rw [h3, CommRingCat.comp_apply]

def specToAffineSpaceExtendCoords (k : Type u) [Field k] (A : Scheme.{u}) [AlgebraicGeometry.IsAffine A]
    (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') :
    Spec B' ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)) :=
  AffineSpace.homOfVector (specHomOfGlobalSections A σ ≫ pA)
    (fun i =>
      Sum.elim
        (fun a : Fin M =>
          (specHomOfGlobalSections A σ ≫ e).appTop
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a)))
        (fun j : Fin n => (Scheme.ΓSpecIso B').inv (b j))
        i.down)

@[simp]
theorem specToAffineSpaceExtendCoords_comp_toSpec (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') :
    specToAffineSpaceExtendCoords k A pA M e σ n b ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n)) =
      specHomOfGlobalSections A σ ≫ pA := by
  simp [specToAffineSpaceExtendCoords]

@[simp]
theorem specToAffineSpaceExtendCoords_appTop_coord_inl (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') (a : Fin M) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n))) =
      (specHomOfGlobalSections A σ ≫ e).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a)) := by
  simp [specToAffineSpaceExtendCoords]

@[simp]
theorem specToAffineSpaceExtendCoords_appTop_coord_inr (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B') (j : Fin n) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n))) =
      (Scheme.ΓSpecIso B').inv (b j) := by
  simp [specToAffineSpaceExtendCoords]

theorem specToAffineSpaceExtendCoords_comp_projLeft (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA) :
    specToAffineSpaceExtendCoords k A pA M e σ n b ≫ projLeft k M n = specHomOfGlobalSections A σ ≫ e := by
  refine AffineSpace.hom_ext ?_ ?_
  · simp [he]
  · rintro ⟨a⟩
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord,
      specToAffineSpaceExtendCoords_appTop_coord_inl]

theorem specToAffineSpaceExtendCoords_appTop_surjective (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA)
    (hgen : ∀ x : B', ∃ p : MvPolynomial (Fin n) Γ(A, ⊤),
      MvPolynomial.eval₂ σ.hom b p = x) :
    Function.Surjective ⇑((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop) := by
  have hsurj : Function.Surjective ⇑(e.appTop) :=
    (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine e).2
  have hproj : specToAffineSpaceExtendCoords k A pA M e σ n b ≫ projLeft k M n
      = specHomOfGlobalSections A σ ≫ e := specToAffineSpaceExtendCoords_comp_projLeft k A pA M e σ n b he
  have hsec : ∀ s : Γ(A, ⊤), ∃ P, (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop P
      = (Scheme.ΓSpecIso B').inv (σ s) := by
    intro s
    obtain ⟨P, hPs⟩ := hsurj s
    refine ⟨(projLeft k M n).appTop P, ?_⟩
    have h2 := congrArg
      (fun g : Spec B' ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)) => g.appTop P) hproj
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h2
    rw [h2, hPs, specHomOfGlobalSections_appTop]
  have key : ∀ p : MvPolynomial (Fin n) Γ(A, ⊤), ∃ P,
      (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop P
        = (Scheme.ΓSpecIso B').inv (MvPolynomial.eval₂ σ.hom b p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C s =>
        obtain ⟨P, hP⟩ := hsec s
        refine ⟨P, ?_⟩
        rw [MvPolynomial.eval₂_C]
        exact hP
    | add p q hp hq =>
        obtain ⟨P, hP⟩ := hp
        obtain ⟨Q, hQ⟩ := hq
        refine ⟨P + Q, ?_⟩
        rw [map_add (f := _), MvPolynomial.eval₂_add, map_add (f := _), hP, hQ]
    | mul_X p j hp =>
        obtain ⟨P, hP⟩ := hp
        refine ⟨P * AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)), ?_⟩
        rw [map_mul, hP, specToAffineSpaceExtendCoords_appTop_coord_inr, MvPolynomial.eval₂_mul,
          MvPolynomial.eval₂_X, map_mul]
  intro y
  obtain ⟨p, hp⟩ := hgen ((Scheme.ΓSpecIso B').hom y)
  obtain ⟨P, hP⟩ := key p
  refine ⟨P, ?_⟩
  rw [hP, hp]
  simp

theorem isClosedImmersion_specToAffineSpaceExtendCoords (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA)
    (hgen : ∀ x : B', ∃ p : MvPolynomial (Fin n) Γ(A, ⊤),
      MvPolynomial.eval₂ σ.hom b p = x) :
    AlgebraicGeometry.IsClosedImmersion (specToAffineSpaceExtendCoords k A pA M e σ n b) :=
  AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine _
    (specToAffineSpaceExtendCoords_appTop_surjective k A pA M e σ n b he hgen)

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChart
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def graphMorphismToAffineSpace (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
    D.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin q)) :=
  AffineSpace.homOfVector
    (D.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n)))
    (fun i =>
      Sum.elim
        (fun a : Fin M =>
          (ConcreteCategory.hom (Scheme.Hom.appTop D.ι))
            (AffineSpace.coord (Spec (CommRingCat.of k))
              (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n))))
        (fun j : Fin q => (ConcreteCategory.hom (Scheme.Hom.appTop D.ι)) (F j))
        i.down)

theorem graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
    graphMorphismToAffineSpace k M n q F D ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin q)) =
      D.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n)) := by
  simp [graphMorphismToAffineSpace]

theorem graphMorphismToAffineSpace_appTop_coord_inl (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) (a : Fin M) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F D)))
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin q))) =
      (ConcreteCategory.hom (Scheme.Hom.appTop D.ι))
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n))) := by
  simp [graphMorphismToAffineSpace]

theorem graphMorphismToAffineSpace_appTop_coord_inr (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) (j : Fin q) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F D)))
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inr j) : ULift.{u, 0} (Fin M ⊕ Fin q))) =
      (ConcreteCategory.hom (Scheme.Hom.appTop D.ι)) (F j) := by
  simp [graphMorphismToAffineSpace]

def SmoothPullbackHasGraphChart : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X Y A : Scheme.{u})
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pA : A ⟶ Spec (CommRingCat.of k)) [IsAffine A] [Smooth pA]
    [LocallyOfFiniteType pA] [QuasiCompact pA]
    (i : X ⟶ A) [IsClosedImmersion i], i ≫ pA = pX →
    ∀ (M : ℕ) (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ],
      ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) = pA →
    ∀ (r : ℕ) (h : Y ⟶ X) [SmoothOfRelativeDimension r h], h ≫ pX = pY →
    ∀ y : Y,
      ∃ (V : Y.Opens) (_ : y ∈ V) (_ : IsAffineOpen V)
        (A' : Scheme.{u}) (pA' : A' ⟶ Spec (CommRingCat.of k)),
        IsAffine A' ∧ Smooth pA' ∧ LocallyOfFiniteType pA' ∧ QuasiCompact pA' ∧
        ∃ g : A' ⟶ A, Smooth g ∧ g ≫ pA = pA' ∧
          ∃ j : V.toScheme ⟶ A', IsClosedImmersion j ∧
            IsPullback j (V.ι ≫ h) g i ∧
            ∃ (n q : ℕ), n = q + r ∧
              ∃ σ : A' ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n)),
                IsClosedImmersion σ ∧
                σ ≫ projLeft k M n = g ≫ ρ ∧
                ∃ (F : Fin q →
                    ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj
                      (Opposite.op ⊤)))
                  (Δ : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj
                      (Opposite.op ⊤))),
                  RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop σ)) =
                      Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k M n)))
                        (RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop ρ))) ⊔
                      Ideal.span (Set.range F) ∧
                  σ ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) = ⊤ ∧
                  Smooth (graphMorphismToAffineSpace k M n q F
                    ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ))

end FunctorialResolution.EmbeddedResolution

end
end

