module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsSmoothBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateQuotient
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0004
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinateCodimensionCriterion
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def castAddImage (c d : ℕ) : Finset (Fin (c + d)) :=
  (Finset.univ : Finset (Fin c)).image (Fin.castAdd d)

theorem castAddImage_eq_image_castAdd (c d : ℕ) :
    castAddImage c d = (Finset.univ : Finset (Fin c)).image (Fin.castAdd d) := rfl

theorem card_castAddImage (c d : ℕ) : (castAddImage c d).card = c := by
  have hinj : Function.Injective (Fin.castAdd d : Fin c → Fin (c + d)) := by
    intro a b hab
    have hv : ((Fin.castAdd d a : Fin (c + d)) : ℕ) = ((Fin.castAdd d b : Fin (c + d)) : ℕ) :=
      congrArg (fun z : Fin (c + d) => (z : ℕ)) hab
    exact Fin.ext hv
  rw [castAddImage_eq_image_castAdd, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin]

private theorem mem_image_ι_of_mem {X' : Scheme.{u}} (U : X'.Opens)
    (V : U.toScheme.Opens) (y : X') (hy : y ∈ U) (h : (⟨y, hy⟩ : ↥U) ∈ V) :
    y ∈ U.ι ''ᵁ V :=
  ⟨⟨y, hy⟩, h, rfl⟩

private theorem range_ι_comp_ι_eq_image {X' : Scheme.{u}} (U : X'.Opens) (V : U.toScheme.Opens) :
    Set.range ((V.ι ≫ U.ι).base) = (↑(U.ι ''ᵁ V) : Set ↥X') := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, w.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

private def etaleChartTop (k : Type u) [Field k] (c : ℕ) :
    EtaleChart (affineSpaceFinToSpec k c) (⊤ : (affineSpaceFin k c).Opens) c where
  map := (⊤ : (affineSpaceFin k c).Opens).ι
  comp_struct := rfl
  isEtale := inferInstance

private theorem etaleChartTop_map (k : Type u) [Field k] (c : ℕ) :
    (etaleChartTop k c).map = (⊤ : (affineSpaceFin k c).Opens).ι := rfl

private theorem restrictIdeal_top_coordSubspaceIdeal_univ (k : Type u) [Field k] (c : ℕ) :
    restrictIdeal (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c)))
      (⊤ : (affineSpaceFin k c).Opens) = (etaleChartTop k c).coordIdeal Finset.univ := by
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, etaleChartTop_map]

theorem exists_etaleChart_image_of_restrictIdeal_eq {X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (U : X'.Opens) (V : U.toScheme.Opens) (n : ℕ)
    (ch : EtaleChart (U.ι ≫ p) V n) (D : X'.IdealSheafData) (S : Finset (Fin n))
    (h : restrictIdeal (restrictIdeal D U) V = ch.coordIdeal S) :
    ∃ ch' : EtaleChart p (U.ι ''ᵁ V) n, restrictIdeal D (U.ι ''ᵁ V) = ch'.coordIdeal S := by
  have hr : Set.range ((U.ι ''ᵁ V).ι).base = Set.range ((V.ι ≫ U.ι).base) := by
    rw [Scheme.Opens.range_ι, ← range_ι_comp_ι_eq_image]
  let φ : (U.ι ''ᵁ V).toScheme ≅ V.toScheme :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq ((U.ι ''ᵁ V).ι) (V.ι ≫ U.ι) hr
  have hfac : φ.hom ≫ (V.ι ≫ U.ι) = (U.ι ''ᵁ V).ι :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr
  have hcs : (φ.hom ≫ ch.map) ≫ affineSpaceFinToSpec k n = (U.ι ''ᵁ V).ι ≫ p := by
    calc (φ.hom ≫ ch.map) ≫ affineSpaceFinToSpec k n
        = φ.hom ≫ (ch.map ≫ affineSpaceFinToSpec k n) := Category.assoc _ _ _
      _ = φ.hom ≫ (V.ι ≫ (U.ι ≫ p)) := by rw [ch.comp_struct]
      _ = (φ.hom ≫ (V.ι ≫ U.ι)) ≫ p := by simp only [Category.assoc]
      _ = (U.ι ''ᵁ V).ι ≫ p := by rw [hfac]
  have : AlgebraicGeometry.Etale ch.map := ch.isEtale
  have hkey : (D.comap U.ι).comap V.ι = (coordSubspaceIdeal k n S).comap ch.map := by
    rw [← restrictIdeal_eq_comap_ι, ← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  refine ⟨⟨φ.hom ≫ ch.map, hcs, inferInstance⟩, ?_⟩
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  calc D.comap (U.ι ''ᵁ V).ι
      = ((D.comap U.ι).comap V.ι).comap φ.hom := by
        rw [← hfac, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    _ = ((coordSubspaceIdeal k n S).comap ch.map).comap φ.hom := by rw [hkey]
    _ = (coordSubspaceIdeal k n S).comap (φ.hom ≫ ch.map) := by
        rw [Scheme.IdealSheafData.comap_comp]

theorem exists_etaleChart_of_restrictIdeal_ker_eq_comap
    {X X' : Scheme.{u}} {k : Type u} [Field k] (p : X' ⟶ Spec (CommRingCat.of k))
    (τ : X ⟶ X') (c : ℕ) (U : X'.Opens) (q : U.toScheme ⟶ affineSpaceFin k c)
    [AlgebraicGeometry.Smooth q] (hq : q ≫ affineSpaceFinToSpec k c = U.ι ≫ p)
    (hker : restrictIdeal τ.ker U =
      (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).comap q)
    (x : X) (hx : τ.base x ∈ U) :
    ∃ (V : U.toScheme.Opens) (_ : IsAffineOpen V) (_ : (⟨τ.base x, hx⟩ : ↥U) ∈ V) (d : ℕ)
      (ch : EtaleChart (U.ι ≫ p) V (c + d)),
      restrictIdeal (restrictIdeal τ.ker U) V = ch.coordIdeal (castAddImage c d) := by
  have : AlgebraicGeometry.Smooth (affineSpaceFinToSpec k c) := affineSpaceIsSmooth ..
  obtain ⟨V, hVU, d, ch, hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_comap_coord_eq (affineSpaceFinToSpec k c) q (etaleChartTop k c)
      (⟨τ.base x, hx⟩ : ↥U) (by trivial)
  have hidtop : (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).ideal
      ⟨⊤, isAffineOpen_top (affineSpaceFin k c)⟩
      = Ideal.span ((etaleChartTop k c).coord ''
          ((Finset.univ : Finset (Fin c)) : Set (Fin c))) :=
    EtaleChart.ideal_eq_span_coord (etaleChartTop k c) (isAffineOpen_top (affineSpaceFin k c))
      (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))) Finset.univ
      (restrictIdeal_top_coordSubspaceIdeal_univ k c)
  have hspanV : (restrictIdeal τ.ker U).ideal ⟨V, hVaff⟩
      = Ideal.span (ch.coord ''
          ((castAddImage c d : Finset (Fin (c + d))) : Set (Fin (c + d)))) := by
    rw [hker,
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE
        (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))) q
        ⟨⊤, isAffineOpen_top (affineSpaceFin k c)⟩ ⟨V, hVaff⟩ hVU,
      hidtop, Ideal.map_span]
    congr 1
    rw [Set.image_image, castAddImage_eq_image_castAdd, Finset.coe_image, Set.image_image]
    exact Set.image_congr (fun j _ => (hcoord j).symm)
  have hcs : ch.map ≫ affineSpaceFinToSpec k (c + d) = V.ι ≫ (U.ι ≫ p) := by
    rw [ch.comp_struct, hq]
  refine ⟨V, hVaff, hyV, d, ⟨ch.map, hcs, ch.isEtale⟩, ?_⟩
  exact restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff _ _ (castAddImage c d) hspanV

theorem hasEtaleCoordCodim_of_locally_smooth_over_affineSpace {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (τ : X ⟶ X') (c : ℕ)
    (h : ∀ x : X, ∃ (U : X'.Opens) (_ : τ.base x ∈ U) (q : U.toScheme ⟶ affineSpaceFin k c),
      AlgebraicGeometry.Smooth q ∧ q ≫ affineSpaceFinToSpec k c = U.ι ≫ p ∧
        restrictIdeal τ.ker U =
          (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).comap q) :
    HasEtaleCoordCodim p τ c := by
  intro x
  obtain ⟨U, hxU, q, hqsm, hqc, hker⟩ := h x
  have := hqsm
  obtain ⟨V, hVaff, hxV, d, ch, hch⟩ :=
    exists_etaleChart_of_restrictIdeal_ker_eq_comap p τ c U q hqc hker x hxU
  obtain ⟨ch', hch'⟩ :=
    exists_etaleChart_image_of_restrictIdeal_eq p U V (c + d) ch τ.ker (castAddImage c d) hch
  exact ⟨U.ι ''ᵁ V, mem_image_ι_of_mem U V (τ.base x) hxU hxV, c + d, ch',
    castAddImage c d, card_castAddImage c d, hch'⟩

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.GermRegularParameters
section
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem germ_mem_maximalIdeal_iff {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U x hx s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let instSt : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  have instLoc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

theorem exists_sections_span_eq_maximalIdeal_with_coords (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (x : X) (hx : x ∈ U) (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, X.presheaf.germ U x hx (c.coord j) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∃ (d : ℕ) (f : Fin d → Γ(X, U)),
      (∀ i, X.presheaf.germ U x hx (f i) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      Ideal.span (Set.range fun i => X.presheaf.germ U x hx (f i)) =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      (d : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) := by
  let instAlg : Algebra (CoordPolynomialRing k m) Γ(X, U) := c.algebra
  have instEt : Algebra.Etale (CoordPolynomialRing k m) Γ(X, U) := c.algebra_etale hU
  let instSt : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  have instLoc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ t : Γ(X, U),
      algebraMap Γ(X, U) (X.presheaf.stalk x) t = X.presheaf.germ U x hx t := fun _ => rfl
  have hcoord : ∀ j : Fin m, etaleChartCoord k m Γ(X, U) j = c.coord j := by
    intro j
    show c.coordRingHom (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) = c.coord j
    exact c.coordRingHom_X j
  have hq : ∀ j ∈ J₀, etaleChartCoord k m Γ(X, U) j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro j hj
    rw [hcoord j]
    exact (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mp (hJ₀ j hj)
  obtain ⟨d, f, hf1, hf2, hf3, hf4⟩ :=
    exists_regularSystemOfParameters_containing_etaleChartCoords k m Γ(X, U)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x) J₀ hq
  refine ⟨d, f, ?_, ?_, ?_, hf4⟩
  · intro i
    exact (germ_mem_maximalIdeal_iff hU x hx (f i)).mpr (hf1 i)
  · intro j hj
    obtain ⟨i, hi⟩ := hf2 j hj
    exact ⟨i, by rw [hi, hcoord j]⟩
  · simpa only [halg] using hf3

theorem exists_isRegularParameterSystem_with_coords_of_mem_prime (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (x : X) (hx : x ∈ U) (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, U)),
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      IsRegularParameterSystem (X.presheaf.stalk x) n
        (fun i => X.presheaf.germ U x hx (f i)) := by
  obtain ⟨d, f, -, h2, h3, h4⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J₀
      (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mpr (hJ₀ j hj))
  exact ⟨d, f, h2, h3, h4⟩

end FunctorialResolution.EmbeddedResolution
end
end

