module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfGeometricPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem hom_ext_of_geometric_points (S X Z : Scheme.{0}) [IsReduced S] (q : X ⟶ Z)
    [IsSeparated q] (f g : S ⟶ X) (hq : f ≫ q = g ≫ q)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), x ≫ f = x ≫ g) : f = g := by
  have hs : Surjective (equalizer.ι f g) := ⟨fun s => by
    let k := AlgebraicClosure (S.residueField s)
    let x : Sp k ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) k)) ≫ S.fromSpecResidueField s
    have hx := h k x
    let p : Sp k := IsLocalRing.closedPoint k
    refine ⟨equalizer.lift x hx p, ?_⟩
    rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]
    simp only [x, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _⟩
  exact ext_of_isDominant_of_isSeparated q hq (equalizer.ι f g) (equalizer.condition _ _)

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndEtaleOfCompOfFiniteEtaleCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem isFinite_and_etale_of_comp_of_finite_etale_cover :
    ∀ (X Y Z : Scheme.{0}) (q : X ⟶ Y) (π : Y ⟶ Z), IsFinite q → Etale q → Surjective q → IsFinite (q ≫ π) → Etale (q ≫ π) → IsSeparated π → LocallyOfFinitePresentation π → IsFinite π ∧ Etale π := by
  intro X Y Z q π _ _ _ _ _ _ _
  have he : Etale π := GlobalTheory.etale_of_comp_of_etale_of_surjective q π
  have : UniversallyClosed π := UniversallyClosed.of_comp_surjective q π
  have : IsProper π := {}
  have : LocallyQuasiFinite π := by
    refine ⟨fun {U} hU {V} hV e => ?_⟩
    have h₁ := π.formallyUnramified_appLE hU hV e
    have h₂ := π.finiteType_appLE hU hV e
    algebraize [(π.appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  exact ⟨.of_isProper_of_locallyQuasiFinite _, he⟩

end GlobalTheory.HkFam
end

