module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeModelBaseChangeSubalgebra
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeSpreadsOutFiniteTypeSubringImports
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0253

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeSpreadsOut
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isCommMonObj_of_iso {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] {M N : C}
    [MonObj M] [MonObj N] [IsCommMonObj N] (e : M ≅ N) [IsMonHom e.hom] : IsCommMonObj M where
  mul_comm := by
    rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm N]

theorem isAbelianScheme_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G]
    [GrpObj (Over.mk (pullback.snd G.hom f))] (φ : pullback G.hom f ⟶ G.left)
    (h : IsGrpPullback (Over.mk (pullback.snd G.hom f)) G f φ) (hG : IsAbelianScheme G) :
    IsAbelianScheme (Over.mk (pullback.snd G.hom f)) := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  refine ⟨isCommMonObj_of_iso e, ?_, ?_, ?_⟩
  · show Smooth (pullback.snd G.hom f); infer_instance
  · show IsProper (pullback.snd G.hom f); infer_instance
  · show GeometricallyConnected (pullback.snd G.hom f); infer_instance

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.ExistsModelAbelianLb
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_model_abelian_lb : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ L : LB A.left, L.IsLB →
      ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left) (M : LB B.left),
        Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧
          M.IsLB ∧ LBIso L (M.pull φ) := by
  intro R _ A _ hA L hL
  obtain ⟨S0, B, gB, φ, -, hft, hB, hpb⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Approx.abelianScheme_descends_to_fg_subring R A ∅ hA
  have hpb' : IsGrpPullback A B (spMap (algebraMap S0 R)) φ := hpb
  haveI : IsProper B.hom := IsAbelianScheme.proper (A := B)
  have hqc : QuasiCompact B.hom := inferInstance
  have hsep : IsSeparated B.hom := inferInstance
  obtain ⟨R', hR', M, hM, hσ⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Approx.lb_descends_fg S0 R B.left A.left B.hom A.hom φ hqc hsep hpb'.1 L hL
  obtain ⟨gB', φ₁, hB'B, hAB', hφ₁⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra S0 R A B φ hpb' R'
  refine ⟨R'.toSubring, Over.mk (pullback.snd B.hom (spMap (algebraMap S0 R'))), gB', φ₁, M,
    ?_, ?_, hAB', hM, ?_⟩
  · have h1 : Algebra.FiniteType S0 R' := (Subalgebra.fg_iff_finiteType R').mp hR'
    have h2 : Algebra.FiniteType ℤ R' := Algebra.FiniteType.trans hft h1
    exact h2
  · exact GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hB'B
  · exact hσ φ₁ hφ₁ hAB'.1.w

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.ImportsFurther
section

end

