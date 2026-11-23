module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.VeryAmpleCompactQuasiSeparatedAffineCharts
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsFiniteGradedModuleLineBundleSections
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem exists_finite_grCube_hom_bijective (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢]
    (h : ∀ i : ι, Module.Finite (MvPolynomial ι R)
      (QuotSMulTop ((MvPolynomial.X i : MvPolynomial ι R) - 1) G)) :
    ∃ K : Submodule (MvPolynomial ι R) G, K.IsHomogeneous 𝒢 ∧
      Module.Finite (MvPolynomial ι R) K ∧ ∀ (t : ℤ) (I : Finset ι), I.Nonempty →
        Function.Bijective (homLocMap (isGradedMap_subtype 𝒢 K) I t) := by
  obtain ⟨r, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating ι R G 𝒢
    fun i => exists_X_pow_smul_mem_span_of_finite_quot ι R G 𝒢 i (h i)
  have hhom : (Submodule.span (MvPolynomial ι R) (Set.range g)).IsHomogeneous 𝒢 :=
    isHomogeneous_span_gr 𝒢 (by
      rintro _ ⟨l, rfl⟩
      exact ⟨d l, hg l⟩)
  refine ⟨_, hhom, Module.Finite.span_of_finite _ (Set.finite_range g), fun t I ⟨i, hi⟩ => ?_⟩
  letI := grSubDecomposition 𝒢 hhom
  exact homLocMap_bijective_of_X _ hi
    (fun m hm => ⟨0, by
      rw [(map_eq_zero_iff _ (Submodule.injective_subtype _)).1 hm, smul_zero]⟩)
    (fun y => by simpa using hsat i y) t

theorem exists_finite_graded_module_secCube : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ (N : Type) (_ : AddCommGroup N) (_ : Module R N) (_ : Module (MvPolynomial (Fin (m + 1)) R) N) (_ : IsScalarTower R (MvPolynomial (Fin (m + 1)) R) N) (𝒩 : ℤ → Submodule R N) (_ : PolyGradedSMul (Fin (m + 1)) 𝒩) (_ : Decomposition 𝒩), Module.Finite (MvPolynomial (Fin (m + 1)) R) N ∧ ∀ t : ℤ, ∃ φ : grCube (Fin (m + 1)) 𝒩 t ⟶ secCube f (tw M H t) (fun i => nonzeroLocus (s i)), ∀ I : Finset (Fin (m + 1)), I.Nonempty → Function.Bijective (φ.app I).hom := by
  intro R _ Y f H m s M hH hM hs
  have hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1))
      (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V :=
    fun V i j t a => SecOn.mulSec_comm (s i) (s j) a
  obtain ⟨K, hK, hfin, hb⟩ := exists_finite_grCube_hom_bijective (Fin (m + 1)) R (GrSum (hx ⊤))
    (GrSum.grading (hx ⊤)) fun i => by
      obtain ⟨haff, r, hr, hsurj⟩ := hs.2 i
      obtain ⟨h1, ε, hε, hk, -⟩ := GlobalTheory.T.exists_dehomogenisation_twisted_chart R Y f H m s M hH hM hs hx i r hr
      letI := cstAlgebra f (nonzeroLocus (s i))
      have hfp := (secOn_finitePresentation_projective Y (tw M H 0) _ (isLB_tw hM hH 0) haff).1
      exact (finite_quotSMulTop_X_sub_one_of_chart (Fin (m + 1)) R (GrSum (hx ⊤))
        (GrSum.grading (hx ⊤)) i Γ(Y, nonzeroLocus (s i)) _ _ (MvPolynomial.aeval r)
        (SecOn (tw M H 0) (nonzeroLocus (s i))) _ _ ε
        ⟨hsurj, (MvPolynomial.aeval_X r i).trans h1, hε, hk⟩).1 inferInstance
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
    grSub (GrSum.grading (hx ⊤)) K, inferInstance, grSubDecomposition _ hK, hfin, fun t => ?_⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_twistedSections_cube_bijective R Y f H m s M hH hM hs hx t
  exact ⟨grCubeMap (isGradedMap_subtype _ K) t ≫ φ, fun I hI => (hφ I).comp (hb t I hI)⟩

end GlobalTheory.AbLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem nonempty_perf_of_smooth_isProjBy :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)),
      Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M) := by
  intro R _ X f hf hp M hM
  obtain ⟨H, hH, m, s, hs⟩ := hp
  obtain ⟨K, φ, hK⟩ := _root_.GlobalTheory.Cohom.exists_finite_projective_complex_cechLB R X f H m s M hH hM hs hf
  exact _root_.GlobalTheory.AbLaw.perf_of_projective_model R X f M (Fin (m + 1)) (fun i => nonzeroLocus (s i)) K φ hM hs.1
    (_root_.GlobalTheory.VeryAmpleCharts.compact_quasiSeparated_isAffineOpen R X f H m s hH hs).2.2 hK

end GlobalTheory.AbLaw
end

