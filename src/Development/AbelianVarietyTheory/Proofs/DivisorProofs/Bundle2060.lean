module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineCoverInfClosed
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_finite_affine_cover_infClosed : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    IsSeparated s → QuasiCompact s → ∃ (J : Type) (_ : Finite J) (_ : SemilatticeInf J)
      (U : J → X.affineOpens), Monotone U ∧ (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) ∧
        ⨆ i, (U i).1 = ⊤ := by
  intro R _ X s hsep hqc
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hdiag : IsAffineHom (pullback.diagonal s) := inferInstance
  have hinf : ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
    fun U V hU hV => isAffineHom_diagonal_iff.mp hdiag ⊤ (isAffineOpen_top _) U (by simp) V
      (by simp) hU hV
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
    (by simpa using isCompact_univ)
  set A : Set X.Opens := infClosure ((fun i : X.affineOpens => i.1) '' S) with hAdef
  have hA : ∀ U ∈ A, IsAffineOpen U :=
    infClosure_min (t := {U | IsAffineOpen U}) (by rintro _ ⟨i, -, rfl⟩; exact i.2)
      (fun a ha b hb => hinf a b ha hb)
  letI inst : SemilatticeInf A :=
    Subtype.semilatticeInf (fun _ _ ha hb => infClosed_infClosure ha hb)
  haveI hfin : Finite A := ((hS.image _).infClosure).to_subtype
  refine ⟨A, hfin, inst, fun j => ⟨j.1, hA j.1 j.2⟩, fun a b h => h, fun i j => rfl, ?_⟩
  apply top_le_iff.mp
  rw [e]
  exact iSup₂_le fun i hi => le_iSup_of_le (⟨i.1, subset_infClosure ⟨i, hi, rfl⟩⟩ : A) le_rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompatibleEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

open scoped TensorProduct

namespace GlobalTheory

theorem exists_finite_ext_compat_of_finite :
    ∀ (k K k₁ : Type) [Field k] [Field K] [Field k₁] [Algebra k K] [Algebra k k₁] [FiniteDimensional k k₁], ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (e : k₁ →+* K'), e.comp (algebraMap k k₁) = (algebraMap K K').comp (algebraMap k K) := by
  intro k K k₁ _ _ _ _ _ _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[k] k₁)
  letI : Field ((K ⊗[k] k₁) ⧸ m) := Ideal.Quotient.field m
  have hfin : FiniteDimensional K ((K ⊗[k] k₁) ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K m)
  refine ⟨(K ⊗[k] k₁) ⧸ m, inferInstance, inferInstance, hfin,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : k₁ →ₐ[k] K ⊗[k] k₁).toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.algebraMap_eq]
  rw [IsScalarTower.algebraMap_apply K (K ⊗[k] k₁) ((K ⊗[k] k₁) ⧸ m),
    Algebra.TensorProduct.algebraMap_apply]
  congr 1
  rw [← Algebra.TensorProduct.algebraMap_apply', ← Algebra.TensorProduct.algebraMap_apply]
  exact IsScalarTower.algebraMap_apply k K (K ⊗[k] k₁) a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTranslatesCoverGeometricFibre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreCover

theorem cover_geometric_fibre : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (K : Type) [Field K] [IsAlgClosed K] (ξ : Sp K ⟶ S), (∀ z, ∃ x ∈ V, A.hom x = ξ z) → ∃ (n : ℕ) (a : Fin n → (Over.mk ξ ⟶ A)), ⨆ i, ((fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  intro S A _ hA V K _ _ ξ hcov
  have hA' : IsAbelianScheme ((Over.pullback ξ).obj A) := GlobalTheory.isAbelianScheme_pullback_obj ξ A hA
  have hpb := isGrpPullback_pullback A ξ
  have hne : ((pullback.fst A.hom ξ ⁻¹ᵁ V : ((Over.pullback ξ).obj A).left.Opens) : Set ((Over.pullback ξ).obj A).left).Nonempty := by
    obtain ⟨x, hxV, hx⟩ := hcov (default : PrimeSpectrum K)
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback hpb.1 x _ hx
    exact ⟨p, by show pullback.fst A.hom ξ p ∈ V; rw [hp]; exact hxV⟩
  obtain ⟨n, a', ha'⟩ := _root_.GlobalTheory.AbCover.cover K ((Over.pullback ξ).obj A) hA' (pullback.fst A.hom ξ ⁻¹ᵁ V) hne
  let a : Fin n → (Over.mk ξ ⟶ A) := fun i => Over.homMk ((a' i).left ≫ pullback.fst A.hom ξ) (by
    show ((a' i).left ≫ pullback.fst A.hom ξ) ≫ A.hom = ξ
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have h := Over.w (a' i)
    change (a' i).left ≫ pullback.snd A.hom ξ = 𝟙 _ at h
    rw [h, Category.id_comp])
  refine ⟨n, a, ?_⟩
  have e : (A ⊗ Over.mk ξ).hom = ((Over.pullback ξ).obj A).hom ≫ ξ := by
    first | rfl | exact pullback.condition
  have hx : (fst A (Over.mk ξ)).left = Over.Hom.left (𝟙 ((Over.pullback ξ).obj A)) ≫ pullback.fst A.hom ξ := by
    first | rfl | simp
  have hy : ∀ i, (snd A (Over.mk ξ) ≫ a i).left = (toUnit ((Over.pullback ξ).obj A) ≫ a' i).left ≫ pullback.fst A.hom ξ := by
    intro i; first | rfl | simp [a]
  have key₁ : ∀ i, (fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)).left =
      (𝟙 ((Over.pullback ξ).obj A) * (toUnit ((Over.pullback ξ).obj A) ≫ a' i)).left ≫ pullback.fst A.hom ξ := fun i =>
    GlobalTheory.CoverOpCompat.push_mul hpb (T := ((Over.pullback ξ).obj A).left) (ρ := ((Over.pullback ξ).obj A).hom)
      (r := (A ⊗ Over.mk ξ).hom) e (𝟙 ((Over.pullback ξ).obj A)) (toUnit ((Over.pullback ξ).obj A) ≫ a' i)
      (fst A (Over.mk ξ)) (snd A (Over.mk ξ) ≫ a i) hx (hy i)
  have key₂ : ∀ i, ((snd A (Over.mk ξ) ≫ a i)⁻¹).left =
      ((toUnit ((Over.pullback ξ).obj A) ≫ a' i)⁻¹).left ≫ pullback.fst A.hom ξ := fun i =>
    GlobalTheory.CoverOpCompat.push_inv hpb (T := ((Over.pullback ξ).obj A).left) (ρ := ((Over.pullback ξ).obj A).hom)
      (r := (A ⊗ Over.mk ξ).hom) e (toUnit ((Over.pullback ξ).obj A) ≫ a' i) (snd A (Over.mk ξ) ≫ a i) (hy i)
  have key₃ : ∀ i, (fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)⁻¹).left =
      (𝟙 ((Over.pullback ξ).obj A) * (toUnit ((Over.pullback ξ).obj A) ≫ a' i)⁻¹).left ≫ pullback.fst A.hom ξ := fun i =>
    GlobalTheory.CoverOpCompat.push_mul hpb (T := ((Over.pullback ξ).obj A).left) (ρ := ((Over.pullback ξ).obj A).hom)
      (r := (A ⊗ Over.mk ξ).hom) e (𝟙 ((Over.pullback ξ).obj A)) ((toUnit ((Over.pullback ξ).obj A) ≫ a' i)⁻¹)
      (fst A (Over.mk ξ)) ((snd A (Over.mk ξ) ≫ a i)⁻¹) hx (key₂ i)
  refine Eq.trans ?_ ha'
  congr 1
  funext i
  rw [key₁ i, key₃ i, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]

end GlobalTheory.FibreCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSubringModelAbelianLineBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

noncomputable section

namespace GlobalTheory.SiegApproxModel

open GlobalTheory.SiegelDataDescent

theorem model_exists : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (F : Finset R), IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (_ : IsCommMonObj B) (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P₀ : LB (G2 B).left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) := by
  intro R _ A _ _ F hA P hP
  classical
  obtain ⟨S₀, B₀, _, φ₀, hF, hft₀, hab₀, hpb₀⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring_anyDim R A F hA
  have := hab₀.comm
  have := hab₀.smooth
  have := hab₀.proper
  have := hab₀.geomConnected
  obtain ⟨φ₂₀, hsq₀⟩ := exists_isSquare hpb₀.1.w
  have hpb₂₀ := isPullback_of_isSquare hpb₀.1 hsq₀
  have : IsProper (B₀ ⊗ B₀).hom := by
    change IsProper (pullback.fst B₀.hom B₀.hom ≫ B₀.hom)
    infer_instance
  obtain ⟨SP, hSP⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R S₀ (A ⊗ A).left (B₀ ⊗ B₀).left
    (A ⊗ A).hom (B₀ ⊗ B₀).hom φ₂₀ P hpb₂₀ hP
  obtain ⟨R₁, h, hT, hft⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S₀ SP hft₀
  let t : Sp R₁ ⟶ Sp S₀ := spMap (Subring.inclusion h)
  have e : spMap R₁.subtype ≫ t = spMap S₀.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let A₁ : Over (Sp R₁) := (Over.pullback t).obj B₀
  have hab₁ : IsAbelianScheme A₁ :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd B₀.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd B₀.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd B₀.hom t)) }
  have hpb₁ : IsPullback (pullback.fst B₀.hom t) A₁.hom B₀.hom t := IsPullback.of_hasPullback _ _
  have wφ : φ₀ ≫ B₀.hom = (A.hom ≫ spMap R₁.subtype) ≫ t := by
    rw [Category.assoc, e]; exact hpb₀.1.w
  let φ : A.left ⟶ A₁.left := pullback.lift φ₀ (A.hom ≫ spMap R₁.subtype) wφ
  have hφ₁ : φ ≫ pullback.fst B₀.hom t = φ₀ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ A₁.hom = A.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hφ : IsGrpPullback A A₁ (spMap R₁.subtype) φ :=
    (isGrpPullback_pullback B₀ t).cancel (hpb₀.congr e.symm hφ₁.symm) hφ₂
  obtain ⟨φ₂₁, hsq₁⟩ := exists_isSquare (A' := A₁) (A := B₀) (φ := pullback.fst B₀.hom t) hpb₁.w
  obtain ⟨φ₂, hsq⟩ := exists_isSquare hφ.1.w
  obtain ⟨P₁, hP₁, hiso⟩ := hSP R₁ h hT
    (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom φ₂₁ φ₂ (isPullback_of_isSquare hpb₁ hsq₁)
    (isSquare_comp hφ₁ hsq hsq₁ hsq₀) (isSquare_w hφ.1.w hsq)
  exact ⟨R₁, A₁, inferInstance, inferInstance, φ, φ₂, P₁, fun x hx => h (hF hx), hft, hab₁, hφ, hsq, hP₁, hiso⟩

end GlobalTheory.SiegApproxModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionConstantPeriodRatioPolarised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HalfRatio

variable {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}

theorem lamVal_change (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)) (hw : w.IsGen)
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) {J₁ J₂ : (Z ⟶ B.left) → M.ι} {J₁' J₂' : (Z ⟶ B'.left) → M'.ι}
    (h₁ : Good M z J₁) (h₂ : Good M z J₂) (h₁' : Good M' z J₁') (h₂' : Good M' z J₂') :
    lamVal w p z J₁ J₁' =
      (∏ I, gm (p ≫ β₂ ≫ PrimCocycle.lamφ B I) z (M.U (J₁ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)) ⊓ M.U (J₂ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)))
          (M.g (J₁ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)) (J₂ (p ≫ β₂ ≫ PrimCocycle.lamφ B I))) ^ PrimCocycle.lamε I) *
      (∏ I, gm (p ≫ PrimCocycle.lamφ B' I) z (M'.U (J₁' (p ≫ PrimCocycle.lamφ B' I)) ⊓ M'.U (J₂' (p ≫ PrimCocycle.lamφ B' I)))
          (M'.g (J₁' (p ≫ PrimCocycle.lamφ B' I)) (J₂' (p ≫ PrimCocycle.lamφ B' I))) ^ PrimCocycle.lamε I)⁻¹ *
      lamVal w p z J₂ J₂' := by
  have mQ : ∀ {J : (Z ⟶ B.left) → M.ι}, Good M z J → p z ∈ LB.wchart (abelian₂ B M) (fun _ : PUnit => β₂)
      (fun _ I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) := fun hJ =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => hJ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)
  have mQ' : ∀ {J : (Z ⟶ B.left) → M.ι}, Good M z J → (p ≫ β₂) z ∈ (abelian₂ B M).U
      (fun I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) := fun hJ =>
    Set.mem_iInter.2 fun I => hJ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)
  have mD : ∀ {J' : (Z ⟶ B'.left) → M'.ι}, Good M' z J' → p z ∈ (abelian₂ B' M').U
      (fun I => J' (p ≫ (psum B' (x2 B') I.down).left)) := fun hJ =>
    hJ.mem (fun I : ULift (Finset (Fin 2)) => (psum B' (x2 B') I.down).left) p
  have mi : p z ∈ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
      (fun _ I => J₁ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₁' (p ≫ (psum B' (x2 B') I.down).left)) :=
    TopologicalSpace.Opens.mem_inf.2 ⟨mQ h₁, mD h₁'⟩
  have mj : p z ∈ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
      (fun _ I => J₂ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₂' (p ≫ (psum B' (x2 B') I.down).left)) :=
    TopologicalSpace.Opens.mem_inf.2 ⟨mQ h₂, mD h₂'⟩
  have e := congrArg (gm p z _) (hw (fun _ I => J₁ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₁' (p ≫ (psum B' (x2 B') I.down).left))
    (fun _ I => J₂ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₂' (p ≫ (psum B' (x2 B') I.down).left)))
  rw [gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), map_mul, gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩)] at e
  refine e.trans (congrArg (· * _) ?_)
  have gQ := gm_linComb (abelian₂ B M) (fun _ : PUnit => β₂) (fun _ => 1) p z _ _ (mQ h₁) (mQ h₂)
  have gQ' := gm_linComb M (fun I : ULift (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (fun I => (-1) ^ (2 - I.down.card)) (p ≫ β₂) z _ _ (mQ' h₁) (mQ' h₂)
  have gD := gm_linComb M' (fun I : ULift (Finset (Fin 2)) => (psum B' (x2 B') I.down).left) (fun I => (-1) ^ (2 - I.down.card)) p z _ _ (mD h₁') (mD h₂')
  rw [Fintype.prod_unique, zpow_one] at gQ
  simp only [Category.assoc] at gQ'
  erw [map_mul, map_inv, gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), gQ, gQ', gD]

end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
theorem ag1 {G : Type*} [CommGroup G] (a b c d : G) : (a⁻¹*b*c*d⁻¹) * (a*b⁻¹*c⁻¹*d) = 1 := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_one]; abel
theorem ag2 {G : Type*} [CommGroup G] (A₂ B₂ C₂ TA TDl TQl TQt : G) (h1 : TA * TDl = 1) (h2 : TQl * TQt = 1) : (TA*A₂)⁻¹ * (TQl * TDl⁻¹ * B₂) * (TQt * C₂) = A₂⁻¹ * B₂ * C₂ := by
  rw [eq_inv_of_mul_eq_one_right h1, eq_inv_of_mul_eq_one_right h2]
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, inv_inv]; abel
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio

theorem exists_unitOn (K : Type) [Field K] (z : Sp K) (r : ((Sp K).presheaf.stalk z)ˣ) :
    ∃ k : Kˣ, gm (𝟙 (Sp K)) z ⊤ (unitOn k) = r := by
  obtain ⟨U, hz, f, hf⟩ := TopCat.Presheaf.germ_exist (Sp K).presheaf r.val
  have hs : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain rfl : U = ⊤ := top_unique fun x _ => (Subsingleton.elim z x) ▸ hz
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom f ≠ 0 := fun h => by
    have : f = 0 := ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply f).symm.trans
      ((congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom h).trans (map_zero _))
    rw [this, map_zero] at hf
    exact r.ne_zero hf.symm
  refine ⟨Units.mk0 _ h0, Units.ext ((gm_val _ z ⊤ trivial _).trans (Eq.trans ?_ hf))⟩
  exact congrArg ((Sp K).presheaf.germ ⊤ z hz).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply f)

theorem prod_neg {S : Scheme.{0}} {B : Over S} [GrpObj B] {T : Over S} (x y : T ⟶ B) {Z : Scheme.{0}} (κ : Z ⟶ T.left)
    {U : Type} [CommGroup U] (h : (Z ⟶ B.left) → U) : ∏ k, h (κ ≫ lamPts x y k) ^ negε k =
      (h (κ ≫ (x * y).left))⁻¹ * h (κ ≫ x.left) * h (κ ≫ y.left) * (h (κ ≫ (1 : T ⟶ B).left))⁻¹ := by
  simp only [Fin.prod_univ_four]
  simp [lamPts, negε]
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
theorem prod_tau {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a b : D.X) {U : Type} [CommGroup U]
    (h : ((TK R).left ⟶ D.P.A.left) → U) :
    ∏ k : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit, h (𝟙 _ ≫ Sum.elim (Sum.elim (Sum.elim (fun _ => ptK (D.c (a + b))) fun _ => ptK (D.c a))
        fun _ => ptK (D.c b)) (fun _ => (toUnit (TK R)).left ≫ eSec D.P.A) k) ^
      (Sum.elim (Sum.elim (Sum.elim (fun _ => -1) fun _ => - -1) fun _ => - -1) (fun _ => -1) k : ℤ) =
      (h (ptK (D.c (a + b))))⁻¹ * h (ptK (D.c a)) * h (ptK (D.c b)) * (h ((toUnit (TK R)).left ≫ eSec D.P.A))⁻¹ := by
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Category.id_comp]
  simp
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R'] {Q : Data R} {ρ : R →+* R'}
  {D : DegPre R'} {e : D.X ≃+ Q.X} {β : D.P.A.left ⟶ Q.B.left} {β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left}

theorem prod_cancel (hpb : IsGrpPullback D.P.A Q.B (spMap ρ) β) (hsq : IsSquare β β₂)
    (hc : ∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) {κ : (TK R').left ⟶ (TK R).left}
    (hκ : κ ≫ jK R = jK R' ≫ spMap ρ) {a b : D.X} {x y : TK R' ⟶ D.P.A} (hx : x = toUnit (TK R') ≫ D.c a)
    (hy : y = toUnit (TK R') ≫ D.c b) {U : Type} [CommGroup U] (H : ((TK R').left ⟶ Q.B.left) → U) :
    (∏ I, H ((lift x y).left ≫ β₂ ≫ PrimCocycle.lamφ Q.B I) ^ PrimCocycle.lamε I) *
      ∏ k, H (κ ≫ lamPts (toUnit (TK R) ≫ Q.c (e a)) (toUnit (TK R) ≫ Q.c (e b)) k) ^ negε k = 1 := by
  have hT : ∀ χ, (toUnit (TK R') ≫ D.c χ).left ≫ β = κ ≫ (toUnit (TK R) ≫ Q.c (e χ)).left := fun χ => by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hc χ]
    show jK R' ≫ spMap ρ ≫ _ = κ ≫ jK R ≫ _
    rw [← Category.assoc, ← hκ, Category.assoc]
  have c0 : D.c 0 = 1 := mul_eq_left.1 ((D.c_add 0 0).symm.trans (by rw [add_zero]))
  have q0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have hxy : toUnit (TK R') ≫ D.c (a + b) = x * y := by
    rw [hx, hy, ← MonObj.comp_mul]; exact congrArg (toUnit (TK R') ≫ ·) (D.c_add a b)
  let T' : Over (Sp R) := Over.mk ((TK R').hom ≫ spMap ρ)
  let up : (TK R' ⟶ D.P.A) → (T' ⟶ Q.B) := fun u => Over.homMk (u.left ≫ β)
    ((Category.assoc _ _ _).trans ((congrArg (u.left ≫ ·) hpb.1.w).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap ρ) (Over.w u)))))
  have f₁ : ((lift x y).left ≫ β₂) ≫ (fst Q.B Q.B).left = (up x).left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift x y).left ≫ ·) hsq.1).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (lift_fst x y))))
  have f₂ : ((lift x y).left ≫ β₂) ≫ (snd Q.B Q.B).left = (up y).left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift x y).left ≫ ·) hsq.2).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (lift_snd x y))))
  have hP : ((lift x y).left ≫ β₂) ≫ (G2 Q.B).hom = T'.hom :=
    (congrArg (_ ≫ ·) (Over.w (fst Q.B Q.B)).symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Q.B.hom) f₁).trans (Over.w (up x))))
  have hl : (lift (up x) (up y)).left = (lift x y).left ≫ β₂ := by
    have : lift (up x) (up y) = (Over.homMk _ hP : T' ⟶ G2 Q.B) :=
      CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Over.OverMorphism.ext f₁.symm))
        ((lift_snd _ _).trans (Over.OverMorphism.ext f₂.symm))
    exact congrArg (fun q : T' ⟶ G2 Q.B => q.left) this
  have ux : (up x).left = κ ≫ (toUnit (TK R) ≫ Q.c (e a)).left := hx ▸ hT a
  have uy : (up y).left = κ ≫ (toUnit (TK R) ≫ Q.c (e b)).left := hy ▸ hT b
  have uxy : (up x * up y).left = κ ≫ (toUnit (TK R) ≫ Q.c (e a) * toUnit (TK R) ≫ Q.c (e b)).left := by
    refine (hpb.2 _ x y (up x) (up y) rfl rfl).trans ?_
    rw [← hxy, hT, map_add (f := _), Q.c_add, MonObj.comp_mul]
  have u1 : (1 : T' ⟶ Q.B).left = κ ≫ (1 : TK R ⟶ Q.B).left := by
    have h : up 1 * up 1 = up 1 := Over.OverMorphism.ext ((hpb.2 _ 1 1 (up 1) (up 1) rfl rfl).trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (_root_.mul_one 1)))
    have h' := hT 0
    rw [map_zero, c0, q0, MonObj.comp_one, MonObj.comp_one] at h'
    rw [← mul_eq_left.1 h]; exact h'
  have h := PrimCocycle.prod_lam (up x) (up y) H
  have h₀ : (∏ I, H ((lift x y).left ≫ β₂ ≫ PrimCocycle.lamφ Q.B I) ^ PrimCocycle.lamε I) = _ :=
    Eq.trans (Finset.prod_congr rfl fun I _ => congrArg (fun q => H q ^ PrimCocycle.lamε I)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ PrimCocycle.lamφ Q.B I) hl.symm))) h
  rw [h₀, prod_neg _ _ κ H, ← ux, ← uy, ← uxy, ← u1, _root_.mul_comm]
  exact ag1 _ _ _ _

theorem ratio_indep (w : letI := D.P.isAb.comm; LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂))
    (hpb : IsGrpPullback D.P.A Q.B (spMap ρ) β) (hsq : IsSquare β β₂) (hw : w.IsGen)
    (hc : ∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) {κ : (TK R').left ⟶ (TK R).left}
    (hκ : κ ≫ jK R = jK R' ≫ spMap ρ) {a b : D.X} {x y : TK R' ⟶ D.P.A} (hx : x = toUnit (TK R') ≫ D.c a)
    (hy : y = toUnit (TK R') ≫ D.c b) :
    letI := D.P.isAb.comm
    ∀ z J₁ J₁' J₂ J₂', Good Q.M.L z J₁ → Good D.P.L z J₁' → Good Q.M.L z J₂ → Good D.P.L z J₂' →
      (val (D.tau a b) (𝟙 _) z J₁')⁻¹ * lamVal w (lift x y).left z J₁ J₁' * val (Q.tau (e a) (e b)) κ z J₁ =
      (val (D.tau a b) (𝟙 _) z J₂')⁻¹ * lamVal w (lift x y).left z J₂ J₂' * val (Q.tau (e a) (e b)) κ z J₂ := by
  letI := D.P.isAb.comm
  have hxy : toUnit (TK R') ≫ D.c (a + b) = x * y := by
    rw [hx, hy, ← MonObj.comp_mul]; exact congrArg (toUnit (TK R') ≫ ·) (D.c_add a b)
  intro z J₁ J₁' J₂ J₂' h₁ h₁' h₂ h₂'
  rw [GlobalTheory.UU.val_change (DVR.tau_isGen D a b) (𝟙 _) h₁' h₂', lamVal_change w hw _ z h₁ h₂ h₁' h₂',
    GlobalTheory.UU.val_change (Q.tau_gen _ _) κ h₁ h₂]
  refine ag2 _ _ _ _ _ _ _ ?_ ?_
  · refine (congrArg₂ (· * ·) ?_ (PrimCocycle.prod_lam x y
      fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q)))).trans (ag1 _ _ _ _)
    have e₁ : ptK (D.c (a + b)) = (x * y).left := congrArg (fun q : TK R' ⟶ D.P.A => q.left) hxy
    have e₂ : (toUnit (TK R')).left ≫ eSec D.P.A = (1 : TK R' ⟶ D.P.A).left := rfl
    have e₃ : ptK (D.c a) = x.left := hx ▸ rfl
    have e₄ : ptK (D.c b) = y.left := hy ▸ rfl
    have gen : ∀ (U : Type) [CommGroup U] (H : ((TK R').left ⟶ D.P.A.left) → U),
        (H (ptK (D.c (a + b))))⁻¹ * H (ptK (D.c a)) * H (ptK (D.c b)) * (H ((toUnit (TK R')).left ≫ eSec D.P.A))⁻¹ =
        (H (x * y).left)⁻¹ * H x.left * H y.left * (H (1 : TK R' ⟶ D.P.A).left)⁻¹ := fun U _ H =>
      congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg (fun q => (H q)⁻¹) e₁) (congrArg H e₃))
        (congrArg H e₄)) (congrArg (fun q => (H q)⁻¹) e₂)
    exact (prod_tau D a b fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q))).trans
      (gen _ fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q)))
  · exact prod_cancel hpb hsq hc hκ hx hy fun q => gm q z (Q.M.L.U (J₁ q) ⊓ Q.M.L.U (J₂ q)) (Q.M.L.g (J₁ q) (J₂ q))

theorem ratio_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (β : D.P.A.left ⟶ Q.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : letI := D.P.isAb.comm; LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)), IsGrpPullback D.P.A Q.B (spMap ρ) β → IsSquare β β₂ → w.IsGen → (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) → ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b, ∃ k : (FractionRing R')ˣ, ∀ z J J', Good Q.M.L z J → Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' * gm (𝟙 (TK R').left) z ⊤ (unitOn k) = (letI := D.P.isAb.comm; lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J') * val (Q.tau (e a) (e b)) κ z J := by
  intro R _ _ R' _ _ Q ρ D e β β₂ w hpb hsq hw hc κ hκ a b
  letI := D.P.isAb.comm
  have indep := ratio_indep w hpb hsq hw hc hκ (a := a) (b := b) rfl rfl
  have hs : Subsingleton (TK R').left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R')))
  let z₀ : (TK R').left := (⊥ : PrimeSpectrum (FractionRing R'))
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt Q.M.isLB z₀
  obtain ⟨J₀', hJ₀'⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z₀
  obtain ⟨k, hk⟩ := exists_unitOn (FractionRing R') z₀ ((val (D.tau a b) (𝟙 _) z₀ J₀')⁻¹ *
    lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z₀ J₀ J₀' * val (Q.tau (e a) (e b)) κ z₀ J₀)
  refine ⟨k, fun z J J' hJ hJ' => ?_⟩
  obtain rfl : z = z₀ := Subsingleton.elim _ _
  have hk' : gm (𝟙 (TK R').left) z₀ ⊤ (unitOn k) = _ := hk.trans (indep _ _ _ _ _ hJ₀ hJ₀' hJ hJ')
  rw [hk', _root_.mul_assoc, mul_inv_cancel_left]
end GlobalTheory.HalfRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.PicGenericInj

theorem exists_gen_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ N : LB G.left, N.IsLB → (∃ t : LB.Gen (N.pull (pullback.fst G.hom (jK R))), t.IsGen) → ∃ t : LB.Gen N, t.IsGen := by
  intro R _ _ _ _ _ G _ hG N hN ht
  have := hG.smooth
  have := hG.geomConnected
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)⟩
  exact GenericExtend.exists_isGen_of_densePart _ _ (jK R) ((isNormalScheme_iff_pred _).1 inferInstance) h₁ h₂
    h₃ inferInstance G (eSec G) N (Over.w η[G]) ‹_› (geometricallyIntegral_of_smooth G.hom) hN
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hN _)) ht

end GlobalTheory.PicGenericInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackCompletionChartToExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_grpPullback_chart_to_ext : ∀ (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G j e → ∀ (x : S) (C : Chart j A x), ∃ π : C.G.left ⟶ G.left, IsGrpPullback C.G G C.ξ π ∧ C.α ≫ e = pullback.fst C.G.hom (jK C.R) ≫ π := by
  intro X S j _ _ A _ G _ e hG he x C
  obtain ⟨_, hnorm⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R
  have hG' : IsSemiAbelian ((Over.pullback C.ξ).obj G) := IsSemiAbelian.pullback C.ξ G hG
  have hp : IsGrpPullback ((Over.pullback C.ξ).obj G) G C.ξ (pullback.fst G.hom C.ξ) := isGrpPullback_pullback G C.ξ
  have h1 : IsGrpPullback ((Over.pullback (jK C.R)).obj C.G) G (jK C.R ≫ C.ξ) (C.α ≫ e) :=
    (C.gen.comp he).congr C.hy rfl
  have h2 : IsGrpPullback ((Over.pullback (jK C.R)).obj ((Over.pullback C.ξ).obj G)) G (jK C.R ≫ C.ξ)
      (pullback.fst ((Over.pullback C.ξ).obj G).hom (jK C.R) ≫ pullback.fst G.hom C.ξ) :=
    (isGrpPullback_pullback _ (jK C.R)).comp hp
  obtain ⟨ε, hε, hεc⟩ := grpPullback_iso h1 h2
  obtain ⟨Φ, ⟨hΦ, hFε⟩, -⟩ := GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic (FractionRing C.R) C.G
    ((Over.pullback C.ξ).obj G) C.semi hG' ε
  replace hFε : (Over.pullback (jK C.R)).map Φ.hom = ε.hom := hFε
  refine ⟨Φ.hom.left ≫ pullback.fst G.hom C.ξ, ((isGrpPullback_of_iso Φ).comp hp).congr (Category.id_comp _) rfl, ?_⟩
  rw [← hεc, ← hFε]
  have hl : ((Over.pullback (jK C.R)).map Φ.hom).left ≫ pullback.fst ((Over.pullback C.ξ).obj G).hom (jK C.R) =
      pullback.fst C.G.hom (jK C.R) ≫ Φ.hom.left := pullback.lift_fst _ _ _
  rw [← Category.assoc, hl, Category.assoc]

end GlobalTheory.Desc
end

