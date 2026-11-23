module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0659
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem allPrim_of_abelianDeRhamFree (h : GlobalTheory.Published.AbelianDeRhamFree) (R : Type) [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : AllPrim (dp0 R) (𝟙 _) A := by
  have hdim : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
    haveI := hg
    haveI : SmoothOfRelativeDimension g (pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip hg
    exact inferInstanceAs (SmoothOfRelativeDimension (g + g) (pullback.fst A.hom A.hom ≫ A.hom))
  obtain ⟨f1, p1, r1, -⟩ := h R A g hA hg
  obtain ⟨f2, p2, r2, -⟩ := h R (A ⊗ A) (g + g)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hdim
  have one0 : ∀ c, pullOver (dp0 R) (𝟙 _) (1 : A ⟶ A) c = 0 := fun c => by
    haveI : IsIso ((𝟙_ (Over (Sp R))).hom ≫ 𝟙 _) := inferInstanceAs (IsIso (𝟙 (Sp R) ≫ 𝟙 _))
    rw [Hom.one_def, ← pullOver_pullOver, firstDeRham_base_eq_zero _ (pullOver (dp0 R) (𝟙 _) η[A] c), map_zero]
  have id0 : ∀ c, pullOver (dp0 R) (𝟙 _) (𝟙 A) c = c := fun c => IsMor.pullCohomologyOne_id _ c
  let Ψ := (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) (1 : A ⟶ A))).prod
    (pullOver (dp0 R) (𝟙 _) (lift (1 : A ⟶ A) (𝟙 A)))
  have hs : Function.Surjective Ψ := fun ⟨a, b⟩ =>
    ⟨pullOver (dp0 R) (𝟙 _) (fst A A) a + pullOver (dp0 R) (𝟙 _) (snd A A) b, by
    refine Prod.ext ?_ ?_
    · change pullOver _ _ _ _ = a
      rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, one0, id0, add_zero]
    · change pullOver _ _ _ _ = b
      rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, one0, id0, zero_add]⟩
  have hb : Function.Bijective Ψ := Module.bijective_of_surjective_of_rankAtStalk_eq hs (by
    intro m hm
    rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2]; ring)
  refine eq_top_iff.2 fun c _ => (mem_prim_iff _ _ _ _).2 (hb.1 ?_)
  have e1 : lift (𝟙 A) (1 : A ⟶ A) ≫ μ[A] = 𝟙 A := by rw [← Hom.mul_def, _root_.mul_one]
  have e2 : lift (1 : A ⟶ A) (𝟙 A) ≫ μ[A] = 𝟙 A := by rw [← Hom.mul_def, _root_.one_mul]
  refine Prod.ext ?_ ?_
  · change pullOver _ _ _ _ = pullOver _ _ _ _
    rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, e1,
      one0, id0, add_zero]
  · change pullOver _ _ _ _ = pullOver _ _ _ _
    rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, e2,
      one0, id0, zero_add]

theorem abelianDeRhamFree_toFree (h : GlobalTheory.Published.AbelianDeRhamFree) :
    GlobalTheory.Published.AbelianDeRham.Free := fun R _ A _ g hA hg =>
  ⟨allPrim_of_abelianDeRhamFree h R A g hA hg, h R A g hA hg⟩

theorem abelianDeRhamStructure_toFree (h : GlobalTheory.Published.AbelianDeRhamStructure) :
    GlobalTheory.Published.AbelianDeRham.Free :=
  abelianDeRhamFree_toFree h.1

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomAgreeLocusClosedSubschemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_homAgreeLocus_closedSubscheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → (φ' ≫ u.left = φ' ≫ v.left ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  first | (exact @GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme) | (exact GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme) | (intros; apply GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem abelianScheme_left_isSeparated_of_affine :
    ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated := by
  intro R _ A _ h
  haveI : IsProper A.hom := h.proper
  refine ⟨?_⟩
  rw [← terminal.comp_from A.hom]
  infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAugEqvOfIsIntegralHomOfStrictlyHenselian
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.IntDescent

theorem isIntegral_algClosure_residue (A : Type) [CommRing A] [IsLocalRing A] :
    Algebra.IsIntegral A (AlgebraicClosure (IsLocalRing.ResidueField A)) := by
  haveI : Algebra.IsIntegral A (IsLocalRing.ResidueField A) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId A (IsLocalRing.ResidueField A)) IsLocalRing.residue_surjective
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)) :=
    Algebra.IsAlgebraic.isIntegral
  exact Algebra.IsIntegral.trans (IsLocalRing.ResidueField A)

theorem isIntegral_tensor (A C B : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B]
    [Algebra.IsIntegral A C] [Algebra.IsIntegral A B] : Algebra.IsIntegral A (C ⊗[A] B) := by
  constructor
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul x y =>
      have h1 : IsIntegral A (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := C) (B := B) x) :=
        (Algebra.IsIntegral.isIntegral x).map _
      have h2 : IsIntegral A (Algebra.TensorProduct.includeRight (R := A) (A := C) (B := B) y) :=
        (Algebra.IsIntegral.isIntegral y).map _
      have := h1.mul h2
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using this
  | add x y hx hy => exact hx.add hy

theorem L1 : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)],
    IsUnit (q : A) → ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
    Eqv (ZMod q) (spMap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom) (tw q i) := by
  intro q i A _ _ _ hq B _ _ _
  have hSH : SH A := ⟨inferInstance, inferInstance⟩
  obtain ⟨ζ0⟩ := GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian q A hSH hq
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) := ζ0.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hgen := GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i (Spec (CommRingCat.of A)) ζ
  haveI := isIntegral_algClosure_residue A
  haveI := isIntegral_tensor A (AlgebraicClosure (IsLocalRing.ResidueField A)) B
  have hfin := GlobalTheory.T.tateTwist_finitary q i
  have hU := GlobalTheory.T.integral_strictHenselian_acyclic_finitary (ZMod q) (tw q i) hfin A B hSH
  have hU' := GlobalTheory.T.integral_strictHenselian_acyclic_finitary (ZMod q) (tw q i) hfin A (AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B) hSH
  have hbij := _root_.GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor (ZMod q) A B
  exact GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective (ZMod q) (tw q i) _ _ hgen (Spec (CommRingCat.of B)) _
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) _ hU hU' hbij

end GlobalTheory.EtC.IntDescent

namespace GlobalTheory.EtC


open IntDescent in
theorem cechAug_eqv_of_isIntegralHom_of_strictlyHenselian : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)), IsIntegralHom g → Surjective g → Eqv _ (cechAug g) (tw q i) := by
  intro q i A _ hSH hq Y g hg hsurj
  obtain ⟨_, _⟩ := hSH
  set Ω := AlgebraicClosure (IsLocalRing.ResidueField A)
  set u : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Ω)) with hu_def
  have hpb : IsPullback (pullback.fst g u) (pullback.snd g u) g u := IsPullback.of_hasPullback g u
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ (pullback.fst g u) (pullback.snd g u) g u hpb
  have hsq : ∀ (Z Z' : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of A)) (h' : Z' ⟶ Spec (CommRingCat.of Ω)) (φ : Z' ⟶ Z),
      IsIntegralHom h → IsPullback φ h' h u → Eqv (ZMod q) (sch.map φ) (tw q i) :=
    GlobalTheory.T.etaleCohomologyEquivalence_pullback_integral_affine (ZMod q) (tw q i) A Ω (fun B _ _ _ => L1 q i A hq B)
  have hEm : Eqv (ZMod q) m (tw q i) :=
    GlobalTheory.T.levelwiseEquivalence_isEquivalence (ZMod q) m (tw q i) (GlobalTheory.T.cechNerve_levelwise_equivalence_integral_pullback (ZMod q) (tw q i) _ _ _ _ _ _ g u hpb hg hsq m hm)
  have hEu : Eqv (ZMod q) (sch.map u) (tw q i) :=
    hsq _ _ (𝟙 _) (𝟙 _) u inferInstance (IsPullback.id_vert u)
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.exists_point_algClosure_residueField_of_isIntegralHom A Y g hg hsurj
  have hEs : Eqv (ZMod q) (cechAug (pullback.snd g u)) (tw q i) :=
    _root_.GlobalTheory.cechAug_eqv_of_section (ZMod q) (tw q i) _ _ (pullback.snd g u) (pullback.lift s (𝟙 _) (by rw [hs, Category.id_comp]))
      (pullback.lift_snd _ _ _)
  obtain ⟨-, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have h1 : Eqv (ZMod q) (cechAug (pullback.snd g u) ≫ sch.map u) (tw q i) :=
    (hcomp _ _ _ _ _).1 hEs hEu
  rw [← hm.w] at h1
  exact (hcomp _ _ _ _ _).2.1 hEm h1

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyVanishesPositive
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cohomology_vanishes_positive : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 0 < s → Subsingleton (Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.cech_level_acyc) | (exact GlobalTheory.EtC.GmStep.cech_level_acyc) | (intros; apply GlobalTheory.EtC.GmStep.cech_level_acyc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelAcyclic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC
theorem sh_of_isSepClosed (Ω : Type) [Field Ω] [IsSepClosed Ω] : SH Ω := by
  refine ⟨inferInstance, ?_⟩
  haveI : Algebra.IsIntegral Ω (IsLocalRing.ResidueField Ω) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId Ω (IsLocalRing.ResidueField Ω)) IsLocalRing.residue_surjective
  exact Algebra.IsAlgebraic.isSepClosed (F := Ω)

theorem cech_level_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (m : ℕ), 0 < m → ∀ y : H R (disc.obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌))) F m, y = 0 := by
  intro R _ F hF K Ω _ _ _ _ k m hm y
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have hf : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
    IsIntegralHom.SpecMap_iff.2 fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨Z, π, e, hπ, -⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom _ _ _ hf (op ⦋k⦌)
  haveI : IsIntegralHom π := hπ
  haveI : IsAffine Z := isAffine_of_isAffineHom π
  let φ : Ω →+* Γ(Z, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ π.appTop).hom
  letI : Algebra Ω Γ(Z, ⊤) := φ.toAlgebra
  have hint : (π.app ⊤).hom.IsIntegral := π.isIntegral_app ⊤ (isAffineOpen_top _)
  haveI : Algebra.IsIntegral Ω Γ(Z, ⊤) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨p, hp, h⟩ := hint b
    refine ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom, hp.map _, ?_⟩
    have hc : (algebraMap Ω Γ(Z, ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom = (π.app ⊤).hom := by
      ext x
      change ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ π.app ⊤).hom x = _
      rw [Iso.hom_inv_id_assoc]
      rfl
    rw [Polynomial.eval₂_map, hc]
    exact h
  have hac : AcycF R (sp Γ(Z, ⊤)) F := GlobalTheory.T.integral_strictHenselian_acyclic_finitary R F hF Ω Γ(Z, ⊤) (sh_of_isSepClosed Ω)
  let i : sp Γ(Z, ⊤) ≅ disc.obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) :=
    sch.mapIso Z.isoSpec.symm ≪≫ disc.mapIso e
  have heq : Eqv R i.hom F := (GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).1 _ _ i.hom inferInstance
  have hs := ((GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).2.2.2 _ _ i.hom heq).1 hac (m : ℤ) (by exact_mod_cast hm)
  exact Subsingleton.elim _ _

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapLinear
section
set_option autoImplicit false

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer

theorem Close.comap_linear : ∀ {I I' : Type} [Fintype I] [Fintype I'] {g g' : ℕ} {W : Opens (Tot I g)} {W' : Opens (Tot I' g')} {C : Type} [CommRing C] (J : Ideal C) (ρ₁ ρ₂ : Hol W' →+* C) (ψ : Hol W →+* Hol W') (M : Fin g → Fin g' → ℂ), (∀ a f, dw a (ψ f) = ∑ b, M b a • ψ (dw b f)) → Close J ρ₁ ρ₂ → Close J (ρ₁.comp ψ) (ρ₂.comp ψ) := by
  intro I I' _ _ g g' W W' C _ J ρ₁ ρ₂ ψ M hψ h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail σ τ _ s ih =>
    obtain ⟨n, h1, h2, h3⟩ := s
    refine Relation.ReflTransGen.tail ih
      ⟨fun b ↦ ∑ a, σ (algebraMap ℂ (Hol W') (M b a)) * n a,
        fun b ↦ J.sum_mem fun a _ ↦ J.mul_mem_left _ (h1 a), fun b c ↦ ?_, fun f ↦ ?_⟩
    · rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun a' _ ↦ ?_
      calc σ (algebraMap ℂ (Hol W') (M b a)) * n a * (σ (algebraMap ℂ (Hol W') (M c a')) * n a')
          = σ (algebraMap ℂ (Hol W') (M b a)) * σ (algebraMap ℂ (Hol W') (M c a')) * (n a * n a') := by ring
        _ = 0 := by rw [h2, mul_zero]
    · simp only [RingHom.comp_apply]
      rw [h3 (ψ f)]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [hψ, map_sum, Algebra.smul_def, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
      ring

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHermitianFormUnitaryChartSectionStatement
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexHermitianForm_unitaryChartSection : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ (τ : X.Ψ) (u v : Fin r → ℂ), hermC τ.1 X.Gm (secM X x w τ *ᵥ u) (secM X x w τ *ᵥ v) = hermC τ.1 X.Gm u v := by
  first | exact @GlobalTheory.SUChartSection.hermC_secM | exact GlobalTheory.SUChartSection.hermC_secM | (intros; apply GlobalTheory.SUChartSection.hermC_secM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstBiadditiveCoboundarySymmetric
section
set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}

theorem exists_shift_retraction (H : ∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') (l : Λ) (T : K.Obj) :
    ∃ (S : K.Obj) (s : S ⟶ T) (s' : T ⟶ S), s.deg = l ∧ s'.deg = -l ∧ s' ≫ s = 𝟙 T := by
  obtain ⟨k, h1, h2⟩ := H l T.k
  let S : K.Obj :=
    { k := k, C := T.C, J := T.J, nil := T.nil, ρ := T.ρ.comp (K.sh h1)
      ρ_cst := fun f ↦ (congrArg T.ρ (K.sh_cst h1 f)).trans (T.ρ_cst f) }
  have key : ∀ m (h : K.le m T.k T.k), m = 0 → ∀ f, K.sh h f = f := by
    rintro m h rfl f
    exact K.sh_refl h f
  have e : (T.ρ.comp (K.sh h1)).comp (K.sh h2) = T.ρ := RingHom.ext fun f ↦
    congrArg T.ρ ((K.sh_sh h2 h1 (K.le_trans h2 h1) f).trans (key _ _ (neg_add_cancel l) f))
  let s : S ⟶ T := ⟨AlgHom.id _ _, l, h1, fun _ h ↦ h, Relation.ReflTransGen.refl⟩
  let s' : T ⟶ S := ⟨AlgHom.id _ _, -l, h2, fun _ h ↦ h, by
    change Close T.J ((T.ρ.comp (K.sh h1)).comp (K.sh h2)) T.ρ
    rw [e]
    exact Relation.ReflTransGen.refl⟩
  exact ⟨S, s, s', rfl, rfl, hom_ext (fun _ ↦ rfl) (neg_add_cancel l)⟩

theorem eq_of_cst_eq (hR : K.Rich) {f f' : Hol F.V} (h : ∀ k, K.cst k f = K.cst k f') : f = f' :=
  Hol.ext_fn fun z hz ↦ by
    obtain ⟨k, hk⟩ := hR.1 (z, 0) hz
    exact (K.fn_cst k f hk).symm.trans ((congrArg (fun u ↦ Hol.fn u (z, 0)) (h k)).trans (K.fn_cst k f' hk))

end GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem const_biadditive_coboundary_symm : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), (∀ c : C1 K.Oc, (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → c T T'' (φ ≫ ψ) = mp K.Oc ψ (c T T' φ) + c T' T'' ψ) → ∃ γ : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c T T' φ = d0 K.Oc γ T T' φ) → (∀ γ : C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → mp K.Oc φ (γ T) = γ T') → ∃ r : Hol F.V, ∀ T, γ T = algebraMap (Hol F.V) (K.Oc.obj T) r) → (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') → K.Rich → ∀ (β : Λ →+ Λ →+ Hol F.V) (c : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), d1 K.Oc c T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg)) → ∀ l m, β l m = β m l := by
  intro I _ g Λ _ F K H1 H2 H3 hR β c hd l m
  obtain ⟨γ, hγ⟩ := H1 c fun T T' T'' φ ψ h h' ↦ by
    have := hd T T' T'' φ ψ
    rw [d1_apply, h', map_zero, map_zero] at this
    linear_combination -this
  obtain ⟨c', hc0, hd'⟩ : ∃ c' : C1 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c' T T' φ = 0) ∧
      ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), mp K.Oc ψ (c' T T' φ) - c' T T'' (φ ≫ ψ) + c' T' T'' ψ =
        algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg) := by
    refine ⟨fun T T' φ ↦ c T T' φ - d0 K.Oc γ T T' φ, fun T T' φ h ↦ sub_eq_zero.2 (hγ T T' φ h),
      fun T T' T'' φ ψ ↦ ?_⟩
    have e1 := hd T T' T'' φ ψ
    have e2 : d0 K.Oc γ T T'' (φ ≫ ψ) = mp K.Oc ψ (d0 K.Oc γ T T' φ) + d0 K.Oc γ T' T'' ψ := commAlgFunctorCoboundaryZero_mem_cocyclesOne K.Oc γ φ ψ
    rw [d1_apply] at e1
    rw [map_sub]
    linear_combination e1 + e2
  choose S s s' hs hs' hss using Charts.exists_shift_retraction H3
  have hκ : ∀ (n : Λ) (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = n → c' T T' φ = c' _ T' (s n T') := by
    intro n T T' φ h
    have h0 : Charts.Hom.deg (φ ≫ s' n T') = 0 := by rw [Charts.comp_deg, h, hs', add_neg_cancel]
    have := hd' _ _ _ (φ ≫ s' n T') (s n T')
    rw [hc0 _ _ _ h0, h0, Category.assoc, hss, Category.comp_id, map_zero, map_zero, AddMonoidHom.zero_apply,
      map_zero] at this
    linear_combination -this
  have hr : ∀ n : Λ, ∃ r : Hol F.V, ∀ T, c' _ T (s n T) = algebraMap (Hol F.V) (K.Oc.obj T) r := fun n ↦
    H2 (fun T ↦ c' _ T (s n T)) fun T T' φ h ↦ by
      have := hd' _ _ _ (s n T) φ
      rw [hc0 _ _ _ h, h, map_zero, map_zero,
        hκ n _ _ (s n T ≫ φ) (by rw [Charts.comp_deg, h, hs, add_zero])] at this
      linear_combination this
  choose r hr using hr
  have main : ∀ (a b : Λ) (T : K.Obj), algebraMap (Hol F.V) (K.Oc.obj T) (β a b) =
      algebraMap (Hol F.V) (K.Oc.obj T) (r a - r (a + b) + r b) := by
    intro a b T
    have := hd' _ _ _ (s a (S b T)) (s b T)
    rw [hκ (a + b) _ _ (s a (S b T) ≫ s b T) (by rw [Charts.comp_deg, hs, hs]), hr, hr, hr, hs, hs,
      AlgHom.commutes] at this
    set_option synthInstance.maxHeartbeats 200000 in
      rw [← this, map_add (algebraMap (Hol F.V) (K.Oc.obj T)), map_sub]
  refine Charts.eq_of_cst_eq hR fun k ↦ ?_
  refine (main l m (K.triv k)).trans (Eq.trans ?_ (main m l (K.triv k)).symm)
  congr 1
  rw [add_comm m l]
  ring

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationLinear
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LawDer.ConstLin

variable {R : Type} [CommRing R] {d : ℕ}

end GlobalTheory.LawDer.ConstLin

theorem GlobalTheory.LawDer.constantCoeff_iterate_invDer_sub_linear :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → (∀ i, swap (μ i) = μ i) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R), ∃ r : R, constantCoeff ((invDer μ u)^[p] F) - ∑ j, constantCoeff ((invDer μ u)^[p] (X j)) * coeff (Finsupp.single j 1) F = p * r := by
  first
  | exact @_root_.GlobalTheory.LinearPartIteration.iterate_linear_part
  | exact _root_.GlobalTheory.LinearPartIteration.iterate_linear_part
  | (apply _root_.GlobalTheory.LinearPartIteration.iterate_linear_part <;> assumption)
  | (intros; apply _root_.GlobalTheory.LinearPartIteration.iterate_linear_part <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LinearPartIteration.iterate_linear_part <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LinearPartIteration.iterate_linear_part ..)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijective
section
open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

theorem small_descent_H2_bijective (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (O κ s) (IsSmall κ s U).ι).pull2 := by
  refine GlobalTheory.CatCoh.Desc.pull2_bijective (O κ s) ?_ (IsSmall κ s U) ?_ ?_
  · intro T b
    obtain ⟨T', l, h1, h2, h3, h4⟩ := GlobalTheory.ThickLoc.exists_localization R I κ X s T b
    exact ⟨T', l, by simpa only [mp_O] using h1, by simpa only [mp_O] using h2,
      by simpa only [mp_O] using h3, by simpa only [mp_O] using h4⟩
  · rintro S S' φ ⟨i, hi⟩
    exact ⟨i, GlobalTheory.Cris.Thick.Hom.le_preimage φ hi⟩
  · intro T
    obtain ⟨n, b, hb, h⟩ := exists_finite_small_cover R I κ X s K U hU T
    exact ⟨n, b, hb, fun i S u hu => h i S u (by simpa only [mp_O] using hu)⟩

end GlobalTheory.Cris
end

