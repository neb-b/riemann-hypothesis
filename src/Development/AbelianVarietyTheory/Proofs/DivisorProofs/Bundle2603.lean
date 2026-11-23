module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoExtendsSemiAbelianDvrInducingFormal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalPointsAbelianPartsMultiply
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.FormalMul

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

theorem map_b_eq {U : UnifPre I D A G} {T : Over (Sp R)} {x : T ⟶ G} {g : GtPt D.toPre T}
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U x g) (e : ℕ) :
    (Over.pullback (thick R I e)).map g.b = (Over.pullback (thick R I e)).map x ≫ (U.gt e).q :=
  (GlobalTheory.FormalExt.map_eq_iff I e g.b _).2 ((hg e).1.trans (Category.assoc _ _ _).symm)

theorem b_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (h h' : (𝟙_ (Over (Sp V))) ⟶ G) (g g' g'' : GtPt D.toPre (𝟙_ (Over (Sp V)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h' g' → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre (h * h') g'' → g''.b = g.b * g'.b := by
  intro V _ _ _ hV D A G _ _ _ U h h' g g' g'' hg hg' hg''
  have := hV.1
  have := hV.2.2.1
  have := D.toPre.P.isAb.proper
  have h1 : Smooth (𝟙_ (Over (Spec (CommRingCat.of V)))).hom := inferInstanceAs (Smooth (𝟙 _))
  have h1' : GeometricallyConnected (𝟙_ (Over (Spec (CommRingCat.of V)))).hom :=
    inferInstanceAs (GeometricallyConnected (𝟙 _))
  refine GlobalTheory.FormalExt.hom_ext_thick (maximalIdeal V) (IsAdicComplete.le_jacobson_bot _) _ fun e => ?_
  have := (U.gt e).q_hom
  rw [Functor.map_mul, map_b_eq hg, map_b_eq hg', map_b_eq hg'', Functor.map_mul, MonObj.mul_comp]

end GlobalTheory.Poinc.Sep.FormalMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedOfDualConstField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.TangentCrit

theorem formallyUnramified_of_dual_const_field {K A B : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    [Algebra.FiniteType K B] [Algebra.FiniteType A B]
    (H : ∀ φ : B →+* DualNumber K, (∀ c, φ (algebraMap K B c) = algebraMap K (DualNumber K) c) →
      (∀ a, (φ (algebraMap A B a)).snd = 0) → ∀ b, (φ b).snd = 0) :
    Algebra.FormallyUnramified A B := by
  refine ⟨?_⟩
  by_contra hne
  rw [← Module.support_eq_empty_iff (R := B), ← ne_eq, ← Set.nonempty_iff_ne_empty] at hne
  obtain ⟨p, hp⟩ := hne
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  let P : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  have hP : P ∈ Module.support B Ω[B⁄A] := by
    rw [Module.support_eq_zeroLocus] at hp ⊢
    exact fun x hx => hpm (hp hx)
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hP
  have hsurj : Function.Surjective (algebraMap B m.ResidueField) := by
    intro y
    obtain ⟨x, rfl⟩ := m.bijective_algebraMap_quotient_residueField.surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨b, rfl⟩
  haveI : Algebra.FiniteType K m.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom K B m.ResidueField) hsurj
  haveI : Module.Finite K m.ResidueField := finite_of_finite_type_of_isJacobsonRing K _
  let ev : m.ResidueField →ₐ[K] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra m.ResidueField K := ev.toRingHom.toAlgebra
  letI : Algebra B K := (ev.toRingHom.comp (algebraMap B m.ResidueField)).toAlgebra
  haveI : IsScalarTower B m.ResidueField K := .of_algebraMap_eq fun _ => rfl
  letI : Algebra A K := ((algebraMap B K).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B K := .of_algebraMap_eq fun _ => rfl
  have key : Function.Injective ((0 : Ω[B⁄A] →ₗ[B] PUnit.{1}).lTensor m.ResidueField) :=
    lTensor_injective_of_extend (k := K) _ fun χ => by
      refine ⟨0, ?_⟩
      let D : Derivation A B K := χ.compDer (KaehlerDifferential.D A B)
      have hlin : ∀ c, derToDual D (algebraMap K B c) = algebraMap K (DualNumber K) c := by
        intro c
        ext
        · rw [fst_derToDual]
          change ev (algebraMap B m.ResidueField (algebraMap K B c)) = _
          rw [← IsScalarTower.algebraMap_apply, ev.commutes]
          rfl
        · rw [snd_derToDual, IsScalarTower.algebraMap_apply K A B, D.map_algebraMap]
          rfl
      have := H (derToDual D) hlin (fun a => (snd_derToDual D _).trans (D.map_algebraMap a))
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b => ?_)
      have := this b
      rw [snd_derToDual] at this
      simpa [D] using this.symm
  obtain ⟨z, hz⟩ := exists_ne (0 : m.ResidueField ⊗[B] Ω[B⁄A])
  exact hz (key (by simp))

end GlobalTheory.TangentCrit

namespace GlobalTheory.TangentCrit

end GlobalTheory.TangentCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantPointDescendsToSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FinDescent

theorem galoisFixed_point_of_finite : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : Over (Sp V)), IsFinite N.hom → ∀ (nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V), spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left) → ∃ s : 𝟙_ (Over (Sp V)) ⟶ N, nb = toUnit _ ≫ s := by
  first
  | exact @_root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed
  | exact _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed
  | (apply _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed ..)

end GlobalTheory.FinDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientSmoothBaseChangeIsoClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem quotient_smooth_and_baseChange_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ)) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hΓ D D' hD A' G' _ _ hG U' a H hH _ X π hX hπ _ hinv hfib hsec x hx
  obtain ⟨_, rfl⟩ : ∃ _ : Algebra R R', algebraMap R R' = ρ := ⟨ρ.toAlgebra, rfl⟩
  have hw := fun σ => (a.cart σ).1.w
  obtain ⟨Y, φ, hY, hφ, hsucc, hσ⟩ := @GlobalTheory.FormalModel.exists_model R _ _ _ hR R' _ _ _ _ D D' hD A' G' _ _ U' a
  obtain ⟨V, W, hxV, hV, hW, hVW⟩ := @_root_.GlobalTheory.Mum.exists_affine_chart R _ _ _ R' _ _ _ _ hR hρ hΓ G' a.act hw a.act_one a.act_mul H hH X π hX hπ hinv
    hfib hsec Y φ hY hφ hsucc hσ x hx
  obtain ⟨C', _, _, _, _, actC, C, j, l, hj, hl, hlV, hP, hjs, hls, hact, hlin, hC⟩ := @_root_.GlobalTheory.Mum.quot_affine_spec_invariants R _ _ _ R' _ _ _ _ hR hρ hΓ G'
    a.act hw a.act_one a.act_mul H hH X π hX hπ hinv hfib hsec V hV
  have hr : Set.range j = π ⁻¹' (V : Set X.left) := by
    rw [← hlV, ← Scheme.Pullback.range_fst π l, ← hP.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, hP.isoPullback.hom.surjective.range_eq, Set.image_univ]
  have hr' : (j ≫ H.ι).opensRange = H.ι ''ᵁ (π ⁻¹ᵁ V) := by
    ext1
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hr]
    rfl
  obtain ⟨O, _, _, i', hO, h₁, h₂, h₃⟩ := @_root_.GlobalTheory.Mum.exists_invariant_maps_of_affine_open R _ R' _ _ _ G' a.act Y φ hY hφ hsucc hσ C' _ _ _ _ actC (j ≫ H.ι) _
    (by rw [Category.assoc, hjs]) (fun σ => by rw [hact, Category.assoc]) W hW (by rw [hVW, hr'])
  have : IsNoetherianRing R := hR.1.1
  have : IsNoetherianRing R' := hρ.1.1
  have : Module.Finite R R' := RingHom.finite_algebraMap.1 hρ.2.2
  obtain ⟨i, k₁, k₂, k₃⟩ := @_root_.GlobalTheory.exists_compatible_maps_mod_pow_maximalIdeal_base R _ _ R' _ _ _ _ _ C' _ _ _ _ _ (fun σ => actC σ) O _ _ i' h₁ h₂ h₃
  have : Algebra.FiniteType R' C' := by
    have := U'.smooth
    have : LocallyOfFiniteType (spMap (algebraMap R' C')) := by rw [← hjs]; infer_instance
    exact RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this)
  obtain ⟨hft, -, f, hf, hf₁, hf₂, hiso⟩ := _root_.GlobalTheory.InvAlg.invariants_of_trivial_on_thickenings R hR.1 R' hρ.2.1 hΓ C' actC hlin O i k₁ k₂ k₃ C hC
  obtain ⟨p, rfl⟩ : x ∈ Set.range j := by rw [hr]; exact hxV
  let q : Sp C := spMap (algebraMap C C') p
  have hq : l q = π (j p) := by rw [← Scheme.Hom.comp_apply, ← hP.w, Scheme.Hom.comp_apply]
  have hq' : q.asIdeal.comap (algebraMap R C) = maximalIdeal R := by
    have : spMap (algebraMap R C) q = closedPoint R := by
      rw [← hx, ← hls, Scheme.Hom.comp_apply, hq, ← Scheme.Hom.comp_apply, hX]
      simp only [Scheme.Hom.comp_apply]
    exact congrArg PrimeSpectrum.asIdeal this
  obtain ⟨g, hg, hsm⟩ := @_root_.GlobalTheory.SmoothAdic.exists_smooth_away_of_quotient_pow_equiv R _ _ _ O C _ _ _ _ hO hft hiso q.asIdeal q.isPrime hq'
  have hfq : f ∉ q.asIdeal := fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := q.asIdeal.sub_mem h (Ideal.map_le_iff_le_comap.2 hq'.ge hf)
    rwa [sub_sub_cancel] at this))
  rw [← hq]
  exact @_root_.GlobalTheory.Mum.LocIso.exists_smooth_basicOpen_iso R R' _ _ _ X H.toScheme π (H.ι ≫ G'.hom) (by rw [hX, Category.assoc]) C' _ _ _ _ C j l hl hP hjs hls f g hf₁ hf₂
    hsm q hfq hg

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesSectionsOfThetaSymmetricFunctionsNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.GenSym

theorem polFib_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {g : ℕ} {R R' : Type}
    [CommRing R] [CommRing R'] {x : Sp R ⟶ S} (i : R →+* R') (h : PolFib G L g x) : PolFib G L g (spMap i ≫ x) := by
  obtain ⟨P, α, hg, hα, hPL⟩ := h
  obtain ⟨P', ψ, hg', hψ, hPL'⟩ := exists_isPolFibre polBaseChange_holds i P
  refine ⟨P', ψ ≫ α, hg'.trans hg, hψ.comp hα, ?_⟩
  exact LBIso.trans P'.isLB (pull_isLB P.isLB ψ) (pull_isLB hL _) hPL'.symm
    (LBIso.trans (pull_isLB P.isLB ψ) (pull_isLB (pull_isLB hL α) ψ) (pull_isLB hL _)
      (RigidBundleGlue.LBIso.pull hPL ψ) (GlobalTheory.UMin.FibMove.lbIso_pull_comp hL α ψ).symm)

theorem isGenSec_of_symAt : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω]
    (x : Sp Ω ⟶ S) (θ : SecAt G L x) (e : Fin N → Ω), Odd m → N = m ^ (4 * g) → PolFib G L g x →
    SymAt G L ρ m x θ e → (∃ j, e j ≠ 0) → IsGenSec G L ((1 : ℕ) : ℤ) θ := by
  intro S G _ _ L ρ hL hρ g m N Ω _ _ x θ e hm hN hpol hsym hne
  obtain ⟨⟨θ₁, h₁⟩, -⟩ := GlobalTheory.UMin.gen_of_polFib S G L hL g Ω x hpol
  obtain ⟨r, hr⟩ := (isGenSec_iff θ₁).1 h₁ (SecM.ofSec G θ)
  obtain ⟨a, rfl⟩ := (fnR x).surjective r
  by_cases ha : a = 0
  · exfalso
    subst ha
    let K := AlgebraicClosure Ω
    let i : Ω →+* K := algebraMap Ω K
    have hpol' : PolFib G L g (spMap i ≫ x) := polFib_base hL i hpol
    have hmK : (m : K) ≠ 0 := by
      have : m ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hm)
      exact_mod_cast this
    obtain ⟨pt, c, hl⟩ := _root_.GlobalTheory.UMin.exists_thList S G L ρ hL hρ g m N K (spMap i ≫ x) (SecAt.pull G L θ₁ i) hm hmK hN hpol'
    have h0 : SecM.ofSec G (SecAt.pull G L θ i) = (0 : Γ((Over.mk (spMap i ≫ x)).left, ⊤)) •
        SecM.ofSec G (SecAt.pull G L θ₁ i) := by
      have q := congrArg (pl i rfl) hr
      rw [pl_smul, map_zero, map_zero, pl_ofSec, pl_ofSec] at q
      exact q
    have hl' : ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun b => 0 * c b) := by
      refine ⟨hl.1, fun b => ?_, hl.2.2⟩
      have q := ThG.smul hL h0 (hl.2.1 b)
      simpa using q
    obtain ⟨j, hj⟩ := hne
    have q := hsym K i pt _ hl' j
    rw [(GlobalTheory.UMin.symTup_basic).1 K N c 0 j, zero_pow (Nat.factorial_ne_zero N), zero_mul] at q
    exact hj (i.injective (q.trans (map_zero i).symm))
  · refine (isGenSec_iff θ).2 fun s => ?_
    obtain ⟨r', hr'⟩ := (isGenSec_iff θ₁).1 h₁ s
    refine ⟨r' * fnR x a⁻¹, ?_⟩
    rw [hr', hr, smul_smul, _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, _root_.mul_one]

end GlobalTheory.UMin.GenSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTorusInvariantOfMultiplicative
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.HomMum

open GlobalTheory.EndRosati

theorem prod_psum_eq_one {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (x y : T ⟶ A)
    (hxy : x = 1 ∨ y = 1) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum A ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I => h (psum A ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    fun _ => rfl).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum A ![x, y] ∅ = 1 := rfl
  have p₁ : psum A ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum A ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum A ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  rcases hxy with rfl | rfl
  · rw [_root_.one_mul y, inv_mul_cancel, _root_.mul_one, mul_inv_cancel]
  · rw [_root_.mul_one x, mul_left_comm (h x.left)⁻¹, inv_mul_cancel, _root_.mul_one, mul_inv_cancel]

theorem prod_mφ_eq_one {S : Scheme.{0}} {H₁ H₂ T : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]
    (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (x y : T ⟶ H₁) (hxy : x = 1 ∨ y = 1) {U : Type} [CommGroup U]
    (h : (T.left ⟶ H₁.left ⨿ H₂.left) → U) :
    ∏ k, h ((lift x y).left ≫ mφ H₁ H₂ a b k) ^ mε k = 1 := by
  simp only [mφ_comp]
  rw [Fintype.prod_sum_type]
  have e₁ := prod_psum_eq_one (x ≫ a) (y ≫ b)
    (hxy.imp (fun e => by rw [e, MonObj.one_comp]) (fun e => by rw [e, MonObj.one_comp]))
    (fun q => h (q ≫ coprod.inr))
  have e₂ := prod_psum_eq_one x y hxy (fun q => h (q ≫ coprod.inl))
  simp only [Sum.elim_inl, Sum.elim_inr, mε, zpow_neg, Finset.prod_inv_distrib]
  rw [e₁, e₂, inv_one, _root_.mul_one]

theorem push_pG_two {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I}
    {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
    [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f : G₁ ⟶ G₂}
    {a : D₁.toPre.P.A ⟶ D₂.toPre.P.A}
    (hf : (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map a) :
    push (U₂.gt e).pG ((Over.pullback (thick R I e)).map f) = (U₁.gt e).pG ≫ a := by
  rw [push, GtCoord.pG, GtCoord.pG, ← Functor.map_comp_assoc, hf, Functor.map_comp_assoc, Category.assoc]
  exact congrArg _ (push_fstG e a)


set_option maxHeartbeats 1600000 in
theorem gen_invariant_of_mul : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ [ConnectedSpace (thickObj R I e G₁).left] (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y : T ⟶ thickObj R I e G₁, (Over.map (thick R I e)).map x ≫ (U₁.gt e).pG = 1 → val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧ val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J) → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg _ v hv hm
  have := (U₁.gt e).q_hom
  have := (U₁.gt e).i_hom
  have hM := jn_isLB D₁.toPre D₂.toPre
  have ti : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (t : Z ⟶ splitTorus _ D₁.toPre.X),
      push (U₁.gt e).pG (t ≫ (U₁.gt e).i) = 1 := fun t =>
    (TorusCoord.im_congr (U₁.gt e) (x' := 1) (by
      rw [Category.assoc, (U₁.gt e).isKernel.w, MonObj.one_comp, comp_toUnit_assoc, Hom.one_def])).trans
      (TorusCoord.im_one (U₁.gt e))
  have unit : ∀ {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x y : T ⟶ thickObj R I e G₁),
      push (U₁.gt e).pG x = 1 ∨ push (U₁.gt e).pG y = 1 → ∃ ρ : Γ(T.left, ⊤)ˣ,
        ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (r : Z ⟶ T) (z : Z.left) (J),
          Good (JN D₁.toPre D₂.toPre) z J →
          gm r.left z ⊤ ρ = val v (lift (r ≫ x) (r ≫ y)).left z J := fun x y hxy => by
    obtain ⟨ρ, hρ⟩ := exists_unit_of_formal hM (fun V _ h =>
      (Finset.prod_congr rfl fun k _ => congrArg (h · ^ mε k) (mφ_push (U₁.gt e).pG (U₂.gt e).pG
        (TorusCoord.im_mul (U₁.gt e)) (TorusCoord.im_mul (U₂.gt e)) (push_pG_two U₁ U₂ e hf)
        (push_pG_two U₁ U₂ e hg) x y k).symm).trans
        (prod_mφ_eq_one fB gB (push (U₁.gt e).pG x) (push (U₁.gt e).pG y) hxy h))
      (LB.pullGen (JN D₁.toPre D₂.toPre) _ _ v (lift x y).left) (DVR.pullGen_isGen _ _ _ _ hv _)
    refine ⟨ρ, fun Z r z J hJ => (hρ _ r.left z J hJ).symm.trans ((val_pull hJ _ _ _).trans ?_)⟩
    rw [← Over.comp_left, comp_lift]
  have one : ∀ (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (z : T.left) (J),
      Good (JN D₁.toPre D₂.toPre) z J →
      ∀ y : T ⟶ thickObj R I e G₁, val v (lift 1 y).left z J = 1 ∧ val v (lift y 1).left z J = 1 :=
    fun T z J hJ y => by
      have := hm T z J hJ 1 1 y (TorusCoord.im_one (U₁.gt e))
      rw [_root_.mul_one] at this
      exact ⟨left_eq_mul.1 this.1, left_eq_mul.1 this.2⟩
  have gd : ∀ {Z : Scheme.{0}} (z : Z), ∃ J, Good (JN D₁.toPre D₂.toPre) z J := fun {Z} z => by
    choose J hJ using fun χ : Z ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left => Geo.Tor.exists_chart hM (χ z)
    exact ⟨J, hJ⟩
  obtain ⟨ρ₁, h₁⟩ := unit (fst (splitTorus _ D₁.toPre.X) (thickObj R I e G₁) ≫ (U₁.gt e).i) (snd _ _) (Or.inl (ti _))
  obtain ⟨ρ₂, h₂⟩ := unit (snd _ _) (fst (splitTorus _ D₁.toPre.X) (thickObj R I e G₁) ≫ (U₁.gt e).i) (Or.inr (ti _))
  have e₁ := fun Z t y z J hJ => h₁ Z (lift t y) z J hJ
  have e₂ := fun Z t y z J hJ => h₂ Z (lift t y) z J hJ
  simp only [lift_fst_assoc, lift_snd] at e₁ e₂
  have k₁ := fun Z t y z => unit_eq_one ρ₁ (fun Z t t' y z => by
      obtain ⟨J, hJ⟩ := gd z
      rw [e₁ Z _ y z J hJ, e₁ Z _ y z J hJ, e₁ Z _ y z J hJ, MonObj.mul_comp]
      exact (hm Z z J hJ _ _ y (ti t)).1) (fun Z t z => by
      obtain ⟨J, hJ⟩ := gd z
      exact (e₁ Z t 1 z J hJ).trans (one Z z J hJ _).2) (Z := Z) t y z
  have k₂ := fun Z t y z => unit_eq_one ρ₂ (fun Z t t' y z => by
      obtain ⟨J, hJ⟩ := gd z
      rw [e₂ Z _ y z J hJ, e₂ Z _ y z J hJ, e₂ Z _ y z J hJ, MonObj.mul_comp]
      exact (hm Z z J hJ _ _ y (ti t)).2) (fun Z t z => by
      obtain ⟨J, hJ⟩ := gd z
      exact (e₂ Z t 1 z J hJ).trans (one Z z J hJ _).1) (Z := Z) t y z
  intro T z J hJ x x' y y' hx hy
  obtain ⟨t, rfl⟩ := TorusCoord.exists_torus (U₁.gt e) x x' hx
  obtain ⟨t', rfl⟩ := TorusCoord.exists_torus (U₁.gt e) y y' hy
  rw [(hm T z J hJ _ x' _ (ti t)).1, (hm T z J hJ _ y' x' (ti t')).2, ← e₁ T t _ z J hJ, ← e₂ T t' _ z J hJ, k₁, k₂,
    _root_.one_mul, _root_.one_mul]

end GlobalTheory.HomMum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointAbelianPartLiesUnderClassZeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricTorsionPoint_abelianPart_lies_under_classZero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (N : ℕ), 1 ≤ N → ∀ β : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A, β ^ N = 1 → ∃ xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, xb ^ N = 1 ∧ (∃ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 ∧ QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb) ∧ ∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 → QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb → p.g.b = β := by
  first | exact @GlobalTheory.Poinc.IntTerm.torsion_lies_under | exact GlobalTheory.Poinc.IntTerm.torsion_lies_under | (intros; apply GlobalTheory.Poinc.IntTerm.torsion_lies_under <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointGenericFibreMemberHasLabelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricTorsionPoint_genericFibre_member_has_label : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), xb ^ (X₁.S.r * X₁.S.N) = 1 → ∃ a : X₁.S.Gam, xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left := by
  first | exact @GlobalTheory.Poinc.IntTerm.torsion_has_label | exact GlobalTheory.Poinc.IntTerm.torsion_has_label | (intros; apply GlobalTheory.Poinc.IntTerm.torsion_has_label <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjSmoothOfGeometricallyReduced
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem grpObj_smooth_of_geometricallyReduced : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G], LocallyOfFiniteType G.hom → GeometricallyReduced G.hom → Smooth G.hom := by
  intro K _ G _ h1 h2
  letI : GrpObj (Over.mk G.hom) := ‹GrpObj G›
  exact smooth_of_grpObj (f := G.hom)

end GlobalTheory
end

