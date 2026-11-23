module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1993
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteExtensionClassicalPointFactors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TraitExtLab

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (u' : Sp S.R ⟶ F.X) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → ∃ (T' : Trait F) (ι' : FractionRing T'.V →+* PadicAlgCl p) (yK : S.R →+* FractionRing T'.V) (e : T'.D.toPre.X ≃+ T.D.toPre.X) (k : ℕ), (∀ x, ‖ι' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V (FractionRing T'.V))) ∧ ι'.comp yK = y₀ ∧ spMap yK ≫ u' = T'.y ∧ ‖ι (algebraMap T.V _ T.ϖ)‖ = ‖ι' (algebraMap T'.V _ T'.ϖ)‖ ^ k ∧ ∀ a b, T'.β a b = k * T.β (e a) (e b) := by
  intro g n F o Ω _ _ _ _ S u' p _ y₀ T ι hι hy
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (o := o) (Ω := Ω)
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  haveI : Algebra.FiniteType ℤ S.R := Algebra.FiniteType.trans (S := o) inferInstance inferInstance
  have hQ := _root_.GlobalTheory.PadicUnitBall.padic_mem_range p T.V T.complete ι hι
  obtain ⟨W, _, _, _, hWc, _, fV, fK, κ, hfV, hfVl, -, hfK, hκι, hκ, hy₀⟩ :=
    _root_.GlobalTheory.DvrFinExt.exists_finite_extension p T.V T.complete ι hι hQ S.R y₀
  have hbase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T', f, gK, hf, hfl, hff, hgK, hTy⟩ :=
    traitExtSt g n _ (zetaAway n) F W hbase inferInstance (spMap fK ≫ T.y)
  letI : Algebra (FractionRing W) (FractionRing T'.V) := gK.toAlgebra
  letI : Algebra W T'.V := f.toAlgebra
  haveI : Module.Finite W T'.V := hff
  haveI : Algebra.IsIntegral W T'.V := Algebra.IsIntegral.of_finite W T'.V
  haveI : IsLocalHom (algebraMap W T'.V) := hfl
  have hcomp : (algebraMap (FractionRing W) (FractionRing T'.V)).comp (algebraMap W (FractionRing W)) =
      (algebraMap T'.V (FractionRing T'.V)).comp (algebraMap W T'.V) := RingHom.ext hgK
  have hI : ∀ a : T'.V, _root_.IsIntegral (FractionRing W) (algebraMap T'.V (FractionRing T'.V) a) := fun a =>
    IsIntegral.map_of_comp_eq (algebraMap W (FractionRing W)) (algebraMap T'.V (FractionRing T'.V)) hcomp
      (Algebra.IsIntegral.isIntegral a)
  haveI : Algebra.IsAlgebraic (FractionRing W) (FractionRing T'.V) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := T'.V) x
    rw [div_eq_mul_inv]
    exact (hI a).isAlgebraic.mul (hI b).isAlgebraic.inv⟩
  letI : Algebra (FractionRing W) (PadicAlgCl p) := κ.toAlgebra
  let ιA : FractionRing T'.V →ₐ[FractionRing W] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ι' : FractionRing T'.V →+* PadicAlgCl p := ιA
  have hι'κ : ι'.comp gK = κ := ιA.comp_algebraMap
  have hint := GlobalTheory.unitBall_eq_of_integral_dvr p W T'.V hf κ ι' (fun v => by
    show ι' (algebraMap T'.V (FractionRing T'.V) (f v)) = _
    rw [← hgK]
    exact congrArg (fun h : FractionRing W →+* PadicAlgCl p => h (algebraMap W (FractionRing W) v)) hι'κ) hκ
  have hιc : ι'.comp (gK.comp fK) = ι := by rw [← RingHom.comp_assoc, hι'κ, hκι]

  have hr : ∀ a, y₀ a ∈ ι'.range := fun a => by
    obtain ⟨x, hx⟩ := hy₀ a
    exact ⟨gK x, by rw [← hx, ← hι'κ]; rfl⟩
  let eι : FractionRing T'.V ≃+* ι'.range := RingEquiv.ofBijective ι'.rangeRestrict
    ⟨fun a b hab => ι'.injective (congrArg Subtype.val hab), ι'.rangeRestrict_surjective⟩
  let yK : S.R →+* FractionRing T'.V := eι.symm.toRingHom.comp (y₀.codRestrict ι'.range hr)
  have hyK : ι'.comp yK = y₀ := RingHom.ext fun a =>
    congrArg Subtype.val (eι.apply_symm_apply (y₀.codRestrict ι'.range hr a))

  have hne : f (fV T.ϖ) ≠ 0 := fun h => T.irr.ne_zero (hfV (hf (by rw [h, map_zero, map_zero])))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T'.irr
  have hbase' : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, T'.complete⟩, inferInstance⟩
  haveI : IsLocalHom (f.comp fV) := by
    haveI : IsLocalHom f := hfl
    haveI : IsLocalHom fV := hfVl
    exact RingHom.isLocalHom_comp f fV
  obtain ⟨e₀, he₀⟩ := TraitUniq.traitUniq g n _ (zetaAway n) F T T' T'.V (f.comp fV) (RingHom.id _) (gK.comp fK)
    (RingHom.id _) hbase' inferInstance (hf.comp hfV) Function.injective_id inferInstance inferInstance
    (fun a => by simp only [RingHom.comp_apply, hfK, hgK]) (fun a => rfl)
    (by rw [hTy, spMap_comp', Category.assoc]; rw [show spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ from Spec.map_id _, Category.id_comp])
    T'.ϖ m 1 T'.irr hm (by rw [pow_one, RingHom.id_apply])
  refine ⟨T', ι', yK, e₀.symm, m, hint, hyK, ?_, ?_, ?_⟩
  · haveI : Epi (spMap ι') := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (spMap ι'), ← Category.assoc, ← spMap_comp', hyK, hy, hTy, ← hιc, spMap_comp', spMap_comp',
      Category.assoc, Category.assoc]
  · obtain ⟨u, hu⟩ := hm
    have hunit : ∀ w : T'.Vˣ, ‖ι' (algebraMap T'.V _ (w : T'.V))‖ = 1 := fun w => by
      have h1 := (hint _).2 ⟨(w : T'.V), rfl⟩
      have h2 := (hint _).2 ⟨((w⁻¹ : T'.Vˣ) : T'.V), rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (w : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (w : T'.V))),
        norm_nonneg (ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V)))]
    have e1 : ι (algebraMap T.V _ T.ϖ) = ι' (algebraMap T'.V _ (f (fV T.ϖ))) := by
      rw [← hιc, RingHom.comp_apply, RingHom.comp_apply, hfK, hgK]
    have e2 : f (fV T.ϖ) = T'.ϖ ^ m * ((u⁻¹ : T'.Vˣ) : T'.V) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e1, e2, map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]
  · intro a b
    have h := he₀ (e₀.symm a) (e₀.symm b)
    simp only [AddEquiv.apply_symm_apply, Nat.cast_one, one_mul] at h
    exact h.symm

end GlobalTheory.TraitExtLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftThetaSetupModelAfterExtension
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitLift

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem mem_of_closedPoint {Y : Scheme.{0}} (U : Set Y) (hU : IsOpen U) (V : Type) [CommRing V] [IsLocalRing V]
    (ξ : Sp V ⟶ Y) (h : ξ (closedPoint V) ∈ U) (x : Sp V) : ξ x ∈ U := by
  have hs : x ⤳ closedPoint V := IsLocalRing.specializes_closedPoint x
  exact (hs.map ξ.continuous).mem_open hU h

theorem exists_finite_point {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] (K : Type) [Field K] (x : Sp K ⟶ Y)
    (hx : x (closedPoint K) ∈ Set.range π) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (η : Sp L ⟶ X),
      η ≫ π = spMap (algebraMap K L) ≫ x := by
  obtain ⟨p, hp⟩ := hx
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of K) (S := S) (e.hom ≫ pullback.snd π x)
  letI : Algebra K S := f.hom.toAlgebra
  have hsp : spMap (algebraMap K S) = e.hom ≫ pullback.snd π x := hf
  have hfin : Module.Finite K S := by
    have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (closedPoint K) hp
  haveI : Nontrivial S := (e.inv z).nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional K (S ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  refine ⟨S ⧸ m, inferInstance, inferInstance, inferInstance, spMap (Ideal.Quotient.mk m) ≫ e.hom ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.hom, ← hsp, ← Category.assoc, spMap_comp']

theorem exists_lift_of_isFinite {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] (R : Type) [CommRing R] [IsDomain R]
    [ValuationRing R] (η : Sp (FractionRing R) ⟶ X) (ξ : Sp R ⟶ Y) (h : η ≫ π = jK R ≫ ξ) :
    ∃ l : Sp R ⟶ X, l ≫ π = ξ ∧ jK R ≫ l = η := by
  have hUC : UniversallyClosed π := inferInstance
  have h2 : (ValuativeCriterion.Existence ⊓ @QuasiCompact) π := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; exact hUC
  let S : ValuativeCommSq π :=
    { R := R, K := FractionRing R, i₁ := η, i₂ := ξ, commSq := ⟨h⟩ }
  obtain ⟨l⟩ := (h2.1 S).exists_lift
  exact ⟨l.l, l.fac_right, l.fac_left⟩

end GlobalTheory.Poinc.TraitLift

namespace GlobalTheory.Poinc.TraitLift

theorem exists_closure (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (L : Type) [Field L] [Algebra (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] :
    ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsLocalRing V₂) (j : V →+* V₂) (e : L →+* FractionRing V₂),
      GlobalTheory.Mum.Base V₂ ∧ IsDiscreteValuationRing V₂ ∧ Function.Injective j ∧ IsLocalHom j ∧
        ∀ a : V, e (algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a)) =
          algebraMap V₂ (FractionRing V₂) (j a) := by
  letI : Algebra V L := ((algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite V (integralClosure V L) := GlobalTheory.FormalIsogeny.finite_integralClosure V (FractionRing V) L
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful V (FractionRing V) L
  haveI hloc : IsLocalRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalRing V L
  haveI hdvr : IsDiscreteValuationRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V (FractionRing V) L
  haveI : IsFractionRing (integralClosure V L) L := integralClosure.isFractionRing_of_finite_extension (FractionRing V) L
  have hj := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj V L
  haveI : CharZero (integralClosure V L) := charZero_of_injective_algebraMap hj
  refine ⟨integralClosure V L, inferInstance, inferInstance, hloc, algebraMap V (integralClosure V L),
    (FractionRing.algEquiv (integralClosure V L) L).symm.toRingEquiv.toRingHom,
    ⟨⟨inferInstance, inferInstance, inferInstance,
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V (integralClosure V L)⟩, inferInstance⟩,
    hdvr, hj, ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom V L, fun a => ?_⟩
  have h1 : algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a) =
      algebraMap (integralClosure V L) L (algebraMap V (integralClosure V L) a) := rfl
  rw [h1]
  exact (FractionRing.algEquiv (integralClosure V L) L).symm.commutes _

end GlobalTheory.Poinc.TraitLift

namespace GlobalTheory.Poinc


open GlobalTheory.Poinc.TraitLift in
theorem exists_trait_lift_setup (hExt : TraitExtSt) : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i), IsClopen (Set.range X₁.π) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ jK T'.V ≫ ξ₁ ≫ X₁.π = T'.y ≫ i := by
  intro g n F Z i W8 X₁ hcl T ξ hξ hc
  haveI : IsFinite X₁.π := X₁.fin
  have hgen : (jK T.V ≫ ξ) (closedPoint (FractionRing T.V)) ∈ Set.range X₁.π := by
    exact mem_of_closedPoint _ hcl.isOpen T.V ξ hc _
  obtain ⟨L, _, _, _, η, hη⟩ := exists_finite_point X₁.π (FractionRing T.V) (jK T.V ≫ ξ) hgen
  haveI := T.complete
  obtain ⟨V₂, _, _, _, j, e, hB, hD, hj, hjl, he⟩ := exists_closure T.V L
  have hring : (algebraMap V₂ (FractionRing V₂)).comp j =
      (e.comp (algebraMap (FractionRing T.V) L)).comp (algebraMap T.V (FractionRing T.V)) :=
    RingHom.ext fun a => (he a).symm
  haveI : ValuationRing V₂ := inferInstance
  have hsq : (spMap e ≫ η) ≫ X₁.π = jK V₂ ≫ (spMap j ≫ ξ) := by
    rw [Category.assoc, hη, ← Category.assoc, spMap_comp', ← Category.assoc, ← Category.assoc, spMap_comp',
      show jK V₂ = spMap (algebraMap V₂ (FractionRing V₂)) from rfl, spMap_comp', hring]
  obtain ⟨l, hl1, -⟩ := exists_lift_of_isFinite X₁.π V₂ (spMap e ≫ η) (spMap j ≫ ξ) hsq
  obtain ⟨T', f'', fK'', hinj'', hloc'', -, hc'', hy''⟩ := hExt g n _ (zetaAway n) F V₂ hB hD
    (spMap (e.comp (algebraMap (FractionRing T.V) L)) ≫ T.y)
  have hring2 : (algebraMap T'.V (FractionRing T'.V)).comp (f''.comp j) =
      (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))).comp (algebraMap T.V (FractionRing T.V)) := by
    ext a
    simp only [RingHom.comp_apply]
    rw [← hc'', ← he]
  have key : jK T'.V ≫ spMap (f''.comp j) = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V := by
    rw [show jK T'.V = spMap (algebraMap T'.V (FractionRing T'.V)) from rfl,
      show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl, spMap_comp', spMap_comp', hring2]
  haveI := hloc''
  refine ⟨T', f''.comp j, fK''.comp (e.comp (algebraMap (FractionRing T.V) L)), spMap f'' ≫ l, hinj''.comp hj,
    inferInstance, fun a => (RingHom.congr_fun hring2 a).symm, ?_, ?_, ?_⟩
  · rw [hy'', ← Category.assoc, spMap_comp']
  · rw [Category.assoc, hl1, ← Category.assoc, spMap_comp']
  · calc jK T'.V ≫ (spMap f'' ≫ l) ≫ X₁.π = jK T'.V ≫ spMap (f''.comp j) ≫ ξ := by
          rw [Category.assoc, hl1, ← spMap_comp', Category.assoc]
      _ = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V ≫ ξ := by
          rw [← Category.assoc, key, Category.assoc]
      _ = T'.y ≫ i := by
          rw [hξ, hy'', ← spMap_comp']
          simp only [Category.assoc]

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem traitLift_setup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i), IsClopen (Set.range X₁.π) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ jK T'.V ≫ ξ₁ ≫ X₁.π = T'.y ≫ i :=
  exists_trait_lift_setup _root_.GlobalTheory.Poinc.traitExtSt

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePreconnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ZariskiConn

theorem fibre_preconnected : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsProper π] [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ U : Z.Opens, (U : Set Z).Nonempty → IsIso (π ∣_ U) → ∀ z : Z, _root_.IsPreconnected (π.base ⁻¹' {z}) := by
  intro Y Z π _ _ _ _ hN U hU hiso z
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  have hS := _root_.GlobalTheory.ZariskiSections.bijective_appTop_restrict Y Z π hN U hU hiso V hV
  haveI : IsAffine (V : Scheme) := hV
  have hC := _root_.GlobalTheory.ZariskiConn.isPreconnected_fibre (V : Scheme) (π ⁻¹ᵁ V) (π ∣_ V) hS ⟨z, hzV⟩
  have key : π.base ⁻¹' {z} = (π ⁻¹ᵁ V).ι.base '' ((π ∣_ V).base ⁻¹' {⟨z, hzV⟩}) := by
    ext y
    constructor
    · intro hy
      have hy' : π.base y = z := hy
      have hyV : y ∈ π ⁻¹ᵁ V := by
        show π.base y ∈ V
        rw [hy']; exact hzV
      refine ⟨⟨y, hyV⟩, ?_, rfl⟩
      show (π ∣_ V).base ⟨y, hyV⟩ = ⟨z, hzV⟩
      exact Subtype.ext ((morphismRestrict_base_coe π V ⟨y, hyV⟩).trans hy')
    · rintro ⟨w, hw, rfl⟩
      have hw' : (π ∣_ V).base w = ⟨z, hzV⟩ := hw
      exact (morphismRestrict_base_coe π V w).symm.trans (congrArg Subtype.val hw')
  rw [key]
  exact hC.image _ (π ⁻¹ᵁ V).ι.base.hom.continuous.continuousOn

end GlobalTheory.ZariskiConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassNumberCentraliserTorusSeparable
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls

theorem exists_finset_cosets {A : Type} [Group A] (U₀ U : Subgroup A) (h : U.relIndex U₀ ≠ 0) :
    ∃ F : Finset A, ∀ u ∈ U₀, ∃ f ∈ F, f ∈ U₀ ∧ ∃ v ∈ U, u = f * v := by
  haveI : (U.subgroupOf U₀).FiniteIndex := ⟨h⟩
  haveI : Finite (U₀ ⧸ U.subgroupOf U₀) := Subgroup.finite_quotient_of_finiteIndex
  haveI := Fintype.ofFinite (U₀ ⧸ U.subgroupOf U₀)
  refine ⟨Finset.univ.image (fun q : U₀ ⧸ U.subgroupOf U₀ => ((q.out : U₀) : A)), ?_⟩
  intro u hu
  set q : U₀ ⧸ U.subgroupOf U₀ := QuotientGroup.mk ⟨u, hu⟩
  refine ⟨((q.out : U₀) : A), Finset.mem_image_of_mem _ (Finset.mem_univ _), (q.out).2,
    ((q.out : U₀) : A)⁻¹ * u, ?_, by group⟩
  have h1 : (q.out)⁻¹ * ⟨u, hu⟩ ∈ U.subgroupOf U₀ := QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

end GlobalTheory.CentCls

namespace GlobalTheory.CentCls

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → ∀ (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∀ r : G.GAf × Gr G 1, ∃ R : Finset (G.GAf × Gr G 1), ∀ c : G.GAf × Gr G 1, c * (toAfF G β x t hx y₀, toP1 G β y₀) = (toAfF G β x t hx y₀, toP1 G β y₀) * c → ∃ y : grp G β, y * y₀ = y₀ * y ∧ ∃ s ∈ R, ∃ k : G.GAf × Gr G 1, k.1 ∈ L.K.toSubgroup ∧ k.2 ∈ K' ∧ c * r = (toAfF G β x t hx y, toP1 G β y) * s * k := by
  intro p hp G L K' hK' β x t hx hsh y₀ _ _ r
  obtain ⟨r₁, r₂⟩ := r
  obtain ⟨F₂, hF₂⟩ := exists_finset_cosets (KHT p G.m G.n 1 G.Fw) K' hK'.1.relIndex_ne_zero
  let ι : G.GAf →* (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ :=
    { toFun := fun g => g, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let U₁ : Subgroup ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :=
    ((L.K.toSubgroup.map (MulAut.conj r₁).toMonoidHom).map ι).comap (psiAway G x)
  let U₂ : Subgroup ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ) :=
    ((KHT p G.m G.n 1 G.Fw).map (MulAut.conj r₂).toMonoidHom).comap (psiP G)
  obtain ⟨O₁, hO₁, h1O₁, hO₁K⟩ :=
    exists_open_psiAway_mem_conj_level p G L β x t hx (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) r₁
  obtain ⟨O₂, hO₂, h1O₂, hO₂K⟩ := GlobalTheory.T.psi_p_neighborhood_in_level_subgroup p G r₂
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  obtain ⟨S, hS⟩ := GlobalTheory.T.similitudeCentraliser_classNumber_finite_borel G.C G.star (β : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) p
    (U₁.prod U₂) ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, ⟨h1O₁, h1O₂⟩,
      fun z hz hT1 _ => Subgroup.mem_prod.mpr ⟨by
        obtain ⟨k, hk, hk'⟩ := hO₁K z.1 hz.1 hT1
        exact Subgroup.mem_comap.mpr
          (Subgroup.mem_map.mpr ⟨r₁ * k * r₁⁻¹, Subgroup.mem_map.mpr ⟨k, hk, rfl⟩, hk'⟩), by
        have h2 := hO₂K z.2 hz.2
        refine Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨r₂⁻¹ * psiP G z.2 * r₂, h2, ?_⟩)
        show r₂ * (r₂⁻¹ * psiP G z.2 * r₂) * r₂⁻¹ = psiP G z.2
        group⟩⟩
  let Pf : G.Cˣ × ℚˣ → Prop := fun e =>
    (e.1 : G.C) * β * MulOpposite.unop (G.star e.1) = algebraMap ℚ G.C e.2 * β ∧
      Commute (e.1 : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
  let e₀ : G.Cˣ × ℚˣ := if h : ∃ e, Pf e ∧ (e.2 : ℚ) < 0 then h.choose else 1
  let S' := S ∪ S.image (fun s => dg G.C p e₀ * s)
  let gOf : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ → G.GAf := fun w =>
    if h : ∃ g : G.GAf, (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w then h.choose else 1
  have hgOf : ∀ w (g : G.GAf), (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w →
      ((gOf w : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w := by
    intro w g hg
    have h : ∃ g : G.GAf, (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = w := ⟨g, hg⟩
    simp only [gOf, dif_pos h]
    exact h.choose_spec
  refine ⟨(S' ×ˢ F₂).image (fun q => (gOf (psiAway G x q.1.1) * r₁, psiP G q.1.2 * r₂ * q.2)), ?_⟩
  intro c hc
  obtain ⟨c₁, c₂⟩ := c
  have hc1 : c₁ * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c₁ := congrArg Prod.fst hc
  have hc2 : c₂ * toP1 G β y₀ = toP1 G β y₀ * c₂ := congrArg Prod.snd hc
  have hz₁ := inT_psiAway_inv_of_commute p G β x t hx y₀ c₁ hc1
  obtain ⟨z₂, hz₂, hz₂c⟩ := _root_.GlobalTheory.TorCls.centraliser_at_p p G β hsh y₀ c₂ hc2
  obtain ⟨γ, hγf, hγc, s, hs, u, hu, hz⟩ := hS (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), z₂) hz₁ hz₂
  obtain ⟨γ', ⟨hγ'f, hγ'c⟩, hγ'pos, s', hs', hds⟩ : ∃ γ' : G.Cˣ × ℚˣ, Pf γ' ∧ (0 : ℚ) < (γ'.2 : ℚ) ∧
      ∃ s' ∈ S', dg G.C p γ * s = dg G.C p γ' * s' := by
    rcases lt_or_gt_of_ne (Units.ne_zero γ.2) with hneg | hpos
    · have hex : ∃ e, Pf e ∧ (e.2 : ℚ) < 0 := ⟨γ, ⟨hγf, hγc⟩, hneg⟩
      have he₀ : e₀ = hex.choose := by simp only [e₀, dif_pos hex]
      obtain ⟨⟨he1, he2⟩, he3⟩ := hex.choose_spec
      refine ⟨γ * e₀⁻¹, ⟨?_, ?_⟩, ?_, dg G.C p e₀ * s,
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs), ?_⟩
      · rw [he₀]
        exact form_mul_inv G.star (β : G.C) γ.1 hex.choose.1 γ.2 hex.choose.2 hγf he1
      · rw [he₀]
        show Commute ((γ.1 * hex.choose.1⁻¹ : G.Cˣ) : G.C) _
        rw [Units.val_mul]
        exact hγc.mul_left he2.units_inv_left
      · rw [he₀]
        show (0 : ℚ) < ((γ.2 * hex.choose.2⁻¹ : ℚˣ) : ℚ)
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
        exact mul_pos_of_neg_of_neg hneg (inv_lt_zero.mpr he3)
      · rw [map_mul, map_inv]
        group
    · exact ⟨γ, ⟨hγf, hγc⟩, hpos, s, Finset.mem_union_left _ hs, rfl⟩
  let y : grp G β := ⟨γ', hγ'f, hγ'pos⟩
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_prod.mp hu
  obtain ⟨g, hg1, hg⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu1)
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg1
  obtain ⟨k₂, hk₂, hk₂e⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu2)
  obtain ⟨f, hf, -, v, hv, hkv⟩ := hF₂ k₂ hk₂
  have hz' : (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), z₂) = dg G.C p γ' * s' * u := by
    rw [hz, hds]
  have hz1 := congrArg Prod.fst hz'
  have hz2 := congrArg Prod.snd hz'
  simp only [Prod.fst_mul, Prod.snd_mul] at hz1 hz2
  have hc₁ : (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      psiAway G x (psiAway G x⁻¹ (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    simp [psiAway_apply, mul_assoc]
  have e1 : psiAway G x (dg G.C p γ').1 = ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :=
    (toAfF_eq_psiAway G β x t hx y).symm
  rw [hz1, map_mul, map_mul, e1, ← hg] at hc₁
  have hs1 : ((gOf (psiAway G x s'.1) : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = psiAway G x s'.1 := by
    refine hgOf _ ((toAfF G β x t hx y)⁻¹ * c₁ * g⁻¹) ?_
    show ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)⁻¹ *
      (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) * (ι g)⁻¹ = _
    rw [hc₁]
    group
  have hc₁' : c₁ = toAfF G β x t hx y * gOf (psiAway G x s'.1) * g := by
    apply Subtype.ext
    show (c₁ : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) *
      ((gOf (psiAway G x s'.1) : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) * ι g
    rw [hs1]
    exact hc₁
  have e2 : psiP G (dg G.C p γ').2 = toP1 G β y := (formGroupToPadicPointsDegreeOne_eq_unitaryPoints G β y).symm
  have hc₂' : c₂ = toP1 G β y * psiP G s'.2 * (r₂ * k₂ * r₂⁻¹) := by
    rw [← hz₂c, hz2, map_mul, map_mul, e2, ← hk₂e]
    rfl
  have hg' : g = r₁ * k * r₁⁻¹ := hkg.symm
  have hmem : (s', f) ∈ S' ×ˢ F₂ := Finset.mem_product.mpr ⟨hs', hf⟩
  refine ⟨y, Subtype.ext (Prod.ext (Units.ext hγ'c.eq) (mul_comm _ _)), _,
    Finset.mem_image_of_mem _ hmem, (k, v), hk, hv, ?_⟩
  rw [hc₁', hg', hc₂', hkv]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> simp only [Prod.fst_mul, Prod.snd_mul] <;> group

end GlobalTheory.CentCls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFieldPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DualCon.FieldRep

theorem hasRep_field : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ,
    SmoothOfRelativeDimension g A.hom → ∀ (K : Type) [Field K] (s : Sp K ⟶ S), HasRep A g (Over.mk s) := by
  intro S A _ hA g hg K _ s
  have hA' : IsAbelianScheme ((Over.pullback s).obj A) := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hg' : SmoothOfRelativeDimension g ((Over.pullback s).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨L, hL, hamp⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy (_root_.GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K _ hA')
  have hAF : HasRepAF ((Over.pullback s).obj A) g (𝟙_ _) := _root_.GlobalTheory.DualPol.hasRepAF_of_relAmple K _ g hA' hg' L hL hamp
  have h := (GlobalTheory.DualCon.hasRep_baseChange_iff S (Sp K) s A ((Over.pullback s).obj A) (pullback.fst A.hom s)
    (isGrpPullback_pullback A s) g (𝟙_ _)).1.1
  obtain ⟨B, b, P, hR, hG, -⟩ := hAF
  have h2 := h ⟨B, b, P, hR, hG⟩
  have e : (𝟙_ (Over (Sp K))).hom ≫ s = s := Category.id_comp s
  rw [e] at h2
  exact h2

end GlobalTheory.DualCon.FieldRep
end
end

