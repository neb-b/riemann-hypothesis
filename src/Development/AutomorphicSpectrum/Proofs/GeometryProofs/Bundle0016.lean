module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymDivisible
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TraceIntegralSubringExtension

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AntisymmetricPerturbationHolds
section
namespace GlobalTheory.CompanionTheory.Ar.Link

theorem antisymPerturbation_holds : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement :=
  GroundTheory.Heights₂.Heights.AntisymPerturbation.proof
    (GroundTheory.Heights₂.Heights.AntisymStability.proof
      GroundTheory.Heights₂.Heights.AntisymDivisible.proof)

end GlobalTheory.CompanionTheory.Ar.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompat
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem genericBaseChange_ringHom_eq {R : Type} [CommRing R] [IsDomain R]
    {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R'] {B : Type} [CommRing B]
    (i : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R')
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R'))
    (hj : Function.Injective j) (hji : j.comp i = algebraMap R _)
    (hj'i : j'.comp i = (algebraMap R' _).comp (algebraMap R R')) :
    j' = κ.comp j := by
  ext b
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := R) (j b)
  have hs0 : algebraMap R (FractionRing R) s ≠ 0 := by
    simpa using IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FractionRing R) hs
  have e1 : algebraMap R (FractionRing R) s * j b = algebraMap R (FractionRing R) r := by
    rw [← hrs]; field_simp
  have hjs : ∀ x : R, j (i x) = algebraMap R (FractionRing R) x := fun x =>
    RingHom.congr_fun hji x
  have e2 : i s * b = i r := by
    apply hj
    rw [map_mul, hjs, hjs, e1]
  have hj's : ∀ x : R, j' (i x) = κ (algebraMap R (FractionRing R) x) := fun x =>
    (RingHom.congr_fun hj'i x).trans (RingHom.congr_fun hκ x).symm
  have e3 : κ (algebraMap R (FractionRing R) s) * j' b = κ (algebraMap R (FractionRing R) r) := by
    rw [← hj's, ← hj's, ← map_mul, e2]
  have e4 : κ (algebraMap R (FractionRing R) s) * κ (j b) = κ (algebraMap R (FractionRing R) r) := by
    rw [← map_mul, e1]
  have hκs : κ (algebraMap R (FractionRing R) s) ≠ 0 := by
    simpa using hs0
  exact mul_left_cancel₀ hκs (e3.trans e4.symm)

theorem genericPoint_baseChange :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ t, (Γ'.pt t).left ≫ F = Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ t
  obtain ⟨B, _, i, j, j', σ, hj, hji, hj'i, -, hσ, hσ'⟩ := hF.pts
  have hjj : j' = κ.comp j := genericBaseChange_ringHom_eq i j j' κ hκ hj hji hj'i
  rw [← hσ' t, ← hσ t, hjj, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHom
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.Funct

theorem valAt_pullback {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (a : X ⟶ Y)
    (y : Spec (CommRingCat.of B) ⟶ Y) (hy : x ≫ a = y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (h' : ⊤ ≤ x ⁻¹ᵁ (a ⁻¹ᵁ U)) (s : Γ(Y, U)) :
    valAt x (a ⁻¹ᵁ U) h' ((a.app U).hom s) = valAt y U h s := by
  subst hy
  simp only [valAt]
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem regularAt_pullback {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ₁ : QFGroup R T)
    {T' : Type} [CommGroup T'] (Γ₂ : QFGroup R T') (a : Γ₁.G ⟶ Γ₂.G) (α : T →* T')
    (ha : ∀ t, Γ₁.pt t ≫ a = Γ₂.pt (α t)) (φ : T' → FractionRing R) (g : Γ₁.G.left)
    (hg : Γ₂.RegularAt φ (a.left g)) : Γ₁.RegularAt (fun t => φ (α t)) g := by
  obtain ⟨U, hU, s, hs⟩ := hg
  refine ⟨a.left ⁻¹ᵁ U, hU, (a.left.app U).hom s, fun t h => ?_⟩
  have hy : (Γ₁.pt t).left ≫ a.left = (Γ₂.pt (α t)).left := by
    rw [← ha t, Over.comp_left]
  have h₂ : ⊤ ≤ (Γ₂.pt (α t)).left ⁻¹ᵁ U := by
    rw [← hy]
    exact h
  rw [valAt_pullback _ _ _ hy U h₂ h s]
  exact hs (α t) h₂

theorem comp_mem_btOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (T' : Type) [CommGroup T'] [Finite T'] (Γ' : QFGroup R T') (a : Γ.G ⟶ Γ'.G) (α : T →* T'), (∀ t, Γ.pt t ≫ a = Γ'.pt (α t)) → ∀ f ∈ Γ'.btOrder ⊤, (fun t => f (α t)) ∈ Γ.btOrder ⊤ := by
  intro R _ _ T _ _ Γ T' _ _ Γ' a α ha f hf
  let Φ : (T' → R) →ₐ[R] (T → R) :=
    { toFun := fun f t => f (α t)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hle : Γ'.btOrder ⊤ ≤ (Γ.btOrder ⊤).comap Φ := by
    refine Algebra.adjoin_le fun f hf => ?_
    refine Algebra.subset_adjoin fun t g _ => ?_
    have h := regularAt_pullback Γ Γ' a α ha _ g (hf (α t) (a.left g) trivial)
    change Γ.RegularAt (fun x => algebraMap R (FractionRing R) (f (α (t * x)))) g
    simpa only [map_mul] using h
  exact hle hf

end GlobalTheory.CompanionTheory.Ar.BT.Funct
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqTopOfEtale
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.EtaleTop

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem stalk_spec_normal [IsIntegrallyClosed R] (y : Spec (CommRingCat.of R)) :
    IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk y) ∧
      IsIntegrallyClosed ((Spec (CommRingCat.of R)).presheaf.stalk y) := by
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := R) y
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  exact GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain y.asIdeal _

theorem genPt_asIdeal (Γ : QFGroup R T) (t : T) (x : Spec (CommRingCat.of (FractionRing R))) :
    (Γ.G.hom ((Γ.pt t).left x)).asIdeal = ⊥ := by
  have hw : (Γ.pt t).left ≫ Γ.G.hom = (genPt R).hom := Over.w (Γ.pt t)
  have : Γ.G.hom ((Γ.pt t).left x) = (genPt R).hom x := by
    rw [← hw]; rfl
  rw [this]
  show Ideal.comap (algebraMap R (FractionRing R)) x.asIdeal = ⊥
  have hx : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ x.asIdeal x.isPrime
  rw [hx, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))

theorem eq_of_specializes_bot {y z : Spec (CommRingCat.of R)} (h : y ⤳ z) (hz : z.asIdeal = ⊥) :
    y = z := by
  have h' : @LE.le (PrimeSpectrum R) _ y z := (PrimeSpectrum.le_iff_specializes (R := R) y z).2 h
  have h'' : y.asIdeal ≤ z.asIdeal := h'
  refine PrimeSpectrum.ext (le_antisymm h'' ?_)
  rw [hz]; exact bot_le

theorem eq_of_specializes_lqf {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyQuasiFinite f] {a b : X}
    (h : a ⤳ b) (e : f a = f b) : a = b := by
  have hd := (f.isDiscrete_preimage_singleton (f b)).to_subtype
  have : (⟨a, e⟩ : f ⁻¹' {f b}) ⤳ ⟨b, rfl⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val this.eq

theorem eq_of_specializes_pt [IsIntegrallyClosed R] (Γ : QFGroup R T) (hE : Etale Γ.G.hom)
    (x : Spec (CommRingCat.of (FractionRing R))) (g : Γ.G.left) (s t : T)
    (hs : (Γ.pt s).left x ⤳ g) (ht : (Γ.pt t).left x ⤳ g) : s = t := by
  have := Γ.quasiFinite
  obtain ⟨h1, h2⟩ := stalk_spec_normal (R := R) (Γ.G.hom g)
  have hdom : IsDomain (Γ.G.left.presheaf.stalk g) :=
    (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth Γ.G.hom g).1
  let e₀ : Spec (Γ.G.left.presheaf.stalk g) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
  have key : ∀ u : T, (Γ.pt u).left x ⤳ g → Γ.G.left.fromSpecStalk g e₀ = (Γ.pt u).left x := by
    intro u hu
    have hr : (Γ.pt u).left x ∈ Set.range (Γ.G.left.fromSpecStalk g) := by
      rw [Scheme.range_fromSpecStalk]; exact hu
    obtain ⟨a, ha⟩ := hr
    have he₀a : e₀ ⤳ a := (PrimeSpectrum.le_iff_specializes (R := Γ.G.left.presheaf.stalk g) e₀ a).1
      (show (⊥ : Ideal _) ≤ _ from bot_le)
    have h3 : Γ.G.left.fromSpecStalk g e₀ ⤳ (Γ.pt u).left x := ha ▸ he₀a.map (Γ.G.left.fromSpecStalk g).continuous
    refine eq_of_specializes_lqf Γ.G.hom h3 ?_
    exact eq_of_specializes_bot (h3.map Γ.G.hom.continuous) (genPt_asIdeal Γ u x)
  exact Γ.pt_inj s t x x ((key s hs).symm.trans (key t ht))

theorem genPt_appLE (f : Spec (CommRingCat.of (FractionRing R)) ⟶ Spec (CommRingCat.of R))
    (hf : f = (genPt R).hom) (e) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ ⊤ e ≫
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom =
      CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
  subst hf
  have : (genPt R).hom.appLE ⊤ ⊤ e = (genPt R).hom.appTop := rfl
  rw [this]
  change (Scheme.ΓSpecIso _).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).appTop ≫ _ = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem regularAt_const [Finite T] [IsIntegrallyClosed R] (Γ : QFGroup R T) (hE : Etale Γ.G.hom)
    (φ : T → R) (g : Γ.G.left) :
    Γ.RegularAt (fun h => algebraMap R (FractionRing R) (φ h)) g := by
  classical
  let x₀ : Spec (CommRingCat.of (FractionRing R)) :=
    (IsLocalRing.closedPoint (FractionRing R) : PrimeSpectrum _)
  let P : T → Γ.G.left := fun t => (Γ.pt t).left x₀
  let Z : Set Γ.G.left := ⋃ t ∈ {t | ¬ P t ⤳ g}, closure {P t}
  have hZ : IsClosed Z := (Set.toFinite _).isClosed_biUnion fun _ _ => isClosed_closure
  let U : Γ.G.left.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hgU : g ∈ U := by
    show g ∉ Z
    simp only [Z, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
    intro t ht hg
    exact ht (specializes_iff_mem_closure.2 hg)
  have hPU : ∀ t, P t ∈ U → P t ⤳ g := by
    intro t ht
    by_contra hn
    exact ht (Set.mem_biUnion (x := t) hn (subset_closure rfl))
  refine ⟨U, hgU, ?_⟩
  by_cases hex : ∃ t₀, P t₀ ⤳ g
  · obtain ⟨t₀, ht₀⟩ := hex
    refine ⟨(Γ.G.hom.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ t₀)), ?_⟩
    intro t h
    have htU : P t ∈ U := h (show x₀ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
    have := eq_of_specializes_pt Γ hE x₀ g t t₀ (hPU t htU) ht₀
    subst this
    have hw : (Γ.pt t).left ≫ Γ.G.hom = (genPt R).hom := Over.w (Γ.pt t)
    have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Γ.G.hom.appLE ⊤ U le_top ≫
        (Γ.pt t).left.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom =
          CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
      erw [Scheme.Hom.appLE_comp_appLE_assoc]
      exact genPt_appLE _ hw _
    exact congrArg (fun m => m.hom (φ t)) key
  · refine ⟨0, fun t h => ?_⟩
    exact absurd ⟨t, hPU t (h (show x₀ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial))⟩ hex

theorem btOrder_top_eq_top_of_etale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), Etale Γ.G.hom → Γ.btOrder ⊤ = ⊤ := by
  intro R _ _ _ T _ _ Γ hE
  refine eq_top_iff.2 fun f _ => Algebra.subset_adjoin ?_
  intro t g _
  exact regularAt_const Γ hE (fun h => f (t * h)) g

end GlobalTheory.CompanionTheory.Ar.BT.EtaleTop
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.Tan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R)

def augPart (f : B) : RingHom.ker ε :=
  ⟨f - algebraMap R B (ε f), by simp [RingHom.mem_ker]⟩

theorem augPart_coe (f : B) : ((augPart ε f : RingHom.ker ε) : B) = f - algebraMap R B (ε f) := rfl

theorem augPart_of_mem (f : RingHom.ker ε) : augPart ε f.1 = f := by
  apply Subtype.ext
  rw [augPart_coe, RingHom.mem_ker.mp f.2, map_zero, sub_zero]

theorem augPart_add (f g : B) : augPart ε (f + g) = augPart ε f + augPart ε g := by
  apply Subtype.ext
  simp only [Submodule.coe_add, augPart_coe, map_add (f := _)]
  abel

theorem augPart_smul (r : R) (f : B) : (RingHom.ker ε).toCotangent (augPart ε (r • f)) =
    r • (RingHom.ker ε).toCotangent (augPart ε f) := by
  have h : augPart ε (r • f) = algebraMap R B r • augPart ε f := by
    apply Subtype.ext
    have hr : algebraMap R R r = r := rfl
    simp only [Submodule.coe_smul, augPart_coe, smul_eq_mul, Algebra.smul_def, map_mul,
      AlgHom.commutes, hr]
    ring
  rw [h, map_smul, algebraMap_smul]

theorem augPart_mul (f g : B) : (RingHom.ker ε).toCotangent (augPart ε (f * g)) =
    (ε f) • (RingHom.ker ε).toCotangent (augPart ε g) + (ε g) • (RingHom.ker ε).toCotangent (augPart ε f) := by
  have hab : ((augPart ε f : B) * (augPart ε g : B)) ∈ RingHom.ker ε :=
    Ideal.mul_mem_left _ _ (augPart ε g).2
  have hdec : augPart ε (f * g) =
      ⟨(augPart ε f : B) * (augPart ε g : B), hab⟩ + algebraMap R B (ε f) • augPart ε g +
        algebraMap R B (ε g) • augPart ε f := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, augPart_coe, smul_eq_mul, map_mul]
    ring
  have h0 : (RingHom.ker ε).toCotangent ⟨(augPart ε f : B) * (augPart ε g : B), hab⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul (augPart ε f).2 (augPart ε g).2
  rw [hdec, map_add (f := _), map_add (f := _), h0, zero_add, map_smul, map_smul, algebraMap_smul, algebraMap_smul]

variable {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

def derRing (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) : B →ₐ[R] TrivSqZeroExt R V :=
  AlgHom.ofLinearMap
    { toFun := fun f => TrivSqZeroExt.inl (ε f) + TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent (augPart ε f)))
      map_add' := fun f g => by
        rw [augPart_add, map_add (f := _), map_add (f := _), map_add (f := _)]
        ext <;> simp <;> abel
      map_smul' := fun r f => by
        rw [augPart_smul, map_smul]
        ext <;> simp }
    (by
      have : augPart ε (1 : B) = 0 := by
        apply Subtype.ext
        simp [augPart_coe]
      simp [this])
    (fun f g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [augPart_mul, map_add (f := _), map_smul, map_smul]
      ext <;> simp [add_comm])

theorem derRing_apply (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) (f : B) : derRing ε ψ f =
    TrivSqZeroExt.inl (ε f) + TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent (augPart ε f))) := rfl

theorem derRing_of_mem (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) (f : RingHom.ker ε) :
    derRing ε ψ f.1 = TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent f)) := by
  rw [derRing_apply, augPart_of_mem, RingHom.mem_ker.mp f.2]
  simp

theorem derRing_injective {ψ ψ' : (RingHom.ker ε).Cotangent →ₗ[R] V} (h : derRing ε ψ = derRing ε ψ') : ψ = ψ' := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker ε) x
  have hy := congrArg TrivSqZeroExt.snd (DFunLike.congr_fun h y.1)
  simpa [derRing_of_mem] using hy

end Alg

section Op
variable (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]

abbrev opMod : Module Rᵐᵒᵖ V := Module.compHom V ((RingHom.id R).fromOpposite fun _ _ => mul_comm _ _)

theorem opCentral : @IsCentralScalar R V _ (opMod R V).toSMul := by
  exact @IsCentralScalar.mk R V _ (opMod R V).toSMul (fun _ _ => rfl)
end Op

section Red
variable {R : Type} [CommRing R] (I : Ideal R)

def kap : TrivSqZeroExt R (R ⧸ I) →ₐ[R] DualNumber (R ⧸ I) where
  toFun a := TrivSqZeroExt.inl (Ideal.Quotient.mk I a.fst) + TrivSqZeroExt.inr a.snd
  map_one' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_zero' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' a b := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [TrivSqZeroExt.snd_mul, Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  commutes' r := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem kap_inr (q : R ⧸ I) : kap I (TrivSqZeroExt.inr q) = TrivSqZeroExt.inr q := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap]

theorem kap_algebraMap (r : R) : kap I (algebraMap R _ r) = algebraMap (R ⧸ I) (DualNumber (R ⧸ I)) (Ideal.Quotient.mk I r) := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap, TrivSqZeroExt.algebraMap_eq_inl']

theorem kap_map (a : DualNumber R) : kap I (TrivSqZeroExt.map (Ideal.Quotient.mkₐ R I).toLinearMap a) =
    dualMap (Ideal.Quotient.mk I) a := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap, dualMap]
end Red

section Rel

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]
  {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

abbrev ev1 (Γ : QFGroup R T) : Γ.btOrder ⊤ →ₐ[R] R := evalAt (Γ.btOrder ⊤) 1

def TanRel (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} {x : Spec (CommRingCat.of R) ⟶ S} (i : Γ.G.left ⟶ G.left)
    (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))) (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) (v : ob x V ⟶ G) : Prop :=
  ∃ y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left,
    y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) ∧
    y ≫ j = Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) ∧
    y ≫ i = v.left

end Rel

end GlobalTheory.CompanionTheory.Ar.BT.Tan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantValuationDifferent
section
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.CompanionTheory.Different

theorem padicValInt_discr_mul_count_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 E)),
      P.IsPrime → (p : 𝓞 E) ∈ P →
      ((padicValInt p (discr E) : ℕ)) * (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count P =
        (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E := by
  intro E _ _ _ p hp P hP hpP
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hdecomp : (discr E).natAbs =
      p ^ padicValNat p (discr E).natAbs * ((discr E).natAbs / p ^ (discr E).natAbs.factorization p) := by
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (discr E).natAbs p]
    rw [Nat.factorization_def _ hp.out, Nat.padicValNat_def]
  have hnd : ¬ p ∣ (discr E).natAbs / p ^ (discr E).natAbs.factorization p :=
    Nat.not_dvd_ordCompl hp.out hd
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E p _ _ hp.out hnd hdecomp P hP hpP
  rw [h]
  rw [padicValInt, Nat.padicValNat_def]

end GlobalTheory.CompanionTheory.Different
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGenericStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stalk_fraction_of_generic : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ b c : X.presheaf.stalk p.1, genMap ξ p c ≠ 0 ∧ a * genMap ξ p c = genMap ξ p b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_frac_genMap | exact GlobalTheory.CompanionTheory.Ar.exists_frac_genMap | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_frac_genMap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsClopenSpecializationsGenPtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_specializations_genPt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → IsClopen {q : X | genPt ξ ⤳ q} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes | exact GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes | (intros; apply GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCptGen_residue_field_generic : ∀ (X : Scheme.{0}), (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ x : X, (∀ y : X, y ⤳ x → y = x) → IsCptGen (Ω := X.residueField x) (X.fromSpecResidueField x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal | exact GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal | (intros; apply GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolynomialFieldExtensionDegreeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_field_extension_degree : ∀ (κ K L I : Type) [Field κ] [Field K] [Field L] [Algebra K L] (ψ : κ ≃+* K) (T : I → L), AlgebraicIndependent K T → ∃ φ : FractionRing (MvPolynomial I κ) →+* L, (∀ a, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.C a)) = algebraMap K L (ψ a)) ∧ (∀ i, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.X i)) = T i) ∧ (letI := φ.toAlgebra; Module.finrank (FractionRing (MvPolynomial I κ)) L) = Module.finrank (IntermediateField.adjoin K (Set.range T)) L := by
  first | exact @GlobalTheory.CompanionTheory.Relay.polynomial_field_extension_degree | exact GlobalTheory.CompanionTheory.Relay.polynomial_field_extension_degree | (intros; apply GlobalTheory.CompanionTheory.Relay.polynomial_field_extension_degree <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TraceIntegralSubringExtensionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_integral_subring_extension : ∀ (K L : Type) [Field K] [Field L] [CharZero K] (φ : K →+* L) (B₀ : Finset L) (x : L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∃ B' : Finset K, ∀ A' : Subring K, (↑B' : Set K) ⊆ A' → ∃ (A : Subring L) (hA : ∀ a : A', φ a ∈ A) (_ : (↑B₀ : Set L) ⊆ A) (hx : x ∈ A) (ht : (letI := φ.toAlgebra; Algebra.trace K L x) ∈ A'), ∀ (C : Type) [Field C] [IsAlgClosed C] (ev : A' →+* C), (∀ a, IsAlgebraic ℤ (ev a)) → ∃ (n : ℕ) (ev' : Fin n → (A →+* C)), (∀ j (a : A'), ev' j ⟨φ a, hA a⟩ = ev a) ∧ (∀ j a, IsAlgebraic ℤ (ev' j a)) ∧ ev ⟨_, ht⟩ = ∑ j, ev' j ⟨x, hx⟩ := by
  first | exact @GlobalTheory.CompanionTheory.TraceSpec.trace_specialisation | exact GlobalTheory.CompanionTheory.TraceSpec.trace_specialisation | (intros; apply GlobalTheory.CompanionTheory.TraceSpec.trace_specialisation <;> assumption)
end

