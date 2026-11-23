module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0348
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroClosureEtaleAt
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem etale_of_isZTorsor (B D : Type) [CommRing B] [IsNoetherianRing B] [CommRing D] [Algebra B D]
    (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D))
    (h : GlobalTheory.KeyOriginCut.IsZTorsor B D q act) : Algebra.Etale B D := by
  haveI := GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor B D q hq act h
  obtain ⟨hfin, hproj, _, _⟩ := h
  haveI := hfin
  haveI := hproj
  haveI : Algebra.FinitePresentation B D :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

theorem exists_ne_zero_closureEtaleAt : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ a : A, a ≠ 0 ∧ ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  intro q A _ _ _ _ _ _ EA _ _ _ _ _ QA _ DA _ _ actA hq _ htor
  haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
  obtain ⟨_, _⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed (Polynomial A) EA QA
  set R := Localization.AtPrime QA
  haveI : Module.Finite (GlobalTheory.LocAcyc.GenFib A R) DA := htor.1
  haveI := etale_of_isZTorsor _ DA q hq actA htor
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R DA
  haveI : Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R DA) := GlobalTheory.T.finite_integralClosureOverGenericFibre_of_etale A R DA
  haveI : Algebra.FinitePresentation R (GlobalTheory.KeyOriginNoeth.closure A R DA) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨m, hm, hE⟩ := GlobalTheory.T.exists_etale_away_of_isEtaleAt R (GlobalTheory.KeyOriginNoeth.closure A R DA)
    (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (fun Q _ hQ =>
      GlobalTheory.T.closure_prime_regular_height A R DA Q (fun a ha => hQ _ ⟨a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩))
  obtain ⟨a, ha, rfl⟩ := hm
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun P _ hP => ?_⟩
  exact GlobalTheory.T.etale_localization_atPrime_tensor_of_etale_away' R _ _ hE P hP

end GlobalTheory.KeyOriginEnlarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIsNilpotentMulFiniteInfFgIdealsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_isNilpotent_mul_finite_inf_fg_ideals : ∀ (D E : Type) [CommRing D] [IsDomain D] [CommRing E] [Algebra D E] (ι : Type) (X : Finset ι) (P : ι → Ideal E), (∀ i ∈ X, (P i).FG) → (∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → (⨅ i ∈ X, P i) ≤ Q) → ∃ s : D, s ≠ 0 ∧ ∀ y ∈ (⨅ i ∈ X, P i), IsNilpotent (algebraMap D E s * y) := by
  first | (exact @GlobalTheory.FinInterNil.main) | (exact GlobalTheory.FinInterNil.main) | (intros; apply GlobalTheory.FinInterNil.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringLeValuationSubringA
section
open Polynomial

namespace GlobalTheory

theorem exists_normal_finiteType_subring_le_valuationSubring :
    ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (V : ValuationSubring κ) (T : Finset κ),
    (∀ a : ℂ, algebraMap ℂ κ a ∈ V) → (∀ x ∈ T, x ∈ V) →
    (∀ f : κ, ∃ a ∈ Algebra.adjoin ℂ (T : Set κ), ∃ b ∈ Algebra.adjoin ℂ (T : Set κ), b ≠ 0 ∧ f * b = a) →
    ∃ (R : Subring κ) (hcR : ∀ a : ℂ, algebraMap ℂ κ a ∈ R),
      ((algebraMap ℂ κ).codRestrict R hcR).FiniteType ∧ (∀ x ∈ T, x ∈ R) ∧ R ≤ V.toSubring ∧
      IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R κ := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro κ _ _ V T hc hT hgen
    classical
    haveI : CharZero κ := charZero_of_injective_algebraMap (algebraMap ℂ κ).injective
    let A : Subalgebra ℂ κ := Algebra.adjoin ℂ (T : Set κ)
    haveI : Algebra.FiniteType ℂ A := .adjoin_of_finite T.finite_toSet
    haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
    have hAV : ∀ y ∈ A, y ∈ V := fun y hy => by
      let E' : Subalgebra ℂ κ := { V.toSubring with algebraMap_mem' := fun a => hc a }
      have : A ≤ E' := Algebra.adjoin_le fun x hx => hT x hx
      exact this hy
    haveI : Algebra.IsAlgebraic A κ := ⟨fun f => by
      obtain ⟨a, ha, b, hb, hb0, he⟩ := hgen f
      have hf : f = a / b := by rw [eq_div_iff hb0, he]
      have ha' : IsAlgebraic A a := isAlgebraic_algebraMap (⟨a, ha⟩ : A)
      have hb' : IsAlgebraic A b := isAlgebraic_algebraMap (⟨b, hb⟩ : A)
      rw [hf, div_eq_mul_inv]
      exact ha'.mul hb'.inv⟩
    have htop : Subfield.closure (Set.range (algebraMap ℂ κ) ∪ (T : Set κ)) = ⊤ := by
      refine eq_top_iff.mpr fun f _ => ?_
      have hle : A.toSubring ≤ (Subfield.closure (Set.range (algebraMap ℂ κ) ∪ (T : Set κ))).toSubring := by
        rw [show A.toSubring = Subring.closure (Set.range (algebraMap ℂ κ) ∪ (T : Set κ)) from
          Algebra.adjoin_eq_ring_closure _]
        exact Subring.closure_le.mpr Subfield.subset_closure
      obtain ⟨a, ha, b, hb, hb0, he⟩ := hgen f
      have hf : f = a / b := by rw [eq_div_iff hb0, he]
      rw [hf]
      exact Subfield.div_mem _ (hle ha) (hle hb)
    haveI : Algebra.EssFiniteType ℂ κ := by
      refine essFiniteType_of_finiteDimensional_subfield_closure T.finite_toSet ?_
      rw [htop]
      exact finiteDimensional_top_subfield κ
    haveI : Algebra.EssFiniteType A κ := .of_comp ℂ A κ
    haveI : Module.Finite A (integralClosure A κ) := finite_integralClosure_of_essFiniteType_field (R := A) ℂ κ
    let S := integralClosure A κ
    haveI : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
    haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
    haveI : IsFractionRing S κ := integralClosure.isFractionRing_of_algebraic fun x hx => Subtype.ext hx
    haveI : IsIntegrallyClosed S := (isIntegrallyClosed_iff κ).mpr fun {x} hx =>
      ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩
    have hcR : ∀ a : ℂ, algebraMap ℂ κ a ∈ S.toSubring := fun a =>
      S.algebraMap_mem (⟨algebraMap ℂ κ a, A.algebraMap_mem a⟩ : A)
    refine ⟨S.toSubring, hcR, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ S)
    · intro x hx
      exact S.algebraMap_mem (⟨x, Algebra.subset_adjoin hx⟩ : A)
    · intro x hx
      obtain ⟨q, hqm, hq⟩ := (hx : IsIntegral A x)
      let ι : A →+* V :=
        { toFun := fun a => ⟨a, hAV a a.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hE : IsIntegral V x := by
        refine ⟨q.map ι, hqm.map ι, ?_⟩
        rw [eval₂_map]
        exact hq
      obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hE
      exact y.2
    · exact (inferInstance : IsNoetherianRing S)
    · exact (inferInstance : IsIntegrallyClosed S)
    · exact (inferInstance : IsFractionRing S κ)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionOfMonicPolynomialsHaveRootsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_retraction_of_monicPolynomialsHaveRoots : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], AIC T → ∀ (ι : T →ₐ[D] E) (Q : Ideal E), Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → ∃ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T ∧ RingHom.ker χ = Q := by
  first | (exact @GlobalTheory.exists_retraction_of_AIC) | (exact GlobalTheory.exists_retraction_of_AIC) | (intros; apply GlobalTheory.exists_retraction_of_AIC  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomLimitOfDoublingJetsStatement
section
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_limit_of_doublingJets : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ∀ φ : ℕ → A → PowerSeries R, (∀ n, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 2) (φ n)) → (∀ n f, (PowerSeries.X : PowerSeries R) ^ (n + 2) ∣ φ (n + 1) f - φ n f) → ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧ PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧ (PowerSeries.rescale 2).comp γ = γ.comp m := by
  first | exact @GlobalTheory.Nef.PathJet.limit_of_jets | exact GlobalTheory.Nef.PathJet.limit_of_jets | (intros; apply GlobalTheory.Nef.PathJet.limit_of_jets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSheafHomLinearMapsSheafCurryEquiv
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

def homShEval (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (f : X ⟶ (homSh J).obj (op M)) (m : M) : X ⟶ J :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun x => (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom m
          map_add' := fun x y => by
            rw [map_add (f.hom.app U).hom x y]; rfl
          map_smul' := fun r x => by
            rw [(f.hom.app U).hom.map_smul]; rfl }
     naturality := fun U V g => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        have h := congrArg (fun k => (show M ⟶ J.obj.obj V from k).hom m)
          (congrArg (fun k => (ModuleCat.Hom.hom k) x) (f.hom.naturality g))
        exact h }⟩

def homShCurry (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (f : X ⟶ (homSh J).obj (op M)) :
    M →ₗ[ULift.{1} R] (X ⟶ J) where
  toFun m := homShEval J X M f m
  map_add' m n := by
    apply Sheaf.hom_ext; ext U x
    exact (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom.map_add m n
  map_smul' r m := by
    apply Sheaf.hom_ext; ext U x
    exact (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom.map_smul r m

def homShUncurry (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (l : M →ₗ[ULift.{1} R] (X ⟶ J)) :
    X ⟶ (homSh J).obj (op M) :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun x => (show M ⟶ J.obj.obj U from ModuleCat.ofHom
            { toFun := fun m => ((l m).hom.app U).hom x
              map_add' := fun m n => by rw [map_add l m n]; rfl
              map_smul' := fun r m => by rw [l.map_smul]; rfl })
          map_add' := fun x y => by
            apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
            exact ((l m).hom.app U).hom.map_add x y
          map_smul' := fun r x => by
            apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
            exact ((l m).hom.app U).hom.map_smul r x }
     naturality := fun U V g => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
        exact congrArg (fun k => (ModuleCat.Hom.hom k) x) ((l m).hom.naturality g) }⟩

def homShEquiv (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) :
    (X ⟶ (homSh J).obj (op M)) ≃ (M →ₗ[ULift.{1} R] (X ⟶ J)) where
  toFun := homShCurry J X M
  invFun := homShUncurry J X M
  left_inv f := by
    apply Sheaf.hom_ext; ext U x
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
    rfl
  right_inv l := by
    apply LinearMap.ext; intro m
    apply Sheaf.hom_ext; ext U x
    rfl

theorem homShEquiv_natural_left (J X : Shv R) (M N : ModuleCat.{1} (ULift.{1} R)) (p : M ⟶ N)
    (f : X ⟶ (homSh J).obj (op N)) :
    homShEquiv J X M (f ≫ (homSh J).map p.op) = (homShEquiv J X N f) ∘ₗ p.hom := by
  apply LinearMap.ext; intro m
  apply Sheaf.hom_ext; ext U x
  rfl

theorem homShEquiv_natural_right (J X Y : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (i : X ⟶ Y)
    (f : Y ⟶ (homSh J).obj (op M)) :
    homShEquiv J X M (i ≫ f) = (Linear.leftComp (ULift.{1} R) J i) ∘ₗ (homShEquiv J Y M f) := by
  apply LinearMap.ext; intro m
  apply Sheaf.hom_ext; ext U x
  rfl

theorem homSh_curry : ∀ (R : Type) [CommRing R] (J : Shv R), ∃ e : ∀ (X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)), (X ⟶ (homSh J).obj (op M)) ≃ (M →ₗ[ULift.{1} R] (X ⟶ J)), (∀ (X : Shv R) (M N : ModuleCat.{1} (ULift.{1} R)) (p : M ⟶ N) (f : X ⟶ (homSh J).obj (op N)), e X M (f ≫ (homSh J).map p.op) = (e X N f) ∘ₗ p.hom) ∧ (∀ (X Y : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (i : X ⟶ Y) (f : Y ⟶ (homSh J).obj (op M)), e X M (i ≫ f) = (Linear.leftComp (ULift.{1} R) J i) ∘ₗ (e Y M f)) :=
  fun _ _ J => ⟨homShEquiv J, homShEquiv_natural_left J, fun X Y M i f => homShEquiv_natural_right J X Y M i f⟩

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtHeckePointWeilPairingOrthogonal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem ev_nsmul (I : TateIsoO D K Q act e) (n j : ℕ) (y : D.La) : I.ev n (j • y) = I.ev n y ^ j := by
  induction j with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (h.symm.trans (_root_.mul_one _).symm)
  | succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem pair_one (I : TateIsoO D K Q act e) (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (w : D.La)
    (hw : ∀ v, (n : ℤ) ∣ 2 * D.EF w v) :
    I.ev n w ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (I.ev n w) z 1 := by
  refine ⟨(I.onto n hn hnp _).2 ⟨w, rfl⟩, fun z hz => ?_⟩
  obtain ⟨v, rfl⟩ := (I.onto n hn hnp z).1 hz
  have h := I.isom n hn hnp w v
  obtain ⟨t, ht⟩ := hw v
  rw [ht, zpow_mul, zpow_natCast, (I.ζ_prim n hn hnp).pow_eq_one, one_zpow] at h
  exact h

theorem sqrt_hecke_point_weil_orthogonal : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (K : Type) [Field K] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D K Q act e)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 0 < N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ x : D.La,
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • g x) ∧ (h' ^ (k ^ 2 / c)) ^ n = 1 ∧
      ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  intro p _ D K _ Q _ act e I g c k N hc hk hN hNp hEF hsurj hck x
  have hp : p.Prime := Fact.out
  have hc0 : c ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hc)
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hk)
  have hm : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have key : ∀ v, ∃ v', ((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v = k * D.EF x v' := by
    intro v
    obtain ⟨v', hv'⟩ := hsurj v
    refine ⟨v', ?_⟩
    have h1 : D.EF (g x) (g v') = (k : ℤ) * D.EF (g x) v := by rw [hv', map_nsmul, nsmul_eq_mul]
    have h2 := hEF x v'
    have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast hc0
    have hmZ : ((k ^ 2 / c : ℕ) : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast hm
    apply mul_left_cancel₀ hcZ
    calc (c : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v)
        = (((k ^ 2 / c : ℕ) : ℤ) * c) * D.EF (g x) v := by ring
      _ = k * (k * D.EF (g x) v) := by rw [hmZ]; ring
      _ = k * (c * D.EF x v') := by rw [← h1, h2]
      _ = c * (k * D.EF x v') := by ring
  have core : ∀ n j : ℕ, 0 < n → n.Coprime p → (n : ℤ) ∣ 2 * j * N * k →
      (I.ev n (j • N • g x) ^ (k ^ 2 / c)) ^ n = 1 ∧
        ∀ z : Q, z ^ n = 1 → e n (I.ev n (j • N • g x) ^ (k ^ 2 / c)) z 1 := by
    intro n j hn hnp hd
    rw [← ev_nsmul]
    refine pair_one I n hn hnp _ (fun v => ?_)
    obtain ⟨v', hv'⟩ := key v
    have : 2 * D.EF ((k ^ 2 / c) • j • N • g x) v = 2 * j * N * k * D.EF x v' := by
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      calc _ = 2 * (j : ℤ) * N * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v) := by ring
        _ = _ := by rw [hv']; ring
    rw [this]
    exact hd.mul_right _
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨r, hr⟩ : Odd k := Nat.odd_iff.2 (by
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · exfalso
        have h2 : 2 ∣ Nat.gcd k 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) dvd_rfl
        rw [hk] at h2; omega
      · exact h)
    have hnp : (N * k).Coprime 2 := Nat.Coprime.mul_left hNp hk
    have hn : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k, I.ev (N * k) ((r + 1) • N • g x), hn, hnp, ?_, ?_⟩
    · rw [ev_nsmul, ← pow_mul, show (r + 1) * 2 = 1 + k by omega, pow_add, pow_one, ← ev_nsmul,
        smul_smul, mul_comm k N, (I.ker (N * k) hn hnp _).2 ⟨g x, rfl⟩, _root_.mul_one]
    · exact core (N * k) (r + 1) hn hnp ⟨2 * (r + 1), by push_cast; ring⟩
  · have h2p : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (fun h => hp2 h.symm)
    have hnp : (N * k * 2).Coprime p := Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hk) h2p
    have hnk : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k * 2, I.ev (N * k * 2) (N • g x), by omega, hnp, I.tower (N * k) 2 hnk (by norm_num) hnp _, ?_⟩
    have := core (N * k * 2) 1 (by omega) hnp ⟨1, by push_cast; ring⟩
    simpa only [one_smul] using this

end GlobalTheory.UPel.HT.HeckeRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSumSquaresRightDerivPowDifferentialOperato
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem apOp_sum_coef {d : ℕ} {ι : Type} (s : Finset ι) (m : ℕ) (a : ι → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (u : E d → ℂ) (x : E d) :
    apOp m (fun n w y => ∑ i ∈ s, a i n w y) u x = ∑ i ∈ s, apOp m (a i) u x := by
  simp only [apOp, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]

theorem symb_sum_coef {d : ℕ} {ι : Type} (s : Finset ι) (m : ℕ) (a : ι → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (x ξ : E d) :
    symb m (fun n w y => ∑ i ∈ s, a i n w y) x ξ = ∑ i ∈ s, symb m (a i) x ξ := by
  simp only [symb, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem exists_apOp_sumSq_pow : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ k : ℕ, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ξ : E d, symb (2 * k) a x ξ = (((∑ i, (∑ j, c (b i) j x * ξ j) ^ 2) ^ k : ℝ) : ℂ)) ∧ ∀ f : h.smoothFuns (F := ℂ), ∀ x ∈ Metric.ball (0 : E d) r, (((∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ^ k) f : G → ℂ) (h.expG (coordEquiv b (x))) = apOp (2 * k) a (fun y => (f : G → ℂ) (h.expG (coordEquiv b (y)))) x := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b r c ⟨hc, _, hder⟩ k
  set U : Set (E d) := Metric.ball 0 r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hchart : ∀ f : G → ℂ, h.IsSmoothFun f →
      ContDiff ℝ ∞ (fun y : E d => f (h.expG (coordEquiv b y))) := by
    intro f hf
    simpa using h.contDiff_comp_coordEquiv hf 1 b
  have step : ∀ (X : 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ v : E d → ℂ,
      (∀ y ∈ U, f (h.expG (coordEquiv b y)) = v y) → ∀ x ∈ U,
      h.rightDeriv X f (h.expG (coordEquiv b x)) = ∑ j, (c X j x : ℂ) * fderiv ℝ v x (ev j) := by
    intro X f hf v hv x hx
    rw [hder f hf X x hx]
    have e : (fun y : E d => f (h.expG (coordEquiv b y))) =ᶠ[nhds x] v :=
      Filter.eventually_of_mem (hU.mem_nhds hx) hv
    rw [e.fderiv_eq]
  have hcC : ∀ i j, ContDiffOn ℝ ∞ (fun y => ((c (b i) j y : ℝ) : ℂ)) U := fun i j =>
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hc (b i) j)
  induction k with
  | zero =>
    refine ⟨fun _ _ _ => 1, fun _ _ => contDiffOn_const, ?_, ?_⟩
    · intro x ξ; simp [symb]
    · intro f x _
      simp [apOp_zero_one]
  | succ k ih =>
    obtain ⟨a, ha, hsa, hap⟩ := ih
    choose a1 ha1 hs1 hap1 using fun i : Fin d =>
      GlobalTheory.VFComp.vectorField_comp d (2 * k) U hU a (fun j y => ((c (b i) j y : ℝ) : ℂ)) ha (hcC i)
    choose a2 ha2 hs2 hap2 using fun i : Fin d =>
      GlobalTheory.VFComp.vectorField_comp d (2 * k + 1) U hU (a1 i) (fun j y => ((c (b i) j y : ℝ) : ℂ)) (ha1 i) (hcC i)
    have e2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    refine ⟨fun n w y => ∑ i, a2 i n w y, fun n w => ContDiffOn.sum fun i _ => ha2 i n w, ?_, ?_⟩
    · intro x ξ
      rw [symb_sum_coef, e2]
      simp only [hs2, hs1, hsa]
      push_cast
      rw [pow_succ', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · intro f x hx
      rw [apOp_sum_coef, e2, pow_succ', Module.End.mul_apply]
      set g := ((∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ^ k) f with hg
      simp only [LinearMap.sum_apply, Finset.sum_apply, Submodule.coe_sum, Module.End.mul_apply,
        IsExpLieAlgebra.coe_rightDerivEnd]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hf0 := hchart _ f.2
      have h1 : ∀ y ∈ U, h.rightDeriv (b i) (g : G → ℂ) (h.expG (coordEquiv b y)) =
          apOp (2 * k + 1) (a1 i) (fun y => (f : G → ℂ) (h.expG (coordEquiv b y))) y := by
        intro y hy
        rw [step (b i) _ g.2 _ (fun z hz => hap f z hz) y hy]
        exact hap1 i _ hf0.contDiffOn y hy
      rw [step (b i) _ (h.isSmoothFun_rightDeriv g.2 (b i)) _ h1 x hx]
      exact hap2 i _ hf0.contDiffOn x hx

end GlobalTheory.HCA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorInductionVirtualCharacterPrimeStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorInduction_virtualCharacter_prime : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ ∈ Virt ℂ ℂ G, ∃ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  first | (exact @GlobalTheory.Shin.tensorInd_virt_prime) | (exact GlobalTheory.Shin.tensorInd_virt_prime) | (intros; apply GlobalTheory.Shin.tensorInd_virt_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopFormsStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ τ : DR k K →ₗ[K] K, IsTop k K x τ) ∧ ∀ τ : DR k K →ₗ[K] K, IsTop k K x τ → ∀ y ∈ ⋀[K]^d Ω[K⁄k], y = τ y • vol0 k K x := by
  first | (exact @GlobalTheory.PD.isTop_exists_and_eq) | (exact GlobalTheory.PD.isTop_exists_and_eq) | (intros; apply GlobalTheory.PD.isTop_exists_and_eq <;> assumption)
end

