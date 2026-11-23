module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0538
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrict
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

private theorem unitsMap_comp_appTop {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ g).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) := by
  ext
  simp [Scheme.Hom.comp_appTop]
  rfl

private theorem isUnit_natCast_appTop {V U : Scheme.{0}} (g : V ⟶ U) (Q : ℕ) (h : IsUnit (Q : Γ(U, ⊤))) :
    IsUnit (Q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem res_defectSec : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) →
    ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u →
      Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defect Q q V v := by
  intro Q q _ hqQ U u hQ

  let S : Sieve U :=
    { arrows := fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ Q = Units.map g.appTop.hom.toMonoidHom u
      downward_closed := by
        rintro V W g ⟨v, hv⟩ k
        refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
        rw [← map_pow, hv, unitsMap_comp_appTop] }
  have hS : S ∈ Scheme.etaleTopology U := by
    obtain ⟨S₀, hS₀, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u
    exact GrothendieckTopology.superset_covering _ (fun V g hg => hP V g hg) hS₀
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res _ (tw q 1)).X 0) V :=
    fun V g hg => defect Q q V hg.choose
  have hcompat : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k) := by
    intro V W g k hg
    have hQV : IsUnit (Q : Γ(V, ⊤)) := isUnit_natCast_appTop g Q hQ
    have hQW : IsUnit (Q : Γ(W, ⊤)) := isUnit_natCast_appTop k Q hQV
    change Sec.res k (defect Q q V hg.choose) = defect Q q W (S.downward_closed hg k).choose
    rw [GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W V k hg.choose hQV]
    refine GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq Q q hqQ W _ _ hQW ?_
    rw [(S.downward_closed hg k).choose_spec, ← map_pow, hg.choose_spec, unitsMap_comp_appTop]
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.EtC.sec_ext_glue _ _ U).2 S hS s hcompat
  have hex : ∃ a : Sec ((res _ (tw q 1)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ),
      v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = defect Q q V v := by
    refine ⟨a, fun V g v hv => ?_⟩
    have hg : S.arrows g := ⟨v, hv⟩
    rw [ha V g hg]
    exact GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq Q q hqQ V _ _ (isUnit_natCast_appTop g Q hQ) (hg.choose_spec.trans hv.symm)
  intro V g v hv
  exact pick_spec hex V g v hv

end GlobalTheory.EtC.RedChern
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNervePullbackBijectiveDegreeZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.LevelZero

variable {R : Type} [CommRing R]

theorem pull_iso_bijective {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem cechC_pull_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (A' : Type) [CommRing A'] [Algebra A A'], Module.Finite A A' → ∀ (k : ℕ) (i : ℤ),
    Function.Bijective (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) := by
  intro q _ A _ hA hq A' _ _ hfin k i
  obtain ⟨e0, e, h1, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI := hfin
  have hT : Module.Finite A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) := inferInstance
  have hr0 := GlobalTheory.T.laurentC_pullback_bijective_finite_strictlyHenselian q A hA hq (PiTensorProduct A (fun _ : Fin (k + 1) => A')) hT i
  have hmap := congrArg (fun f => disc.map f) h1
  simp only [Functor.map_comp] at hmap
  have heq : ∀ x, pull _ (disc.map e.hom) (tw q i) 0 (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0 x) =
      pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q i) 0
        (pull _ (disc.map e0.hom) (tw q i) 0 x) := by
    intro x
    rw [← pull_comp, hmap, pull_comp]
    rfl
  have hcomp : (pull _ (disc.map e.hom) (tw q i) 0) ∘ (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) =
      (pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q i) 0) ∘
        (pull _ (disc.map e0.hom) (tw q i) 0) := funext heq
  have he : Function.Bijective (pull _ (disc.map e.hom) (tw q i) 0) :=
    pull_iso_bijective (disc.mapIso e) (tw q i) 0
  have he0 : Function.Bijective (pull _ (disc.map e0.hom) (tw q i) 0) :=
    pull_iso_bijective (disc.mapIso e0) (tw q i) 0
  rw [← Function.Bijective.of_comp_iff' he, hcomp]
  exact hr0.comp he0

end GlobalTheory.EtC.GmStep.LevelZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingModTEmbedsStrictHenselianStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localRing_mod_t_embeds_strictHenselian : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [HenselianLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA] (j : EA →+* O),
      j.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (f : A →+* A₁) (i₁ : A₁ →+* T) (e : EA →+* A₁),
      Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp f = i ∧
      e.comp (algebraMap (Polynomial A) EA) = f.comp (Polynomial.evalRingHom 0) ∧
      ∀ x : EA, algebraMap T O (i₁ (e x)) - j x ∈ Ideal.span {algebraMap (Polynomial T) O Polynomial.X} := by
  first | (exact @GlobalTheory.FibreRetract.fibre_retract) | (exact GlobalTheory.FibreRetract.fibre_retract) | (intros; apply GlobalTheory.FibreRetract.fibre_retract  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdentityComponentsOfMulInv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem identityComponent_shear_mul {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    lift (fst G G ≫ ι[G]) μ[G] ≫ μ[G] = snd G G := by
  have h1 : lift (fst G G ≫ ι[G]) μ[G] ≫ μ[G] = (fst G G)⁻¹ * (fst G G * snd G G) := by
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Hom.inv_def]
  rw [h1, inv_mul_cancel_left]

theorem mem_identityComponents_of_mul_inv :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (∀ z ∈ U, G.hom z = G.hom y → z ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G _ hs U y hU hy
  obtain ⟨w, hf, hm, rfl⟩ := hy
  have hbf : G.hom ((fst G G).left w) = G.hom ((snd G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w, Over.w]
  have hbm : G.hom ((μ[G]).left w) = G.hom ((snd G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w, Over.w]
  have zf := hU _ hf hbf
  have zm := hU _ hm hbm
  have zi := GlobalTheory.T.inv_mem_identity_component_fibre S G _ zf
  set φ : G ⊗ G ⟶ G ⊗ G := lift (fst G G ≫ ι[G]) μ[G] with hφ
  have e1 : (fst G G).left (φ.left w) = (ι[G]).left ((fst G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, hφ, lift_fst]
  have e2 : (snd G G).left (φ.left w) = (μ[G]).left w := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφ, lift_snd]
  have key := _root_.GlobalTheory.IdCompMul.mul_mem S G hs (φ.left w) (e1 ▸ zi) (e2 ▸ zm)
  have e3 : (μ[G]).left (φ.left w) = (snd G G).left w := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφ, identityComponent_shear_mul]
  rwa [e3] at key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismsEqSpreadToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem morphisms_eq_spread_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ Z : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (q : Z ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [LocallyOfFiniteType q] (a b : X₀ ⟶ Z), IsPullback π f f₀ (spMap R₀.subtype) → a ≫ q = f₀ → b ≫ q = f₀ → π ≫ a = π ≫ b → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hle)) → π₁ ≫ a = π₁ ≫ b := by
  intro S _ R₀ X X₀ Z f f₀ q π _ _ a b hp ha hb hab
  have hp' : IsPullback π f f₀ (spMap (algebraMap R₀ S)) := hp
  have hfst : pullback.fst f₀ (spMap (algebraMap R₀ S)) = hp'.isoPullback.inv ≫ π := by
    rw [hp'.isoPullback_inv_fst]
  obtain ⟨R', hR', ⟨s, rfl⟩, h⟩ := Spread.exists_fg_comp_eq_comp (A := S) f₀ q ⊥ Subalgebra.fg_bot
    (pullback.fst _ _ ≫ a) (pullback.fst _ _ ≫ b)
    (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb])
    (by rw [Spread.bcMap_fst_assoc, Spread.bcMap_fst_assoc, hfst, Category.assoc, Category.assoc, hab])
  rw [Spread.bcMap_fst_assoc, Spread.bcMap_fst_assoc] at h
  refine ⟨s, fun R₁ h₀ hs X₁ f₁ π₁ hp₁ ↦ ?_⟩
  have hle : (Algebra.adjoin R₀ (s : Set S)).toSubring ≤ R₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h₀ r.2
    | add x y _ _ hx hy => exact R₁.add_mem hx hy
    | mul x y _ _ hx hy => exact R₁.mul_mem hx hy
  let g : Algebra.adjoin R₀ (s : Set S) →+* R₁ := Subring.inclusion hle
  have hg : spMap g ≫ spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))) =
      spMap (Subring.inclusion h₀) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let m : X₁ ⟶ pullback f₀ (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S)))) :=
    pullback.lift π₁ (f₁ ≫ spMap g) (by rw [Category.assoc, hg, hp₁.w])
  have hm : m ≫ pullback.fst _ _ = π₁ := pullback.lift_fst _ _ _
  rw [← hm, Category.assoc, Category.assoc, h]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechDegreeZeroCocyclesCorrespond
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq_id {a : (NE κ)ᵒᵖ} (f : a ⟶ a) : f = 𝟙 a :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem mp_single (c : CC F 0) (i j : κ) (hij : j = i) (h : sub (ne {j} (Finset.singleton_nonempty j)) ⊆
    sub (ne {i} (Finset.singleton_nonempty i))) (hc : ({j} : Finset κ).card = 0 + 1) :
    mp F (homOf h) (c ⟨{j}, hc⟩) = c ⟨{i}, Finset.card_singleton i⟩ := by
  subst hij
  rw [hom_eq_id (homOf h), mp_id]

theorem sum_cubeSign_two (t : Finset κ) (ht : t.card = 2) : ∑ i ∈ t, GlobalTheory.cubeSign t i = 0 := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 ht
  rw [Finset.sum_pair hxy]
  rcases lt_or_gt_of_ne hxy with h | h
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]

theorem orderedCech_degreeZero_cocycles_correspond : (∀ c : CC F 0, δ F 0 c = 0 → e0 F c = 0 → c = 0) ∧
    ∀ g : C0 F, d0 F g = 0 → ∃ c : CC F 0, δ F 0 c = 0 ∧ e0 F c = g := by
  refine ⟨fun c _ he => ?_, fun g hg => ?_⟩
  · funext s
    obtain ⟨s, hs⟩ := s
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    have H := congrFun he (ne {i} (Finset.singleton_nonempty i))
    have hm : mn (ne {i} (Finset.singleton_nonempty i)) = i := Finset.min'_singleton i
    have := mp_single F c i _ hm
    simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply] at H
    exact (this (Finset.singleton_subset_iff.2 (mn_mem _)) (Finset.card_singleton _)).symm.trans H
  · have hg' : ∀ {T T' : (NE κ)ᵒᵖ} (φ : T ⟶ T'), mp F φ (g T) = g T' := by
      intro T T' φ
      have := congrFun (congrFun (congrFun hg T) T') φ
      rw [amitsur_d0_apply] at this
      exact (sub_eq_zero.1 this).symm
    refine ⟨fun s => g (ne s.1 (card_nonempty s)), ?_, ?_⟩
    · funext t
      rw [δ_apply]
      simp only [hg']
      rw [← Finset.sum_smul, Finset.sum_coe_sort t.1 (fun i => GlobalTheory.cubeSign t.1 i),
        sum_cubeSign_two t.1 t.2, zero_smul]
      rfl
    · funext a
      simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact hg' _

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechDifferentialZeroConstOne
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem sum_cubeSign_card_two {κ : Type} [LinearOrder κ] (t : Finset κ) (h : t.card = 2) :
    ∑ i ∈ t, GlobalTheory.cubeSign t i = 0 := by
  have key : ∀ x y : κ, x < y → ∑ i ∈ ({x, y} : Finset κ), GlobalTheory.cubeSign {x, y} i = 0 := by
    intro x y hxy
    rw [Finset.sum_pair hxy.ne]
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, hxy, hxy.not_gt]
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h
  rcases lt_or_gt_of_ne hxy with h' | h'
  · exact key x y h'
  · rw [Finset.pair_comm]; exact key y x h'

theorem δ_zero_one : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), δ F 0 (fun _ => 1) = 0 := by
  intro κ _ R _ F
  funext t
  rw [δ_apply]
  simp only [map_one, Pi.zero_apply]
  rw [← Finset.sum_smul, Finset.sum_coe_sort t.1 (fun i => GlobalTheory.cubeSign t.1 i),
    sum_cubeSign_card_two t.1 t.2, zero_smul]

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsOneCoboundaryComm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPosetDegreeOne
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)


open Classical in
def val {p : ℕ} (c : CC F p) (s : Finset κ) (b : (NE κ)ᵒᵖ) : F.obj b :=
  if h : s.card = p + 1 ∧ s ⊆ sub b then
    mp F (homOf (a := ne s (card_nonempty ⟨s, h.1⟩)) (b := b) h.2) (c ⟨s, h.1⟩) else 0

theorem val_eq {p : ℕ} (c : CC F p) (s : {s : Finset κ // s.card = p + 1}) (b : (NE κ)ᵒᵖ)
    (f : ne s.1 (card_nonempty s) ⟶ b) : mp F f (c s) = val F c s.1 b := by
  unfold val
  obtain ⟨s, hs⟩ := s
  have hsub : s ⊆ sub b := sub_subset f
  rw [dite_eq_left (⟨hs, hsub⟩ : s.card = p + 1 ∧ s ⊆ sub b)]
  exact congrArg (fun φ => mp F φ (c ⟨s, hs⟩)) (Subsingleton.elim _ _)

theorem mp_val {p : ℕ} (c : CC F p) (s : Finset κ) {b d : (NE κ)ᵒᵖ} (g : b ⟶ d)
    (h : s.card = p + 1) (hs : s ⊆ sub b) : mp F g (val F c s b) = val F c s d := by
  rw [← val_eq F c ⟨s, h⟩ b (homOf hs), ← mp_comp, val_eq]

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (c : CC F 1) {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) :
    e1 F c a b f = if mn b < mn a then - val F c {mn b, mn a} b else 0 := by
  simp only [e1, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
    exact congrArg Neg.neg (val_eq F c ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ b _)
  · rfl

theorem alternatingToOrderedCechDegreeTwo_apply_valueAtSubset (c : CC F 2) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    e2 F c a b d f g = if mn d < mn b ∧ mn b < mn a then - val F c {mn d, mn b, mn a} d else 0 := by
  simp only [e2, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
    exact congrArg Neg.neg (val_eq F c ⟨{mn d, mn b, mn a}, card_three h.1 h.2⟩ d _)
  · rfl

theorem val_δ {p : ℕ} (c : CC F p) (t : Finset κ) (d : (NE κ)ᵒᵖ) (h : t.card = p + 1 + 1)
    (ht : t ⊆ sub d) :
    val F (δ F p c) t d = ∑ i ∈ t, GlobalTheory.cubeSign t i • val F c (t.erase i) d := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← val_eq F (δ F p c) ⟨t, h⟩ d (homOf ht), δ_apply, map_sum,
    ← Finset.sum_coe_sort t (fun i => GlobalTheory.cubeSign t i • val F c (t.erase i) d)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, ← mp_comp, val_eq]

theorem val_δ_three (c : CC F 1) {x y z : κ} (h₁ : x < y) (h₂ : y < z) (d : (NE κ)ᵒᵖ)
    (ht : ({x, y, z} : Finset κ) ⊆ sub d) :
    val F (δ F 1 c) {x, y, z} d = val F c {y, z} d - val F c {x, z} d + val F c {x, y} d := by
  have h₃ := h₁.trans h₂
  rw [val_δ F c _ d (card_three h₁ h₂) ht, Finset.sum_insert (by simp [h₁.ne, h₃.ne]),
    Finset.sum_pair h₂.ne]
  have e₁ : ({x, y, z} : Finset κ).erase x = {y, z} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₁.ne', h₃.ne']
  have e₂ : ({x, y, z} : Finset κ).erase y = {x, z} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₁.ne, h₂.ne']
  have e₃ : ({x, y, z} : Finset κ).erase z = {x, y} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₃.ne, h₂.ne]
  have s₁ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) x = 1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₁.not_gt, h₃.not_gt]
  have s₂ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) y = -1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₁, h₂.not_gt]
  have s₃ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) z = 1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₃, h₂, Finset.card_pair h₁.ne]
  rw [e₁, e₂, e₃, s₁, s₂, s₃]
  simp only [one_smul, neg_smul]
  ring

theorem orderedCechToCatCochainsOne_coboundary_comm {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (c : CC F 1) : d1 F (e1 F c) = e2 F (δ F 1 c) := by
  funext a b d f g
  rw [d1_apply, orderedCechToCatCochainsOne_apply_valueAtSubset, orderedCechToCatCochainsOne_apply_valueAtSubset, orderedCechToCatCochainsOne_apply_valueAtSubset, alternatingToOrderedCechDegreeTwo_apply_valueAtSubset]
  rcases (mn_le_of_hom f).lt_or_eq with h₂ | h₂ <;> rcases (mn_le_of_hom g).lt_or_eq with h₁ | h₁
  · rw [if_pos h₂, if_pos h₁, if_pos (h₁.trans h₂), if_pos ⟨h₁, h₂⟩, map_neg,
      mp_val F c _ g (Finset.card_pair h₂.ne) (pair_subset f),
      val_δ_three F c h₁ h₂ d (triple_subset f g)]
    ring
  · rw [if_pos h₂, if_neg h₁.not_lt, if_pos (h₁ ▸ h₂), if_neg (fun h => h₁.not_lt h.1), map_neg,
      mp_val F c _ g (Finset.card_pair h₂.ne) (pair_subset f), h₁]
    ring
  · rw [if_neg h₂.not_lt, if_pos h₁, if_pos (h₂ ▸ h₁), if_neg (fun h => h₂.not_lt h.2), map_zero, h₂]
    ring
  · rw [if_neg h₂.not_lt, if_neg h₁.not_lt, if_neg (h₁.trans h₂).not_lt,
      if_neg (fun h => h₂.not_lt h.2), map_zero]
    ring

end GlobalTheory.CechPosetDegreeOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdealExtensionPrime
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.origin_ideal_extension_prime : ∀ (A' : Type) [CommRing A'] [HenselianLocalRing A'] [IsSepClosed (ResidueField A')]
    (𝔭 : Ideal A') [𝔭.IsPrime] (E : Type) [CommRing E] [Algebra (Polynomial A') E]
    [Algebra.Etale (Polynomial A') E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A') E) = GlobalTheory.KeyOriginCut.originIdeal A' →
    (𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)).IsPrime := by
  first | (exact @GlobalTheory.OriginPrimes.origin_primes) | (exact GlobalTheory.OriginPrimes.origin_primes) | (intros; apply GlobalTheory.OriginPrimes.origin_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique : ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k → ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν → ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h := by
  first
  | exact @GlobalTheory.EtC.TwPairUniq.main
  | exact GlobalTheory.EtC.TwPairUniq.main
  | (intros; apply GlobalTheory.EtC.TwPairUniq.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedDualRegularFormsFiniteCoverStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDual_regularForms_finiteCover : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ p q : ℕ, p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K (rB k K x I) p, Algebra.trace F K (τ (a * y)) ∈ omA k x I) ↔ y ∈ omB k K (rB k K x I) q := by
  first | (exact @GlobalTheory.PD.twistedDual_omB) | (exact GlobalTheory.PD.twistedDual_omB) | (intros; apply GlobalTheory.PD.twistedDual_omB  <;> assumption)
end

