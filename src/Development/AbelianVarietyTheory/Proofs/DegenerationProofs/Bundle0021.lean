module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingEquivPowerSeriesOfComplete
section
open IsLocalRing

namespace GlobalTheory.ArcAvoid

theorem exists_ringEquiv_powerSeries_of_complete {k O : Type*} [Field k] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (ι : k →+* O)
    (hι : Function.Surjective ((residue O).comp ι)) :
    ∃ e : PowerSeries k ≃+* O, ∀ a, e (PowerSeries.C a) = ι a := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨ev, hev⟩ := exists_algHom_powerSeries_apply_X_of_isAdicComplete (maximalIdeal O)
    (π := π) (by rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π)
  let ψ : PowerSeries k →+* O := (ev : PowerSeries O →+* O).comp (PowerSeries.map ι)
  have hX : ψ PowerSeries.X = π := by simp [ψ, hev]
  have hC : ∀ a, ψ (PowerSeries.C a) = ι a := fun a => by
    simpa [ψ] using ev.commutes (ι a)
  have hmap : (Ideal.span {(PowerSeries.X : PowerSeries k)}).map ψ = maximalIdeal O := by
    rw [Ideal.map_span, Set.image_singleton, hX, hπ.maximalIdeal_eq]
  have hH : IsHausdorff ((Ideal.span {(PowerSeries.X : PowerSeries k)}).map ψ) O := by
    rw [hmap]; infer_instance
  have hs : Function.Surjective ψ := by
    refine surjective_of_mk_map_comp_surjective (I := Ideal.span {PowerSeries.X}) ψ ?_
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hι (residue O y)
    refine ⟨PowerSeries.C a, ?_⟩
    rw [RingHom.comp_apply, hC, Ideal.Quotient.eq, hmap]
    exact Ideal.Quotient.eq.mp ha
  have hi : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 (PowerSeries.X_irreducible (R := k))
    rw [map_mul, map_pow, (u.isUnit.map _).mul_right_eq_zero, hX] at ha
    exact hπ.ne_zero (eq_zero_of_pow_eq_zero ha)
  exact ⟨RingEquiv.ofBijective ψ ⟨hi, hs⟩, hC⟩

theorem exists_ringHom_powerSeries_of_dvr {k V : Type*} [Field k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (ι : k →+* V) (hι : Function.Surjective ((residue V).comp ι)) :
    ∃ φ : V →+* PowerSeries k, Function.Injective φ ∧ (∀ a, φ (ι a) = PowerSeries.C a) ∧
      ∀ v, v ∈ maximalIdeal V ↔ PowerSeries.constantCoeff (φ v) = 0 := by
  let O := AdicCompletion (maximalIdeal V) V
  obtain ⟨e, he⟩ := exists_ringEquiv_powerSeries_of_complete ((algebraMap V O).comp ι) (by
    intro y
    obtain ⟨z, rfl⟩ := (AdicCompletion.residueField_map_bijective V).2 y
    obtain ⟨a, rfl⟩ := hι z
    exact ⟨a, rfl⟩)
  refine ⟨(e.symm : O →+* PowerSeries k).comp (algebraMap V O),
    e.symm.injective.comp (algebraMap_adicCompletion_injective_of_dvr V), fun a => ?_, fun v => ?_⟩
  · exact e.symm_apply_eq.mpr (he a).symm
  · rw [mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (algebraMap V O),
      ← isUnit_map_iff e.symm, PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
    rfl


open Polynomial in
theorem surjective_residue_of_isAlgebraic {k V : Type*} [Field k] [IsAlgClosed k] [CommRing V]
    [IsDomain V] [IsLocalRing V] [Algebra k[X] V] [Algebra.IsAlgebraic k[X] V]
    [FaithfulSMul k[X] V] (hX : algebraMap k[X] V X ∈ maximalIdeal V) :
    Function.Surjective ((residue V).comp ((algebraMap k[X] V).comp C)) := by
  classical
  letI : Algebra k (ResidueField V) := ((residue V).comp ((algebraMap k[X] V).comp C)).toAlgebra
  have hc : (algebraMap k (ResidueField V)).comp (constantCoeff : k[X] →+* k) =
      (residue V).comp (algebraMap k[X] V) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [RingHom.algebraMap_toAlgebra]
    · simpa using ((residue_eq_zero_iff _).mpr hX).symm
  have : Algebra.IsAlgebraic k (ResidueField V) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := k[X]) x
    have h1 := aeval_primPart_eq_zero hp0 hp
    refine ⟨p.primPart.map constantCoeff, fun h => ?_, ?_⟩
    · refine Polynomial.not_isUnit_X (R := k) (p.isPrimitive_primPart X ?_)
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (fun q => q.coeff i) h
      simpa [X_dvd_iff] using this
    · rw [aeval_def, eval₂_map, hc, ← hom_eval₂, ← aeval_def, h1, map_zero]⟩
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := ResidueField V)).2


open Polynomial in
theorem exists_injective_of_height_le_one {k B : Type*} [Field k] [IsAlgClosed k] [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (m : Ideal B) [hm : m.IsMaximal]
    (h1 : m.height ≤ 1) :
    ∃ φ : B →ₐ[k] PowerSeries k, Function.Injective φ ∧
      ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by
  rcases eq_or_ne m ⊥ with rfl | hne
  · letI : Field B := (Ring.isField_iff_maximal_bot.mpr hm).toField
    have : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
    let e : k ≃ₐ[k] B :=
      .ofBijective (Algebra.ofId k B) IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨(Algebra.ofId k (PowerSeries k)).comp e.symm, RingHom.injective _, fun b => ?_⟩
    simp [Algebra.ofId_apply]
  obtain ⟨t, htm, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  letI : Algebra k[X] B := (aeval t : k[X] →ₐ[k] B).toRingHom.toAlgebra
  have hal : ∀ p : k[X], algebraMap k[X] B p = aeval t p := fun _ => rfl
  have : IsScalarTower k k[X] B := .of_algebraMap_eq fun a => by simp [hal]
  have : Algebra.FiniteType k[X] B := .of_restrictScalars_finiteType k k[X] B
  have hinj : Function.Injective (algebraMap k[X] B) := by
    refine transcendental_iff_injective.mp fun halg => hm.ne_top ?_
    exact m.eq_top_of_isUnit_mem htm (halg.isIntegral.isUnit ht0)
  obtain ⟨K', _, _, _, V, φ, hφ, hφi, hφm⟩ := exists_valuationSubring_of_height_le_one
    (O := k[X]) (K := FractionRing k[X]) hinj m h1 X X_ne_zero (by simpa [hal] using htm)
  letI : Algebra k[X] V := (φ.comp (algebraMap k[X] B)).toAlgebra
  letI : Algebra k[X] K' :=
    ((algebraMap (FractionRing k[X]) K').comp (algebraMap k[X] (FractionRing k[X]))).toAlgebra
  have : IsScalarTower k[X] (FractionRing k[X]) K' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k[X] V K' := .of_algebraMap_eq fun a => (hφ a).symm
  have : FaithfulSMul k[X] V := (faithfulSMul_iff_algebraMap_injective _ _).mpr (hφi.comp hinj)
  have halg : Algebra.IsAlgebraic k[X] K' :=
    (IsFractionRing.comap_isAlgebraic_iff (A := k[X]) (K := FractionRing k[X]) (C := K')).mpr
      inferInstance
  have : Algebra.IsAlgebraic k[X] V :=
    .of_injective (IsScalarTower.toAlgHom k[X] V K') Subtype.val_injective
  have hXV : algebraMap k[X] V X ∈ maximalIdeal V := by
    change algebraMap k[X] B X ∈ (maximalIdeal V).comap φ
    simpa [hal, hφm] using htm
  let W : Subalgebra k[X] K' :=
    { V.toSubring with algebraMap_mem' := fun r => (hφ r) ▸ (φ (algebraMap k[X] B r)).2 }
  have hVn : IsNoetherianRing V := (krullAkizuki (FractionRing k[X]) W).1
  have hnf : ¬ IsField V := by
    rw [isField_iff_maximalIdeal_eq]
    intro h
    rw [h] at hXV
    exact X_ne_zero ((FaithfulSMul.algebraMap_eq_zero_iff k[X] V).mp hXV)
  have hval : ValuationRing V := inferInstance
  have : IsDiscreteValuationRing V := ((IsDiscreteValuationRing.TFAE V hnf).out 2 1).mp hval
  obtain ⟨ψ, hψi, hψC, hψm⟩ :=
    exists_ringHom_powerSeries_of_dvr _ (surjective_residue_of_isAlgebraic hXV)
  refine ⟨{ ψ.comp φ with commutes' := fun a => ?_ }, hψi.comp hφi, fun b => ?_⟩
  · have := hψC a
    rw [IsScalarTower.algebraMap_apply k k[X] B]
    exact this
  · rw [← hφm]
    exact hψm (φ b)

theorem exists_algHom_powerSeries_ne_zero :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (m : Ideal B), m.IsMaximal → ∀ f : B, f ≠ 0 →
      ∃ φ : B →ₐ[k] PowerSeries k, φ f ≠ 0 ∧
        ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by
  intro k _ _ B _ _ _ _ m hm f hf
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨q, hqf, hqm, hht⟩ := exists_mem_height_map_le_one m (PrimeSpectrum.basicOpen f).isOpen
    ⟨⊥, hf, bot_le⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by
      rw [e, Ideal.comap_top] at hcomap
      exact hm.ne_top hcomap.symm
  obtain ⟨φ, hφi, hφm⟩ := exists_injective_of_height_le_one (k := k) _ hht
  refine ⟨φ.comp (Ideal.Quotient.mkₐ k q.asIdeal), fun h => hqf ?_, fun b => ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.mp (hφi (h.trans (map_zero φ).symm))
  · conv_lhs => rw [← hcomap]
    exact hφm _

end GlobalTheory.ArcAvoid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStalkDerivationOfIsPullback
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.StalkDer
variable {K : Type} [Field K] {P : Scheme.{0}} {X : Over (Sp K)}

def gm (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) :
    Γ(X.left, V) →+* P.presheaf.stalk z :=
  (P.presheaf.germ (f ⁻¹ᵁ V) z hz).hom.comp (f.app V).hom

theorem germ_appLE (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (W : P.Opens) (h : W ≤ f ⁻¹ᵁ V)
    (hz : z ∈ W) (u : Γ(X.left, V)) :
    (P.presheaf.germ W z hz).hom ((f.appLE V W h).hom u) = gm f z V (h hz) u :=
  TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE h) z hz _

theorem gm_res (f : P ⟶ X.left) (z : P) (V V' : X.left.Opens) (h : V' ≤ V) (hz : z ∈ f ⁻¹ᵁ V')
    (u : Γ(X.left, V)) :
    gm f z V' hz ((X.left.presheaf.map (homOfLE h).op).hom u) = gm f z V (h hz) u := by
  rw [← germ_appLE f z V' _ le_rfl hz, ← germ_appLE f z V (f ⁻¹ᵁ V') (fun _ hx => h hx) hz]
  congr 1
  exact congrArg (fun φ => φ.hom u) (f.map_appLE le_rfl (homOfLE h).op)

def gmDual (D : VF X) (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) :
    Γ(X.left, V) →+* DualNumber (P.presheaf.stalk z) where
  toFun b := (gm f z V hz b, gm f z V hz (D.D V b))
  map_one' := TrivSqZeroExt.ext (map_one _) (by
    show gm f z V hz (D.D V 1) = 0
    have := D.const V 1
    rw [map_one] at this
    rw [this, map_zero])
  map_mul' a b := TrivSqZeroExt.ext (map_mul _ a b) (by
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    show gm f z V hz (D.D V (a * b)) = gm f z V hz a * gm f z V hz (D.D V b) +
      gm f z V hz (D.D V a) * gm f z V hz b
    rw [D.leibniz, map_add (f := _), map_mul, map_mul]; ring)
  map_zero' := TrivSqZeroExt.ext (map_zero _) (by
    show gm f z V hz (D.D V 0) = 0
    rw [map_zero, map_zero])
  map_add' a b := TrivSqZeroExt.ext (map_add _ a b) (by
    show gm f z V hz (D.D V (a + b)) = gm f z V hz (D.D V a) + gm f z V hz (D.D V b)
    rw [map_add (f := _), map_add (f := _)])

theorem gmDual_res (D : VF X) (f : P ⟶ X.left) (z : P) (V V' : X.left.Opens) (h : V' ≤ V)
    (hz : z ∈ f ⁻¹ᵁ V') (u : Γ(X.left, V)) :
    gmDual D f z V' hz ((X.left.presheaf.map (homOfLE h).op).hom u) = gmDual D f z V (h hz) u :=
  TrivSqZeroExt.ext (gm_res f z V V' h hz u) (by
    show gm f z V' hz (D.D V' _) = gm f z V (h hz) (D.D V u)
    rw [D.res, gm_res])

theorem extend (D : VF X) (f : P ⟶ X.left) (z : P)
    (Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z)) (V₀ : X.left.Opens)
    (hV₀ : IsAffineOpen V₀) (hz₀ : z ∈ f ⁻¹ᵁ V₀)
    (H : ∀ u, Φ (gm f z V₀ hz₀ u) = gmDual D f z V₀ hz₀ u)
    (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) (u : Γ(X.left, V)) :
    Φ (gm f z V hz u) = gmDual D f z V hz u := by
  obtain ⟨r, hr, hzr⟩ := hV₀.exists_basicOpen_le (V := V) ⟨f z, hz⟩ hz₀
  have hzr' : z ∈ f ⁻¹ᵁ X.left.basicOpen r := hzr
  have := hV₀.isLocalization_basicOpen r
  have e : Φ.comp (gm f z _ hzr') = gmDual D f z _ hzr' := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    refine RingHom.ext fun a => ?_
    have h1 := gm_res f z V₀ _ (X.left.basicOpen_le r) hzr' a
    have h2 := gmDual_res D f z V₀ _ (X.left.basicOpen_le r) hzr' a
    exact ((congrArg Φ h1).trans (H a)).trans h2.symm
  rw [← gm_res f z V _ hr hzr', ← gmDual_res D f z V _ hr hzr']
  exact RingHom.congr_fun e _

theorem gmDual_const (D : VF X) (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V)
    (c : Γ(Sp K, ⊤)) :
    gmDual D f z V hz ((X.hom.appLE ⊤ V le_top).hom c) =
      TrivSqZeroExt.inl ((P.presheaf.germ ⊤ z trivial).hom (((f ≫ X.hom).appLE ⊤ ⊤ le_top).hom c)) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show gm f z V hz _ = (P.presheaf.germ ⊤ z trivial).hom _
    rw [← germ_appLE f z V _ le_rfl hz,
      ← TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)) z hz]
    congr 1
    have e1 := Scheme.Hom.appLE_comp_appLE f X.hom ⊤ V (f ⁻¹ᵁ V) le_top le_rfl
    have e2 := (f ≫ X.hom).appLE_map (U := ⊤) (V := ⊤) le_top (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op
    exact congrArg (fun φ => φ.hom c) (e1.trans e2.symm)
  · show gm f z V hz (D.D V _) = 0
    have e : (X.hom.appLE ⊤ V le_top).hom c =
        cstK X V ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom c) := by
      show _ = (X.hom.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom _)
      congr 1
      exact (congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id).symm
    rw [e, D.const, map_zero]

theorem exists_dual {Y : Over (Sp K)} (p : P ⟶ X.left) (q : P ⟶ Y.left)
    (H : IsPullback p q X.hom Y.hom) (D : VF X) (E : VF Y) (z : P) :
    ∃ Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z), (∀ a, (Φ a).fst = a) ∧
      (∀ V hz u, Φ (gm p z V hz u) = gmDual D p z V hz u) ∧
      ∀ V hz u, Φ (gm q z V hz u) = gmDual E q z V hz u := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p z)) isOpen_univ
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ := Y.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (q z)) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hW : IsAffineOpen W := hW
  have hzU : z ∈ p ⁻¹ᵁ U := hzU
  have hzW : z ∈ q ⁻¹ᵁ W := hzW
  have hO : IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) := by
    have : IsAffine _ := isAffineOpen_top (Sp K)
    have : IsAffine _ := hU
    have : IsAffine _ := hW
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top
      rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := W) (UX := U) le_top
    le_top rfl).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hW hU)
  have hz : z ∈ p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W := ⟨hzU, hzW⟩
  have w : X.hom.appLE ⊤ U le_top ≫ CommRingCat.ofHom (gmDual D p z U hzU) =
      Y.hom.appLE ⊤ W le_top ≫ CommRingCat.ofHom (gmDual E q z W hzW) := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    refine (gmDual_const D p z U hzU c).trans (Eq.trans ?_ (gmDual_const E q z W hzW c).symm)
    simp only [H.w]
  let φ := po.desc _ _ w
  have h1 : ∀ u, φ.hom ((p.appLE U _ inf_le_left).hom u) = gmDual D p z U hzU u := fun u =>
    congrArg (fun φ => φ.hom u) (po.inl_desc _ _ w)
  have h2 : ∀ u, φ.hom ((q.appLE W _ inf_le_right).hom u) = gmDual E q z W hzW u := fun u =>
    congrArg (fun φ => φ.hom u) (po.inr_desc _ _ w)
  have hf : φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom (P.presheaf.stalk z) (P.presheaf.stalk z)
      (P.presheaf.stalk z)).toRingHom = P.presheaf.germ _ z hz := by
    refine po.hom_ext (CommRingCat.hom_ext (RingHom.ext fun u => ?_))
      (CommRingCat.hom_ext (RingHom.ext fun u => ?_))
    · exact (congrArg TrivSqZeroExt.fst (h1 u)).trans (germ_appLE p z U _ inf_le_left hz u).symm
    · exact (congrArg TrivSqZeroExt.fst (h2 u)).trans (germ_appLE q z W _ inf_le_right hz u).symm
  have hf' : ∀ b, (φ.hom b).fst = (P.presheaf.germ _ z hz).hom b := fun b =>
    congrArg (fun φ => φ.hom b) hf
  letI := P.presheaf.algebra_section_stalk (⟨z, hz⟩ : (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W : P.Opens))
  have loc := hO.isLocalization_stalk ⟨z, hz⟩
  have hu : ∀ s : (hO.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl, IsUnit (φ.hom s) := fun s => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hf']
    exact IsLocalization.map_units (P.presheaf.stalk z) s
  let Φ : P.presheaf.stalk z →+* DualNumber (P.presheaf.stalk z) := IsLocalization.lift hu
  have hΦ : ∀ b, Φ ((P.presheaf.germ _ z hz).hom b) = φ.hom b := fun b =>
    IsLocalization.lift_eq hu b
  refine ⟨Φ, fun a => ?_, extend D p z Φ U hU hzU fun u => ?_, extend E q z Φ W hW hzW fun u => ?_⟩
  · have : (TrivSqZeroExt.fstHom (P.presheaf.stalk z) (P.presheaf.stalk z)
        (P.presheaf.stalk z)).toRingHom.comp Φ = RingHom.id _ := by
      apply IsLocalization.ringHom_ext (hO.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
      refine RingHom.ext fun b => ?_
      exact (congrArg TrivSqZeroExt.fst (hΦ b)).trans (hf' b)
    exact congrArg (fun f => f a) this
  · rw [← germ_appLE p z U _ inf_le_left hz, hΦ, h1]
  · rw [← germ_appLE q z W _ inf_le_right hz, hΦ, h2]

end GlobalTheory.SS.StalkDer

namespace GlobalTheory.SS

open StalkDer in
theorem exists_stalk_derivation_of_isPullback : ∀ (K : Type) [Field K] (P X Y : Over (Sp K)) (p : P.left ⟶ X.left) (q : P.left ⟶ Y.left), IsPullback p q X.hom Y.hom → ∀ (D : VF X) (z : P.left), ∃ δ : P.left.presheaf.stalk z →+ P.left.presheaf.stalk z, (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ (∀ (V : X.left.Opens) (W : P.left.Opens) (h : W ≤ p ⁻¹ᵁ V) (hz : z ∈ W) (u : Γ(X.left, V)), δ ((P.left.presheaf.germ W z hz).hom ((p.appLE V W h).hom u)) = (P.left.presheaf.germ W z hz).hom ((p.appLE V W h).hom (D.D V u))) ∧ ∀ (V : Y.left.Opens) (W : P.left.Opens) (h : W ≤ q ⁻¹ᵁ V) (hz : z ∈ W) (u : Γ(Y.left, V)), δ ((P.left.presheaf.germ W z hz).hom ((q.appLE V W h).hom u)) = 0 := by
  intro K _ P X Y p q H D z
  obtain ⟨Φ, h0, h1, h2⟩ := exists_dual p q H D (VF.zero Y) z
  refine ⟨⟨⟨fun x => (Φ x).snd, by simp⟩, fun a b => by simp⟩, fun a b => ?_,
    fun V W h hz u => ?_, fun V W h hz u => ?_⟩
  · show (Φ (a * b)).snd = a * (Φ b).snd + b * (Φ a).snd
    rw [map_mul, DualNumber.snd_mul, h0, h0]; ring
  · rw [germ_appLE, germ_appLE]
    exact congrArg TrivSqZeroExt.snd (h1 V (h hz) u)
  · rw [germ_appLE]
    exact (congrArg TrivSqZeroExt.snd (h2 V (h hz) u)).trans (map_zero (gm q z V (h hz)))
end GlobalTheory.SS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVf
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.StalkGlue

theorem sec_ext {X : Scheme.{0}} (U : X.Opens) (s t : Γ(X, U))
    (h : ∀ (x : X) (hx : x ∈ U), (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom t) :
    s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t h

theorem germ_map {X : Scheme.{0}} {U V : X.Opens} (i : V ⟶ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom ((X.presheaf.map i.op).hom s) =
      (X.presheaf.germ U x (i.le hx)).hom s :=
  TopCat.Presheaf.germ_res_apply X.presheaf i x hx s

theorem exists_section {X : Scheme.{0}} (U : X.Opens) (g : ∀ (x : X), x ∈ U → X.presheaf.stalk x)
    (H : ∀ x : X, x ∈ U → ∃ (W : X.Opens) (h : W ≤ U) (t : Γ(X, W)), x ∈ W ∧
      ∀ (y : X) (hy : y ∈ W), g y (h hy) = (X.presheaf.germ W y hy).hom t) :
    ∃ s : Γ(X, U), ∀ (x : X) (hx : x ∈ U), (X.presheaf.germ U x hx).hom s = g x hx := by
  choose W hW t hx ht using H
  have hcov : U ≤ iSup (fun p : U => W p.1 p.2) := fun x hxU =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun p : U => W p.1 p.2) U
    (fun p => homOfLE (hW p.1 p.2)) hcov (fun p => t p.1 p.2) (by
      intro p q
      apply sec_ext (W p.1 p.2 ⊓ W q.1 q.2)
      intro y hy
      exact (germ_map (TopologicalSpace.Opens.infLELeft _ _) y hy _).trans
        (((ht p.1 p.2 y hy.1).symm.trans (ht q.1 q.2 y hy.2)).trans
          (germ_map (TopologicalSpace.Opens.infLERight _ _) y hy _).symm))
  refine ⟨s, fun x hxU => ?_⟩
  have h1 : (X.presheaf.map (homOfLE (hW x hxU)).op).hom s = t x hxU := hs ⟨x, hxU⟩
  rw [ht x hxU x (hx x hxU), ← h1]
  exact (germ_map (homOfLE (hW x hxU)) x (hx x hxU) s).symm

theorem exists_vf : ∀ (K : Type) [Field K] (X : Over (Sp K)) (δ : ∀ x : X.left, X.left.presheaf.stalk x →+ X.left.presheaf.stalk x), (∀ x a b, δ x (a * b) = a * δ x b + b * δ x a) → (∀ (U : X.left.Opens) (x : X.left) (hx : x ∈ U) (c : K), δ x ((X.left.presheaf.germ U x hx).hom (cstK X U c)) = 0) → (∀ (U : X.left.Opens) (s : Γ(X.left, U)) (x : X.left), x ∈ U → ∃ (W : X.left.Opens) (h : W ≤ U) (t : Γ(X.left, W)), x ∈ W ∧ ∀ (y : X.left) (hy : y ∈ W), δ y ((X.left.presheaf.germ U y (h hy)).hom s) = (X.left.presheaf.germ W y hy).hom t) → ∃ D : VF X, ∀ (U : X.left.Opens) (s : Γ(X.left, U)) (x : X.left) (hx : x ∈ U), (X.left.presheaf.germ U x hx).hom (D.D U s) = δ x ((X.left.presheaf.germ U x hx).hom s) := by
  intro K _ X δ hL hc hloc
  choose D hD using fun (U : X.left.Opens) (s : Γ(X.left, U)) =>
    exists_section U (fun x hx => δ x ((X.left.presheaf.germ U x hx).hom s)) (hloc U s)
  refine ⟨⟨fun U => AddMonoidHom.mk' (D U) (fun a b => ?_), fun U a b => ?_, fun U c => ?_,
    fun U V h a => ?_⟩, fun U s x hx => hD U s x hx⟩
  · apply sec_ext
    intro x hx
    simp only [map_add (f := _), hD]
  · apply sec_ext
    intro x hx
    simp only [AddMonoidHom.mk'_apply, map_add (f := _), map_mul, hD, hL]
  · apply sec_ext
    intro x hx
    simp only [AddMonoidHom.mk'_apply, map_zero, hD, hc]
  · apply sec_ext
    intro x hx
    simp only [AddMonoidHom.mk'_apply]
    rw [hD, germ_map, germ_map, hD]

end GlobalTheory.SS.StalkGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusHomEqOneOfNoCocharacter
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem splitTorus_hom_eq_one_of_no_cocharacter :
    ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X], (∀ f : Gm S ⟶ B, IsMonHom f → f = 1) →
      ∀ u : splitTorus S X ⟶ B, IsMonHom u → u = 1 := by
  intro S B _ X _ _ _ h u hu
  classical
  let b := Module.Free.chooseBasis ℤ X
  let l : _ → (X →+ ULift.{0} ℤ) := fun i =>
    (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).symm.toAddMonoidHom.comp (b.coord i).toAddMonoidHom
  let c : _ → (ULift.{0} ℤ →+ X) := fun i =>
    (zmultiplesHom X (b i)).comp (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddMonoidHom
  have h1 : ∀ i, SplitTorus.torusMap S ((c i).comp (l i)) ≫ u = 1 := fun i => by
    have e : SplitTorus.torusMap S (l i) ≫ u = 1 := h _ (inferInstanceAs
      (IsMonHom (SplitTorus.torusMap S (l i) ≫ u)))
    rw [SplitTorus.torusMap_comp, Category.assoc, e, MonObj.comp_one]
  have h2 : ∀ s : Finset (Module.Free.ChooseBasisIndex ℤ X),
      SplitTorus.torusMap S (∑ i ∈ s, (c i).comp (l i)) ≫ u = 1 := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, SplitTorus.torusMap_zero, MonObj.one_comp]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, SplitTorus.torusMap_add, MonObj.mul_comp, h1, ih, _root_.mul_one]
  have h3 : (∑ i, (c i).comp (l i)) = AddMonoidHom.id X := by
    ext x
    rw [AddMonoidHom.finsetSum_apply]
    simpa [c, l] using b.sum_repr x
  have := h2 Finset.univ
  rwa [h3, SplitTorus.torusMap_id, Category.id_comp] at this

end GlobalTheory.SS
end

