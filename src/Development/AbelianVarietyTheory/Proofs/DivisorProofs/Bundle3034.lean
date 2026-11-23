module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModuliObjectSpreadNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenPartClassifiedMonomialBoundaryFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.OpenPart

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem pow_eq_one_of_left_eq {S T : Scheme.{0}} {G : Over S} [GrpObj G] {a b : T ⟶ S} (h : a = b)
    (u : Over.mk a ⟶ G) (v : Over.mk b ⟶ G) (huv : u.left = v.left) {n : ℕ} (hu : u ^ n = 1) : v ^ n = 1 := by
  subst h
  obtain rfl : u = v := Over.OverMorphism.ext huv
  exact hu

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem torsRat_of_point {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E))
    {A : Type} [CommRing A] [IsDomain A] {K₀ : Type} [Field K₀] (gA : A →+* K₀) (ρ : K₀ →+* FractionRing A)
    (hρ : ρ.comp gA = algebraMap A (FractionRing A)) (tO : SAB H (Sp A)) (tK : SAB H (Sp K₀))
    (k : SABMap tK tO (spMap gA)) (y : Sp K₀ ⟶ Xo.XF c) (mK : SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) :
    GlobalTheory.TChart.TorsRat tO.G l.M' := by
  intro K _ _ κ x hx
  let κ' : K₀ →+* K := κ.comp ρ
  have e₀ : spMap κ' ≫ spMap gA = spMap κ ≫ jK A := by
    rw [spMap_comp', spMap_comp']
    show spMap (κ.comp (ρ.comp gA)) = _
    rw [hρ]
  have hw : x.left ≫ tO.G.hom = spMap κ' ≫ spMap gA := (Over.w x).trans e₀.symm
  let xK : Over.mk (spMap κ') ⟶ tK.G :=
    Over.homMk (k.cart.1.lift x.left (spMap κ') hw) (k.cart.1.lift_snd _ _ _)
  have hxK : xK ^ l.M' = 1 := by
    have hpush : pushHom k.cart (Over.mk (spMap κ')) xK ^ l.M' = 1 :=
      pow_eq_one_of_left_eq e₀.symm x _ (k.cart.1.lift_fst _ _ _).symm hx
    apply (fun (u v : Over.mk (spMap κ') ⟶ tK.G) (e : pushHom k.cart (Over.mk (spMap κ')) u = pushHom k.cart (Over.mk (spMap κ')) v) =>
      Over.OverMorphism.ext (k.cart.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])))
    rw [map_pow, hpush, map_one]
  let x' := pushHom mK.cart (Over.mk (spMap κ')) xK
  have hx' : x' ^ l.M' = 1 := by rw [← map_pow, hxK, map_one]
  obtain ⟨x₀, -, hx₀⟩ := _root_.GlobalTheory.XFTorsion.torsion_rational Xo c φ K₀ K κ' y x' hx'
  have w₀ : x₀.left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ (y ≫ pullback.fst _ _) := by
    rw [Category.id_comp]; exact Over.w x₀
  let s₀ := mK.cart.1.lift x₀.left (𝟙 _) w₀
  have hs₀ : s₀ ≫ tK.G.hom = 𝟙 _ := mK.cart.1.lift_snd _ _ _
  have hK : xK.left = spMap κ' ≫ s₀ := by
    apply mK.cart.1.hom_ext
    · rw [Category.assoc, mK.cart.1.lift_fst]
      exact hx₀
    · rw [Category.assoc, hs₀]
      erw [Category.comp_id]
      exact k.cart.1.lift_snd _ _ _
  have hover : (spMap ρ ≫ s₀ ≫ k.φ) ≫ tO.G.hom = jK A := by
    rw [Category.assoc, Category.assoc, k.cart.1.w, ← Category.assoc s₀, hs₀, Category.id_comp, spMap_comp', hρ]
  refine ⟨Over.homMk (spMap ρ ≫ s₀ ≫ k.φ) hover, ?_⟩
  show x.left = spMap κ ≫ spMap ρ ≫ s₀ ≫ k.φ
  have e₁ : spMap κ ≫ spMap ρ = spMap κ' := spMap_comp' _ _
  calc x.left = xK.left ≫ k.φ := (k.cart.1.lift_fst _ _ _).symm
    _ = (spMap κ' ≫ s₀) ≫ k.φ := by rw [hK]
    _ = spMap κ ≫ spMap ρ ≫ s₀ ≫ k.φ := by rw [← e₁]; simp only [Category.assoc]

end GlobalTheory.UCanon.OpenPart

namespace GlobalTheory.UCanon.OpenPart

theorem ring_facts {R : Type} [CommRing R] [IsDomain R] (f : R) (hf : f ≠ 0) (A : Type) [CommRing A] [IsDomain A]
    [Algebra R A] [IsLocalization.Away f A] :
    ∃ (gA : A →+* FractionRing R) (ρ : FractionRing R →+* FractionRing A),
      gA.comp (algebraMap R A) = algebraMap R (FractionRing R) ∧ ρ.comp gA = algebraMap A (FractionRing A) ∧
      ∀ g : A →+* FractionRing R, g.comp (algebraMap R A) = algebraMap R (FractionRing R) → g = gA := by
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hu : IsUnit (algebraMap R (FractionRing R) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf)
  have hgA : (IsLocalization.Away.lift f hu : A →+* FractionRing R).comp (algebraMap R A) = algebraMap R (FractionRing R) :=
    IsLocalization.Away.lift_comp _ hu
  have hinj : Function.Injective ((algebraMap A (FractionRing A)).comp (algebraMap R A)) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective A (FractionRing A)).comp (IsLocalization.injective A hle)
  refine ⟨IsLocalization.Away.lift f hu, IsFractionRing.lift (K := FractionRing R) hinj, hgA, ?_, fun g hg =>
    IsLocalization.ringHom_ext (Submonoid.powers f) (hg.trans hgA.symm)⟩
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  rw [RingHom.comp_assoc, hgA]
  exact RingHom.ext fun r => by rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

end GlobalTheory.UCanon.OpenPart

namespace GlobalTheory.UCanon.OpenPart

theorem openCls : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : MonoFam Xo c φ R, OpenCls C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := id hR
  have hf0 : (∏ i, C.s i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => C.s_ne_zero i
  have hle : Submonoid.powers (∏ i, C.s i) ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away (∏ i, C.s i)) := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing (Localization.Away (∏ i, C.s i)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (∏ i, C.s i)) _ hN
  haveI : IsIntegrallyClosed (Localization.Away (∏ i, C.s i)) :=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (∏ i, C.s i)) hle

  let aR := algebraMap R (Localization.Away (∏ i, C.s i))
  let incl := (IntermediateField.inclusion c.le).toRingHom
  obtain ⟨gA, ρ, hgA, hρ, hgU⟩ := ring_facts _ hf0 (Localization.Away (∏ i, C.s i))
  have eR : spMap gA ≫ spMap aR = jK R := by rw [spMap_comp', hgA]

  obtain ⟨tO, ⟨mO⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap aR) C.t
  obtain ⟨hprop, hamp, hkt⟩ := _root_.GlobalTheory.UCanon.Principal.isProper_relAmple_kTriv_of_psiUnitOn R hR C.t C.P (∏ i, C.s i)
    (fun y => C.mono.psiUnitOn y fun p hp => hp) tO mO

  let s' : Sp (FractionRing R) ⟶ Sp (KA l) := (C.y ≫ pullback.fst _ _) ≫ Xo.s
  obtain ⟨oK, ⟨mK⟩⟩ := (GlobalTheory.UCanon.obj_pull_comp_cancel (D := Dw) (l := l)).1 Xo.s Xo.univ (C.y ≫ pullback.fst _ _) s' rfl
  obtain ⟨t', ⟨m₁⟩, ⟨m₂⟩⟩ := C.gen
  obtain ⟨k₁⟩ := GlobalTheory.TraitOrder.cancel (Category.id_comp _) m₂ mK.toSABMap
  obtain ⟨k₂⟩ := GlobalTheory.TraitOrder.comp (Category.id_comp _) m₁ k₁
  obtain ⟨k₃⟩ := GlobalTheory.TraitOrder.cancel eR mO k₂
  have htors := torsRat_of_point Xo c φ gA ρ hρ tO oK.t k₃ C.y mK.toSABMap
  let b' : c.F →+* Localization.Away (∏ i, C.s i) := aR.comp C.b
  have hs' : s' = spMap gA ≫ spMap (b'.comp incl) := by
    show (C.y ≫ pullback.fst _ _) ≫ Xo.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.y_over, ← eR]
    simp only [Category.assoc, spMap_comp']
  obtain ⟨o, ho, ⟨mo⟩⟩ := _root_.GlobalTheory.ObjSpread.exists_obj Dw l c _ b' tO hprop hamp hkt htors (FractionRing R) gA s' oK hs' k₃
  obtain ⟨fX, ⟨hfs, ⟨mf⟩⟩, -⟩ := Xo.rep (Sp (Localization.Away (∏ i, C.s i))) (spMap (b'.comp incl)) inferInstance o
  have hfs' : fX ≫ Xo.s = spMap b' ≫ spMap incl := hfs.trans (spMap_comp' _ _).symm
  subst ho
  refine ⟨pullback.lift fX (spMap b') hfs', o.t, ⟨mO⟩, ?_, fun g hg => ?_⟩
  · rw [pullback.lift_fst]
    exact ⟨mf.toSABMap⟩
  obtain ⟨g₀, rfl⟩ := Spec.map_surjective g
  have h₁ : CommRingCat.ofHom (algebraMap R (Localization.Away (∏ i, C.s i))) ≫ g₀ =
      CommRingCat.ofHom (algebraMap R (FractionRing R)) := Spec.map_injective (by rw [Spec.map_comp]; exact hg)
  have hg₀ : g₀ = CommRingCat.ofHom gA := by
    have e := hgU g₀.hom (by
      have := congrArg CommRingCat.Hom.hom h₁
      simpa using this)
    rw [← e]
    rfl
  subst hg₀
  obtain ⟨_, _, huK⟩ := Xo.rep (Sp (FractionRing R)) s' inferInstance oK
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    obtain ⟨n₁, -⟩ := ((GlobalTheory.UCanon.obj_pull_comp_cancel (D := Dw) (l := l)).2 Xo.s (spMap (b'.comp incl)) s' Xo.univ o oK
      fX (spMap gA) mf).1 mo
    exact (huK _ ⟨by rw [Category.assoc, hfs]; exact hs'.symm, ⟨n₁⟩⟩).trans (huK _ ⟨rfl, ⟨mK⟩⟩).symm
  · rw [Category.assoc, pullback.lift_snd, C.y_over, ← eR, Category.assoc, spMap_comp' C.b aR]

end GlobalTheory.UCanon.OpenPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfFiniteOfFormallyUnramified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.InteriorChart

theorem bijective_stalkSpecializes {X : Scheme.{0}} {x y : X} (e : x = y) (h : x ⤳ y) :
    Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

theorem isEtaleCompletion_comp {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [CommRing C]
    [IsLocalRing C] (φ : A →+* B) (ρ : B →+* C) [IsLocalHom ρ] (hφ : IsEtaleCompletion φ) (hf : ρ.Flat)
    (hm : (maximalIdeal B).map ρ = maximalIdeal C) (hfin : ρ.Finite) : IsEtaleCompletion (ρ.comp φ) := by
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨RingHom.Flat.comp h1 hf, ?_, ?_⟩
  · rw [← Ideal.map_map, h2, hm]
  · have e : (residue C).comp (ρ.comp φ) = (ResidueField.map ρ).comp ((residue B).comp φ) := by
      rw [← RingHom.comp_assoc, ← ResidueField.map_comp_residue, RingHom.comp_assoc]
    rw [e]
    have hm' : (ResidueField.map ρ).Finite := by
      have h := RingHom.Finite.comp (RingHom.Finite.of_surjective (residue C) residue_surjective) hfin
      rw [← ResidueField.map_comp_residue] at h
      exact RingHom.Finite.of_comp_finite h
    exact RingHom.Finite.comp hm' h3

theorem completedStalk_chart (X : Scheme.{0}) (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    IsEtaleCompletion (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom ∧
      Function.Surjective ((residue (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom) := by
  have fg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let φ := algebraMap (X.presheaf.stalk x) (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
  haveI : IsLocalHom φ := ((IsLocalRing.local_hom_tfae φ).out 1 3).mpr hm.symm.le
  have hres : Function.Surjective ((residue _).comp φ) := by
    intro r
    obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)).2 r
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine ⟨b, ?_⟩
    rw [← ha, RingHom.comp_apply, ResidueField.map_residue]
  have hx : GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x := by
    rw [GlobalTheory.fromSpecCompletedStalk]
    erw [Scheme.Hom.comp_apply]
    have hc : Spec.map (CommRingCat.ofHom φ) (closedPoint _) = closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint φ
    erw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨e, he, hψ⟩ := GlobalTheory.GenFan.stalk_factor_eq hx (CommRingCat.ofHom φ)
    (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x))
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)
  refine ⟨?_, ?_⟩
  · rw [hψ]
    exact isEtaleCompletion_comp_bij e he φ ⟨RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
      hm.symm, RingHom.Finite.of_surjective _ hres⟩
  · rw [hψ, ← RingHom.comp_assoc]
    exact hres.comp he.2

end GlobalTheory.InteriorChart

namespace GlobalTheory.InteriorChart

end GlobalTheory.InteriorChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.FineAgree

theorem sec_hom {S : Scheme.{0}} {G : Over S} (x : 𝟙_ (Over S) ⟶ G) : x.left ≫ G.hom = 𝟙 S := Over.w x

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A] [IsDomain A] (f₁ f₂ : L.W →+* A), f₁.comp L.b = f₂.comp L.b → ∀ (B' : Over (Sp A)) [GrpObj B'] (π₁ π₂ : B'.left ⟶ L.D.P.A.left) (act' : 𝓞 E → (B'.left ⟶ B'.left)), IsGrpPullback B' L.D.P.A (spMap f₁) π₁ → IsGrpPullback B' L.D.P.A (spMap f₂) π₂ → (letI := H.starRing; ∀ x, act' x ≫ π₁ = π₁ ≫ (L.oa.onB.act x).left) → (letI := H.starRing; ∀ x, act' x ≫ π₂ = π₂ ≫ (L.oa.onB.act x).left) → (∀ x, act' x ≫ B'.hom = B'.hom) → LBIso (L.D.P.L.pull π₁) (L.D.P.L.pull π₂) → ∀ (F : Type) [Field F] (j : A →+* F), Function.Injective j → (∀ a, ∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ (L.o.etaA a).left ≫ L.φB ∧ z ≫ π₂ = spMap j ≫ spMap f₂ ≫ (L.o.etaA a).left ≫ L.φB) → (∀ y, ∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ (L.D.c y).left ∧ z ≫ π₂ = spMap j ≫ spMap f₂ ≫ (L.D.c y).left) → f₁ = f₂ ∧ π₁ = π₂ := by
  intro E _ _ _ H D' l c L A _ _ f₁ f₂ hb B' _ π₁ π₂ act' h₁ h₂ ha₁ ha₂ hab hL F _ j hj hη hc
  letI := H.starRing
  obtain ⟨o', ⟨m₁⟩⟩ := GlobalTheory.obj_pull E H D' (LowDat.lowLevel l) _ _ (baseKA _) (baseKA _) (RingHom.id _) _ _
    (lowMap c L.b) (lowMap c (f₁.comp L.b)) (spMap f₁) rfl rfl (by
      simp only [lowMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) L.o
  have hφ₁ : IsGrpPullback o'.t.G L.D.P.A (spMap f₁) (m₁.φ ≫ L.φB) :=
    (m₁.cart.comp L.ab.1).congr (Category.comp_id _) rfl
  obtain ⟨e, he, heq⟩ := grpPullback_iso hφ₁ h₁
  haveI := he
  have hew : e.hom.left ≫ B'.hom = o'.t.G.hom := Over.w e.hom
  obtain ⟨ψ, hψ₁, hψ₂⟩ : ∃ ψ : o'.t.G.left ⟶ L.o.t.G.left, ψ ≫ L.φB = e.hom.left ≫ π₂ ∧
      ψ ≫ L.o.t.G.hom = o'.t.G.hom ≫ spMap f₂ :=
    ⟨L.ab.1.1.lift (e.hom.left ≫ π₂) (o'.t.G.hom ≫ spMap f₂) (by
      rw [Category.assoc, h₂.1.w, ← Category.assoc, hew, Category.comp_id]), IsPullback.lift_fst _ _ _ _,
      IsPullback.lift_snd _ _ _ _⟩
  have hψ : IsGrpPullback o'.t.G L.o.t.G (spMap f₂) ψ := by
    have n : IsGrpPullback o'.t.G L.D.P.A (spMap f₂ ≫ 𝟙 _) (ψ ≫ L.φB) := by
      rw [hψ₁, Category.comp_id]
      exact ((isGrpPullback_of_iso e).comp h₂).congr (Category.id_comp _) rfl
    exact L.ab.1.cancel n hψ₂
  have hact : ∀ x, (o'.t.act.act x).left ≫ ψ = ψ ≫ (L.o.t.act.act x).left := by
    intro x
    have key : (o'.t.act.act x).left ≫ e.hom.left = e.hom.left ≫ act' x := by
      apply h₁.1.hom_ext
      · have e1 : (o'.t.act.act x).left ≫ m₁.φ = m₁.φ ≫ (L.o.t.act.act x).left := m₁.act x
        calc ((o'.t.act.act x).left ≫ e.hom.left) ≫ π₁ = ((o'.t.act.act x).left ≫ m₁.φ) ≫ L.φB := by
              rw [Category.assoc, heq, Category.assoc]
          _ = m₁.φ ≫ (L.o.t.act.act x).left ≫ L.φB := by rw [e1, Category.assoc]
          _ = (m₁.φ ≫ L.φB) ≫ (L.oa.onB.act x).left := by rw [L.ab.2.1, Category.assoc]
          _ = (e.hom.left ≫ act' x) ≫ π₁ := by rw [← heq, Category.assoc, Category.assoc, ha₁]
      · rw [Category.assoc, hew, Category.assoc, hab, hew, Over.w (o'.t.act.act x)]
    apply L.ab.1.1.hom_ext
    · calc ((o'.t.act.act x).left ≫ ψ) ≫ L.φB = ((o'.t.act.act x).left ≫ e.hom.left) ≫ π₂ := by
            rw [Category.assoc, hψ₁, Category.assoc]
        _ = (ψ ≫ L.φB) ≫ (L.oa.onB.act x).left := by rw [key, Category.assoc, ha₂, hψ₁, Category.assoc]
        _ = (ψ ≫ (L.o.t.act.act x).left) ≫ L.φB := by rw [Category.assoc, Category.assoc, L.ab.2.1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (o'.t.act.act x), Category.assoc,
        Over.w (L.o.t.act.act x), hψ₂]

  have hLψ : LBIso o'.t.PP.L (L.o.t.PP.L.pull ψ) := by
    obtain ⟨w, hw, -⟩ := m₁.lin
    have K1 : LBIso o'.t.PP.L (L.D.P.L.pull (m₁.φ ≫ L.φB)) :=
      GlobalTheory.ThetaAffineGlue.lbIso_comp o'.t.PP.isLB L.o.t.PP.isLB L.D.P.isLB ⟨w, hw⟩ L.ab.2.2
    rw [← heq] at K1
    have K2 : LBIso o'.t.PP.L ((L.D.P.L.pull π₂).pull e.hom.left) :=
      GlobalTheory.ThetaAffineGlue.lbIso_cancel o'.t.PP.isLB (pull_isLB L.D.P.isLB _) L.D.P.isLB K1 hL.symm
    have K3 : LBIso o'.t.PP.L (L.D.P.L.pull (e.hom.left ≫ π₂)) :=
      GlobalTheory.ThetaAffineGlue.lbIso_comp o'.t.PP.isLB (pull_isLB L.D.P.isLB _) L.D.P.isLB K2
        (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB L.D.P.isLB _))
    rw [← hψ₁] at K3
    exact GlobalTheory.ThetaAffineGlue.lbIso_cancel o'.t.PP.isLB L.o.t.PP.isLB L.D.P.isLB K3 L.ab.2.2
  obtain ⟨n, hn⟩ := GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper o'.t L.o.t (spMap f₂) ψ L.o.proper hψ hact hLψ
  haveI : IsDominant (spMap j) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  haveI := L.o.proper
  have transfer : ∀ (u : Sp A ⟶ o'.t.G.left) (v : Sp L.W ⟶ L.o.t.G.left), u ≫ o'.t.G.hom = 𝟙 _ →
      v ≫ L.o.t.G.hom = 𝟙 _ → u ≫ m₁.φ = spMap f₁ ≫ v →
      (∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ v ≫ L.φB ∧
        z ≫ π₂ = spMap j ≫ spMap f₂ ≫ v ≫ L.φB) → u ≫ ψ = spMap f₂ ≫ v := by
    intro u v hu hv huv ⟨z, hz0, hz1, hz2⟩
    have hz : spMap j ≫ u ≫ e.hom.left = z := by
      apply h₁.1.hom_ext
      · rw [hz1, Category.assoc, Category.assoc, heq, ← Category.assoc u, huv, Category.assoc]
      · rw [hz0, Category.assoc, Category.assoc, hew, hu, Category.comp_id]
    refine ext_of_isDominant_of_isSeparated (X := Sp A) L.o.t.G.hom ?_ (spMap j) ?_
    · rw [Category.assoc, hψ₂, ← Category.assoc, hu, Category.id_comp, Category.assoc, hv, Category.comp_id]
    · apply L.ab.1.1.hom_ext
      · rw [Category.assoc, Category.assoc, hψ₁, ← Category.assoc u, ← Category.assoc, hz, hz2,
          Category.assoc, Category.assoc]
      · rw [Category.assoc, Category.assoc, hψ₂, ← Category.assoc u, hu, Category.id_comp, Category.assoc,
          Category.assoc, hv, Category.comp_id]
  have hetaA : ∀ a, (o'.etaA a).left ≫ n.φ = spMap f₂ ≫ (L.o.etaA a).left := by
    intro a
    rw [hn]
    exact transfer _ _ (sec_hom _) (sec_hom _) (m₁.etaA a) (hη a)
  have heta := _root_.GlobalTheory.UCanon.sabMap_keeps_eta c A L.W (f₁.comp L.b) L.b o' L.o f₂ hb.symm n hetaA
  obtain ⟨m₂, hm₂⟩ : ∃ m₂ : ObjMap o' L.o (spMap f₂), m₂.φ = ψ := ⟨⟨n, heta, hetaA⟩, hn⟩

  have hcy : ∀ y, ∃ cy : Sp L.W ⟶ L.o.t.G.left, cy ≫ L.φB = (L.D.c y).left ∧ cy ≫ L.o.t.G.hom = 𝟙 _ := fun y =>
    ⟨L.ab.1.1.lift (L.D.c y).left (𝟙 _) (by rw [sec_hom, Category.comp_id]),
      IsPullback.lift_fst _ _ _ _, IsPullback.lift_snd _ _ _ _⟩
  choose cy hcy₁ hcy₂ using hcy
  have hx : ∀ y, ∃ x : Sp A ⟶ o'.t.G.left, x ≫ m₁.φ = spMap f₁ ≫ cy y ∧ x ≫ o'.t.G.hom = 𝟙 _ := fun y =>
    ⟨m₁.cart.1.lift (spMap f₁ ≫ cy y) (𝟙 _) (by
      rw [Category.assoc, hcy₂, Category.comp_id, Category.id_comp]),
      IsPullback.lift_fst _ _ _ _, IsPullback.lift_snd _ _ _ _⟩
  choose x hx₁ hx₃ using hx
  have hf : f₁ = f₂ := by
    refine L.fineRed A f₁ f₂ hb o' m₁ m₂ x (fun y => ?_) (fun y => ?_) hx₃
    · rw [← Category.assoc, hx₁, Category.assoc, hcy₁]
    · rw [hm₂, ← Category.assoc, transfer (x y) (cy y) (hx₃ y) (hcy₂ y) (hx₁ y) (by
        obtain ⟨z, hz⟩ := hc y
        exact ⟨z, by simpa only [hcy₁] using hz⟩), Category.assoc, hcy₁]
  subst hf
  refine ⟨rfl, ?_⟩
  have hu : m₁.φ = m₂.φ := GlobalTheory.ObjMapUnique.objMap_unique_of_nilpotent_nilradical A
    (by rw [nilradical_eq_zero]; exact IsNilpotent.zero) _ _ o' L.o (spMap f₁) m₁ m₂
  have hi : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  apply (cancel_epi e.hom.left).1
  rw [heq, hu, hm₂, hψ₁]

end GlobalTheory.UCanon.FineAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryGeneratorValueLocalUnitsMulSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG.SymVal

theorem sym_val : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a : D.X, ∃ c ∈ k₀, (val D.sym (spMap ev ≫ (D.c a).left) z J).val =
      ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (-a)).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ a
  obtain ⟨-, hM₀, hpb, hw, hc, -, -⟩ := hFB
  set φ' : Fin 2 → (D.P.A.left ⟶ D.P.A.left) := ![(ι[D.P.A]).left, 𝟙 D.P.A.left] with hφ'
  obtain ⟨t, ht, hmap⟩ := _root_.GlobalTheory.GenTransport.exists_gen_down_pmaps w hw hM₀ D.P.isLB φ' ![1, -1] D.sym D.sym_gen
  have hφ : ∀ k, φ' k ≫ β = β ≫ (![(ι[B₀]).left, 𝟙 B₀.left] : Fin 2 → (B₀.left ⟶ B₀.left)) k := by
    intro k
    fin_cases k
    · exact GlobalTheory.PolDeg.SymPol.inv_comm hpb
    · simp [hφ']
  have hpt : ∀ b : D.X, (spMap ev ≫ (D.c b).left) ≫ D.P.A.hom = spMap ev := fun b => by
    rw [Category.assoc, Over.w (D.c b)]; rfl
  have hdef : ∀ b : D.X, DefOver k₀ ((spMap ev ≫ (D.c b).left) ≫ β) := fun b => by
    have e : (spMap ev ≫ (D.c b).left) ≫ β = spMap (ev.comp ib) ≫ c₀ b := by
      rw [Category.assoc]
      erw [hc b]
      rw [← Category.assoc]
      congr 1
      simp only [spMap, ← Spec.map_comp]
      rfl
    rw [e]
    exact GlobalTheory.Poinc.Sep.defOver_comp k₀ (GlobalTheory.Poinc.Sep.defOver_spMap k₀ _ hk) _

  have read : ∀ (x : Sp K ⟶ D.P.A.left) (z' : Sp K) (I : (Sp K ⟶ D.P.A.left) → D.P.L.ι)
      (I₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z' I → Good M₀ z' I₀ →
      val t x z' I₀ = gwx w z' I I₀ (x ≫ (ι[D.P.A]).left) * (gwx w z' I I₀ x)⁻¹ * val D.sym x z' I := by
    intro x z' I I₀ hI hI₀
    have H := hmap (Sp K) x z' (fun k => I₀ ((x ≫ φ' k) ≫ β)) (fun k => I (x ≫ φ' k))
      (fun k => hI₀ ((x ≫ φ' k) ≫ β)) (fun k => hI (x ≫ φ' k))
    rw [Category.comp_id, Fin.prod_univ_two] at H
    rw [val_of t x z' I₀ (fun k => I₀ ((x ≫ φ' k) ≫ β)) (fun k => by rw [Category.assoc]), H]
    simp only [hφ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one, zpow_neg, Category.comp_id]
    rfl
  have hx₁ : (spMap ev ≫ (D.c 0).left) ≫ (ι[D.P.A]).left = spMap ev ≫ (D.c 0).left := by
    rw [Category.assoc, ← Over.comp_left, ← GlobalTheory.PsiEvenPull.c_neg, neg_zero]
  have hnorm : ∀ (z' : Sp K) (I₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z' I₀ →
      val t (spMap ev ≫ (D.c 0).left) z' I₀ = 1 := by
    intro z' I₀ hI₀
    choose I hI using fun χ : Sp K ⟶ D.P.A.left => exists_chart D.P.isLB (χ z')
    have hIg : Good D.P.L z' I := hI
    rw [read _ z' I I₀ hIg hI₀, hx₁, _root_.mul_inv_cancel, _root_.one_mul, GlobalTheory.Poinc.ThetaOne.c_zero]
    have e1 : (1 : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A).left = eSec D.P.A := rfl
    rw [e1, ← val_pull hIg, val_corr hIg D.sym_rig, val_one]
  obtain ⟨c, hc₀, hv⟩ := _root_.GlobalTheory.Poinc.Sep.gen_values_mem V₁ W₀ ib D.P.A D.P.isAb B₀ β hpb.1 M₀ hM₀ (Fin 2) (fun k => φ' k ≫ β) _ hφ
    ![1, -1] t ht K ev k₀ hk₀ hk _ (hpt 0) (hdef 0) hnorm _ (hpt a) (hdef a) z J₀ hJ₀
  refine ⟨c, hc₀, ?_⟩
  have r := read (spMap ev ≫ (D.c a).left) z J J₀ hJ hJ₀
  have hneg : (spMap ev ≫ (D.c a).left) ≫ (ι[D.P.A]).left = spMap ev ≫ (D.c (-a)).left := by
    rw [Category.assoc, ← Over.comp_left, ← GlobalTheory.PsiEvenPull.c_neg]
  rw [hneg] at r
  have key : val D.sym (spMap ev ≫ (D.c a).left) z J =
      (gwx w z J J₀ (spMap ev ≫ (D.c (-a)).left))⁻¹ * gwx w z J J₀ (spMap ev ≫ (D.c a).left) *
        val t (spMap ev ≫ (D.c a).left) z J₀ := by
    rw [r]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [key, Units.val_mul, hv]

end GlobalTheory.USep.EvG.SymVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulFinrankBalancedSymmIntBilinFormsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_finrank_balancedSymmIntBilinForms : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], 2 * Module.finrank ℤ (balForms H.bar X) = Module.finrank ℤ (GlobalTheory.BalRank.balBil H.bar X) := by
  first | exact @GlobalTheory.BalRankSym.two_mul_finrank_balForms | exact GlobalTheory.BalRankSym.two_mul_finrank_balForms | (intros; apply GlobalTheory.BalRankSym.two_mul_finrank_balForms <;> assumption)
end

