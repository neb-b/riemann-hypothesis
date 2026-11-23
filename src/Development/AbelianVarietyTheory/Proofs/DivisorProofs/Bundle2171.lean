module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueMapClosurePoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ResMap

def stalkEquiv {X : Scheme.{0}} [IsIntegral X] (x : X) : X.presheaf.stalk x ≃+* locRing x :=
  RingEquiv.ofBijective (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective _ X.functionField (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩

theorem residueMap : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (z : X) (k : ℕ),
  topologicalKrullDim (closure ({z} : Set X)) = k →
  ∃ (κ : Type) (_ : Field κ) (_ : Algebra ℂ κ) (π₀ : locRing z →+* κ),
    Function.Surjective π₀ ∧ (∀ r : locRing z, π₀ r = 0 ↔ ZeroAt z (r : X.functionField)) ∧
    (∀ a (h : Cartier.constFn p a ∈ locRing z), π₀ ⟨Cartier.constFn p a, h⟩ = algebraMap ℂ κ a) ∧
    (∃ w : Fin k → κ, TrBasis (algebraMap ℂ κ) w) ∧
    ∀ (x : X) (h : locRing x ≤ locRing z), IsLocModel (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range ∧
      (∀ f : κ, ∃ a b : locRing x, π₀ (Subring.inclusion h b) ≠ 0 ∧ f * π₀ (Subring.inclusion h b) = π₀ (Subring.inclusion h a)) ∧
      (IsClosed ({x} : Set X) → RatRes (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range) := by
  intro X _ _ p hp z k hk
  have hprop : IsProper p := by
    obtain ⟨N, j, hj, rfl⟩ := hp
    have := isProper_str ℂ N
    infer_instance
  have hsep : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from p]; infer_instance⟩
  obtain ⟨Z, i, hi, hZ, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  let q := i ≫ p
  have hrange : Set.range i = closure ({i (genericPoint Z)} : Set X) := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact (isGenericPoint_def.mp h₁).symm
  have hdim : topologicalKrullDim Z = k := by
    rw [← GlobalTheory.topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
    exact hk
  obtain ⟨-, w, hw⟩ := isLocModel_locRing_and_exists_trBasis Z q k (genericPoint Z) hdim
  letI alg : Algebra ℂ Z.functionField := (Cartier.constFn q).toAlgebra
  let π₀ : locRing (i (genericPoint Z)) →+* Z.functionField :=
    (i.stalkMap (genericPoint Z)).hom.comp (stalkEquiv (i (genericPoint Z))).symm.toRingHom
  refine ⟨Z.functionField, inferInstance, alg, π₀, ?_, ?_, ?_, ⟨w, hw⟩, ?_⟩
  · exact (i.stalkMap_surjective _).comp (stalkEquiv _).symm.surjective
  · intro r
    obtain ⟨a, rfl⟩ := (stalkEquiv _).surjective r
    have e1 : π₀ (stalkEquiv _ a) = (i.stalkMap (genericPoint Z)).hom a := by
      show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ a)) = _
      rw [RingEquiv.symm_apply_apply]
    have e2 : ((stalkEquiv _ a : locRing _) : X.functionField) = algebraMap _ _ a := rfl
    rw [e1, e2]
    constructor
    · intro h0
      refine ⟨a, ?_, rfl⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map (i.stalkMap (genericPoint Z)).hom
      rw [h0] at this
      exact not_isUnit_zero this
    · rintro ⟨b, hb, e⟩
      obtain rfl := IsFractionRing.injective _ X.functionField e
      by_contra hne
      have hu : IsUnit ((i.stalkMap (genericPoint Z)).hom b) := isUnit_iff_ne_zero.2 hne
      exact (IsLocalRing.mem_maximalIdeal _).1 hb ((isUnit_map_iff _ _).1 hu)
  · intro a ha
    have hg := (algebraMap_germ (X := X) (x := i (genericPoint Z)) (U := ⊤) trivial (algX p ⊤ a)).trans
      (RingHom.congr_fun (fnOf_comp_algX p ⊤ (gen_mem (x := i (genericPoint Z)) trivial)) a)
    have hr : (⟨Cartier.constFn p a, ha⟩ : locRing _) =
        stalkEquiv _ (X.presheaf.germ ⊤ _ trivial (algX p ⊤ a)) := Subtype.ext hg.symm
    rw [hr]
    show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ _)) = _
    rw [RingEquiv.symm_apply_apply]
    erw [Scheme.Hom.germ_stalkMap_apply i ⊤ (genericPoint Z) trivial (algX p ⊤ a)]
    have hc : (i.app ⊤).hom (algX p ⊤ a) = algX q (i ⁻¹ᵁ ⊤) a := by
      have e : (i ≫ p).appLE ⊤ (i ⁻¹ᵁ ⊤) (le_top.trans (Scheme.Hom.preimage_top _).ge) =
          p.appLE ⊤ ⊤ (le_top.trans (Scheme.Hom.preimage_top _).ge) ≫ i.appLE ⊤ (i ⁻¹ᵁ ⊤) le_rfl := by
        first
          | rw [Scheme.Hom.appLE_comp_appLE]
          | (simp only [Scheme.Hom.comp_appLE, Scheme.Hom.appLE, Category.assoc,
              Scheme.Hom.naturality_assoc]; rfl)
      simp only [algX, q, RingHom.comp_apply]
      rw [Scheme.Hom.app_eq_appLE, e, CommRingCat.comp_apply]
    rw [hc]
    exact RingHom.congr_fun (fnOf_comp_algX q (i ⁻¹ᵁ ⊤) (gen_mem (x := genericPoint Z) trivial)) a
  · intro x h
    have hs : i (genericPoint Z) ⤳ x := GlobalTheory.T.specializes_of_pointLocalRing_le_separated X x _ h
    obtain ⟨y, rfl⟩ : x ∈ Set.range i := by
      rw [hrange]; exact specializes_iff_mem_closure.mp hs
    have key : ∀ a : X.presheaf.stalk (i y),
        π₀ (Subring.inclusion h ⟨algebraMap _ X.functionField a, a, rfl⟩) =
          algebraMap (Z.presheaf.stalk y) Z.functionField ((i.stalkMap y).hom a) := by
      intro a
      have e : (Subring.inclusion h ⟨algebraMap _ X.functionField a, a, rfl⟩ : locRing _) =
          stalkEquiv _ ((X.presheaf.stalkSpecializes hs).hom a) := by
        apply Subtype.ext
        show algebraMap _ X.functionField a =
          algebraMap _ X.functionField ((X.presheaf.stalkSpecializes hs).hom a)
        simp only [RingHom.algebraMap_toAlgebra]
        rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
      rw [e]
      show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ _)) = _
      rw [RingEquiv.symm_apply_apply]
      exact Scheme.Hom.stalkSpecializes_stalkMap_apply i (genericPoint Z) y
        ((genericPoint_spec Z).specializes trivial) a
    have hR : (π₀.comp (Subring.inclusion h)).range = locRing y := by
      ext f
      constructor
      · rintro ⟨⟨r, a, rfl⟩, rfl⟩
        exact ⟨(i.stalkMap y).hom a, (key a).symm⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨a, rfl⟩ := i.stalkMap_surjective y b
        exact ⟨⟨_, a, rfl⟩, key a⟩
    have hloc : IsLocModel (Cartier.constFn q) (locRing y) := isLocModel_locRing y
    rw [hR]
    refine ⟨hloc, fun f => ?_, fun hx => ?_⟩
    · obtain ⟨a', ha', b', hb', hb0, e⟩ := hloc.frac f
      rw [← hR] at ha' hb'
      obtain ⟨a, rfl⟩ := ha'
      obtain ⟨b, rfl⟩ := hb'
      exact ⟨a, b, hb0, e⟩
    · have hy : IsClosed ({y} : Set Z) := by
        have hpre : (i : Z → X) ⁻¹' {i y} = {y} := by
          ext t
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact i.isClosedEmbedding.injective.eq_iff
        rw [← hpre]
        exact hx.preimage i.continuous
      exact _root_.GlobalTheory.FieldPair.ratRes_locRing_of_isClosed Z q y hy

end GlobalTheory.ResMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfNaturalOnAlgebraPointsOfCover
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem Pt.aff_in (s : X ⟶ Sp R) (V : X.affineOpens) : (Pt.aff s V).In V.1 :=
  V.2.fromSpec_preimage_self.ge

def Pt.homAff (V : X.affineOpens) (Q : Pt s) (h : Q.In V.1) : (Pt.aff s V).Hom Q :=
  ⟨{ (GlobalTheory.Points.valMap Q.x V.1 h).hom with
      commutes' := fun r ↦ by
        have e := GlobalTheory.Points.valR_constFn_of_over s (algebraMap R Q.B) Q.x Q.w V.1 h r
        rw [GlobalTheory.Points.valR_eq Q.x V.1 h] at e
        exact e },
    GlobalTheory.Points.specMap_valMap_fromSpec V.2 Q.x h⟩

theorem Pt.homAff_apply (V : X.affineOpens) (Q : Pt s) (h : Q.In V.1) (a : CechDR.Sec s V.1) :
    (Pt.homAff V Q h).ρ a = valR Q.x V.1 a :=
  (GlobalTheory.Points.valR_eq Q.x V.1 h a).symm

theorem exists_sec_of_isNat (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens)
    (U : X.Opens) (hWU : ∀ j, W j ≤ U) (hU : U ≤ ⨆ j, W j) (F : PtFn s) (hF : ∀ j, IsNat (W j) F) :
    ∃ f : Γ(X, U), ∀ (j : J) (P : Pt s), P.In (W j) → F P = valR P.x U f := by
  let Ix := {V : X.affineOpens // ∃ j, V.1 ≤ W j}
  let Vs : Ix → X.Opens := fun i ↦ i.1.1
  have hVU : ∀ i : Ix, Vs i ≤ U := fun i ↦ i.2.choose_spec.trans (hWU _)
  let iUV : ∀ i : Ix, Vs i ⟶ U := fun i ↦ homOfLE (hVU i)
  have hcov : U ≤ iSup Vs := by
    intro x hx
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU hx)
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := W j) (x := x) hj
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, j, hVW⟩, hxV⟩
  have hres : ∀ (i : Ix) (V : X.affineOpens) (h : V.1 ≤ i.1.1),
      F (Pt.aff s V) = CechDR.Sec.res s h (F (Pt.aff s i.1)) := fun i V h ↦
    hF i.2.choose (Pt.aff s i.1) (Pt.aff s V) (Pt.affHom s h) ((Pt.aff_in s i.1).mono i.2.choose_spec)
  let sf : ∀ i : Ix, Γ(X, Vs i) := fun i ↦ F (Pt.aff s i.1)
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 Vs sf := by
    intro i i'
    refine X.sheaf.eq_of_locally_eq' (fun V : {V : X.affineOpens // V.1 ≤ Vs i ⊓ Vs i'} ↦ V.1.1) _
      (fun V ↦ homOfLE V.2) ?_ _ _ ?_
    · intro x hx
      obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := Vs i ⊓ Vs i') (x := x) hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
    · intro V
      have k : ∀ (T : Ix) (h2 : Vs i ⊓ Vs i' ≤ Vs T) (g : Vs i ⊓ Vs i' ⟶ Vs T),
          X.sheaf.1.map (homOfLE V.2).op (X.sheaf.1.map g.op (sf T)) = F (Pt.aff s V.1) := fun T h2 g ↦ by
        rw [Subsingleton.elim g (homOfLE h2)]
        change CechDR.Sec.res s V.2 (CechDR.Sec.res s h2 (sf T)) = _
        rw [← CechDR.Sec.res_res]
        exact (hres T V.1 _).symm
      exact (k i inf_le_left _).trans (k i' inf_le_right _).symm
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' Vs U iUV hcov sf hcomp
  refine ⟨f, fun j P hP ↦ ?_⟩
  have hPU : P.In U := hP.mono (hWU j)
  have key : ∀ (V' : (Sp P.B).affineOpens) (i : Ix), V'.1 ≤ P.x ⁻¹ᵁ i.1.1 →
      CechDR.toSec R P.B V' (F P) = CechDR.toSec R P.B V' (valR P.x U f) := by
    intro V' i hV'
    let P' : Pt s := ⟨CechDR.Sec (CechDR.algStr R P.B) V'.1, CechDR.affPt (CechDR.algStr R P.B) V' ≫ P.x, by
      rw [Category.assoc, P.w]; exact CechDR.affPt_w _ V'⟩
    have hpt : spMap ((CechDR.toSec R P.B V' : P.B →ₐ[R] P'.B) : P.B →+* P'.B) ≫ P.x = P'.x := by
      change _ = CechDR.affPt _ V' ≫ P.x
      rw [CechDR.affPt_eq]; rfl
    let φ : P.Hom P' := ⟨CechDR.toSec R P.B V', hpt⟩
    have hP'V : P'.In i.1.1 := fun q _ ↦ hV' (V'.2.fromSpec_preimage_self.ge (Set.mem_univ q))
    have e1 : F P' = φ.ρ (F P) := hF j P P' φ hP
    have e2 : F P' = (Pt.homAff i.1 P' hP'V).ρ (F (Pt.aff s i.1)) :=
      hF i.2.choose _ _ _ ((Pt.aff_in s i.1).mono i.2.choose_spec)
    rw [Pt.homAff_apply] at e2
    have e3 : valR P'.x i.1.1 (F (Pt.aff s i.1)) = valR P'.x U f := by
      have h0 := hf i
      have h1 := GlobalTheory.Points.valR_res P'.x (hVU i) hP'V f
      change valR P'.x i.1.1 (sf i) = _
      rw [← h0]
      exact h1
    have e4 : valR P'.x U f = φ.ρ (valR P.x U f) := by
      have h2 := GlobalTheory.Points.valR_spMap_comp (φ.ρ : P.B →+* P'.B) P.x U hPU f
      rw [hpt] at h2
      exact h2
    exact e1.symm.trans (e2.trans (e3.trans e4))
  have hex : ∀ y : Sp P.B, ∃ V' : (Sp P.B).affineOpens, y ∈ V'.1 ∧ ∃ i : Ix, V'.1 ≤ P.x ⁻¹ᵁ i.1.1 := by
    intro y
    obtain ⟨V, hV, hyV, hVW⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := W j) (x := P.x y) (hP (Set.mem_univ y))
    obtain ⟨V', hV', hyV', hV'V⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Sp P.B) (U := P.x ⁻¹ᵁ V) (x := y) hyV
    exact ⟨⟨V', hV'⟩, hyV', ⟨⟨V, hV⟩, j, hVW⟩, hV'V⟩
  choose V' hyV' i hi using hex
  have key2 : (Scheme.ΓSpecIso (CommRingCat.of P.B)).inv (F P) =
      (Scheme.ΓSpecIso (CommRingCat.of P.B)).inv (valR P.x U f) := by
    refine (Sp P.B).sheaf.eq_of_locally_eq' (fun y ↦ (V' y).1) ⊤ (fun _ ↦ homOfLE le_top)
      (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyV' y⟩) _ _ (fun y ↦ ?_)
    have := key (V' y) (i y) (hi y)
    change (CechDR.secMap (𝟙 (Sp P.B)) (V' y).1).hom (F P) =
      (CechDR.secMap (𝟙 (Sp P.B)) (V' y).1).hom (valR P.x U f) at this
    simp only [CechDR.secMap, Scheme.Hom.appLE, Scheme.Hom.id_app, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  exact (Scheme.ΓSpecIso (CommRingCat.of P.B)).symm.commRingCatIsoToRingEquiv.injective key2

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistedLineBundleNonzeroClosedFibre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistGen

theorem whisker_eq_twistLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ)
    {T T' : Over S} (ρ : T' ⟶ T) (c : T ⟶ A) :
    LB.LinComb L (K := Fin 2) (fun k => (ρ ▷ A).left ≫ ![(snd T A).left, (translPt A c).left] k)
      ![(q : ℤ) - 1, 1] = twistLB A L q (ρ ≫ c) := by
  unfold twistLB
  congr 1
  funext k
  fin_cases k
  · show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left
    rw [← Over.comp_left, whiskerRight_snd]
  · show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left
    rw [← Over.comp_left]
    congr 1
    simp [translPt, comp_lift_assoc]

theorem mem_of_isPullSecLC {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε))
    (hs : IsPullSecLC L φ ε h s s') (y : Y') (hy : y ∈ nonzeroLocus s') : h y ∈ nonzeroLocus s := by
  obtain ⟨(j : K → L.ι), hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  rw [hs j] at hj
  erw [Scheme.basicOpen_res] at hj
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (Scheme.preimage_basicOpen h (s.f j)).ge hj.2⟩

theorem transfer {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (α : D.X)
    (s : LB.Sec (twistLB D.P.A D.P.L 2 (D.c α)))
    (z : (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ D.P.A).left) (hz : z ∈ nonzeroLocus s) :
    ∃ σ : D.SecB 2 α, (snd _ D.P.A).left z ∈ nonzeroLocus σ := by
  let T := 𝟙_ (Over (Spec (CommRingCat.of R)))
  let A := D.P.A
  let iota : A.left ⟶ (T ⊗ A).left := (lift (toUnit A) (𝟙 A)).left
  have hsec : snd T A ≫ lift (toUnit A) (𝟙 A) = 𝟙 (T ⊗ A) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact (toUnit_unique _ _)
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  have hiota : iota ((snd T A).left z) = z := by
    have e : (snd T A).left ≫ iota = 𝟙 _ := by rw [← Over.comp_left, hsec]; rfl
    have e' := congrArg (fun f => f.base z) e
    exact e'
  obtain ⟨u₀, hu₀⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2)
    (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) ![-1, 1]
  let u := LB.pullGen D.P.L _ _ u₀ (toUnit A).left
  have hu : u.IsGen := DVR.pullGen_isGen_of_isGen _ _ u₀ hu₀ _
  let s₁ := pullMulSec s iota u hu
  have hF : FormEq (Sum.elim (fun k => iota ≫ ![(snd T A).left, (translPt A (D.c α)).left] k)
      (fun k => (toUnit A).left ≫ (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) k))
      (Sum.elim ![((2 : ℕ) : ℤ) - 1, 1] ![-1, 1]) (D.famφB α) (DegPre.famε 2) := by
    have e₁ : iota ≫ (snd T A).left = 𝟙 _ := by
      rw [← Over.comp_left, lift_snd]; rfl
    have e₂ : iota ≫ (translPt A (D.c α)).left = (padd A (𝟙 A) (toUnit A ≫ D.c α)).left := by
      rw [← Over.comp_left]
      congr 1
      show lift (toUnit A) (𝟙 A) ≫ ((fst T A ≫ D.c α) * snd T A) = 𝟙 A * (toUnit A ≫ D.c α)
      rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, lift_snd, ← Category.assoc, lift_fst]
      show (toUnit A ≫ D.c α) * 𝟙 A = 𝟙 A * (toUnit A ≫ D.c α)
      exact mul_comm _ _
    intro U _ hh
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr,
      DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e₁, e₂]
    simp only [_root_.mul_assoc]; rfl
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB hF s₁
  refine ⟨σ, ?_⟩
  set xx := (snd T A).left z
  choose J hJ using fun χ : A.left ⟶ A.left => exists_chart D.P.isLB (χ xx)
  obtain ⟨(k : Fin 2 → D.P.L.ι), hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hv : IsUnit (sval s (𝟙 A.left ≫ iota) xx J) := by
    refine H1.SectionArithmetic.isUnit_sval s (𝟙 A.left ≫ iota) xx hJ k ?_
    rw [Category.id_comp, hiota]; exact hk
  have hval : IsUnit (sval σ (𝟙 A.left) xx J) := by
    rw [hσ _ _ xx J hJ, sval_pullMulSec s iota u hu (𝟙 A.left) xx hJ]
    exact hv.mul (Units.isUnit _)
  have hm := (Good.mem hJ (D.famφB α) (𝟙 A.left))
  rw [sval] at hval
  erw [gs_eq (𝟙 A.left) xx _ hm] at hval
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => J (𝟙 A.left ≫ D.famφB α k), ?_⟩
  exact (A.left.mem_basicOpen _ xx hm).2 hval

theorem exists_sec_nonzeroLocus_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R],
    IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (D : DegPre R) (α : D.X) (x : D.P.A.left),
    D.P.A.hom x = IsLocalRing.closedPoint R → ∃ σ : D.SecB 2 α, x ∈ nonzeroLocus σ := by
  intro R _ _ _ _ _ D α x hx
  let S := Spec (CommRingCat.of R)
  let tk : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let T : Over S := 𝟙_ (Over S)
  let ρ : Over.mk (tk ≫ T.hom) ⟶ Over.mk T.hom := Over.homMk tk rfl
  obtain ⟨y, hy⟩ : ∃ y : (Over.mk (tk ≫ T.hom) ⊗ D.P.A).left, (snd _ D.P.A).left y = x := by
    obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) := inferInstance
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := tk ≫ T.hom) (g := D.P.A.hom) p x (by
      rw [hx]; exact IsLocalRing.PrimeSpectrum.comap_residue R p)
    exact ⟨z, hz⟩
  have hg := _root_.GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus S D.P _ (tk ≫ T.hom) (ρ ≫ D.c α) y
  rw [← whisker_eq_twistLB] at hg
  obtain ⟨sb, hsb⟩ := hg
  obtain ⟨s, hs⟩ := (GlobalTheory.abelianSchemeLaws_all.2.secTwist S D.P 2 (by norm_num) R T.hom (D.c α)).2 sb
  have hz := mem_of_isPullSecLC D.P.L _ _ _ s sb hs y hsb
  obtain ⟨σ, hσ⟩ := transfer D α s _ hz
  refine ⟨σ, ?_⟩
  have e : (snd T D.P.A).left ((ρ ▷ D.P.A).left y) = x := by
    rw [← hy]
    have e' := congrArg (fun f => f.left.base y) (whiskerRight_snd ρ D.P.A)
    exact e'
  rwa [e] at hσ

end GlobalTheory.TwistGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.HenselLift

theorem exists_lift_mem_open (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
    (hc : IsAdicComplete (maximalIdeal R') R') (ρ : R →+* R') (U : Over (Sp R)) (hU : Smooth U.hom)
    (x₀ : Sp (ResidueField R') ⟶ U.left) (hx : x₀ ≫ U.hom = spMap ((residue R').comp ρ))
    (O : U.left.Opens) (hO : Set.range x₀ ⊆ O) :
    ∃ a : Sp R' ⟶ U.left, a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  obtain ⟨y, hy⟩ : ∃ y, x₀ (closedPoint (ResidueField R')) = y := ⟨_, rfl⟩
  obtain ⟨α, hs, hα⟩ := GlobalTheory.HenselZero.exists_formallySmooth_stalk (O := CommRingCat.of R) U.hom y
  obtain ⟨χ₀, hχ₀⟩ := GlobalTheory.HenselZero.exists_factor_stalk (T := CommRingCat.of (ResidueField R')) x₀ (y := y) hy
  letI := α.hom.toAlgebra
  letI := ρ.toAlgebra
  haveI : Algebra.FormallySmooth R (U.left.presheaf.stalk y) := hs
  haveI := hc
  have e₁ : α ≫ χ₀ = CommRingCat.ofHom ((residue R').comp ρ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hχ₀, hx]
  let f : U.left.presheaf.stalk y →ₐ[R] R' ⧸ maximalIdeal R' :=
    { χ₀.hom with commutes' := fun r => congrArg (fun g => g.hom r) e₁ }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := maximalIdeal R') f
  have hg' : CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom (residue R') = χ₀ := by
    ext a
    exact congr($hg a)
  refine ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y, ?_, ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp]
    congr 1
    ext r
    exact g.commutes r
  · have hcl : (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y) (closedPoint R') = y := by
      have h1 : Spec.map (CommRingCat.ofHom (residue R')) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
          U.left.fromSpecStalk y = x₀ := by
        rw [← Spec.map_comp_assoc, hg', hχ₀]
      have h2 := congrArg (fun h => h (closedPoint (ResidueField R'))) h1
      simp only [Scheme.Hom.comp_apply] at h2
      rw [hy] at h2
      refine Eq.trans ?_ h2
      exact congrArg (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y)
        (comap_closedPoint (residue R')).symm
    rintro _ ⟨p, rfl⟩
    refine Specializes.mem_open ((specializes_closedPoint p).map (Scheme.Hom.continuous _)) O.isOpen ?_
    rw [hcl]
    exact hO ⟨_, hy⟩

end GlobalTheory.HenselLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointSmoothLocalRingOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_separable_point_of_smooth : ∀ (R : Type) [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom →
    ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra (ResidueField R) k') (_ : Module.Finite (ResidueField R) k')
      (_ : Algebra.IsSeparable (ResidueField R) k') (x : Sp k' ⟶ U.left),
      x ≫ U.hom = spMap ((algebraMap (ResidueField R) k').comp (residue R)) ∧ Set.range x ⊆ O := by
  intro R _ _ U hU O hO
  obtain ⟨W, _, _, _, ε, y, hy, hyO⟩ := GlobalTheory.exists_etale_point_of_smooth U.hom R
    (SeparableClosure (ResidueField R)) (𝟙 _) O (by obtain ⟨u, hu, e⟩ := hO; exact ⟨u, hu, e⟩)
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R W).FG)
  let k' : IntermediateField (ResidueField R) (SeparableClosure (ResidueField R)) :=
    IntermediateField.adjoin (ResidueField R) (ε '' (s : Set W))
  have hfin : FiniteDimensional (ResidueField R) k' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hsep : Algebra.IsSeparable (ResidueField R) k' := Algebra.IsSeparable.of_algHom _ _ k'.val
  have hle : Algebra.adjoin R (s : Set W) ≤ (k'.toSubalgebra.restrictScalars R).comap ε :=
    Algebra.adjoin_le fun w hw => IntermediateField.subset_adjoin _ _ ⟨w, hw, rfl⟩
  have hmem : ∀ w, ε w ∈ k' := fun w => hle (hs ▸ Algebra.mem_top)
  let g : W →+* k' := ε.toRingHom.codRestrict k' hmem
  set_option synthInstance.maxHeartbeats 200000 in
    refine ⟨k', inferInstance, inferInstance, hfin, hsep, Spec.map (CommRingCat.ofHom g) ≫ y, ?_, ?_⟩
  · rw [Category.assoc, hy, Category.comp_id, ← Spec.map_comp]
    congr 2
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    congr 1
    change ε (algebraMap R W r) = algebraMap (ResidueField R) _ (residue R r)
    rw [ε.commutes]
    exact IsScalarTower.algebraMap_apply R (ResidueField R) _ r
  · rintro _ ⟨z, rfl⟩
    exact hyO ⟨_, rfl⟩

end GlobalTheory.Mum
end

