module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoValueOneOriginPolarised
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.NormIso

theorem prod_zpow_eq_one {K U : Type} [Fintype K] [CommGroup U] (ε : K → ℤ) (hε : ∑ k, ε k = 0) (c : U) :
    ∏ k, c ^ ε k = 1 := by
  have h : ∀ s : Finset K, ∏ k ∈ s, c ^ ε k = c ^ (∑ k ∈ s, ε k) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  rw [h, hε, zpow_zero]

theorem gm_const {B X Y : Scheme.{0}} (M : LB B) {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (ε : K → ℤ) (hε : ∑ k, ε k = 0)
    (r : Y ⟶ X) (q : Y ⟶ B) (hq : ∀ k, r ≫ φ k = q) (y : Y) (a a' : M.ι)
    (ha : r y ∈ LB.wchart M φ (fun _ => a)) (ha' : r y ∈ LB.wchart M φ (fun _ => a')) :
    gm r y (LB.wchart M φ (fun _ => a) ⊓ LB.wchart M φ (fun _ => a'))
      ((LB.LinComb M φ ε).g (fun _ => a) (fun _ => a')) = 1 :=
  (gm_linComb M φ ε r y _ _ ha ha').trans ((Finset.prod_congr rfl fun k _ => by rw [hq k]).trans
    (prod_zpow_eq_one ε hε (gm q y (M.U a ⊓ M.U a') (M.g a a'))))

theorem mem_const {B X Y : Scheme.{0}} (M : LB B) {K : Type} [Fintype K] (φ : K → (X ⟶ B))
    (r : Y ⟶ X) (q : Y ⟶ B) (hq : ∀ k, r ≫ φ k = q) (y : Y) (a : M.ι) (ha : q y ∈ M.U a) :
    r y ∈ LB.wchart M φ (fun _ => a) :=
  Set.mem_iInter.2 fun k => show (r ≫ φ k) y ∈ M.U a by rw [hq k]; exact ha

theorem exists_normalised {S X X' B B' : Scheme.{0}} (M : LB B) (M' : LB B') (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (φ' : K → (X' ⟶ B')) (ε : K → ℤ) (hε : ∑ k, ε k = 0) (F : X' ⟶ X)
    (e : S ⟶ X') (π : X' ⟶ S) (he : e ≫ π = 𝟙 S) (q : S ⟶ B) (q' : S ⟶ B') (hq : ∀ k, (e ≫ F) ≫ φ k = q)
    (hq' : ∀ k, e ≫ φ' k = q') (w₀ : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F)) (hw : w₀.IsGen) :
    ∃ w : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (t : Z ⟶ S) (z : Z) (a : M.ι) (b : M'.ι), q (t z) ∈ M.U a → q' (t z) ∈ M'.U b →
        gw w (t ≫ e) z (fun _ => a) (fun _ => b) = 1 := by
  let C : M.ι × M'.ι → X'.Opens := fun i =>
    ((LB.LinComb M φ ε).pull F).U (fun _ _ => i.1) ⊓ (LB.LinComb M' φ' ε).U (fun _ => i.2)
  have mem : ∀ (x : S) (a : M.ι) (b : M'.ι), q x ∈ M.U a → q' x ∈ M'.U b → e x ∈ C (a, b) := fun x a b ha hb =>
    ⟨mem_pull.2 (mem_const M φ (e ≫ F) q hq x a ha), mem_const M' φ' e q' hq' x b hb⟩
  obtain ⟨u, hu⟩ := glue_unit (⊤ : S.Opens) (fun i => e ⁻¹ᵁ C i) (fun _ => le_top) (fun x _ => by
      obtain ⟨a, ha⟩ := exists_chart hM (q x)
      obtain ⟨b, hb⟩ := exists_chart hM' (q' x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), mem x a b ha hb⟩)
    (fun i => pullU e (C i) (w₀.s (fun _ _ => i.1, fun _ => i.2))) (fun i j x hx => by
      have hi : e x ∈ C i := hx.1
      have hj : e x ∈ C j := hx.2
      refine (gm_pull (𝟙 S) e x (C i) hi _).trans (Eq.trans ?_ (gm_pull (𝟙 S) e x (C j) hj _).symm)
      rw [Category.id_comp]
      have h := (isGen_iff w₀).1 hw S e x (fun _ => i.1) (fun _ => j.1) (fun _ => i.2) (fun _ => j.2)
        (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
      refine h.trans ((congrArg (· * _) ((congrArg₂ (fun s t => s * t⁻¹)
        (gm_const M φ ε hε (e ≫ F) q hq x i.1 j.1 (mem_pull.1 hi.1) (mem_pull.1 hj.1))
        (gm_const M' φ' ε hε e q' hq' x i.2 j.2 hi.2 hj.2)).trans (mul_inv_cancel 1))).trans (_root_.one_mul _)))
  let c : Γ(X', ⊤)ˣ := res (fun _ _ => trivial : (⊤ : X'.Opens) ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ u⁻¹)
  refine ⟨DVR.scaleGen c w₀, DVR.scaleGen_isGen c w₀ hw, fun Z t z a b ha hb => ?_⟩
  have hm : e (t z) ∈ C (a, b) := mem (t z) a b ha hb
  have h₁ : gm (t ≫ e) z (C (a, b)) (res le_top c) = (gm t z ⊤ u)⁻¹ := by
    refine (gm_res (t ≫ e) z le_top hm c).trans ((gm_res (t ≫ e) z (V := ⊤) _ trivial _).trans
      ((gm_pull (t ≫ e) π z ⊤ trivial _).trans ?_))
    rw [Category.assoc, he, Category.comp_id, map_inv]
  have h₂ : gm (t ≫ e) z (C (a, b)) (w₀.s (fun _ _ => a, fun _ => b)) = gm t z ⊤ u :=
    (gm_pull t e z (C (a, b)) hm _).symm.trans ((congrArg (gm t z (e ⁻¹ᵁ C (a, b))) (hu (a, b)).symm).trans
      (gm_res t z le_top hm u))
  exact (map_mul (gm (t ≫ e) z (C (a, b))) _ _).trans ((congrArg₂ (· * ·) h₁ h₂).trans (inv_mul_cancel _))

theorem lift_one_psum {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (I : Finset (Fin 2)) :
    lift (1 : T ⟶ G) 1 ≫ psum G (x2 G) I = 1 := by
  have h : (fun k => lift (1 : T ⟶ G) 1 ≫ x2 G k) = fun _ => 1 := by
    funext k
    fin_cases k
    · exact lift_fst _ _
    · exact lift_snd _ _
  rw [comp_psum, h, psum_one]

theorem origin_square {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {β : G'.left ⟶ G.left} {β₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsGrpPullback G' G f β) (hs : IsSquare β β₂)
    (T : Over S') :
    (lift (1 : T ⟶ G') 1).left ≫ β₂ = (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left := by
  have h₁ : (1 : T ⟶ G').left ≫ β = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h T))
  have a₁ : ((lift (1 : T ⟶ G') 1).left ≫ β₂) ≫ (fst G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
    rw [Category.assoc, hs.1, ← Category.assoc, ← Over.comp_left, lift_fst, h₁]
  have a₂ : ((lift (1 : T ⟶ G') 1).left ≫ β₂) ≫ (snd G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
    rw [Category.assoc, hs.2, ← Category.assoc, ← Over.comp_left, lift_snd, h₁]
  have b₁ : (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left ≫ (fst G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (lift_fst (1 : Over.mk (T.hom ≫ f) ⟶ G) (1 : Over.mk (T.hom ≫ f) ⟶ G))
  have b₂ : (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left ≫ (snd G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (lift_snd (1 : Over.mk (T.hom ≫ f) ⟶ G) (1 : Over.mk (T.hom ≫ f) ⟶ G))
  exact pullback.hom_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)

theorem exists_lamVal_origin {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} {β₂ : (G2 G').left ⟶ (G2 G).left} {M : LB G.left}
    {M' : LB G'.left} (hM : M.IsLB) (hM' : M'.IsLB) (h : IsGrpPullback G' G f β) (hs : IsSquare β β₂)
    (H : LBIso (abelian₂ G' M') ((abelian₂ G M).pull β₂)) :
    ∃ w : LB.Iso (abelian₂ G' M') ((abelian₂ G M).pull β₂), w.IsGen ∧ ∀ (T : Over S') z J J', Good M z J → Good M' z J' →
      lamVal w (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J J' = 1 := by
  obtain ⟨w₀, hw₀⟩ := H
  let e : (𝟙_ (Over S')).left ⟶ (G2 G').left := (lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
  let q : (𝟙_ (Over S')).left ⟶ G.left := (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left
  let q' : (𝟙_ (Over S')).left ⟶ G'.left := (1 : 𝟙_ (Over S') ⟶ G').left
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ β₂) ≫ (psum G (x2 G) I.down).left = q := fun I =>
    (congrArg (· ≫ (psum G (x2 G) I.down).left) (origin_square h hs (𝟙_ (Over S')))).trans
      (congrArg (fun z => z.left) (lift_one_psum G (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) I.down))
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum G' (x2 G') I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (lift_one_psum G' (T := 𝟙_ (Over S')) I.down)
  obtain ⟨w, hw, hv⟩ := exists_normalised M M' hM hM' (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum G (x2 G) I.down).left) (fun I => (psum G' (x2 G') I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) β₂ e (toUnit (G2 G')).left
    (congrArg (fun z => z.left) (toUnit_unique (lift (1 : 𝟙_ (Over S') ⟶ G') 1 ≫ toUnit (G2 G')) (𝟙 _))) q q' hq hq'
    w₀ hw₀
  refine ⟨w, hw, fun T z J J' hJ hJ' => ?_⟩
  have hp : (lift (1 : T ⟶ G') (1 : T ⟶ G')).left = (toUnit T).left ≫ e := by
    show _ = (toUnit T ≫ lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
    rw [comp_lift, MonObj.comp_one]
  have key : ∀ (p : T.left ⟶ (G2 G').left) (j : (abelian₂ G M).ι) (k : (abelian₂ G' M').ι),
      (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ β₂ ≫ (psum G (x2 G) I.down).left)) = j →
      (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum G' (x2 G') I.down).left)) = k →
      lamVal w p z J J' = gw (L := abelian₂ G M) (L' := abelian₂ G' M') w p z j k := by
    rintro p _ _ rfl rfl
    rfl
  rw [hp]
  refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
    (funext fun I => ?_)).trans (hv T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
  · rw [← hq I, Category.assoc, Category.assoc]
  · rw [← hq' I, Category.assoc]

theorem exists_normalised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → letI := P.isAb.comm; ∃ w : LB.Iso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂), w.IsGen ∧ ∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good P.L z J' → lamVal w (lift (1 : T ⟶ P.A) (1 : T ⟶ P.A)).left z J J' = 1 :=
  fun _ _ _ _ _ _ Q _ P _ _ hpb hs H =>
    letI := P.isAb.comm
    exists_lamVal_origin Q.M.isLB P.isLB hpb hs H

end GlobalTheory.PolDeg.NormIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalChartLiftsOfMorphism
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

section Chart

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

theorem chart_spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem chart_spMap_inj {A B : Type} [CommRing A] [CommRing B] {a b : A →+* B} (e : spMap a = spMap b) : a = b := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

variable (hI : I ^ 2 = 0) {X₀ Z₀ X Z : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {t₀ : Z₀ ⟶ Sp R₀} {s : X ⟶ Sp R}
  {t : Z ⟶ Sp R} {i : X₀ ⟶ X} {k : Z₀ ⟶ Z} {S : Sys I π s₀} {S' : Sys I π t₀} (P : S.Presents s i)
  (P' : S'.Presents t k) {f₀ : Z₀ ⟶ X₀} {f : Z ⟶ X} (hkf : k ≫ f = f₀ ≫ i)


include hkf in
theorem chart_red (p : Pair f₀) :
    spMap (S'.p (Opposite.op p.1.1)) ≫ P'.y (Opposite.op p.1.1) ≫ f =
      spMap (GlobalTheory.CechDR.secPull s₀ t₀ p) ≫ spMap (S.p (Opposite.op p.1.2)) ≫ P.y (Opposite.op p.1.2) := by
  rw [← Category.assoc, P'.red, P.red, Category.assoc, hkf, ← Category.assoc, ← Category.assoc,
    ← GlobalTheory.CechDR.secPull_affPt s₀ t₀ p, Category.assoc]


include hI hkf in
theorem chart_range (p : Pair f₀) :
    Set.range ⇑(P'.y (Opposite.op p.1.1) ≫ f) ⊆ Set.range ⇑(P.y (Opposite.op p.1.2)) := by
  rintro _ ⟨q, rfl⟩
  obtain ⟨q₀, rfl⟩ := (S'.surjective_spMap_p hI (Opposite.op p.1.1)).surj q
  have e := congrArg (fun g ↦ g q₀) (chart_red P P' hkf p)
  simp only [Scheme.Hom.comp_apply] at e
  rw [Scheme.Hom.comp_apply, e]
  exact ⟨_, rfl⟩

def chartMor (p : Pair f₀) : Sp (S'.F.obj (Opposite.op p.1.1)) ⟶ Sp (S.F.obj (Opposite.op p.1.2)) :=
  haveI := P.isOpen (Opposite.op p.1.2)
  IsOpenImmersion.lift _ _ (chart_range hI P P' hkf p)

theorem chartMor_fac (p : Pair f₀) :
    chartMor hI P P' hkf p ≫ P.y (Opposite.op p.1.2) = P'.y (Opposite.op p.1.1) ≫ f :=
  haveI := P.isOpen (Opposite.op p.1.2)
  IsOpenImmersion.lift_fac _ _ _

def chartRing (p : Pair f₀) : S.F.obj (Opposite.op p.1.2) →+* S'.F.obj (Opposite.op p.1.1) :=
  (Spec.preimage (chartMor hI P P' hkf p)).hom

theorem spMap_chartRing (p : Pair f₀) : spMap (chartRing hI P P' hkf p) = chartMor hI P P' hkf p := by
  simp only [spMap, chartRing, CommRingCat.ofHom_hom]
  exact Spec.map_preimage _

theorem chart_ext {A : Type} [CommRing A] (U : AffOp X₀) {a b : S.F.obj U →+* A}
    (e : spMap a ≫ P.y U = spMap b ≫ P.y U) : a = b :=
  haveI := P.isOpen U
  chart_spMap_inj ((cancel_mono (P.y U)).1 e)

include hkf in
theorem chartRing_fac (p : Pair f₀) :
    spMap (chartRing hI P P' hkf p) ≫ P.y (Opposite.op p.1.2) = P'.y (Opposite.op p.1.1) ≫ f := by
  rw [spMap_chartRing, chartMor_fac]


include hkf in
theorem chartRing_comp_algebraMap (hf : f ≫ s = t) (p : Pair f₀) :
    (chartRing hI P P' hkf p).comp (algebraMap R (S.F.obj (Opposite.op p.1.2))) =
      algebraMap R (S'.F.obj (Opposite.op p.1.1)) := by
  refine chart_spMap_inj ?_
  rw [chart_spMap_comp, ← P.base, ← Category.assoc, chartRing_fac, Category.assoc, hf, P'.base]

def chartAlg (hf : f ≫ s = t) (p : Pair f₀) : S.F.obj (Opposite.op p.1.2) →ₐ[R] S'.F.obj (Opposite.op p.1.1) :=
  { chartRing hI P P' hkf p with
    commutes' := fun r ↦ congrArg (fun g ↦ g r) (chartRing_comp_algebraMap hI P P' hkf hf p) }


include hkf in
theorem chartRing_red (p : Pair f₀) :
    (S'.p (Opposite.op p.1.1)).comp (chartRing hI P P' hkf p) =
      (GlobalTheory.CechDR.secPull s₀ t₀ p).comp (S.p (Opposite.op p.1.2)) := by
  refine chart_ext P _ ?_
  rw [chart_spMap_comp, chart_spMap_comp, Category.assoc, Category.assoc, chartRing_fac, chart_red P P' hkf p]


include hkf in
theorem chartRing_nat {p q : Pair f₀} (a : q ≤ p) (b : S.F.obj (Opposite.op p.1.2)) :
    mp S'.F (homOfLE (Pair.le_fst a)).op (chartRing hI P P' hkf p b) =
      chartRing hI P P' hkf q (mp S.F (homOfLE (Pair.le_snd a)).op b) := by
  have e : ((mp S'.F (homOfLE (Pair.le_fst a)).op : _ →+* _)).comp (chartRing hI P P' hkf p) =
      (chartRing hI P P' hkf q).comp (mp S.F (homOfLE (Pair.le_snd a)).op : _ →+* _) := by
    refine chart_ext P _ ?_
    rw [chart_spMap_comp, chart_spMap_comp, Category.assoc, Category.assoc, chartRing_fac, P.nat,
      chartRing_fac, ← Category.assoc, P'.nat]
  exact congrArg (fun g ↦ g b) e

end Chart

end GlobalTheory.Obs

namespace GlobalTheory.Obs

theorem exists_chart_lifts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (f : Z ⟶ X), f ≫ s = t → k ≫ f = f₀ ≫ i → ∃ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l ∧ (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l := by
  intro R R₀ _ _ I hI π _ _ X₀ Z₀ X Z s₀ t₀ s t i k _ _ S S' P P' f₀ h f hf hkf
  refine ⟨fun T ↦ chartAlg hI P P' hkf hf T.unop, fun T b ↦ ?_, fun T T' a b ↦ ?_⟩
  · exact congrArg (fun g ↦ g b) (chartRing_red hI P P' hkf T.unop)
  · exact chartRing_nat hI P P' hkf (leOfHom a.unop) b

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroScalarWeightCuspFormComponent
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.ScalarCusp

theorem bdd_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (hp : X.p0 = 0 ∨ X.p0 = r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) :
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C := by
  obtain ⟨R, hR⟩ := GlobalTheory.orthonormal_frames_bounded_of_definite r X hp
  let K : Set (Frame X.Ψ r) := {x | X.IsOrtho x}
  have hKd : K ⊆ X.dom := fun x hx => PIW.FdPA.orthonormal_domain r X x hx
  have hKc : IsClosed K := by
    have e : K = ⋂ τ : X.Ψ, {x : Frame X.Ψ r | gram τ.1 X.Gm (mat x τ) =
        Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)} := by
      ext x; simp [K, Data.IsOrtho]
    rw [e]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    unfold gram hermC col mat
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.of_apply]
    fun_prop
  have hKb : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max R 0, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun τ => ?_
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun b => ?_
    exact (hR x hx τ a b).trans (le_max_left _ _)
  obtain ⟨C, hC⟩ := (Metric.isCompact_of_isClosed_isBounded hKc hKb).exists_bound_of_continuousOn
    (hP.1.continuousOn.mono hKd)
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨b, hb, ho⟩ := (orthonormalFlagTranslate_holds r X).1 x hx
  rw [← (orthonormalFlagTranslate_holds r X).2.1 la P hP.2.1 x hx b hb,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit X la P (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho X ho)]
  exact hC _ ho

end GlobalTheory.ScalarCusp

namespace GlobalTheory.ScalarCusp

theorem exists_scalar_cusp_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL σ hσ Z
  have hU := hL.unf σ hσ
  have hr : r = Dw.p + Dw.q := hU.1
  obtain ⟨k, hk⟩ := GlobalTheory.FlatCore.framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  by_cases hdef : Dw.p = 0 ∨ Dw.q = 0
  · obtain ⟨z, hz⟩ := GlobalTheory.FlatLine.framesOn_nonempty hU Z
    have hz' : z.1 = k ∧ z.2 ∈ ((U σ).X z.1).dom := by rw [hk] at hz; exact hz
    obtain ⟨n, hn, he, f, hf, hne⟩ :=
      GlobalTheory.Reg.exists_even_sec_evR_ne_zero E H Dw l Xo c σ ((U σ).un z.1 ⟨z.2, hz'.2⟩)
    have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun τ i i' _ => le_rfl, he⟩
    refine ⟨n, hn, he, f, ?_, z, hz, ?_⟩
    · rw [mem_cusp]
      refine ⟨hf, fun σ' hσ' => holCusp_mem_holSub _ _ fun j => ?_⟩
      have hU' := hL.unf σ' hσ'
      have hs := hU'.2.2.2.2.1 0 n hD f hf j
      obtain ⟨τ0⟩ : Nonempty ((U σ').X j).Ψ := by
        obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
        by_cases h : τ ∈ ((U σ').X j).Ψ
        · exact ⟨⟨τ, h⟩⟩
        · exact ⟨⟨_, not_not.mp (fun h' => h ((((U σ').X j).cmType τ).mpr h'))⟩⟩
      have hp0 : ((U σ').X j).p0 = 0 ∨ ((U σ').X j).p0 = r := by
        rw [(hU'.2.1 j).1]; omega
      exact GlobalTheory.BoundedCusp.mem_SS_of_definite _ _ τ0 hp0 _ ⟨hs, bdd_of_definite _ hp0 _ _ hs⟩
    · have e : rdU (U σ) f z.1 z.2 = toC (evR Xo c f ((U σ).un z.1 ⟨z.2, hz'.2⟩)) := dif_pos hz'.2
      rw [e]
      exact hne
  · push_neg at hdef
    have hp : 1 ≤ Dw.p := Nat.one_le_iff_ne_zero.2 hdef.1
    have hq : 1 ≤ Dw.q := Nat.one_le_iff_ne_zero.2 hdef.2
    by_cases hrun : ∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ 16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ (Dw.p ≤ m ∨ Dw.q ≤ m)
    · obtain ⟨m, hm1, hm4, hf2, hrd, hpm⟩ := hrun
      have hr2 : 2 ≤ r := by omega
      have hf1 : 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E := le_trans (Nat.one_le_pow _ _ hm1) hm4
      have hfr : 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r := by nlinarith
      obtain ⟨q', R0, -, -, hrunOK⟩ := GlobalTheory.RunParametersBound.exists_run_bound E r m hfr hm1 hm4 hf2 hrd
      have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
      obtain ⟨i, J, _, cf, xs, f, hi, -, -, -, hf, -, hnz, -⟩ :=
        GlobalTheory.EtaAn.exists_etaRule_cusp_ne_zero_bounds E H Dw l Xo c r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) σ
          (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hL.unf σ hσ)) hσ hT hr2 5 (by decide)
          (by norm_num) 1 q' m R0 hrunOK hpm
      obtain ⟨y, hy, hne⟩ := hnz k
      have hf' : f ∈ cusp Xo c U 0 (2 * 5 ^ 4 * r * i) := hf
      refine ⟨2 * 5 ^ 4 * r * i, by positivity, ⟨5 ^ 4 * r * i, by ring⟩, f, hf', ⟨k, y⟩, ?_, hne⟩
      rw [hk]
      exact ⟨rfl, hy⟩
    · exact _root_.GlobalTheory.ScalarCuspTwist.exists_scalar_cusp_indefinite E H Dw l Xo c r U x hL hp hq hrun σ hσ Z

end GlobalTheory.ScalarCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatePrimitiveOfAmpleKTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PrimitiveNonSym
open GlobalTheory.PrimitiveOverField GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.UU

theorem exists_point_translate_of_ample : ∀ (A : Type) [Field A] [IsAlgClosed A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  intro K _ _ B _ _ g L O hB _ hLl _ hK hΘ hO hu
  by_contra hno
  have := hB.smooth
  have := hB.proper
  have hpr : IsProjBy B.hom := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K B hB
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ B.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f B.hom u → IsProjBy f :=
    fun R _ u X π f h => GlobalTheory.StabFlat.isProjBy_baseChange hpr h
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls L hLl) (fst B B) (snd B B) -
    CechPic.pull (snd B B).left (cls O hO))
  have hpq : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ B, (toUnit B ≫ x).left = B.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit B)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (toUnit B ≫ x) (𝟙 B)).left) =
      lam (cls L hLl) (toUnit B ≫ x) (𝟙 B) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (𝟙 B) (toUnit B ≫ x)).left) =
      lam (cls L hLl) (toUnit B ≫ x) (𝟙 B) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst B B).left ≫ B.hom) F := by
    refine (_root_.GlobalTheory.ProductAcyclic.acyclic_of_over_affine_and_converse K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
    refine ⟨(lift (toUnit B ≫ x') (𝟙 B)).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit B ≫ x') (𝟙 B))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit B ≫ x') (𝟙 B))
    · rw [s₁, lam_sub, lam_lam hLl hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero, lam_const]
      refine fun e => hno ⟨x', (cls_eq_iff hO (LB.isLB_linComb hLl _ _)).1 (e.symm.trans ?_)⟩
      refine Eq.trans ?_ (cls_linComb hLl _ _ _).symm
      rw [Fin.sum_univ_two, sub_eq_add_neg]
      exact (congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)).symm
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ B.left := η[B].left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hcl : IsClosed ({o (IsLocalRing.closedPoint K)} : Set B.left) := by
    have : IsClosedImmersion (o ≫ B.hom) := by rw [ho]; infer_instance
    have : IsClosedImmersion o := IsClosedImmersion.of_comp o B.hom
    have h := o.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint K}
      (by rw [show ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) = Set.univ from
        Set.eq_univ_of_forall fun z => Subsingleton.elim (α := PrimeSpectrum K) _ _]; exact isClosed_univ)
    exact (congrArg IsClosed Set.image_singleton).mp h
  have all := (_root_.GlobalTheory.ProductAcyclic.acyclic_of_over_affine_and_converse K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance inferInstance F hF).2
    _ hcl (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
      refine ⟨(lift (𝟙 B) (toUnit B ≫ x')).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ x'))
      · rw [s₂, lam_lam hLl hΘ]
      · rw [s₂]
        intro e
        have e₁ : x' = η[B] := (eq_one_of_lam_eq_zero hLl hK x' e).trans (by
          rw [Hom.one_def, toUnit_unit, Category.id_comp])
        have e₂ : x = o := congrArg CommaMorphism.left e₁
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (e₂ ▸ hy)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 B) (toUnit B ≫ η[B])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ η[B]))).trans (cst_left η[B]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ η[B])))
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : Nonempty B.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.PrimitiveNonSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetsInAffineOpenAbelianSchemeRelAmple
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.FinAffNoeth

theorem finAff_of_relAmple_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → FinAff A.left := by
  intro R _ _ A _ hA L hL hR
  exact GlobalTheory.DualCon.FinAffAmple.finAff_of_relAmple R A hA L hL hR

end GlobalTheory.DualCon.FinAffNoeth
end

