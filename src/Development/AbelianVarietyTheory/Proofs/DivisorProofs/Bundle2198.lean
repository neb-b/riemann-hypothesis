module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionIsUnitGermOfLocalIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackFstSndOfAdditiveTrivialKern
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescIsoExists

theorem lbIso_pull_fst_snd : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → P.IsLB → IsAdditive P → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → LBIso (P.pull (pullback.fst (q ▷ B).left (q ▷ B).left)) (P.pull (pullback.snd (q ▷ B).left (q ▷ B).left)) := by
  intro K _ _ A A' B _ _ _ q P _ _ _ hq hP hadd hker
  let f := (q ▷ B).left
  have hw : f ≫ (A' ⊗ B).hom = (A ⊗ B).hom := Over.w (q ▷ B)
  let Z : Over (Sp K) := Over.mk (pullback.fst f f ≫ (A ⊗ B).hom)
  have hsnd : pullback.snd f f ≫ (A ⊗ B).hom = pullback.fst f f ≫ (A ⊗ B).hom := by
    rw [← hw, ← Category.assoc, ← pullback.condition, Category.assoc]
  have hB : (q ▷ B) ≫ snd A' B = snd A B := whiskerRight_snd q B
  have hA : (q ▷ B) ≫ fst A' B = fst A B ≫ q := whiskerRight_fst q B
  have hBl : f ≫ (snd A' B).left = (snd A B).left := by rw [← Over.comp_left, hB]
  have hAl : f ≫ (fst A' B).left = (fst A B).left ≫ q.left := by
    rw [← Over.comp_left, hA, Over.comp_left]
  let a : Z ⟶ A := Over.homMk (pullback.fst f f ≫ (fst A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w])
  let a' : Z ⟶ A := Over.homMk (pullback.snd f f ≫ (fst A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w]; exact hsnd)
  let b : Z ⟶ B := Over.homMk (pullback.fst f f ≫ (snd A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w])
  let u : Z ⟶ A ⊗ B := Over.homMk (pullback.fst f f) rfl
  let u' : Z ⟶ A ⊗ B := Over.homMk (pullback.snd f f) hsnd
  have hu : lift a b = u := by
    ext1
    · ext; simp [a, u]
    · ext; simp [b, u]
  have hu' : lift a' b = u' := by
    ext1
    · ext; simp [a', u']
    · ext
      simp only [b, u', lift_snd, Over.homMk_left, Over.comp_left]
      rw [← hBl, ← Category.assoc, pullback.condition, Category.assoc]
  have hq' : a ≫ q = a' ≫ q := by
    ext
    simp only [a, a', Over.comp_left, Over.homMk_left, Category.assoc]
    rw [← hAl, ← Category.assoc, pullback.condition, Category.assoc]

  have e1 : (pullback.fst f f : pullback f f ⟶ _) = (lift a b).left := by rw [hu]; rfl
  have e2 : (pullback.snd f f : pullback f f ⟶ _) = (lift a' b).left := by rw [hu']; rfl
  refine (cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).1 ?_
  have c1 : cls _ (pull_isLB hP (pullback.fst f f)) = evc hP a b := by
    rw [cls_pull hP]; simp only [evc]; rw [e1]
  have c2 : cls _ (pull_isLB hP (pullback.snd f f)) = evc hP a' b := by
    rw [cls_pull hP]; simp only [evc]; rw [e2]
  rw [c1, c2]
  let k : Z ⟶ A := a' * a⁻¹
  have hinv : a⁻¹ ≫ q = (a ≫ q)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  have hk : k ≫ q = 1 := by
    simp only [k]
    rw [MonObj.mul_comp, hinv, ← hq', mul_inv_cancel]
  have h0 : evc hP k b = 0 := by
    have e := congrArg (CechPic.pull (lift (𝟙 Z) b).left) ((triv_ev_iff hP _ _).1 (hker Z k hk))
    rwa [pull_evc, map_zero, lift_fst_assoc, Category.id_comp, lift_snd] at e
  have ha : a' = k * a := by simp only [k, inv_mul_cancel_right]
  rw [ha, (isAdditive_iff hP).1 hadd, h0, zero_add]

end GlobalTheory.DescIsoExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLocalSectionFamilyUnitAtFinitePoints
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem isUnit_add_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {u m : R}
    (hu : IsUnit u) (hm : ¬ IsUnit m) : IsUnit (u + m) := by
  by_contra h
  have h1 : u + m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hm
  have h3 : u ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ h1 h2
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).mp h3 hu

theorem secFam_unit_at_finite : ∀ (X : Scheme.{0}) (L : LB X) (W : X.Opens) (J : Type) (D : J → X.Opens), (∀ j, D j ≤ W) → ∀ (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (F : Set X), F.Finite → ∀ (a : X → Γ(X, W)), (∀ x ∈ F, x ∈ X.basicOpen (a x)) → (∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ∉ X.basicOpen (a x)) → ∀ (E : X → ∀ j, Γ(X, D j)), (∀ x ∈ F, GlobalTheory.Pinch.IsSecFam L D k hD (E x)) → (∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (E x j))) → ∃ e : ∀ j, Γ(X, D j), GlobalTheory.Pinch.IsSecFam L D k hD e ∧ ∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) := by
  intro X L W J D hDW k hD F hF a ha hsep E hE hEu
  classical
  let r : ∀ j, Γ(X, W) →+* Γ(X, D j) := fun j => (X.presheaf.map (homOfLE (hDW j)).op).hom
  refine ⟨fun j => ∑ x ∈ hF.toFinset, r j (a x) * E x j, ?_, ?_⟩
  ·
    have hr : ∀ j z (hz : z ∈ D j) (s : Γ(X, W)),
        (X.presheaf.germ (D j) z hz).hom (r j s) = (X.presheaf.germ W z (hDW j hz)).hom s := by
      intro j z hz s
      exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hDW j)) z hz s
    intro j j' z hz hz'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hr, hr, hE x (hF.mem_toFinset.mp hx) j j' z hz hz']
    ring
  · intro y hy j hyj
    have hyW : y ∈ W := hDW j hyj
    have hyF : y ∈ hF.toFinset := hF.mem_toFinset.mpr hy
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
    rw [← Finset.add_sum_erase _ _ hyF]
    have hr : ∀ s : Γ(X, W),
        (X.presheaf.germ (D j) y hyj).hom (r j s) = (X.presheaf.germ W y hyW).hom s :=
      fun s => TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hDW j)) y hyj s
    apply isUnit_add_of_not_isUnit
    · rw [hr]
      exact ((X.mem_basicOpen (a y) y hyW).mp (ha y hy)).mul (hEu y hy j hyj)
    · intro hu
      have hmem : ∑ x ∈ hF.toFinset.erase y,
          (X.presheaf.germ (D j) y hyj).hom (r j (a x)) * (X.presheaf.germ (D j) y hyj).hom (E x j)
            ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
        refine Ideal.sum_mem _ fun x hx => ?_
        have hxy : x ≠ y := (Finset.mem_erase.mp hx).1
        have hxF : x ∈ F := hF.mem_toFinset.mp (Finset.mem_erase.mp hx).2
        refine Ideal.mul_mem_right _ _ ?_
        rw [hr, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu'
        exact hsep x hxF y hy (Ne.symm hxy) ((X.mem_basicOpen (a x) y hyW).mpr hu')
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionBaseMulCancelFlatDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secIsMul_cancel : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (q : R), q ≠ 0 → ∀ s t t' : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t' → t = t' := by
  intro R _ _ X p hp L q hq s t t' h h'
  haveI := hp
  have key : ∀ j, t.f j = t'.f j := by
    intro j
    refine fn_ext fun x hx => ?_
    have e1 := GlobalTheory.secIsMul_gs h (𝟙 X) x j hx
    have e2 := GlobalTheory.secIsMul_gs h' (𝟙 X) x j hx
    rw [Category.id_comp] at e1 e2
    have h0 : cst p x q * (gs (𝟙 X) x (L.U j) (t.f j) - gs (𝟙 X) x (L.U j) (t'.f j)) = 0 := by
      rw [mul_sub, ← e1, ← e2, sub_self]
    obtain ⟨u, hu⟩ := GlobalTheory.cst_dvd_of_cst_mul_eq_zero p x (a := q) (b := 0)
      (fun c hc => by
        rcases mul_eq_zero.1 hc with h1 | h1
        · exact absurd h1 hq
        · rw [h1]) h0
    have hz : cst p x (0 : R) = 0 := by
      rw [cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero]
    rw [hz, zero_mul, sub_eq_zero] at hu
    exact hu
  cases t; cases t'
  congr 1
  exact funext key

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionDvdEverywhereSmoothConnectedFib
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DivSpread

theorem dvd_of_specializes {X : Scheme.{0}} {V : Type} [CommRing V] (p : X ⟶ Spec (CommRingCat.of V)) {L : LB X}
    (hL : L.IsLB) (s : LB.Sec L) (a : V) {x y : X} (hyx : y ⤳ x)
    (h : ∀ j, x ∈ L.U j → cst p x a ∣ gs (𝟙 X) x (L.U j) (s.f j)) :
    ∀ j, y ∈ L.U j → cst p y a ∣ gs (𝟙 X) y (L.U j) (s.f j) := by
  intro i hyi
  obtain ⟨k, hxk⟩ : ∃ k, x ∈ L.U k := by
    have : x ∈ (⨆ k, L.U k) := hL.cover ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hyk : y ∈ L.U k := hyx.mem_open (L.U k).isOpen hxk
  have sp : ∀ (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)),
      gs (𝟙 X) y U b = (X.presheaf.stalkSpecializes hyx).hom (gs (𝟙 X) x U b) := by
    intro U hx b
    rw [gs_eq _ y U (hyx.mem_open U.isOpen hx), gs_eq _ x U hx]
    exact (congrArg (fun φ => φ.hom ((Scheme.Hom.app (𝟙 X) U).hom b))
      (X.presheaf.germ_stalkSpecializes _ hyx)).symm
  let c : Γ(X, p ⁻¹ᵁ ⊤) := (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  have hc : ∀ z, gs (𝟙 X) z (p ⁻¹ᵁ ⊤) c = cst p z a := fun z =>
    (gs_pull (𝟙 X) p z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
  obtain ⟨t, ht⟩ := h k hxk
  have hk : cst p y a ∣ gs (𝟙 X) y (L.U k) (s.f k) := by
    refine ⟨(X.presheaf.stalkSpecializes hyx).hom t, ?_⟩
    rw [sp _ hxk, ht, map_mul, ← hc, ← hc, ← sp (p ⁻¹ᵁ ⊤) (show p x ∈ (⊤ : (Spec (CommRingCat.of V)).Opens) from trivial)]
  have hm : y ∈ L.U i ⊓ L.U k := ⟨hyi, hyk⟩
  have e := congrArg (gs (𝟙 X) y (L.U i ⊓ L.U k)) (s.compat i k)
  rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm] at e
  rw [e]
  exact Dvd.dvd.mul_left hk _

theorem exists_specializes_not_dvd {X : Scheme.{0}} {U W : X.Opens} (c : Γ(X, W)) (f : Γ(X, U)) {x : X}
    (hxU : x ∈ U) (hxW : x ∈ W) [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsNoetherianRing (X.presheaf.stalk x)] (h : ¬ gs (𝟙 X) x W c ∣ gs (𝟙 X) x U f) :
    ∃ y, y ⤳ x ∧ Order.coheight y ≤ 1 ∧ ¬ gs (𝟙 X) y W c ∣ gs (𝟙 X) y U f := by
  by_contra H
  push Not at H
  apply h
  obtain ⟨V, hV, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U ⊓ W) (x := x) ⟨hxU, hxW⟩
  have hVU : V ≤ U := fun z hz => (hVle hz).1
  have hVW : V ≤ W := fun z hz => (hVle hz).2
  let fV : Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom f
  let cV : Γ(X, V) := (X.presheaf.map (homOfLE hVW).op).hom c
  have hgf : ∀ z (hz : z ∈ V), gs (𝟙 X) z U f = (X.presheaf.germ V z hz).hom fV := fun z hz => by
    rw [← gs_res (𝟙 X) z hVU hz, gs_eq _ z V hz]; rfl
  have hgc : ∀ z (hz : z ∈ V), gs (𝟙 X) z W c = (X.presheaf.germ V z hz).hom cV := fun z hz => by
    rw [← gs_res (𝟙 X) z hVW hz, gs_eq _ z V hz]; rfl
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have hlocx := hV.isLocalization_stalk ⟨x, hxV⟩
  rw [← Ideal.mem_span_singleton]
  refine GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one _ _ fun Q hQ hQ1 => ?_
  let P : Ideal Γ(X, V) := Q.comap (algebraMap Γ(X, V) (X.presheaf.stalk x))
  have hPp : P.IsPrime := Ideal.comap_isPrime _ Q
  let Pt : PrimeSpectrum Γ(X, V) := ⟨P, hPp⟩
  have hyV : hV.fromSpec Pt ∈ V := by
    have : hV.fromSpec Pt ∈ Set.range hV.fromSpec := ⟨Pt, rfl⟩
    rwa [hV.range_fromSpec] at this
  let yV : V := ⟨hV.fromSpec Pt, hyV⟩
  have hPt : hV.primeIdealOf yV = Pt := hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf yV)
  have hsp : yV.1 ⤳ x := by
    have hle : Pt ≤ hV.primeIdealOf ⟨x, hxV⟩ := by
      show P ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
      rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at this
  let : Algebra Γ(X, V) (X.presheaf.stalk yV.1) := X.presheaf.algebra_section_stalk yV
  have hlocy := hV.isLocalization_stalk yV
  rw [hPt] at hlocy
  have hdim : Order.coheight yV.1 ≤ 1 := by
    rw [← GlobalTheory.ringKrullDim_stalk_le_one_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P (X.presheaf.stalk yV.1)]
    have := IsLocalization.height_under (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl Q
    change (P.height : WithBot ℕ∞) ≤ 1
    rw [show P = Ideal.under Γ(X, V) Q from rfl, this]
    exact_mod_cast hQ1
  obtain ⟨t, ht⟩ := H yV.1 hsp hdim
  rw [hgf _ hyV, hgc _ hyV] at ht
  change algebraMap Γ(X, V) _ fV = algebraMap Γ(X, V) _ cV * t at ht
  obtain ⟨⟨a, w⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl t
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq, ← map_mul] at ht
  obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) ht
  refine ⟨algebraMap Γ(X, V) (X.presheaf.stalk x) (m * w), ?_, ?_⟩
  · exact (P.primeCompl.mul_mem m.2 w.2 : (m : Γ(X, V)) * w ∉ P)
  · rw [Ideal.mem_span_singleton, hgf x hxV, hgc x hxV]
    change algebraMap Γ(X, V) _ cV ∣ algebraMap Γ(X, V) _ (m * w) * algebraMap Γ(X, V) _ fV
    refine ⟨algebraMap Γ(X, V) (X.presheaf.stalk x) (m * a), ?_⟩
    rw [← map_mul, ← map_mul, show (m : Γ(X, V)) * w * fV = m * (fV * w) by ring, hm,
      show (m : Γ(X, V)) * (cV * a) = cV * (m * a) by ring]

theorem eq_of_specializes_of_coheight_le_one {X S : Scheme.{0}} (p : X ⟶ S) [Flat p] {y w : X}
    (hy : Order.coheight y ≤ 1) {P' : S} (hP' : P' ⤳ p y) (hne : P' ≠ p y) (hw : w ⤳ y) (he : p w = p y) :
    w = y := by
  by_contra hne'
  have hlt : y < w := lt_of_le_not_ge (show y ≤ w from hw) (fun h => hne' (hw.antisymm h).eq)
  have hmaxw : IsMax w := by simpa using (Order.coheight_le_coe_iff (n := 1)).1 hy w hlt
  obtain ⟨z, hz, hpz⟩ := Flat.generalizingMap p (show P' ⤳ p w from he ▸ hP')
  have h1 : w ≤ z := hz
  have h2 : z = w := (hz.antisymm (hmaxw h1)).eq
  exact hne (hpz.symm.trans (h2 ▸ he))

theorem mem_of_not_isUnit_cst {X : Scheme.{0}} {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) (y : X)
    (a : R) (h : ¬ IsUnit (cst p y a)) : a ∈ (p y).asIdeal := by
  by_contra ha
  apply h
  have hy : y ∈ p ⁻¹ᵁ ⊤ := show p y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial
  rw [cst, gs_eq p y ⊤ hy]
  refine (X.mem_basicOpen _ y hy).1 ?_
  rw [← Scheme.preimage_basicOpen]
  show p y ∈ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  rw [basicOpen_eq_of_affine]
  exact ha

theorem specializes_of_mem_fibre {X S : Scheme.{0}} (p : X ⟶ S) [GeometricallyIrreducible p] {y : X}
    (hmax : ∀ w, w ⤳ y → p w = p y → w = y) {z : X} (hz : p z = p y) : y ⤳ z := by
  obtain ⟨y', hy'⟩ : y ∈ Set.range (p.fiberι (p y)) := by rw [Scheme.Hom.range_fiberι]; rfl
  obtain ⟨z', hz'⟩ : z ∈ Set.range (p.fiberι (p y)) := by rw [Scheme.Hom.range_fiberι]; exact hz
  have hg : ∀ t, genericPoint (p.fiber (p y)) ⤳ t := fun t => (genericPoint_spec _).specializes trivial
  have hgm : p (p.fiberι (p y) (genericPoint (p.fiber (p y)))) = p y := by
    have : p.fiberι (p y) (genericPoint (p.fiber (p y))) ∈ Set.range (p.fiberι (p y)) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have h1 : p.fiberι (p y) (genericPoint (p.fiber (p y))) = y :=
    hmax _ (by have := (hg y').map (p.fiberι (p y)).continuous; rwa [hy'] at this) hgm
  rw [← h1, ← hz']
  exact (hg z').map (p.fiberι (p y)).continuous

end GlobalTheory.DivSpread

open GlobalTheory.DivSpread in
theorem GlobalTheory.DivSpread.dvd_everywhere : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Smooth p → GeometricallyConnected p → ∀ (e : Spec (CommRingCat.of R) ⟶ X), e ≫ p = 𝟙 _ → ∀ (L : LB X), L.IsLB → ∀ (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X), p x = closedPoint R → ∀ j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t := by
  intro R _ _ _ _ _ X p hsm hgc e he L hL s q hq hcl x j hxj
  have : GeometricallyIntegral p := GlobalTheory.geometricallyIntegral_of_smooth p
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.isNormalScheme_of_smooth p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  by_contra hnot
  let c : Γ(X, p ⁻¹ᵁ ⊤) := (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom q)
  have hc : ∀ z, gs (𝟙 X) z (p ⁻¹ᵁ ⊤) c = cst p z q := fun z =>
    (gs_pull (𝟙 X) p z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
  obtain ⟨y, hyx, hy1, hyn⟩ := exists_specializes_not_dvd c (s.f j) hxj trivial (by rw [hc]; exact hnot)
  rw [hc] at hyn
  have hyj : y ∈ L.U j := hyx.mem_open (L.U j).isOpen hxj
  have hqP : q ∈ (p y).asIdeal := mem_of_not_isUnit_cst p y q fun hu =>
    hyn ⟨hu.unit⁻¹ * gs (𝟙 X) y (L.U j) (s.f j), by rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]⟩
  let P0 : Spec (CommRingCat.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  have hP0 : P0 ⤳ p y := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have hP0' : P0 ≠ p y := fun h => hq (by
    have : q ∈ P0.asIdeal := h ▸ hqP
    exact this)
  have hmax : ∀ w, w ⤳ y → p w = p y → w = y := fun w hw hpe =>
    eq_of_specializes_of_coheight_le_one p hy1 hP0 hP0' hw hpe
  have hey : p (e (p y)) = p y := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have h1 : y ⤳ e (p y) := specializes_of_mem_fibre p hmax hey
  have h2 : e (p y) ⤳ e (closedPoint R) := (IsLocalRing.specializes_closedPoint (p y)).map e.continuous
  have hcm : p (e (closedPoint R)) = closedPoint R := by
    show (e ≫ p) (closedPoint R) = _
    rw [he]; rfl
  exact hyn (dvd_of_specializes p hL s q (h1.trans h2) (fun k hk => hcl _ hcm k hk) j hyj)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentCotangentOfIsTopFormFrameOfVani
section
set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.CotIndep

open IsLocalRing TensorProduct

theorem tmul_D_eq_zero_of_mem_sq (k P : Type*) [CommRing k] [CommRing P] [IsLocalRing P]
    [Algebra k P] {x : P} (hx : x ∈ maximalIdeal P ^ 2) :
    (1 : ResidueField P) ⊗ₜ[P] KaehlerDifferential.D k P x = 0 := by
  have hker : RingHom.ker (algebraMap P (ResidueField P)) = maximalIdeal P := ker_residue
  have hx' : x ∈ RingHom.ker (algebraMap P (ResidueField P)) := by
    rw [hker]; exact Ideal.pow_le_self two_ne_zero hx
  have h0 : (RingHom.ker (algebraMap P (ResidueField P))).toCotangent ⟨x, hx'⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    change x ∈ _ ^ 2
    rw [hker]; exact hx
  have := congrArg (KaehlerDifferential.kerCotangentToTensor k P (ResidueField P)) h0
  rwa [KaehlerDifferential.kerCotangentToTensor_toCotangent, map_zero] at this

theorem linearIndependent_toCotangent {k A P : Type*} [CommRing k] [CommRing A] [CommRing P]
    [IsLocalRing P] (α : k →+* A) (ρ : A →+* P)
    (hρ : letI := ρ.toAlgebra; Algebra.FormallyEtale A P) {n : ℕ} (z : Fin n → A)
    (hω : IsFreeGen A (dForm α z)) (J : Finset (Fin n))
    (hz : ∀ j : J, ρ (z j) ∈ maximalIdeal P) :
    LinearIndependent (ResidueField P)
      (fun j : J => ((maximalIdeal P).toCotangent ⟨ρ (z j), hz j⟩ : CotangentSpace P)) := by
  classical
  have h1 : IsFreeGen P (dForm (ρ.comp α) fun i => ρ (z i)) := by
    have := MorJac.isFreeGen_formMap (D := n) hρ rfl hω
    rwa [formMap_dForm] at this
  letI := (ρ.comp α).toAlgebra
  set κ := ResidueField P
  let φ : Omega (ρ.comp α) →ₗ[P] κ ⊗[P] Omega (ρ.comp α) := TensorProduct.mk P κ _ 1
  have h2 := h1.of_isBaseChange
    (isBaseChange_exteriorPower (TensorProduct.isBaseChange P (Omega (ρ.comp α)) κ) n)
  rw [dForm_eq, exteriorPowerMapOver_ιMulti] at h2
  have h3 : exteriorPower.ιMulti κ n (fun i => φ (dFun (ρ.comp α) (ρ (z i)))) ≠ 0 := by
    intro h0
    rw [h0] at h2
    exact one_ne_zero (h2.1 (a₁ := (1 : κ)) (a₂ := 0) (by simp))
  have h4 : LinearIndependent κ (fun i => φ (dFun (ρ.comp α) (ρ (z i)))) := by
    by_contra h
    exact h3 (AlternatingMap.map_linearDependent _ _ h)
  have h5 := h4.comp (Subtype.val : J → Fin n) Subtype.val_injective
  rw [Fintype.linearIndependent_iff] at h5 ⊢
  intro g hg i
  choose b hb using fun j => residue_surjective (R := P) (g j)
  have hsq : ∑ j : J, b j * ρ (z j) ∈ maximalIdeal P ^ 2 := by
    have e : ∑ j : J, g j • ((maximalIdeal P).toCotangent ⟨ρ (z j), hz j⟩ : CotangentSpace P) =
        (maximalIdeal P).toCotangent (∑ j : J, b j • (⟨ρ (z j), hz j⟩ : maximalIdeal P)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← hb j, ← ResidueField.algebraMap_eq, algebraMap_smul]
    rw [e, Ideal.toCotangent_eq_zero] at hg
    simpa [Submodule.coe_sum] using hg
  have h0 := tmul_D_eq_zero_of_mem_sq k P hsq
  have htk : ∀ j : J, algebraMap P κ (ρ (z j)) = 0 := fun j => by
    rw [ResidueField.algebraMap_eq]; exact (residue_eq_zero_iff _).2 (hz j)
  refine h5 g ?_ i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h0, map_sum, tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul, Algebra.smul_def, mul_one,
    Algebra.smul_def, mul_one, htk, zero_tmul, add_zero, ← hb j, ← ResidueField.algebraMap_eq]
  change (algebraMap P κ (b j)) • ((1 : κ) ⊗ₜ[P] KaehlerDifferential.D k P (ρ (z j))) = _
  rw [smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.CotIndep

namespace GlobalTheory.CotIndep

theorem linearIndependent_cotangent_of_isFrame : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (y : Y) (hy : y ∈ U) (J : Finset (Fin n)) (hz : ∀ j : J, Y.presheaf.germ U y hy (z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : J => Y.presheaf.germ U y hy (z j)) j, hz j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  intro Y _ _ q n _ U z hf y hy J hz
  exact linearIndependent_toCotangent (algX q U) (Y.presheaf.germ U y hy).hom
    (MorJac.formallyEtale_germ hf.affine y hy) z hf.gen J hz

end GlobalTheory.CotIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationIntertwinesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_evaluation_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
    ∀ d' d₁' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = M.co.e x) → (∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d₁'.e xᵀ = M₁.co.e x) →
      HasDbl (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d' d₁' T := by
  first | exact @GlobalTheory.DblTr.hasDbl_transp | exact GlobalTheory.DblTr.hasDbl_transp | (intros; apply GlobalTheory.DblTr.hasDbl_transp <;> assumption)
end

