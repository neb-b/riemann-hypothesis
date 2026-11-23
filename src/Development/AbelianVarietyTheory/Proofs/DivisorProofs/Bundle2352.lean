module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialCharacterFiniteCommGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFamilyAgreeingSmallExtensionTang
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen.SmallExt

variable {S : Scheme.{0}}

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap]

theorem surjective_spMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (hφ : Function.Surjective φ)
    (hn : ∀ a ∈ RingHom.ker φ, IsNilpotent a) : Surjective (spMap φ) := by
  refine ⟨fun (x : PrimeSpectrum R) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap φ) := by
    rw [range_comap_of_surjective _ _ hφ]
    intro a ha
    obtain ⟨n, hn⟩ := hn a ha
    exact x.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  exact this

theorem pull_wl_comp {A X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) (c : Pic (A ⊗ Z).left) :
    CechPic.pull (A ◁ (f ≫ g)).left c = CechPic.pull (A ◁ f).left (CechPic.pull (A ◁ g).left c) := by
  rw [MonoidalCategory.whiskerLeft_comp, Over.comp_left, pull_comp]

theorem pull_wl_id {A X : Over S} (c : Pic (A ⊗ X).left) : CechPic.pull (A ◁ 𝟙 X).left c = c := by
  rw [MonoidalCategory.whiskerLeft_id, Over.id_left, pull_id]

end GlobalTheory.DualOpen.SmallExt


open GlobalTheory.DualOpen.SmallExt in
theorem GlobalTheory.DualOpen.exists_same_of_smallExt : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : Over S) (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∀ u' : Over.mk s ⟶ U, Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) (ptMap s (Ideal.Quotient.mk (Ideal.span {e})) ≫ u') → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  intro S _ A _ hA U M hMf hMi hMt C _ _ e he hme hne s N hNf u' hsame
  haveI : Smooth A.hom := hA.smooth
  obtain ⟨P, _, i, p, σ, q, hpi, hσi, hqi, hσc, hσs, hM1, hM2⟩ := _root_.GlobalTheory.DualOpen.smallExt_fibre_ring C e he hme hne
  have calc3 := (_root_.GlobalTheory.FamCalc.famCalc S A).2.2.1
  set k := IsLocalRing.ResidueField C
  set π : C →+* C ⧸ Ideal.span {e} := Ideal.Quotient.mk (Ideal.span {e})
  set ρ : C →+* k := IsLocalRing.residue C
  have hfi : (dnFst k).comp (dnInl k) = RingHom.id k := RingHom.ext fun x ↦ rfl
  let TC : Over S := Over.mk s
  let TP : Over S := Over.mk (spMap i ≫ s)
  let Tε : Over S := Over.mk (spMap (dnInl k) ≫ spMap ρ ≫ s)
  let Tk : Over S := Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ spMap ρ ≫ s)
  let jp : TC ⟶ TP := Over.homMk (spMap p) (by
    show spMap p ≫ spMap i ≫ s = s
    rw [← Category.assoc, ← spMap_comp', hpi, spMap_id', Category.id_comp])
  let jσ : TC ⟶ TP := Over.homMk (spMap σ) (by
    show spMap σ ≫ spMap i ≫ s = s
    rw [← Category.assoc, ← spMap_comp', hσi, spMap_id', Category.id_comp])
  let jq : Tε ⟶ TP := Over.homMk (spMap q) (by
    show spMap q ≫ spMap i ≫ s = spMap (dnInl k) ≫ spMap ρ ≫ s
    rw [← Category.assoc, ← spMap_comp', hqi, spMap_comp', Category.assoc])
  let r : TP ⟶ TC := Over.homMk (spMap i) rfl
  let kε : Tk ⟶ Tε := ptMap _ (dnFst k)
  let kc : Tk ⟶ TC := Over.homMk (spMap ρ) (by
    show spMap ρ ≫ s = spMap (dnFst k) ≫ spMap (dnInl k) ≫ spMap ρ ≫ s
    rw [← Category.assoc, ← spMap_comp', hfi, spMap_id', Category.id_comp])
  let k₀ := ptMap s π
  have hjr : jp ≫ r = 𝟙 _ := Over.OverMorphism.ext (by
    show spMap p ≫ spMap i = 𝟙 _
    rw [← spMap_comp', hpi, spMap_id'])
  have hσr : jσ ≫ r = 𝟙 _ := Over.OverMorphism.ext (by
    show spMap σ ≫ spMap i = 𝟙 _
    rw [← spMap_comp', hσi, spMap_id'])
  have hsq : kε ≫ jq = kc ≫ jp := Over.OverMorphism.ext hM2.w.symm
  have hkqr : kε ≫ jq ≫ r = kc := Over.OverMorphism.ext (by
    show spMap (dnFst k) ≫ spMap q ≫ spMap i = spMap ρ
    rw [← spMap_comp' i q, hqi, spMap_comp', ← Category.assoc, ← spMap_comp', hfi, spMap_id', Category.id_comp])
  have hεs : Function.Surjective (dnFst k) := fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩
  have hεn : ∀ a ∈ RingHom.ker (dnFst k), IsNilpotent a := by
    intro a ha
    have h0 : a.fst = 0 := ha
    refine ⟨2, ?_⟩
    ext <;> simp [pow_two, h0]
  have hπn : ∀ a ∈ RingHom.ker π, IsNilpotent a := by
    intro a ha
    rw [Ideal.mk_ker] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    exact ⟨2, by rw [mul_pow, sq e, hme e he, mul_zero]⟩
  have hkεs : Surjective kε.left := surjective_spMap _ hεs hεn
  have hkεc : IsClosedImmersion kε.left := IsClosedImmersion.spec_of_surjective _ hεs
  have hk₀s : Surjective k₀.left := surjective_spMap _ Ideal.Quotient.mk_surjective hπn

  set n := cls N hNf.isLB
  set m := cls M hMf.isLB
  have hd : CechPic.pull (A ◁ k₀).left (n - CechPic.pull (A ◁ u').left m) = 0 := by
    have h := (calc3 _ _ _ N M hNf.isLB hMf.isLB _ _).1 hsame
    rw [map_sub, h, pull_wl_comp, sub_self]
  obtain ⟨d', hd'p, hd'σ⟩ := _root_.GlobalTheory.DualOpen.exists_pic_extend_of_milnor S A TP TC TC _ jp jσ k₀ k₀ hM1 hσc hσs hk₀s _ hd
  have h3 : CechPic.pull (A ◁ kε).left (CechPic.pull (A ◁ jq).left d') = 0 := by
    rw [← pull_wl_comp, hsq, pull_wl_comp, hd'p, map_zero]
  obtain ⟨D, hD, hDc⟩ := cls_surj (CechPic.pull (A ◁ jq).left d')
  have hDf : Fam A D := _root_.GlobalTheory.DualOpen.fam_of_triv_mod_eps S A hA k (spMap (dnInl k) ≫ spMap ρ ≫ s) D hD (by rw [hDc]; exact h3)
  obtain ⟨D₂, hD₂, hD₂c⟩ := cls_surj (CechPic.pull (A ◁ jq).left d' + CechPic.pull (A ◁ (jq ≫ r ≫ u')).left m)
  have hD₂f : Fam A D₂ := (_root_.GlobalTheory.FamCalc.famCalc S A).2.1 Tε U Tε D M hDf hMf (𝟙 _) (jq ≫ r ≫ u') D₂ hD₂
    (Or.inl (by rw [hD₂c, pull_wl_id, hDc]))
  obtain ⟨v, hv⟩ := hMt k (spMap ρ ≫ s) D₂ hD₂f (kε ≫ jq ≫ r ≫ u') ((calc3 _ _ _ D₂ M hD₂ hMf.isLB _ _).2 (by
    rw [hD₂c, map_add (f := _), h3, zero_add, pull_wl_comp kε]))
  have hv' : CechPic.pull (A ◁ jq).left d' + CechPic.pull (A ◁ (jq ≫ r ≫ u')).left m =
      CechPic.pull (A ◁ v).left m := by
    have h := (calc3 _ _ _ D₂ M hD₂ hMf.isLB _ _).1 hv
    rwa [pull_wl_id, hD₂c] at h
  have hglue : kc ≫ u' = kε ≫ v := hMi Tk _ _ ((calc3 _ _ _ M M hMf.isLB hMf.isLB _ _).2 (by
    rw [← hkqr, Category.assoc, Category.assoc, pull_wl_comp kε (jq ≫ r ≫ u'), pull_wl_comp kε v, ← hv', map_add (f := _),
      h3, zero_add]))
  obtain ⟨V, hVa, hV0, -⟩ := exists_isAffineOpen_mem_and_subset (X := U.left) (U := ⊤)
    (x := u'.left (IsLocalRing.closedPoint C)) trivial
  have hu'V : ∀ x, u'.left x ∈ V := fun x ↦
    ((IsLocalRing.specializes_closedPoint (R := C) x).map u'.left.continuous).mem_open V.isOpen hV0
  have hvV : ∀ y, v.left y ∈ V := by
    intro y
    obtain ⟨z, rfl⟩ := hkεs.surj y
    have h := congrArg (fun f ↦ f.left z) hglue
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    rw [← h]
    exact hu'V _
  obtain ⟨w, hw₁, hw₂⟩ := GlobalTheory.T.glue_morphisms_into_affineOpen_milnorSquare S U TP TC Tε Tk jp jq kc kε hM2 V hVa u' v hglue hu'V hvV
  have hunit := _root_.GlobalTheory.DualOpen.units_lift_of_thickening S A hA Tε Tk kε (inferInstanceAs (IsAffine (Sp (DualNumber k)))) hkεc hkεs
  have hE := _root_.GlobalTheory.DualOpen.pic_eq_zero_of_milnor S A TP TC Tε Tk jp jq kc kε hM2 hunit
    (CechPic.pull (A ◁ w).left m - CechPic.pull (A ◁ (r ≫ u')).left m - d') (by
      rw [map_sub, map_sub, ← pull_wl_comp, ← pull_wl_comp, hw₁, ← Category.assoc, hjr, Category.id_comp, hd'p,
        sub_self, sub_zero]) (by
      rw [map_sub, map_sub, ← pull_wl_comp, ← pull_wl_comp, hw₂, ← hv', add_sub_cancel_right, sub_self])
  have hwe : CechPic.pull (A ◁ w).left m = CechPic.pull (A ◁ (r ≫ u')).left m + d' := by
    rw [sub_sub] at hE
    exact sub_eq_zero.1 hE
  refine ⟨jσ ≫ w, (calc3 _ _ _ N M hNf.isLB hMf.isLB _ _).2 ?_⟩
  rw [pull_wl_id, pull_wl_comp, hwe, map_add (f := _), ← pull_wl_comp, ← Category.assoc, hσr, Category.id_comp, hd'σ]
  exact (add_sub_cancel _ _).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LinCombComp

variable {X Y Z : Scheme.{0}}

theorem gm_gen {M : LB Y} {t : LB.Gen M} (ht : t.IsGen) (f : Z ⟶ Y) (z : Z) {i j : M.ι}
    (hi : f z ∈ M.U i) (hj : f z ∈ M.U j) :
    gm f z (M.U i) (t.s i) = gm f z (M.U i ⊓ M.U j) (M.g i j) * gm f z (M.U j) (t.s j) := by
  have hm : f z ∈ M.U i ⊓ M.U j := ⟨hi, hj⟩
  exact (gm_res f z _ hm _).symm.trans ((congrArg (gm f z _) (ht i j)).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res f z _ hm _))))

theorem gm_div (M N : LB Y) (f : Z ⟶ Y) (z : Z) (p q : (LB.div M N).ι)
    (hp : f z ∈ (LB.div M N).U p) (hq : f z ∈ (LB.div M N).U q) :
    gm f z ((LB.div M N).U p ⊓ (LB.div M N).U q) ((LB.div M N).g p q) =
      gm f z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm f z (N.U p.2 ⊓ N.U q.2) (N.g p.2 q.2))⁻¹ := by
  have hm : f z ∈ (LB.div M N).U p ⊓ (LB.div M N).U q := ⟨hp, hq⟩
  show gm f z _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z _ hm _)
    ((map_inv _ _).trans (congrArg _ (gm_res f z _ hm _))))

theorem trF_self {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y)
    (z : Z) (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j) : trF φ ε r z j j = 1 :=
  Finset.prod_eq_one fun k _ => by
    rw [gm_self hL (r ≫ φ k) z (Set.mem_iInter.1 hj k), one_zpow]

theorem trF_sum {L : LB X} {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ)
    (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (r : Z ⟶ Y) (z : Z) (j₁ j₁' : K₁ → L.ι) (j₀ j₀' : K → L.ι) :
    trF (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)) r z (Sum.elim j₁ j₀) (Sum.elim j₁' j₀') =
      trF φ₁ ε₁ r z j₁ j₁' * (trF φ₀ ε₀ r z j₀ j₀')⁻¹ := by
  rw [trF, trF, trF, Fintype.prod_sum_type, ← Finset.prod_inv_distrib]
  congr 1
  exact Finset.prod_congr rfl fun k _ => zpow_neg _ _

theorem wchart_sum_le (L : LB X) {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X))
    (φ₁ : K₁ → (Y ⟶ X)) (j₁ : K₁ → L.ι) (j₀ : K → L.ι) :
    LB.wchart L φ₁ j₁ ⊓ LB.wchart L φ₀ j₀ ≤ LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀) :=
  fun _ hy => Set.mem_iInter.2 fun k => by
    cases k with
    | inl k => exact Set.mem_iInter.1 hy.1 k
    | inr k => exact Set.mem_iInter.1 hy.2 k

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem gm_iso_linComb {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K : Type} [Fintype K]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (u : LB.Iso A (LB.LinComb L φ₀ ε₀)) (hu : u.IsGen)
    (y : Y) (j₀ j₀' : K → L.ι) (a a' : A.ι) (h0 : y ∈ LB.wchart L φ₀ j₀) (ha : y ∈ A.U a)
    (h0' : y ∈ LB.wchart L φ₀ j₀') (ha' : y ∈ A.U a') :
    gm (𝟙 Y) y (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) =
      (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀' * (gm (𝟙 Y) y (A.U a ⊓ A.U a') (A.g a a'))⁻¹) *
        gm (𝟙 Y) y (LB.wchart L φ₀ j₀' ⊓ A.U a') (u.s (j₀', a')) := by
  have hp : (𝟙 Y) y ∈ (LB.div (LB.LinComb L φ₀ ε₀) A).U (j₀, a) := ⟨h0, ha⟩
  have hq : (𝟙 Y) y ∈ (LB.div (LB.LinComb L φ₀ ε₀) A).U (j₀', a') := ⟨h0', ha'⟩
  have e1 := gm_gen hu (𝟙 Y) y hp hq
  have e2 := gm_div (LB.LinComb L φ₀ ε₀) A (𝟙 Y) y (j₀, a) (j₀', a') hp hq
  have e3 : gm (𝟙 Y) y (LB.wchart L φ₀ j₀ ⊓ LB.wchart L φ₀ j₀') ((LB.LinComb L φ₀ ε₀).g j₀ j₀') =
      trF φ₀ ε₀ (𝟙 Y) y j₀ j₀' := gm_linComb L φ₀ ε₀ (𝟙 Y) y j₀ j₀' h0 h0'
  rw [e2] at e1
  exact e1.trans (congrArg (fun t => t * (gm (𝟙 Y) y (A.U a ⊓ A.U a') (A.g a a'))⁻¹ *
    gm (𝟙 Y) y (LB.wchart L φ₀ j₀' ⊓ A.U a') (u.s (j₀', a'))) e3)

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem gm_gen_sum {X Y : Scheme.{0}} {L : LB X} {K K₁ : Type} [Fintype K] [Fintype K₁]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ)
    (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))) (hc : c.IsGen)
    (y : Y) (j₁ j₁' : K₁ → L.ι) (j₀ j₀' : K → L.ι) (h1 : y ∈ LB.wchart L φ₁ j₁) (h0 : y ∈ LB.wchart L φ₀ j₀)
    (h1' : y ∈ LB.wchart L φ₁ j₁') (h0' : y ∈ LB.wchart L φ₀ j₀') :
    gm (𝟙 Y) y (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) =
      (trF φ₁ ε₁ (𝟙 Y) y j₁ j₁' * (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀')⁻¹) *
        gm (𝟙 Y) y (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁' j₀')) (c.s (Sum.elim j₁' j₀')) := by
  rw [← trF_sum]
  exact gen_trans hc (𝟙 Y) y (wchart_sum_le L φ₀ φ₁ j₁ j₀ ⟨h1, h0⟩) (wchart_sum_le L φ₀ φ₁ j₁' j₀' ⟨h1', h0'⟩)

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem exists_iso_comp_val {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K K₁ : Type} [Fintype K] [Fintype K₁]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (hL : L.IsLB) (hA : A.IsLB)
    (u : LB.Iso A (LB.LinComb L φ₀ ε₀)) (hu : u.IsGen)
    (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))) (hc : c.IsGen) :
    ∃ u' : LB.Iso A (LB.LinComb L φ₁ ε₁), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z)
      (J : (Z ⟶ X) → L.ι) (a : A.ι), q z ∈ A.U a → Good L z J →
      gm q z _ (u'.s (fun k => J (q ≫ φ₁ k), a)) = gm q z _ (u.s (fun k => J (q ≫ φ₀ k), a)) * val c q z J := by
  have eu := gm_iso_linComb φ₀ ε₀ u hu
  have ec := gm_gen_sum φ₀ ε₀ φ₁ ε₁ c hc
  have glue : ∀ (j₁ : K₁ → L.ι) (a : A.ι), ∃ s : Γ(Y, LB.wchart L φ₁ j₁ ⊓ A.U a)ˣ,
      ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K → L.ι), q z ∈ LB.wchart L φ₁ j₁ → q z ∈ A.U a →
        q z ∈ LB.wchart L φ₀ j₀ →
        gm q z (LB.wchart L φ₁ j₁ ⊓ A.U a) s =
          gm q z (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) *
            gm q z (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) := by
    intro j₁ a
    obtain ⟨W, hW⟩ : ∃ W : (K → L.ι) → Y.Opens, ∀ j₀, W j₀ = LB.wchart L φ₁ j₁ ⊓ A.U a ⊓ LB.wchart L φ₀ j₀ :=
      ⟨_, fun _ => rfl⟩
    have l₀ : ∀ j₀, W j₀ ≤ LB.wchart L φ₁ j₁ ⊓ A.U a := fun j₀ => (hW j₀).le.trans inf_le_left
    have l₁ : ∀ j₀, W j₀ ≤ LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀) := fun j₀ y hy => by
      rw [hW] at hy; exact wchart_sum_le L φ₀ φ₁ j₁ j₀ ⟨hy.1.1, hy.2⟩
    have l₂ : ∀ j₀, W j₀ ≤ LB.wchart L φ₀ j₀ ⊓ A.U a := fun j₀ y hy => by
      rw [hW] at hy; exact ⟨hy.2, hy.1.2⟩
    obtain ⟨uu, hu'⟩ : ∃ uu : ∀ j₀, Γ(Y, W j₀)ˣ, ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K → L.ι),
        q z ∈ W j₀ → gm q z (W j₀) (uu j₀) =
          gm q z (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) *
            gm q z (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) :=
      ⟨fun j₀ => res (l₁ j₀) (c.s (Sum.elim j₁ j₀)) * res (l₂ j₀) (u.s (j₀, a)), fun Z' q z j₀ h =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res q z (l₁ j₀) h _) (gm_res q z (l₂ j₀) h _))⟩
    have memW : ∀ y j₀, y ∈ W j₀ ↔ (y ∈ LB.wchart L φ₁ j₁ ∧ y ∈ A.U a) ∧ y ∈ LB.wchart L φ₀ j₀ := fun y j₀ => by
      rw [hW]; exact Iff.rfl
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart L φ₁ j₁ ⊓ A.U a) W l₀ (fun y hy => by
        choose j₀ hj₀ using fun k => exists_chart hL (φ₀ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j₀, (memW y j₀).2 ⟨hy, Set.mem_iInter.2 hj₀⟩⟩) uu (fun j₀ j₀' y hy => by
        obtain ⟨⟨h1, ha⟩, h0⟩ := (memW y j₀).1 hy.1
        obtain ⟨-, h0'⟩ := (memW y j₀').1 hy.2
        refine (hu' Y (𝟙 Y) y j₀ hy.1).trans (Eq.trans ?_ (hu' Y (𝟙 Y) y j₀' hy.2).symm)
        rw [ec y j₁ j₁ j₀ j₀' h1 h0 h1 h0', eu y j₀ j₀' a a h0 ha h0' ha, trF_self hL φ₁ ε₁ (𝟙 Y) y j₁ h1,
          gm_self hA (𝟙 Y) y ha, _root_.one_mul, _root_.inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, _root_.inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z' q z j₀ h1 ha h0 => ?_⟩
    have hy : q z ∈ W j₀ := (memW _ j₀).2 ⟨⟨h1, ha⟩, h0⟩
    exact (gm_res q z (l₀ j₀) hy s).symm.trans ((congrArg (gm q z (W j₀)) (hs j₀)).trans (hu' Z' q z j₀ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun p p' => unit_ext fun y hy => ?_, fun Z q z J a ha hJ => ?_⟩
  · obtain ⟨⟨h1, ha⟩, h1', ha'⟩ := hy
    choose j₀ hj₀ using fun k => exists_chart hL (φ₀ k y)
    have h0 : y ∈ LB.wchart L φ₀ j₀ := Set.mem_iInter.2 hj₀
    have key : gm (𝟙 Y) y (LB.wchart L φ₁ p.1 ⊓ A.U p.2) (s p.1 p.2) =
        (trF φ₁ ε₁ (𝟙 Y) y p.1 p'.1 * (gm (𝟙 Y) y (A.U p.2 ⊓ A.U p'.2) (A.g p.2 p'.2))⁻¹) *
          gm (𝟙 Y) y (LB.wchart L φ₁ p'.1 ⊓ A.U p'.2) (s p'.1 p'.2) := by
      rw [hs p.1 p.2 Y (𝟙 Y) y j₀ h1 ha h0, hs p'.1 p'.2 Y (𝟙 Y) y j₀ h1' ha' h0,
        ec y p.1 p'.1 j₀ j₀ h1 h0 h1' h0, eu y j₀ j₀ p.2 p'.2 h0 ha h0 ha', trF_self hL φ₀ ε₀ (𝟙 Y) y j₀ h0,
        _root_.inv_one, _root_.mul_one, _root_.one_mul, _root_.mul_mul_mul_comm, _root_.mul_assoc]
    have hm : y ∈ (LB.div (LB.LinComb L φ₁ ε₁) A).U p ⊓ (LB.div (LB.LinComb L φ₁ ε₁) A).U p' :=
      ⟨⟨h1, ha⟩, h1', ha'⟩
    have ed := (gm_div _ _ (𝟙 Y) y p p' hm.1 hm.2).trans
      (congrArg (· * _) (gm_linComb L φ₁ ε₁ (𝟙 Y) y p.1 p'.1 h1 h1'))
    exact (gm_res _ y _ hm _).trans (key.trans ((congrArg₂ (· * ·) ed.symm (gm_res _ y _ hm _).symm).trans
      (map_mul _ _ _).symm))
  · have h1 := hJ.mem φ₁ q
    have h0 := hJ.mem φ₀ q
    refine (hs _ a Z q z (fun k => J (q ≫ φ₀ k)) h1 ha h0).trans ((mul_comm _ _).trans (congrArg _ ?_))
    exact (val_of c q z J _ (fun k => by cases k <;> rfl)).symm

end GlobalTheory.LinCombComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCombinationTangentVectorsAffineOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

namespace GlobalTheory.CechKS.LinTan

open GlobalTheory.FlagMod

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem le_preimage_top {T Z : Scheme.{0}} (z : T ⟶ Z) : ⊤ ≤ z ⁻¹ᵁ ⊤ := le_rfl

theorem eq_of_ev {Y : Scheme.{0}} {S : Type} [CommRing S] {U : Y.Opens} (hU : IsAffineOpen U) {z z' : Sp S ⟶ Y}
    (h : ⊤ ≤ z ⁻¹ᵁ U) (h' : ⊤ ≤ z' ⁻¹ᵁ U) (e : ∀ f, ev z U h f = ev z' U h' f) : z = z' := by
  rw [← spMap_ev z hU h, ← spMap_ev z' hU h', RingHom.ext e]

theorem le_preimage_of_fst {Y : Scheme.{0}} {B : Type} [CommRing B] {n : ℕ} {x : Sp B ⟶ Y}
    {w : Sp (TrivSqZeroExt B (Fin n → B)) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) :
    ⊤ ≤ w ⁻¹ᵁ O := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (TrivSqZeroExt B (Fin n → B))) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← hw] at this
  exact this

theorem exists_glue {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (e : A →+* B) (d : Fin n → (A →+* DualNumber B))
    (hd : ∀ a f, (d a f).fst = e f) : ∃ q : A →+* TrivSqZeroExt B (Fin n → B),
      ∀ f, (q f).fst = e f ∧ ∀ a, (q f).snd a = (d a f).snd := by
  refine ⟨{ toFun := fun f => TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr fun a => (d a f).snd,
            map_one' := ?_, map_mul' := fun f g => ?_,
            map_zero' := ?_, map_add' := fun f g => ?_ }, fun f => ⟨add_zero (e f), fun a => zero_add (d a f).snd⟩⟩
  · ext <;> simp
  · ext
    · simp
    · simp [hd, mul_comm]
  · ext <;> simp
  · ext <;> simp

theorem exists_linComb {K B : Type} [CommRing K] [CommRing B] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (Y₀ : Y.affineOpens)
    (φ : K →+* B) (x : Sp B ⟶ Y) (hx : x ≫ p = spMap φ) (hxY : ⊤ ≤ x ⁻¹ᵁ Y₀.1) {n : ℕ}
    (w : Fin n → (Sp (DualNumber B) ⟶ Y)) (hwp : ∀ a, w a ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ))
    (hwx : ∀ a, spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w a = x) (c : Fin n → B) :
    ∃ S : Sp (DualNumber B) ⟶ Y, S ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ) ∧
      spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x ∧
      ∀ O : Y.Opens, ⊤ ≤ x ⁻¹ᵁ O → ∀ f : Γ(Y, O), (valR S O f).snd = ∑ a, c a * (valR (w a) O f).snd := by
  have hwY : ∀ a, ⊤ ≤ w a ⁻¹ᵁ Y₀.1 := fun a => le_preimage_of_red (hwx a) hxY
  obtain ⟨q, hq⟩ := exists_glue (ev x Y₀.1 hxY) (fun a => ev (w a) Y₀.1 (hwY a)) (fun a f => by
    have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom (w a) Y₀.1 (hwY a) (le_preimage_comp _ (hwY a))
    rw [ev_congr (hwx a) _ _ hxY] at this
    rw [this]; rfl)
  let T : Sp (TrivSqZeroExt B (Fin n → B)) ⟶ Y := spMap q ≫ tau Y₀.2
  have hT : ∀ {S : Type} [CommRing S] (σ : TrivSqZeroExt B (Fin n → B) →+* S) (z : Sp S ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ Y₀.1),
      (∀ f, σ (q f) = ev z Y₀.1 hz f) → spMap σ ≫ T = z := fun σ z hz e => by
    rw [← spMap_ev z Y₀.2 hz, ← RingHom.ext (f := σ.comp q) e, ← spMap_comp_spMap, Category.assoc]
    rfl
  let σ : ((Fin n → B) →ₗ[B] B) → (TrivSqZeroExt B (Fin n → B) →+* DualNumber B) := fun l =>
    (TrivSqZeroExt.map l).toRingHom
  have hσ1 : ∀ l r, (σ l r).fst = r.fst := fun l r => TrivSqZeroExt.fst_map l r
  have hσ2 : ∀ l r, (σ l r).snd = l r.snd := fun l r => TrivSqZeroExt.snd_map l r
  have hTx : spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom ≫ T = x := hT _ x hxY fun f => (hq f).1
  have hTw : ∀ a, spMap (σ (LinearMap.proj a)) ≫ T = w a := fun a => hT _ _ (hwY a) fun f => by
    ext
    · rw [hσ1, (hq f).1]
      have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom (w a) Y₀.1 (hwY a) (le_preimage_comp _ (hwY a))
      rw [ev_congr (hwx a) _ _ hxY] at this
      rw [this]; rfl
    · rw [hσ2]; exact (hq f).2 a
  let l : (Fin n → B) →ₗ[B] B := Fintype.linearCombination B c
  have hSx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (spMap (σ l) ≫ T) = x := by
    rw [← Category.assoc, spMap_comp_spMap, ← hTx]
    congr 2
    exact RingHom.ext fun r => hσ1 l r
  have hS : ∀ O : Y.Opens, ⊤ ≤ x ⁻¹ᵁ O → ∀ f : Γ(Y, O),
      (valR (spMap (σ l) ≫ T) O f).snd = ∑ a, c a * (valR (w a) O f).snd := fun O hO f => by
    have hTO : ⊤ ≤ T ⁻¹ᵁ O := le_preimage_of_fst hTx hO
    have key : ∀ l', valR (spMap (σ l') ≫ T) O f = σ l' (ev T O hTO f) := fun l' => by
      rw [valR_eq_ev _ _ (le_preimage_comp _ hTO), ev_spMap _ _ _ hTO]; rfl
    rw [key, hσ2, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hTw a, key, hσ2, smul_eq_mul, mul_comm]; rfl
  refine ⟨spMap (σ l) ≫ T, ?_, hSx, hS⟩
  have hv : ∀ {S : Type} [CommRing S] (ψ : K →+* S) (f : Γ(Sp K, ⊤)),
      valR (spMap ψ) ⊤ f = ψ (ev (𝟙 (Sp K)) ⊤ (le_preimage_top _) f) := fun ψ f => by
    rw [← Category.comp_id (spMap ψ), valR_eq_ev _ _ (le_preimage_top _), ev_spMap _ _ _ (le_preimage_top _)]; rfl
  refine eq_of_ev (isAffineOpen_top (Sp K)) (le_preimage_top _) (le_preimage_top _) fun f => ?_
  rw [← valR_eq_ev, ← valR_eq_ev, hv]
  ext
  · have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom ((spMap (σ l) ≫ T) ≫ p) ⊤ (le_preimage_top _) (le_preimage_top _)
    rw [ev_congr (z' := spMap φ) (by rw [← Category.assoc, hSx, hx]) _ _ (le_preimage_top _)] at this
    have h2 := RingHom.congr_fun this f
    rw [← valR_eq_ev, hv] at h2
    rw [valR_eq_ev _ _ (le_preimage_top _)]
    exact h2.symm
  · rw [valR_comp_app, hS (p ⁻¹ᵁ ⊤) (le_preimage_top (x ≫ p))]
    simp only [← valR_comp_app, hwp, hv]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.CechKS.LinTan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialAdditiveFamilyKilledByIsogeny
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

theorem exists_nontriv_family : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite N.hom → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → i ≠ 1 → ∃ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB ∧ IsAdditive M ∧ Triv (ev M (fst A T ≫ q) (snd A T)) ∧ ¬ Triv M := by
  intro K _ _ A A' N _ _ _ i q hA hA' hi hq hNf hqf hqfl hqs hker hi1
  have hmono : Mono i := hker.mono_fst_of_mono
  have hcomm : IsCommMonObj A := hA.comm
  have : IsCommMonObj N := AbelianSubgroupFinite.isCommMonObj_of_mono i
  have hN1 : 𝟙 N ≠ (1 : N ⟶ N) := by
    intro h
    apply hi1
    rw [← Category.id_comp i, h, MonObj.one_comp]
  obtain ⟨T, χ, hχ, hne⟩ := _root_.GlobalTheory.CharExists.exists_character_ne_one K N hNf hN1
  obtain ⟨M, e, hM, he⟩ := _root_.GlobalTheory.CharKer.exists_equivGen _ A A' N T i q χ hi hq hqf hqfl hqs hker hχ
  exact ⟨T, M, hM, _root_.GlobalTheory.CharKer.isAdditive_of_isEquivGen K A A' N T i q χ M e hA hA' hi hq hqf hqfl hqs hker hχ hM he,
    _root_.GlobalTheory.CharKer.triv_pull_of_isPullGen _ _ _ M e he.1, fun h => hne (_root_.GlobalTheory.CharKer.character_eq_one_of_triv K A A' N T i q χ M e hA hq hker hM he h)⟩

end GlobalTheory.CharKer
end
end

