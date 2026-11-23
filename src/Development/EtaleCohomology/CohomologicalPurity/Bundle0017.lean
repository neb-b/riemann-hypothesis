module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0009
public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPurNatPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurNatPf

open PurPf

theorem fold_map {P' P : Arrow Spc} (ψ : P' ⟶ P) : dbl.map ψ ≫ dbl.fold P = dbl.fold P' ≫ ψ.right := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext <;>
      simp only [dbl.map, dbl.fold, pushout.map] <;> (first
        | (erw [pushout.inl_desc_assoc, Category.assoc]; erw [pushout.inl_desc, pushout.inl_desc_assoc]; simp)
        | (erw [pushout.inr_desc_assoc, Category.assoc]; erw [pushout.inr_desc, pushout.inr_desc_assoc]; simp)
        | (erw [pushout.inl_desc_assoc, Category.assoc, Category.assoc]; erw [pushout.inl_desc, pushout.inl_desc]; simp)
        | (erw [pushout.inr_desc_assoc, Category.assoc, Category.assoc]; erw [pushout.inr_desc, pushout.inr_desc]; simp))

theorem proj_pull (q : ℕ) {P' P : Arrow Spc} (ψ : P' ⟶ P) (n i : ℤ) (c : Ht q (dbl P) n i) :
    Hs.pull q ψ n i (Hs.proj q P n i c) = Hs.proj q P' n i (pull _ (dbl.map ψ) _ n c) := by
  apply Subtype.ext
  change pull _ (dbl.map ψ) _ n (c - _) = _ - _
  rw [map_sub, ← pull_comp, fold_map, pull_comp, ← pull_comp _ (dbl.inr P') (dbl.map ψ), dbl.inr_map, pull_comp]

theorem act_pull (hN : DivisorNaturality) (q : ℕ) [NeZero q] {P' P : Arrow Spc} (ψ : P' ⟶ P) {n m i j : ℤ} (a : Ht q P.right n i)
    (b : Hs q P m j) : Hs.pull q ψ _ _ (Hs.act q a b) = Hs.act q (pull _ ψ.right _ _ a) (Hs.pull q ψ _ _ b) := by
  unfold Hs.act
  rw [proj_pull, (hN q).1]
  congr 2
  rw [← pull_comp, ← pull_comp, fold_map]

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem dbl_map_comp {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) :
    dbl.map α ≫ dbl.map β = dbl.map (α ≫ β) := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext
    · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
      rw [← Category.assoc, inl_map, Category.assoc, inl_map, inl_map, Arrow.comp_right, Category.assoc]
    · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
      rw [← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, dbl.inr_map, Arrow.comp_right, Category.assoc]

theorem pull_pull (q : ℕ) {P'' P' P : Arrow Spc} (α : P'' ⟶ P') (β : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q α n i (Hs.pull q β n i x) = Hs.pull q (α ≫ β) n i x := by
  apply Subtype.ext
  change pull _ (dbl.map α) _ n (pull _ (dbl.map β) _ n x.1) = pull _ (dbl.map (α ≫ β)) _ n x.1
  rw [← pull_comp, dbl_map_comp]

def purOf {d : ℕ} {P : SP d} (t : Tube P) (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(P.X, ⊤))) (n i : ℤ)
    (x : Ht q (sch.obj P.Z) n i) : Hs q (opn P.U) (n + 2 * d) (i + d) :=
  (AddEquiv.ofBijective _ ((t.ok q hq).2.2.1 (n + 2 * d) (i + d))).symm
    (Hs.act q (P := abv P.U t.π) ((AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).symm
      (pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x)) (Hs.pull q (abvMap P.U t.π) _ _ (fcl d q P)))

theorem purT_eq {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (x : Ht q (sch.obj P.Z) n i) : purT T q P n i x = purOf (T P) q hq n i x := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  unfold purT
  rw [dite_eq_left h]
  rfl

theorem purOf_char {d : ℕ} {P : SP d} (t : Tube P) (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(P.X, ⊤))) (n i : ℤ)
    (x : Ht q (sch.obj P.Z) n i) (y : Hs q (opn P.U) (n + 2 * d) (i + d)) (e : Ht q t.E n i)
    (he : pull _ (pullback.fst t.π (sch.map P.ι)) (tw q i) n e = pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x)
    (hy : Hs.pull q (abvMap P.U t.π) _ _ y = Hs.act q (P := abv P.U t.π) e (Hs.pull q (abvMap P.U t.π) _ _ (fcl d q P))) :
    purOf t q hq n i x = y := by
  have he' : (AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).symm
      (pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x) = e := by
    rw [AddEquiv.symm_apply_eq]; exact he.symm
  unfold purOf
  rw [he', AddEquiv.symm_apply_eq]
  exact hy.symm

theorem unit_of {d : ℕ} {P' P : SP d} (φ : P'.Hom P) (q : ℕ) (hq : IsUnit (q : Γ(P.X, ⊤))) :
    IsUnit (q : Γ(P'.X, ⊤)) := by
  have := hq.map φ.f.appTop.hom
  simpa using this

theorem purOf_nat (hN : DivisorNaturality) {d : ℕ} (hC : IsCl d (fcl d)) {P' P : SP d} (φ : P'.Hom P) (t : Tube P) (t' : Tube P')
    (b : t'.E ⟶ t.E) (hb : b ≫ t.π = t'.π ≫ sch.map φ.f) (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (x : Ht q (sch.obj P.Z) n i) :
    Hs.pull q (opnMap φ.f _ _ φ.le) _ _ (purOf t q hq n i x) =
      purOf t' q (unit_of φ q hq) n i (pull _ (sch.map φ.g) _ _ x) := by
  set_option synthInstance.maxHeartbeats 200000 in
    symm

    set e := (AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).symm (pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x)
      with he_def
    have he : pull _ (pullback.fst t.π (sch.map P.ι)) (tw q i) n e = pull _ (pullback.snd t.π (sch.map P.ι)) (tw q i) n x :=
      (AddEquiv.ofBijective _ ((t.ok q hq).1 i n)).apply_symm_apply _
    have hy : Hs.pull q (abvMap P.U t.π) _ _ (purOf t q hq n i x) =
        Hs.act q (P := abv P.U t.π) e (Hs.pull q (abvMap P.U t.π) _ _ (fcl d q P)) :=
      (AddEquiv.ofBijective _ ((t.ok q hq).2.2.1 (n + 2 * d) (i + d))).apply_symm_apply _

    have hw : (pullback.fst t'.π (sch.map P'.ι) ≫ b) ≫ t.π = (pullback.snd t'.π (sch.map P'.ι) ≫ sch.map φ.g) ≫ sch.map P.ι := by
      rw [Category.assoc, hb, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp, φ.cart.w]
    let c : pullback t'.π (sch.map P'.ι) ⟶ pullback t.π (sch.map P.ι) := pullback.lift _ _ hw

    have hw2 : (pullback.fst t'.π (sch.map P'.U.ι) ≫ b) ≫ t.π =
        (pullback.snd t'.π (sch.map P'.U.ι) ≫ sch.map (φ.f.resLE P.U P'.U φ.le)) ≫ sch.map P.U.ι := by
      rw [Category.assoc, hb, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp, Scheme.Hom.resLE_comp_ι]
    let ψ : abv P'.U t'.π ⟶ abv P.U t.π := Arrow.homMk (pullback.lift _ _ hw2) b (by simp only [abv, Arrow.mk_hom]; exact pullback.lift_fst _ _ _)
    have hsq : abvMap P'.U t'.π ≫ opnMap φ.f _ _ φ.le = ψ ≫ abvMap P.U t.π := by
      apply Arrow.hom_ext
      · simp only [Arrow.comp_left, abvMap, opnMap, ψ, Arrow.homMk_left]; exact (pullback.lift_snd _ _ _).symm
      · simp only [Arrow.comp_right, abvMap, opnMap, ψ, Arrow.homMk_right]; exact hb.symm
    apply purOf_char t' q _ n i _ _ (pull _ b _ _ e)
    · rw [← pull_comp, ← pull_comp, show pullback.fst t'.π (sch.map P'.ι) ≫ b = c ≫ pullback.fst t.π (sch.map P.ι) from (pullback.lift_fst _ _ hw).symm,
        show pullback.snd t'.π (sch.map P'.ι) ≫ sch.map φ.g = c ≫ pullback.snd t.π (sch.map P.ι) from (pullback.lift_snd _ _ hw).symm,
        pull_comp, pull_comp, he]
    · rw [pull_pull, hsq, ← pull_pull, hy]
      refine (act_pull hN q ψ (P := abv P.U t.π) e _).trans ?_
      congr 1
      rw [pull_pull, ← hsq, ← pull_pull, (hC q).2.1 P' P φ hq]

theorem dbl_map_of_right {P : Arrow Spc} (ψ : P ⟶ P) (h : ψ.right = 𝟙 _) : dbl.map ψ = 𝟙 _ := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext
    · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
      rw [inl_map, h, Category.id_comp, Category.comp_id]
    · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
      rw [dbl.inr_map, h, Category.id_comp, Category.comp_id]

theorem pull_of_right (q : ℕ) {P : Arrow Spc} (ψ : P ⟶ P) (h : ψ.right = 𝟙 _) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q ψ n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map ψ) _ n x.1 = x.1
  rw [dbl_map_of_right ψ h, pull_id]

def idHom {d : ℕ} (P : SP d) : P.Hom P where
  f := 𝟙 _
  g := 𝟙 _
  cart := by
    first
      | exact IsPullback.of_vert_isIso ⟨by simp⟩
      | exact IsPullback.of_horiz_isIso ⟨by simp⟩
  le := fun x hx => hx

end PurNatPf

open PurNatPf PurPf

theorem LeafPurNat_of : EtalePurityNaturality := by
  intro hH hCl d T hT q _ P hq P' φ n i x
  have hN : DivisorNaturality := hH.2.2.2.2.1
  have hC : IsCl d (fcl d) := pick_spec (hCl hH d)
  obtain ⟨T', a, b, ha, hb⟩ := hT P' P φ
  have hq' := unit_of φ q hq
  rw [purT_eq T q P hq, purT_eq T q P' hq', purOf_nat hN hC φ (T P) T' b hb q hq]
  have hb' : a ≫ (T P').π = T'.π ≫ sch.map (idHom P').f := by
    rw [ha]; change _ = T'.π ≫ sch.map (𝟙 _); rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have key := purOf_nat hN hC (idHom P') (T P') T' a hb' q hq' n i (pull _ (sch.map φ.g) _ _ x)
  rw [pull_of_right] at key
  · rw [key]
    change _ = purOf T' q _ n i (pull _ (sch.map (𝟙 _)) _ _ _)
    rw [CategoryTheory.Functor.map_id, pull_id]
  · change sch.map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
    rfl

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPurRedPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurRedPf

open PurPf

theorem inv_red (q r : ℕ) {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (hq : Function.Bijective (pull (ZMod q) f (tw q i) n)) (hr : Function.Bijective (pull (ZMod r) f (tw r i) n))
    (y : Ht q E n i) :
    (AddEquiv.ofBijective _ hr).symm (red q r E n i y) = red q r E' n i ((AddEquiv.ofBijective _ hq).symm y) := by
  apply hr.1
  rw [AddEquiv.ofBijective_apply_symm_apply]
  rw [GlobalTheory.EtC.pull_red]
  congr 1
  exact ((AddEquiv.ofBijective _ hq).apply_symm_apply y).symm

def redS (q r : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs r P n i :=
  ⟨red q r _ n i x.1, by
    change pull _ (dbl.inr P) (tw r i) n (red q r _ n i x.1) = 0
    have hx : pull _ (dbl.inr P) (tw q i) n x.1 = 0 := x.2
    rw [GlobalTheory.EtC.pull_red, hx, map_zero]⟩

theorem redS_coe (q r : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : (redS q r P n i x).1 = red q r _ n i x.1 := rfl

theorem Hs.pullS_red (q r : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull r φ n i (redS q r P n i x) = redS q r P' n i (Hs.pull q φ n i x) := by
  apply Subtype.ext
  change pull _ (dbl.map φ) (tw r i) n (red q r _ n i x.1) = red q r _ n i (pull _ (dbl.map φ) (tw q i) n x.1)
  rw [GlobalTheory.EtC.pull_red]

theorem Hs.inv_red (q r : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ)
    (hq : Function.Bijective (Hs.pull q φ n i)) (hr : Function.Bijective (Hs.pull r φ n i)) (y : Hs q P' n i) :
    (AddEquiv.ofBijective _ hr).symm (redS q r P' n i y) = redS q r P n i ((AddEquiv.ofBijective _ hq).symm y) := by
  apply hr.1
  rw [AddEquiv.ofBijective_apply_symm_apply, Hs.pullS_red]
  congr 1
  exact ((AddEquiv.ofBijective _ hq).apply_symm_apply y).symm

theorem Hs.act_red (hA : A11) (q r : ℕ) [NeZero q] (hrq : r ∣ q) {P : Arrow Spc} {n m i j : ℤ}
    (a : Ht q P.right n i) (b : Hs q P m j) :
    Hs.act r (red q r _ n i a) (redS q r P m j b) = redS q r P _ _ (Hs.act q a b) := by
  apply Subtype.ext
  have hc : cup r (pull _ (dbl.fold P) (tw r i) n (red q r _ n i a)) (red q r _ m j b.1) =
      red q r _ _ _ (cup q (pull _ (dbl.fold P) (tw q i) n a) b.1) := by
    rw [(hA q r hrq (dbl P)).1, GlobalTheory.EtC.pull_red]
  simp only [Hs.act, Hs.proj, redS_coe]
  rw [hc, map_sub, GlobalTheory.EtC.pull_red, GlobalTheory.EtC.pull_red]

theorem fcl_isCl (hH : Hyp) (hCl : LeafCl) (d : ℕ) : IsCl d (fcl d) := by
  unfold fcl
  exact pick_spec (hCl hH d)

theorem purT_eq {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (a : Ht q (sch.obj P.Z) n i) :
    purT T q P n i a = (AddEquiv.ofBijective _ (((T P).ok q hq).2.2.1 (n + 2 * d) (i + d))).symm
      (Hs.act q (P := abv P.U (T P).π) ((AddEquiv.ofBijective _ (((T P).ok q hq).1 i n)).symm
        (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n a))
        (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P))) := by
  unfold purT
  rw [dite_eq_left ⟨NeZero.ne q, hq⟩]
  rfl

theorem act_fcl (hH : Hyp) (hCl : LeafCl) {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d)
    (hq : IsUnit (q : Γ(P.X, ⊤))) (r : ℕ) (hrq : r ∣ q) (n i : ℤ) (x : Ht q (T P).E n i) :
    Hs.act r (P := abv P.U (T P).π) (red q r (T P).E n i x) (Hs.pull r (abvMap P.U (T P).π) _ _ (fcl d r P)) =
      redS q r _ _ _ (Hs.act q (P := abv P.U (T P).π) x (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P))) := by
  have hfr : fcl d r P = redS q r _ _ _ (fcl d q P) := Subtype.ext (((fcl_isCl hH hCl d) q).2.2 r hrq P hq)
  rw [hfr, Hs.pullS_red]
  exact Hs.act_red hH.2.2.2.2.2.2.2.1 q r hrq _ _

end PurRedPf

open PurPf PurRedPf

theorem LeafPurRed_of : EtalePurityReduction := by
  intro hH hCl d T q _ P hq r hrq n i a
  have hq0 : q ≠ 0 := NeZero.ne q
  have hr0 : r ≠ 0 := by rintro rfl; exact hq0 (zero_dvd_iff.mp hrq)
  have : NeZero r := ⟨hr0⟩
  have hru : IsUnit (r : Γ(P.X, ⊤)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hrq) hq
  rw [purT_eq T r P hru, purT_eq T q P hq, GlobalTheory.EtC.pull_red, inv_red q r _ n i (((T P).ok q hq).1 i n) (((T P).ok r hru).1 i n), act_fcl hH hCl T q P hq r hrq, Hs.inv_red q r _ _ _, redS_coe]

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPushPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut
namespace PushPf

variable {J' J : Type} [SmallCategory J'] [SmallCategory J] {D' : J' ⥤ PSh} {D : J ⥤ PSh} {G : J' ⥤ J}

def phi (α : D' ⟶ G ⋙ D) (U : Scheme.{0}ᵒᵖ) : (D'.flip.obj U).Elements ⥤ (D.flip.obj U).Elements where
  obj e := (D.flip.obj U).elementsMk (G.obj e.obj) ((α.app e.obj).app U e.val)
  map {e e'} g := Functor.Elements.homMk (G.map g.hom) (by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality g.hom) U) e.val
    exact h.symm.trans (congrArg (fun y => (α.app e'.obj).app U y) g.map_val))
  map_id e := Functor.Elements.hom_ext (G.map_id e.obj)
  map_comp g g' := Functor.Elements.hom_ext (G.map_comp g.hom g'.hom)

theorem elem_ext {X : Type} [Category X] {F : J ⥤ Type} (A B : X ⥤ F.Elements) (ho : ∀ x, A.obj x = B.obj x)
    (hm : A ⋙ Functor.Elements.π F = B ⋙ Functor.Elements.π F) : A = B := by
  refine CategoryTheory.Functor.ext ho (fun x y g => ?_)
  apply (Functor.Elements.π F).map_injective
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hm g

theorem phi_nat (α : D' ⟶ G ⋙ D) {U U' : Scheme.{0}ᵒᵖ} (f : U ⟶ U') :
    phi α U ⋙ (D.flip.map f).mapElements = (D'.flip.map f).mapElements ⋙ phi α U' :=
  elem_ext _ _ (fun e => by
    refine Functor.Elements.ext _ _ rfl ?_
    change (D.flip.obj U').map (𝟙 (G.obj e.obj))
        ((D.obj (G.obj e.obj)).map f ((α.app e.obj).app U e.val)) =
      (α.app e.obj).app U' ((D'.obj e.obj).map f e.val)
    rw [(D.flip.obj U').map_id]
    exact (ConcreteCategory.congr_hom ((α.app e.obj).naturality f) e.val).symm) rfl

def bmap (α : D' ⟶ G ⋙ D) : hoc D' ⟶ hoc D where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => (chn x ⋙ phi α U : Fin (n.unop.len + 1) ⥤ _)
      naturality := fun U U' f => by
        ext x
        change (chn x ⋙ (D'.flip.map f).mapElements) ⋙ phi α U' = (chn x ⋙ phi α U) ⋙ (D.flip.map f).mapElements
        rw [Functor.assoc, Functor.assoc, phi_nat] }
  naturality n m θ := by
    ext U x
    rfl

theorem goal (α : D' ⟶ G ⋙ D) {Y' Y : PSh} (f : Y' ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y') (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, α.app j ≫ c (G.obj j) = c' j ≫ f) : bmap α ≫ aug c hc = aug c' hc' ≫ disc.map f := by
  ext n U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h ((chn x).obj 0).obj) U) ((chn x).obj 0).val

end PushPf

theorem LeafPush_of : LeafPush := fun _ _ _ _ _ _ _ α _ _ f c' c hc' hc h => ⟨PushPf.bmap α, PushPf.goal α f c' c hc' hc h⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafQuotPf
section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem LeafQuot_of : LeafQuot := by
  intro A B _ _ φ I h
  obtain ⟨J, _, _, D, s, t, ⟨hc⟩, hj⟩ := h
  have hst : ∀ j (a : A), (t.app j).hom ((s.app j).hom a) = φ a := fun j a =>
    congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom a) (hj j).2
  have sn : ∀ {j k : J} (f : j ⟶ k), (D.map f).hom.comp (s.app j).hom = (s.app k).hom := by
    intro j k f
    have := s.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    rw [this]; rfl
  have tn : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), (t.app k).hom ((D.map f).hom y) = (t.app j).hom y := by
    intro j k f y
    have := t.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
    exact congrArg (fun g : D.obj j ⟶ CommRingCat.of B => g.hom y) this
  have mv : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), y ∈ I.map (s.app j).hom →
      (D.map f).hom y ∈ I.map (s.app k).hom := by
    intro j k f y hy
    have := Ideal.mem_map_of_mem (D.map f).hom hy
    rwa [Ideal.map_map, sn f] at this
  have rep : ∀ b : B, ∃ j, ∃ y : D.obj j, (t.app j).hom y = b := fun b =>
    Concrete.isColimit_exists_rep D hc b
  have mem : ∀ x ∈ I.map φ, ∃ j, ∃ y : D.obj j, y ∈ I.map (s.app j).hom ∧ (t.app j).hom y = x := by
    intro x hx
    obtain ⟨j0⟩ := IsFiltered.nonempty (C := J)
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, ha, rfl⟩ := h
      exact ⟨j0, (s.app j0).hom a, Ideal.mem_map_of_mem _ ha, hst j0 a⟩
    | zero => exact ⟨j0, 0, zero_mem _, map_zero _⟩
    | add x x' _ _ h h' =>
      obtain ⟨j, y, hy, rfl⟩ := h
      obtain ⟨k, y', hy', rfl⟩ := h'
      refine ⟨IsFiltered.max j k, (D.map (IsFiltered.leftToMax j k)).hom y + (D.map (IsFiltered.rightToMax j k)).hom y',
        add_mem (mv _ _ hy) (mv _ _ hy'), ?_⟩
      rw [map_add (f := _), tn, tn]
    | smul b x _ h =>
      obtain ⟨j, y, hy, rfl⟩ := h
      obtain ⟨k, c, rfl⟩ := rep b
      refine ⟨IsFiltered.max k j, (D.map (IsFiltered.leftToMax k j)).hom c * (D.map (IsFiltered.rightToMax k j)).hom y,
        Ideal.mul_mem_left _ _ (mv _ _ hy), ?_⟩
      rw [map_mul, tn, tn]; rfl
  constructor
  · intro u v huv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.eq] at huv
    rw [Ideal.Quotient.eq]
    rw [← map_sub] at huv
    obtain ⟨j, y, hy, hy'⟩ := mem _ huv
    rw [← hst j] at hy'
    obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc y ((s.app j).hom (a - a')) hy'
    have h1 : (s.app k).hom (a - a') ∈ I.map (s.app k).hom := by
      have e : (D.map g).hom ((s.app j).hom (a - a')) = (D.map f).hom y := hfg.symm
      have e2 : ((D.map g).hom.comp (s.app j).hom) (a - a') = (s.app k).hom (a - a') :=
        congrArg (fun r : A →+* D.obj k => r (a - a')) (sn g)
      rw [← e2]
      have := mv f y hy
      rw [← e] at this
      exact this
    have h2 := (hj k).1.2.1 (a₁ := Ideal.Quotient.mk I (a - a')) (a₂ := 0) (by
      rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]; exact h1)
    exact (Ideal.Quotient.eq_zero_iff_mem).1 h2
  · intro w
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨j, y, rfl⟩ := rep b
    obtain ⟨u, hu⟩ := (hj j).1.2.2 (Ideal.Quotient.mk _ y)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hu
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    have hc' : (t.app j).hom.comp (s.app j).hom = φ :=
      congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom) (hj j).2
    have := Ideal.mem_map_of_mem (t.app j).hom hu
    rw [Ideal.map_map, hc', map_sub, hst] at this
    exact this

end LateralTheory.CohomologicalPurity.TubeCut
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafRelHocPfX
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem pull_iso_bij (R : Type) [CommRing R] {E E' : Spc} (i : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R i.hom F n) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R i.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, i.inv_hom_id, pull_id]
  · rw [← pull_comp, i.hom_inv_id, pull_id]

theorem eqv_of_arrowIso (R : Type) [CommRing R] {E' E G' G : Spc} {f : E' ⟶ E} {g : G' ⟶ G} (F : Shv R)
    (e : Arrow.mk f ≅ Arrow.mk g) (hf : Eqv R f F) : Eqv R g F := by
  intro n
  have w : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
  have k : (pull R e.hom.left F n) ∘ (pull R g F n) = (pull R f F n) ∘ (pull R e.hom.right F n) := by
    funext x
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, w]
  have hl : Function.Bijective (pull R e.hom.left F n) :=
    pull_iso_bij R ((Arrow.leftFunc).mapIso e) F n
  have hr : Function.Bijective (pull R e.hom.right F n) :=
    pull_iso_bij R ((Arrow.rightFunc).mapIso e) F n
  have hc : Function.Bijective ((pull R e.hom.left F n) ∘ (pull R g F n)) := by
    rw [k]; exact (hf n).comp hr
  exact (Function.Bijective.of_comp_iff' hl _).mp hc

theorem eqv_sum_RRelH (hS : LeafSum) (R : Type) [CommRing R] (F : Shv R) {A : Type} {E' E : A → Spc} (c' : Cofan E') (c : Cofan E)
    (hc' : Nonempty (IsColimit c')) (hc : Nonempty (IsColimit c)) (f : ∀ a, E' a ⟶ E a) (φ : c'.pt ⟶ c.pt)
    (hφ : ∀ a, c'.inj a ≫ φ = f a ≫ c.inj a) (hf : ∀ a, Eqv R (f a) F) : Eqv R φ F := by
  intro n
  have k : (fun (y : H R c'.pt F n) (a : A) => pull R (c'.inj a) F n y) ∘ (pull R φ F n) =
      (fun (z : ∀ a, H R (E a) F n) (a : A) => pull R (f a) F n (z a)) ∘
        (fun (x : H R c.pt F n) (a : A) => pull R (c.inj a) F n x) := by
    funext x a
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, hφ]
  have h1 := hS R F A E' c' hc' n
  have h2 := hS R F A E c hc n
  have hc3 : Function.Bijective ((fun (y : H R c'.pt F n) (a : A) => pull R (c'.inj a) F n y) ∘ (pull R φ F n)) := by
    rw [k]
    exact (Function.Bijective.piMap (fun a => hf a n)).comp h2
  exact (Function.Bijective.of_comp_iff' h1 _).mp hc3

def LeafRelLev : Prop := LeafLevel → ∀ (J : Type) [SmallCategory J] (D' D : J ⥤ PSh) (α : D' ⟶ D)
  (Y G : PSh) (g : G ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j)) (h' : (hocF J).map α ≫ aug c hc = aug c' hc')
  (n : SimplexCategoryᵒᵖ),
  ∃ (A : Type) (ι : A → J) (E' E : A → Spc) (k' : Cofan E') (k : Cofan E) (f : ∀ a, E' a ⟶ E a) (φ : k'.pt ⟶ k.pt),
    Nonempty (IsColimit k') ∧ Nonempty (IsColimit k) ∧ (∀ a, k'.inj a ≫ φ = f a ≫ k.inj a) ∧
    (∀ a, Nonempty (Arrow.mk (pbRel (disc.map g) (disc.map (α.app (ι a))) (disc.map (c' (ι a))) (disc.map (c (ι a)))
      (h (ι a))) ≅ Arrow.mk (f a))) ∧
    Nonempty (Arrow.mk φ ≅ Arrow.mk (disc.map ((pbRel (disc.map g) ((hocF J).map α) (aug c' hc') (aug c hc) h').app n)))

theorem LeafRelHoc_of (hL : LeafLevel) (hS : LeafSum) (hB : LeafRelLev) : LeafRelHoc := by
  intro hA3 R _ F J _ D' D α Y G g c' c hc' hc h h' hE
  apply hA3
  intro n
  obtain ⟨A, ι, E', E, k', k, f, φ, h1, h2, h3, h4, ⟨e⟩⟩ := hB hL J D' D α Y G g c' c hc' hc h h' n
  refine eqv_of_arrowIso R F e ?_
  exact eqv_sum_RRelH hS R F k' k h1 h2 f φ h3 fun a => eqv_of_arrowIso R F (h4 a).some (hE (ι a))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

