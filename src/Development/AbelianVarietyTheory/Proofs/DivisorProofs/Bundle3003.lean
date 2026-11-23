module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFactorOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalAbelianSchemeTorsionRationalFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.XFTorsion

open GlobalTheory.FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem zeta_pow (l : Geo.Tor.Level H) : zeta l.M' ^ (l.M' / l.A) = zeta l.A := by
  obtain ⟨m, hm⟩ := A_dvd_M' l
  have hM := M'_pos l
  have hm0 : (m : ℂ) ≠ 0 := by
    rintro h
    rw [Nat.cast_eq_zero] at h
    subst h
    omega
  have hA : (l.A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 l.A_pos.ne'
  rw [hm, Nat.mul_div_cancel_left _ l.A_pos, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem torsion_fixed {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    (β : B →+* k) (hx : x ≫ s = spMap β) (z : kˣ) (hz : IsPrimitiveRoot z l.M')
    (hzA : (z : k) ^ (l.M' / l.A) = β b.ζ) (σ : k ≃+* k) (hσ : spMap (σ : k →+* k) ≫ x = x) (hσz : σ z = z)
    (w : Over.mk x ⟶ o.t.G) (hw : w ^ l.M' = 1) : spMap (σ : k →+* k) ≫ w.left = w.left := by
  obtain ⟨ev, ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩, hu⟩ := exists_unique_fullLevel o k x β hx z hz hzA
  have hid : spMap (RingHom.id k) = 𝟙 (Sp k) := Spec.map_id _
  have e1 : spMap (σ.symm : k →+* k) ≫ spMap (σ : k →+* k) = 𝟙 _ := by
    rw [spMap_comp, ← hid]; congr 1; ext a; simp
  have e2 : spMap (σ : k →+* k) ≫ spMap (σ.symm : k →+* k) = 𝟙 _ := by
    rw [spMap_comp, ← hid]; congr 1; ext a; simp
  have hσ' : spMap (σ.symm : k →+* k) ≫ x = x := by
    conv_lhs => rw [← hσ, ← Category.assoc, e1, Category.id_comp]
  let g : (Over.mk x : Over S) ⟶ Over.mk x := Over.homMk (spMap (σ : k →+* k)) hσ
  let g' : (Over.mk x : Over S) ⟶ Over.mk x := Over.homMk (spMap (σ.symm : k →+* k)) hσ'
  have gg' : g ≫ g' = 𝟙 _ := Over.OverMorphism.ext e2
  have g'g : g' ≫ g = 𝟙 _ := Over.OverMorphism.ext e1
  have key : (fun a => g ≫ ev a) = ev := by
    refine (hu _ ⟨⟨fun a c => ?_, fun c a => ?_, fun a => ?_, fun u => ?_, fun a c => ?_⟩, fun a => ?_, fun a ha => ?_⟩).trans
      (hu ev ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩).symm
    · show g ≫ ev (a + c) = (g ≫ ev a) * (g ≫ ev c)
      rw [h1, MonObj.comp_mul]
    · show g ≫ ev (c • a) = (g ≫ ev a) ≫ o.t.act.act c
      rw [h2, Category.assoc]
    · show g ≫ ev a = 1 ↔ _
      rw [← h3]
      refine ⟨fun h => ?_, fun h => by rw [h, MonObj.comp_one]⟩
      rw [← Category.id_comp (ev a), ← g'g, Category.assoc, h, MonObj.comp_one]
    · refine ⟨fun h => ?_, ?_⟩
      · obtain ⟨a, ha⟩ := (h4 (g' ≫ u)).1 (by rw [← MonObj.comp_pow, h, MonObj.comp_one])
        refine ⟨a, ?_⟩
        show g ≫ ev a = u
        rw [ha, ← Category.assoc, gg', Category.id_comp]
      · rintro ⟨a, rfl⟩
        show (g ≫ ev a) ^ l.M' = 1
        rw [← MonObj.comp_pow, (h4 _).2 ⟨a, rfl⟩, MonObj.comp_one]
    · have h₁ := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.SemiRigid.globalFns (GlobalTheory.ObjDim.isAbelianScheme o) o.t.PP.isLB g
        (h5 a c)
      have e' : Units.map g.left.appTop.hom.toMonoidHom (unitOn (z ^ D.EF a c)) =
          unitOn (Units.map (σ : k →+* k).toMonoidHom (z ^ D.EF a c)) :=
        Units.ext (congrArg (fun q => q.hom (z ^ D.EF a c).val)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : k →+* k)))).symm
      have e'' : Units.map (σ : k →+* k).toMonoidHom (z ^ D.EF a c) = z ^ D.EF a c := by
        rw [map_zpow]
        congr 1
        exact Units.ext hσz
      rw [e''] at e'
      exact (congrArg (WeilIs o.t.G o.t.PP.L (l.M' : ℕ) (g ≫ ev a) (g ≫ ev c)) e').mp h₁
    · show (g ≫ ev a) ^ (l.M' / l.A) = toUnit _ ≫ o.etaA a
      rw [← MonObj.comp_pow, h6, comp_toUnit_assoc]
    · show (g ≫ ev a) ^ (l.M' / l.M) = toUnit _ ≫ o.eta a
      rw [← MonObj.comp_pow, h7 a ha, comp_toUnit_assoc]
  obtain ⟨a, rfl⟩ := (h4 w).1 hw
  exact congrArg CommaMorphism.left (congrFun key a)

theorem torsion_rational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (K K' : Type) [Field K] [Field K'] [IsAlgClosed K'] (κ : K →+* K') (y : Sp K ⟶ Xo.XF c) (x : Over.mk (spMap κ ≫ y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G), x ^ l.M' = 1 → ∃ x₀ : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G, x₀ ^ l.M' = 1 ∧ x.left = spMap κ ≫ x₀.left := by
  intro E _ _ _ H Dw l Xo c _ K K' _ _ _ κ y x hx
  obtain ⟨bF, hbF⟩ : ∃ bF : c.F →+* K, y ≫ pullback.snd _ _ = spMap bF :=
    ⟨(Spec.preimage (y ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩
  haveI : CharZero K := RingHom.charZero_iff bF.injective |>.1 inferInstance
  letI : Algebra K K' := κ.toAlgebra
  let inc := (IntermediateField.inclusion c.le).toRingHom
  have hs : (spMap κ ≫ y ≫ pullback.fst _ _) ≫ Xo.s = spMap (κ.comp (bF.comp inc)) := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc y, hbF, spMap_comp, spMap_comp]
  let z₀ : c.F := ⟨zeta l.M', c.zeta_mem⟩
  have hz₀ : IsPrimitiveRoot z₀ l.M' := IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom)
    (Complex.isPrimitiveRoot_exp l.M' (M'_pos l).ne') Subtype.val_injective
  have hz₁ : IsPrimitiveRoot (κ (bF z₀)) l.M' := (hz₀.map_of_injective bF.injective).map_of_injective κ.injective
  let z : K'ˣ := (hz₁.isUnit (M'_pos l).ne').unit
  have hz : IsPrimitiveRoot z l.M' := IsPrimitiveRoot.coe_units_iff.1 hz₁
  have hzA : (z : K') ^ (l.M' / l.A) = (κ.comp (bF.comp inc)) (baseKA l).ζ := by
    show κ (bF z₀) ^ _ = κ (bF (inc _))
    rw [← map_pow, ← map_pow]
    congr 2
    exact Subtype.ext (zeta_pow l)
  obtain ⟨p, hp, -⟩ := GlobalTheory.FixedPoint.existsUnique_factor_of_isAlgClosed (K₀ := K) (L := K') x.left fun σ =>
    torsion_fixed Xo.univ K' _ _ hs z hz hzA σ.toRingEquiv (by
      rw [← Category.assoc, spMap_comp]
      congr 2
      ext a
      exact σ.commutes a) (σ.commutes (bF z₀)) x hx
  haveI : Epi (spMap κ) := GlobalTheory.FixedPoint.epi_specAlg (K₀ := K) (K₁ := K')
  have hp' : spMap κ ≫ p = x.left := hp
  have hpo : p ≫ Xo.univ.t.G.hom = y ≫ pullback.fst _ _ := by
    rw [← cancel_epi (spMap κ), ← Category.assoc, hp']
    exact Over.w x
  let x₀ : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G := Over.homMk p hpo
  let g : (Over.mk (spMap κ ≫ y ≫ pullback.fst _ _) : Over Xo.X) ⟶ Over.mk (y ≫ pullback.fst _ _) :=
    Over.homMk (spMap κ) rfl
  have hg : g ≫ x₀ = x := Over.OverMorphism.ext hp'
  refine ⟨x₀, Over.OverMorphism.ext ?_, hp'.symm⟩
  have h : g ≫ x₀ ^ l.M' = g ≫ 1 := by rw [MonObj.comp_pow, hg, hx, MonObj.comp_one]
  exact (cancel_epi (spMap κ)).1 (congrArg CommaMorphism.left h)

end GlobalTheory.XFTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelFirstCoordEquations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section
open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinKerA

variable {S : Scheme.{0}}

theorem mkZ_pa' {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S}
    (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) : mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa, lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb' {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S}
    (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) : mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb, lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem pull_zCls {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (w w' : Y ⟶ Zob A B) :
    CechPic.pull (lift w w').left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (w ≫ pa A B i) (w' ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (w ≫ pa A B i) (w' ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (w' ≫ pa A B i) (w ≫ pb A B j)) +
      ∑ j, evc hQ (w' ≫ pb A B j ≫ mu) (w ≫ pb A B j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zCls, map_add (f := _), map_sum, map_zsmul, evc, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc]

theorem zarhinBundle_kernel : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i ≫ la) * ∏ j, (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx i
  have hP := c.isLB
  have hQ : Q.IsLB := hZ.2.1.isLB
  have hQd : IsDual c.A B Q := hZ.2.1
  have hQd' : IsDual B c.A (swap Q) := hZ.2.2.1
  have hs : (swap Q).IsLB := hQd'.isLB
  haveI : IsMonHom mu := hZ.2.2.2.2.1

  have h0 : CechPic.pull (lift (snd (Zob c.A B) T ≫ x) (fst (Zob c.A B) T)).left
      (zCls c.A B c.isLB hQ d mu) = 0 := by
    rw [← cls_zP c.A B c.isLB hQ d mu, ← cls_pull (zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _
      (pull_isLB (zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _)]
    exact (cls_eq_zero_iff _).2 hx

  let inc : c.A ⟶ Zob c.A B := mkZ c.A B (fun k => if k = i then 𝟙 c.A else 1) (fun _ => 1)
  have h1 := congrArg (CechPic.pull (lift (fst c.A T ≫ inc) (snd c.A T)).left) h0
  rw [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst, pull_zCls] at h1
  have hpa : ∀ k, (fst c.A T ≫ inc) ≫ pa c.A B k = if k = i then fst c.A T else 1 := by
    intro k
    rw [Category.assoc, mkZ_pa']
    split_ifs <;> simp [MonObj.comp_one]
  have hpb : ∀ j, (fst c.A T ≫ inc) ≫ pb c.A B j = 1 := by
    intro j
    rw [Category.assoc, mkZ_pb', MonObj.comp_one]
  have z1 : ∀ {Y : Over S} (a : Y ⟶ c.A), evc hP a (1 : Y ⟶ c.A) = 0 := fun a => evc_one_right hP c.rig₂ a
  have z2 : ∀ {Y : Over S} (a : Y ⟶ c.A), evc hQ a (1 : Y ⟶ B) = 0 := fun a => evc_one_right hQ hQd.zero a
  have z3 : ∀ {Y : Over S} (b : Y ⟶ B), evc hQ (1 : Y ⟶ c.A) b = 0 := fun b => hQd.additive.evc_one hQ b
  have s1 : (∑ k, evc hP ((snd c.A T ≫ x) ≫ pa c.A B k) ((fst c.A T ≫ inc) ≫ pa c.A B k)) =
      evc hP ((snd c.A T ≫ x) ≫ pa c.A B i) (fst c.A T) := by
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [hpa, if_neg hk, z1]) (fun hi => absurd (Finset.mem_univ i) hi),
      hpa, if_pos rfl]
  have s2 : (∑ k, ∑ j, quat d j k • evc hQ ((snd c.A T ≫ x) ≫ pa c.A B k) ((fst c.A T ≫ inc) ≫ pb c.A B j)) = 0 := by
    simp only [hpb, z2, smul_zero, Finset.sum_const_zero]
  have s3 : (∑ k, ∑ j, quat d j k • evc hQ ((fst c.A T ≫ inc) ≫ pa c.A B k) ((snd c.A T ≫ x) ≫ pb c.A B j)) =
      ∑ j, quat d j i • evc hQ (fst c.A T) ((snd c.A T ≫ x) ≫ pb c.A B j) := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp only [hpa, if_neg hk, z3, smul_zero, Finset.sum_const_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [hpa, if_pos rfl]
  have s4 : (∑ j, evc hQ ((fst c.A T ≫ inc) ≫ pb c.A B j ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j)) = 0 := by
    simp only [← Category.assoc _ (pb c.A B _) mu, hpb, MonObj.one_comp, z3, Finset.sum_const_zero]
  rw [s1, s2, s3, s4, add_zero, add_zero] at h1

  have eS : cls c.P hP = evc hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
  have eL : cls c.P hP = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
    (cls_eq_iff hP (pull_isLB hQ _)).2 hZ.2.2.2.2.2.2.2
  have ePQ : ∀ {Y : Over S} (u a : Y ⟶ c.A), evc hP u a = evc hQ a (u ≫ la) := by
    intro Y u a
    have e1 := congrArg (CechPic.pull (lift u a).left) eS
    have e2 := congrArg (CechPic.pull (lift a u).left) eL
    rw [pull_evc, lift_snd, lift_fst] at e1
    rw [pull_evc, lift_fst, lift_snd_assoc] at e2
    exact e1.trans e2

  have hadd : ∀ {Y : Over S} (a : Y ⟶ c.A) (b b' : Y ⟶ B), evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
    intro Y a b b'
    rw [← evc_swap hQ hs, ← evc_swap hQ hs, ← evc_swap hQ hs]
    exact (isAdditive_iff hs).1 hQd'.additive Y b b' a
  let φ : (T ⟶ B) →* Multiplicative (Pic (c.A ⊗ T).left) :=
    MonoidHom.mk' (fun b => Multiplicative.ofAdd (evc hQ (fst c.A T) (snd c.A T ≫ b))) fun b b' => by
      simp only [MonObj.comp_mul, hadd, ofAdd_add]
  refine (hQd.isPerfect hQd').ker_right T _ ((triv_ev_iff hQ _ _).2 ?_)
  have key : Multiplicative.toAdd (φ ((x ≫ pa c.A B i ≫ la) * ∏ j, (x ≫ pb c.A B j) ^ quat d j i)) =
      evc hQ (fst c.A T) (snd c.A T ≫ ((x ≫ pa c.A B i ≫ la) * ∏ j, (x ≫ pb c.A B j) ^ quat d j i)) := rfl
  rw [← key, map_mul, map_prod, toAdd_mul, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, φ, MonoidHom.mk'_apply, toAdd_ofAdd]
  rw [← Category.assoc, ← Category.assoc, ← ePQ]
  simpa only [Category.assoc] using h1

end GlobalTheory.ZarhinKerA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelSecondCoordEquations
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

section RadialKernelIntegrals

variable {S : Scheme.{0}}

def precompHom {Y Y' G : Over S} [GrpObj G] (f : Y' ⟶ Y) : (Y ⟶ G) →* (Y' ⟶ G) :=
  MonoidHom.mk' (fun a => f ≫ a) (fun a b => MonObj.comp_mul f a b)

def postcompHom {Y G H : Over S} [GrpObj G] [GrpObj H] (g : G ⟶ H) [IsMonHom g] : (Y ⟶ G) →* (Y ⟶ H) :=
  MonoidHom.mk' (fun a => a ≫ g) (fun a b => MonObj.mul_comp a b g)

def evcHom {A T Y : Over S} [GrpObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB) (h : IsAdditive M) (t : Y ⟶ T) :
    (Y ⟶ A) →* Multiplicative (Pic Y.left) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hM a t)) (fun a b => by
    rw [(isAdditive_iff hM).1 h Y a b t]; rfl)

theorem evc_prod_zpow_left {A T Y : Over S} [GrpObj A] [IsCommMonObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (h : IsAdditive M) {K : Type} [Fintype K] (a : K → (Y ⟶ A)) (n : K → ℤ) (t : Y ⟶ T) :
    evc hM (∏ k, a k ^ n k) t = ∑ k, n k • evc hM (a k) t := by
  have e := map_prod (evcHom hM h t) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact congrArg Multiplicative.toAdd e

theorem evc_pow_left {A T Y : Over S} [GrpObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (h : IsAdditive M) (a : Y ⟶ A) (n : ℕ) (t : Y ⟶ T) : evc hM (a ^ n) t = n • evc hM a t :=
  congrArg Multiplicative.toAdd (map_pow (evcHom hM h t) a n)

theorem evc_mul_right {A B Y : Over S} [GrpObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) (a : Y ⟶ A) (b b' : Y ⟶ B) : evc hM a (b * b') = evc hM a b + evc hM a b' := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', ← evc_swap hM hs', ← evc_swap hM hs']
  exact (isAdditive_iff hs').1 hs Y b b' a

theorem evc_prod_zpow_right {A B Y : Over S} [GrpObj B] [IsCommMonObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) {K : Type} [Fintype K] (a : Y ⟶ A) (b : K → (Y ⟶ B)) (n : K → ℤ) :
    evc hM a (∏ k, b k ^ n k) = ∑ k, n k • evc hM a (b k) := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', evc_prod_zpow_left hs' hs]
  exact Finset.sum_congr rfl fun k _ => by rw [evc_swap hM hs']

theorem evc_pow_right {A B Y : Over S} [GrpObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) : evc hM a (b ^ n) = n • evc hM a b := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', evc_pow_left hs' hs, evc_swap hM hs']

theorem comp_prod_zpow'' {Y Y' G : Over S} [GrpObj G] [IsCommMonObj G] {K : Type} [Fintype K] (f : Y' ⟶ Y)
    (a : K → (Y ⟶ G)) (n : K → ℤ) : f ≫ ∏ k, a k ^ n k = ∏ k, (f ≫ a k) ^ n k := by
  have e := map_prod (precompHom f) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact e

theorem prod_zpow_comp'' {Y G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj G] [IsCommMonObj H] {K : Type}
    [Fintype K] (a : K → (Y ⟶ G)) (n : K → ℤ) (g : G ⟶ H) [IsMonHom g] :
    (∏ k, a k ^ n k) ≫ g = ∏ k, (a k ≫ g) ^ n k := by
  have e := map_prod (postcompHom (Y := Y) g) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact e

end RadialKernelIntegrals

end GlobalTheory.ZarhinKerB

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

section KerAux2

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa' {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  rw [pa, ← Category.assoc, mkZ, lift_fst]
  exact (Out.powIsLimit A 4).fac _ ⟨i⟩

theorem mkZ_pb' {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  rw [pb, ← Category.assoc, mkZ, lift_snd]
  exact (Out.powIsLimit B 4).fac _ ⟨j⟩

theorem pull_zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (p q : Y ⟶ Zob A B) :
    CechPic.pull (lift p q).left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (p ≫ pa A B i) (q ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (p ≫ pa A B i) (q ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (q ≫ pa A B i) (p ≫ pb A B j)) +
      ∑ j, evc hQ (q ≫ pb A B j ≫ mu) (p ≫ pb A B j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zCls, map_add (f := _), map_sum, map_zsmul, evc, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc]

end KerAux2

end GlobalTheory.ZarhinKerB

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zarhinBundle_kernel : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ j, ((∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i) ≫ la) * (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ d = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx j
  have hQ : IsDual c.A B Q := hZ.2.1
  have hQ' : IsDual B c.A (swap Q) := hZ.2.2.1
  haveI hla : IsMonHom la := hZ.2.2.2.1
  haveI hmu : IsMonHom mu := hZ.2.2.2.2.1
  have hlm : la ≫ mu = 𝟙 c.A ^ d := hZ.2.2.2.2.2.1
  have hPQ := hZ.2.2.2.2.2.2.2
  have hzP := zarhinBundle_isLineBundle c.A B c.isLB hQ.isLB d mu
  have h0 : ∀ (Y : Over S) (s : Y ⟶ T) (z : Y ⟶ Zob c.A B),
      CechPic.pull (lift (s ≫ x) z).left (zCls c.A B c.isLB hQ.isLB d mu) = 0 := by
    intro Y s z
    have e := congrArg (CechPic.pull (lift z s).left) ((cls_eq_zero_iff (pull_isLB hzP _)).2 hx)
    rw [cls_pull hzP, cls_zP, map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst] at e
    exact e

  have e := h0 (c.A ⊗ T) (snd c.A T)
    (mkZ c.A B (fun _ => 1) (fun j' => if j' = j then fst c.A T ≫ la else 1))
  rw [pull_zCls] at e
  simp only [mkZ_pa', mkZ_pb'] at e
  simp only [← Category.assoc, mkZ_pa', mkZ_pb'] at e
  have t2 : ∀ i, ∑ j', quat d j' i • evc hQ.isLB ((snd c.A T ≫ x) ≫ pa c.A B i)
      (if j' = j then fst c.A T ≫ la else 1) = quat d j i • evc hQ.isLB ((snd c.A T ≫ x) ≫ pa c.A B i) (fst c.A T ≫ la) :=
    fun i => by
      rw [Fintype.sum_eq_single j (fun j' hj' => by rw [if_neg hj', evc_one_right hQ.isLB hQ.zero, smul_zero]),
        if_pos rfl]
  have t4 : ∑ j', evc hQ.isLB ((if j' = j then fst c.A T ≫ la else 1) ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j') =
      evc hQ.isLB ((fst c.A T ≫ la) ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j) := by
    rw [Fintype.sum_eq_single j (fun j' hj' => by rw [if_neg hj', MonObj.one_comp, hQ.additive.evc_one hQ.isLB]),
      if_pos rfl]
  simp only [t2, t4, evc_one_right c.isLB c.rig₂, hQ.additive.evc_one hQ.isLB, smul_zero, Finset.sum_const_zero,
    zero_add, add_zero] at e
  have hPev : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc c.isLB p q = evc hQ.isLB p (q ≫ la) := by
    intro Y p q
    have e1 : cls c.P c.isLB = evc hQ.isLB (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ.isLB _)).2 hPQ
    rw [evc, e1, pull_evc, lift_fst, lift_snd_assoc]
  have hPsymm : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc c.isLB p q = evc c.isLB q p := by
    intro Y p q
    have e1 : cls c.P c.isLB = evc c.isLB (snd c.A c.A) (fst c.A c.A) :=
      (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
    rw [evc, e1, pull_evc, lift_fst, lift_snd]
  have hQsw : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc hQ.isLB p (q ≫ la) = evc hQ.isLB q (p ≫ la) := by
    intro Y p q
    rw [← hPev, ← hPev, hPsymm]
  refine (hQ.isPerfect hQ').ker_right T _ ((triv_ev_iff hQ.isLB _ _).2 ?_)
  rw [MonObj.comp_mul, ← Category.assoc, comp_prod_zpow'', prod_zpow_comp'', MonObj.comp_pow,
    evc_mul_right hQ.isLB hQ'.additive, evc_prod_zpow_right hQ.isLB hQ'.additive, evc_pow_right hQ.isLB hQ'.additive]
  rw [Category.assoc, hlm, MonObj.comp_pow, Category.comp_id, evc_pow_left hQ.isLB hQ.additive] at e
  rw [← e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hQsw, Category.assoc]

end GlobalTheory.ZarhinKerB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinKernelLinearAlgebraTrivial
section
open Matrix

namespace GlobalTheory.ZarhinFam

theorem zpow_finset_sum' {G ι : Type} [CommGroup G] (a : G) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ k ∈ s, e k) = ∏ k ∈ s, a ^ e k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, _root_.zpow_add, ih]

theorem prod_prod_zpow_mul {G : Type} [CommGroup G] (P Q : Matrix (Fin 4) (Fin 4) ℤ) (w : Fin 4 → G)
    (a : Fin 4) : ∏ k, (∏ i, w i ^ Q k i) ^ P a k = ∏ i, w i ^ (P * Q) a i := by
  simp_rw [← Finset.prod_zpow, ← _root_.zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, zpow_finset_sum']
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem prod_zpow_smul_one {G : Type} [CommGroup G] (c : ℤ) (w : Fin 4 → G) (a : Fin 4) :
    ∏ i, w i ^ (c • (1 : Matrix (Fin 4) (Fin 4) ℤ)) a i = w a ^ c := by
  simp [Matrix.smul_apply, Matrix.one_apply]

theorem zarhin_kernel_trivial : ∀ (d : ℕ) (GA GB : Type) [CommGroup GA] [CommGroup GB] (f : GA →* GB) (g : GB →* GA), 0 < d → (∀ a, g (f a) = a ^ d) → ∀ (u : Fin 4 → GA) (v : Fin 4 → GB), (∀ i, f (u i) * ∏ j, v j ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ j, f (∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i) * v j ^ d = 1) → ((∀ j, v j = 1) → ∀ j, ∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ i, u i = 1) ∧ ∀ j, v j = 1 := by
  intro d GA GB _ _ f g hd hgf u v hA hB hC
  have hxx : quat d * (quat d)ᵀ = (((d - 1 : ℕ) : ℤ)) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
    quat_mul_transpose d
  have hxtx : (quat d)ᵀ * quat d = (((d - 1 : ℕ) : ℤ)) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
    quat_transpose_mul d
  have hd1 : d = (d - 1) + 1 := by omega
  have hv : ∀ k, v k = 1 := by
    intro k
    have E : ∏ i, (f (u i) * ∏ j, v j ^ quat d j i) ^ quat d k i = 1 := by
      simp [hA]
    rw [Finset.prod_congr rfl fun i _ => mul_zpow (f (u i)) (∏ j, v j ^ quat d j i) (quat d k i),
      Finset.prod_mul_distrib] at E
    have E2 : ∏ i, (∏ j, v j ^ (quat d)ᵀ i j) ^ quat d k i = v k ^ (((d - 1 : ℕ) : ℤ)) := by
      rw [prod_prod_zpow_mul, hxx, prod_zpow_smul_one]
    simp only [Matrix.transpose_apply] at E2
    have hF : f (∏ i, u i ^ quat d k i) = ∏ i, f (u i) ^ quat d k i := by
      simp [map_prod, map_zpow]
    rw [E2, ← hF, zpow_natCast] at E
    have hBk := hB k
    rw [show v k ^ d = v k ^ (d - 1) * v k by rw [← pow_succ, ← hd1], ← mul_assoc, E, one_mul] at hBk
    exact hBk
  refine ⟨?_, hv⟩
  have hxu := hC hv
  intro l
  have E : ∏ k, (∏ i, u i ^ quat d k i) ^ (quat d)ᵀ l k = 1 := by
    simp [hxu]
  rw [prod_prod_zpow_mul, hxtx, prod_zpow_smul_one, zpow_natCast] at E
  have hfu : f (u l) = 1 := by
    have h := hA l
    simpa [hv] using h
  have hdu : u l ^ d = 1 := by
    rw [← hgf, hfu, map_one]
  rw [show u l ^ d = u l ^ (d - 1) * u l by rw [← pow_succ, ← hd1], E, one_mul] at hdu
  exact hdu

end GlobalTheory.ZarhinFam
end

