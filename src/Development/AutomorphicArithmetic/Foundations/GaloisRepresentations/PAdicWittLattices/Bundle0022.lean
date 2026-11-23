module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsogFEt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isUnit_nat_of_rat {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}} (s : S ⟶ Sp R) {d : ℕ}
    (hd : 0 < d) : IsUnit (d : Γ(S, ⊤)) := by
  have hR : IsUnit (d : R) := by
    have hq : IsUnit (algebraMap ℚ R (d : ℚ)) :=
      (isUnit_iff_ne_zero.mpr (by exact_mod_cast hd.ne')).map _
    simpa using hq
  have h := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
  simpa using h

theorem UpperTheory.Gal.G3.pIsogFEt :
    IsogFEt := by
  intro R _ _ S s A A' _ _ _ _ hA hA' ψ ψ' d hd hψ hψ' h1 h2
  exact GlobalTheory.UPel.HT.ES.isFinite_etale_surjective_of_isQuasiInv S A A' d ψ ψ' hA hA'
    (isUnit_nat_of_rat s hd) ⟨hψ, hψ', h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPolDesc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

open GlobalTheory.CechPic GlobalTheory.BirigUniq in
theorem UpperTheory.Gal.G3.pPolDesc :
    PolDesc := by
  intro G₀ R _ _ gb S S' s s' c _ _ _ N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' hψ hcomm e h'
  obtain ⟨h'⟩ := h'
  haveI := hψ
  have hpb : IsPullback m₁.φ o₁'.A.hom o₁.A.hom c := m₁.cart.1
  let Y' : Over S := Over.mk (m₁.φ ≫ o₁.A.hom)
  let cO : Y' ⟶ o₁.A := Over.homMk m₁.φ rfl
  have hP1 : (Hecke.lbPow o₁.P e).IsLB := by
    unfold Hecke.lbPow
    exact LB.isLB_linComb o₁.isLB _ _
  have hP1' : (Hecke.lbPow o₁'.P e).IsLB := by
    unfold Hecke.lbPow
    exact LB.isLB_linComb o₁'.isLB _ _
  have hQ : (o₂.P.pull (Hecke.sq2 ψ)).IsLB := pull_isLB o₂.isLB _
  have hQ' : (o₂'.P.pull (Hecke.sq2 ψ')).IsLB := pull_isLB o₂'.isLB _
  refine ⟨(cls_eq_iff hP1 hQ).1 ?_⟩
  rw [← sub_eq_zero]
  have hfl : Flat m₁.φ := MorphismProperty.of_isPullback (P := @Flat) hpb.flip (inferInstance : Flat c)
  have hsu : Surjective m₁.φ :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb.flip (inferInstance : Surjective c)
  have hqc : QuasiCompact m₁.φ :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip (inferInstance : QuasiCompact c)
  refine pic_eq_zero_of_fpqc o₁.A o₁.A Y' o₁.ab cO hfl hsu hqc _ ?_ ?_
  · have key : (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left ≫ Hecke.sq2 ψ =
        ψ.left ≫ (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left := by
      unfold Hecke.sq2
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext
      · simp [one_comp_monHom]
      · simp
    rw [map_sub, GlobalTheory.BirigidPow.cls_lbPow o₁.isLB e hP1, map_nsmul,
      ← cls_pull o₁.isLB _ (pull_isLB o₁.isLB _), (cls_eq_zero_iff _).2 o₁.rig₁, smul_zero,
      cls_pull o₂.isLB _ hQ, ← pull_comp, key, pull_comp,
      ← cls_pull o₂.isLB _ (pull_isLB o₂.isLB _), (cls_eq_zero_iff _).2 o₂.rig₁, map_zero, sub_zero]
  · have hw : (fst o₁.A Y').left ≫ o₁.A.hom = ((snd o₁.A Y').left ≫ o₁'.A.hom) ≫ c := by
      have h1 := Over.w (fst o₁.A Y')
      have h2 := Over.w (snd o₁.A Y')
      rw [h1, ← h2, Category.assoc, ← hpb.w]
      rfl
    let u₀ : (o₁.A ⊗ Y').left ⟶ o₁'.A.left := hpb.lift (fst o₁.A Y').left ((snd o₁.A Y').left ≫ o₁'.A.hom) hw
    have hu₀ : u₀ ≫ o₁'.A.hom = (snd o₁.A Y').left ≫ o₁'.A.hom := hpb.lift_snd _ _ _
    let g : (o₁.A ⊗ Y').left ⟶ Limits.pullback o₁'.A.hom o₁'.A.hom :=
      Limits.pullback.lift u₀ (snd o₁.A Y').left hu₀
    have K1 : (lift (fst o₁.A Y') (snd o₁.A Y' ≫ cO)).left = g ≫ m₁.φ₂ := by
      apply Limits.pullback.hom_ext (f := o₁.A.hom) (g := o₁.A.hom)
      · change _ ≫ (fst o₁.A o₁.A).left = (g ≫ m₁.φ₂) ≫ (fst o₁.A o₁.A).left
        rw [← Over.comp_left, lift_fst, Category.assoc, m₁.sq.1, ← Category.assoc]
        change _ = (g ≫ Limits.pullback.fst _ _) ≫ m₁.φ
        rw [Limits.pullback.lift_fst]
        exact (hpb.lift_fst _ _ _).symm
      · change _ ≫ (snd o₁.A o₁.A).left = (g ≫ m₁.φ₂) ≫ (snd o₁.A o₁.A).left
        rw [← Over.comp_left, lift_snd, Category.assoc, m₁.sq.2, ← Category.assoc]
        change _ = (g ≫ Limits.pullback.snd _ _) ≫ m₁.φ
        rw [Limits.pullback.lift_snd, Over.comp_left]
        rfl
    have K2 : m₁.φ₂ ≫ Hecke.sq2 ψ = Hecke.sq2 ψ' ≫ m₂.φ₂ := by
      unfold Hecke.sq2
      apply Limits.pullback.hom_ext (f := o₂.A.hom) (g := o₂.A.hom)
      · change (_ ≫ _) ≫ (fst o₂.A o₂.A).left = (_ ≫ _) ≫ (fst o₂.A o₂.A).left
        rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_fst, m₂.sq.1, Over.comp_left,
          ← Category.assoc, m₁.sq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left,
          Category.assoc, Category.assoc, hcomm]
      · change (_ ≫ _) ≫ (snd o₂.A o₂.A).left = (_ ≫ _) ≫ (snd o₂.A o₂.A).left
        rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_snd, m₂.sq.2, Over.comp_left,
          ← Category.assoc, m₁.sq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left,
          Category.assoc, Category.assoc, hcomm]
    have pol1 : cls o₁'.P o₁'.isLB = cls (o₁.P.pull m₁.φ₂) (pull_isLB o₁.isLB _) :=
      (cls_eq_iff _ _).2 m₁.pol
    have pol2 : cls o₂'.P o₂'.isLB = cls (o₂.P.pull m₂.φ₂) (pull_isLB o₂.isLB _) :=
      (cls_eq_iff _ _).2 m₂.pol
    have E1 : (pull (lift (fst o₁.A Y') (snd o₁.A Y' ≫ cO)).left) (cls _ hP1) =
        (pull g) (cls _ hP1') := by
      rw [K1, pull_comp, GlobalTheory.BirigidPow.cls_lbPow o₁.isLB e hP1, map_nsmul,
        ← cls_pull o₁.isLB _ (pull_isLB o₁.isLB _), ← pol1, ← GlobalTheory.BirigidPow.cls_lbPow o₁'.isLB e hP1']
    have E2 : (pull (lift (fst o₁.A Y') (snd o₁.A Y' ≫ cO)).left) (cls _ hQ) =
        (pull g) (cls _ hQ') := by
      rw [K1, cls_pull o₂.isLB _ hQ, ← pull_comp, Category.assoc, K2, ← Category.assoc, pull_comp,
        pull_comp, ← cls_pull o₂.isLB _ (pull_isLB o₂.isLB _), ← pol2, cls_pull o₂'.isLB _ hQ']
    rw [map_sub, E1, E2, (cls_eq_iff hP1' hQ').2 h', sub_self]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPolUniq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u


open GlobalTheory.CechPic GlobalTheory.BirigUniq in
theorem UpperTheory.Gal.G3.pPolUniq :
    PolUniq := by
  intro S A A' _ _ _ _ hA hA' ψ hm hfin het hsurj P Q hP hQ h1 h2 h3 h4 hiso
  have hfl : Flat (Over.Hom.left ψ) := inferInstance
  have hqc : QuasiCompact (Over.Hom.left ψ) := inferInstance
  have hcls : ∀ {Y : Scheme} (F : Y ⟶ (G2 A').left),
      pull F (cls P hP - cls Q hQ) = cls (P.pull F) (pull_isLB hP F) - cls (Q.pull F) (pull_isLB hQ F) := by
    intro Y F
    rw [map_sub]
    rfl
  have hzero : ∀ {Y : Scheme} (F : Y ⟶ (G2 A').left), LBIso (P.pull F) (Q.pull F) →
      pull F (cls P hP - cls Q hQ) = 0 := by
    intro Y F h
    rw [hcls, sub_eq_zero]
    exact (cls_eq_iff _ _).mpr h
  set d := cls P hP - cls Q hQ with hd
  have hs1 : pull (Over.Hom.left (lift (1 : A' ⟶ A') (𝟙 A'))) d = 0 := by
    rw [hcls, sub_eq_zero, (cls_eq_zero_iff _).mpr h1, (cls_eq_zero_iff _).mpr h3]
  have hs2 : pull (Over.Hom.left (lift (𝟙 A') (1 : A' ⟶ A'))) d = 0 := by
    rw [hcls, sub_eq_zero, (cls_eq_zero_iff _).mpr h2, (cls_eq_zero_iff _).mpr h4]
  have hsq : pull (Hecke.sq2 ψ) d = 0 := hzero _ hiso
  let E : A' ⊗ A ⟶ A' ⊗ A' := lift (fst A' A) (snd A' A ≫ ψ)
  let W : A ⊗ A' ⟶ A' ⊗ A := lift (snd A A') (fst A A')
  let W' : A' ⊗ A ⟶ A ⊗ A' := lift (snd A' A) (fst A' A)
  have hf : pull (Over.Hom.left (W ≫ E)) d = 0 := by
    refine pic_eq_zero_of_fpqc A A' A hA ψ hfl hsurj hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : A' ⟶ A) (𝟙 A') ≫ W ≫ E = lift (𝟙 A') (1 : A' ⟶ A') := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [E, W, one_comp_monHom]
      rw [this, hs2]
    · rw [← pull_comp_left]
      have : lift (fst A A) (snd A A ≫ ψ) ≫ W ≫ E
          = lift (snd A A) (fst A A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [E, W]
      rw [this, pull_comp_left]
      have h' : pull (Over.Hom.left (lift (fst A A ≫ ψ) (snd A A ≫ ψ))) d = 0 := hsq
      rw [h', map_zero]
  have he : pull (Over.Hom.left E) d = 0 := by
    have : W' ≫ W ≫ E = E := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [E, W, W']
    rw [← this, pull_comp_left, hf, map_zero]
  have hd0 : d = 0 := pic_eq_zero_of_fpqc A' A' A hA' ψ hfl hsurj hqc d hs1 he
  rw [hd, sub_eq_zero] at hd0
  exact (cls_eq_iff hP hQ).mp hd0
end

