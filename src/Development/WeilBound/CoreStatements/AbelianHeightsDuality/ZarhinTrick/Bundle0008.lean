module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0005
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleB
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]


set_option maxHeartbeats 400000 in
theorem relAmple_lPart (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (mu : B ⟶ A) [IsMonHom mu]
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (ha : Out.RelAmple ((Over.pullback s).obj A) L) (hmu : IsFinite ((Over.pullback s).map mu).left) :
    Out.RelAmple ((Over.pullback s).obj (G4 (A ⊗ B))) (lPart mu s L) := by
  have hGA : IsAbelianScheme ((Over.pullback s).obj A) := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  haveI : IsProper ((Over.pullback s).obj A).hom := hGA.proper
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hAB : IsAbelianScheme (A ⊗ B) := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have h4A : IsAbelianScheme (G4 (A ⊗ A)) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAA
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAA (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAA hAA))
  have h4B : IsAbelianScheme (G4 (A ⊗ B)) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB hAB))
  have hY : IsAbelianScheme ((Over.pullback s).obj (G4 (A ⊗ A))) := GlobalTheory.isAbelianScheme_pullback_obj s _ h4A
  have hG : IsAbelianScheme ((Over.pullback s).obj (G4 (A ⊗ B))) := GlobalTheory.isAbelianScheme_pullback_obj s _ h4B
  haveI : IsProper ((Over.pullback s).obj (G4 (A ⊗ A))).hom := hY.proper
  haveI : IsProper ((Over.pullback s).obj (G4 (A ⊗ B))).hom := hG.proper
  have hL' : (L.LinComb ![𝟙 _, Over.Hom.left (𝟙 ((Over.pullback s).obj A))⁻¹] ![1, 1]).IsLB :=
    LB.isLB_linComb hL _ _
  have ha' := XB.relAmple_sym hL ha
  haveI hpr : ∀ j, IsMonHom (XB.pr8 A j) := by
    intro j
    fin_cases j <;> simp only [XB.pr8] <;> infer_instance
  let p : Out.IsPowGrp ((Over.pullback s).obj (G4 (A ⊗ A))) ((Over.pullback s).obj A) 8 :=
    { pr := fun j => (Over.pullback s).map (XB.pr8 A j)
      hom := fun j => inferInstance
      lim := (isLimitMapConeFanMkEquiv (Over.pullback s) _ _).1 (isLimitOfPreserves _ (XB.lim8 A)) }
  have hbox := GlobalTheory.relAmple_boxLB _ _ _ 8 p _ hL' ha'
  have hboxLB : (Out.boxLB (L.LinComb ![𝟙 _, Over.Hom.left (𝟙 ((Over.pullback s).obj A))⁻¹] ![1, 1])
      p.pr).IsLB := LB.isLB_linComb hL' _ _
  have hid : IsFinite ((Over.pullback s).map (𝟙 A)).left := by
    have e1 : (Over.pullback s).map (𝟙 A) = 𝟙 _ := (Over.pullback s).map_id A
    rw [e1, Over.id_left]
    infer_instance
  have hΦ : IsFinite ((Over.pullback s).map (XB.fourfoldProductMap (𝟙 A ⊗ₘ mu))).left :=
    XB.isFinite_map_g4map s _ (XB.isFinite_map_tensorHom s _ _ hid hmu)
  haveI := hΦ
  have h2 := GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom ((Over.pullback s).map (XB.fourfoldProductMap (𝟙 A ⊗ₘ mu)))
    hboxLB hbox
  have hlpLB : (lPart mu s L).IsLB := LB.isLB_linComb hL _ _
  have hq : ∀ i : Fin 4, XB.fourfoldProductMap (𝟙 A ⊗ₘ mu) ≫ prj (A ⊗ A) i = prj (A ⊗ B) i ≫ (𝟙 A ⊗ₘ mu) := by
    intro i
    fin_cases i <;> simp [XB.fourfoldProductMap, prj]
  have hinv : ∀ {X : Over (Sp Ω)} (f : X ⟶ (Over.pullback s).obj A),
      (pull (Over.Hom.left f⁻¹)) (cls L hL) =
        (pull (Over.Hom.left f)) ((pull (Over.Hom.left (𝟙 ((Over.pullback s).obj A))⁻¹)) (cls L hL)) := by
    intro X f
    rw [← pull_comp, ← Over.comp_left, GrpObj.comp_inv, Category.comp_id]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hlpLB (LB.isLB_pull hboxLB _) le_rfl ?_ h2
  rw [one_smul, cls_pull hboxLB, GlobalTheory.PosDefAmple.pull_cls_boxLB p.pr hL']
  simp only [lPart]
  simp only [cls_linComb hL, Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_eight, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, map_add, Over.id_left, pull_id]
  simp only [p, ← Functor.map_comp, XB.pr8]
  simp only [← Category.assoc, hq]
  simp only [Category.assoc, tensorHom_fst, tensorHom_snd, Category.comp_id, phiL]
  simp only [hinv (pA s 0), hinv (pA s 1), hinv (pA s 2), hinv (pA s 3), hinv (pM mu s 0), hinv (pM mu s 1),
    hinv (pM mu s 2), hinv (pM mu s 3)]
  simp only [pA, pM]
  abel

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamD
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]


omit [GrpObj A] [GrpObj B] in
theorem pull_zcPair {P : LB (A ⊗ B).left} (hP : P.IsLB) (lm : A ⟶ B) (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ)
    {Y Z : Over S} (w : Z ⟶ Y) (u u' : Y ⟶ G4 (A ⊗ B)) :
    pull w.left (zcPair hP lm mu α u u') = zcPair hP lm mu α (w ≫ u) (w ≫ u') := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zcPair, map_add (f := _), map_sum, map_nsmul, map_zsmul, pull_evc, Category.assoc]

section Pieces

variable {P : LB (A ⊗ B).left} (hD : IsDual A B P) (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l]
  (mu : B ⟶ A) [IsMonHom mu] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left)
  (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
  {T : Over (Sp Ω)} (u u' : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B)))

include e in
theorem line_bundle_pairing_zeroth (i : Fin 4) :
    lam (pull (phiL mu s (0, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ fst A B) (toBase _ s u' ≫ prj _ i ≫ fst A B ≫ l) := by
  have hm := map_mul_pt s (prj (A ⊗ B) i ≫ fst A B) u u'
  have h1 := map_one_pt s (prj (A ⊗ B) i ≫ fst A B) (T := T)
  show lam (pull (pA s i).left (cls L hL)) u u' = _
  rw [lam_pull_pt (pA s i) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e]
  simp only [pA, toBase_map, Category.assoc]

include e hD' in
theorem line_bundle_pairing_first [IsCommMonObj A] (i : Fin 4) :
    lam (pull (phiL mu s (1, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ fst A B) (toBase _ s u' ≫ prj _ i ≫ fst A B ≫ l) := by
  have hm0 := map_mul_pt s (prj (A ⊗ B) i ≫ fst A B) u u'
  have hm : (u * u') ≫ (pA (B := B) s i)⁻¹ = u ≫ (pA s i)⁻¹ * u' ≫ (pA s i)⁻¹ := by
    rw [GrpObj.comp_inv, GrpObj.comp_inv, GrpObj.comp_inv]
    show ((u * u') ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ fst A B))⁻¹ = _
    rw [hm0, mul_inv]
    rfl
  have h1 : (1 : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) ≫ (pA (B := B) s i)⁻¹ = 1 := by
    rw [GrpObj.comp_inv]
    show ((1 : T ⟶ _) ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ fst A B))⁻¹ = 1
    rw [map_one_pt, inv_one]
  show lam (pull ((pA (B := B) s i)⁻¹).left (cls L hL)) u u' = _
  rw [lam_pull_pt ((pA s i)⁻¹) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e,
    GrpObj.comp_inv, GrpObj.comp_inv, toBase_inv, toBase_inv, GrpObj.inv_comp]
  simp only [pA, toBase_map, Category.assoc]
  exact evc_inv_inv hD hD' _ _

include e in
theorem line_bundle_pairing_second (i : Fin 4) :
    lam (pull (phiL mu s (2, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ snd A B ≫ mu) (toBase _ s u' ≫ prj _ i ≫ snd A B ≫ mu ≫ l) := by
  have hm := map_mul_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) u u'
  have h1 := map_one_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) (T := T)
  show lam (pull (pM mu s i).left (cls L hL)) u u' = _
  rw [lam_pull_pt (pM mu s i) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e]
  simp only [pM, toBase_map, Category.assoc]

include e hD' in
theorem line_bundle_pairing_third [IsCommMonObj A] (i : Fin 4) :
    lam (pull (phiL mu s (3, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ snd A B ≫ mu) (toBase _ s u' ≫ prj _ i ≫ snd A B ≫ mu ≫ l) := by
  have hm0 := map_mul_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) u u'
  have hm : (u * u') ≫ (pM mu s i)⁻¹ = u ≫ (pM mu s i)⁻¹ * u' ≫ (pM mu s i)⁻¹ := by
    rw [GrpObj.comp_inv, GrpObj.comp_inv, GrpObj.comp_inv]
    show ((u * u') ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ snd A B ≫ mu))⁻¹ = _
    rw [hm0, mul_inv]
    rfl
  have h1 : (1 : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) ≫ (pM mu s i)⁻¹ = 1 := by
    rw [GrpObj.comp_inv]
    show ((1 : T ⟶ _) ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ snd A B ≫ mu))⁻¹ = 1
    rw [map_one_pt, inv_one]
  show lam (pull ((pM mu s i)⁻¹).left (cls L hL)) u u' = _
  rw [lam_pull_pt ((pM mu s i)⁻¹) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e,
    GrpObj.comp_inv, GrpObj.comp_inv, toBase_inv, toBase_inv, GrpObj.inv_comp]
  simp only [pM, toBase_map, Category.assoc]
  exact evc_inv_inv hD hD' _ _

include hD hD' in
theorem evc_lam_key {Y : Over S} (a a' : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hD.isLB (a * a') (b * b') - evc hD.isLB a b - evc hD.isLB a' b' + evc hD.isLB (1 : Y ⟶ A) (1 : Y ⟶ B) =
      evc hD.isLB a b' + evc hD.isLB a' b := by
  rw [evc_mul_left hD, evc_mul_right hD hD', evc_mul_right hD hD',
    IsAdditive.evc_one hD.isLB hD.additive]
  abel

private theorem pull_pull_phiP_eq_evc (ij : Fin 4 × Fin 4) (v : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) :
    pull v.left (pull (phiP s ij) (cls P hD.isLB)) =
      evc hD.isLB (toBase _ s v ≫ prj _ ij.1 ≫ fst A B) (toBase _ s v ≫ prj _ ij.2 ≫ snd A B) := by
  have hv := toBase_comp s (G4 (A ⊗ B)) v (𝟙 _)
  rw [Category.comp_id] at hv
  rw [evc, ← pull_comp, hv]
  congr 2
  simp only [phiP, ← comp_lift, Over.comp_left]
  rfl

include hD' in
theorem lam_phiP (ij : Fin 4 × Fin 4) :
    lam (pull (phiP s ij) (cls P hD.isLB)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ ij.1 ≫ fst A B) (toBase _ s u' ≫ prj _ ij.2 ≫ snd A B) +
        evc hD.isLB (toBase _ s u' ≫ prj _ ij.1 ≫ fst A B) (toBase _ s u ≫ prj _ ij.2 ≫ snd A B) := by
  simp only [GlobalTheory.CechPic.lam, pull_pull_phiP_eq_evc hD, toBase_mul, toBase_one, MonObj.mul_comp, MonObj.one_comp]
  exact evc_lam_key hD hD' _ _ _ _

end Pieces

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KerMemKL
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

theorem ker_memKL {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (l : A ⟶ B) [IsMonHom l] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) [IsCommMonObj ((Over.pullback s).obj A)]
    (L : LB ((Over.pullback s).obj A).left)
    (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {T : Over (Sp Ω)} (x : T ⟶ (Over.pullback s).obj A) (hx : x ≫ (Over.pullback s).map l = 1) :
    GlobalTheory.MemKL ((Over.pullback s).obj A) L x := by
  have hx0 : lam (cls L hL) (fst T ((Over.pullback s).obj A) ≫ x) (snd T ((Over.pullback s).obj A)) = 0 := by
    rw [lam_comm, lam_cL_pt s hD.isLB l L hL e, ← toBase_map, Category.assoc, hx, MonObj.comp_one, toBase_one]
    exact evc_one_right hD.isLB hD.zero _
  have hD' : (Out.translDiff ((Over.pullback s).obj A) L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD' (fst T _) (snd T _)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD' = GlobalTheory.CechPic.pull (fst T ((Over.pullback s).obj A)).left
      (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx0, lam]
    abel
  rw [cls_pull hD', e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T _).left ⁻¹ᵁ V).ι ≫ (fst T _).left) (fun z ↦ z.2) hc

end PositivityTheory.PrwZar.Z2
end
end

