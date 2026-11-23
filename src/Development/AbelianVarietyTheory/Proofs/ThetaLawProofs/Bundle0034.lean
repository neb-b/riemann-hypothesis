module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisBaseChangeRelativeBasisPulledBackSections
section
noncomputable section

namespace GlobalTheory.RelBasisFibre

section General

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (pw isLB_pw)
open GlobalTheory.RelBasis GlobalTheory.KeyBasis

variable {X Y : Scheme.{0}} {L : LB X} {M : LB Y} {C : Type} [CommRing C] {n N : ℕ}
  {φ : Y ⟶ X} {w : LB.Iso M (L.pull φ)}

theorem comb_eq (p : Y ⟶ Sp C) {b : Fin N → LB.Sec (pw L (n : ℤ))} {b' : Fin N → ∀ i, Γ(Y, M.U i)}
    (hb : ∀ k, KeyVia.Via w n (b' k) (b k).f) (a : Fin N → C) (y : Y) {j : L.ι} {i : M.ι}
    (hj : φ y ∈ L.U j) (hi : y ∈ M.U i) :
    comb b p φ ⊤ (fun k => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (a k)) y j =
      (gw w (𝟙 Y) y j i ^ n).val * gs (𝟙 Y) y (M.U i) (∑ k, AbLaw.cst p (M.U i) (a k) * b' k i) := by
  rw [gs_comb p (M.U i) (𝟙 Y) y hi, Finset.mul_sum, comb]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := via_val (hb k) (𝟙 Y) y (j := j) (i := i) hj hi
  rw [Category.id_comp] at e
  rw [mul_left_comm, ← e, Category.id_comp]
  rfl

theorem exists_down (hL : L.IsLB) (hM : M.IsLB) (hw : w.IsGen) (V : Y.Opens) (hV : ∀ y, y ∈ V)
    (σ : ∀ j : L.ι, Γ(Y, V ⊓ φ ⁻¹ᵁ L.U j))
    (hσ : ∀ (y : Y) (j j' : L.ι), φ y ∈ L.U j → φ y ∈ L.U j' →
      gs (𝟙 Y) y _ (σ j) = (gm φ y (L.U j ⊓ L.U j') (L.g j j') ^ (n : ℤ)).val * gs (𝟙 Y) y _ (σ j')) :
    ∃ s : LB.Sec (pw M (n : ℤ)), ∀ (y : Y) (j : L.ι) (i : M.ι), φ y ∈ L.U j → y ∈ M.U i →
      gs (𝟙 Y) y _ (σ j) = (gw w (𝟙 Y) y j i ^ n).val * gs (𝟙 Y) y (M.U i) (s.f i) := by
  have le : ∀ j : (L.pull φ).ι, (L.pull φ).U j ≤ V ⊓ φ ⁻¹ᵁ L.U (j PUnit.unit) :=
    fun j y hy => ⟨hV y, KeyVia.chart_le j hy⟩
  let t : LB.Sec (pw (L.pull φ) (n : ℤ)) := ⟨fun j => resG Y (le j) (σ (j PUnit.unit)), fun j j' => fn_ext fun y hy => by
    refine ((gs_res (𝟙 Y) y _ hy _).trans (gs_res (𝟙 Y) y (le j) hy.1 _)).trans
      ((hσ y _ _ (le j hy.1).2 (le j' hy.2).2).trans (Eq.trans ?_ (gs_mul (𝟙 Y) y _ hy _ _).symm))
    refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 Y) y _ hy _).trans (gs_res (𝟙 Y) y (le j') hy.2 _)).symm
    refine Eq.trans ?_ ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (map_zpow _ _ _))).symm
    refine congrArg (fun u : (Y.presheaf.stalk y)ˣ => (u ^ (n : ℤ)).val) ?_
    have e := gm_pull_g L φ (𝟙 Y) y j j' hy.1 hy.2
    rw [Category.id_comp] at e
    exact e.symm⟩
  have hu := KeyVia.pwIso_isGen hw (n : ℤ)
  have hA := isLB_pw hM (n : ℤ)
  have hB := isLB_pw (DVR.linComb_isLB L hL (fun _ : PUnit => φ) (fun _ => 1)) (n : ℤ)
  refine ⟨DVR.secOfIso t hu hA hB, fun y j i hj hi => ?_⟩
  have hj' : y ∈ (L.pull φ).U (fun _ => j) := mem_pull.2 hj
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U i ⊓ (L.pull φ).U (fun _ => j) := ⟨hi, hj'⟩
  have e : gs (𝟙 Y) y (M.U i) ((DVR.secOfIso t hu hA hB).f i) =
      ((gw w (𝟙 Y) y j i ^ n)⁻¹).val * gs (𝟙 Y) y _ (σ j) := by
    refine (gs_res (𝟙 Y) y inf_le_left hm _).symm.trans ((congrArg (gs (𝟙 Y) y _)
      (DVR.secOfIso_spec t hu hA hB i (fun _ => j))).trans ((gs_mul (𝟙 Y) y _ hm _ _).trans
        (congrArg₂ (· * ·) ?_ ((gs_res (𝟙 Y) y _ hm _).trans (gs_res (𝟙 Y) y (le _) hj' _)))))
    refine (gs_unit (𝟙 Y) y _ hm _).trans (congrArg Units.val ((map_inv _ _).trans ?_))
    exact congrArg (·⁻¹) ((gm_res (𝟙 Y) y _ hm _).trans ((map_zpow _ _ _).trans (zpow_natCast _ _)))
  rw [e, Units.mul_inv_cancel_left]

end General

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (l N : ℕ) (b : Fin N → RR x l) (b' : Fin N → RR x' l), KeyVia x' x f φ w → (∀ k, SecVia x' x φ w (b' k) (b k)) → IsBasis x' b' → GlobalTheory.RelBasis.IndepOn b x'.P.A.hom φ ⊤ ∧ GlobalTheory.RelBasis.SpanOn b x'.P.A.hom φ ⊤ := by
  rintro R R' _ _ x x' f φ w l N b b' ⟨he, hg, F, -, hw, -⟩ hb hB
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv
  have hb' : ∀ k, KeyVia.Via w l (b' k).f (b k).f := hb
  constructor
  · intro c hc
    choose a ha using fun k => bij.2 (c k)
    obtain rfl : (fun k => (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (a k)) = c := funext ha
    let z : RR x' l := ⟨fun _ => 0, fun _ _ => (map_zero _).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm⟩
    have h₁ : Coords x' b' a z.f := fun i => fn_ext fun y hy => by
      obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ y)
      have e := (comb_eq x'.P.A.hom hb' a y hj hy).symm.trans (hc y j trivial hj)
      rw [Units.mul_right_eq_zero] at e
      refine Eq.trans ?_ e.symm
      exact (GlobalTheory.RelBasis.gs_eq_gsHom _ y _ hy _).trans (map_zero _)
    have h₂ : Coords x' b' 0 z.f := fun i =>
      (Finset.sum_eq_zero fun k _ => by rw [Pi.zero_apply, map_zero, zero_mul]).symm
    obtain rfl : a = 0 := (hB z).unique h₁ h₂
    exact funext fun k => map_zero _
  · intro σ hσ
    obtain ⟨s, hs⟩ := exists_down x.P.isLB x'.P.isLB hw (x'.P.A.hom ⁻¹ᵁ ⊤) (fun _ => trivial) σ
      (fun y j j' hj hj' => hσ y j j' trivial hj hj')
    obtain ⟨a, ha, -⟩ := hB s
    refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (a k), fun y j _ hj => ?_⟩
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB y
    exact (hs y j i hj hi).trans ((congrArg _ (GlobalTheory.KeyBasis.gs_congr _ y (ha i))).trans
      (comb_eq x'.P.A.hom hb' a y hj hi).symm)

end GlobalTheory.RelBasisFibre

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsGenSimilitudePull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.SimilPull

section Algebra

variable {A U : Type} [AddCommGroup A] [AddCommGroup U] {q : A → U} {B : A →+ A →+ U}

theorem quad_zsmul (h0 : q 0 = 0) (hq : ∀ x y, q (x + y) = q x + q y + B x y) (h2 : ∀ x, B x x = q x + q x)
    (n : ℤ) (x : A) : q (n • x) = (n * n) • q x := by
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ n ih =>
    rw [add_smul, one_smul, hq, ih, map_zsmul, AddMonoidHom.zsmul_apply, h2]
    module
  | pred n ih =>
    have e := hq ((-(n : ℤ) - 1) • x) x
    rw [show (-(n : ℤ) - 1) • x + x = (-(n : ℤ)) • x by module, ih, map_zsmul, AddMonoidHom.zsmul_apply, h2] at e
    have e' : q ((-(n : ℤ) - 1) • x) = (-(n : ℤ) * -(n : ℤ)) • q x - q x - (-(n : ℤ) - 1) • (q x + q x) := by
      rw [e]; abel
    rw [e']
    module

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]

theorem sum_quad_rows (h0 : q 0 = 0) (hq : ∀ x y, q (x + y) = q x + q y + B x y) (h2 : ∀ x, B x x = q x + q x)
    (al : I → J → ℤ) (m : ℤ) (hal : ∀ c c', ∑ r, al r c * al r c' = if c = c' then m else 0) (y : J → A)
    (s : Finset J) : ∑ r, q (∑ c ∈ s, al r c • y c) = m • ∑ c ∈ s, q (y c) := by
  induction s using Finset.induction_on with
  | empty => simp [h0]
  | insert d s hd ih =>
    simp only [Finset.sum_insert hd, hq, Finset.sum_add_distrib, ih, quad_zsmul h0 hq h2, smul_add]
    have e₁ : ∑ r, (al r d * al r d) • q (y d) = m • q (y d) := by
      rw [← Finset.sum_smul, hal, if_pos rfl]
    have e₂ : ∑ r, B (al r d • y d) (∑ c ∈ s, al r c • y c) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul, AddMonoidHom.zsmul_apply, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [← Finset.sum_smul, hal, if_neg (fun e : c = d => hd (e ▸ hc)), zero_smul]
    rw [e₁, e₂, add_zero]

theorem sum_quad_rows_add (h0 : q 0 = 0) (hq : ∀ x y, q (x + y) = q x + q y + B x y)
    (h2 : ∀ x, B x x = q x + q x)
    (al : I → J → ℤ) (m : ℤ) (hal : ∀ c c', ∑ r, al r c * al r c' = if c = c' then m else 0) (y : J → A)
    (ξ : I → A) (hξ : ∀ r, q (ξ r) = 0) (hk : ∀ c, ∑ r, al r c • ξ r = 0) :
    ∑ r, q (∑ c, al r c • y c + ξ r) = m • ∑ c, q (y c) := by
  simp only [hq, hξ, add_zero, Finset.sum_add_distrib, sum_quad_rows h0 hq h2 al m hal y]
  have e : ∑ r, B (∑ c, al r c • y c) (ξ r) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_zsmul, ← map_sum, hk, map_zero]
  rw [e, add_zero]

end Algebra

section Mul

open GlobalTheory.PrimNorm

variable {A U : Type} [CommGroup A] [CommGroup U] {q : A → U} {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]

theorem prod_quad_rows_mul (hc : ∀ x y z, diff₃ q x y z = 1) (h0 : q 1 = 1) (h2 : ∀ x, q (x ^ 2) = q x ^ 4)
    (al : I → J → ℤ) (m : ℤ) (hal : ∀ c c', ∑ r, al r c * al r c' = if c = c' then m else 0) (y : J → A)
    (ξ : I → A) (hξ : ∀ r, q (ξ r) = 1) (hk : ∀ c, ∏ r, ξ r ^ al r c = 1) :
    ∏ r, q ((∏ c, y c ^ al r c) * ξ r) = (∏ c, q (y c)) ^ m := by
  let B : Additive A →+ Additive A →+ Additive U := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun z => Additive.ofMul (diff₂ q x.toMul z.toMul))
      (fun z z' => congrArg Additive.ofMul (diff₂_mul_right hc _ _ _)))
    (fun x x' => AddMonoidHom.ext fun z => congrArg Additive.ofMul (diff₂_mul_left hc _ _ _))
  have hB : ∀ x z, B x z = Additive.ofMul (diff₂ q x.toMul z.toMul) := fun _ _ => rfl
  have key := sum_quad_rows_add (q := fun x : Additive A => Additive.ofMul (q x.toMul)) (B := B)
    (congrArg Additive.ofMul h0) (fun x z => by
      simp only [hB, diff₂, h0, toMul_add, ofMul_mul, ofMul_inv, ofMul_one]
      abel) (fun x => by
      simp only [hB, diff₂, h0, ← sq, h2, ofMul_mul, ofMul_inv, ofMul_one, ofMul_pow]
      abel) al m hal (fun c => Additive.ofMul (y c)) (fun r => Additive.ofMul (ξ r))
    (fun r => congrArg Additive.ofMul (hξ r)) (fun c => by
      simpa only [ofMul_prod, ofMul_zpow, ofMul_one] using congrArg Additive.ofMul (hk c))
  apply Additive.ofMul.injective
  simpa only [ofMul_prod, ofMul_zpow, toMul_add, toMul_sum, toMul_zsmul, toMul_ofMul] using key

end Mul

open GlobalTheory.PrimNorm GlobalTheory.MulPull

theorem exists_gen_similitude_pull : Out.Laws → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x), al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ c, (List.ofFn fun r : Fin 4 => ξ r ^ al r c).prod = 1) → ∃ w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w.IsGen := by
  intro laws R _ _ _ x m al ξ hal hk
  have hL := x.P.isLB
  let T := Out.powObj x.P.A 4
  obtain ⟨⟨cub⟩, -⟩ := laws.cube _ x.P ⟨x.P.L, x.rig, hL, x.rig_gen⟩ rfl
  have hconst : ∀ z : Pt x, ptCls x.P.L T (toUnit T ≫ z) = 1 := fun z => by
    have h : HasGen x.P.L (K := PUnit) (fun _ => z.left) (fun _ => 1) :=
      DVR.exists_gen_of_local (V := R) x.P.L hL (K := PUnit) (fun _ => z.left) (fun _ => 1)
    have e := (hasGen_iff hL _ _).1 (h.pull (toUnit T).left)
    rw [Fintype.prod_unique, zpow_one] at e
    exact e
  have h2 : ∀ y : T ⟶ x.P.A, ptCls x.P.L T (y ^ 2) = ptCls x.P.L T y ^ 4 := fun y => by
    have h : HasGen x.P.L (K := Fin 2) ![𝟙 x.P.A.left, (Out.mulA x.P.A 2).left] ![((2 : ℕ) : ℤ) ^ 2, -1] :=
      laws.mulPull _ x.P 2
    have e := (hasGen_iff hL _ _).1 (h.pull y.left)
    have e₂ : y ≫ Out.mulA x.P.A 2 = y ^ 2 := by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
      ← Over.comp_left, e₂, zpow_neg, zpow_one, mul_inv_eq_one] at e
    refine e.symm.trans ?_
    norm_num
  have key := prod_quad_rows_mul (q := ptCls x.P.L T) (diff₃_ptCls hL ⟨cub.t, cub.isGen⟩)
    (by simpa only [MonObj.comp_one] using hconst 1) h2 (fun r c => al r c) (m : ℤ)
    (fun c c' => by
      have := congrFun (congrFun hal c) c'
      simpa [Matrix.mul_apply, Matrix.one_apply] using this)
    (fun c => Out.powPr x.P.A c) (fun r => toUnit T ≫ ξ r) (fun r => hconst _) (fun c => by
      have e := congrArg (fun z : Pt x => toUnit T ≫ z) (hk c)
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow,
        MonObj.comp_one] at e
      simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero] using e)
  refine (hasGen_iff hL _ _).2 ?_
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_one, zpow_neg, Finset.prod_inv_distrib,
    mul_inv_eq_one, Finset.prod_zpow]
  refine Eq.trans (Finset.prod_congr rfl fun r _ => ?_) key
  rw [alMap, List.prod_ofFn]

end GlobalTheory.SimilPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RelAmplePowObjBoxLB
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relAmple_powObj_boxLB : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (j : ℕ), Out.RelAmple (Out.powObj P.A j) (Out.boxLB P.L (Out.powPr P.A (n := j))) :=
  fun _ _ P j => relAmple_boxLB _ _ _ j (Out.powIsPowGrp P.A j) P.L P.isLB P.ample

end GlobalTheory
end

