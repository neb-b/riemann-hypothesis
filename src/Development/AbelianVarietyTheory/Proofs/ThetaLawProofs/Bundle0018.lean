module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem dualNumber_ringHom_ext {R S : Type} [CommRing R] [CommRing S] {F G : DualNumber R →+* S}
    (h : ∀ a, F (algebraMap R _ a) = G (algebraMap R _ a)) (he : F DualNumber.eps = G DualNumber.eps) : F = G := by
  refine RingHom.ext fun z => ?_
  have e : z = algebraMap R _ z.fst + algebraMap R _ z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, map_add (f := _), map_add (f := _), map_mul, map_mul, h, h, he]

section Sec

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem appLE_eq_iff_stalk (w : LB.Iso L' (L.pull F)) (s : L.Sec) (s' : L'.Sec) :
    (∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ L.U (j PUnit.unit)),
      (F.appLE _ _ hle).hom (s.f (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i)) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun y hy => mem_pull.1 hy.1
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy]
    exact congrArg (· * _) (gs_unit _ z _ hy _)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit _ y _ hy _).symm

end Sec

theorem keyPB_cancel : ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (x : KeyIn R) (x' : KeyIn R')
    (x'' : KeyIn R'') (f : R →+* R') (f' : R' →+* R''), KeyPB x' x f → KeyPB x'' x (f'.comp f) → KeyPB x'' x' f' := by
  intro R R' R'' _ _ _ x x' x'' f f' ⟨φ, he, w, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩
    ⟨φ'', he'', w'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x''.P.A.left ⟶ x'.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x'.P.A.hom = x''.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x''.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x''.P.A ≫ φ' = spMap f' ≫ eSec x'.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x''.P.A ≫ x''.P.A.hom = 𝟙 _ := Over.w η[x''.P.A]
      have a₂ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel x.P.isLB w w'' g g'' x'.P.isLB x''.P.isLB
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp F = F'' := dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', he', w', hg''.trans hg.symm, Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel x.P.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel x.P.isLB (fun _ => he') r r''),
    (appLE_eq_iff_stalk w' x'.th x''.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (appLE_eq_iff_stalk w x.th x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (appLE_eq_iff_stalk w'' x.th x''.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, ← hFF, ← Category.assoc]
      congr 1
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KeyCancel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EqOfInvariantGenTranslates
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory

theorem eq_of_invariantGen_translates :
    Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (ξ ξ' : 𝟙_ (Over (Sp K)) ⟶ P.A) (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ)).left, ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ')).left] ![1, -1])), (m : K) ≠ 0 → u.IsGen → (∀ δ : 𝟙_ (Over (Sp K)) ⟶ P.A, δ ^ m = 1 → ∀ (y : P.A.left) J, Good P.L y J → val u ((toUnit P.A ≫ δ) * 𝟙 P.A).left y J = val u (𝟙 _) y J) → ξ = ξ' := by
  intro laws K _ _ P m ξ ξ' u hm hu hinv
  haveI : IsCommMonObj P.A := P.isAb.comm
  have hmul : ∀ {Z : Over (Sp K)} (y : Z ⟶ P.A), y ≫ Out.mulA P.A m = y ^ m :=
    fun y => by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  obtain ⟨v, hv⟩ := exists_isGen_of_invariant P.isLB (K := Fin 2)
    ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] ![1, -1]
    (Out.mulA P.A m).left
    (I := {y : 𝟙_ (Over (Sp K)) ⟶ P.A // y ^ m = 1})
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => by
      rw [← Over.comp_left, hmul, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul,
        Out.mulA])
    (fun U f hf => torsion_invariant_descends (fun S _ Q n hn =>
      let ⟨a, b, c, d, _⟩ := laws.mulN S Q n hn; ⟨a, b, c, d⟩) K P m hm U f fun y hy => hf ⟨y, hy⟩) _
    (fun i => by
      fin_cases i
      · change ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ)).left =
          (Out.mulA P.A m ≫ (𝟙 P.A * (toUnit P.A ≫ ξ))).left
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.mulA]
      · change ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ')).left =
          (Out.mulA P.A m ≫ (𝟙 P.A * (toUnit P.A ≫ ξ'))).left
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.mulA])
    u hu (fun y z J hJ => hinv y.1 y.2 z J hJ)
  let B : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let x : B ⟶ P.A := toUnit B ≫ (ξ * ξ'⁻¹)
  let r : B ⊗ P.A ⟶ P.A := snd B P.A * (toUnit _ ≫ ξ'⁻¹)
  have hx : x = toUnit _ ≫ η[P.A] := by
    refine P.ktriv K (𝟙 _) x fun p => ⟨⊤, trivial, ?_⟩
    have h3 : (fun i => r.left ≫
        ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] i) =
        ![(lift (fst B P.A ≫ x) (snd B P.A) ≫ μ[P.A]).left, (snd B P.A).left] := by
      funext i
      fin_cases i
      · change (r ≫ (𝟙 P.A * (toUnit P.A ≫ ξ))).left = ((fst B P.A ≫ x) * snd B P.A).left
        congr 1
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
        simp only [r, x, comp_toUnit_assoc, MonObj.comp_mul]
        rw [_root_.mul_assoc, _root_.mul_comm (snd B P.A), _root_.mul_comm (toUnit _ ≫ ξ'⁻¹)]
      · change (r ≫ (𝟙 P.A * (toUnit P.A ≫ ξ'))).left = (snd B P.A).left
        congr 1
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
        simp only [r]
        rw [GrpObj.comp_inv, inv_mul_cancel_right]
    have h4 : ∃ w : LB.Gen (LB.LinComb P.L (fun i => r.left ≫
        ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] i) ![1, -1]),
        w.IsGen := ⟨_, DVR.pullGen_isGen _ _ _ v hv _⟩
    rw [h3] at h4
    obtain ⟨w, hw⟩ := h4
    exact exists_isGen_pull (Out.translDiff P.A P.L x) w hw _
  let s : 𝟙_ (Over (Sp K)) ⟶ B := Over.homMk (𝟙_ (Over (Sp K))).hom (Category.comp_id _)
  have h5 := congrArg (fun q => s ≫ q) hx
  simp only [x, comp_toUnit_assoc] at h5
  rw [← Hom.one_def, toUnit_unit, Category.id_comp] at h5
  exact mul_inv_eq_one.1 h5

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExactAtSectionCubeOfMulPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

noncomputable section
namespace GlobalTheory.TraceDescent
open GlobalTheory.AbLaw.PowVanish

theorem exactAt_of_trace {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (A B : GlobalTheory.Cube.{0} κ R)
    (φ : ∀ s, A.obj s →+ B.obj s) (T : ∀ s, B.obj s →+ B.obj s)
    (hφ : ∀ {s t : Finset κ} (h : s ⊆ t) x, φ t (Cube.res A h x) = Cube.res B h (φ s x))
    (hT : ∀ {s t : Finset κ} (h : s ⊆ t) x, T t (Cube.res B h x) = Cube.res B h (T s x))
    (inj : ∀ s, Function.Injective (φ s)) (n : ℕ) (hn : IsUnit (n : R))
    (himg : ∀ s y, ∃ x, φ s x = T s y) (htr : ∀ s x, T s (φ s x) = n • φ s x) (p : ℕ)
    (H : (cubeComplex B).ExactAt p) : (cubeComplex A).ExactAt p := by
  have dφ : ∀ q (x : Cube.Term A q), Cube.d B q (fun s => φ s.1 (x s)) = fun t => φ t.1 (Cube.d A q x t) :=
    fun q x => funext fun t => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Cube.d_apply, map_sum, map_zsmul, hφ]
  have dT : ∀ q (x : Cube.Term B q), Cube.d B q (fun s => T s.1 (x s)) = fun t => T t.1 (Cube.d B q x t) :=
    fun q x => funext fun t => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Cube.d_apply, map_sum, map_zsmul, hT]
  rcases p with _ | p
  · rw [cubeComplex_exactAt_zero_iff'] at H ⊢
    intro x y hxy
    have : (fun s => φ s.1 (x s) : Cube.Term B 0) = fun s => φ s.1 (y s) := H (by rw [dφ, dφ, hxy])
    exact funext fun s => inj _ (congrFun this s)
  · rw [cubeComplex_exactAt_succ_iff] at H ⊢
    intro x
    refine ⟨fun hx => ?_, fun ⟨y, hy⟩ => hy ▸ Cube.d_d A p y⟩
    obtain ⟨y, hy⟩ := (H (fun s => φ s.1 (x s))).1 (by
      rw [dφ, hx]; exact funext fun t => map_zero _)
    choose z hz using fun s : {s : Finset κ // s.card = p} => himg s.1 (y s)
    have key : Cube.d A p z = (n : R) • x := funext fun t => inj _ (by
      have e := congrFun (dφ p z) t
      have e' := congrFun (dT p y) t
      simp only [hz] at e
      rw [← e, e', hy, htr, Pi.smul_apply, Nat.cast_smul_eq_nsmul, map_nsmul])
    obtain ⟨u, hu⟩ := hn.exists_left_inv
    exact ⟨u • z, by rw [map_smul, key, smul_smul, hu, one_smul]⟩

variable {X Y : Scheme.{0}} (f : Y ⟶ X) (M : LB X)

theorem le_deck {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W) (j : (M.pull f).ι) :
    W' ⊓ (M.pull f).U j ≤ τ ⁻¹ᵁ (W ⊓ (M.pull f).U j) := fun y hy =>
  ⟨e hy.1, mem_pull.2 (by
    have := mem_pull.1 hy.2
    rwa [← hτ] at this)⟩

def act {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W) :
    SecOn (M.pull f) W →+ SecOn (M.pull f) W' where
  toFun s := GlobalTheory.LB.mkSec (fun j => pb τ (le_deck f M hτ e j) (GlobalTheory.LB.coord s j)) fun i j => by
    have e₀ : W' ⊓ (M.pull f).U i ⊓ (M.pull f).U j ≤ τ ⁻¹ᵁ (W ⊓ (M.pull f).U i ⊓ (M.pull f).U j) :=
      le_deck f M hτ (le_deck f M hτ e i) j
    have h := congrArg (pb τ e₀) (GlobalTheory.LB.coord_mem s i j)
    have g₁ : ∀ (O : Y.Opens) (e : O ≤ (M.pull f).U i ⊓ (M.pull f).U j),
        rs Y e ((M.pull f).g i j).val = pb f (pre_pull M f (i PUnit.unit) (j PUnit.unit) e)
          (M.g (i PUnit.unit) (j PUnit.unit)).val :=
      fun O e => rs_pull_g M f (i PUnit.unit) (j PUnit.unit) (W := O) e
    exact (rs_pb τ _ _ _).trans ((pb_rs τ e₀ _ _).symm.trans (h.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ((congrArg (pb τ e₀) (g₁ _ _)).trans ((pb_pb τ f _ e₀ _).trans
        ((pb_congr hτ _ _).trans (g₁ _ _).symm))) ((pb_rs τ e₀ _ _).trans (rs_pb τ _ _ _).symm)))))
  map_zero' := GlobalTheory.LB.sec_ext fun j => map_zero (pb τ _)
  map_add' s t := GlobalTheory.LB.sec_ext fun j => map_add (pb τ _) _ _

theorem coord_act {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W)
    (s : SecOn (M.pull f) W) (j : (M.pull f).ι) :
    GlobalTheory.LB.coord (act f M hτ e s) j = pb τ (le_deck f M hτ e j) (GlobalTheory.LB.coord s j) := rfl

theorem act_restrict {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W) (e' : W' ≤ τ ⁻¹ᵁ W')
    (h : W' ≤ W) (s : SecOn (M.pull f) W) :
    act f M hτ e' (SecOn.restrict _ h s) = SecOn.restrict _ h (act f M hτ e s) :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, SecOn.coord_restrict, SecOn.coord_restrict, coord_act, pb_rs, rs_pb]

theorem act_act {τ σ ρ : Y ⟶ Y} (hτ : τ ≫ f = f) (hσ : σ ≫ f = f) (hρ : ρ ≫ f = f) (H : τ ≫ σ = ρ)
    {W : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W) (e' : W ≤ σ ⁻¹ᵁ W) (e'' : W ≤ ρ ⁻¹ᵁ W) (s : SecOn (M.pull f) W) :
    act f M hτ e (act f M hσ e' s) = act f M hρ e'' s :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, coord_act, coord_act, pb_pb, pb_congr H]

theorem coord_pullLE {V : X.Opens} {W : Y.Opens} (e : W ≤ f ⁻¹ᵁ V) (s : SecOn M V) (j : (M.pull f).ι) :
    GlobalTheory.LB.coord (SecOn.pullLE M f V W e s) j =
      pb f ((inf_le_inf_right _ e).trans (GlobalTheory.LB.pull_inf_le f V j)) (GlobalTheory.LB.coord s (j PUnit.unit)) :=
  SecOn.coord_pullLE f e s j

theorem act_pullLE {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {V : X.Opens} {W : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W)
    (h : W ≤ f ⁻¹ᵁ V) (s : SecOn M V) :
    act f M hτ e (SecOn.pullLE M f V W h s) = SecOn.pullLE M f V W h s :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, coord_pullLE, pb_pb, pb_congr hτ]

variable {G : Type} (τ : G → (Y ⟶ Y)) (hτ : ∀ y, τ y ≫ f = f)
    (hgal : ∀ (U : X.Opens) (s : Γ(Y, f ⁻¹ᵁ U)),
      (∀ y (e : f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U)), pb (τ y) e s = s) → ∃! g : Γ(X, U), (f.app U).hom g = s)
include hτ hgal


omit hτ in
theorem exists_fun (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : f ⁻¹ᵁ U ≤ W) (s : Γ(Y, W))
    (hs : ∀ y (e : W ≤ τ y ⁻¹ᵁ W), pb (τ y) e s = s) : ∃! g : Γ(X, U), pb f e g = s := by
  obtain rfl := le_antisymm e e'
  simpa only [app_eq_pb] using hgal U s hs

theorem pb_injective (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : f ⁻¹ᵁ U ≤ W) :
    Function.Injective (pb f e) := fun a _ hab =>
  (exists_fun f τ hgal U W e e' (pb f e a) (fun y _ => by rw [pb_pb, pb_congr (hτ y)])).unique rfl hab.symm

theorem pullLE_injective (V : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ V) (e' : f ⁻¹ᵁ V ≤ W) :
    Function.Injective (SecOn.pullLE M f V W e) := fun a b hab => GlobalTheory.LB.sec_ext fun i => by
  have h := (coord_pullLE f M e a (fun _ => i)).symm.trans
    ((congrArg (GlobalTheory.LB.coord · (fun _ => i : (M.pull f).ι)) hab).trans (coord_pullLE f M e b (fun _ => i)))
  exact pb_injective f τ hτ hgal (V ⊓ M.U i) (W ⊓ (M.pull f).U (fun _ => i)) _
    (fun y hy => ⟨e' hy.1, mem_pull.2 hy.2⟩) h

theorem exists_pullLE (V : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ V) (e' : f ⁻¹ᵁ V ≤ W)
    (s : SecOn (M.pull f) W) (hs : ∀ y (e : W ≤ τ y ⁻¹ᵁ W), act f M (hτ y) e s = s) :
    ∃ x, SecOn.pullLE M f V W e x = s := by
  have inv : ∀ y, W ≤ τ y ⁻¹ᵁ W := fun y => by
    obtain rfl := le_antisymm e e'
    rw [← Scheme.Hom.comp_preimage, hτ]
  have H : ∀ i : M.ι, ∃ g : Γ(X, V ⊓ M.U i),
      pb f ((inf_le_inf_right _ e).trans (GlobalTheory.LB.pull_inf_le f V (fun _ => i))) g =
        GlobalTheory.LB.coord s (fun _ => i) := fun i =>
    (exists_fun f τ hgal (V ⊓ M.U i) (W ⊓ (M.pull f).U (fun _ => i)) _
      (fun y hy => ⟨e' hy.1, mem_pull.2 hy.2⟩) _ fun y _ =>
      congrArg (GlobalTheory.LB.coord · (fun _ => i : (M.pull f).ι)) (hs y (inv y))).exists
  choose g hg using H
  refine ⟨GlobalTheory.LB.mkSec g fun i j => ?_, GlobalTheory.LB.sec_ext fun j => (coord_pullLE f M e _ j).trans (hg _)⟩
  have e₀ : W ⊓ (M.pull f).U (fun _ => i) ⊓ (M.pull f).U (fun _ => j) ≤ f ⁻¹ᵁ (V ⊓ M.U i ⊓ M.U j) :=
    fun y hy => ⟨⟨e hy.1.1, mem_pull.1 hy.1.2⟩, mem_pull.1 hy.2⟩
  apply pb_injective f τ hτ hgal (V ⊓ M.U i ⊓ M.U j) _ e₀
    (fun y hy => ⟨⟨e' hy.1.1, mem_pull.2 hy.1.2⟩, mem_pull.2 hy.2⟩)
  have h := GlobalTheory.LB.coord_mem s (fun _ => i) (fun _ => j)
  rw [← hg, ← hg] at h
  exact (pb_rs f e₀ _ _).trans ((rs_pb f _ _ _).symm.trans (h.trans ((congrArg₂ (· * ·)
    ((rs_pull_g M f i j _).trans (pb_rs f e₀ _ _).symm)
    ((rs_pb f _ _ _).trans (pb_rs f e₀ _ _).symm)).trans (map_mul _ _ _).symm)))

theorem exactAt_of_pull [Group G] [Fintype G] (hmul : ∀ y z, τ y ≫ τ z = τ (y * z))
    {R : Type} [CommRing R] (a : X ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ Spec (CommRingCat.of R))
    (hu : IsUnit ((Fintype.card G : ℕ) : R)) {I : Type} [LinearOrder I] (D : I → X.Opens) (p : ℕ)
    (H : (cubeComplex (secCube b (M.pull f) (fun i => f ⁻¹ᵁ D i))).ExactAt p) :
    (cubeComplex (secCube a M D)).ExactAt p := by
  have inv : ∀ y (s : Finset I), (⨅ i ∈ s, f ⁻¹ᵁ D i) ≤ τ y ⁻¹ᵁ (⨅ i ∈ s, f ⁻¹ᵁ D i) := fun y s => by
    rw [← preimage_biInf, ← Scheme.Hom.comp_preimage, hτ]
  let φ : ∀ s : Finset I, SecOn M (⨅ i ∈ s, D i) →+ SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) :=
    fun s => (SecOn.pullLE M f _ _ (preimage_biInf D f s).ge).toAddMonoidHom
  let T : ∀ s : Finset I, SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) →+ SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) :=
    fun s => ∑ y, act f M (hτ y) (inv y s)
  have hT : ∀ s x, T s x = ∑ y, act f M (hτ y) (inv y s) x := fun s x => AddMonoidHom.finsetSum_apply _ _ _
  refine exactAt_of_trace _ _ φ T (fun {s t} h x => ?_) (fun {s t} h x => ?_)
    (fun s => pullLE_injective f M τ hτ hgal _ _ (preimage_biInf D f s).ge (preimage_biInf D f s).le) _ hu (fun s y => ?_)
    (fun s x => ?_) p H
  · exact (SecOn.pullLE_restrict f (iInf_le_iInf_of_subset D h) (preimage_biInf D f t).ge _).trans
      (SecOn.restrict_pullLE f (preimage_biInf D f s).ge (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) _).symm
  · change T t (SecOn.restrict _ (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) x) =
      SecOn.restrict _ (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) (T s x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT t, hT s x, map_sum]
    exact Finset.sum_congr rfl fun y _ => act_restrict f M (hτ y) (inv y s) (inv y t) _ x
  · refine exists_pullLE f M τ hτ hgal _ _ (preimage_biInf D f s).ge (preimage_biInf D f s).le (T s y)
      fun z e => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT s y, map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun w =>
      act_act f M (hτ z) (hτ w) (hτ (z * w)) (hmul z w) e (inv w s) (inv (z * w) s) y
  · refine (hT s _).trans ((Finset.sum_congr rfl fun y _ =>
      act_pullLE f M (hτ y) (inv y s) (preimage_biInf D f s).ge x).trans ?_)
    rw [Finset.sum_const, Finset.card_univ]
    rfl

end GlobalTheory.TraceDescent

theorem GlobalTheory.exactAt_secCube_of_mul_pull : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (N : LB P.A.left) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens) (p : ℕ), (m : K) ≠ 0 → N.IsLB → (cubeComplex (secCube P.A.hom (N.pull (Out.mulA P.A m).left) (fun i => (Out.mulA P.A m).left ⁻¹ᵁ D i))).ExactAt p → (cubeComplex (secCube P.A.hom N D)).ExactAt p := by
  intro L K _ _ P m N I _ _ D p hm _ H
  classical
  haveI := P.isAb.comm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h => hm (by rw [h, Nat.cast_zero])
  let G : Subgroup (𝟙_ (Over (Sp K)) ⟶ P.A) := (powMonoidHom m).ker
  have hc : Nat.card G = m ^ (2 * P.g) := (L.mulN _ P m hm1).2.2.2.2 K (𝟙 _) hm
  haveI : Finite G := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ (by omega))
  haveI : Fintype G := Fintype.ofFinite G
  have hgal := GlobalTheory.torsion_invariant_descends (fun S _ P n hn =>
    have h := L.mulN S P n hn
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) K P m hm
  refine GlobalTheory.TraceDescent.exactAt_of_pull (Out.mulA P.A m).left N (G := G)
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left) (fun y => ?_)
    (fun U f hf => hgal U f fun y hy e => hf ⟨y, hy⟩ e) (fun y z => ?_) _ _ ?_ D p H
  · have hy : y.1 ^ m = 1 := y.2
    rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy,
      MonObj.comp_one, _root_.one_mul]
  · rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
      Subgroup.coe_mul, MonObj.comp_mul, ← _root_.mul_assoc, _root_.mul_comm (toUnit P.A ≫ z.1)]
  · rw [← Nat.card_eq_fintype_card, hc, Nat.cast_pow]
    exact (IsUnit.mk0 _ hm).pow _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAdmissibleKeyNumericalDataPrimeTo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_quaternion_matrix (m : ℕ) : ∃ A : Matrix (Fin 4) (Fin 4) ℤ,
    A.transpose * A = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  have h' : (m : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    rw [← h]; push_cast; ring
  refine ⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_⟩
  rw [h']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.one_apply] <;> ring

theorem exists_admissibleKeyNumericalData_prime_to : ∀ g p : ℕ, 1 ≤ g → p.Prime → ∃ (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ), admitted g n l l' al ∧ ¬ p ∣ degProd g n l l' ∧ 1 ≤ degProd g n l l' ∧ 1 ≤ kaExp g n l l' := by
  intro g p hg hp
  choose al hal using exists_quaternion_matrix
  have hp0 := hp.pos
  have hnd : ¬ p ∣ degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p) := by
    unfold degProd
    rw [Prime.dvd_finsetProd_iff hp.prime]
    rintro ⟨j, hj, hd⟩
    have hj' : j ≤ g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj'
    have e1 : (j + k) * (4 * p) + 1 - j * (4 * p) = p * (4 * k) + 1 := by
      apply Nat.sub_eq_of_eq_add; ring
    have e2 : (j + k) * (4 * p) + 1 + p - j * (4 * p) = p * (4 * k + 1) + 1 := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e1, e2] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))
  have hpos : 0 < degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p) :=
    Nat.pos_of_ne_zero fun h => hnd (h ▸ dvd_zero p)
  refine ⟨4 * p, g * (4 * p) + 1, g * (4 * p) + 1 + p, al, ⟨by omega, by omega, by omega, hal⟩,
    hnd, hpos, ?_⟩
  unfold kaExp
  have h1 : 0 < g * (4 * p) + 1 + p - (g * (4 * p) + 1) := by omega
  have h2 := Nat.factorial_pos g
  apply Nat.succ_le_of_lt
  positivity

end GlobalTheory.KeyKa
end

