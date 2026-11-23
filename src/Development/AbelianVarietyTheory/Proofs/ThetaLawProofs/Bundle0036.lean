module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyNormalExists

def constMul {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} (a : R) (s : L.Sec) : L.Sec where
  f j := constFn p _ a * s.f j
  compat j k := by
    rw [map_mul, map_mul, ThetaOnto.res_constFn, ThetaOnto.res_constFn, s.compat j k]
    ring

theorem mem_nonzeroLocus_constMul {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : L.Sec) {z : X} (hz : z ∈ Out.nonzeroLocus s) : z ∈ Out.nonzeroLocus (constMul p a s) := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  have hu : IsUnit (constFn p (L.U i) a) := (ha.map _).map _
  change z ∈ X.basicOpen (constFn p (L.U i) a * s.f i)
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]
  exact ⟨X.basicOpen_le _ hi, hi⟩

theorem isFn_constMul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (a : ℂ) {s : L.Sec}
    {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) : u.IsFn (constMul A.hom a s) (fun z => a * θ z) := by
  intro i z hz
  change valAt' _ _ (constFn A.hom (L.U i) a * s.f i) = _
  rw [valAt'_mul, valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz, h i z hz, _root_.mul_assoc]

theorem exists_normalAt_one (x : KeyIn ℂ) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hM : M.det ≠ 0) (h : KeyPow.NormalAt x τ M a b c) :
    ∃ th hth v hv, KeyPow.NormalAt ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ τ 1 a b 1 := by
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  have := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hb⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  choose v hv using fun i => (hex (M⁻¹ i)).exists
  refine ⟨constMul x.P.A.hom c⁻¹ x.th, fun s => ?_, v,
    (hb M⁻¹ v x.basis hv).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit), u, h₁, h₂, h₃, h₄, ?_, fun i => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne s
    exact ⟨z, hz, mem_nonzeroLocus_constMul _ (inv_ne_zero hc).isUnit _ hz'⟩
  · have := isFn_constMul u c⁻¹ h₅
    simpa only [inv_mul_cancel_left₀ hc, _root_.one_mul] using this
  · have := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v (M⁻¹ i) (v i) x.basis.1 h₆ (hv i)
    have e : ∑ j, M⁻¹ i j • (2 * Real.pi * Complex.I : ℂ)⁻¹ • M j =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (1 : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) i := by
      rw [← Matrix.nonsing_inv_mul M hM.isUnit]
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at this
    exact this

theorem exists_normalAt :
    ThetaUnifAV → ∀ x : KeyIn ℂ, (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), GlobalTheory.KeyPow.charHalf x.P.g a b ∧ c ≠ 0 ∧ M.det ≠ 0 ∧ GlobalTheory.KeyPow.NormalAt x τ M a b c) ∧ ∃ (th : x.P.L.Sec) (hth : _) (v : _) (hv : _) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ), GlobalTheory.KeyPow.charHalf x.P.g a b ∧ GlobalTheory.KeyPow.NormalAt ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ τ 1 a b 1 := by
  intro hU x
  obtain ⟨u, Hm, χ, -, hA, hR, hd, -⟩ := hU x.P x.rig x.rig_gen
  choose W hW using fun i => (hd _ (x.basis.1 i)).exists
  obtain ⟨θ, hθ⟩ := KeyPow.exists_isFn x.P.isLB u x.th
  obtain ⟨Fd, hF⟩ := KeyPow.exists_isAddFundamentalDomain u
  obtain ⟨u', τ, M, a, b, c, h₁, h₂, ha, hb, h₃, h₄, hc, h₅, hM, h₆, -⟩ :=
    keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd _ _ hA hR hθ hW hF rfl rfl
  have hN : KeyPow.NormalAt x τ M a b c := ⟨u', h₁, h₂, h₃, h₄, h₅, h₆⟩
  obtain ⟨th, hth, v, hv, h⟩ := exists_normalAt_one x hc hM hN
  exact ⟨⟨τ, M, a, b, c, ⟨ha, hb⟩, hc, hM, hN⟩, th, hth, v, hv, τ, a, b, ⟨ha, hb⟩, h⟩

end GlobalTheory.KeyNormalExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.RigSymSubring

open GlobalTheory.CechPic

theorem pic_descends (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S)
    (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (c d : Pic X₀)
    (H : IsPullback π f f₀ (spMap R₀.subtype)) (e : pull π c = pull π d) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀),
        IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → pull π₁ c = pull π₁ d := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨N, hN, rfl⟩ := cls_surj d
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.lbIso_descends_to_subring_containing_finset S R₀ X X₀ f f₀ π M N H hM hN
    ((cls_eq_iff (pull_isLB hM π) (pull_isLB hN π)).1 e)
  exact ⟨F, fun R₁ h hR X₁ f₁ π₁ H₁ =>
    (cls_eq_iff (pull_isLB hM π₁) (pull_isLB hN π₁)).2 (hF R₁ h hR X₁ f₁ π₁ H₁)⟩

variable {T : Scheme.{0}} {A : Over T} [GrpObj A] {L : LB A.left}

theorem rigidified_iff (hL : L.IsLB) : Out.Rigidified A L ↔ pull (eSec A) (cls L hL) = 0 :=
  (cls_eq_zero_iff (pull_isLB hL _)).symm

theorem gen_iff (hL : L.IsLB) {Y : Scheme.{0}} (r : Y ⟶ A.left) :
    (∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![r ≫ (GrpObj.inv : A ⟶ A).left, r] ![1, -1]), t.IsGen) ↔
      pull r (pull (GrpObj.inv : A ⟶ A).left (cls L hL)) = pull r (cls L hL) := by
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL, Fin.sum_univ_two, ← pull_comp]
  simp [← sub_eq_add_neg, sub_eq_zero]

theorem sym_of_cls (hL : L.IsLB) (e : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL) : Out.Sym A L :=
  fun _ => ⟨⊤, trivial, (gen_iff hL _).2 (by rw [e])⟩

theorem cls_of_sym {S : Type} [CommRing S] [IsLocalRing S] {A : Over (Sp S)} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) (hs : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  obtain ⟨U, hU, ht⟩ := hs (IsLocalRing.closedPoint S)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have i : ∀ c : Pic A.left, pull (inv (A.hom ⁻¹ᵁ ⊤).ι (I := inferInstanceAs (IsIso A.left.topIso.hom)))
      (pull (A.hom ⁻¹ᵁ ⊤).ι c) = c := fun c => by rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  exact (i _).symm.trans ((congrArg _ ((gen_iff hL _).1 ht)).trans (i _))

end GlobalTheory.RigSymSubring

namespace GlobalTheory

open GlobalTheory.CechPic GlobalTheory.RigSymSubring

theorem rigidified_sym_descend_to_subring : ∀ (S : Type) [CommRing S] [IsLocalRing S] (R₀ : Subring S) (P : Out.PolAV (Sp S)) (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : P.A.left ⟶ A₀.left) (L₀ : LB A₀.left), IsAbelianScheme A₀ → L₀.IsLB → IsGrpPullback P.A A₀ (spMap R₀.subtype) φ → LBIso P.L (L₀.pull φ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (π : A₁.left ⟶ A₀.left), IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π → Out.Rigidified A₁ (L₀.pull π) ∧ Out.Sym A₁ (L₀.pull π) := by
  classical
  intro S _ _ R₀ P A₀ _ φ L₀ hA hL H hw
  have := hA.proper
  have hc : cls P.L P.isLB = pull φ (cls L₀ hL) := (cls_eq_iff P.isLB (pull_isLB hL φ)).2 hw
  have e₁ : pull (spMap R₀.subtype) (pull (X := A₀.left) (Y := Sp R₀) (eSec A₀) (cls L₀ hL)) =
      pull (spMap R₀.subtype) 0 := by
    have h₁ := (rigidified_iff P.isLB).1 P.rigid
    rw [hc, ← pull_comp, PolBaseChange.eSec_comm H] at h₁
    exact (pull_comp _ _ _).symm.trans (h₁.trans (map_zero _).symm)
  have e₂ : pull φ (pull (GrpObj.inv : A₀ ⟶ A₀).left (cls L₀ hL)) = pull φ (cls L₀ hL) := by
    have h₂ := cls_of_sym P.isLB P.sym
    rwa [hc, ← pull_comp, PolBaseChange.inv_comm H, pull_comp] at h₂
  obtain ⟨F₁, h₁⟩ := pic_descends S R₀ (Sp S) (Sp R₀) (𝟙 _) (𝟙 _) (spMap R₀.subtype) _ _
    (IsPullback.of_vert_isIso ⟨by simp⟩) e₁
  obtain ⟨F₂, h₂⟩ := pic_descends S R₀ _ _ P.A.hom A₀.hom φ _ _ H.1 e₂
  refine ⟨F₁ ∪ F₂, fun R₁ h hF A₁ _ π H₁ => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hF
  have a := h₁ R₁ h hF.1 (Sp R₁) (𝟙 _) (spMap (Subring.inclusion h)) (IsPullback.of_vert_isIso ⟨by simp⟩)
  have b := h₂ R₁ h hF.2 _ A₁.hom π H₁.1
  refine ⟨(rigidified_iff (pull_isLB hL π)).2 ?_, sym_of_cls (pull_isLB hL π) ?_⟩
  · rw [cls_pull hL, ← pull_comp, PolBaseChange.eSec_comm H₁]
    exact (pull_comp _ _ _).trans (a.trans (map_zero _))
  · rw [cls_pull hL, ← pull_comp, PolBaseChange.inv_comm H₁, pull_comp, b]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyComp

theorem stalk_of_appLE_eq {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (s : L.Sec)
    (s' : L'.Sec) (h : ∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ L.U (j PUnit.unit)),
      (F.appLE _ _ hle).hom (s.f (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i))
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun _ hy => mem_pull.1 hy.1
  have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have e := congrArg (gs r z _) (h (fun _ => j) k hle)
  refine (gs_appLE F _ _ hle r z hy _).symm.trans (e.trans ?_)
  rw [gs_mul _ z _ hy, gs_res _ z _ hy]
  exact congrArg (· * _) (gs_unit _ z _ hy _)

end GlobalTheory.KeyComp

namespace GlobalTheory

theorem keyPB_trans : ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (x : KeyIn R) (x' : KeyIn R') (x'' : KeyIn R'') (f : R →+* R') (f' : R' →+* R''), KeyPB x' x f → KeyPB x'' x' f' → KeyPB x'' x (f'.comp f) := by
  intro R R' R'' _ _ _ x x' x'' f f' H H'
  obtain ⟨φ, he, w, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x'.P.isLB w w' g g' x.P.isLB x''.P.isLB
  have he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec x.P.A := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl,
    (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _
      (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).2 r₂
  · refine KeyPow.appLE_eq_of_stalk w'' x.th x''.th fun z j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' z)
    have a := KeyComp.stalk_of_appLE_eq w x.th x'.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := KeyComp.stalk_of_appLE_eq w' x'.th x''.th hs' (𝟙 _) z i k hi hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

end GlobalTheory
end
end

