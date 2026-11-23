module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.EllConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_mem (H : Host E) (a : OK H) : H.bar (a : 𝓞 E) ∈ OK H := by
  obtain ⟨a, ha⟩ := a
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl : x = H.w0 := hx
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]
    exact sub_mem (one_mem _) (wK H).2
  | algebraMap r =>
    have : H.bar (algebraMap ℤ (𝓞 E) r) = algebraMap ℤ (𝓞 E) r := by simp
    show H.bar (algebraMap ℤ (𝓞 E) r) ∈ OK H
    rw [this]
    exact Subalgebra.algebraMap_mem _ r
  | add x y hx hy h₁ h₂ => exact (map_add H.bar x y) ▸ add_mem h₁ h₂
  | mul x y hx hy h₁ h₂ => exact (map_mul H.bar x y) ▸ mul_mem h₁ h₂

def barK (H : Host E) : OK H →+* OK H where
  toFun a := ⟨H.bar (a : 𝓞 E), bar_mem H a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem barK_wK_add (H : Host E) : barK H (wK H) + wK H = 1 :=
  Subtype.ext (by
    show H.bar H.w0 + H.w0 = 1
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, sub_add_cancel])

theorem isLieComb_one_sub {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (v : epsR R ⟶ G)
    (hv : IsTangent v) (ω : R) (f g : G ⟶ G) (hfg : g * f = 𝟙 G) (h : IsLieComb ![ω] ![v] (v ≫ f)) :
    IsLieComb ![1 - ω] ![v] (v ≫ g) := by
  have hv' : ∀ i, IsTangent (![v] i) := fun i => by fin_cases i; exact hv
  rw [GlobalTheory.LieComb.isLieComb_iff_tanExp] at h ⊢
  have e₁ : (v ≫ g) * (v ≫ f) = v := by rw [← MonObj.comp_mul, hfg, Category.comp_id]
  have e₂ := map_add (GlobalTheory.LieComb.combHom hv') ![1 - ω] ![ω]
  have e₃ : (![1 - ω] + ![ω] : Fin 1 → R) = Pi.single 0 1 := by
    funext i
    fin_cases i
    simp
  rw [e₃] at e₂
  have e₄ : v = GlobalTheory.SqZero.tanExp ![v] ![1 - ω] * GlobalTheory.SqZero.tanExp ![v] ![ω] :=
    (GlobalTheory.LieComb.tanExp_single hv' 0).symm.trans (congrArg Additive.toMul e₂)
  rw [← h] at e₄
  exact mul_right_cancel (e₁.trans e₄)


open GlobalTheory.PrimNorm in
theorem lbIso_of_adj {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {f g : B ⟶ B} (h : LamEq M f (𝟙 B) M (𝟙 B) g) : LBIso (cubeLB B ![𝟙 B, g] M) (cubeLB B ![𝟙 B, f] M) := by
  have h' : LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) := by
    simpa only [LamEq, Category.comp_id] using h
  have e := diff₂_ptCls_adj hM h' (𝟙 B) (𝟙 B)
  rw [Category.id_comp, Category.id_comp, diff₂_comm] at e
  exact (lbIso_iff hM _ _ _ _).2 ((prod_square_id _ _ (cls M)).trans (e.symm.trans (prod_square_id _ _ (cls M)).symm))

theorem exists_conj_action (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    (ω : R) (C : Ell H R ω) :
    ∃ a : OAct (OK H) C.P.A, (∀ x y : OK H, (y : 𝓞 E) = H.bar x → a.act x = C.act.act y) ∧
      IsLieComb ![1 - ω] ![C.v] (C.v ≫ a.act (wK H)) ∧
      (∀ x y : OK H, (y : 𝓞 E) = H.bar x → LamEq C.P.L (a.act x) (𝟙 C.P.A) C.P.L (𝟙 C.P.A) (a.act y)) ∧
      LBIso C.P.L (cubeLB C.P.A ![𝟙 C.P.A, a.act (wK H)] C.P.L) := by
  refine ⟨Serre.comapAct C.act (barK H), fun x y h => ?_, ?_, fun x y h => ?_, ?_⟩
  · exact congrArg C.act.act (Subtype.ext h.symm)
  · exact isLieComb_one_sub C.v (C.basis.1 0) ω (C.act.act (wK H)) _
      (by rw [Serre.comapAct_act, ← C.act.add, barK_wK_add, C.act.one]) C.eig
  · exact C.adj _ _ (congrArg H.bar h)
  · exact LBIso.trans C.P.isLB (DVR.linComb_isLB _ C.P.isLB _ _) (DVR.linComb_isLB _ C.P.isLB _ _) C.prim
      (lbIso_of_adj C.P.isLB (C.adj (barK H (wK H)) (wK H) (GlobalTheory.HostModel.bar_bar H _).symm))

end GlobalTheory.CM.EllConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPicardGroup
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CechPicMul


open Classical in
def cl {X : Scheme.{0}} (L : LB X) : Multiplicative (CechPic.Pic X) :=
  if h : L.IsLB then Multiplicative.ofAdd (CechPic.cls L h) else 1

theorem cl_eq {X : Scheme.{0}} {L : LB X} (h : L.IsLB) : cl L = Multiplicative.ofAdd (CechPic.cls L h) := dif_pos h

theorem exists_picardGroup : ∃ (Pic : Scheme.{0} → Type 1) (_ : ∀ X, CommGroup (Pic X)) (cl : ∀ {X : Scheme.{0}}, LB X → Pic X) (pl : ∀ {X Y : Scheme.{0}}, (Y ⟶ X) → (Pic X →* Pic Y)),
  (∀ (X : Scheme.{0}) (L M : LB X), L.IsLB → M.IsLB → (cl L = cl M ↔ LBIso L M)) ∧ (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → (cl L = 1 ↔ ∃ t : LB.Gen L, t.IsGen)) ∧
  (∀ (X : Scheme.{0}) (c : Pic X), pl (𝟙 X) c = c) ∧ (∀ (X Y Z : Scheme.{0}) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Pic X), pl (g ≫ f) c = pl g (pl f c)) ∧
  (∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ), (LB.LinComb L φ ε).IsLB ∧ cl (LB.LinComb L φ ε) = ∏ k, pl (φ k) (cl L) ^ ε k) ∧
  ∀ (X : Scheme.{0}) (L M : LB X), L.IsLB → M.IsLB → (LB.div M L).IsLB ∧ cl (LB.div M L) = cl M / cl L := by
  refine ⟨fun X => Multiplicative (CechPic.Pic X), fun X => inferInstance, cl,
    fun f => AddMonoidHom.toMultiplicative (CechPic.pull f), fun X L M hL hM => ?_, fun X L hL => ?_,
    fun X c => CechPic.pull_id c.toAdd, fun X Y Z f g c => CechPic.pull_comp g f c.toAdd,
    fun X Y L hL I _ φ ε => ⟨LB.isLB_linComb hL φ ε, ?_⟩, fun X L M hL hM => ⟨LB.isLB_div hM hL, ?_⟩⟩
  · beta_reduce
    rw [cl_eq hL, cl_eq hM]
    exact CechPic.cls_eq_iff hL hM
  · beta_reduce
    rw [cl_eq hL]
    exact CechPic.cls_eq_zero_iff hL
  · beta_reduce
    rw [cl_eq (LB.isLB_linComb hL φ ε), cl_eq hL, CechPic.cls_linComb hL, ofAdd_sum]
    rfl
  · beta_reduce
    rw [cl_eq (LB.isLB_div hM hL), cl_eq hL, cl_eq hM, CechPic.cls_div hM hL]
    rfl

end GlobalTheory.CechPicMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRigLBExtensionDedekind
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

open GlobalTheory.CechPic in
theorem exists_rigLB_extension_dedekind :
    ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ (X' : Scheme.{0}) (π : X' ⟶ G.left) (p : X' ⟶ Sp K), IsPullback π p G.hom (spMap (algebraMap R K)) → ∀ L : LB X', L.IsLB → ∃ L' : RigLB G, LBIso (L'.L.pull π) L := by
  intro R K _ _ _ _ _ A _ hA X' φ p hφ N hN
  have := hA.smooth
  have := hA.proper
  have hR : IsRegularRing R := inferInstance
  have : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth
      hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : GeometricallyIntegral p :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hφ inferInstance
  have : Smooth p := MorphismProperty.of_isPullback (P := @Smooth) hφ inferInstance
  have : IsIntegral X' := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  have h1 : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h2 : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) hφ.flip h1
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) hφ.flip h2
  have hst : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth R A.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  obtain ⟨L, hL, hLN⟩ := exists_lineBundle_extension_of_generalizing A.left X' φ
    (Flat.generalizingMap φ) hst N hN
  let e : Sp R ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 _ := Over.w η[A]
  have hL' : (L.pull (A.hom ≫ e)).IsLB := pull_isLB hL _
  have hM : (LB.div L (L.pull (A.hom ≫ e))).IsLB := LB.isLB_div hL hL'
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen ((LB.div L (L.pull (A.hom ≫ e))).pull e), t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hM e)).1 ?_
    rw [cls_pull hM e (pull_isLB hM e), cls_div hL hL' hM, cls_pull hL (A.hom ≫ e) hL', map_sub, ← pull_comp, ← Category.assoc, he,
      Category.id_comp, sub_self]
  refine ⟨⟨LB.div L (L.pull (A.hom ≫ e)), t, hM, ht⟩, (cls_eq_iff (pull_isLB hM φ) hN).1 ?_⟩
  have h0 : pull (spMap (algebraMap R K) ≫ e) (cls L hL) = 0 :=
    (cls_eq_zero_iff (pull_isLB hL _)).2 (DVR.exists_gen_of_local L hL _ _)
  rw [cls_pull hM φ (pull_isLB hM φ), cls_div hL hL' hM, cls_pull hL (A.hom ≫ e) hL', map_sub, ← pull_comp, ← Category.assoc, hφ.w,
    Category.assoc, pull_comp, h0, map_zero, sub_zero]
  exact (cls_eq_iff (pull_isLB hL φ) hN).2 hLN

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem lamBC_psum_hom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S}
    {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (I : Finset (Fin n)) : ρ (psum G' x I) = psum G (fun i => ρ (x i)) I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact map_one ρ
  | cons k l ih => exact (map_mul ρ _ _).trans (congrArg (ρ (x k) * ·) ih)

theorem lamBC_psum_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ}
    (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T)
    (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) (I : Finset (Fin n)) :
    (psum G' x' I).left ≫ φ = U.left ≫ (psum G x I).left := by
  have e : pushPt h.1.w (psum G' x' I) = U ≫ psum G x I :=
    (lamBC_psum_hom (pushHom h T') x' I).trans ((congrArg (fun z => psum G z I) (funext hx)).trans
      (lamBC_psum_hom (preHom U) x I).symm)
  exact congrArg (fun z => z.left) e

theorem lamEq_baseChange : ∀ (S S' : Scheme.{0}) (s : S' ⟶ S) (X Y A B : Over S) (X' Y' A' B' : Over S') [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] (x : X'.left ⟶ X.left) (y : Y'.left ⟶ Y.left) (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left),
  x ≫ X.hom = X'.hom ≫ s → y ≫ Y.hom = Y'.hom ≫ s → IsGrpPullback A' A s a → IsGrpPullback B' B s b → ∀ (L : LB A.left) (M : LB B.left) (L' : LB A'.left) (M' : LB B'.left), L.IsLB → M.IsLB → L'.IsLB → M'.IsLB → LBIso (L.pull a) L' → LBIso (M.pull b) M' →
  ∀ (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) (f₁' : X' ⟶ A') (f₂' : Y' ⟶ A') (g₁' : X' ⟶ B') (g₂' : Y' ⟶ B'),
  f₁'.left ≫ a = x ≫ f₁.left → f₂'.left ≫ a = y ≫ f₂.left → g₁'.left ≫ b = x ≫ g₁.left → g₂'.left ≫ b = y ≫ g₂.left → LamEq L f₁ f₂ M g₁ g₂ → LamEq L' f₁' f₂' M' g₁' g₂' := by
  intro S S' s X Y A B X' Y' A' B' _ _ _ _ x y a b hx hy hA hB L M L' M' hL hM hL' hM' iL iM
    f₁ f₂ g₁ g₂ f₁' f₂' g₁' g₂' e₁ e₂ e₃ e₄ H
  let p : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ X := Over.homMk ((fst X' Y').left ≫ x) (by
    show ((fst X' Y').left ≫ x) ≫ X.hom = (X' ⊗ Y').hom ≫ s
    rw [Category.assoc, hx, ← Category.assoc, Over.w])
  let q : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ Y := Over.homMk ((snd X' Y').left ≫ y) (by
    show ((snd X' Y').left ≫ y) ≫ Y.hom = (X' ⊗ Y').hom ≫ s
    rw [Category.assoc, hy, ← Category.assoc, Over.w])
  let U : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ X ⊗ Y := lift p q
  have key : ∀ {C : Over S} {C' : Over S'} [GrpObj C] [GrpObj C'] {c : C'.left ⟶ C.left}
      (hC : IsGrpPullback C' C s c) (u : X ⟶ C) (v : Y ⟶ C) (u' : X' ⟶ C') (v' : Y' ⟶ C'),
      u'.left ≫ c = x ≫ u.left → v'.left ≫ c = y ≫ v.left → ∀ I : Finset (Fin 2),
      (psum C' ![fst X' Y' ≫ u', snd X' Y' ≫ v'] I).left ≫ c =
        U.left ≫ (psum C ![fst X Y ≫ u, snd X Y ≫ v] I).left := by
    intro C C' _ _ c hC u v u' v' hu hv I
    refine lamBC_psum_push hC _ _ U (fun i => ?_) I
    fin_cases i
    · show pushPt hC.1.w (fst X' Y' ≫ u') = lift p q ≫ fst X Y ≫ u
      rw [lift_fst_assoc]
      refine Over.OverMorphism.ext ?_
      show ((fst X' Y').left ≫ u'.left) ≫ c = ((fst X' Y').left ≫ x) ≫ u.left
      rw [Category.assoc, hu, Category.assoc]
    · show pushPt hC.1.w (snd X' Y' ≫ v') = lift p q ≫ snd X Y ≫ v
      rw [lift_snd_assoc]
      refine Over.OverMorphism.ext ?_
      show ((snd X' Y').left ≫ v'.left) ≫ c = ((snd X' Y').left ≫ y) ≫ v.left
      rw [Category.assoc, hv, Category.assoc]
  have H₁ : LBIso (cubeLB A' ![fst X' Y' ≫ f₁', snd X' Y' ≫ f₂'] (L.pull a))
      (cubeLB B' ![fst X' Y' ≫ g₁', snd X' Y' ≫ g₂'] (M.pull b)) :=
    LBIso.chartPull
      (chartPullLinComb L a _ _ _ U.left fun I => key hA f₁ f₂ f₁' f₂' e₁ e₂ I.down)
      (chartPullLinComb M b _ _ _ U.left fun I => key hB g₁ g₂ g₁' g₂' e₃ e₄ I.down) H
  have hLa : (L.pull a).IsLB := DVR.linComb_isLB _ hL _ _
  have hMb : (M.pull b).IsLB := DVR.linComb_isLB _ hM _ _
  exact LBIso.trans (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hLa _ _) (DVR.linComb_isLB _ hM' _ _)
    (PowPrimitive.lbIso_linComb iL.symm _ _)
    (LBIso.trans (DVR.linComb_isLB _ hLa _ _) (DVR.linComb_isLB _ hMb _ _) (DVR.linComb_isLB _ hM' _ _) H₁
      (PowPrimitive.lbIso_linComb iM _ _))

end GlobalTheory.CM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIsoOfSurjectivePrincipalPairing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.PairingIso

open GlobalTheory.KerPow

theorem exists_gen_of_lbIso {X : Scheme.{0}} {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId P) (chartPullPull Q (𝟙 X) (𝟙 X) rfl)
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull P (𝟙 X) (𝟙 X) rfl) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem locGen_base {X Y B : Scheme.{0}} {L : LB X} (hL : L.IsLB) (π : Y ⟶ B) (a : B ⟶ X) {b : Y ⟶ X}
    (e : b = π ≫ a) : LocGen L π (fun _ : PUnit => b) (fun _ => 1) := by
  subst e
  intro p
  obtain ⟨i, hi⟩ := exists_chart hL (a p)
  exact ⟨a ⁻¹ᵁ L.U i, hi, ChartRig.exists_gen_pull L _ i hL fun y _ => y.2⟩

theorem eq_one_of_comp_eq_one {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    {L : LB A.left} {M : LB B.left} {Φ : A ⟶ B} (hL : L.IsLB) (hM : M.IsLB) (hK : Out.KTriv A L)
    (h : LamEq M Φ Φ L (𝟙 A) (𝟙 A)) {T : Over S} (x : T ⟶ A) (hx : x ≫ Φ = 1) : x = 1 := by
  have h' : LBIso (cubeLB B ![1, snd T A ≫ Φ] M) (cubeLB A ![fst T A ≫ x, snd T A] L) :=
    LBIso.chartPull
      (PrimNorm.chartSquare M (lift (fst T A ≫ x) (snd T A))
        (by rw [lift_fst_assoc, Category.assoc, hx, MonObj.comp_one]) (by rw [lift_snd_assoc]))
      (PrimNorm.chartSquare L (lift (fst T A ≫ x) (snd T A)) (by simp) (by simp)) h
  have g₁ : ∃ t : LB.Gen (cubeLB B ![1, snd T A ≫ Φ] M), t.IsGen :=
    hasGen_of_trivial hM fun U _ k => (PrimNorm.prod_square_id _ _ k).trans (by simp [PrimNorm.diff₂])
  have g₂ : HasGen L _ _ :=
    exists_gen_of_lbIso (DVR.linComb_isLB _ hM _ _) (DVR.linComb_isLB _ hL _ _) h' g₁
  have g₃ : LocGen L (fst T A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst T A ≫ x, snd T A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩
  have b₁ := locGen_base hL (fst T A).left x.left (b := (fst T A ≫ x).left) rfl
  have b₀ := locGen_base hL (fst T A).left (1 : T ⟶ A).left (b := (1 : T ⊗ A ⟶ A).left)
    (congrArg (fun q : T ⊗ A ⟶ A => q.left) (MonObj.comp_one (fst T A) : fst T A ≫ (1 : T ⟶ A) = 1).symm)
  have b := b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ A ⟶ A).left, (fst T A ≫ x).left]) (ε'' := ![1, -1])
    fun U _ k => by simp [Fin.prod_univ_two]
  refine eq_one_of_locGen hK x (g₃.comb hL b fun U _ k => ?_)
  rw [PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]
  show k ((fst T A ≫ x) * snd T A).left * (k (fst T A ≫ x).left)⁻¹ * (k (snd T A).left)⁻¹ * k (1 : T ⊗ A ⟶ A).left *
    (k (1 : T ⊗ A ⟶ A).left ^ (1 : ℤ) * k (fst T A ≫ x).left ^ (-1 : ℤ))⁻¹ =
    k ((fst T A ≫ x) * snd T A).left ^ (1 : ℤ) * k (snd T A).left ^ (-1 : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem isIso_of_lamEq : ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom Φ → Out.KTriv A L → LamEq M Φ Φ L (𝟙 A) (𝟙 A) → Surjective Φ.left → IsIso Φ := by
  intro S _ A B _ _ L M Φ hA hB hL hM hΦ hK h hs
  have := hA.comm
  have := hB.comm
  have := hA.proper
  have := hB.proper
  have := hB.smooth
  have : Mono Φ := ⟨fun {T} x y e => mul_inv_eq_one.1 (eq_one_of_comp_eq_one hL hM hK h (x * y⁻¹) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]))⟩
  have : Mono Φ.left := inferInstanceAs (Mono ((Over.forget S).map Φ))
  have : IsReduced B.left := GlobalTheory.isReduced_of_smooth_of_isReduced B.hom
  have : IsProper (Φ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper Φ.left := IsProper.of_comp Φ.left B.hom
  have : IsClosedImmersion Φ.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have : IsIso Φ.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map Φ) := ‹_›
  exact isIso_of_reflects_iso Φ (Over.forget _)

end GlobalTheory.CM.PairingIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsPullCubicalOfIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CartTriple

section Charts

variable {X Y : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem chart_of_val (hM : M.IsLB) {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (α : (Z.presheaf.stalk z)ˣ)
    (h : ∀ J, Good M z J → val u r z J = α * val u' r z J) (q : K → M.ι) (hq : r z ∈ LB.wchart M φ q) :
    gm r z (LB.wchart M φ q) (u.s q) = α * gm r z (LB.wchart M φ q) (u'.s q) := by
  obtain ⟨J, hJ⟩ := GlobalTheory.DegPull.exists_good' hM z
  rw [gen_trans hu r z hq (hJ.mem φ r), gen_trans hu' r z hq (hJ.mem φ r), mul_left_comm]
  exact congrArg _ (h J hJ)

end Charts

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left}


omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem exists_rigidified (he : eSec G' ≫ F = f ≫ eSec G) (L : RigLB G) (L' : RigLB G')
    (h : LBIso L'.L (L.L.pull F)) : ∃ w : LB.Iso L'.L (L.L.pull F), PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig f := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨ρ, hρ, H⟩ := GlobalTheory.DegPull.exists_pmaps ((isGen_iff w).1 hw) L.isLB L'.isLB (K := PUnit)
    (φ' := fun _ => eSec G') (φ := fun _ => eSec G) (ε := fun _ => 1) f (fun _ => he) L.rig L.rigGen
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio L'.isLB (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1)
    hρ L'.rigGen
  let b : Γ(G'.left, ⊤)ˣ := pullU G'.hom ⊤ a
  refine ⟨GlobalTheory.UU.scaleGen b w, (isGen_iff _).1 (GlobalTheory.UU.scaleGen_isGen b hw), fun Z r z p q hp hq => ?_⟩
  have hs : eSec G' ≫ G'.hom = 𝟙 _ := Over.w η[G']
  have e : gw (GlobalTheory.UU.scaleGen b w) (r ≫ eSec G') z (p PUnit.unit) (q PUnit.unit) =
      gm r z ⊤ a * gw w (r ≫ eSec G') z (p PUnit.unit) (q PUnit.unit) := by
    have hm : (r ≫ eSec G') z ∈ (L.L.pull F).U (fun _ => p PUnit.unit) ⊓ L'.L.U (q PUnit.unit) :=
      ⟨mem_pull.2 (hp PUnit.unit), hq PUnit.unit⟩
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z le_top hm b).trans
      ((gm_pull (r ≫ eSec G') G'.hom z ⊤ trivial a).trans ?_)) rfl)
    rw [Category.assoc, hs]
    exact congrArg (fun g => gm g z ⊤ a) (Category.comp_id r)
  have e₂ := chart_of_val L'.isLB (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) hρ L'.rigGen r z _
    (ha Z r z) q (Set.mem_iInter.2 hq)
  refine (H Z r z p q hp hq).trans ((congrArg (_ * ·) e₂).trans ?_)
  rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, ← _root_.mul_assoc]
  exact congrArg (· * _) ((mul_comm _ _).trans e.symm)

theorem val_origin (gp : IsGrpPullback G' G f F) {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L)
    {w : LB.Iso L'.L (L.L.pull F)} {t : LB.Gen (LB.LinComb L'.L (thφ G' (x3 G')) thε)}
    (H : PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε t c.t (cubeMapOf gp).F3) (T : Over S') (y : T.left) (J')
    (hJ' : Good L'.L y J') : val t (lift (1 : T ⟶ G') (lift 1 1)).left y J' = 1 := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨J, hJ⟩ := GlobalTheory.DegPull.exists_good' L.isLB y
  have q : ∀ a : T ⟶ G', (lift a (lift a a)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp T a) (lift (pushHom gp T a) (pushHom gp T a))).left := fun a => hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  have e := GlobalTheory.DegPull.pmaps_val hψ H (lift (1 : T ⟶ G') (lift 1 1)).left y hJ hJ'
  rw [q, map_one] at e
  have p := prod_cub (1 : T ⟶ G') 1 1 (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [_root_.mul_one, _root_.mul_one] at p
  have face : cubV c (T := Over.mk (T.hom ≫ f)) y J 1 1 1 = 1 := by
    have e := val_corr hJ (c.face 0) (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left
    rw [val_one] at e
    refine (Eq.trans ?_ (val_cub c (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1) hJ (pzero G _) (x2 G 0) (x2 G 1)).symm).trans e
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have e' := face.symm.trans
    (e.trans (congrArg₂ (· * ·) p rfl))
  have alg : ∀ {U : Type} [CommGroup U] (a v : U), 1 = a * a⁻¹ * a⁻¹ * a⁻¹ * a * a * a * a⁻¹ * v → v = 1 :=
    fun a v h => by simpa using h.symm
  exact alg _ _ e'

theorem pmaps_cube (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G') (gp : IsGrpPullback G' G f F) {L : RigLB G}
    {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w) :
    PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (cubeMapOf gp).F3 := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨t, ht, H⟩ := GlobalTheory.DegPull.exists_pmaps hw L.isLB L'.isLB (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  have face (y : (𝟙_ (Over S')).left) (J') (hJ' : Good L'.L y J') :
      cubV c' y J' (1 : 𝟙_ (Over S') ⟶ G') 1 1 = 1 := by
    have e := val_corr hJ' (c'.face 0) (lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
    rw [val_one] at e
    refine (Eq.trans ?_ (val_cub c' (lift (1 : 𝟙_ (Over S') ⟶ G') 1) hJ' (pzero G' _) (x2 G' 0) (x2 G' 1)).symm).trans e
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have key := gen_unique L'.isLB (φ := thφ G' (x3 G')) (ε := thε) (G3 G').hom
    (lift (1 : 𝟙_ (Over S') ⟶ G') (lift 1 1)).left (Over.w _) (GlobalTheory.UU.surjective_cube hG hA) ht c'.isGen
    (fun y J' hJ' => (val_origin gp c H (𝟙_ (Over S')) y J' hJ').trans (face y J' hJ').symm)
  intro Z r z p q hp hq
  have e := (chart_of_val L'.isLB (φ := thφ G' (x3 G')) (ε := thε) ht c'.isGen r z 1
    (fun J hJ => (key Z r z J hJ).trans (_root_.one_mul _).symm) q (Set.mem_iInter.2 hq)).trans (_root_.one_mul _)
  exact (H Z r z p q hp hq).trans (congrArg₂ (· * ·) rfl e)

theorem isPullCubical_of_iso (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G') (gp : IsGrpPullback G' G f F)
    {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') (h : LBIso L'.L (L.L.pull F)) :
    (cubeMapOf gp).IsPullCubical c' c := by
  obtain ⟨w, hw, hr⟩ := exists_rigidified (cubeMapOf gp).e_comm L L' h
  exact (isPullCubical_iff _ c c').2 ⟨w, hw, hr, pmaps_cube hG hA gp c c' hw⟩

theorem exists_tripleMap : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (t : SAB H S) (φ : t'.G.left ⟶ t.G.left), IsAbelianScheme t'.G → IsGrpPullback t'.G t.G f φ → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull φ) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hG E _ _ _ H S S' f t' t φ hA gp hact h
  exact ⟨⟨cubeMapOf gp, gp, rfl, hact, isPullCubical_of_iso hG hA gp t.cub t'.cub h⟩, rfl⟩

end GlobalTheory.CartTriple
end

