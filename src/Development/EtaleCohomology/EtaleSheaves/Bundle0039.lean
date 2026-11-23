module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0022
public import Development.EtaleCohomology.EtaleSheaves.Bundle0003
public import Development.EtaleCohomology.EtaleSheaves.Bundle0017
public import Development.EtaleCohomology.EtaleSheaves.Bundle0008
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.EtaleCohomology.TateTwists.Bundle0010
public import Development.EtaleCohomology.TateTwists.Bundle0008
public import Development.EtaleCohomology.TateTwists.Bundle0025
public import Development.EtaleCohomology.EtaleSheaves.Bundle0028
public import Development.EtaleCohomology.EtaleSheaves.Bundle0007
public import Development.EtaleCohomology.EtaleSheaves.Bundle0026

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafEvMkPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafEvMkPf

variable {R : Type} [CommRing R]

def preLift {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.ofHom (Finsupp.lift (F.obj.obj U) (ULift.{1} R) (ULift.{1} (P.obj U)) (fun y => a U.unop y.down))
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro y'
    obtain ⟨y⟩ := y'
    have := ha V.unop U.unop g.unop y
    simp only [Sec.res, Quiver.Hom.op_unop, op_unop] at this
    dsimp [freeP]
    change (Finsupp.lift (F.obj.obj V) (ULift.{1} R) (ULift.{1} (P.obj V)) (fun y => a V.unop y.down))
        (Finsupp.mapDomain (fun x : ULift.{1} (P.obj U) => ULift.up (P.map g x.down)) (Finsupp.single (ULift.up y) 1)) =
      F.obj.map g ((Finsupp.lift (F.obj.obj U) (ULift.{1} R) (ULift.{1} (P.obj U)) (fun y => a U.unop y.down)) (Finsupp.single (ULift.up y) 1))
    rw [Finsupp.mapDomain_single, Finsupp.lift_apply, Finsupp.lift_apply, Finsupp.sum_single_index, Finsupp.sum_single_index]
    · simpa using this.symm
    all_goals simp

theorem preLift_app {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U) (ha) (U : Scheme.{0})
    (x : P.obj (op U)) : ((preLift a ha).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = a U x := by
  show (Finsupp.lift (F.obj.obj (op U)) (ULift.{1} R) (ULift.{1} (P.obj (op U))) (fun y => a U y.down)) (Finsupp.single (ULift.up x) 1) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp

def shLift {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (free R).obj P ⟶ F :=
  ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology (preLift a ha) F.property)

theorem shLift_gen {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U) (ha) (U : Scheme.{0})
    (x : P.obj (op U)) : ((shLift a ha).hom.app (op U)).hom (freeGen R P U x) = a U x := by
  unfold freeGen
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyLift Scheme.etaleTopology (preLift a ha) F.property).app (op U)).hom _ = _
  rw [toSheafify_sheafifyLift]
  exact preLift_app a ha U x

variable {E : Spc} {I : Cx R} {n : ℤ}

def comp (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : ((chains R).obj E).X (-(p : ℤ)) ⟶ I.X s :=
  (chainsXIso R E p).hom ≫ shLift (P := E.obj (op (SimplexCategory.mk p))) (a p s h) (fun V U g x => ha p s h V U g x)

theorem comp_key (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p q : ℕ) (hq : q = p) (s : ℤ) (h : -(p : ℤ) + n = s) (h' : -(q : ℤ) + n = s)
    (e : ((chains R).obj E).X (-(p : ℤ)) = ((chains R).obj E).X (-(q : ℤ))) :
    (chainsXIso R E p).inv ≫ eqToHom e ≫ comp a ha q s h' =
      shLift (P := E.obj (op (SimplexCategory.mk p))) (a p s h) (fun V U g x => ha p s h V U g x) := by
  subst hq
  simp [comp]

theorem LeafEvMk_of : LateralTheory.E.ChernClassExistence.LeafEvMk := by
  intro R _ E I n a ha
  refine ⟨Cochain.mk fun i j hij => if hi : i ≤ 0 then
      eqToHom (congrArg (fun k => ((chains R).obj E).X k) (by omega : i = -(((-i).toNat : ℕ) : ℤ))) ≫
        comp a ha ((-i).toNat) j (by omega) else 0, ?_⟩
  intro p s h U x
  unfold ev
  rw [Cochain.mk_v, dite_eq_left (by omega), comp_key a ha p _ (by omega) s h]
  exact shLift_gen _ _ U x

end LateralTheory.E.LeafEvMkPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafMVVanishPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafMVVanishPf

theorem mvSpc : LateralTheory.E.MVPf.MVSpc :=
  LateralTheory.E.MVPf.MVSpc_of (fun R _ _ _ _ f g h => LateralTheory.Fin.EtaleMayerVietorisChainsShortExact.intersectionNumber_baseChange R f g h)

end LateralTheory.E.LeafMVVanishPf

namespace LateralTheory.E.E8
open LateralTheory.E.LeafMVVanishPf

end LateralTheory.E.E8
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPairExtPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafPairExtPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitPairGPf

def LeafActSgl : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) L, IsAct q i L →
  ∃ lam : Pair (sgl (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      lam.mul U 0 t t (zero_add t) (Sec.map (sglι (tw q 0)) a) b = L U t a b

def LeafExtAlongAug : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (lam : Pair (sgl (tw q 0)) (res _ (tw q i)) (res _ (tw q i))),
  ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (x : Sec ((sgl (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      ν.mul U 0 t t (zero_add t) (Sec.map ((resAug (tw q 0)).f 0) x) b = lam.mul U 0 t t (zero_add t) x b

section Act
variable {q : ℕ} {i : ℤ}

def actPair (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) : Sec ((sgl (tw q 0)).X s) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)]
      Sec ((res _ (tw q i)).X w) U :=
  if hs : s = 0 then
    ((L U t).compl₁₂ (((HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (tw q 0) s hs).hom.hom.app (op U)).hom)
      LinearMap.id).compr₂ ((((res _ (tw q i)).XIsoOfEq (show t = w by omega)).hom.hom.app (op U)).hom)
  else 0

theorem actPair_pos (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (t : ℤ)
    (a : Sec ((sgl (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U) :
    actPair L U 0 t t (zero_add t) a b =
      L U t (Sec.map (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (tw q 0) 0 rfl).hom a) b := by
  simp [actPair, HomologicalComplex.XIsoOfEq_rfl]

theorem actPair_neg (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) (hs : s ≠ 0) : actPair L U s t w h = 0 := by
  simp [actPair, hs]

end Act

theorem LeafPairExt_of (h1 : LeafActSgl) (h2 : LeafExtAlongAug) : LeafPairExt := by
  intro q _ i L hL
  obtain ⟨lam, hlam⟩ := h1 q i L hL
  obtain ⟨ν, hν⟩ := h2 q i lam
  refine ⟨ν, fun U t a b => ?_⟩
  have e : Sec.map (resι _ (tw q 0)) a = Sec.map ((resAug (tw q 0)).f 0) (Sec.map (sglι (tw q 0)) a) := rfl
  rw [e, hν, hlam]

theorem etale_twist_action_induces_single_complex_pairing_holds : LeafActSgl := by
  intro q _ i L hL
  refine ⟨⟨actPair L, ?_, ?_⟩, ?_⟩
  · intro V U g s t w h a b
    by_cases hs : s = 0
    · subst hs
      obtain rfl : w = t := by omega
      rw [actPair_pos, actPair_pos, hL.1]
      congr 2
    · rw [actPair_neg L U s t w h hs, actPair_neg L V s t w h hs]
      simp
  · intro U s t w h a b
    have hd : (sgl (tw q 0)).d s (s + 1) = 0 := by simp
    rw [hd]
    have h0 : Sec.map (0 : (sgl (tw q 0)).X s ⟶ (sgl (tw q 0)).X (s + 1)) a = 0 := rfl
    rw [h0, map_zero, LinearMap.zero_apply, zero_add]
    by_cases hs : s = 0
    · subst hs
      obtain rfl : w = t := by omega
      rw [actPair_pos, actPair_pos, Int.negOnePow_zero, one_smul]
      exact hL.2 U _ _ b
    · rw [actPair_neg L U s t w h hs, actPair_neg L U s (t + 1) (w + 1) (by omega) hs]
      simp
  · intro U t a b
    change actPair L U 0 t t (zero_add t) _ b = _
    rw [actPair_pos]
    congr 1

theorem LeafPairExt_of' (h2 : LeafExtAlongAug) : LeafPairExt := LeafPairExt_of etale_twist_action_induces_single_complex_pairing_holds h2

end LateralTheory.E.LeafPairExtPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadVCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafSpreadVCut

def LeafDescendV : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type) [Field Ω]
    [Algebra k Ω] {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
      IsProper q ∧ SmoothOfRelativeDimension 1 q ∧ IsProper (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
      IsProper (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
      f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) ∧
      IrreducibleSpace D0 ∧ topologicalKrullDim D0 ≤ ringKrullDim R + 1 ∧
      IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafCloseB : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (B : Scheme.{0}) (b : B ⟶ Sp k) (ι : Sp A ⟶ B), IsIntegral B ∧ IsProper b ∧
    IsOpenImmersion ι ∧ ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A)) ∧ topologicalKrullDim B ≤ ringKrullDim A

lemma succ_le_of_lt {a x : WithBot ℕ∞} (h : a < x) : a + 1 ≤ x ∧ a + 1 < ⊤ := by
  induction a with
  | bot => exact ⟨by simp, by simp⟩
  | coe n =>
    induction x with
    | bot => exact absurd h (not_lt_bot)
    | coe m =>
      have h' : n < m := WithBot.coe_lt_coe.mp h
      have hn : n ≠ ⊤ := ne_top_of_lt h'
      refine ⟨?_, ?_⟩
      · rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
        exact Order.add_one_le_of_lt h'
      · rw [← WithBot.coe_one, ← WithBot.coe_add]
        exact WithBot.coe_lt_coe.mpr (lt_top_iff_ne_top.mpr (by
          lift n to ℕ using hn
          exact ENat.natCast_ne_top (n + 1)))

end LateralTheory.E.LeafSpreadVCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTruncPf
section
noncomputable section
open CategoryTheory Limits Pretriangulated Triangulated

namespace LateralTheory.E.LeafTruncPf

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

lemma mono_H_ι (Y : DerivedCategory C) (n : ℤ) :
    Mono ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app Y)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished (n + 1) Y
  have := (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (n - 1) n (by lia)).2
    (IsZero.eq_of_src (DerivedCategory.isZero_of_isGE _ (n + 1) (n - 1) (by lia)) _ _)
  exact this

lemma epi_H_π (X : DerivedCategory C) (n : ℤ) :
    Epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app X)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished n X
  have := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT n (n + 1) (by lia)).2
    (IsZero.eq_of_tgt (DerivedCategory.isZero_of_isLE _ (n - 1) (n + 1) (by lia)) _ _)
  exact this

lemma lift_LT {X Y : DerivedCategory C} (n : ℤ) (φ : X ⟶ Y)
    (h : φ ≫ (DerivedCategory.TStructure.t.truncGEπ n).app Y = 0) :
    ∃ ψ : X ⟶ (DerivedCategory.TStructure.t.truncLT n).obj Y,
      φ = ψ ≫ (DerivedCategory.TStructure.t.truncLTι n).app Y :=
  Triangle.coyoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n Y) φ h

lemma desc_GE {X Y : DerivedCategory C} (n : ℤ) (φ : X ⟶ Y)
    (h : (DerivedCategory.TStructure.t.truncLTι n).app X ≫ φ = 0) :
    ∃ ψ : (DerivedCategory.TStructure.t.truncGE n).obj X ⟶ Y,
      φ = (DerivedCategory.TStructure.t.truncGEπ n).app X ≫ ψ :=
  Triangle.yoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n X) φ h

lemma heart_zero {X Y : DerivedCategory C} (n : ℤ) [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    (χ : X ⟶ Y) (hχ : (DerivedCategory.homologyFunctor C n).map χ = 0) : χ = 0 := by
  obtain ⟨A, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  obtain ⟨B, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y n
  obtain ⟨a, ha⟩ := (DerivedCategory.singleFunctor C n).map_surjective (eX.inv ≫ χ ≫ eY.hom)
  have ha0 : a = 0 := by
    have eq := NatIso.naturality_1 (DerivedCategory.singleFunctorCompHomologyFunctorIso C n) a
    dsimp at eq
    rw [← eq, ha]
    simp [hχ]
  have : χ = eX.hom ≫ (eX.inv ≫ χ ≫ eY.hom) ≫ eY.inv := by simp
  rw [this, ← ha, ha0, Functor.map_zero]
  simp

lemma zero_of_H {X Y : DerivedCategory C} (n : ℤ) [X.IsLE n] [Y.IsGE n] (φ : X ⟶ Y)
    (hφ : (DerivedCategory.homologyFunctor C n).map φ = 0) : φ = 0 := by
  have h1 : φ ≫ (DerivedCategory.TStructure.t.truncGEπ (n + 1)).app Y = 0 :=
    DerivedCategory.TStructure.t.zero _ n (n + 1)
  obtain ⟨ψ, hψ⟩ := lift_LT (n + 1) φ h1
  have h2 : (DerivedCategory.TStructure.t.truncLTι n).app X ≫ ψ = 0 :=
    DerivedCategory.TStructure.t.zero _ (n - 1) n
  obtain ⟨χ, hχ⟩ := desc_GE n ψ h2
  have hHχ : (DerivedCategory.homologyFunctor C n).map χ = 0 := by
    have := mono_H_ι Y n
    have := epi_H_π X n
    rw [hψ, hχ, Functor.map_comp, Functor.map_comp] at hφ
    rw [← cancel_epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app X)),
      ← cancel_mono ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app Y))]
    simpa using hφ
  have : χ = 0 := heart_zero n χ hHχ
  rw [hψ, hχ, this]
  simp

end LateralTheory.E.LeafTruncPf

open LateralTheory.E.LeafTruncPf in
theorem LateralTheory.E.LeafGhostRelCut.LeafTrunc_of : LateralTheory.E.LeafGhostRelCut.LeafTrunc := by
  intro A _ _ _ K0 K1 K2 L f g ℓ hK0 hf hg hK2 hL hℓ
  have : K0.IsLE 2 := (DerivedCategory.isLE_iff K0 2).2 hK0
  have : K2.IsGE 0 := (DerivedCategory.isGE_iff K2 0).2 hK2
  have : L.IsLE 0 := (DerivedCategory.isLE_iff L 0).2 (fun i hi => hL i (by lia))
  have : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLT 2).obj K1) 1 :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _
  have hP : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLT 1).obj K2) 0 :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _
  have e1 : f ≫ (DerivedCategory.TStructure.t.truncGEπ 2).app K1 = 0 :=
    zero_of_H 2 _ (by simp [Functor.map_comp, hf])
  obtain ⟨f', hf'⟩ := lift_LT 2 f e1
  have e2 : ((DerivedCategory.TStructure.t.truncLTι 2).app K1 ≫ g) ≫
      (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0 :=
    zero_of_H 1 _ (by simp [Functor.map_comp, hg])
  obtain ⟨w, hw⟩ := lift_LT 1 _ e2
  have e3 : ℓ ≫ (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0 :=
    DerivedCategory.TStructure.t.zero _ 0 1
  obtain ⟨ℓ', hℓ'⟩ := lift_LT 1 ℓ e3
  have hiso : IsIso ℓ' := by
    rw [DerivedCategory.isIso_iff]
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · have hm0 := mono_H_ι K2 0
      rw [zero_add] at hm0
      have hc : IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ' ≫
          (DerivedCategory.homologyFunctor A 0).map
            ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) := by
        rw [← Functor.map_comp, ← hℓ']; exact hℓ
      have : Epi ((DerivedCategory.homologyFunctor A 0).map
          ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) :=
        epi_of_epi ((DerivedCategory.homologyFunctor A 0).map ℓ') _
      have : IsIso ((DerivedCategory.homologyFunctor A 0).map
          ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) := isIso_of_mono_of_epi _
      exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor A 0).map
        ((DerivedCategory.TStructure.t.truncLTι 1).app K2))
    · have hZ : IsZero ((DerivedCategory.homologyFunctor A m).obj
          ((DerivedCategory.TStructure.t.truncLT 1).obj K2)) := by
        rcases lt_or_gt_of_ne hm with h | h
        · exact DerivedCategory.isZero_of_isGE _ 0 m h
        · exact DerivedCategory.isZero_of_isLE _ 0 m h
      exact ⟨⟨0, (hL m hm).eq_of_src _ _, hZ.eq_of_src _ _⟩⟩
  refine ⟨f' ≫ w ≫ inv ℓ', ?_⟩
  rw [hf', hℓ']
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, hw]

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwSecPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafTwSecPf

def ρ {B : Type} [CommRing B] (U : Over (Spec (CommRingCat.of B))) : B →+* Γ(U.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ U.hom.appTop).hom

abbrev Pr (q : ℕ) (k : ℤ) (X : Scheme.{0}) : (Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) :=
  (Over.forget X).op ⋙ (Scheme.Γ ⋙ twF q k)

abbrev Cst (q : ℕ) (X : Scheme.{0}) : (Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) :=
  (Functor.const _).obj (ModuleCat.of _ (ULift.{1} (ZMod q)))

def gen {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) (U : Over (Spec (CommRingCat.of B))) :
    (Pr q k _).obj (op U) :=
  Submodule.Quotient.mk (Finsupp.single (Prim.map (ρ U) ζ) 1)

theorem gen_map {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) {U V : Over (Spec (CommRingCat.of B))}
    (f : V ⟶ U) : ((Pr q k _).map f.op).hom (gen ζ k U) = gen ζ k V := by
  change Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single _ _)) = _
  rw [Finsupp.mapDomain_single]
  have h : Prim.map (Scheme.Γ.map f.left.op).hom (Prim.map (ρ U) ζ) = Prim.map (ρ V) ζ := by
    apply Subtype.ext
    change (Scheme.Γ.map f.left.op).hom (ρ U ζ.1) = ρ V ζ.1
    simp only [ρ]
    rw [← Over.w f]
    first | rfl | simp [Scheme.Hom.comp_appTop] | simp
  exact congrArg (fun z => Submodule.Quotient.mk (p := twRel q k _) (Finsupp.single z (1 : ULift.{1} (ZMod q)))) h

def cmap {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) : Cst q _ ⟶ Pr q k (Spec (CommRingCat.of B)) where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (gen ζ k U.unop))
  naturality := by
    intro U V f
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (LinearMap.toSpanSingleton (ULift.{1} (ZMod q)) _ (gen ζ k V.unop)) (1 : ULift.{1} (ZMod q)) =
      ((Pr q k _).map f).hom ((LinearMap.toSpanSingleton (ULift.{1} (ZMod q)) _ (gen ζ k U.unop)) (1 : ULift.{1} (ZMod q)))
    simp only [LinearMap.toSpanSingleton_apply, one_smul]
    exact (gen_map ζ k f.unop).symm

def LeafTwLB : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  IsIso ((presheafToSheaf (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (ModuleCat.{1} (ULift.{1} (ZMod q)))).map
    (cmap ζ k))

theorem LeafTwSec_of (h : LeafTwLB) : LateralTheory.E.LeafTwistPf.LeafTwSec := by
  intro q _ B _ ζ i j
  let K := (Over.forget (Spec (CommRingCat.of B))).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{1} (ULift.{1} (ZMod q))) (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) Scheme.etaleTopology
  haveI := h q B ζ i
  haveI := h q B ζ j
  let Φ := (K.app (Scheme.Γ ⋙ twF q i)).symm ≪≫ (asIso ((presheafToSheaf _ _).map (cmap ζ i))).symm ≪≫
    asIso ((presheafToSheaf _ _).map (cmap ζ j)) ≪≫ K.app (Scheme.Γ ⋙ twF q j)
  let Ψ := (sheafToPresheaf _ _).mapIso Φ
  refine ⟨fun U x => (Ψ.app (op (Over.mk x))).toLinearEquiv, ?_⟩
  intro V U g x s
  have := congrArg (fun f => f.hom s) (Ψ.hom.naturality (Over.homMk g : Over.mk (g ≫ x) ⟶ Over.mk x).op)
  exact this

def LeafTwSurj : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (cmap ζ k)

def LeafTwInj : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  Presheaf.IsLocallyInjective (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (cmap ζ k)

theorem LeafTwLB_of (hI : LeafTwInj) (hS : LeafTwSurj) : LeafTwLB := by
  intro q _ B _ ζ k
  haveI := hI q B ζ k
  haveI := hS q B ζ k
  exact (GrothendieckTopology.W_iff _ _).1 (GrothendieckTopology.W_of_isLocallyBijective _ _)

theorem LeafTwSec_of' (hI : LeafTwInj) (hS : LeafTwSurj) : LateralTheory.E.LeafTwistPf.LeafTwSec :=
  LeafTwSec_of (LeafTwLB_of hI hS)

end LateralTheory.E.LeafTwSecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitActPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitActPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitPairGPf

def LeafActSheaf : Prop := ∀ (q : ℕ) [NeZero q], ∃ L : ∀ (F : Shv (ZMod q)) (U : Scheme.{0}),
    Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)] Sec F U →ₗ[ULift.{1} (ZMod q)] Sec F U,
  (∀ (F : Shv (ZMod q)) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec (tw q 0) U) (b : Sec F U),
      Sec.res g (L F U a b) = L F V (Sec.res g a) (Sec.res g b)) ∧
  (∀ {F G : Shv (ZMod q)} (φ : F ⟶ G) (U : Scheme.{0}) (a : Sec (tw q 0) U) (b : Sec F U),
      Sec.map φ (L F U a b) = L G U a (Sec.map φ b)) ∧
  ∀ (F : Shv (ZMod q)) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (b : Sec F U), L F U (twGen 0 ζ) b = b

theorem LeafUnitAct_of (h : LeafActSheaf) : LeafUnitAct := by
  intro q _ i
  obtain ⟨L, hU, hF, hζ⟩ := h q
  refine ⟨fun U t => L ((res _ (tw q i)).X t) U, ⟨fun g t a b => hU _ g a b, fun U t a b => hF _ U a b⟩,
    fun U t ζ b => hζ _ U ζ b⟩

end LateralTheory.E.LeafUnitActPf
end
end

