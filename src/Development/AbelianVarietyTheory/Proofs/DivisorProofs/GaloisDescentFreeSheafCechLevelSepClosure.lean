module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

open Simplicial

namespace GlobalTheory.EtC.GalSec

theorem freePresheaf_map_freeMk {R : Type} [CommRing R] (P : PSh) {U V : Scheme.{0}ᵒᵖ} (g : U ⟶ V) (x : P.obj U) :
    (((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g x)) := by
  exact ModuleCat.free_map_apply (uliftFunctor.{1, 0}.map (P.map g)) (ULift.up x)

theorem val_nat {R : Type} [CommRing R] {P : PSh} {F : Shv R} (s : (free R).obj P ⟶ F) {U V : Scheme.{0}} (g : V ⟶ U)
    (x : P.obj (op U)) : val s V (P.map g.op x) = Sec.res g (val s U x) := by
  unfold val freeGen
  calc _ = (s.hom.app (op V)).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
        ((((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)))) := by
          rw [freePresheaf_map_freeMk]
    _ = _ := ?_
  have e1 := congrArg (fun φ => φ.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  have e2 := congrArg
    (fun φ => φ.hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U)).hom (ModuleCat.freeMk (ULift.up x))))
    (s.hom.naturality g.op)
  simp only [ModuleCat.hom_comp] at e1 e2
  exact (congrArg (fun z => (s.hom.app (op V)).hom z) e1).trans e2

theorem cechPt_nat {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U V : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X)
    (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h) =
      cechPt f k (g ≫ x) (fun i => g ≫ y i) (fun i => by rw [Category.assoc, h i]) := by
  unfold cechPt
  have hL : yoneda.map g ≫ WidePullback.lift (yoneda.map x) (fun i => yoneda.map (y i))
      (fun i => by rw [← Functor.map_comp, h i]) =
      WidePullback.lift (yoneda.map (g ≫ x)) (fun i => yoneda.map (g ≫ y i))
      (fun i => by rw [← Functor.map_comp, Category.assoc, h i]) := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, WidePullback.lift_π, WidePullback.lift_π, Functor.map_comp]
    · rw [Category.assoc, WidePullback.lift_base, WidePullback.lift_base, Functor.map_comp]
  erw [← NatTrans.naturality_apply]
  rw [← hL]
  simp
  rfl

theorem cechPt_congr {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U : Scheme.{0}} {x x' : U ⟶ X}
    {y y' : Fin (k + 1) → (U ⟶ Y)} (h : ∀ i, y i ≫ f = x) (h' : ∀ i, y' i ≫ f = x') (hx : x = x') (hy : y = y') :
    cechPt f k x y h = cechPt f k x' y' h' := by
  subst hx hy
  rfl

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {U V W : Scheme.{0}} (a : W ⟶ V) (b : V ⟶ U) (t : Sec F U) :
    Sec.res (a ≫ b) t = Sec.res a (Sec.res b t) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (t : Sec F U) : Sec.res (𝟙 U) t = t := by
  simp [Sec.res]

end GlobalTheory.EtC.GalSec

namespace GlobalTheory.EtC.GalSec

theorem ofHom_one (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] :
    CommRingCat.ofHom (((1 : Ω ≃ₐ[K] Ω) : Ω ≃ₐ[K] Ω) : Ω →+* Ω) = 𝟙 (CommRingCat.of Ω) := by
  ext a
  rfl

theorem tailG_cons_one (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (k : ℕ) (g : Fin k → (Ω ≃ₐ[K] Ω)) :
    tailG K Ω k (Fin.cons 1 g) = g := by
  funext i
  simp [tailG]

theorem mul_cons_tailG (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) :
    (fun i => σ 0 * (Fin.cons 1 (tailG K Ω k σ) : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) i) = σ := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp [tailG]

theorem continuous_tailG (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (k : ℕ) : Continuous (tailG K Ω k) := by
  unfold tailG
  exact continuous_pi fun i => ((continuous_apply 0).inv).mul (continuous_apply i.succ)

private theorem gal_sec_of_lemma {R : Type} [CommRing R] {F : Shv R} (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (k : ℕ)
    (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F)
    (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) :
    val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) =
      Sec.res (Spec.map (CommRingCat.ofHom ((σ 0 : Ω ≃ₐ[K] Ω) : Ω →+* Ω)))
        (Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (tailG K Ω k σ))))
          (val s (Spec (CommRingCat.of (LCRing K Ω k)))
            (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (baseHom K Ω k)))
              (fun i => Spec.map (CommRingCat.ofHom (legHom K Ω k i)))
              (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp])))) := by
  have hb : (ptHom K Ω k σ).comp (baseHom K Ω k) = algebraMap K Ω := by
    rw [← legHom_comp K Ω k 0, ← RingHom.comp_assoc, ptHom_legHom]
    exact RingHom.ext fun a => (σ 0).commutes a
  rw [← res_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show ((σ 0 : Ω ≃ₐ[K] Ω) : Ω →+* Ω).comp (LocallyConstant.evalRingHom (tailG K Ω k σ)) = ptHom K Ω k σ from rfl,
    ← val_nat, cechPt_nat]
  congr 1
  apply cechPt_congr
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]
  · funext i
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ptHom_legHom]

theorem gal_sec_of (TopsChoicePartA : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (B : Type) [CommRing B] (g : Fin (k + 1) → (Ω →+* B)) (c : K →+* B), (∀ i, (g i).comp (algebraMap K Ω) = c) → ∃! u : GlobalTheory.EtC.GalSec.LCRing K Ω k →+* B, u.comp (GlobalTheory.EtC.GalSec.baseHom K Ω k) = c ∧ ∀ i, u.comp (GlobalTheory.EtC.GalSec.legHom K Ω k i) = g i) (TopsChoiceSecondBound : ∀ (n : ℕ) (C D A : Type) [CommRing C] [CommRing D] [CommRing A] (a : C →+* D) (b : C →+* A) (l : Fin n → (D →+* A)) (hl : ∀ i, (l i).comp a = b), (∀ (B : Type) [CommRing B] (g : Fin n → (D →+* B)) (c : C →+* B), (∀ i, (g i).comp a = c) → ∃! u : A →+* B, u.comp b = c ∧ ∀ i, u.comp (l i) = g i) → Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) (fun i => Spec.map (CommRingCat.ofHom (l i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i])))) (S2 : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (B : Type) [CommRing B], (∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), IsLocallyConstant (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t)) ∧ Function.Injective (fun (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) (x : X) => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t) ∧ ∀ ψ : X → Sec F (Spec (CommRingCat.of B)), IsLocallyConstant ψ → ∃ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = ψ x) (S3 : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Sec F (Spec (CommRingCat.of Ω))), IsLocallyConstant (fun τ : Ω ≃ₐ[K] Ω => Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x)) : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ), Function.Injective (fun (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x))) ∧ (∀ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, IsLocallyConstant (fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)))) ∧ ∀ φ : (Fin (k + 1) → (Ω ≃ₐ[K] Ω)) → Sec F (Spec (CommRingCat.of Ω)), IsLocallyConstant φ → (∀ (τ : Ω ≃ₐ[K] Ω) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)), φ (fun i => τ * σ i) = Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) (φ σ)) → ∃ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, ∀ σ, val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) = φ σ := by
  intro R _ F hF K Ω _ _ _ _ k
  obtain ⟨hlim⟩ := TopsChoiceSecondBound (k + 1) K Ω (LCRing K Ω k) (algebraMap K Ω) (baseHom K Ω k) (legHom K Ω k)
    (legHom_comp K Ω k) (TopsChoicePartA K Ω k)
  let f := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let Z := Spec (CommRingCat.of (LCRing K Ω k))
  let x : Z ⟶ _ := Spec.map (CommRingCat.ofHom (baseHom K Ω k))
  let y (i : Fin (k + 1)) : Z ⟶ _ := Spec.map (CommRingCat.ofHom (legHom K Ω k i))
  have h (i : Fin (k + 1)) : y i ≫ f = x := by
    dsimp [y, f, x]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp]
  let P := (cech f).obj (op ⦋k⦌)
  let p : P.obj (op Z) := cechPt f k x y h
  have hbij : Function.Bijective (fun s : (free R).obj P ⟶ F => val s Z p) := by
    have e (U : Scheme.{0}) : Function.Bijective (fun g : U ⟶ Z => P.map g.op p) := by
      have hb := CechPts.bij f k x y h hlim U
      constructor
      · intro g g' hg
        apply hb.1
        exact (CechPts.map_cechPt f k x y h g).symm.trans
          (hg.trans (CechPts.map_cechPt f k x y h g'))
      · intro v
        obtain ⟨g, hg⟩ := hb.2 v
        exact ⟨g, (CechPts.map_cechPt f k x y h g).trans hg⟩
    have hval (s : (free R).obj P ⟶ F) (U : Scheme.{0}) (v : P.obj (op U)) :
        val s U v = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom).app (op U)).hom
          (ModuleCat.freeMk (ULift.up v)) := rfl
    constructor
    · intro s s' hs
      apply Sheaf.hom_ext
      apply sheafify_hom_ext _ _ _ F.property
      apply NatTrans.ext
      funext U
      apply ModuleCat.free_hom_ext
      rintro ⟨v⟩
      obtain ⟨g, rfl⟩ := (e U.unop).2 v
      change val s U.unop (P.map g.op p) = val s' U.unop (P.map g.op p)
      change val s Z p = val s' Z p at hs
      rw [val_nat, val_nat, hs]
    · intro a
      choose c hc using fun (U : Scheme.{0}) (v : P.obj (op U)) => (e U).2 v
      dsimp only at hc
      let φ (U : Scheme.{0}) (v : P.obj (op U)) := Sec.res (c U v) a
      have hφ (V U : Scheme.{0}) (g : V ⟶ U) (v : P.obj (op U)) :
          φ V (P.map g.op v) = Sec.res g (φ U v) := by
        have hccomp : c V (P.map g.op v) = g ≫ c U v := by
          apply (e V).1
          dsimp only
          rw [hc, op_comp, Functor.map_comp_apply, hc]
        dsimp [φ]
        rw [hccomp, res_comp]
      refine ⟨FreeHom.desc P F φ hφ, ?_⟩
      have hcid : c Z p = 𝟙 Z := by
        apply (e Z).1
        dsimp only
        rw [hc, op_id, Functor.map_id_apply]
      change val (FreeHom.desc P F φ hφ) Z p = a
      rw [hval]
      have hdesc : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫
          (FreeHom.desc P F φ hφ).hom = FreeHom.descP P F φ hφ := by
        have he := ((sheafificationAdjunction Scheme.etaleTopology.{0}
          (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply (FreeHom.descP P F φ hφ)
        rw [Adjunction.homEquiv_unit] at he
        exact he
      rw [hdesc]
      change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up p)) = a
      erw [ModuleCat.freeDesc_apply]
      change Sec.res (c Z p) a = a
      rw [hcid, res_id]
  obtain ⟨hloc, hinj, hsurj⟩ := S2 R F hF (Fin k → (Ω ≃ₐ[K] Ω)) Ω
  refine ⟨?_, ?_, ?_⟩
  · intro s s' hss
    apply hbij.1
    apply hinj
    funext g
    have e := congrFun hss (Fin.cons 1 g)
    simp only at e
    rw [gal_sec_of_lemma, gal_sec_of_lemma] at e
    simpa [tailG_cons_one, ofHom_one, res_id] using e
  · intro s
    rw [IsLocallyConstant.iff_eventually_eq]
    intro σ
    have h1 := (continuous_tailG K Ω k).continuousAt (x := σ) |>.eventually
      ((IsLocallyConstant.iff_eventually_eq _).mp (hloc (val s (Spec (CommRingCat.of (LCRing K Ω k))) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (baseHom K Ω k))) (fun i => Spec.map (CommRingCat.ofHom (legHom K Ω k i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp])))) (tailG K Ω k σ))
    have h2 := (continuous_apply 0 : Continuous fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => σ 0).continuousAt (x := σ)
      |>.eventually ((IsLocallyConstant.iff_eventually_eq _).mp
        (S3 R F hF K Ω (Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (tailG K Ω k σ)))) (val s (Spec (CommRingCat.of (LCRing K Ω k))) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (baseHom K Ω k))) (fun i => Spec.map (CommRingCat.ofHom (legHom K Ω k i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp])))))
        (σ 0))
    filter_upwards [h1, h2] with τ e1 e2
    rw [gal_sec_of_lemma, gal_sec_of_lemma, e1]
    exact e2
  · intro φ hφ heq
    have hψ : IsLocallyConstant (fun g : Fin k → (Ω ≃ₐ[K] Ω) => φ (Fin.cons 1 g)) :=
      hφ.comp_continuous (continuous_const.finCons continuous_id)
    obtain ⟨t, ht⟩ := hsurj _ hψ
    obtain ⟨s, hs⟩ := hbij.2 t
    refine ⟨s, fun σ => ?_⟩
    rw [gal_sec_of_lemma]
    simp only at hs
    rw [hs, ht, ← heq, mul_cons_tailG]

end GlobalTheory.EtC.GalSec

namespace GlobalTheory.EtC.GalSec

theorem gal_sec : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ), Function.Injective (fun (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x))) ∧ (∀ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, IsLocallyConstant (fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)))) ∧ ∀ φ : (Fin (k + 1) → (Ω ≃ₐ[K] Ω)) → Sec F (Spec (CommRingCat.of Ω)), IsLocallyConstant φ → (∀ (τ : Ω ≃ₐ[K] Ω) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)), φ (fun i => τ * σ i) = Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) (φ σ)) → ∃ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, ∀ σ, val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) = φ σ := by
  have hsections : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
      ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (B : Type) [CommRing B],
        (∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))),
          IsLocallyConstant (fun x : X =>
            Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t)) ∧
        Function.Injective (fun (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) (x : X) =>
          Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t) ∧
        ∀ ψ : X → Sec F (Spec (CommRingCat.of B)), IsLocallyConstant ψ →
          ∃ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∀ x,
            Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = ψ x := by
    intro R _ F hF X _ _ B _
    have hfin := (GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements
      (ULift.{1} R) (onRings F)).2.mp hF _ (LCSec.stage X B) (LCSec.lcCocone X B)
        (LCSec.lcCoconeIsColimit X B)
    have hrep (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) :
        ∃ (S : DiscreteQuotient X) (y : Sec F (Spec (CommRingCat.of (S → B)))),
          Sec.res (Spec.map (CommRingCat.ofHom (LCSec.pullQ X B S))) y = t := by
      obtain ⟨S, y, hy⟩ := hfin.1 t
      exact ⟨S.unop, y, hy⟩
    have hzero (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))))
        (ht : ∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = 0) :
        t = 0 := by
      obtain ⟨S, y, rfl⟩ := hrep t
      have hy : y = 0 := by
        apply (LCSec.sec_pi_bijective R F B S).1
        funext s
        obtain ⟨x, rfl⟩ := S.proj_surjective s
        exact ((LCSec.res_eval_pullQ R F X B S y x).symm.trans (ht x)).trans (map_zero _).symm
      rw [hy]
      exact map_zero _
    refine ⟨fun t => ?_, fun t₁ t₂ h => ?_, fun ψ hψ => ?_⟩
    · obtain ⟨S, y, rfl⟩ := hrep t
      have he : (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x)))
          (Sec.res (Spec.map (CommRingCat.ofHom (LCSec.pullQ X B S))) y)) =
          (fun s : S => Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y) ∘ S.proj :=
        funext (LCSec.res_eval_pullQ R F X B S y)
      rw [he]
      exact S.proj_isLocallyConstant.comp _
    · apply sub_eq_zero.mp (hzero (t₁ - t₂) fun x => ?_)
      change (F.obj.map _).hom (t₁ - t₂) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrFun h x)
    · let q : LocallyConstant X (Sec F (Spec (CommRingCat.of B))) := ⟨ψ, hψ⟩
      obtain ⟨y, hy⟩ := (LCSec.sec_pi_bijective R F B q.discreteQuotient).2 (⇑q.lift)
      refine ⟨Sec.res (Spec.map (CommRingCat.ofHom (LCSec.pullQ X B q.discreteQuotient))) y, fun x => ?_⟩
      rw [LCSec.res_eval_pullQ]
      exact congrFun hy (q.discreteQuotient.proj x)
  have haction : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
      ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
        (x : Sec F (Spec (CommRingCat.of Ω))),
        IsLocallyConstant (fun τ : Ω ≃ₐ[K] Ω =>
          Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x) := by
    intro R _ F hF K Ω _ _ _ _ x
    classical
    have elements := (GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements
      (ULift.{1} R) (onRings F)).2.mp hF
    obtain ⟨s, y, hy⟩ := (elements (Finset Ω) (GalSmooth.diag Ω) (GalSmooth.cocone Ω)
      (GalSmooth.coconeIsColimit Ω)).1 x
    have restrict_eq (τ : Ω ≃ₐ[K] Ω) :
        Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x =
          ((onRings F).map (CommRingCat.ofHom ((τ : Ω →+* Ω).comp (GalSmooth.sr Ω s).subtype))).hom y := by
      rw [← hy, GalSmooth.cocone_ι]
      show _ = ((onRings F).map (CommRingCat.ofHom (GalSmooth.sr Ω s).subtype ≫
        CommRingCat.ofHom (τ : Ω →+* Ω))).hom y
      rw [Functor.map_comp]
      rfl
    rw [IsLocallyConstant.iff_eventually_eq]
    intro τ₀
    have : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
      IntermediateField.finiteDimensional_adjoin (fun a _ => Algebra.IsIntegral.isIntegral a)
    let H := (IntermediateField.adjoin K (s : Set Ω)).fixingSubgroup
    have hopen : IsOpen (Set.ofPred fun σ : Ω ≃ₐ[K] Ω => τ₀⁻¹ * σ ∈ H) :=
      (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
    have hmem : τ₀⁻¹ * τ₀ ∈ H := by
      rw [inv_mul_cancel]
      exact H.one_mem
    filter_upwards [hopen.mem_nhds hmem] with τ hτ
    have hs : Set.EqOn (τ : Ω →+* Ω) (τ₀ : Ω →+* Ω) (s : Set Ω) := fun b hb => by
      have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ b
        (IntermediateField.subset_adjoin K _ hb)
      simpa [AlgEquiv.mul_apply] using congrArg τ₀ hfix
    have hc : (τ : Ω →+* Ω).comp (GalSmooth.sr Ω s).subtype =
        (τ₀ : Ω →+* Ω).comp (GalSmooth.sr Ω s).subtype := by
      ext a
      exact RingHom.eqOn_set_closure hs a.2
    rw [restrict_eq τ, restrict_eq τ₀, hc]
  exact gal_sec_of GlobalTheory.T.galoisLocallyConstantTupleRing_tensorPower_universal
    GlobalTheory.T.spec_widePushout_isLimit_widePullback hsections haction

end GlobalTheory.EtC.GalSec

end
