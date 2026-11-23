module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeBalancedLatticeDoubleSum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeRankOneEtaleSheafEquivLocallyConstant
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

theorem res_comp {W V U : Scheme.{0}} (k : W ⟶ V) (j : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ j) x = Sec.res k (Sec.res j x) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_smul {V U : Scheme.{0}} (j : V ⟶ U) (c : R) (x : Sec F U) :
    Sec.res j ((ULift.up c : ULift.{1} R) • x) = (ULift.up c : ULift.{1} R) • Sec.res j x :=
  map_smul _ _ _

theorem res_add {V U : Scheme.{0}} (j : V ⟶ U) (x y : Sec F U) :
    Sec.res j (x + y) = Sec.res j x + Sec.res j y := map_add _ _ _

theorem res_sub {V U : Scheme.{0}} (j : V ⟶ U) (x y : Sec F U) :
    Sec.res j (x - y) = Sec.res j x - Sec.res j y := map_sub _ _ _

theorem sep {U : Scheme.{0}} (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U) (he : ∀ i, Etale (j i))
    (hc : ∀ u : U, ∃ i v, j i v = u) (x y : Sec F U) (h : ∀ i, Sec.res (j i) x = Sec.res (j i) y) : x = y :=
  sub_eq_zero.1 ((_root_.GlobalTheory.EtC.sec_sep_glue_of_points R F U ι V j he hc).1 (x - y) (fun i => by rw [res_sub, h i, sub_self]))

theorem sec_empty {V : Scheme.{0}} [IsEmpty V] (x y : Sec F V) : x = y :=
  sep PEmpty (fun _ => V) (fun _ => 𝟙 V) (fun _ => inferInstance) (fun u => isEmptyElim u) x y (fun i => i.elim)

def fib {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (v : V) : V.Opens :=
  ⟨ψ ⁻¹' {ψ v}, ψ.isLocallyConstant.isOpen_fiber _⟩

theorem fib_apply {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (v : V) (w : (fib ψ v).toScheme) :
    ψ ((fib ψ v).ι w) = ψ v := by
  have h := (Scheme.Opens.range_ι (fib ψ v)).subset ⟨w, rfl⟩
  exact h

theorem fib_cov {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (u : V) :
    ∃ (i : V) (w : (fib ψ i).toScheme), (fib ψ i).ι w = u := by
  have h : u ∈ Set.range (fib ψ u).ι := by rw [Scheme.Opens.range_ι]; exact rfl
  obtain ⟨w, hw⟩ := h
  exact ⟨u, w, hw⟩

end GlobalTheory.EtC.GenLC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

def IsMul {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x : Sec F U) : Prop :=
  ∀ (V : Scheme.{0}) (j : V ⟶ U) (c : R), (∀ v, φ (j v) = c) →
    Sec.res j x = (ULift.up c : ULift.{1} R) • Sec.res (j ≫ s) g

theorem isMul_of_fib {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x : Sec F U)
    (h : ∀ u, Sec.res (fib φ u).ι x = (ULift.up (φ u) : ULift.{1} R) • Sec.res ((fib φ u).ι ≫ s) g) : IsMul s g φ x := by
  intro V j c hc
  by_cases hV : IsEmpty V
  · exact sec_empty _ _
  obtain ⟨v⟩ := not_isEmpty_iff.1 hV
  have H : Set.range j ⊆ Set.range (fib φ (j v)).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    change φ (j w) = φ (j v)
    rw [hc w, hc v]
  have hf := IsOpenImmersion.lift_fac (fib φ (j v)).ι j H
  rw [← hf, res_comp, h, res_smul, ← res_comp, hc v, Category.assoc]

theorem isMul_unique {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x y : Sec F U)
    (hx : IsMul s g φ x) (hy : IsMul s g φ y) : x = y :=
  sep U (fun u => (fib φ u).toScheme) (fun u => (fib φ u).ι) (fun _ => inferInstance) (fib_cov φ) x y
    (fun u => by rw [hx _ _ (φ u) (fib_apply φ u), hy _ _ (φ u) (fib_apply φ u)])

theorem isMul_exists {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) :
    ∃ x, IsMul s g φ x := by
  obtain ⟨x, hx⟩ := (_root_.GlobalTheory.EtC.sec_sep_glue_of_points R F U U (fun u => (fib φ u).toScheme) (fun u => (fib φ u).ι) (fun _ => inferInstance)
    (fib_cov φ)).2 (fun u => (ULift.up (φ u) : ULift.{1} R) • Sec.res ((fib φ u).ι ≫ s) g) (by
      intro i k
      rw [res_smul, res_smul, ← res_comp, ← res_comp, ← Category.assoc, ← Category.assoc, pullback.condition]
      by_cases hP : IsEmpty (pullback (fib φ i).ι (fib φ k).ι : Scheme.{0})
      · exact sec_empty _ _
      obtain ⟨p⟩ := not_isEmpty_iff.1 hP
      have e : φ i = φ k := by
        rw [← fib_apply φ i (pullback.fst (fib φ i).ι (fib φ k).ι p), ← fib_apply φ k (pullback.snd (fib φ i).ι (fib φ k).ι p),
          ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      rw [e])
  exact ⟨x, isMul_of_fib s g φ x hx⟩

theorem isMul_add {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ ψ : LocallyConstant U R) (x y : Sec F U)
    (hx : IsMul s g φ x) (hy : IsMul s g ψ y) : IsMul s g (φ + ψ) (x + y) := by
  intro V j c hc
  let χ : LocallyConstant V (R × R) :=
    ⟨fun v => (φ (j v), ψ (j v)), ((φ.comap j.base.hom).isLocallyConstant.comp₂ (ψ.comap j.base.hom).isLocallyConstant Prod.mk)⟩
  refine sep V (fun v => (fib χ v).toScheme) (fun v => (fib χ v).ι) (fun _ => inferInstance) (fib_cov χ) _ _ (fun v => ?_)
  have h1 : ∀ w, φ (((fib χ v).ι ≫ j) w) = φ (j v) := fun w => congrArg Prod.fst (fib_apply χ v w)
  have h2 : ∀ w, ψ (((fib χ v).ι ≫ j) w) = ψ (j v) := fun w => congrArg Prod.snd (fib_apply χ v w)
  rw [← res_comp, res_add, hx _ _ _ h1, hy _ _ _ h2, res_smul, ← res_comp, ← add_smul, ← hc v]
  rfl

end GlobalTheory.EtC.GenLC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

noncomputable def mulSec {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) : Sec F U :=
  (isMul_exists s g φ).choose

theorem mulSec_spec {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) :
    IsMul s g φ (mulSec s g φ) := (isMul_exists s g φ).choose_spec

theorem mulSec_add {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ ψ : LocallyConstant U R) :
    mulSec s g (φ + ψ) = mulSec s g φ + mulSec s g ψ :=
  isMul_unique s g _ _ _ (mulSec_spec s g _) (isMul_add s g φ ψ _ _ (mulSec_spec s g φ) (mulSec_spec s g ψ))

theorem coeff_eq {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (x : Sec F U)
    {V₁ V₂ : Scheme.{0}} (j₁ : V₁ ⟶ U) (j₂ : V₂ ⟶ U) (c₁ c₂ : R)
    (h₁ : Sec.res j₁ x = (ULift.up c₁ : ULift.{1} R) • Sec.res (j₁ ≫ s) g)
    (h₂ : Sec.res j₂ x = (ULift.up c₂ : ULift.{1} R) • Sec.res (j₂ ≫ s) g) (v₁ : V₁) (v₂ : V₂) (hv : j₁ v₁ = j₂ v₂) :
    c₁ = c₂ := by
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v₁ v₂ hv
  have e : Sec.res (pullback.fst j₁ j₂) (Sec.res j₁ x) = Sec.res (pullback.snd j₁ j₂) (Sec.res j₂ x) := by
    rw [← res_comp, ← res_comp, pullback.condition]
  rw [h₁, h₂, res_smul, res_smul, ← res_comp, ← res_comp, ← Category.assoc, ← Category.assoc, ← pullback.condition] at e
  have h0 : (ULift.up (c₁ - c₂) : ULift.{1} R) • Sec.res ((pullback.fst j₁ j₂ ≫ j₁) ≫ s) g = 0 := by
    have hu : (ULift.up (c₁ - c₂) : ULift.{1} R) = ULift.up c₁ - ULift.up c₂ := rfl
    rw [hu, sub_smul, e, sub_self]
  exact sub_eq_zero.1 ((hg _ _).2 (c₁ - c₂) ⟨p⟩ h0)

theorem mulSec_inj {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (φ : LocallyConstant U R)
    (h : mulSec s g φ = 0) : φ = 0 := by
  ext u
  have e := mulSec_spec s g φ _ (fib φ u).ι (φ u) (fib_apply φ u)
  rw [h] at e
  have hu : u ∈ Set.range (fib φ u).ι := by rw [Scheme.Opens.range_ι]; exact rfl
  obtain ⟨w, -⟩ := hu
  exact (hg (fib φ u).toScheme ((fib φ u).ι ≫ s)).2 (φ u) ⟨w⟩ (by rw [← e]; exact map_zero _)

theorem mulSec_surj {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (x : Sec F U) :
    ∃ φ, mulSec s g φ = x := by
  choose V j v c he hv hx₀ using (hg U s).1 x
  have hx : ∀ u, Sec.res (j u) x = (ULift.up (c u) : ULift.{1} R) • Sec.res (j u ≫ s) g := hx₀
  have hconst : ∀ u, ∀ u' ∈ Set.range (j u), c u' = c u := by
    rintro u _ ⟨w, rfl⟩
    exact coeff_eq s g hg x (j (j u w)) (j u) _ _ (hx _) (hx u) _ w (hv _)
  have hlc : IsLocallyConstant c := (IsLocallyConstant.iff_exists_open c).2 fun u =>
    ⟨Set.range (j u), (j u).isOpenMap.isOpen_range, ⟨v u, hv u⟩, hconst u⟩
  refine ⟨⟨c, hlc⟩, isMul_unique s g _ _ _ (mulSec_spec s g _) ?_⟩
  intro W k a ha
  refine sep W (fun w => (pullback (j (k w)) k : Scheme.{0})) (fun w => pullback.snd (j (k w)) k)
    (fun _ => inferInstance) (fun w => ?_) _ _ (fun w => ?_)
  · obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback (v (k w)) w (hv (k w))
    exact ⟨w, p, hp⟩
  · have hc : c (k w) = a := ha w
    rw [← res_comp, ← pullback.condition, res_comp, hx, res_smul, ← res_comp, res_smul, ← res_comp, hc,
      ← Category.assoc, ← Category.assoc, pullback.condition]

end GlobalTheory.EtC.GenLC


open GlobalTheory.EtC.GenLC in
theorem GlobalTheory.EtC.gen_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g → ∃ e : ∀ (U : Scheme.{0}) (s : U ⟶ S), LocallyConstant U R ≃+ Sec F U, (∀ U s (c : R), e U s (LocallyConstant.const U c) = (ULift.up c : ULift.{1} R) • Sec.res s g) ∧ ∀ (V U : Scheme.{0}) (j : V ⟶ U) (s : U ⟶ S) (φ : LocallyConstant U R), Sec.res j (e U s φ) = e V (j ≫ s) (φ.comap j.base.hom) := by
  intro R _ F S g hg
  let m : ∀ (U : Scheme.{0}) (s : U ⟶ S), LocallyConstant U R →+ Sec F U := fun U s =>
    AddMonoidHom.mk' (mulSec s g) (mulSec_add s g)
  refine ⟨fun U s => AddEquiv.ofBijective (m U s)
    ⟨(injective_iff_map_eq_zero (m U s)).2 (fun φ h => mulSec_inj s g hg φ h), mulSec_surj s g hg⟩, ?_, ?_⟩
  · intro U s c
    show mulSec s g (LocallyConstant.const U c) = _
    refine isMul_unique s g _ _ _ (mulSec_spec s g _) ?_
    intro V j a ha
    rw [res_smul, ← res_comp]
    by_cases hV : IsEmpty V
    · exact sec_empty _ _
    obtain ⟨v⟩ := not_isEmpty_iff.1 hV
    have hca : c = a := ha v
    rw [hca]
  · intro V U j s φ
    show Sec.res j (mulSec s g φ) = mulSec (j ≫ s) g (φ.comap j.base.hom)
    refine isMul_unique (j ≫ s) g _ _ _ ?_ (mulSec_spec (j ≫ s) g _)
    intro W k a ha
    rw [← res_comp, mulSec_spec s g φ W (k ≫ j) a ha, Category.assoc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeSheafHomValueAtCechNerveSimplexBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.CechPts

variable {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {Z : Scheme.{0}} (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y))
  (h : ∀ i, y i ≫ f = x)

def cmp : yoneda.obj Z ⟶ widePullback (yoneda.obj X) (fun _ : Fin (k + 1) => yoneda.obj Y) (fun _ => yoneda.map f) :=
  WidePullback.lift (yoneda.map x) (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i])

theorem cechPt_eq : cechPt f k x y h = (cmp f k x y h).app (op Z) (𝟙 Z) := rfl

theorem map_cechPt {U : Scheme.{0}} (g : U ⟶ Z) :
    ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h) = (cmp f k x y h).app (op U) g := by
  rw [cechPt_eq]
  have hn := (congrArg (fun t => t (𝟙 Z)) ((cmp f k x y h).naturality g.op)).symm
  change _ = (cmp f k x y h).app (op U) (g ≫ 𝟙 Z)
  change ((cech f).obj (op ⦋k⦌)).map g.op ((cmp f k x y h).app (op Z) (𝟙 Z)) =
    (cmp f k x y h).app (op U) (g ≫ 𝟙 Z) at hn
  exact hn

theorem app_eq {U : Scheme.{0}} (g : U ⟶ Z) :
    (cmp f k x y h).app (op U) g = yonedaEquiv (yoneda.map g ≫ cmp f k x y h) := by
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]

theorem bij (hc : IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h)) (U : Scheme.{0}) :
    Function.Bijective ((cmp f k x y h).app (op U)) := by
  constructor
  · intro g g' hg
    rw [app_eq, app_eq] at hg
    have hm := yonedaEquiv.injective hg
    apply WidePullbackCone.IsLimit.hom_ext hc
    · apply yoneda.map_injective
      have := hm =≫ WidePullback.base _
      simp only [cmp, Category.assoc, WidePullback.lift_base] at this
      exact (yoneda.map_comp _ _).trans (this.trans (yoneda.map_comp _ _).symm)
    · intro i
      apply yoneda.map_injective
      have := hm =≫ WidePullback.π _ i
      simp only [cmp, Category.assoc, WidePullback.lift_π] at this
      exact (yoneda.map_comp _ _).trans (this.trans (yoneda.map_comp _ _).symm)
  · intro v
    obtain ⟨m, rfl⟩ := yonedaEquiv.surjective v
    have w : ∀ i, yonedaEquiv (m ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) ≫ f =
        yonedaEquiv (m ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) := by
      intro i
      rw [← WidePullback.π_arrow (fun _ : Fin (k + 1) => yoneda.map f) i, ← Category.assoc, yonedaEquiv_comp]
      rfl
    refine ⟨WidePullbackCone.IsLimit.lift hc _ _ w, (app_eq f k x y h _).trans ?_⟩
    congr 1
    apply WidePullback.hom_ext
    · intro i
      apply yonedaEquiv.injective
      have := WidePullbackCone.IsLimit.lift_π hc _ _ w i
      simp only [WidePullbackCone.mk_π] at this
      rw [Category.assoc]
      simp only [cmp, WidePullback.lift_π]
      exact (congrArg yonedaEquiv (yoneda.map_comp _ _).symm).trans ((yonedaEquiv_yoneda_map _).trans this)
    · apply yonedaEquiv.injective
      have := WidePullbackCone.IsLimit.lift_base hc _ _ w
      simp only [WidePullbackCone.mk_base] at this
      rw [Category.assoc]
      simp only [cmp, WidePullback.lift_base]
      exact (congrArg yonedaEquiv (yoneda.map_comp _ _).symm).trans ((yonedaEquiv_yoneda_map _).trans this)

end GlobalTheory.EtC.CechPts


open GlobalTheory.EtC.CechPts in
theorem GlobalTheory.EtC.CechPts.main : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (k : ℕ) (Z : Scheme.{0}) (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y)) (h : ∀ i, y i ≫ f = x), IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h) → Function.Bijective (fun s : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F => val s Z (cechPt f k x y h)) := by
  intro R _ F Y X f k Z x y h hc
  have e : ∀ U : Scheme.{0}, Function.Bijective
      (fun g : U ⟶ Z => ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h)) := by
    intro U
    have hb := bij f k x y h hc U
    refine ⟨fun g g' hg => hb.1 ((map_cechPt f k x y h g).symm.trans (hg.trans (map_cechPt f k x y h g'))), fun v => ?_⟩
    obtain ⟨g, hg⟩ := hb.2 v
    exact ⟨g, (map_cechPt f k x y h g).trans hg⟩
  have hext : ∀ s s' : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F,
      (∀ U v, val s U v = val s' U v) → s = s' := by
    intro s s' hs
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ F.property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨v⟩
    exact hs U.unop v
  have hnat : ∀ (s : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U) (v : ((cech f).obj (op ⦋k⦌)).obj (op U)),
      val s V (((cech f).obj (op ⦋k⦌)).map g.op v) = Sec.res g (val s U v) := by
    intro s V U g v
    let η := toSheafify Scheme.etaleTopology ((freeP R).obj ((cech f).obj (op ⦋k⦌))) ≫ s.hom
    change (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (((cech f).obj (op ⦋k⦌)).map g.op v))) =
      (F.obj.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up v)))
    rw [← GlobalTheory.EtC.FreeHom.freePresheaf_map_freeMk _ g.op v]
    exact congrArg (fun t => t.hom (ModuleCat.freeMk (ULift.up v))) (η.naturality g.op)
  have hex : ∀ φ : ∀ U : Scheme.{0}, ((cech f).obj (op ⦋k⦌)).obj (op U) → Sec F U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) v, φ V (((cech f).obj (op ⦋k⦌)).map g.op v) = Sec.res g (φ U v)) →
      ∃ s : (free R).obj ((cech f).obj (op ⦋k⦌)) ⟶ F, ∀ U v, val s U v = φ U v := by
    intro φ hφ
    refine ⟨GlobalTheory.EtC.FreeHom.desc _ F φ hφ, ?_⟩
    intro U v
    change ((toSheafify Scheme.etaleTopology ((freeP R).obj _) ≫ (GlobalTheory.EtC.FreeHom.desc _ F φ hφ).hom).app (op U)).hom (ModuleCat.freeMk (ULift.up v)) = _
    have hd : toSheafify Scheme.etaleTopology ((freeP R).obj ((cech f).obj (op ⦋k⦌))) ≫ (GlobalTheory.EtC.FreeHom.desc _ F φ hφ).hom = GlobalTheory.EtC.FreeHom.descP _ F φ hφ := by
      have ht := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply (GlobalTheory.EtC.FreeHom.descP _ F φ hφ)
      rw [Adjunction.homEquiv_unit] at ht
      exact ht
    rw [hd]
    change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up v)) = _
    erw [ModuleCat.freeDesc_apply]
    rfl
  constructor
  · intro s s' hs
    change val s Z (cechPt f k x y h) = val s' Z (cechPt f k x y h) at hs
    apply hext
    intro U v
    obtain ⟨g, rfl⟩ := (e U).2 v
    dsimp only
    rw [hnat s U Z g, hnat s' U Z g, hs]
  · intro a
    choose c hc0 using fun (U : Scheme.{0}) (v : ((cech f).obj (op ⦋k⦌)).obj (op U)) => (e U).2 v
    have hc' : ∀ (U : Scheme.{0}) (v : ((cech f).obj (op ⦋k⦌)).obj (op U)),
        ((cech f).obj (op ⦋k⦌)).map (c U v).op (cechPt f k x y h) = v := hc0
    obtain ⟨s, hs⟩ := hex (fun U v => Sec.res (c U v) a) (by
      intro V U g v
      have h1 : c V (((cech f).obj (op ⦋k⦌)).map g.op v) = g ≫ c U v := by
        apply (e V).1
        change ((cech f).obj (op ⦋k⦌)).map (c V _).op (cechPt f k x y h) =
          ((cech f).obj (op ⦋k⦌)).map (g ≫ c U v).op (cechPt f k x y h)
        rw [hc' V, op_comp, Functor.map_comp_apply, hc' U v]
      dsimp only
      rw [h1]
      simp [Sec.res])
    refine ⟨s, ?_⟩
    change val s Z (cechPt f k x y h) = a
    rw [hs]
    have h2 : c Z (cechPt f k x y h) = 𝟙 Z := by
      apply (e Z).1
      change ((cech f).obj (op ⦋k⦌)).map (c Z _).op (cechPt f k x y h) =
        ((cech f).obj (op ⦋k⦌)).map (𝟙 Z).op (cechPt f k x y h)
      rw [hc' Z, op_id]
      change _ = ((cech f).obj (op ⦋k⦌)).map (𝟙 (op Z)) _
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [h2]
    simp [Sec.res]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceIsDVRAndResidueEqGround
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem isDiscreteValuationRing_functionFieldPlace_ring {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) :
    IsDiscreteValuationRing v.O := by
  haveI hn : Nontrivial (MonoidWithZeroHom.valueGroup ((v.1 : F →*₀ WithZero (Multiplicative ℤ)))) := by
    obtain ⟨z, hz⟩ := v.2.1 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    let u : (WithZero (Multiplicative ℤ))ˣ :=
      Units.mk0 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) WithZero.coe_ne_zero
    refine ⟨⟨1, ⟨u, MonoidWithZeroHom.mem_valueGroup _ ⟨z, hz⟩⟩, ?_⟩⟩
    intro h
    have := congrArg (fun u => ((u : _ ˣ) : WithZero (Multiplicative ℤ))) (congrArg Subtype.val h)
    have h2 : (Multiplicative.ofAdd (1:ℤ)) = 1 := WithZero.coe_injective (by simpa [u] using this.symm)
    simp at h2
  exact Valuation.valuationSubring_isDiscreteValuationRing v.1

theorem place_le_one_const {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (c : k) :
    v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

theorem functionFieldPlace_exists_const_sub_lt_one {k F : Type} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (hF : IsFF k F) (v : Place k F) (x : F) (hx : v.1 x ≤ 1) :
    ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by
  by_contra hne
  push_neg at hne
  have h1 : ∀ c : k, v.1 (x - algebraMap k F c) = 1 := fun c =>
    le_antisymm ((v.1.map_sub _ _).trans (max_le hx (place_le_one_const v c))) (hne c)
  have hq : ∀ q : k[X], q ≠ 0 → v.1 (Polynomial.aeval x q) = 1 := by
    intro q hq0
    have hs := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := q) IsAlgClosed.card_roots_eq_natDegree
    rw [← hs, map_mul, map_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod]
    simp only [Polynomial.aeval_C, Function.comp_def, map_sub, Polynomial.aeval_X, Multiset.map_map]
    rw [(v.2.2 _ (Polynomial.leadingCoeff_ne_zero.mpr hq0)), one_mul]
    simp [h1]
  have htr : Transcendental k x := by
    rintro ⟨q, hq0, hqx⟩
    have := hq q hq0
    rw [hqx, map_zero] at this
    exact zero_ne_one this
  haveI hfin : FiniteDimensional k⟮x⟯ F := (_root_.GlobalTheory.Nef.isFF_main k F hF).1 x htr
  have hK : ∀ y ∈ k⟮x⟯, v.1 y ≤ 1 := by
    intro y hy
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k y).1 hy
    have hle : ∀ q : k[X], v.1 (Polynomial.aeval x q) ≤ 1 := fun q => by
      by_cases h0 : q = 0
      · simp [h0]
      · exact (hq q h0).le
    by_cases hs0 : s = 0
    · simp [hs0]
    · rw [map_div₀, hq s hs0, div_one]
      exact hle r
  have hint : ∀ y : F, v.1 y ≤ 1 := by
    intro y
    obtain ⟨f, hm, hf⟩ := Algebra.IsIntegral.isIntegral (R := k⟮x⟯) y
    have hc : ∀ i, v.1 (algebraMap k⟮x⟯ F (f.coeff i)) ≤ 1 := fun i => hK _ (f.coeff i).2
    by_cases hn : f.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hn
      obtain ⟨c, rfl⟩ := hn
      simp [hm.ne_zero_of_C] at hf
    simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
      one_mul, add_eq_zero_iff_eq_neg] at hf
    apply_fun v.1 at hf
    rw [Valuation.map_neg, Valuation.map_pow] at hf
    contrapose! hf
    refine ne_of_lt (v.1.map_sum_lt ?_ ?_)
    · simp [hn, (hf.trans' (zero_lt_one)).ne']
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [Valuation.map_mul, Valuation.map_pow]
      exact mul_lt_of_le_one_of_lt (hc _) <| pow_lt_pow_right₀ hf hi
  obtain ⟨z, hz⟩ := v.2.1 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  have := hint z
  rw [hz] at this
  exact absurd this (by decide)

theorem place_isDVR_residue : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ v : Place k F, IsDiscreteValuationRing v.O ∧ ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by
  intro k F _ _ _ _ _ hF v
  exact ⟨isDiscreteValuationRing_functionFieldPlace_ring v, fun x hx => functionFieldPlace_exists_const_sub_lt_one hF v x hx⟩

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoTermIteratedFDerivSummableBound
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

theorem fTerm_deriv_summable_bound : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F),
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ, Summable u ∧
      ∀ p, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z p.1.out.1 p.2.1) z‖ ≤ u p := by
  intro F _ _ _ 𝔞 𝔟 K hK hKH L hL hLU n
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound F K hK hKH L hL hLU n
  obtain ⟨C₀, -, hC₀⟩ := _root_.GlobalTheory.BalancedUnits.balanced_unit_multiple F
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.HeckeTwo.summable_balanced_latSum F 𝔞 𝔟 C₀ m
  obtain ⟨C, hC⟩ := hm N
  choose ε hε using fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) => hC₀ c.out.1 c.out.2.2
  refine ⟨fun p => C * ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N, (hN ε hε).mul_left C, ?_⟩
  rintro ⟨c, ν⟩ σ hσ z hz
  have hee : (((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε c : 𝓞 F) : F) = 1 := unit_inv_mul (ε c)
  have hfun : (fun z : Emb F → ℂ => fTerm σ z c.out.1 ν.1) =
      fun z => fTerm σ z (((ε c : 𝓞 F) : F) * c.out.1) (((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1) := by
    funext z
    have hb : c.out.1 = ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * (((ε c : 𝓞 F) : F) * c.out.1) := by
      rw [← mul_assoc, hee, one_mul]
    conv_lhs => rw [hb]
    exact _root_.GlobalTheory.HeckeTwoUnit.fTerm_unit_move F σ z _ _ (ε c)⁻¹
  have hb0 : ((ε c : 𝓞 F) : F) * c.out.1 ≠ 0 := mul_ne_zero (right_ne_zero_of_mul_eq_one hee) c.out.2.2
  have hν0 : ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1 ≠ 0 := mul_ne_zero (left_ne_zero_of_mul_eq_one hee) ν.2.2
  dsimp only
  rw [hfun]
  refine (hC σ hσ z hz _ _ hb0 hν0).trans (le_of_eq ?_)
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := congrArg τ hee
  rw [map_mul, map_one] at h1
  have h2 : τ (((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1) * τ (((ε c : 𝓞 F) : F) * c.out.1) = τ ν.1 * τ c.out.1 := by
    rw [map_mul, map_mul]; linear_combination (τ ν.1 * τ c.out.1) * h1
  rw [h2]

end GlobalTheory.HeckeTwo
end
end

