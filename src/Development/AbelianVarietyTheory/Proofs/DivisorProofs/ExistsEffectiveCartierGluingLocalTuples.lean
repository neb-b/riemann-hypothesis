module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelCartierDivisorThetaSetup
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2999

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def toA (T : UTrait Xo c) {X : Scheme.{0}} (ξ : Sp T.V ⟶ X) : ATrait X where
  V := T.V
  dvr := T.cdvr.1
  char := T.cdvr.2.2
  complete := T.cdvr.2.1
  ϖ := T.ϖ
  irr := T.irr
  ξ := ξ

variable {C : UCompact Xo c}

theorem exists_utrait_of_stalk (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (x : Y.Z) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (hcomp : IsAdicComplete (maximalIdeal V) V) (θ : Y.Z.presheaf.stalk x →+* V)
    (hθ : Function.Injective θ) :
    ∃ (T : UTrait Xo c) (f : V →+* T.V) (γ : X₁.Ω₁ →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧
      (∀ a, γ (Y.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a))) ∧
      jK T.V ≫ spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x = spMap γ ≫ Y.pt ∧ T.y = spMap γ ≫ X₁.uΩ := by
  haveI := ArithBase.char (o := X₁.o₁) (Ω := X₁.Ω₁)
  haveI : CharZero (Y.Z.presheaf.stalk x) := (Y.stalkHom x).charZero
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : Y.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (Y.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (Y.stalkEquiv x).symm.injective)
  let γ₀ : X₁.Ω₁ →+* FractionRing V := IsFractionRing.lift (A := Y.O x) (K := X₁.Ω₁) hθ'
  have hγ₀ : ∀ a, γ₀ (Y.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := Y.O x) (K := X₁.Ω₁) hθ' (Y.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, hfi, hfl, -, hc, hy⟩ :=
    GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V hB inferInstance (spMap γ₀ ≫ X₁.uΩ)
  refine ⟨T, f, fK.comp γ₀, hfi, hfl, ?_, ?_, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hγ₀, hc]
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (Y.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← GlobalTheory.Poinc.GenTrait.spMap_stalkHom_fromSpecStalk Y x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e,
      ← Formalism.L2.Pj.spMap_comp', Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']

end GlobalTheory.UPoinc.UGlue


open GlobalTheory.UPoinc.UGlue GlobalTheory.Poinc.OrdGlue in
theorem GlobalTheory.UPoinc.UGlue.glue (hgood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), Set.range ξ ⊆ (U₀ : Set Y.Z) → (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → Subsingleton T.P.D.toPre.X) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (ι : ℕ) (K : Type) [Fintype K] (Jk : K → Type) [∀ k, Fintype (Jk k)] (t : ∀ k, Jk k → X₁.Ω₁), (∀ k j, t k j ≠ 0) → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → (∀ k, Nonempty (Jk k) → Y.HasDiv (t k)) → (∀ x : Y.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ (∀ j, UOrdGe Y T ξ (t k j) a) ∧ ∃ j, UOrdEq Y T ξ (t k j) a) → ∃ D : GlobalTheory.EffCartierData Y.Z, (∀ y ∈ D.idealSheaf.support, y ∉ U₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  intro E _ _ _ H Dw _ φ _ l Xo c C X₁ ι K _ Jk _ t _ Y U₀ EE out hAdm hdiv hloc
  haveI := isLocallyNoetherian Y
  haveI := ArithBase.char (o := X₁.o₁) (Ω := X₁.Ω₁)
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z := hAdm.1.normal
  have hU₀ : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact Y.top_le_preimage_pt hAdm.1.ne (x := w) trivial

  have hthru : ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z) (γ : X₁.Ω₁ →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ Y.pt →
      T.y = spMap γ ≫ X₁.uΩ → ∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧
        X₁.Lies (ξ₀ ≫ out.u₀) T.y := by
    intro T ξ γ h₁ h₂
    refine ⟨spMap γ ≫ IsOpenImmersion.lift U₀.ι Y.pt hU₀, ?_, spMap γ ≫ spMap (ratHull X₁.S.R).val.toRingHom, ?_, ?_⟩
    · rw [Category.assoc, IsOpenImmersion.lift_fac, h₁]
    · rw [Category.assoc, spMap_val_toRat, Category.assoc, out.u₀_gen _ (IsOpenImmersion.lift_fac _ _ _)]
    · rw [h₂, Category.assoc]

  have hcentre : ∀ x : Y.Z, ∃ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z) (γ : X₁.Ω₁ →+* FractionRing T.V),
      ξ (closedPoint T.V) = x ∧ jK T.V ≫ ξ = spMap γ ≫ Y.pt ∧ T.y = spMap γ ≫ X₁.uΩ := by
    intro x
    haveI : CharZero (Y.Z.presheaf.stalk x) := RingHom.charZero (Y.stalkHom x)
    obtain ⟨V, _, _, _, θ, ⟨hd, hc, -⟩, hi, hl⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (Y.Z.presheaf.stalk x)
    obtain ⟨T, f, γ, -, hfl, -, h₂, h₃⟩ := exists_utrait_of_stalk X₁ Y x V hc θ hi
    haveI := hfl
    exact ⟨T, _, γ, GlobalTheory.Poinc.OrdGlue.centre (f.comp θ), h₂, h₃⟩

  have hreg : ∀ (x : Y.Z) (s : X₁.Ω₁), (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z) (γ : X₁.Ω₁ →+* FractionRing T.V),
      jK T.V ≫ ξ = spMap γ ≫ Y.pt → T.y = spMap γ ≫ X₁.uΩ → ξ (closedPoint T.V) = x →
        ∃ w : T.V, γ s = algebraMap T.V (FractionRing T.V) w) → s ∈ Y.O x := by
    intro x s h
    haveI : CharZero (Y.Z.presheaf.stalk x) := RingHom.charZero (Y.stalkHom x)
    haveI := (hN x).2
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Y.O x) s
    obtain ⟨a, rfl⟩ := (Y.stalkEquiv x).surjective a
    obtain ⟨b, rfl⟩ := (Y.stalkEquiv x).surjective b
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact nonZeroDivisors.ne_zero hb (map_zero _)
    have hb1 : Y.stalkHom x b ≠ 0 := (map_ne_zero_iff _ (Y.stalkHom_injective x)).2 hb0
    change Y.stalkHom x a / Y.stalkHom x b ∈ Y.O x
    obtain ⟨c', rfl⟩ := GlobalTheory.Poinc.dvd_of_forall_complete_dvr (Y.Z.presheaf.stalk x) a b hb0 fun V _ _ _ hV θ hθ hl => by
      obtain ⟨T, f, γ, hf, hfl, h₄, h₂, h₃⟩ := exists_utrait_of_stalk X₁ Y x V hV θ hθ
      haveI := hfl
      obtain ⟨w, hw⟩ := h T _ γ h₂ h₃ (GlobalTheory.Poinc.OrdGlue.centre (f.comp θ))
      refine dvd_of_map_dvd f hf ⟨w, IsFractionRing.injective T.V (FractionRing T.V) ?_⟩
      rw [map_mul, ← h₄, ← h₄, ← hw, ← map_mul]
      congr 1
      change _ = _ * (Y.stalkHom x a / Y.stalkHom x b)
      rw [mul_div_cancel₀ _ hb1]
    rw [map_mul, mul_div_cancel_left₀ _ hb1]
    exact (Y.stalkEquiv x c').2
  have hgen : ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme,
      ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → (toA T ξ).GenIn U₀ := by
    rintro T ξ ⟨ξ₀, h₀, -⟩ _ ⟨w, rfl⟩
    rw [← Scheme.Opens.range_ι]
    exact ⟨ξ₀ w, by change U₀.ι (ξ₀ w) = (jK T.V ≫ ξ) w; rw [← h₀]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩
  have exists_spread {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
      (f : ∀ x : X, X.presheaf.stalk x) (hU : ∀ η ∈ U, ringKrullDim (X.presheaf.stalk η) = 1 → IsUnit (f η))
      (hne : ∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → genericPoint X ∈ U) (x : X) (h0 : f x ≠ 0)
      (hc : ∀ (η : X) (h : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
        Associated ((X.presheaf.stalkSpecializes h).hom (f x)) (f η)) :
      ∃ (W : X.Opens) (hx : x ∈ W) (s : Γ(X, W)), (X.presheaf.germ W x hx).hom s = f x ∧
        ∀ (η : X) (hη : η ∈ W), ringKrullDim (X.presheaf.stalk η) = 1 →
          Associated ((X.presheaf.germ W η hη).hom s) (f η) := by
    obtain ⟨W₀, hx₀, s₀, hs₀⟩ := X.presheaf.exists_germ_eq (f x)
    obtain ⟨⟨W, hW⟩, hx, hle⟩ := EffCartierData.exists_affine_le hx₀
    let s : Γ(X, W) := resG X hle s₀
    have hs : (X.presheaf.germ W x hx).hom s = f x := (Cartier.germ_resG hle _ hx _).trans hs₀
    let B : Set X := {η | ∃ hη : η ∈ W, ringKrullDim (X.presheaf.stalk η) = 1 ∧
      ¬ Associated ((X.presheaf.germ W η hη).hom s) (f η)}
    have hgen : ∀ {V : X.Opens} {y : X}, y ∈ V → genericPoint X ∈ V := fun {V y} hy =>
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨y, trivial, hy⟩
    have hB : B.Finite := by
      rcases B.eq_empty_or_nonempty with h | ⟨η₀, -, h₀, -⟩
      · rw [h]; exact Set.finite_empty
      have hs0 : s ≠ 0 := fun e => h0 (by rw [← hs, e, map_zero])
      have hb : genericPoint X ∈ X.basicOpen s := by
        rw [X.mem_basicOpen s _ (hgen hx)]
        have : (X.presheaf.germ W _ (hgen hx)).hom s ≠ 0 := fun e =>
          hs0 (germ_injective_of_isIntegral X _ (hgen hx) (e.trans (map_zero _).symm))
        exact (IsUnit.mk0 (G₀ := X.functionField) _ this)
      refine (GlobalTheory.Poinc.TraitGlue.finite_dim_one hW (U ⊓ X.basicOpen s) (hgen hx) ⟨hne η₀ h₀, hb⟩).subset ?_
      rintro η ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun h4 => h3 ?_⟩
      exact (associated_one_iff_isUnit.2 ((X.mem_basicOpen s η h1).1 h4.2)).trans
        (associated_one_iff_isUnit.2 (hU η h4.1 h2)).symm
    have hcl : IsClosed (⋃ η ∈ B, closure ({η} : Set X)) := hB.isClosed_biUnion fun _ _ => isClosed_closure
    let W' : X.Opens := W ⊓ ⟨_, hcl.isOpen_compl⟩
    have hx' : x ∈ W' := by
      refine ⟨hx, fun hm => ?_⟩
      obtain ⟨η, ⟨h1, h2, h3⟩, h4⟩ := Set.mem_iUnion₂.1 hm
      have h5 : η ⤳ x := specializes_iff_mem_closure.2 h4
      refine h3 ?_
      rw [← GlobalTheory.Poinc.TraitGlue.specializes_germ h5 hx h1, hs]
      exact hc η h5 h2
    refine ⟨W', hx', resG X inf_le_left s, (Cartier.germ_resG _ _ hx' _).trans hs, fun η hη h1 => ?_⟩
    rw [Cartier.germ_resG]
    by_contra hn
    exact hη.2 (Set.mem_iUnion₂.2 ⟨η, ⟨hη.1, h1, hn⟩, subset_closure rfl⟩)

  have exists_of_germs {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
      (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (U : X.Opens)
      (f : ∀ x : X, X.presheaf.stalk x) (hU : ∀ η ∈ U, ringKrullDim (X.presheaf.stalk η) = 1 → IsUnit (f η))
      (hne : ∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → genericPoint X ∈ U) (h0 : ∀ x, f x ≠ 0)
      (hc : ∀ (x η : X) (h : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
        Associated ((X.presheaf.stalkSpecializes h).hom (f x)) (f η)) :
      ∃ D : EffCartierData X, (∀ x ∈ D.idealSheaf.support, x ∉ U) ∧
        ∀ x, FinalTheorems.stalkId D.idealSheaf x = Ideal.span {f x} := by
    choose W hx s hs hW using fun x => exists_spread U f hU hne x (h0 x) (hc x)
    have hs0 : ∀ x, s x ≠ 0 := fun x e => h0 x (by rw [← hs x, e, map_zero])
    have hreg : ∀ x, Cartier.IsRegularFn (s x) := fun x => Cartier.isRegularFn_of_ne_zero (hs0 x)
    have hdvd : ∀ (i j y : X) (hi : y ∈ W i) (hj : y ∈ W j),
        (X.presheaf.germ _ y hi).hom (s i) ∣ (X.presheaf.germ _ y hj).hom (s j) := by
      intro i j y hi hj
      refine GlobalTheory.Poinc.TraitGlue.dvd_of_generisations hX y (fun e =>
        hs0 i (germ_injective_of_isIntegral X _ hi (e.trans (map_zero _).symm))) fun η hη h1 => ?_
      have hi' : η ∈ W i := hη.mem_open (W i).isOpen hi
      have hj' : η ∈ W j := hη.mem_open (W j).isOpen hj
      rw [GlobalTheory.Poinc.TraitGlue.specializes_germ hη hi hi', GlobalTheory.Poinc.TraitGlue.specializes_germ hη hj hj']
      exact ((hW i η hi' h1).trans (hW j η hj' h1).symm).dvd
    let D : EffCartierData X :=
      { ι := X
        U := W
        f := s
        cover := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩
        regular := hreg
        assoc := fun i j => ((hreg i).resG _).associated_of_germ ((hreg j).resG _) fun y hy => by
          rw [Cartier.germ_resG, Cartier.germ_resG]
          exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 (hdvd j i y hy.2 hy.1))
            (Ideal.span_singleton_le_span_singleton.2 (hdvd i j y hy.1 hy.2)) }
    refine ⟨D, fun x hxD hxU => ?_, fun x => (D.stalkId_idealSheaf x x (hx x)).trans (congrArg (fun t => Ideal.span {t}) (hs x))⟩
    refine (D.mem_support_iff x (hx x)).1 hxD ((X.mem_basicOpen (s x) x (hx x)).2 ?_)
    change IsUnit ((X.presheaf.germ _ x (hx x)).hom (s x))
    rw [hs x]
    refine isUnit_of_dvd_one (GlobalTheory.Poinc.TraitGlue.dvd_of_generisations hX x (h0 x) fun η hη h1 => ?_)
    exact ((hc x η hη h1).symm.isUnit (hU η (hη.mem_open U.isOpen hxU) h1)).dvd

  have exists_effCartier_of_orders : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (U : X.Opens) (R : ATrait X → ℕ → Prop), (∀ (T : ATrait X) (a : ℕ), Set.range T.ξ ⊆ U → R T a → a = 0) → (∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → ∃ (T : ATrait X) (a e : ℕ), T.CentredAt η e ∧ T.GenIn U ∧ R T a) → (∀ x : X, ∃ f : X.presheaf.stalk x, ∀ (T : ATrait X) (h : T.ξ (closedPoint T.V) ⤳ x) (a : ℕ), T.GenIn U → R T a → T.HasOrd h f a) → ∃ D : EffCartierData X, (∀ x ∈ D.idealSheaf.support, x ∉ U) ∧ ∀ (T : ATrait X) (a : ℕ), T.GenIn U → R T a → idlAlong D.idealSheaf T.ξ = Ideal.span {T.ϖ ^ a} := by
    intro X _ _ hX U R hR hT hf
    have hf' : ∀ x : X, ∃ f : X.presheaf.stalk x, f ≠ 0 ∧ ∀ (T : ATrait X) (h : T.ξ (closedPoint T.V) ⤳ x) (a : ℕ),
        T.GenIn U → R T a → T.HasOrd h f a := by
      intro x
      obtain ⟨f, hf⟩ := hf x
      by_cases h0 : f = 0
      · refine ⟨1, one_ne_zero, fun T h a h1 h2 => ?_⟩
        have := hf T h a h1 h2
        rw [h0, ATrait.HasOrd, map_zero, map_zero, Ideal.span_singleton_eq_span_singleton] at this
        exact absurd (this.eq_zero_iff.1 rfl) (pow_ne_zero _ T.irr.ne_zero)
      · exact ⟨f, h0, hf⟩
    choose f h0 hf using hf'
    have hself : ∀ (T : ATrait X) (a : ℕ), T.GenIn U → R T a →
        Ideal.span {(Scheme.stalkClosedPointTo T.ξ).hom (f _)} = Ideal.span {T.ϖ ^ a} := by
      intro T a h1 h2
      have := hf _ T specializes_rfl a h1 h2
      rwa [ATrait.HasOrd, TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, RingHom.id_apply] at this
    obtain ⟨D, hD, hD'⟩ := exists_of_germs hX U f (fun η hη h1 => by
        obtain ⟨T, a, e, ⟨rfl, -⟩, h2, h3⟩ := hT η h1
        have ha : a = 0 := hR T a (by
          rintro _ ⟨p, rfl⟩
          exact ((IsLocalRing.specializes_closedPoint p).map T.ξ.continuous).mem_open U.isOpen hη) h3
        have := hself T a h2 h3
        rw [ha, pow_zero, Ideal.span_singleton_one, Ideal.span_singleton_eq_top] at this
        exact isUnit_of_map_unit _ _ this)
      (fun η h1 => by
        obtain ⟨T, a, e, -, h2, -⟩ := hT η h1
        obtain ⟨p⟩ : Nonempty (Sp (FractionRing T.V)) := inferInstanceAs (Nonempty (PrimeSpectrum _))
        exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨_, trivial, h2 ⟨p, rfl⟩⟩) h0
      (fun x η h h1 => by
        obtain ⟨T, a, e, ⟨rfl, -⟩, h2, h3⟩ := hT η h1
        have := GlobalTheory.Poinc.TraitGlue.valuationRing_stalk hX _ h1
        have e1 := Ideal.span_singleton_eq_span_singleton.1 (hf x T h a h2 h3)
        have e2 := Ideal.span_singleton_eq_span_singleton.1 (hself T a h2 h3)
        exact GlobalTheory.Poinc.TraitGlue.associated_of_map (Scheme.stalkClosedPointTo T.ξ).hom (e1.trans e2.symm)
          (e1.ne_zero_iff.2 (pow_ne_zero _ T.irr.ne_zero)))
    refine ⟨D, hD, fun T a h1 h2 => ?_⟩
    rw [idlAlong, hD', Ideal.map_span, Set.image_singleton]
    exact hself T a h1 h2
  refine Exists.elim (exists_effCartier_of_orders Y.Z hN U₀
    (fun A a => ∃ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), A = toA T ξ ∧ (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme,
      ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧ (a : ℝ) = ι * φ.evalZ T.be) ?_ ?_ ?_) fun D ⟨hD, hord⟩ => ?_
  rotate_right
  · refine ⟨D, hD, fun T ξ hT => ?_⟩
    obtain ⟨k, hk⟩ := hloc (ξ (closedPoint T.V))
    obtain ⟨a, ha, -⟩ := hk T ξ hT specializes_rfl
    exact ⟨a, ha, hord (toA T ξ) a (hgen T ξ hT) ⟨T, ξ, rfl, hT, ha⟩⟩
  · rintro _ a hr ⟨T, ξ, rfl, hT, ha⟩
    haveI := hgood E H Dw l Xo c C X₁ Y U₀ EE out hAdm T ξ hr hT
    rw [InvFun.evalZ, InvFun.eval_of_subsingleton, mul_zero] at ha
    exact_mod_cast ha
  · intro η hη
    obtain ⟨T, ξ, γ, rfl, h₁, h₂⟩ := hcentre η
    obtain ⟨k, hk⟩ := hloc (ξ (closedPoint T.V))
    obtain ⟨a, ha, -⟩ := hk T ξ (hthru T ξ γ h₁ h₂) specializes_rfl
    have hinj : Function.Injective (Scheme.stalkClosedPointTo ξ).hom := by
      refine (injective_iff_map_eq_zero _).2 fun b hb => ?_
      have e := val_jK ξ specializes_rfl b
      rw [TopCat.Presheaf.stalkSpecializes_refl, h₁, val_generic] at e
      simp only [CommRingCat.hom_id, RingHom.id_apply] at e
      rw [hb, map_zero, map_eq_zero, map_eq_zero_iff _ (Y.stalkHom_injective _)] at e
      exact e
    have hne : (maximalIdeal (Y.Z.presheaf.stalk (ξ (closedPoint T.V)))).map (Scheme.stalkClosedPointTo ξ).hom ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
      intro hb
      rw [ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.2 hb)] at hη
      exact zero_ne_one hη
    haveI := T.cdvr.1
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne T.irr
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · exfalso
        rw [pow_zero, Ideal.span_singleton_one] at he
        have hle : (maximalIdeal (Y.Z.presheaf.stalk (ξ (closedPoint T.V)))).map (Scheme.stalkClosedPointTo ξ).hom ≤
            maximalIdeal T.V := Ideal.map_le_iff_le_comap.2 fun b hb => (map_mem_nonunits_iff _ b).2 hb
        exact (maximalIdeal.isMaximal T.V).ne_top (top_le_iff.1 (he ▸ hle))
      · exact h
    refine ⟨toA T ξ, a, e, ⟨rfl, hinj, he1, specializes_rfl, ?_⟩, hgen T ξ (hthru T ξ γ h₁ h₂), T, ξ, rfl,
      hthru T ξ γ h₁ h₂, ha⟩
    change Ideal.map ((Scheme.stalkClosedPointTo ξ).hom.comp
      (Y.Z.presheaf.stalkSpecializes (specializes_refl (ξ (closedPoint T.V)))).hom) _ = _
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact he
  · intro x
    obtain ⟨k, hk⟩ := hloc x
    obtain ⟨T₀, ξ₀, γ₀, h₀, h₁, h₂⟩ := hcentre x
    obtain ⟨_, -, -, j₁, -⟩ := hk T₀ ξ₀ (hthru T₀ ξ₀ γ₀ h₁ h₂) (specializes_of_eq h₀)
    obtain ⟨j₀, hj₀⟩ := hdiv k ⟨j₁⟩ x
    have hr : t k j₀ ∈ Y.O x := hreg x _ fun T ξ γ h₁ h₂ h₀ => by
      obtain ⟨a, -, hge, -⟩ := hk T ξ (hthru T ξ γ h₁ h₂) (specializes_of_eq h₀)
      obtain ⟨-, w, hw⟩ := hge j₀
      rw [h₁, val_generic] at hw
      exact ⟨_, hw⟩
    obtain ⟨f, hf⟩ := (Y.stalkEquiv x).surjective ⟨_, hr⟩
    have hf' : Y.stalkHom x f = t k j₀ := congrArg Subtype.val hf
    refine ⟨f, ?_⟩
    rintro _ h a - ⟨T, ξ, rfl, hT, ha⟩
    change ξ (closedPoint T.V) ⤳ x at h
    obtain ⟨a', ha', hge, j, w', hw'⟩ := hk T ξ hT h
    obtain rfl : a = a' := by exact_mod_cast ha.trans ha'.symm
    obtain ⟨-, w, hw⟩ := hge j₀
    obtain ⟨q, hq⟩ := (Y.stalkEquiv x).surjective ⟨_, hj₀.2 j⟩
    have hq' : Y.stalkHom x q = t k j / t k j₀ := congrArg Subtype.val hq
    have e₁ := val_jK ξ h f
    have e₂ := val_jK ξ h (f * q)
    rw [hf', hw] at e₁
    rw [map_mul, hf', hq', mul_div_cancel₀ _ hj₀.1, hw', map_mul (Y.Z.presheaf.stalkSpecializes h).hom,
      map_mul (Scheme.stalkClosedPointTo ξ).hom] at e₂
    have e₃ := IsFractionRing.injective T.V (FractionRing T.V) e₁
    have e₄ := IsFractionRing.injective T.V (FractionRing T.V) e₂
    rw [← e₃, mul_assoc] at e₄
    have hu : IsUnit w := isUnit_of_mul_isUnit_left (mul_left_cancel₀ (pow_ne_zero a T.irr.ne_zero) e₄ ▸ w'.isUnit)
    exact (congrArg (fun r => Ideal.span {r}) e₃.symm).trans (Ideal.span_singleton_mul_right_unit hu _)

theorem GlobalTheory.UPoinc.UGlue.exists_effCartier_of_locTuples : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (ι : ℕ) (K : Type) [Fintype K] (Jk : K → Type) [∀ k, Fintype (Jk k)] (t : ∀ k, Jk k → X₁.Ω₁), (∀ k j, t k j ≠ 0) → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → (∀ k, Nonempty (Jk k) → Y.HasDiv (t k)) → (∀ x : Y.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ (∀ j, UOrdGe Y T ξ (t k j) a) ∧ ∃ j, UOrdEq Y T ξ (t k j) a) → ∃ D : GlobalTheory.EffCartierData Y.Z, (∀ y ∈ D.idealSheaf.support, y ∉ U₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} :=
  GlobalTheory.UPoinc.UGlue.glue _root_.GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset
