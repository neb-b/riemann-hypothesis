module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0102
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionExteriorValue
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.FieldStage

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem tied_pull (Y : Model Xo c β) {B F : Type} [CommRing B] [CommRing F] (ψ : B →+* F)
    {y : Sp B ⟶ Xo.XF c} {y' : Sp F ⟶ Xo.XF c} (hy : y' = spMap ψ ≫ y)
    {V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {V' : Sp (DualNumber B) ⟶ Y.t.G.left} (h : Tied Y y V V') :
    Tied Y y' (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V') := by
  subst hy
  obtain ⟨u, h1, h2, h3⟩ := h
  refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ u, ?_, ?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc]
    congr 1
    exact spec_dual_alg ψ
  · rw [Category.assoc, h2]
  · rw [Category.assoc, h3]

theorem tied_over (Y : Model Xo c β) {B : Type} [CommRing B] {y : Sp B ⟶ Xo.XF c}
    {V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {V' : Sp (DualNumber B) ⟶ Y.t.G.left} (h : Tied Y y V V') :
    V ≫ Xo.univ.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ under y := by
  obtain ⟨u, h1, rfl, -⟩ := h
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  rw [Category.assoc, hp.w, ← Category.assoc, h1, Category.assoc]

theorem isCombAt_pull {B F : Type} [CommRing B] [CommRing F] (ψ : B →+* F) {x : Sp B ⟶ Xo.X} {x' : Sp F ⟶ Xo.X}
    (hx : spMap ψ ≫ x = x') {m : ℕ} {vs : Fin m → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left)} {cf : Fin m → B}
    {w : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} (h : Formalism.L2.Pj.IsCombAt x vs cf w) :
    Formalism.L2.Pj.IsCombAt x' (fun k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ vs k) (fun k => ψ (cf k))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let P : Formalism.L2.Pj.tEps x' ⟶ Formalism.L2.Pj.tEps x := epsBase ψ hx
  let Q : (Formalism.L2.Pj.tEps x ⟶ Xo.univ.t.G) →* (Formalism.L2.Pj.tEps x' ⟶ Xo.univ.t.G) :=
    { toFun := fun f => P ≫ f, map_one' := comp_one _, map_mul' := fun a b => comp_mul _ _ _ }
  refine ⟨fun i => P ≫ u i, fun i => ?_, ?_⟩
  · change spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ (u i).left = _
    rw [hu i, ← GlobalTheory.CompanionTheory.Ar.FrameEig.epsMul_eq, ← GlobalTheory.CompanionTheory.Ar.FrameEig.epsMul_eq, ← Category.assoc, ← Category.assoc]
    congr 1
    exact spec_dual_eps ψ (cf i)
  · have : (List.ofFn fun i => P ≫ u i).prod = P ≫ (List.ofFn u).prod := by
      change (List.ofFn fun i => Q (u i)).prod = Q (List.ofFn u).prod
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [this]
    rfl

theorem exists_pulled (Y : Model Xo c β) {B F : Type} [CommRing B] [Field F] (ψ : B →+* F) (yB : Sp B ⟶ Xo.XF c)
    (y : Sp F ⟶ Xo.XF c) (hy : y = spMap ψ ≫ yB) (x₀ : Sp B ⟶ Xo.X) (hx₀ : x₀ = under yB) {n : ℕ} (v : Vecs y n)
    (vs : Fin n → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left))
    (hv : ∀ k, (v k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ vs k) (C : Matrix (Fin n) (Fin n) B)
    (ee : Fin n → (Sp (DualNumber B) ⟶ Y.t.G.left))
    (hV : ∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y yB V (ee i) ∧
      Formalism.L2.Pj.IsCombAt x₀ vs (C i) V) :
    ∃ v₀ : Vecs y n, (∀ i, IsComb ((ψ.mapMatrix C) i) v (v₀ i)) ∧
      ∀ i, Tied Y y (v₀ i).left (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ ee i) := by
  choose V hT hC using hV
  have hT' := fun i => tied_pull Y ψ hy (hT i)
  refine ⟨fun i => Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫ V i) (tied_over Y (hT' i)), fun i => ?_, hT'⟩
  rw [GlobalTheory.CompanionTheory.Ar.FrameEig.isComb_iff]
  have hx : spMap ψ ≫ x₀ = under y := by
    rw [hx₀, hy]
    exact (Category.assoc _ _ _).symm
  have := isCombAt_pull ψ hx (hC i)
  simp only [← hv] at this
  exact this

theorem exists_germ (Y : Model Xo c β) {U : Set (Xo.XF c)} (Z : CptOver Y U) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (φ₂ : R →+* Z.Ω) (hφ : spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j) {F : Type} [Field F]
    (y : Sp F ⟶ Xo.XF c) (hU : Set.range y ⊆ U) (θF : R →+* F) (hθ : spMap θF ≫ x = y ≫ Y.j) :
    ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (θ' : R →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))),
      spMap θ' ≫ x = Y.X.fromSpecStalk (centre (y ≫ Y.j)) ∧
      (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ' = φ₂ ∧
      (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ' = θF := by
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := by
    have h1 : genPt Z.ξ₀ ⤳ y (IsLocalRing.closedPoint F) := (Z.closure _).1 (hU ⟨_, rfl⟩)
    have h2 := h1.map Y.j.continuous
    simp only [genPt, centre, Scheme.Hom.comp_apply]
    exact h2
  have hqr : centre (y ≫ Y.j) ∈ x.opensRange := by
    rw [← hθ]
    change (spMap θF ≫ x) (IsLocalRing.closedPoint F) ∈ Set.range x
    simp only [Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hqx : (Y.X.fromSpecStalk (centre (y ≫ Y.j)))
      (IsLocalRing.closedPoint (Y.X.presheaf.stalk (centre (y ≫ Y.j)))) ∈ x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hqr
  obtain ⟨θ', hθ'⟩ := exists_lift (A := Y.X.presheaf.stalk (centre (y ≫ Y.j))) x _ hqx
  refine ⟨h, θ', hθ', ?_, ?_⟩
  · have h1 : spMap ((genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ') ≫ x = spMap φ₂ ≫ x := by
      have e1 : spMap ((genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ') =
          spMap (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩) ≫ spMap θ' := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e1, Category.assoc, hθ', hφ]
      exact spec_genMap _ _
    exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))
  · have h1 : spMap ((Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ') ≫ x = spMap θF ≫ x := by
      have e1 : spMap ((Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ') =
          spMap (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom ≫ spMap θ' := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e1, Category.assoc, hθ', hθ]
      exact spec_centre _
    exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))

theorem valAt_of_chart (Y : Model Xo c β) {U : Set (Xo.XF c)} (Z : CptOver Y U) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y.X) (φ₂ : R →+* Z.Ω) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (θF : R →+* F)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (θ' : R →+* Y.X.presheaf.stalk (centre (y ≫ Y.j)))
    (h₁ : spMap θ' ≫ x = Y.X.fromSpecStalk (centre (y ≫ Y.j)))
    (h₂ : (genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h⟩).comp θ' = φ₂)
    (h₃ : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp θ' = θF) (b : Z.V) (e : epsAt x ⟶ Y.t.G)
    (ht : GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x e) (hb : (Z.M.pt b).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ e.left)
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) (hv' : v'.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θF) ≫ e.left) :
    Z.M.ValAt (y ≫ Y.j) b v' := by
  refine ⟨h, epsBase θ' h₁ ≫ e, ⟨isTanAt_base _ _ ht, ?_⟩, ?_⟩
  · rw [hb, ← h₂, ← spMap_dual_comp]
    simp [epsBase, spMap]
  · rw [hv', ← h₃, ← spMap_dual_comp]
    simp [epsBase, spMap]

theorem sameVec_of_tied (Y : Model Xo c β) {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v : epsAt (under y) ⟶ Xo.univ.t.G} {v' : epsAt (y ≫ Y.j) ⟶ Y.t.G} {w : Sp (DualNumber F) ⟶ Y.t.G.left}
    (h : Tied Y y v.left w) (hw : w = v'.left) : SameVec Y y v v' := by
  subst hw
  exact h

end GlobalTheory.CompanionTheory.Ar.LocFn.FieldStage

theorem GlobalTheory.CompanionTheory.Ar.LocFn.function_of_frames_at_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (R : Type) [CommRing R] (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (φ₂ : R →+* Z.Ω) (e₁ : Fin D.p → (epsAt x ⟶ Y.t.G)) (e₂ : Fin D.q → (epsAt x ⟶ Y.t.G)) (f : R) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (α κ : Z.Ω) (B : Type) [CommRing B] [Algebra S B] (θ : R →+* B) (C₁ : Matrix (Fin D.p) (Fin D.p) B) (C₂ : Matrix (Fin D.q) (Fin D.q) B), IsLineFn U τ φ → Represents Y U τ Z.M a b φ → spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j → a = α • exteriorPower.ιMulti Z.Ω D.p b₁ → b = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → φ₂ f = α / κ → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) → (∀ i, (Z.M.pt (b₁ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₁ i).left) → (∀ i, (Z.M.pt (b₂ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₂ i).left) → spMap θ ≫ x = spMap (algebraMap S B) ≫ zPt z ≫ Y.j → IsUnit C₁.det → IsUnit C₂.det → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u τ (k.cast hp.symm)) (C₁ i) V) → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) (C₂ i) V) → ∀ (F : Type) [Field F] (ψ : B →+* F) (y : Sp F ⟶ Xo.XF c), y = spMap ψ ≫ spMap (algebraMap S B) ≫ zPt z → Set.range y ⊆ U → ∀ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → φ F y v w * ψ C₂.det = ψ (θ f) * ψ C₁.det := by
  intro E _ _ _ H D l Xo c U τ O _ β Y Z φ a b S _ _ z hp hq R _ x _ φ₂ e₁ e₂ f b₁ b₂ α κ B _ _ θ C₁ C₂ hφ hrep hξ ha hb
    hf ht₁ ht₂ hb₁ hb₂ hθ hC₁ hC₂ hV₁ hV₂ F _ ψ y hy hU v w hv hw
  have e0 : ∀ {A : Type} [CommRing A] (g : A →+* B), spMap (ψ.comp g) = spMap ψ ≫ spMap g := fun g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hyS : under y = spMap (ψ.comp (algebraMap S B)) ≫ z.x := by
    rw [hy, e0]
    simp only [under, Category.assoc, zPt_fst]
  have hys : y ≫ pullback.snd _ _ = spMap ((ψ.comp (algebraMap S B)).comp (algebraMap c.F S)) := by
    rw [hy]
    simp only [Category.assoc, zPt_snd]
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨v', w', hv', hw', hfr⟩ := GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt E H D l Xo c τ S z F (ψ.comp (algebraMap S B)) y
    hp hq hyS hys
  have ev : v' = v := funext fun i => Over.OverMorphism.ext ((hv' i).trans (hv i).symm)
  have ew : w' = w := funext fun i => Over.OverMorphism.ext ((hw' i).trans (hw i).symm)
  rw [ev, ew] at hfr
  have hF := hfr U hU
  have hzx : spMap (algebraMap S B) ≫ z.x = under (spMap (algebraMap S B) ≫ zPt z) := by
    simp only [under, Category.assoc, zPt_fst]
  have hvv : ∀ k, (v k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫
      (spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u τ (k.cast hp.symm)) := fun k => by
    rw [hv k, ← Category.assoc]
    exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp (algebraMap S B) ψ).symm
  have hww : ∀ k, (w k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) ≫
      (spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) := fun k => by
    rw [hw k, ← Category.assoc]
    exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp (algebraMap S B) ψ).symm
  obtain ⟨v₀, hc₁, hT₁⟩ := FieldStage.exists_pulled Y ψ _ y hy _ hzx v _ hvv C₁
    (fun i => spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) hV₁
  obtain ⟨w₀, hc₂, hT₂⟩ := FieldStage.exists_pulled Y ψ _ y hy _ hzx w _ hww C₂
    (fun i => spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) hV₂
  have hu₁ : IsUnit (ψ.mapMatrix C₁).det := by
    rw [← RingHom.map_det]; exact hC₁.map ψ
  have hu₂ : IsUnit (ψ.mapMatrix C₂).det := by
    rw [← RingHom.map_det]; exact hC₂.map ψ
  have hF₀ : IsFramed U τ ((ψ.comp (algebraMap S B)).comp (algebraMap c.F S)) y v₀ w₀ :=
    ⟨hF.1, hF.2.1, _root_.GlobalTheory.CompanionTheory.Ar.FrameUnit.isEigFrame_of_isUnit_det Xo.X F Xo.univ.t.G (under y) (𝓞 E) Xo.univ.t.act _ D.p v v₀ (ψ.mapMatrix C₁) hF.2.2.1 hc₁ hu₁,
      _root_.GlobalTheory.CompanionTheory.Ar.FrameUnit.isEigFrame_of_isUnit_det Xo.X F Xo.univ.t.G (under y) (𝓞 E) Xo.univ.t.act _ D.q w w₀ (ψ.mapMatrix C₂) hF.2.2.2 hc₂ hu₂⟩
  have hθF : spMap (ψ.comp θ) ≫ x = y ≫ Y.j := by
    rw [e0, Category.assoc, hθ, hy]
    simp only [Category.assoc]
  obtain ⟨h, θ', g₁, g₂, g₃⟩ := FieldStage.exists_germ Y Z x φ₂ hξ y hU (ψ.comp θ) hθF
  have hval₁ : ∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v₀ i) v' := fun i =>
    ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase (ψ.comp θ) hθF ≫ e₁ i,
      FieldStage.valAt_of_chart Y Z x φ₂ y (ψ.comp θ) h θ' g₁ g₂ g₃ (b₁ i) (e₁ i) (ht₁ i) (hb₁ i) _ rfl,
      FieldStage.sameVec_of_tied Y (hT₁ i) (by
        rw [← Category.assoc]
        exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp θ ψ))⟩
  have hval₂ : ∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₂ i) v' ∧ SameVec Y y (w₀ i) v' := fun i =>
    ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase (ψ.comp θ) hθF ≫ e₂ i,
      FieldStage.valAt_of_chart Y Z x φ₂ y (ψ.comp θ) h θ' g₁ g₂ g₃ (b₂ i) (e₂ i) (ht₂ i) (hb₂ i) _ rfl,
      FieldStage.sameVec_of_tied Y (hT₂ i) (by
        rw [← Category.assoc]
        exact congrArg (· ≫ _) (GlobalTheory.CompanionTheory.Ar.LieVB.spMap_dual_comp θ ψ))⟩
  obtain ⟨h', s, hs₁, hs₂⟩ := hrep F _ y v₀ w₀ b₁ b₂ α κ hF₀ ha hb hval₁ hval₂
  have hs : s = θ' f := Z.gen.inj ⟨_, h'⟩ (hs₁.trans (hf.symm.trans (by rw [← g₂]; rfl)))
  have hvalue : φ F y v₀ w₀ = ψ (θ f) := by
    rw [← hs₂, hs]
    exact RingHom.congr_fun g₃ f
  have hchg := hφ.chg F _ y v w v₀ w₀ (ψ.mapMatrix C₁) (ψ.mapMatrix C₂) hF hF₀ hc₁ hc₂
  rw [hvalue, ← RingHom.map_det, ← RingHom.map_det] at hchg
  exact hchg.symm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetQuotientFormula
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section Pow1

variable {k : Type} [Field k] {d : ℕ}

theorem aeval_firstOrder {B A : Type} [CommRing B] [Algebra k B] [CommRing A] [Algebra k A]
    (τ : B →ₐ[k] A) (ε : A) (hε : ε * ε = 0) (c : Fin d → k) (z : Fin d → B)
    (P : MvPolynomial (Fin 2 × Fin d) k) :
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then algebraMap k A (c q.2) * ε else τ (z q.2)) P =
      τ (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2) P) +
      ε * ∑ i, algebraMap k A (c i) * τ (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2)
        (MvPolynomial.pderiv ((0 : Fin 2), i) P)) := by
  set θ : MvPolynomial (Fin 2 × Fin d) k →ₐ[k] B :=
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2) with hθ
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    simp only [map_add (f := _), hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P q hP =>
    obtain ⟨a, j⟩ := q
    rw [map_mul, hP, MvPolynomial.aeval_X]
    by_cases ha : a = 0
    · subst ha
      have key : ∀ i, τ (θ (MvPolynomial.pderiv ((0 : Fin 2), i) (P * MvPolynomial.X ((0 : Fin 2), j)))) =
          if j = i then τ (θ P) else 0 := by
        intro i
        have hX : θ (MvPolynomial.X ((0 : Fin 2), j)) = 0 := by simp [hθ]
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, hX, zero_mul, add_zero,
          MvPolynomial.pderiv_X]
        by_cases hij : j = i
        · subst hij; simp
        · simp [Pi.single_apply, hij, Ne.symm hij]
      simp only [key, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hX : θ (P * MvPolynomial.X ((0 : Fin 2), j)) = 0 := by simp [hθ]
      rw [hX, map_zero, zero_add]
      linear_combination (algebraMap k A (c j) * ∑ i, algebraMap k A (c i) * τ (θ (MvPolynomial.pderiv ((0 : Fin 2), i) P))) * hε
    · have key : ∀ i, θ (MvPolynomial.pderiv ((0 : Fin 2), i) (P * MvPolynomial.X (a, j))) =
          θ (MvPolynomial.pderiv ((0 : Fin 2), i) P) * z j := by
        intro i
        have h0 : MvPolynomial.pderiv ((0 : Fin 2), i) (MvPolynomial.X (a, j) : MvPolynomial (Fin 2 × Fin d) k) = 0 := by
          rw [MvPolynomial.pderiv_X, Pi.single_apply, if_neg]
          intro h; exact ha (congrArg Prod.fst h)
        rw [Derivation.leibniz, h0, smul_zero, zero_add, smul_eq_mul, map_mul, mul_comm]
        simp [hθ, ha]
      have hX : θ (P * MvPolynomial.X (a, j)) = θ P * z j := by simp [hθ, ha]
      simp only [key, hX, ha, if_false, map_mul, Finset.mul_sum, Finset.sum_mul, add_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

theorem mk_psTrunc_of_le {κ : Type} [Fintype κ] [DecidableEq κ] {m N : ℕ} (hN : m ≤ N)
    (f : MvPowerSeries κ k) :
    Ideal.Quotient.mk (orig k κ ^ (m + 1)) (psTrunc N f) = psJet m f := by
  rw [psJet, Ideal.Quotient.eq]
  refine GermD.mem_orig_pow_of fun e he => ?_
  by_contra hlt
  push Not at hlt
  apply MvPolynomial.mem_support_iff.mp he
  rw [MvPolynomial.coeff_sub, GermFun.coeff_psTrunc _ _ _ (by omega), GermFun.coeff_psTrunc _ _ _ (by omega), sub_self]

theorem mk_pderiv_psTrunc {κ : Type} [Fintype κ] [DecidableEq κ] {m N : ℕ} (hN : m + 1 ≤ N)
    (f : MvPowerSeries κ k) (q : κ) :
    Ideal.Quotient.mk (orig k κ ^ (m + 1)) (MvPolynomial.pderiv q (psTrunc N f)) =
      psJet m (MvPowerSeries.pderiv (R := k) q f) := by
  rw [psJet, Ideal.Quotient.eq]
  refine GermD.mem_orig_pow_of fun e he => ?_
  by_contra hlt
  push Not at hlt
  apply MvPolynomial.mem_support_iff.mp he
  have hd : (e + Finsupp.single q 1).degree = e.degree + 1 := by simp
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_pderiv, GermFun.coeff_psTrunc _ _ _ (by omega),
    GermFun.coeff_psTrunc _ _ _ (by omega), MvPowerSeries.coeff_pderiv, sub_self]

theorem aeval_axis_eq_psJet (m : ℕ) (P : MvPolynomial (Fin 2 × Fin d) k) (h : Germ.PS k 2 d)
    (hP : Ideal.Quotient.mk (orig k (Fin 2 × Fin d) ^ (m + 1)) P = psJet m h) :
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : Jet k (Fin 1 × Fin d) m)
      else Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2))) P =
      psJet m (Germ.ev (n := 1) ![0, Germ.pt k d 0] h) := by
  have ha : ∀ q : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) q.1 q.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a <;> simp [Germ.pt]
  rw [Germ.ev, FBIdJet.psJet_subst m _ ha, ← hP, GermD.jetMap_mk]
  have e : (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : Jet k (Fin 1 × Fin d) m)
      else Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2))) : MvPolynomial (Fin 2 × Fin d) k →ₐ[k] _) =
      (Ideal.Quotient.mkₐ k _).comp (MvPolynomial.aeval fun q : Fin 2 × Fin d =>
        psTrunc m ((![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) q.1 q.2)) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    obtain ⟨a, j⟩ := q
    rw [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.aeval_X]
    show _ = psJet m _
    fin_cases a
    · simp [psJet, psTrunc]
    · have : (![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) 1 j =
          ((MvPolynomial.X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries _ k) := by
        simp [Germ.pt]
      simp only [Fin.mk_one, this, ExpGF.psJet_coe]
      simp
  rw [e]
  rfl

theorem psJet_sum_C_mul {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (u : Fin d → k)
    (h : Fin d → MvPowerSeries κ k) :
    psJet m (∑ i, MvPowerSeries.C (u i) * h i) = ∑ i, algebraMap k (Jet k κ m) (u i) * psJet m (h i) := by
  have hadd : ∀ f g : MvPowerSeries κ k, psJet m (f + g) = psJet m f + psJet m g := fun f g => by
    simp [psJet, psTrunc, Finset.sum_add_distrib]
  have hzero : psJet m (0 : MvPowerSeries κ k) = 0 := by simp [psJet, psTrunc]
  have hC : ∀ c : k, psJet m (MvPowerSeries.C c : MvPowerSeries κ k) = algebraMap k (Jet k κ m) c := fun c => by
    have : (MvPowerSeries.C c : MvPowerSeries κ k) = ((MvPolynomial.C c : MvPolynomial κ k) : MvPowerSeries κ k) := by simp
    rw [this, ExpGF.psJet_coe]
    rfl
  let L : MvPowerSeries κ k →+ Jet k κ m := ⟨⟨psJet m, hzero⟩, hadd⟩
  have := map_sum L (fun i => MvPowerSeries.C (u i) * h i) Finset.univ
  refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
  show psJet m _ = _
  rw [FBIdJet.psJet_mul, hC]

theorem jq_psJet_ptPow (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d m : ℕ) (w : Fin d → k)
    (g : Germ.PS k 2 d) (hg : AxOne g) :
    jq w p m (psJet (p + m + 1) (Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] g)) =
      1 + dQ _ p ^ p * algebraMap _ _ (psJet m (dSer g fun i => w i ^ p)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set B := Jet k (Fin 1 × Fin d) m with hB
  set A := Jet B Unit p with hA
  have hε : dQ B p ^ p * dQ B p ^ p = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (by omega) (dQ_pow B p)
  have ha : ∀ q : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) q.1 q.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a
    · simp [ptPow, hp]
    · simp [Germ.pt]
  have hjq : ∀ Q : MvPolynomial (Fin 2 × Fin d) k, jq w p m (Ideal.Quotient.mk _ Q) =
      MvPolynomial.aeval (fun q : Fin 2 × Fin d =>
        if q.1 = 0 then algebraMap k A (w q.2) * dQ B p
        else inR (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2)))) Q := fun Q => rfl
  have step : jq w p m (psJet (p + m + 1) (Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] g)) =
      MvPolynomial.aeval (fun q : Fin 2 × Fin d =>
        if q.1 = 0 then algebraMap k A (w q.2 ^ p) * dQ B p ^ p
        else inR (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2)))) (psTrunc (p + m + 1) g) := by
    rw [Germ.ev, FBIdJet.psJet_subst _ _ ha, psJet, GermD.jetMap_mk, hjq, MvPolynomial.comp_aeval_apply]
    congr 2
    funext q
    obtain ⟨a, j⟩ := q
    rw [← hjq]
    show jq w p m (psJet _ _) = _
    fin_cases a
    · have : (![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) 0 j =
          ((MvPolynomial.X ((0 : Fin 2), j) ^ p : MvPolynomial (Fin 2 × Fin d) k) : MvPowerSeries _ k) := by
        simp [ptPow]
      simp only [Fin.zero_eta, this, ExpGF.psJet_coe, hjq]
      simp [mul_pow]
    · have : (![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) 1 j =
          ((MvPolynomial.X ((1 : Fin 2), j) : MvPolynomial (Fin 2 × Fin d) k) : MvPowerSeries _ k) := by
        simp [Germ.pt]
      simp only [Fin.mk_one, this, ExpGF.psJet_coe, hjq]
      simp
  rw [step, aeval_firstOrder (inR (k := k) B p) (dQ B p ^ p) hε (fun i => w i ^ p)
    (fun j => Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) (psTrunc (p + m + 1) g)]
  rw [aeval_axis_eq_psJet m _ g (mk_psTrunc_of_le (by omega) g), hg.1, FBIdJet.psJet_one, map_one]
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dSer, psJet_sum_C_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_axis_eq_psJet m _ _ (mk_pderiv_psTrunc (by omega) g _), map_mul]
  rw [← IsScalarTower.algebraMap_apply]
  rfl

end Pow1

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteGeneratingValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif


set_option backward.isDefEq.respectTransparency false in
theorem lie_frame_values_basis : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (z₀ : Sp ℂ ⟶ X), IsCptGen ξ → genPt ξ ⤳ centre z₀ → ∃ (N : ℕ) (s : Fin N → Li), (∀ i, ∃ v : epsAt z₀ ⟶ G, M.ValAt z₀ (s i) v) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z₀ V) (b : Fin N → V), (∀ i, M.ValAt z₀ (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ := by
  intro X Ω _ ξ G _ _ _ Li _ _ M z₀ hξ h
  obtain ⟨R, _, x, hx, F, _, _, MR, n, b₀, hp⟩ := LieVB.exists_chart G (centre z₀)
  have hq' : (X.fromSpecStalk (centre z₀)) (IsLocalRing.closedPoint (X.presheaf.stalk (centre z₀))) ∈
      x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hp
  obtain ⟨ψ, hψ⟩ := LieVB.exists_lift (A := X.presheaf.stalk (centre z₀)) x (X.fromSpecStalk (centre z₀)) hq'
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀))
  obtain ⟨-, BA, -, -⟩ := LieVB.basis_tr (A := X.presheaf.stalk (centre z₀)) ψ x (X.fromSpecStalk (centre z₀))
    hψ MR MA b₀
  obtain ⟨i, hi⟩ := LieVB.exists_tr (A := X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀)) ξ
    (genMap ξ ⟨centre z₀, h⟩) (LieTangent.spec_genMap ξ ⟨centre z₀, h⟩) MA M
  have hext : ∀ a, M.Extends ⟨centre z₀, h⟩ (i a) (MA.pt a) := fun a => ⟨MA.tan a, hi a⟩
  refine ⟨n, fun k => i (BA k), fun k => ?_, fun V _ _ Mz b hb => ?_⟩
  · obtain ⟨E₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G ℂ z₀
    obtain ⟨j, hj⟩ := LieVB.exists_tr (A := X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀)) z₀
      (Scheme.stalkClosedPointTo z₀).hom (LieTangent.spec_centre z₀) MA M₀
    exact ⟨M₀.pt (j (BA k)), h, _, hext _, hj _⟩
  · obtain ⟨β, B, hB, hβ⟩ := LieVB.basis_tr (R := X.presheaf.stalk (centre z₀))
      (Scheme.stalkClosedPointTo z₀).hom (X.fromSpecStalk (centre z₀)) z₀ (LieTangent.spec_centre z₀) MA Mz BA
    have hbB : b = B := by
      funext k
      obtain ⟨_, v, hv, hw⟩ := hb k
      have hva : MA.pt (BA k) = v := (hext (BA k)).unique (hξ.inj _) hv
      subst hva
      rw [hB]
      exact LieVB.pt_left_inj Mz (hw.trans (hβ _).symm)
    rw [hbB]
    exact ⟨B.linearIndependent, B.span_eq⟩

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieFreeSmooth

theorem lieModel_free_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom →
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E]
      [Module R E] (M : LieModel G x E), ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R E) := by
  intro S G _ hG R _ _ x E _ _ M
  haveI := hG
  obtain ⟨hfin, hproj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective S G R x E M
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R E := Module.free_of_flat_of_isLocalRing
  exact ⟨_, ⟨Module.finBasis R E⟩⟩

end GlobalTheory.CompanionTheory.Ar.LieFreeSmooth
end

