module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CorrOfGenericOfIsSeparated
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory

universe u

theorem corr_of_corr_pullGen {X Y Z : Scheme.{u}} (L : LB X) {I I' : Type u} [Fintype I] [Fintype I']
    (φ : I → (Y ⟶ X)) (ε : I → ℤ) (φ' : I' → (Y ⟶ X)) (ε' : I' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (h : Z ⟶ Y)
    (hinj : ∀ U, Function.Injective (h.app U).hom) (hc : ∀ a b : Y ⟶ X, h ≫ a = h ≫ b → a = b)
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h)) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  intro j j' c₁ c₂ c₃
  have e := H j j' (fun a b e => c₁ a b (hc _ _ e)) (fun a b e => c₂ a b (hc _ _ e))
    (fun a b e => c₃ a b (hc _ _ e))
  have le : h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') ≤
      LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' := fun _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k⟩
  have e' := congrArg (res le) e
  change res le (res _ (LB.ts (LB.pullGen L _ _ t h) j)) = res le (res _ (LB.ts (LB.pullGen L _ _ t' h) j')) at e'
  rw [LB.ts_pullGen, LB.ts_pullGen] at e'
  simp only [LB.res_res] at e'
  refine Units.map_injective (f := (h.app (LB.wchart L φ j ⊓ LB.wchart L φ' j')).hom.toMonoidHom)
    (hinj _) ?_
  exact (LB.pullU_res h _ _).trans (e'.trans (LB.pullU_res h _ _).symm)

theorem corr_of_generic_of_isSeparated
    (V : Type u) [CommRing V] (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [IsSeparated G.hom]
    (T : Over (Spec (CommRingCat.of V))) [Flat T.hom]
    (L : LB G.left) {I I' : Type u} [Fintype I] [Fintype I']
    (φ : I → (T.left ⟶ G.left)) (ε : I → ℤ) (φ' : I' → (T.left ⟶ G.left)) (ε' : I' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (H : LB.Gen.Corr L _ _ _ _
      (LB.pullGen L _ _ t (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))))
      (LB.pullGen L _ _ t' (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))))) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  have := (ExtUnique.spec_fractionRing V K).2
  have : IsSchemeTheoreticallyDominant
      (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))) :=
    .of_isPullback (IsPullback.of_hasPullback _ _).flip
  refine corr_of_corr_pullGen L φ ε φ' ε' t t' _ (fun U => Scheme.Hom.app_injective _ U)
    (fun a b e => ?_) H
  exact ExtUnique.hom_ext_of_dominant (G.hom ≫ terminal.from _) (terminal.hom_ext _ _) _ e

namespace DoubledPoint

variable {X : Scheme.{0}} (U : X.Opens)

end DoubledPoint

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSecValueIsUnit
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.NoBasePoint

theorem exists_section_mem {K : Type} [Field K] [IsAlgClosed K] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] (W : Y.Opens) (hW : (W : Set Y).Nonempty) :
    ∃ σ : Spec (CommRingCat.of K) ⟶ Y, σ ≫ f = 𝟙 _ ∧ ∀ p, σ p ∈ W := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hW W.isOpen.isLocallyClosed
  exact ⟨pointOfClosedPoint f c hc, pointOfClosedPoint_comp f c hc, fun p =>
    (congrArg (· ∈ W) (pointOfClosedPoint_apply f c hc p)).mpr hcW⟩

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translPt_eq {T : Over S} (a : T ⟶ A) : translPt A a = (fst T A ≫ a) * snd T A := rfl

theorem ptSecT_translT {T : Over S} (a x : T ⟶ A) : ptSecT A x ≫ translT A a = ptSecT A (a * x) := by
  simp [ptSecT, translT, translPt_eq, comp_lift, MonObj.comp_mul]

theorem exists_two_points {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S)
    [LocallyOfFiniteType A.hom] [IsIntegral (Over.mk t ⊗ A).left] (D : (Over.mk t ⊗ A).left.Opens)
    (hD : (D : Set (Over.mk t ⊗ A).left).Nonempty) (x c : Over.mk t ⟶ A) :
    ∃ a : Over.mk t ⟶ A, (∀ p, (ptSecT A (a * x)).left p ∈ D) ∧ ∀ p, (ptSecT A (a⁻¹ * c)).left p ∈ D := by
  let T := Over.mk t
  let u₁ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A * (fst T A ≫ x))
  let w₁ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A * (fst T A ≫ x)⁻¹)
  let u₂ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) ((snd T A)⁻¹ * (fst T A ≫ c))
  let w₂ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) ((fst T A ≫ c) * (snd T A)⁻¹)
  have e₁ : w₁ ≫ u₁ = 𝟙 _ := by
    ext <;> simp [u₁, w₁, MonObj.comp_mul]
  have e₂ : w₂ ≫ u₂ = 𝟙 _ := by
    ext <;> simp [u₂, w₂, MonObj.comp_mul, GrpObj.comp_inv]
  have ne : ∀ u w : T ⊗ A ⟶ T ⊗ A, w ≫ u = 𝟙 _ → ((u.left ⁻¹ᵁ D : (T ⊗ A).left.Opens) : Set (T ⊗ A).left).Nonempty := by
    intro u w e
    obtain ⟨d, hd⟩ := hD
    refine ⟨w.left d, ?_⟩
    show u.left (w.left d) ∈ D
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact hd
  have hne : ((u₁.left ⁻¹ᵁ D ⊓ u₂.left ⁻¹ᵁ D : (T ⊗ A).left.Opens) : Set (T ⊗ A).left).Nonempty :=
    nonempty_preirreducible_inter (u₁.left ⁻¹ᵁ D).isOpen (u₂.left ⁻¹ᵁ D).isOpen (ne _ _ e₁) (ne _ _ e₂)
  have : LocallyOfFiniteType (X := (T ⊗ A).left) (Y := Spec (CommRingCat.of K)) (fst T A).left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst t A.hom))
  obtain ⟨σ, hσ, hm⟩ := exists_section_mem (Y := (T ⊗ A).left) (fst T A).left _ hne
  let σ' : T ⟶ T ⊗ A := Over.homMk σ (by
    rw [← Over.w (fst T A), ← Category.assoc]
    exact (congrArg (· ≫ T.hom) hσ).trans (Category.id_comp _))
  have hf : σ' ≫ fst T A = 𝟙 T := Over.OverMorphism.ext hσ
  have f₁ : σ' ≫ u₁ = ptSecT A ((σ' ≫ snd T A) * x) := by
    simp [u₁, ptSecT, comp_lift, MonObj.comp_mul, hf, reassoc_of% hf]
  have f₂ : σ' ≫ u₂ = ptSecT A ((σ' ≫ snd T A)⁻¹ * c) := by
    simp [u₂, ptSecT, comp_lift, MonObj.comp_mul, GrpObj.comp_inv, hf, reassoc_of% hf]
  refine ⟨σ' ≫ snd T A, fun p => ?_, fun p => ?_⟩
  · rw [← f₁]; exact (hm p).1
  · rw [← f₂]; exact (hm p).2

variable {L : LB A.left}

theorem unitAt_of_local (hL : L.IsLB) {T : Over S} [Subsingleton T.left] {I : Type} [Fintype I]
    (φ : I → ((T ⊗ A).left ⟶ A.left)) (ε : I → ℤ) (p : T.left) (V : T.left.Opens) (hp : p ∈ V)
    (c : LB.Gen ((LB.LinComb L φ ε).pull ((fst T A).left ⁻¹ᵁ V).ι)) (hc : c.IsGen) (y : (T ⊗ A).left) :
    UnitAt L φ ε y := by
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by rw [Subsingleton.elim q p]; exact hp
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (T ⊗ A).left) ((fst T A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst T A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr hL ?_ ⟨pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem unitAt_transl (hL : L.IsLB) {T : Over S} (θ : LB.Sec (LPow A L 1 T)) (k : (LPow A L 1 T).ι)
    (a : T ⟶ A) (y : (T ⊗ A).left) (hy : (translT A a).left y ∈ (T ⊗ A).left.basicOpen (θ.f k)) :
    UnitAt L (K := Fin 1) (fun _ => (translPt A a).left) (fun _ => 1) y := by
  refine UnitAt.congr hL ?_ ⟨pullSec θ (translT A a).left, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Over.comp_left, translT, lift_snd]
  · rw [sval_pullSec θ _ (𝟙 _) y hJ]
    exact isUnit_sval θ _ y hJ k hy

theorem exists_value_one (hL : L.IsLB) {T : Over S} [Subsingleton T.left] (n : ℤ) (x : T ⟶ A) (p : T.left)
    (h : UnitAt L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => n) ((ptSecT A x).left p)) :
    ∃ (s : LB.Sec (LPow A L n T))
      (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => n))),
      τ.IsGen ∧ IsValueAt A L n s x τ 1 := by
  obtain ⟨s, hs⟩ := h
  choose I hI using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ ((ptSecT A x).left p))
  have hm := Good.mem hI (fun _ : Fin 1 => (snd T A).left) (𝟙 _)
  have hb : (ptSecT A x).left p ∈ (T ⊗ A).left.basicOpen (s.f (fun _ => I (𝟙 _ ≫ (snd T A).left))) :=
    ((T ⊗ A).left.mem_basicOpen _ _ hm).2 ((congrArg IsUnit (gs_eq (𝟙 _) _ _ hm _)).mp (hs I hI))
  let s' := GlobalTheory.EvVal.pullSec L (fun _ : Fin 1 => (snd T A).left) (fun _ => n) (ptSecT A x).left
    (fun _ => x.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd]) (val_le A L x) s
  have hu : ∀ j, IsUnit (s'.f j) := fun j => T.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun q hq => by
    obtain rfl : q = p := Subsingleton.elim _ _
    choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ q)
    have u := isUnit_sval s (ptSecT A x).left q hJ _ hb
    have e := sec_trans s (ptSecT A x).left q (val_le A L x j hq) (Good.mem hJ _ (ptSecT A x).left)
    have e' : gs (𝟙 T.left) q (LB.wchart L (fun _ : Fin 1 => x.left) j) (s'.f j) =
        gs (𝟙 T.left ≫ (ptSecT A x).left) q (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (s.f j) :=
      (gs_res (𝟙 T.left) q (val_le A L x j) hq _).trans
        (gs_pull (𝟙 T.left) (ptSecT A x).left q (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j)
          (val_le A L x j hq) (s.f j))
    rw [Category.id_comp] at e'
    exact (congrArg IsUnit ((gs_eq (𝟙 T.left) q (LB.wchart L (fun _ : Fin 1 => x.left) j) hq _).symm.trans
      (e'.trans e))).mpr ((Units.isUnit _).mul u)
  refine ⟨s, ⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s'.compat i j), fun j => ?_⟩
  rw [map_one, _root_.one_mul]
  rfl

end

theorem exists_sec_value_isUnit :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left), ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 1 ≤ n → Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L n (Over.mk t)) = n ^ P.g) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 2 ≤ n → ∀ x : Over.mk t ⟶ P.A, ∃ (s : LB.Sec (LPow P.A P.L n (Over.mk t))) (τ : LB.Gen (LB.LinComb P.L (Y := (Over.mk t).left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (v : Γ((Over.mk t).left, ⊤)), τ.IsGen ∧ IsValueAt P.A P.L n s x τ v ∧ IsUnit v := by
  intro hGI hsq hH0 _ S _ P K _ _ t n hn x
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := hGI _ _ _ inferInstance inferInstance
  have : IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 := hH0 S P K t 1 le_rfl
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let p : (Over.mk t).left := IsLocalRing.closedPoint K
  let y := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    unitAt_transl P.isLB θ k a y (by
      rw [← ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hsq S P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e1 : translPt P.A (1 : Over.mk t ⟶ P.A) = snd _ _ := by
    rw [translPt_eq, MonObj.comp_one, _root_.one_mul]
  obtain ⟨s, τ, hτ, hv⟩ := exists_value_one P.isLB ((m + 2 : ℕ) : ℤ) x p
    (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by
      simp [Fin.sum_univ_succ, e1]
      module) (main m 1))
  exact ⟨s, τ, 1, hτ, hv, isUnit_one⟩

end GlobalTheory.NoBasePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TwistedPowTranslate
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistTranslate

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

section Gen

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem exists_gen_of_sec (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (hs : ∀ (y : Y) J, Good L y J → IsUnit (sval s (𝟙 Y) y J)) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    exact (congrArg IsUnit ((gs_eq (𝟙 Y) y (LB.wchart L φ j) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul (hs y J hJ))
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j)⟩

theorem gen_congr (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (hf : FormEq φ ε φ' ε') (h : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ' ε'), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := exists_gen hL hf t ht
  exact ⟨t', ht'⟩

theorem gen_mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) (h' : ∃ t : LB.Gen (LB.LinComb L φ' ε'), t.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  exact ⟨_, DVR.mulGen_isGen L φ ε φ' ε' t t' ht ht'⟩

theorem gen_of_pull_top (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (W : Y.Opens) (hW : ∀ y, y ∈ W)
    (c : LB.Gen ((LB.LinComb L φ ε).pull W.ι)) (hc : c.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := Y) W.ι c hc
  let e := IsOpenImmersion.lift W.ι (𝟙 Y)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; exact hW _)
  have he : e ≫ W.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine gen_congr hL ?_ (exists_gen_of_sec hL (pullSec s e) fun y J hJ => ?_)
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

end Gen

variable {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)

theorem gen_square (hsq : ∀ (x y : Over.mk t ⟶ P.A) (p : (Over.mk t).left), ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd (Over.mk t) P.A).left,
        (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull
          ((fst (Over.mk t) P.A).left ⁻¹ᵁ V).ι), c.IsGen)
    (x y : Over.mk t ⟶ P.A) :
    ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]), w.IsGen := by
  obtain ⟨V, hpV, c, hc⟩ := hsq x y (IsLocalRing.closedPoint K)
  refine gen_of_pull_top P.isLB _ (fun z => ?_) c hc
  show (fst (Over.mk t) P.A).left z ∈ V
  rw [spec_pt_eq ((fst (Over.mk t) P.A).left z) (IsLocalRing.closedPoint K)]
  exact hpV

theorem gen_iter (hsq : ∀ (x y : Over.mk t ⟶ P.A) (p : (Over.mk t).left), ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd (Over.mk t) P.A).left,
        (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull
          ((fst (Over.mk t) P.A).left ⁻¹ᵁ V).ι), c.IsGen)
    (d : Over.mk t ⟶ P.A) :
    ∀ n : ℕ, ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left,
      (translPt P.A (d ^ (n + 1))).left, (translPt P.A d).left] ![(n : ℤ), 1, -((n : ℤ) + 1)]), w.IsGen
  | 0 => by
    refine gen_congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (gen_mul (gen_square P t hsq d d) ⟨_, DVR.invGen_isGen _ _ _ _ (gen_square P t hsq d d).choose_spec⟩)
    simp [Fin.sum_univ_succ]
    module
  | n + 1 => by
    refine gen_congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (gen_mul (gen_iter hsq d n) (gen_square P t hsq (d ^ (n + 1)) d))
    have e : d ^ (n + 1) * d = d ^ (n + 1 + 1) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

theorem exists_root [IsAlgClosed K] (r : ℕ) [IsFinite (mulA P.A r).left] [Surjective (mulA P.A r).left]
    (c : Over.mk t ⟶ P.A) : ∃ d : Over.mk t ⟶ P.A, d ^ r = c := by
  obtain ⟨u, hu⟩ := H1.SectionDivision.exists_section (k := K) (pullback.snd (mulA P.A r).left c.left)
  have hb' : (u ≫ pullback.fst (mulA P.A r).left c.left) ≫ (mulA P.A r).left = c.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]; exact Category.id_comp _
  have hw : (u ≫ pullback.fst (mulA P.A r).left c.left) ≫ P.A.hom = (Over.mk t).hom := by
    rw [← Over.w (mulA P.A r), ← Category.assoc, hb']; exact Over.w c
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk t ⟶ P.A, b ^ r = b ≫ mulA P.A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'

end GlobalTheory.TwistTranslate

namespace GlobalTheory

theorem twisted_pow_translate :
    (∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left), ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (q : ℕ), 1 ≤ q → ∀ c : Over.mk t ⟶ P.A, ∃ d : Over.mk t ⟶ P.A, d ^ q = c ∧ ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left, (translPt P.A c).left, (translPt P.A d).left] ![(q : ℤ) - 1, 1, -(q : ℤ)]), w.IsGen := by
  intro hsq hmul S _ P K _ _ t q hq c
  obtain ⟨hfin, -, hsurj, -⟩ := hmul S P q hq
  obtain ⟨d, rfl⟩ := TwistTranslate.exists_root P t q c
  refine ⟨d, rfl, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  refine TwistTranslate.gen_congr P.isLB (H1.SquareUnits.formEq_of_add fun U _ hh => ?_)
    (TwistTranslate.gen_iter P t (hsq S P _) d n)
  simp [Fin.sum_univ_succ]

end GlobalTheory
end
end

