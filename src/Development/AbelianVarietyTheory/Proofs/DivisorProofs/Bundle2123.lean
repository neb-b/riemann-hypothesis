module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureDetOneFactorNearIdentityLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFlagHodgeIndexVanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleDescendsOnTripleOverlaps
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct
namespace GlobalTheory.LBDescent.CocycleTensor

theorem appLE_congr_hom {A B : Scheme.{0}} {g₁ g₂ : A ⟶ B} (hg : g₁ = g₂) (U : B.Opens) (W : A.Opens)
    (e₁ : W ≤ g₁ ⁻¹ᵁ U) (e₂ : W ≤ g₂ ⁻¹ᵁ U) : g₁.appLE U W e₁ = g₂.appLE U W e₂ := by
  subst hg; rfl

theorem germ_appLE_gm {A B : Scheme.{0}} (g : A ⟶ B) {U U' : B.Opens} (W : A.Opens) (e : W ≤ g ⁻¹ᵁ U)
    (hUU' : U ≤ U') (w : A) (hw : w ∈ W) (a : Γ(B, U')ˣ) :
    (A.presheaf.germ W w hw).hom ((g.appLE U W e).hom (res hUU' a).val) = (gm g w U' a).val :=
  (TopCat.Presheaf.germ_res_apply A.presheaf (homOfLE e) w hw ((g.app U).hom (res hUU' a).val)).trans
    ((gm_val g w U (e hw) (res hUU' a)).symm.trans (congrArg Units.val (gm_res g w hUU' (e hw) a)))

set_option maxHeartbeats 1600000 in
theorem cocycle_tensor_of_pointwise : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (V V₀ : Y.Opens), IsAffineOpen V₀ →
    ∀ (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀)
      (hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
    (∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c) →
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    ∀ e : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀) ≃+* Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
      (∀ a b : Γ(X, f ⁻¹ᵁ V₀), e (a ⊗ₜ b) =
        ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a * ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b) →
      Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) *
          Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) := by
  intro X Y f _ V V₀ hV₀ h hle c hc e he
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  have hcond : ∀ z : ↥(pullback f f), f ((pullback.fst f f) z) = f ((pullback.snd f f) z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hq : ∀ w : ↥(Triple f), (pullback.snd f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w) = (pullback.fst f f) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) w) := fun w => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have h1 : (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) ≤ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := fun z hz => by
    show f ((pullback.fst f f) z) ∈ V₀
    rw [hcond]; exact hz
  have hleG : ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ≤ (pullback.fst (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) := fun w hw => by
    show f ((pullback.snd f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w)) ∈ V₀
    rw [hq]; exact hw
  have hp1 : pr13 f ≫ (pullback.fst f f) = (pullback.fst (pullback.snd f f) (pullback.fst f f)) ≫ (pullback.fst f f) := pullback.lift_fst _ _ _
  have hp2 : pr13 f ≫ (pullback.snd f f) = (pullback.snd (pullback.snd f f) (pullback.fst f f)) ≫ (pullback.snd f f) := pullback.lift_snd _ _ _
  have h13 : ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ≤ pr13 f ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := fun w hw => by
    show f ((pullback.fst f f) (pr13 f w)) ∈ V₀
    have e13 : (pullback.fst f f) (pr13 f w) = (pullback.fst f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w) :=
      (Scheme.Hom.comp_apply _ _ w).symm.trans ((congrArg (fun g => g w) hp1).trans (Scheme.Hom.comp_apply _ _ w))
    rw [e13]
    exact h1 (hleG hw)
  have h2 : (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) ≤ (pullback.fst f f) ⁻¹ᵁ f ⁻¹ᵁ V := h1.trans hle
  have hP := Out.GtBCPf.isPushout_appLE (IsPullback.of_hasPullback (pullback.snd f f) (pullback.fst f f)) inferInstance
    (hV₀.preimage f) ((hV₀.preimage f).preimage (pullback.fst f f)) le_rfl hleG
  have e1 : ∀ s : Γ(X, f ⁻¹ᵁ V₀), e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom s) = 1 ⊗ₜ s := fun s => by
    rw [e.symm_apply_eq, he, map_one, _root_.one_mul]
  have e2 : ∀ s : Γ(X, f ⁻¹ᵁ V₀), e.symm (((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom s) = s ⊗ₜ 1 := fun s => by
    rw [e.symm_apply_eq, he, map_one, _root_.mul_one]
  let m₁ : Γ(pullback f f, (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ⟶ CommRingCat.of ((Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) :=
    CommRingCat.ofHom ((Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))).toRingHom.comp (e.symm.toRingHom.comp ((pullback f f).presheaf.map (homOfLE h).op).hom))
  let m₂ : Γ(pullback f f, (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ⟶ CommRingCat.of ((Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) :=
    CommRingCat.ofHom ((Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))).toRingHom.comp e.symm.toRingHom)
  have cond : (pullback.snd f f).app (f ⁻¹ᵁ V₀) ≫ m₁ = (pullback.fst f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) le_rfl ≫ m₂ := by
    ext s
    show (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom s)) = (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) le_rfl).hom s))
    rw [Scheme.Hom.appLE_eq_app, e1, e2]
    simp
  let Ψ := hP.desc m₁ m₂ cond
  have hΨ1 : ∀ y, Ψ.hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom y) = m₁.hom y := fun y =>
    congrArg (fun k => k.hom y) (hP.inl_desc m₁ m₂ cond)
  have hΨ2 : ∀ y, Ψ.hom (((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom y) = m₂.hom y := fun y =>
    congrArg (fun k => k.hom y) (hP.inr_desc m₁ m₂ cond)
  have ka : ∀ a : Γ(X, f ⁻¹ᵁ V₀), ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a) =
      ((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a) := fun a => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom a) ((Scheme.Hom.appLE_comp_appLE (pr13 f) (pullback.fst f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) le_rfl h13).trans
      ((appLE_congr_hom hp1 (f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) _ _).trans (Scheme.Hom.appLE_comp_appLE (pullback.fst (pullback.snd f f) (pullback.fst f f)) (pullback.fst f f) (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h1 hleG).symm))
  have kb : ∀ b : Γ(X, f ⁻¹ᵁ V₀), ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b) =
      ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b) := fun b => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom b) ((Scheme.Hom.appLE_comp_appLE (pr13 f) (pullback.snd f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h h13).trans
      ((appLE_congr_hom hp2 (f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) _ _).trans (Scheme.Hom.appLE_comp_appLE (pullback.snd (pullback.snd f f) (pullback.fst f f)) (pullback.snd f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h le_rfl).symm))
  have ra : ∀ a : Γ(X, f ⁻¹ᵁ V₀), ((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a) =
      ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a := fun a => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom a) (Scheme.Hom.appLE_map (pullback.fst f f) h1 (homOfLE h).op)
  have hΨ3 : ∀ t, Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (e t)) = (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b =>
      rw [he, map_mul, map_mul, ka, kb, hΨ1, hΨ2]
      show (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a))) *
        (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b)) = _
      rw [ra, e1, e2]
      simp
  have hABC : ((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val * ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val =
      ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val := by
    apply TopCat.Presheaf.section_ext (Triple f).sheaf ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀))
    intro w hw
    have hw1 : (pullback.fst (pullback.snd f f) (pullback.fst f f)) w ∈ (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) := hleG hw
    have hw13 : pr13 f w ∈ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := h13 hw
    have key := congrArg Units.val (hc w (hle (h1 hw1)))
    show ((Triple f).presheaf.germ ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) w hw).hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val * ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val) =
      ((Triple f).presheaf.germ ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) w hw).hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val)
    rw [Scheme.Hom.app_eq_appLE]
    refine (RingHom.map_mul _ _ _).trans ?_
    exact (congrArg₂ (· * ·) (germ_appLE_gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) _ hleG h2 w hw c) (germ_appLE_gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) _ _ hle w hw c)).trans
      ((Units.val_mul _ _).symm.trans (key.trans (germ_appLE_gm (pr13 f) _ h13 hle w hw c).symm))
  have hA : (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val) := by
    have hres : ((pullback f f).presheaf.map (homOfLE h).op).hom (res h2 c).val = (res hle c).val := by
      show ((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback f f).presheaf.map (homOfLE h2).op).hom c.val) =
        ((pullback f f).presheaf.map (homOfLE hle).op).hom c.val
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    exact (congrArg (fun y => (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm y)) hres).symm.trans (hΨ1 _).symm
  have hB : (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val) := (hΨ2 _).symm
  have hC : (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val) := by
    exact (hΨ3 (e.symm (res hle c).val)).symm.trans (congrArg (fun y => Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom y)) (e.apply_symm_apply _))
  exact (congrArg₂ (· * ·) hA hB).trans ((map_mul Ψ.hom _ _).symm.trans ((congrArg Ψ.hom hABC).trans hC.symm))

end GlobalTheory.LBDescent.CocycleTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecomposition
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.MassUp

theorem inv_facts {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) :
    (permM (e ρ))ᵀ * A ρ * mat x (σ ρ) = 1 ∧ mat x (σ ρ) * ((permM (e ρ))ᵀ * A ρ) = 1 ∧
    A ρ * (mat x (σ ρ) * (permM (e ρ))ᵀ) = 1 ∧ mat x (σ ρ) * (permM (e ρ))ᵀ * A ρ = 1 := by
  have h0 := (hI ρ).2
  have h1 : (permM (e ρ))ᵀ * A ρ * mat x (σ ρ) = 1 := by rw [Matrix.mul_assoc, h0, transpose_mul_permM]
  have h2 : mat x (σ ρ) * ((permM (e ρ))ᵀ * A ρ) = 1 := mul_eq_one_comm.1 h1
  refine ⟨h1, h2, ?_, by rw [Matrix.mul_assoc, h2]⟩
  rw [← Matrix.mul_assoc, h0, permM_mul_transpose]

theorem det_ne {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) : G.det ≠ 0 := by
  obtain ⟨-, -, h3, h4⟩ := inv_facts hI ρ
  set B := mat x (σ ρ) * (permM (e ρ))ᵀ
  have hJ := GlobalTheory.UpqTopology.jpq_sq (P := p ρ) (Q := q ρ)
  have key : (-(G.map (σ ρ).1)ᵀ) * (B * Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ) = 1 := by
    rw [← (hI ρ).1]
    calc (A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ * (B * Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ)
        = (A ρ)ᴴ * (Formalism.UG.Jpq (p ρ) (q ρ) * ((A ρ * B) * (Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [h3, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.UG.Jpq (p ρ) (q ρ)), hJ, Matrix.one_mul,
            ← Matrix.conjTranspose_mul, h4, Matrix.conjTranspose_one]
  have hd := Matrix.det_ne_zero_of_right_inverse key
  rw [Matrix.det_neg, Matrix.det_transpose] at hd
  have hd' : (G.map (σ ρ).1).det ≠ 0 := fun h => hd (by rw [h, mul_zero])
  intro h0
  apply hd'
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem perm_conj {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix ι ι ℂ) (a b : Fin r) :
    ((permM e)ᵀ * M * permM e) a b = M (e.symm a) (e.symm b) := by
  simp [Matrix.mul_apply, permM, Equiv.apply_eq_iff_eq_symm_apply]

theorem preimage_frBall : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G), IsIdent p q Ψ G x σ A e → IsProj p q Ψ G σ A a₀ π → ∀ ε : ℝ, π ⁻¹' frBall Ψ G x ε = Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) | ∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε}) := by
  intro E _ _ _ r κ p q Ψ G x σ A e a₀ π hI hP ε
  ext b
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq, frBall]
  have key : ∀ ρ, (mat x (σ ρ))⁻¹ * (((π b).1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x (σ ρ) - 1
      = (permM (e ρ))ᵀ * (sMat (a₀ ρ) (b ρ) - 1) * permM (e ρ) := by
    intro ρ
    obtain ⟨h1, -, -, -⟩ := inv_facts hI ρ
    have hinv : (mat x (σ ρ))⁻¹ = (permM (e ρ))ᵀ * A ρ := Matrix.inv_eq_left_inv h1
    rw [hinv, Matrix.mul_assoc (permM (e ρ))ᵀ (A ρ), hP b ρ]
    simp only [Matrix.mul_assoc, (hI ρ).2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      transpose_mul_permM]
  constructor
  · intro h ρ i j
    have := h (σ ρ) (e ρ i) (e ρ j)
    rwa [key ρ, perm_conj, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  · intro h τ i j
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    rw [key ρ, perm_conj]
    exact h ρ _ _
theorem exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), IsIdent p q Ψ G x σ A e → ∀ s : realSU Ψ G, ∃ b₀ : ∀ ρ, UpqT (p ρ) (q ρ), ∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  intro E _ _ _ r κ p q Ψ G x σ A e hI s
  have key : ∀ ρ, ∃ b : UpqT (p ρ) (q ρ), UpqT.mat b =
      A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat x (σ ρ) * (permM (e ρ))ᵀ) := by
    intro ρ
    rw [← Set.mem_range, GlobalTheory.UpqTopology.range_mat]
    show _ = _
    set Sm := ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
    set Bm := mat x (σ ρ) * (permM (e ρ))ᵀ
    have hmem := ((GlobalTheory.SUVol.DensOne.mem_realSU_iff Ψ G s.1).1 s.2 (σ ρ)).1
    have h2 : Smᴴ * (G.map (σ ρ).1)ᵀ * Sm = (G.map (σ ρ).1)ᵀ := by
      have := congrArg Matrix.transpose hmem
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
      rw [Matrix.mul_assoc]
      exact this
    calc (A ρ * Sm * Bm)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * (A ρ * Sm * Bm)
        = Bmᴴ * (Smᴴ * ((A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ) * Sm) * Bm := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Bmᴴ * ((A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ) * Bm := by
          rw [(hI ρ).1, Matrix.mul_neg, Matrix.neg_mul, h2]
      _ = (A ρ * Bm)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * (A ρ * Bm) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.UG.Jpq (p ρ) (q ρ) := by
          rw [(inv_facts hI ρ).2.2.1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  choose b hb using key
  refine ⟨b, fun ρ => ?_⟩
  rw [hb ρ, Matrix.mul_assoc (A ρ * _), (inv_facts hI ρ).2.2.2, Matrix.mul_one]
theorem constant_bound : ∀ (f r : ℕ) (ε : ℝ), 1 ≤ f → 1 ≤ r → 0 < ε → ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ f ≤ (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ (f * r ^ 2) * ((ε / (2 * ((f : ℝ) * (r : ℝ) ^ 2))) ^ (f * (r ^ 2 - 1)) / 2) := by
  intro f r ε hf hr hε
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hN : 1 ≤ f * r ^ 2 := by have := Nat.one_le_pow 2 r hr; nlinarith
  have hnN : f * (r ^ 2 - 1) ≤ f * r ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hL : ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ f =
      (200 * (r : ℝ)) ^ (f * r ^ 2) * ε ^ (f * (r ^ 2 - 1)) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (r ^ 2) f, mul_comm (r ^ 2 - 1) f]
  rw [hL, div_pow]
  generalize hN' : f * r ^ 2 = N at hN hnN
  generalize hn' : f * (r ^ 2 - 1) = n at hnN
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ hr'
  have ha1 : (1 : ℝ) ≤ 2 * ((f : ℝ) * (r : ℝ) ^ 2) := by nlinarith
  generalize ha : 2 * ((f : ℝ) * (r : ℝ) ^ 2) = a at ha1
  have ha0 : 0 < a := by linarith
  have e1 : 1000 * (f : ℝ) * (r : ℝ) ^ 3 = (5 / 2) * (200 * (r : ℝ) * a) := by rw [← ha]; ring
  have han : a ^ n ≤ a ^ N := pow_le_pow_right₀ ha1 hnN
  have hq : 0 ≤ 200 * (r : ℝ) * a := mul_nonneg (by positivity) ha0.le
  have h52 : (2 : ℝ) ≤ (5 / 2) ^ N := by
    calc (2 : ℝ) ≤ 5 / 2 := by norm_num
      _ = (5 / 2) ^ 1 := (pow_one _).symm
      _ ≤ (5 / 2) ^ N := pow_le_pow_right₀ (by norm_num) hN
  have key : (200 * (r : ℝ)) ^ N * a ^ N * 2 ≤ (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ N := by
    rw [e1, mul_pow (5 / 2 : ℝ), ← mul_pow (200 * (r : ℝ)) a N]
    have hp : 0 ≤ (200 * (r : ℝ) * a) ^ N := pow_nonneg hq _
    nlinarith
  have hεn : 0 < ε ^ n := pow_pos hε _
  have han0 : 0 < a ^ n := pow_pos ha0 _
  have hw : 0 ≤ ε ^ n / a ^ n / 2 := by positivity
  calc (200 * (r : ℝ)) ^ N * ε ^ n = ((200 * (r : ℝ)) ^ N * a ^ n * 2) * (ε ^ n / a ^ n / 2) := by
        field_simp
    _ ≤ ((200 * (r : ℝ)) ^ N * a ^ N * 2) * (ε ^ n / a ^ n / 2) := by
        gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_right key hw

theorem massUp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) (m : ∀ ρ, Measure (UpqT (p ρ) (q ρ))), 1 ≤ r → 1 ≤ Ψ.card → IsIdent p q Ψ G x σ A e → Continuous π → IsProj p q Ψ G σ A a₀ π → (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) → (∀ ρ, IsMinf (m ρ)) → ∀ S : Set (realSU Ψ G), MeasurableSet S → Measure.pi m (π ⁻¹' S) ≤ ENNReal.ofReal ((1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ π m hr hΨ hI hπc hP hT hm S hS
  classical
  haveI : ∀ ρ, IsTopologicalGroup (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  haveI : ∀ ρ, LocallyCompactSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.1
  haveI : ∀ ρ, SecondCountableTopology (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.1
  haveI : ∀ ρ, BorelSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.1
  haveI : ∀ ρ, (m ρ).IsHaarMeasure := fun ρ => (hm ρ).1

  have hcard : Fintype.card κ = Ψ.card := by
    rw [Fintype.card_congr σ]; simp
  have hne : Nonempty κ := by
    rw [← Fintype.card_pos_iff, hcard]; omega
  obtain ⟨ρ₀⟩ := hne
  have hG : G.det ≠ 0 := det_ne hI ρ₀
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    exact Matrix.det_ne_zero_of_right_inverse (inv_facts hI ρ).2.1
  have hpq : ∀ ρ, p ρ + q ρ = r := by
    intro ρ; simpa using Fintype.card_congr (e ρ)
  have hπm : Measurable π := hπc.measurable
  set μ := Measure.pi m with hμ
  set ν := μ.map π with hν

  haveI hinv : ν.IsMulLeftInvariant := by
    constructor
    intro s
    obtain ⟨b₀, hb₀⟩ := exists_lift E r κ p q Ψ G x σ A e hI s
    rw [hν, Measure.map_map (measurable_const_mul s) hπm]
    have h : (fun y => s * y) ∘ π = π ∘ (fun b => b₀ * b) := funext fun b => (hT s b₀ hb₀ b).symm
    rw [h, ← Measure.map_map hπm (measurable_const_mul b₀), map_mul_left_eq_self]

  have hopen : ∀ ε, IsOpen (frBall Ψ G x ε) := by
    intro ε
    have hc : ∀ τ a b, Continuous fun s : realSU Ψ G =>
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ := by
      intro τ a b
      have h1 : Continuous fun s : realSU Ψ G => ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) :=
        Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)
      exact ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).sub continuous_const).matrix_elem a b).norm
    have : frBall Ψ G x ε = ⋂ τ, ⋂ a, ⋂ b, {s : realSU Ψ G |
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε} := by
      ext s; simp [frBall]
    rw [this]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b => isOpen_lt (hc τ a b) continuous_const
  have h1mem : ∀ ε, 0 < ε → (1 : realSU Ψ G) ∈ frBall Ψ G x ε := by
    intro ε hε τ a b
    have : (mat x τ)⁻¹ * ((((1 : realSU Ψ G).1 τ : GL (Fin r) ℂ)) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = 1 := by
      simp [Matrix.nonsing_inv_mul _ (hx τ).isUnit]
    rw [this, sub_self]; simpa using hε
  have hplace := fun ρ => _root_.GlobalTheory.CovTop.VolUp.OneMeasure.measure_sMat_near_le (p ρ) (q ρ) (a₀ ρ) (m ρ) (hm ρ)
  choose εp hεp hbp using hplace
  obtain ⟨εl, hεl, hbl⟩ := _root_.GlobalTheory.CovTop.VolUp.LowBall.riemHaar_frBall_ge E r Ψ G x hr hG hx
  set δ := Finset.univ.inf' ⟨ρ₀, Finset.mem_univ _⟩ εp with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun ρ _ => hεp ρ
  set ε := min δ εl / 2 with hεdef
  have hεm : ε < min δ εl := half_lt_self (lt_min hδ hεl)
  have hε : 0 < ε := half_pos (lt_min hδ hεl)
  have hεδ : ∀ ρ, ε < εp ρ := fun ρ =>
    lt_of_lt_of_le (lt_of_lt_of_le hεm (min_le_left _ _)) (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hεl' : ε < εl := lt_of_lt_of_le hεm (min_le_right _ _)
  set U := ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ Ψ.card with hU
  have hνB : ν (frBall Ψ G x ε) ≤ ENNReal.ofReal U := by
    rw [hν, Measure.map_apply hπm (hopen ε).measurableSet,
      preimage_frBall E r κ p q Ψ G x σ A e a₀ π hI hP ε, hμ, Measure.pi_pi]
    calc _ ≤ ∏ _ρ : κ, ENNReal.ofReal ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) :=
          Finset.prod_le_prod' fun ρ _ => by
            have := hbp ρ ε hε (hεδ ρ)
            rw [hpq ρ] at this
            exact this
      _ = ENNReal.ofReal U := by
          rw [Finset.prod_const, Finset.card_univ, hcard, ← ENNReal.ofReal_pow (by positivity)]
  have hfinB : ν (frBall Ψ G x ε) < ∞ := lt_of_le_of_lt hνB ENNReal.ofReal_lt_top
  haveI : IsLocallyFiniteMeasure ν := ⟨fun g => ⟨(fun h => g⁻¹ * h) ⁻¹' frBall Ψ G x ε,
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by
      show frBall Ψ G x ε ∈ nhds (g⁻¹ * g)
      rw [inv_mul_cancel]; exact (hopen ε).mem_nhds (h1mem ε hε)),
    by rw [measure_preimage_mul]; exact hfinB⟩⟩
  haveI hH : (riemHaar Ψ G x).IsHaarMeasure :=
    (GlobalTheory.SUVol.DensOne.tangentHaar_riemLie (Ψ := Ψ) (G := G) (hG := hG) (x := x) (hx := hx)).1
  have hc := Measure.isMulLeftInvariant_eq_smul ν (riemHaar Ψ G x)
  set c := ν.haarScalarFactor (riemHaar Ψ G x) with hcdef
  have hL := hbl ε hε hεl'
  have hf : (0 : ℝ) < Ψ.card := by exact_mod_cast hΨ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set L := (ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2 with hLdef
  have hLpos : 0 < L := div_pos (pow_pos (div_pos hε (mul_pos two_pos (mul_pos hf (pow_pos hr' 2)))) _) two_pos
  have hcL : (c : ℝ) * L ≤ U := by
    have h1 : (c : ℝ≥0∞) * ENNReal.ofReal L ≤ ENNReal.ofReal U := by
      calc (c : ℝ≥0∞) * ENNReal.ofReal L ≤ c * riemHaar Ψ G x (frBall Ψ G x ε) := mul_le_mul_of_nonneg_left hL (zero_le)
        _ = ν (frBall Ψ G x ε) := by
          conv_rhs => rw [hc]
          rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        _ ≤ _ := hνB
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg (mul_nonneg (by positivity) (pow_nonneg hε.le _)) _)).1 h1
  have hUC := constant_bound Ψ.card r ε hΨ hr hε
  have hcC : (c : ℝ) ≤ (1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2) :=
    le_of_mul_le_mul_right (hcL.trans hUC) hLpos
  rw [← Measure.map_apply hπm hS, ← hν, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcC' : (c : ℝ≥0∞) ≤ ENNReal.ofReal ((1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2)) := by
    rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hcC
  exact mul_le_mul_of_nonneg_right hcC' (zero_le)

end GlobalTheory.CovTop.VolUp.MassUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFirstOrderDeformation
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan.KSUniv

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

noncomputable def reparam {K : Type} [Field K] (F : Type) [Field F] [Algebra F K] {ι : Type} [Fintype ι]
    (P : Matrix ι ι K) : TrivSqZeroExt K (ι → K) →ₐ[F] TrivSqZeroExt K (ι → K) :=
  (TrivSqZeroExt.map (Matrix.mulVecLin P.transpose)).restrictScalars F

theorem isTanX_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K}
    {ι : Type} [Fintype ι] {X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X} (h1 : X ≫ Xo.s = sOf c _)
    (h2 : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x) (M : ι → K) :
    GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, sOf, sOf, spMap_comp_spMap']
    congr 1
    rw [← RingHom.comp_assoc]
    congr 1
    exact (GlobalTheory.FlagTan.dir c M).comp_algebraMap
  · rw [← Category.assoc, spMap_comp_spMap', ← h2]
    congr 2
    ext z
    simp

theorem dir_comp_reparam {K : Type} [Field K] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Level H} {c : Coeff l} [Algebra c.F K] {ι : Type} [Fintype ι] (P : Matrix ι ι K) (M : ι → K) :
    (GlobalTheory.FlagTan.dir c M).toRingHom.comp (reparam c.F P).toRingHom = (GlobalTheory.FlagTan.dir c (P.mulVec M)).toRingHom := by
  ext z
  · simp [reparam]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GlobalTheory.FlagTan.snd_dir, reparam,
      AlgHom.restrictScalars_apply, GlobalTheory.FlagTan.fst_dir, TrivSqZeroExt.snd_map, Matrix.mulVecLin_apply]
    have e := Matrix.dotProduct_mulVec z.snd P M
    rw [← Matrix.mulVec_transpose] at e
    simpa [dotProduct, mul_comm] using e.symm


open GlobalTheory.FlagTan in
theorem ksUniv : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧ ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  classical
  obtain ⟨X₀, h1, h2, hinj⟩ :=
    _root_.GlobalTheory.TanBasis.exists_point_tanBasis E H Dw l Xo c K y (HIx Dw (psiSet H)) (card_HIx (isHalf_psiSet H))
  choose N hN using fun k : HIx Dw (psiSet H) =>
    _root_.GlobalTheory.KSExist.ksExist hP E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 (Pi.single k 1))
  have hL := _root_.GlobalTheory.FlagTan.isKS_dir_sum hP E H Dw l Xo c K y _ X₀ hpq h1 h2 N hN
  let L : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K) := Fintype.linearCombination K N
  have hLa : ∀ M, L M = ∑ k, M k • N k := fun M => Fintype.linearCombination_apply _ _ _
  have h0 : spMap (dir c (0 : HIx Dw (psiSet H) → K)).toRingHom ≫ X₀ =
      spMap (algebraMap K (DualNumber K)) ≫ y.x := by
    rw [← h2, ← Category.assoc, spMap_comp_spMap']
    congr 2
    ext z <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have Linj : Function.Injective L := (injective_iff_map_eq_zero L).2 fun M hM =>
    hinj ((_root_.GlobalTheory.FlagTan.eq_const_of_isKS_zero hP hG E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 M)
      (by rw [← hM, hLa]; exact hL M)).trans h0.symm)
  let e := LinearEquiv.ofInjectiveEndo L Linj
  let P := LinearMap.toMatrix' (e.symm : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K))
  have hP' : ∀ M, P.mulVec M = e.symm M := fun M => LinearMap.toMatrix'_mulVec _ M
  refine ⟨spMap (reparam c.F P).toRingHom ≫ X₀, ?_, ?_, fun M => ?_⟩
  · rw [Category.assoc, h1, sOf, spMap_comp_spMap']
    congr 1
    rw [← RingHom.comp_assoc]
    congr 1
    exact (reparam c.F P).comp_algebraMap
  · rw [← Category.assoc, spMap_comp_spMap', ← h2]
    congr 2
    ext z
    simp [reparam]
  · rw [← Category.assoc, spMap_comp_spMap', dir_comp_reparam, hP']
    have := hL (e.symm M)
    rwa [← hLa, show L (e.symm M) = M from e.apply_symm_apply M] at this

end GlobalTheory.FlagTan.KSUniv
end

