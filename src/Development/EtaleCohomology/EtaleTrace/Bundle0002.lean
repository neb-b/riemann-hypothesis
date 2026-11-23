module

public import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
public import Development.EtaleCohomology.KummerTheory.Bundle0001
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleTrace.LKunnethCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.EtaleTrace

theorem bilin_ext_one_tmul (l : ℕ) [Fact l.Prime] {M N W : Type 1} [AddCommGroup M] [Module ℤ_[l] M] [AddCommGroup N]
    [Module ℤ_[l] N] [AddCommGroup W] [Module ℚ_[l] W]
    (f g : (ℚ_[l] ⊗[ℤ_[l]] M) ⊗[ℚ_[l]] (ℚ_[l] ⊗[ℤ_[l]] N) →ₗ[ℚ_[l]] W)
    (h : ∀ x y, f ((1 ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)) = g ((1 ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y))) : f = g := by
  refine TensorProduct.ext' fun u v => ?_
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [TensorProduct.add_tmul, map_add (f := _), map_add (f := _), ha, hb]
  | tmul a x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hc, hd]
    | tmul b y =>
      have e1 : (a ⊗ₜ[ℤ_[l]] x : ℚ_[l] ⊗[ℤ_[l]] M) = a • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have e2 : (b ⊗ₜ[ℤ_[l]] y : ℚ_[l] ⊗[ℤ_[l]] N) = b • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1, e2, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul, map_smul, h]

theorem kun_bijective_of_kunIso (l : ℕ) [Fact l.Prime] {k : Type} [Field k] {X Y : Scheme.{0}} (p : X ⟶ S k) (q : Y ⟶ S k)
    (n : ℤ) (hc : ∀ (a m r : ℤ) (h : a + m = r), IsCup l (pullback p q) h (cupV l (pullback p q) h))
    (hk : LateralTheory.KummerTheory.KunIso l p q n 0) : Function.Bijective (kun l p q n) := by
  obtain ⟨κ, hκ⟩ := hk
  have e : kun l p q n = κ.toLinearMap := by
    refine DirectSum.linearMap_ext _ fun a => ?_
    refine bilin_ext_one_tmul l _ _ fun x y => ?_
    obtain ⟨z, hz, hz'⟩ := hκ a x y
    refine Eq.trans ?_ hz'.symm
    have h1 := hc a (n - a) n (by omega) (pullHl l (sch.map (pullback.fst p q)) a 0 x)
      (pullHl l (sch.map (pullback.snd p q)) (n - a) 0 y) z (fun j => hz j)
    refine Eq.trans ?_ h1
    simp only [kun, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    rfl
  rw [e]
  exact κ.bijective

end LateralTheory.EtaleTrace

end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.LTransferCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.Tr

def Splits {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)) : Prop :=
  ∃ hs : ∀ j, s j ≫ a = x, IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 W) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => W) ⟶ pullback a x)

section
variable (R : Type) [CommRing R]

abbrev fr (X : Scheme.{0}) : Shv R := (free R).obj (yoneda.obj X)

abbrev gen {U X : Scheme.{0}} (x : U ⟶ X) : Sec (fr R X) U := freeGen R (yoneda.obj X) U x

def IsTr {Y X : Scheme.{0}} (a : Y ⟶ X) (τ : fr R X ⟶ fr R Y) : Prop :=
  ∀ (W : Scheme.{0}) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
    Sec.map τ (gen R x) = ∑ j, gen R (s j)

variable {R}

end

def LSpl : Prop := ∀ {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
  (∀ (U : Scheme.{0}) (w : U ⟶ W), Splits a (w ≫ x) m (fun j => w ≫ s j)) ∧
  (∀ y : W ⟶ Y, y ≫ a = x → ∀ t : W, ∃ (O : W.Opens) (j : Fin m), t ∈ O ∧ O.ι ≫ y = O.ι ≫ s j) ∧
  (Nonempty W → Function.Injective s)

def LLoc : Prop := ∀ {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → ∀ (W : Scheme.{0}) (x : W ⟶ X) (t : W),
  ∃ (U : Scheme.{0}) (g : U ⟶ W) (m : ℕ) (s : Fin m → (U ⟶ Y)), Etale g ∧ t ∈ Set.range g ∧ Splits a (g ≫ x) m s

def LTau : Prop := ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a →
  ∃ τ : fr R X ⟶ fr R Y, IsTr R a τ

section Glue
variable (l : ℕ) [Fact l.Prime]

end Glue

end LateralTheory.EtaleTrace.Tr

end
end

