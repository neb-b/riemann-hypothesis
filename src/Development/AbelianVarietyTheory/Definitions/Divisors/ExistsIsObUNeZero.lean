module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.Obs.Model

namespace GlobalTheory.LBObs.Model

section Alg

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀}

variable (hI : I ^ 2 = 0)




end Alg

section Example

end Example

section Geo

variable {X : Scheme.{0}} {C : Type} [Category.{0} C]

theorem isCoc_of_isFrame {L : LB X} (hL : L.IsLB) {V : C → X.Opens} {hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T}
    {u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ} (h : IsFrame L V hV u) : IsCoc V hV u := by
  obtain ⟨τ, -, h⟩ := h
  intro T T' T'' a b
  have k : ∀ m, res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (u T T'' (a ≫ b)) =
      res inf_le_left (res (hV b) (u T T' a) * u T' T'' b) := fun m ↦ by
    have e1 := congrArg (res (inf_le_inf_right (L.U m) (hV b))) (h T T' a m)
    rw [map_mul, h T' T'' b m, LB.res_res, LB.res_res, h T T'' (a ≫ b) m, ← mul_assoc] at e1
    rw [map_mul, LB.res_res]
    exact mul_right_cancel e1
  refine Units.ext (X.sheaf.eq_of_locally_eq' (fun m ↦ V T'' ⊓ L.U m) _ (fun m ↦ homOfLE inf_le_left) ?_ _ _
    fun m ↦ congrArg Units.val (k m))
  rw [← inf_iSup_eq, hL.cover, inf_top_eq]

def Ch (L : LB X) : Type := {p : X.affineOpens × L.ι // p.1.1 ≤ L.U p.2}

instance (L : LB X) : Preorder (Ch L) := Preorder.lift fun p ↦ OrderDual.toDual p.1.1

def chG (L : LB X) : Ch L ⥤ AffOp X where
  obj p := Opposite.op p.1.1
  map a := (homOfLE (leOfHom a)).op

theorem isFrame_ch {L : LB X} (hL : L.IsLB) : IsFrame L (opOf (chG L)) (opOf_le (chG L))
    fun T T' a ↦ res (le_inf T'.2 ((opOf_le (chG L) a).trans T.2)) (L.g T'.1.2 T.1.2) := by
  refine ⟨fun T m ↦ res (le_inf inf_le_right (inf_le_left.trans T.2)) (L.g m T.1.2), fun T m m' ↦ ?_,
    fun T T' a m ↦ ?_⟩
  · exact ((LB.res_res _ _ _).trans (LB.res_cocycle hL _ _ _ _ _ _).symm).trans
      (congrArg (_ * ·) (LB.res_res _ _ _).symm)
  · exact (((LB.res_res _ _ _).trans (LB.res_cocycle hL _ _ _ _ _ _).symm).trans
      (congrArg (_ * ·) (LB.res_res _ _ _).symm)).trans (mul_comm _ _)

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {s₀ : X ⟶ Sp R₀}

end Geo

end GlobalTheory.LBObs.Model
