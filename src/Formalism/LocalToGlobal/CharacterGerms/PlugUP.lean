module

public import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.DualLattices.Bundle0034
public import ReciprocityTheory.DualLattices.Bundle0019
public import ReciprocityTheory.DualLattices.Bundle0020
public import Formalism.SharpRestriction.GrowthBounds.FittingIdeal.DetMulMemFitt0

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace ValuationFitting

open ReciprocityTheory.PGsh.Up CharacteristicFromRanks

variable {C : Type} [Field C]

instance factL (V : VF C) : Fact V.l.Prime := ⟨V.l_prime⟩

def ValTie (V : VF C) (vm : Valuation C NNReal) : Prop :=
  ∀ x : C, x ≠ 0 → ∃ t : ℝ, V.v x = (t : WithTop ℝ) ∧ (vm x : ℝ) = (vm (V.l : C) : ℝ) ^ t

section Val

variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

def vA (V : VF C) (R : Type) [CommRing R] [Algebra R C] : AddValuation R (WithTop ℝ) :=
  V.v.comap (algebraMap R C)

theorem vA_apply (x : R) : vA V R x = V.v (algebraMap R C x) := rfl

theorem vA_nonneg (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) : ∀ x : R, 0 ≤ vA V R x := by
  intro x
  rw [vA_apply]
  by_cases hx : algebraMap R C x = 0
  · rw [hx, V.v.map_zero]; exact le_top
  · obtain ⟨t, ht1, ht2⟩ := hT _ hx
    rw [ht1]
    have hle : (vm (algebraMap R C x) : ℝ) ≤ 1 := by exact_mod_cast hv.map_le_one x
    have : 0 ≤ t := by
      by_contra hneg
      have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (not_le.mp hneg)
      rw [← ht2] at this
      linarith
    exact_mod_cast this

theorem lenCoker_vA {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) :
    S4.lenCoker (vA V R) α = S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) := by
  unfold S4.lenCoker
  congr 1
  funext g
  rw [vA_apply, RingHom.map_det]
  rfl

end Val

theorem rpow_neg_succ {l : ℕ} (hl : 0 < l) (n : ℕ) :
    (l : ℝ) ^ (-((n : ℝ) + 1)) = ((l : ℝ) ^ (n + 1))⁻¹ := by
  have h0 : (0 : ℝ) ≤ l := by positivity
  rw [Real.rpow_neg h0, ← Nat.cast_succ, Real.rpow_natCast]

section Val2

variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem lenCoker_eq_logb (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : HasLen vm R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) (hpos : 0 < (x : ℝ)) :
    S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) =
      ((Real.logb (vm (V.l : C) : ℝ) x : ℝ) : WithTop ℝ) := by
  have hxb : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x = x :=
    Real.rpow_logb h0 (ne_of_lt h1) hpos
  rw [← lenCoker_vA]
  apply le_antisymm
  · obtain ⟨y, hy, hyV⟩ := Formalism.MainNotions.G.ValuationFitting.fitt_ge hv α hx
    have hy0 : algebraMap R C y ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hyV
      rw [← hyV] at hpos
      simp at hpos
    obtain ⟨t, ht1, ht2⟩ := hT _ hy0
    refine le_trans (S4.lenCoker_le_of_mem (vA V R) (vA_nonneg hT hv h0 h1) _ hy) ?_
    rw [vA_apply, ht1]
    have : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x ≤ (vm (V.l : C) : ℝ) ^ t := by
      rw [hxb, ← ht2, hyV]
    rw [Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at this
    exact_mod_cast this
  · unfold S4.lenCoker
    refine Finset.le_inf fun g _ => ?_
    rw [vA_apply]
    by_cases hz : algebraMap R C (α.submatrix id g).det = 0
    · rw [hz, V.v.map_zero]; exact le_top
    · obtain ⟨t, ht1, ht2⟩ := hT _ hz
      rw [ht1]
      have hle : (vm (algebraMap R C (α.submatrix id g).det) : ℝ) ≤ x := by
        exact_mod_cast Formalism.MainNotions.G.ValuationFitting.fitt_le hv α hx g
      rw [ht2, ← hxb, Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at hle
      exact_mod_cast hle

end Val2

end ValuationFitting

end Formalism.L2.FormalSeriesBounds
