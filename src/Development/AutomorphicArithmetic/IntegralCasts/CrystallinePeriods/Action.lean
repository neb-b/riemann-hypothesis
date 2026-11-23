module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Bundle0001

@[expose] public section

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

@[reducible] def actionOf {G B : Type*} [Monoid G] [CommRing B] (f : G → B →+* B)
    (h1 : ∀ x, f 1 x = x) (hmul : ∀ g h x, f (g * h) x = f g (f h x)) : MulSemiringAction G B where
  smul g x := f g x
  one_smul := h1
  mul_smul := hmul
  smul_zero g := map_zero (f g)
  smul_add g := map_add (f g)
  smul_one g := map_one (f g)
  smul_mul g := map_mul (f g)

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

theorem toRingHom_one : MulSemiringAction.toRingHom G R 1 = RingHom.id R := by ext; simp

theorem toRingHom_mul (g h : G) : MulSemiringAction.toRingHom G R (g * h) =
    (MulSemiringAction.toRingHom G R g).comp (MulSemiringAction.toRingHom G R h) := by
  ext; simp [mul_smul]

theorem toRingHom_injective (g : G) : Function.Injective (MulSemiringAction.toRingHom G R g) :=
  MulAction.injective g

variable [Fact ¬IsUnit (p : R)]

variable [IsAdicComplete (span {(p : R)}) R]

instance BdRPlus.mulSemiringAction : MulSemiringAction G (BdRPlus p R) :=
  actionOf (fun g => BdRPlus.map p (MulSemiringAction.toRingHom G R g))
    (fun x => by simpa only [toRingHom_one] using BdRPlus.map_id x)
    (fun g h x => by simpa only [toRingHom_mul] using (BdRPlus.map_map _ _ x).symm)

instance Bcris.mulSemiringAction : MulSemiringAction G (Bcris p R) :=
  actionOf (fun g => Bcris.map p (MulSemiringAction.toRingHom G R g) (toRingHom_injective g))
    (fun x => by
      rw [Bcris.map_congr _ Function.injective_id toRingHom_one, Bcris.map_id])
    (fun g h x => by
      have hi := (toRingHom_injective (R := R) g).comp (toRingHom_injective h)
      rw [Bcris.map_map _ _ _ _ hi, Bcris.map_congr _ hi (toRingHom_mul g h)])

instance BdR.mulSemiringAction : MulSemiringAction G (BdR p R) :=
  actionOf (fun g => (BdR.map p (MulSemiringAction.toRingEquiv G R g)).toRingHom)
    (fun x => by
      have : MulSemiringAction.toRingEquiv G R 1 = RingEquiv.refl R := by ext; simp
      simp [this])
    (fun g h x => by
      have : MulSemiringAction.toRingEquiv G R (g * h) =
          (MulSemiringAction.toRingEquiv G R h).trans (MulSemiringAction.toRingEquiv G R g) := by
        ext; simp [mul_smul]
      simp [this, BdR.map_map])


theorem BdR.smul_algebraMap (g : G) (x : BdRPlus p R) :
    g • algebraMap _ (BdR p R) x = algebraMap _ _ (g • x) := BdR.map_algebraMap _ x



end Reformulated.AutPerF
