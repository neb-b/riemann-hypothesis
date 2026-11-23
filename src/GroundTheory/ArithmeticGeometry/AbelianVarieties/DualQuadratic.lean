module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle0005

@[expose] public section

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {E E' : WeierstrassCurve F}
  [E.IsElliptic] [E'.IsElliptic]

theorem mulIsogeny_toHom (n : ℤ) (hn : n ≠ 0) :
    (mulIsogeny E n hn).toHom = n • (homId : isogEnd E) :=
  Subtype.ext (by rw [Isogeny.toHom_val, Isogeny.mulIsogeny_val]; rfl)

namespace Isogeny

end Isogeny

end GroundTheory.Arith.Abelian
