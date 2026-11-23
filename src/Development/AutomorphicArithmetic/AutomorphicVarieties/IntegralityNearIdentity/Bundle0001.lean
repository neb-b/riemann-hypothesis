module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0030
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0015
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0026
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0051
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0038
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.EqOneOfNear
section
namespace UpperTheory.V.Lib.Small

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral l x hx

end UpperTheory.V.Lib.Small
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.IsIntegralOfNormLe
section
namespace UpperTheory.V.Lib.Small

theorem single_mem {k : Type} [Field k] {n : ℕ} (W : Submodule k (Fin n → k)) (d : Fin n → k) (hd : Function.Injective d)
    (hW : ∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) (v : Fin n → k) (hv : v ∈ W) (i : Fin n) (hi : v i ≠ 0) :
    (Pi.single i 1 : Fin n → k) ∈ W :=
  _root_.UpperTheory.Reformulated.B.S3.single_mem W d hd hW v hv i hi

theorem isIntegral_of_norm_le {l : ℕ} [Fact l.Prime] {z : PadicAlgCl l} (hz : ‖z‖ ≤ 1) : IsIntegral ℤ_[l] z :=
  _root_.UpperTheory.Reformulated.B.S4.isIntegral_of_norm_le hz

end UpperTheory.V.Lib.Small
end

