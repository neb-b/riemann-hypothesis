module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0006

@[expose] public section

namespace Formalism.MainNotions.S.Gauge

theorem gauge_density_exists : ∀ (n : ℕ) (ε : Fin n → Bool), GaugeDens ε := fun _ ε =>
  gaugeDens_of_parts ε (chartNhd ε) (transC ε) (jacInv ε) (locInvOf ε) (ballFormOf ε) (densOfBall ε)

end Formalism.MainNotions.S.Gauge
