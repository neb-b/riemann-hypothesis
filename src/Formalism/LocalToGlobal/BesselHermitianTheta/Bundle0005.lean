module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.LocalToGlobal.HermitianColumns.Bundle0002
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.BesselUnipotentSubgroup
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsDualFlag {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (f : Matrix (Fin B.rank) (Fin d.ρ) D.host.E) :
    Prop where
  iso : IsIsoSub B f
  pair : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * B.gram * f = 1
  perpA : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram * f = 0
  perpZ : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) f * B.gram).mulVec d.z = 0

end Formalism.L2.Theta

end
end

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.Joints
section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Theta

theorem VolTieG.hermVolTied {D : D7} (h : VolTieG D) : Formalism.L2.Herm.VolumeCompatible D := by
  intro W P Q hs hsig μ hμ 𝓕 h𝓕
  exact ((h.volTie W P Q hs hsig).2 μ hμ).2 𝓕 h𝓕

end Formalism.L2.Theta

end
end

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.TiedDef
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : ThetaX D}

def AutFunDefIffSm (D : D7) : Prop :=
  ∀ θ, IsInfFam (D := D) θ → ∀ V : HSp D, V.SigOK → V.IsDefinite → ∀ φ, IsAutFunDef V φ ↔ IsAutFunSm θ V φ

end Formalism.L2.Theta

end
end

-- bundled from Formalism.LocalToGlobal.BesselHermitianTheta.TiedLocW
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def conjId (D : D7) : (AE D)ˣ →* (AE D)ˣ := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

end Formalism.L2.Theta

end
end

