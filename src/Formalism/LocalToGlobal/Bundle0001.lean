module

public import Formalism.LocalToGlobal.ClassRec
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SelSide
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2

namespace SelJ

variable {D : D7} {X : Col.Fields}

def oEq (s : Ker.Seam D X) : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE

def Carried (s : Ker.Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (P' : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  P'.asIdeal = P.asIdeal.map (oEq s)

end SelJ

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

end

end Formalism.L2
end
end

-- bundled from Formalism.LocalToGlobal.ThresholdSelection
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

def TSelF {eps : ℝ} (Fm : FamP eps) : Type _ :=
  Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, RecT (Fm.ex x hx i)

def TSel (𝒞 : FamClass) : Type _ := ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TSelF Fm

end Formalism.L2

end
end

