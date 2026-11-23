module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExCayS

@[expose] public section

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

section Chart

variable (P Q : ℕ)

def cayCand (g : UpqT P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  (1 + 1) * (UpqT.mat g + 1)⁻¹ * (UpqT.mat g - 1)

open Classical in
def cayInv (g : UpqT P Q) : lieU P Q :=
  if h : cayCand P Q g ∈ lieU P Q then ⟨cayCand P Q g, h⟩ else 0

def CayInvMeas : Prop := ∀ P Q : ℕ, Measurable (cayInv P Q)

def CayInvIff : Prop := ∀ (P Q : ℕ) (g : UpqT P Q) (X : lieU P Q),
  UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
    (1 + 1) + ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) → cayInv P Q g = X

end Chart

end HcInf
