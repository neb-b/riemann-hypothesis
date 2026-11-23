module

public import Mathlib
public import GroundTheory.LocalFields.LocalZetaEpsilon

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Quotient


variable (K) in
abbrev unitsModFiltration (c : ℕ) : Type _ :=
  unitFiltrationUnits K 0 ⧸ (unitFiltrationUnits K c).subgroupOf (unitFiltrationUnits K 0)

instance finite_unitsModFiltration (c : ℕ) : Finite (unitsModFiltration K c) := by
  have : CompactSpace (unitFiltrationUnits K 0) :=
    isCompact_iff_compactSpace.mp isCompact_unitFiltrationUnits_zero
  refine Subgroup.quotient_finite_of_isOpen _ ?_
  rw [Subgroup.coe_subgroupOf]
  exact (isOpen_unitFiltrationUnits c).preimage continuous_subtype_val

noncomputable instance fintype_unitsModFiltration (c : ℕ) : Fintype (unitsModFiltration K c) :=
  Fintype.ofFinite _

def unitsModRep {c : ℕ} (t : unitsModFiltration K c) : Kˣ :=
  ((Quotient.out t : unitFiltrationUnits K 0) : Kˣ)

def unitsModCoset {c : ℕ} (t : unitsModFiltration K c) : Set Kˣ :=
  (fun x => (unitsModRep t)⁻¹ * x) ⁻¹' (unitFiltrationUnits K c : Set Kˣ)

end Quotient

variable [MeasurableSpace K] [BorelSpace K]

section Integral

end Integral

section Gauss

variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}


variable (χ ψ) in
def gaussSum : ℂ :=
  ∑ t : unitsModFiltration K (quasiCharConductor χ),
    ((χ (unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * unitsModRep t) : ℂˣ) : ℂ)⁻¹ *
      (ψ ((unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * unitsModRep t : Kˣ) : K) : ℂ)

end Gauss

end GroundTheory.LocalField
