module

public import Mathlib
public import GroundTheory.PAdicHodge.LocalBridge
public import GroundTheory.PAdicHodge.ACrisGalois
public import GroundTheory.LocalFields.Bundle0007
public import GroundTheory.LocalFields.PrincipalUnitsRank

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open ValuativeRel IsLocalRing

namespace UnramifiedACris

variable {p : ℕ} [hp : Fact p.Prime]


variable (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K₀]


omit [FiniteDimensional ℚ_[p] K₀] in
theorem mem_integer_iff (x : K₀) : x ∈ 𝒪[K₀] ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  rw [integer_eq_normInteger, mem_normInteger]
  rfl

theorem natCast_p_mem_maximalIdeal : (p : 𝒪[K₀]) ∈ 𝓂[K₀] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : ((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p) = 1 := by rw [hv]; rfl
  have hv1 : ‖(((v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖ ≤ 1 := (mem_integer_iff K₀ _).1 v.2
  have h2 : ‖((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖ < 1 := by
    have : ((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p) =
        (p : PadicAlgCl p) * (((v : 𝒪[K₀]) : K₀) : PadicAlgCl p) := by
      simp
    rw [this, norm_mul]
    calc ‖(p : PadicAlgCl p)‖ * ‖(((v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖
        ≤ ‖(p : PadicAlgCl p)‖ * 1 := by gcongr
      _ < 1 := by
        rw [mul_one, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends]
        exact Padic.norm_p_lt_one
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

instance charP_residueField : CharP 𝓀[K₀] p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (residue 𝒪[K₀]), residue_eq_zero_iff]
    exact natCast_p_mem_maximalIdeal K₀)

variable [GroundTheory.LocalField.IsUnramified ℚ_[p] K₀]

end UnramifiedACris

end GroundTheory.PAdicHodge
