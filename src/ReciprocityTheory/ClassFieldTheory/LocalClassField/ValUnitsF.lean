module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsE

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem rpow_neg_div_nonneg (i : ℕ) : 0 ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K) :=
  Real.rpow_nonneg (Nat.cast_nonneg p) _

def UKi (i : ℕ) : Subgroup Kˣ where
  carrier := {x | x ∈ UK p K ∧ ‖((x : K) : PadicAlgCl p) - 1‖ ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K)}
  one_mem' := ⟨(UK p K).one_mem, by
    show ‖(((1 : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    simp only [Units.val_one, OneMemClass.coe_one, sub_self, norm_zero]
    exact rpow_neg_div_nonneg p K i⟩
  mul_mem' := fun {x y} hx hy => ⟨(UK p K).mul_mem hx.1 hy.1, by
    have hx1 : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx.1
    have h : (((x * y : Kˣ) : K) : PadicAlgCl p) - 1 =
        ((x : K) : PadicAlgCl p) * (((y : K) : PadicAlgCl p) - 1) + (((x : K) : PadicAlgCl p) - 1) := by
      rw [Units.val_mul, MulMemClass.coe_mul]; ring
    show ‖(((x * y : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    rw [h]
    refine (PadicAlgCl.isNonarchimedean p _ _).trans (max_le ?_ hx.2)
    rw [norm_mul, hx1, one_mul]; exact hy.2⟩
  inv_mem' := fun {x} hx => ⟨(UK p K).inv_mem hx.1, by
    have hx1 : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx.1
    have hx0 := coe_units_ne_zero x
    have h : (((x⁻¹ : Kˣ) : K) : PadicAlgCl p) - 1 =
        - ((((x : K) : PadicAlgCl p) - 1) * ((x : K) : PadicAlgCl p)⁻¹) := by
      rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
      field_simp
      ring
    show ‖(((x⁻¹ : Kˣ) : K) : PadicAlgCl p) - 1‖ ≤ _
    rw [h, norm_neg, norm_mul, norm_inv, hx1, inv_one, mul_one]; exact hx.2⟩

theorem mem_UKi_iff (i : ℕ) (x : Kˣ) :
    x ∈ UKi p K i ↔ x ∈ UK p K ∧ ‖((x : K) : PadicAlgCl p) - 1‖ ≤ (p : ℝ) ^ (- (i : ℝ) / eK p K) := Iff.rfl

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
