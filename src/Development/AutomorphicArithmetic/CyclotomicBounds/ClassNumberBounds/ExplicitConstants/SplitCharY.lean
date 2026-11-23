module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0005
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ExistsIsPrimitiveRootIff
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0004

@[expose] public section

open NumberField KStar.Ram

namespace KStar.Consta

theorem exists_quadField {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) := by
  have : NeZero d := ⟨hd.ne_zero⟩
  have : NeZero (d : ℚ) := ⟨by exact_mod_cast hd.ne_zero⟩
  have : IsCyclotomicExtension {d} ℚ (CyclotomicField d ℚ) :=
    CyclotomicField.isCyclotomicExtension d ℚ
  obtain ⟨ψ, hψ⟩ := exists_isImagQuad (N := d) hd h4 dvd_rfl
  obtain ⟨E, hE⟩ := (fieldChars_lattice (N := d) (K := CyclotomicField d ℚ)).1.2
    (Subgroup.zpowers ψ)
  exact ⟨E, inferInstance, inferInstance, (quadratic_discr_iff (N := d) E d).2 ⟨ψ, hψ, hE⟩⟩

end KStar.Consta
