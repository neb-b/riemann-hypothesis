module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem gmap_eq_iff (g : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap g L = L ↔ ∀ y, y ∈ L ↔ g y ∈ L := by
  have hm : ∀ x, x ∈ Formalism.HermitianLatticesTheory.gmap g L ↔ g.symm x ∈ L := by
    intro x
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨g.symm x, hx, by simp⟩
  constructor
  · intro h y
    have := hm (g y)
    rw [h] at this
    simpa using this.symm
  · intro h
    ext x
    rw [hm, h (g.symm x)]
    simp

variable (Λ : Submodule (𝓞 E) S.V)

theorem isAutLam_mul {a b : S.V ≃ₗ[E] S.V} (ha : IsAutLam S Λ a) (hb : IsAutLam S Λ b) :
    IsAutLam S Λ (a * b) := by
  refine ⟨mul_mem ha.1 hb.1, (gmap_eq_iff _ _).2 fun y => ?_⟩
  rw [(gmap_eq_iff _ _).1 hb.2 y, (gmap_eq_iff _ _).1 ha.2 (b y)]
  rfl

theorem isAutLam_inv {a : S.V ≃ₗ[E] S.V} (ha : IsAutLam S Λ a) : IsAutLam S Λ a⁻¹ := by
  refine ⟨inv_mem ha.1, (gmap_eq_iff _ _).2 fun y => ?_⟩
  have := (gmap_eq_iff _ _).1 ha.2 (a.symm y)
  change y ∈ Λ ↔ a.symm y ∈ Λ
  rw [this]
  simp

variable {Λ}

variable {r : ℕ}

theorem mem_orth_iff (U : Submodule E S.V) (y : S.V) : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

end Gen

end Formalism.L2.SG.Pf.RelativeIndexFlags
