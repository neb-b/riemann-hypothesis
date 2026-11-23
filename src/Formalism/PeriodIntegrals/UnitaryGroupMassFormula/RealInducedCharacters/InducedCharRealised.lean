module

public import Mathlib

@[expose] public section

set_option autoImplicit false

namespace BrauerSchur

open scoped BigOperators

section IndFun

variable {G : Type*} [Group G] [Fintype G]


open scoped Classical in
noncomputable def indFun {R : Type*} [Field R] (H : Subgroup G) (f : H → R) (g : G) : R :=
  (Nat.card H : R)⁻¹ * ∑ x : G, if hx : x⁻¹ * g * x ∈ H then f ⟨x⁻¹ * g * x, hx⟩ else 0

end IndFun

end BrauerSchur
