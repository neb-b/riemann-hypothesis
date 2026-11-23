module

public import Mathlib

@[expose] public section

namespace GlobalTheory

section Defs

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

noncomputable def relLength (A B : Submodule R V) : ℕ∞ :=
  Module.length R (A ⧸ B.submoduleOf A)

def LengthCommensurable (A B : Submodule R V) : Prop :=
  relLength A B ≠ ⊤ ∧ relLength B A ≠ ⊤

noncomputable def signedLength (A B : Submodule R V) : ℤ :=
  ((relLength A B).toNat : ℤ) - ((relLength B A).toNat : ℤ)

end Defs

section Basic

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

theorem relLength_def (A B : Submodule R V) :
    relLength A B = Module.length R (A ⧸ B.submoduleOf A) := rfl

theorem relLength_eq_length_quotient_comap (A B : Submodule R V) :
    relLength A B = Module.length R (A ⧸ B.comap A.subtype) := rfl

theorem relLength_eq_length_range {P : Type*} [AddCommGroup P] [Module R P]
    {A B : Submodule R V} (g : A →ₗ[R] P) (hg : LinearMap.ker g = B.submoduleOf A) :
    relLength A B = Module.length R (LinearMap.range g) := by
  rw [relLength_def, ← hg]
  exact g.quotKerEquivRange.length_eq

theorem relLength_eq_length_of_surjective {P : Type*} [AddCommGroup P] [Module R P]
    {A B : Submodule R V} (g : A →ₗ[R] P) (hg : LinearMap.ker g = B.submoduleOf A)
    (hs : Function.Surjective g) : relLength A B = Module.length R P := by
  rw [relLength_eq_length_range g hg, LinearMap.range_eq_top.mpr hs, Module.length_top]

theorem relLength_eq_length_map_mkQ (A B : Submodule R V) :
    relLength A B = Module.length R (A.map B.mkQ) := by
  rw [relLength_eq_length_range (B.mkQ ∘ₗ A.subtype)
    (by rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl), LinearMap.range_comp,
    Submodule.range_subtype]

theorem relLength_ne_top_iff {A B : Submodule R V} :
    relLength A B ≠ ⊤ ↔ IsFiniteLength R (A ⧸ B.submoduleOf A) :=
  Module.length_ne_top_iff

theorem relLength_congr_right {A B B' : Submodule R V} (h : A ⊓ B = A ⊓ B') :
    relLength A B = relLength A B' := by
  have : B.submoduleOf A = B'.submoduleOf A := by
    ext x
    have := SetLike.ext_iff.mp h (x : V)
    simpa [Submodule.submoduleOf, x.2] using this
  rw [relLength_def, relLength_def, this]

theorem relLength_congr_left {A A' B : Submodule R V} (h : A ⊔ B = A' ⊔ B) :
    relLength A B = relLength A' B := by
  have : A.map B.mkQ = A'.map B.mkQ := by
    have := congrArg (Submodule.map B.mkQ) h
    simpa [Submodule.map_sup] using this
  rw [relLength_eq_length_map_mkQ, relLength_eq_length_map_mkQ, this]

@[simp] theorem relLength_inf_right (A B : Submodule R V) :
    relLength A (A ⊓ B) = relLength A B :=
  relLength_congr_right (by rw [← inf_assoc, inf_idem])

@[simp] theorem relLength_inf_right' (A B : Submodule R V) :
    relLength A (B ⊓ A) = relLength A B := by
  rw [inf_comm, relLength_inf_right]

@[simp] theorem relLength_sup_left (A B : Submodule R V) :
    relLength (A ⊔ B) B = relLength A B :=
  relLength_congr_left (by rw [sup_assoc, sup_idem])

@[simp] theorem relLength_sup_left' (A B : Submodule R V) :
    relLength (B ⊔ A) B = relLength A B := by
  rw [sup_comm, relLength_sup_left]

@[simp] theorem relLength_eq_zero_iff {A B : Submodule R V} : relLength A B = 0 ↔ A ≤ B := by
  rw [relLength_def, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Submodule.submoduleOf_eq_top]

theorem relLength_eq_zero_of_le {A B : Submodule R V} (h : A ≤ B) : relLength A B = 0 :=
  relLength_eq_zero_iff.mpr h

theorem relLength_self (A : Submodule R V) : relLength A A = 0 := by simp

@[simp] theorem relLength_bot_right (A : Submodule R V) :
    relLength A ⊥ = Module.length R A :=
  relLength_eq_length_of_surjective (LinearMap.id : A →ₗ[R] A)
    (by simp [Submodule.submoduleOf]) Function.surjective_id

@[simp] theorem relLength_top_left (B : Submodule R V) :
    relLength ⊤ B = Module.length R (V ⧸ B) := by
  rw [relLength_eq_length_map_mkQ, Submodule.map_top, Submodule.range_mkQ, Module.length_top]

theorem relLength_mono_left {A A' : Submodule R V} (h : A ≤ A') (B : Submodule R V) :
    relLength A B ≤ relLength A' B := by
  rw [relLength_eq_length_map_mkQ, relLength_eq_length_map_mkQ]
  exact Module.length_le_of_injective (Submodule.inclusion (Submodule.map_mono h))
    (Submodule.inclusion_injective _)

theorem relLength_anti_right (A : Submodule R V) {B B' : Submodule R V} (h : B ≤ B') :
    relLength A B' ≤ relLength A B :=
  Module.length_le_of_surjective
    (Submodule.factor (Submodule.comap_mono h : B.submoduleOf A ≤ B'.submoduleOf A))
    (Submodule.factor_surjective _)

@[gcongr] theorem relLength_le_relLength {A A' B B' : Submodule R V} (hA : A ≤ A')
    (hB : B' ≤ B) : relLength A B ≤ relLength A' B' :=
  (relLength_mono_left hA B).trans (relLength_anti_right A' hB)

end Basic

section Map

variable {R S V V' : Type*} [Ring R] [Ring S] [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module S V'] {σ : R →+* S} [RingHomSurjective σ]

theorem length_eq_of_semilinear_bijective (f : V →ₛₗ[σ] V') (hf : Function.Bijective f) :
    Module.length R V = Module.length S V' := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

theorem relLength_map_left (f : V →ₛₗ[σ] V') (A : Submodule R V) (B' : Submodule S V') :
    relLength (A.map f) B' = relLength A (B'.comap f) := by
  symm
  let g : A →ₛₗ[σ] A.map f := f.restrict fun x hx => Submodule.mem_map_of_mem hx
  refine length_eq_of_semilinear_bijective
    (Submodule.mapQ ((B'.comap f).submoduleOf A) (B'.submoduleOf (A.map f)) g
      fun x hx => hx) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : (Submodule.Quotient.mk (g x) : A.map f ⧸ B'.submoduleOf (A.map f)) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at hx' ⊢
    exact hx'
  · intro y
    obtain ⟨⟨_, x, hx, rfl⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩

theorem relLength_comap_comap (f : V →ₛₗ[σ] V') (A' B' : Submodule S V') :
    relLength (A'.comap f) (B'.comap f) = relLength (LinearMap.range f ⊓ A') B' := by
  rw [← relLength_map_left, Submodule.map_comap_eq]

theorem relLength_map_of_injective (f : V →ₛₗ[σ] V') (hf : Function.Injective f)
    (A B : Submodule R V) : relLength (A.map f) (B.map f) = relLength A B := by
  rw [relLength_map_left, Submodule.comap_map_eq_of_injective hf]

theorem relLength_comap_of_le_range (f : V →ₛₗ[σ] V') {A' : Submodule S V'}
    (hA : A' ≤ LinearMap.range f) (B' : Submodule S V') :
    relLength (A'.comap f) (B'.comap f) = relLength A' B' := by
  rw [relLength_comap_comap, inf_eq_right.mpr hA]

theorem lengthCommensurable_map_iff_of_injective (f : V →ₛₗ[σ] V') (hf : Function.Injective f)
    {A B : Submodule R V} :
    LengthCommensurable (A.map f) (B.map f) ↔ LengthCommensurable A B := by
  simp only [LengthCommensurable, relLength_map_of_injective f hf]

theorem LengthCommensurable.signedLength_map_of_injective {A B : Submodule R V}
    (_h : LengthCommensurable A B) (f : V →ₛₗ[σ] V') (hf : Function.Injective f) :
    signedLength (A.map f) (B.map f) = signedLength A B := by
  simp only [signedLength, relLength_map_of_injective f hf]

end Map

section Equiv

variable {R S V V' : Type*} [Ring R] [Ring S] [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module S V'] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [RingHomSurjective σ]

end Equiv

section Ambient

open scoped Pointwise

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

theorem relLength_submoduleOf {A W : Submodule R V} (h : A ≤ W) (B : Submodule R V) :
    relLength (A.submoduleOf W) (B.submoduleOf W) = relLength A B :=
  relLength_comap_of_le_range W.subtype (by rwa [Submodule.range_subtype]) B


open Pointwise in
theorem relLength_smul_smul {G : Type*} [Monoid G] [DistribMulAction G V] [SMulCommClass G R V]
    {a : G} (ha : IsSMulRegular V a) (A B : Submodule R V) :
    relLength (a • A) (a • B) = relLength A B :=
  relLength_map_of_injective (DistribSMul.toLinearMap R V a) ha A B


open Pointwise in
theorem lengthCommensurable_smul_smul_iff {G : Type*} [Monoid G] [DistribMulAction G V]
    [SMulCommClass G R V] {a : G} (ha : IsSMulRegular V a) {A B : Submodule R V} :
    LengthCommensurable (a • A) (a • B) ↔ LengthCommensurable A B :=
  lengthCommensurable_map_iff_of_injective (DistribSMul.toLinearMap R V a) ha


open Pointwise in
theorem LengthCommensurable.signedLength_smul_smul {G : Type*} [Monoid G] [DistribMulAction G V]
    [SMulCommClass G R V] {a : G} {A B : Submodule R V} (h : LengthCommensurable A B)
    (ha : IsSMulRegular V a) : signedLength (a • A) (a • B) = signedLength A B :=
  h.signedLength_map_of_injective (DistribSMul.toLinearMap R V a) ha


end Ambient

section Signed

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {A B : Submodule R V}

@[refl] theorem LengthCommensurable.refl (A : Submodule R V) : LengthCommensurable A A := by
  simp [LengthCommensurable, relLength_self]

@[symm] theorem LengthCommensurable.symm (h : LengthCommensurable A B) :
    LengthCommensurable B A := ⟨h.2, h.1⟩

theorem lengthCommensurable_iff_of_ge (h : B ≤ A) :
    LengthCommensurable A B ↔ relLength A B ≠ ⊤ := by
  simp [LengthCommensurable, relLength_eq_zero_of_le h]

theorem signedLength_eq_of_relLength_eq {m n : ℕ} (hm : relLength A B = m)
    (hn : relLength B A = n) : signedLength A B = (m : ℤ) - n := by
  simp [signedLength, hm, hn]

namespace LengthCommensurable

theorem signedLength_swap (_h : LengthCommensurable A B) :
    signedLength B A = -signedLength A B := by
  simp [signedLength]

theorem signedLength_of_ge (_h : LengthCommensurable A B) (hBA : B ≤ A) :
    signedLength A B = (relLength A B).toNat := by
  simp [signedLength, relLength_eq_zero_of_le hBA]

theorem signedLength_eq_natCast_iff_of_ge (h : LengthCommensurable A B) (hBA : B ≤ A) {n : ℕ} :
    signedLength A B = n ↔ relLength A B = n := by
  rw [h.signedLength_of_ge hBA, Nat.cast_inj, ← ENat.natCast_inj, ENat.natCast_toNat h.1]

theorem signedLength_nonneg (h : LengthCommensurable A B) (hBA : B ≤ A) :
    0 ≤ signedLength A B := by
  rw [h.signedLength_of_ge hBA]
  exact Int.natCast_nonneg _

end LengthCommensurable

end Signed

section Examples

theorem relLength_top_of_isMaximal {R : Type*} [CommRing R] (I : Ideal R) [hI : I.IsMaximal] :
    relLength (⊤ : Ideal R) I = 1 := by
  rw [relLength_top_left, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
  exact hI.out

theorem relLength_int_top_span_prime {p : ℤ} (hp : Prime p) :
    relLength (⊤ : Ideal ℤ) (Ideal.span {p}) = 1 :=
  have := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  relLength_top_of_isMaximal _

end Examples

end GlobalTheory
