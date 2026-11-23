module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.GenLeOfFintype

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

namespace UpperTheory.V

instance (A : AbF) : NeZero A.m := ⟨A.pos.ne'⟩

namespace B1

section Cyc

variable (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) [NeZero N]

include F in
theorem natCard_roots : Nat.card (rootsOfUnity N Ω) = N := by
  haveI := IsAlgClosure.isAlgClosed F (K := Ω)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  exact hζ.card_rootsOfUnity

def cycN : G F Ω →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter Ω (natCard_roots F Ω N)).comp (MulSemiringAction.toRingAut (G F Ω) Ω)

theorem cycN_spec (g : G F Ω) {ζ : Ω} (h : ζ ^ N = 1) : g ζ = ζ ^ (cycN F Ω N g : ZMod N).val := by
  have hz : ζ ≠ 0 := by
    rintro rfl
    simp [NeZero.ne N] at h
  have hu : Units.mk0 ζ hz ∈ rootsOfUnity N Ω := by
    rw [mem_rootsOfUnity]
    ext
    simp [h]
  have key := modularCyclotomicCharacter.spec Ω (natCard_roots F Ω N)
    (MulSemiringAction.toRingAut (G F Ω) Ω g) hu
  simpa [cycN] using key

theorem cycN_eq_iff (g : G F Ω) (b : (ZMod N)ˣ) :
    cycN F Ω N g = b ↔ ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (b : ZMod N).val := by
  constructor
  · rintro rfl ζ hζ
    exact cycN_spec F Ω N g hζ
  · intro hb
    have hz : ∀ t ∈ rootsOfUnity N Ω, (MulSemiringAction.toRingAut (G F Ω) Ω g) (t : Ω) = (t : Ω) ^ (b : ZMod N).val := by
      intro t ht
      have ht' : (t : Ω) ^ N = 1 := by
        rw [mem_rootsOfUnity] at ht
        simpa using congrArg Units.val ht
      simpa using hb t ht'
    have := modularCyclotomicCharacter.unique Ω (natCard_roots F Ω N)
      (MulSemiringAction.toRingAut (G F Ω) Ω g) hz
    ext
    exact this.symm

end Cyc

section Coord

variable (n q d : ℕ) [Fact q.Prime] [Fact d.Prime]


end Coord

end B1

namespace AbF

open B1

def U (A : AbF) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] : Subgroup (G ℚ Ω) := A.H.comap (cycN ℚ Ω A.m)

def comp (A B : AbF) : AbF :=
  ⟨Nat.lcm A.m B.m, Nat.lcm_pos A.pos B.pos,
    A.H.comap (ZMod.unitsMap (Nat.dvd_lcm_left _ _)) ⊓ B.H.comap (ZMod.unitsMap (Nat.dvd_lcm_right _ _))⟩

end AbF

end UpperTheory.V

end
