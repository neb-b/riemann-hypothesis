module

public import Formalism.UnipotentAdelicQuotients.Bundle0001

@[expose] public section

noncomputable section

namespace PIW.ClassFinD

open NumberField IsDedekindDomain

def Ohat (F : Type) [Field F] [NumberField F] : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}
  mul_mem' := fun {a b} ha hb v => by have h := mul_mem (ha v) (hb v); exact h
  one_mem' := fun v => (v.adicCompletionIntegers F).one_mem
  add_mem' := fun {a b} ha hb v => by have h := add_mem (ha v) (hb v); exact h
  zero_mem' := fun v => (v.adicCompletionIntegers F).zero_mem
  neg_mem' := fun {a} ha v => by have h := neg_mem (ha v); exact h

def MatInt {F : Type} [Field F] [NumberField F] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Prop :=
  ∀ i j, M i j ∈ Ohat F

theorem matInt_one (F : Type) [Field F] [NumberField F] (n : ℕ) :
    MatInt (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact (Ohat F).one_mem
  · exact (Ohat F).zero_mem

theorem matInt_mul {F : Type} [Field F] [NumberField F] {n : ℕ}
    {M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)} (hM : MatInt M) (hN : MatInt N) :
    MatInt (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (Ohat F).sum_mem fun k _ => (Ohat F).mul_mem (hM i k) (hN k j)

def KGL (F : Type) [Field F] [NumberField F] (n : ℕ) :
    Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) where
  carrier := {g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F) | MatInt g.val ∧ MatInt g⁻¹.val}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · exact matInt_one F n
    · rw [inv_one]; exact matInt_one F n
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact matInt_mul ha hb
    · rw [mul_inv_rev, Units.val_mul]; exact matInt_mul hb' ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩

abbrev glIncl (F : Type) [Field F] [NumberField F] (n : ℕ) :
    GL (Fin n) F →* GL (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
  Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom

def BorelKGL : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ),
    ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
      ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), ∃ γ : GL (Fin n) F, ∃ s ∈ T, ∃ k ∈ KGL F n,
        x = glIncl F n γ * s * k

end PIW.ClassFinD

end
