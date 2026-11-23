module

public import Mathlib

@[expose] public section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis

noncomputable section

section Defs

variable {E : Type} [Field E] [NumberField E]

def IsRanks [IsCMField E] (r : ℕ) (rk : (E ≃ₐ[ℚ] E) → ℕ) : Prop :=
  ∀ σ : E ≃ₐ[ℚ] E, rk σ + rk ((IsCMField.complexConj E).restrictScalars ℚ * σ) = r


variable (E) in
structure ClassBasis where

  k : ℕ

  c : Fin k → (FractionalIdeal (𝓞 E)⁰ E)ˣ

  γ : Fin k → Eˣ
  span : ∀ x : ClassGroup (𝓞 E), ∃ a : Fin k → ℤ, x = ∏ i, ClassGroup.mk E (c i) ^ a i
  indep : ∀ a : Fin k → ℤ, ∏ i, ClassGroup.mk E (c i) ^ a i = 1 →
    ∀ i, ClassGroup.mk E (c i) ^ a i = 1
  pow_eq : ∀ i, c i ^ orderOf (ClassGroup.mk E (c i)) = toPrincipalIdeal (𝓞 E) E (γ i)

def ClassBasis.h (B : ClassBasis E) (i : Fin B.k) : ℕ := orderOf (ClassGroup.mk E (B.c i))

theorem ClassBasis.h_pos (B : ClassBasis E) (i : Fin B.k) : 0 < B.h i := by
  unfold ClassBasis.h
  exact orderOf_pos _

variable {rk : (E ≃ₐ[ℚ] E) → ℕ} {B : ClassBasis E} {Ω : Type} [Field Ω] [Algebra E Ω]

end Defs

section Exist

private lemma prod_mulSingle_zpow_eq_symm {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [CommGroup G]
    {n : ι → ℕ} (e : G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) (b : ι → ℤ) :
    ∏ j, e.symm (Pi.mulSingle j (Multiplicative.ofAdd 1)) ^ b j =
      e.symm (fun j => Multiplicative.ofAdd (b j : ZMod (n j))) := by
  apply e.injective
  rw [map_prod, MulEquiv.apply_symm_apply]
  simp only [map_zpow, MulEquiv.apply_symm_apply, ← Pi.mulSingle_zpow]
  refine (Finset.univ_prod_mulSingle
    (fun j => Multiplicative.ofAdd (1 : ZMod (n j)) ^ b j)).trans (funext fun j => ?_)
  rw [← ofAdd_zsmul]
  simp

theorem exists_basis (G : Type) [CommGroup G] [Finite G] :
    ∃ (k : ℕ) (g : Fin k → G), (∀ x, ∃ a : Fin k → ℤ, x = ∏ i, g i ^ a i) ∧
      ∀ a : Fin k → ℤ, ∏ i, g i ^ a i = 1 → ∀ i, g i ^ a i = 1 := by
  obtain ⟨ι, _, n, -, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  classical
  set q := Fintype.equivFin ι
  have key : ∀ a : Fin (Fintype.card ι) → ℤ,
      ∏ i, e.symm (Pi.mulSingle (q.symm i) (Multiplicative.ofAdd 1)) ^ a i =
        e.symm (fun j => Multiplicative.ofAdd (a (q j) : ZMod (n j))) := by
    intro a
    rw [← prod_mulSingle_zpow_eq_symm e (fun j => a (q j))]
    exact Fintype.prod_equiv q.symm _ _ (fun i => by simp)
  refine ⟨Fintype.card ι, fun i => e.symm (Pi.mulSingle (q.symm i) (Multiplicative.ofAdd 1)),
    ?_, ?_⟩
  · intro x
    choose b hb using fun j => ZMod.intCast_surjective (Multiplicative.toAdd (e x j))
    refine ⟨fun i => b (q.symm i), ?_⟩
    rw [key]
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    funext j
    simp [hb]
  · intro a ha i
    rw [key] at ha
    have h0 : ∀ j, (a (q j) : ZMod (n j)) = 0 := by
      intro j
      have h1 := congrFun (e.symm.injective (ha.trans (map_one e.symm).symm)) j
      simpa using h1
    have h2 := h0 (q.symm i)
    simp only [Equiv.apply_symm_apply] at h2
    rw [← map_zpow, ← Pi.mulSingle_zpow, ← ofAdd_zsmul]
    simp [h2]

variable {E : Type} [Field E] [NumberField E]

theorem exists_gen {I : (FractionalIdeal (𝓞 E)⁰ E)ˣ} (h : ClassGroup.mk E I = 1) :
    ∃ γ : Eˣ, I = toPrincipalIdeal (𝓞 E) E γ := by
  obtain ⟨x, hx⟩ := (ClassGroup.mk_eq_one_iff.mp h).principal
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply I.ne_zero
    apply FractionalIdeal.coeToSubmodule_injective
    dsimp only
    rw [hx]
    simp
  refine ⟨Units.mk0 x hx0, ?_⟩
  symm
  rw [toPrincipalIdeal_eq_iff]
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [FractionalIdeal.coe_spanSingleton, hx]
  simp

instance : Nonempty (ClassBasis E) := by
  obtain ⟨k, g, hs, hi⟩ := exists_basis (ClassGroup (𝓞 E))
  have hsurj : ∀ x : ClassGroup (𝓞 E), ∃ I, ClassGroup.mk E I = x :=
    ClassGroup.induction E fun I => ⟨I, rfl⟩
  choose c hc using fun i => hsurj (g i)
  choose γ hγ using fun i => exists_gen (I := c i ^ orderOf (ClassGroup.mk E (c i)))
    (by rw [map_pow, pow_orderOf_eq_one])
  exact ⟨⟨k, c, γ, by simpa only [hc] using hs, by simpa only [hc] using hi, hγ⟩⟩

variable {rk : (E ≃ₐ[ℚ] E) → ℕ} {B : ClassBasis E} {Ω : Type} [Field Ω] [Algebra E Ω]

end Exist

end

end GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis
