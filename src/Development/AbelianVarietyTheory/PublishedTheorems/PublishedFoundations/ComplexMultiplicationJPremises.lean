module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsBasisEmbedding

@[expose] public section

open NumberField
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Published

instance galSMulCommClassIntegers {K L : Type*} [Field K] [Field L] [Algebra K L] :
    SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm s a x := by
    apply RingOfIntegers.ext
    rw [Algebra.smul_def, Algebra.smul_def]
    change s (algebraMap K L a * x) = algebraMap K L a * s x
    rw [map_mul, AlgEquiv.commutes]

section Defs

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

def IsUnramifiedAbelian (M : IntermediateField K ℂ) : Prop :=
  FiniteDimensional K M ∧ IsAbelianGalois K M ∧
    ∀ (P : Ideal (𝓞 M)) [P.IsPrime], P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P

def IsHilbertClassField (H : IntermediateField K ℂ) : Prop :=
  IsUnramifiedAbelian H ∧ ∀ M : IntermediateField K ℂ, IsUnramifiedAbelian M → M ≤ H

def IsArtinMap {H : IntermediateField K ℂ} (art : ClassGroup (𝓞 K) →* (H ≃ₐ[K] H)) : Prop :=
  ∀ (𝔭 : (Ideal (𝓞 K))⁰) (𝔓 : Ideal (𝓞 H)), 𝔓.IsPrime → 𝔓.LiesOver (𝔭 : Ideal (𝓞 K)) →
    IsArithFrobAt (𝓞 K) (art (ClassGroup.mk0 𝔭)) 𝔓

def IsIdealLattice (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair) : Prop :=
  (L.lattice : Set ℂ) = algebraMap K ℂ '' 𝔞.1

end Defs

def ComplexMultiplicationJSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ],
    Module.finrank ℚ K = 2 →
    ∃ (H : IntermediateField K ℂ) (art : ClassGroup (𝓞 K) ≃* (H ≃ₐ[K] H)),
      IsHilbertClassField H ∧ IsArtinMap art.toMonoidHom ∧
      (∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair), IsIdealLattice 𝔞 L →
        K⟮(latticeCurve L).j⟯ = H) ∧
      ∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair),
        IsIdealLattice 𝔞 L → IsIdealLattice (𝔟⁻¹ * 𝔞) L' →
        ∀ x : H, (x : ℂ) = (latticeCurve L).j →
          (art (ClassGroup.mk K 𝔟) x : ℂ) = (latticeCurve L').j

section Lemmas

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]


open NumberField in
open scoped nonZeroDivisors IntermediateField in
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] in
theorem _root_.GlobalTheory.Published.latticeCurve_j_eq (L : PeriodPair) :
    (_root_.GlobalTheory.latticeCurve L).j = 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    _root_.GlobalTheory.latticeCurve_c₄, _root_.GlobalTheory.latticeCurve_Δ]
  ring


open NumberField in
open scoped nonZeroDivisors IntermediateField in
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] in
theorem _root_.GlobalTheory.Published.exists_isIdealLattice [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ∃ L, _root_.GlobalTheory.Published.IsIdealLattice 𝔞 L := by
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by
    have := IsTotallyComplex.finrank (K := K)
    omega
  have hs := sign_discr K
  rw [hc, pow_one, Int.sign_eq_neg_one_iff_neg] at hs
  have hd : discr K = -((-discr K).toNat : ℤ) := by omega
  obtain ⟨L, hL⟩ := _root_.GlobalTheory.QuadraticZeta.exists_periodPair h2 hd (algebraMap K ℂ) 𝔞
  exact ⟨L, hL⟩



open NumberField in
open scoped nonZeroDivisors IntermediateField in
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] in
theorem _root_.GlobalTheory.Published.ComplexMultiplicationJSt.finrank_eq
    (h : _root_.GlobalTheory.Published.ComplexMultiplicationJSt) [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) {H : IntermediateField K ℂ} (hH : _root_.GlobalTheory.Published.IsHilbertClassField H) :
    Module.finrank K H = classNumber K := by
  obtain ⟨H₀, art, hH₀, -, -, -⟩ := h K h2
  obtain rfl : H = H₀ := le_antisymm (hH₀.2 H hH.1) (hH.2 H₀ hH₀.1)
  haveI := hH.1.1
  haveI := hH.1.2.1
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr art.toEquiv, classNumber,
    Nat.card_eq_fintype_card]


end Lemmas

end GlobalTheory.Published
