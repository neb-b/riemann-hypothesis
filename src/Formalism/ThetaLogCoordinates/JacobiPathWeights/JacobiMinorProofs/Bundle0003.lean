module

public import Mathlib
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.CorA3primeB
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LemmaA2indepOf
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.JacobiMinorProof
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.Bundle0001
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ValuationProductsComponents
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ExistsSuppOfEvalNe
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.Bundle0002

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.GoodWOfWeight
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace DominanceOrderLemmas

theorem domLe_refl {n : ℕ} (ν : Fin n → ℤ) : DomLe ν ν := ⟨rfl, fun _ => le_rfl⟩

theorem domLe_trans {n : ℕ} {a b c : Fin n → ℤ} (h1 : DomLe a b) (h2 : DomLe b c) : DomLe a c :=
  ⟨h1.1.trans h2.1, fun j => (h1.2 j).trans (h2.2 j)⟩

theorem vars_of_polB {R : Type*} [CommRing R] {n N : ℕ} {B : ℕ → ℕ} {G : MvPolynomial (ℕ × Fin n) R}
    (hG : G ∈ polB R n N B) : ∀ x ∈ G.vars, x.1 < N := by
  intro x hx
  by_contra hlt
  push_neg at hlt
  have hGi := (Submodule.mem_iInf _).mp hG x.1
  rw [if_neg (not_lt.mpr hlt), mem_weightedHomogeneousSubmodule] at hGi
  obtain ⟨e, he, hex⟩ := (MvPolynomial.mem_vars_iff_mem_support x).mp hx
  have h0 := hGi (mem_support_iff.mp he)
  have hpos : 0 < e x := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hex)
  rw [Finsupp.weight_apply, Finsupp.sum] at h0
  have hle := Finset.single_le_sum (f := fun y => e y • (if y.1 = x.1 then 1 else 0 : ℕ))
    (fun _ _ => Nat.zero_le _) hex
  simp only [if_true, smul_eq_mul, mul_ite, mul_one, mul_zero] at hle h0
  omega

theorem actAll_X {L : Type*} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (g gi : Matrix (Fin n) (Fin n) L)
    (i : ℕ) (a : Fin n) :
    actAll isVec g gi (X (i, a)) =
      if isVec i then ∑ b, X (i, b) * C (g b a) else ∑ b, X (i, b) * C (gi a b) := by
  unfold actAll
  rw [aeval_X]
  split_ifs <;> simp [Matrix.vecMul, dotProduct]

theorem vars_actX {L : Type*} [CommRing L] [Nontrivial L] {n : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) (x : ℕ × Fin n) :
    ∀ y ∈ (actAll isVec g gi (X x)).vars, y.1 = x.1 := by
  intro y hy
  rw [actAll_X] at hy
  split_ifs at hy <;>
  · obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hy)
    have h' := MvPolynomial.vars_mul _ _ hb
    rw [Finset.mem_union, vars_X, vars_C] at h'
    simp only [Finset.mem_singleton, Finset.notMem_empty, or_false] at h'
    rw [h']

theorem vars_act {L : Type*} [CommRing L] [Nontrivial L] {n N : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) {P : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ P.vars, x.1 < N) :
    ∀ y ∈ (actAll isVec g gi P).vars, y.1 < N := by
  intro y hy
  have heq : actAll isVec g gi P = bind₁ (fun x => actAll isVec g gi (X x)) P := by
    simp only [actAll, bind₁, aeval_X]
  rw [heq] at hy
  obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_bind₁ _ _ hy)
  rw [vars_actX isVec g gi x y hyx]
  exact hv x hx

end DominanceOrderLemmas

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.UnitAndFieldPowerLemmas
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace ExponentSetCounting

variable {n : ℕ}

def ContP (i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ)
    (x : (ℕ → Fin n → ℤ) × (ℤ → Finset (Fin n))) : Prop :=
  x.1 i = μ₀ ∧ (∀ j, j < i ∨ N < j → x.1 j = 0) ∧
    (∀ j, i ≤ j → j < N →
      if isVec j then HStrip (x.1 (j + 1)) (x.1 j) (B j) else HStrip (x.1 j) (x.1 (j + 1)) (B j)) ∧
    IsStd (x.1 N) x.2

def expSet (n i N : ℕ) (B : ℕ → ℕ) : Set (ℕ × Fin n →₀ ℕ) :=
  {β | ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0}

theorem shift_inj (n i : ℕ) : Function.Injective (fun x : ℕ × Fin n => (i + x.1, x.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (by omega) h.2

theorem expSet_subset (n i N : ℕ) (B : ℕ → ℕ) :
    expSet n i N B ⊆ Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2)) ''
      {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0} := by
  intro β hβ
  have hβ' : ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0 := hβ
  have hsupp : ↑β.support ⊆ Set.range (fun x : ℕ × Fin n => (i + x.1, x.2)) := by
    intro p hp
    obtain ⟨j, a⟩ := p
    have hpa : β (j, a) ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hij : i ≤ j := by
      by_contra hlt
      have h0 := hβ' j
      rw [if_neg (fun h => hlt h.1)] at h0
      exact hpa ((Finset.sum_eq_zero_iff.mp h0) a (Finset.mem_univ a))
    exact ⟨(j - i, a), Prod.ext (show i + (j - i) = j by omega) rfl⟩
  refine ⟨Finsupp.comapDomain _ β (fun _ _ _ _ h => shift_inj n i h), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    intro j
    show ∑ a, β (i + j, a) = _
    rw [hβ' (i + j)]
    by_cases h : j < N - i
    · rw [if_pos ⟨by omega, by omega⟩, if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · apply Finsupp.mapDomain_comapDomain
    · exact shift_inj n i
    · exact hsupp

theorem expSet_finite (hR : PolBRank) (n i N : ℕ) (B : ℕ → ℕ) : (expSet n i N B).Finite :=
  ((hR n (N - i) (fun j => B (i + j))).2.1.image _).subset (expSet_subset n i N B)

theorem expSet_card (hR : PolBRank) (n i N : ℕ) (B : ℕ → ℕ) :
    (expSet n i N B).ncard ≤ ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  have hfin : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.Finite :=
    (hR n (N - i) (fun j => B (i + j))).2.1
  have hcard : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard =
      ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) :=
    (hR n (N - i) (fun j => B (i + j))).1
  calc (expSet n i N B).ncard
      ≤ ((Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2))) ''
          {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}).ncard :=
        Set.ncard_le_ncard (expSet_subset n i N B) (hfin.image _)
    _ ≤ {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard :=
        Set.ncard_image_le hfin
    _ = ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) := hcard
    _ = ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) :=
        (Finset.prod_Ico_eq_prod_range (fun l => (n + B l - 1).choose (B l)) i N).symm

theorem psiFam_mem (k : Type) [Field k] (N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (x : PathIdx n N isVec B) :
    psiFam k n N isVec B x ∈ polB k n N B := by
  rw [polB, Submodule.mem_iInf]
  intro j
  exact (pathProductDegrees k n N isVec B x.1.1 x.1.2 x.2.1 x.2.2.2.1).2 j

end ExponentSetCounting

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

