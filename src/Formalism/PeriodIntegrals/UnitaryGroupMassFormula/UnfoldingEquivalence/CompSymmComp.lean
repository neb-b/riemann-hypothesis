module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingEquivalence.Points

@[expose] public section

open PI.UnfoldEquiv PI.UnfoldEquiv.Loc

noncomputable section

namespace PI.UnfoldEquiv.UnitaryGroupMassFormula

variable {k : Type} [CommRing k]

theorem atN_map {n c i : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hi : i < c)
    {w : Fin (n + c) → k} (hw : w ∈ Ufl k n c (i + 1)) : atN (r w) (n + i) = atN w (n + i) := by
  have hlt : n + i < n + c := by omega
  have hw' : w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i) ∈ PI.UnfoldEquiv.Loc.Ufl k n c i := by
    rw [mem_Ufl] at hw ⊢
    intro l hl
    rw [Pi.sub_apply, Pi.smul_apply, eN_apply, smul_eq_mul]
    by_cases hl' : l.1 = n + i
    · rw [if_pos hl', mul_one, PI.UnfoldEquiv.Loc.atN, dite_eq_left hlt]
      have hle : l = ⟨n + i, hlt⟩ := Fin.ext hl'
      rw [hle, sub_self]
    · rw [if_neg hl', mul_zero, sub_zero]
      exact hw l (by omega)
  have hre : PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i))) (n + i) = 1 := by
    have h1 := atN_of_mem (hr.2.2 i)
    have h2 := atN_add (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (n + i)
    rw [sub_add_cancel] at h2
    rw [h2, h1, atN_eN hlt, zero_add]
  have hdec : r w = r (w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) + PI.UnfoldEquiv.Loc.atN w (n + i) • r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) := by
    rw [map_sub, map_smul, sub_add_cancel]
  rw [hdec, atN_add, atN_smul, atN_of_mem (hr.1 i _ hw'), hre, zero_add, mul_one]

private theorem atN_zero {N : ℕ} (i : ℕ) : PI.UnfoldEquiv.Loc.atN (0 : Fin N → k) i = 0 := by
  have h := atN_smul (0 : k) (0 : Fin N → k) i
  rwa [zero_smul, zero_mul] at h

private theorem eN_eq_zero_of_le {N i : ℕ} (h : N ≤ i) : PI.UnfoldEquiv.Loc.eN k N i = 0 := by
  funext l
  have hl := l.2
  rw [eN_apply, Pi.zero_apply, if_neg (by omega)]

theorem chArg_map {n' n c : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r)
    {xj : (Fin n' → k) →ₗ[k] (Fin n → k)} {x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)} (h : Q xj x) :
    chArg (n' := n') (c' := c + 1) (n := n) (c := c) (r.toLinearMap ∘ₗ x) = chArg x + n1Arg r := by
  have key : ∀ i ∈ Finset.range c,
      PI.UnfoldEquiv.Loc.atN (r (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)))) (n + i) =
        PI.UnfoldEquiv.Loc.atN (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1))) (n + i) + PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1))) (n + i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hic : i + 1 < c
    · have hu : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1) :=
        h.2.2 (i + 1) (by omega) hic
      have hcoord := atN_map hr hi hu
      have hx : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) =
          (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1)) + PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1) :=
        (sub_add_cancel _ _).symm
      rw [hx, map_add (f := _), atN_add, atN_add, hcoord, atN_eN_ne (by omega : n + i + 1 ≠ n + i), add_zero]
    · have hw : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1) := by
        rw [mem_Ufl]
        intro l hl
        exfalso
        have := l.2
        omega
      rw [atN_map hr hi hw, eN_eq_zero_of_le (by omega : n + c ≤ n + i + 1), map_zero,
        atN_zero, add_zero]
  simp only [PI.UnfoldEquiv.Loc.chArg, PI.UnfoldEquiv.Loc.n1Arg, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  congr 1
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
    rw [Nat.add_sub_cancel, Finset.sum_range_succ, eN_eq_zero_of_le (by omega : n + (m + 1) ≤ n + m + 1), map_zero,
      atN_zero, add_zero]

end PI.UnfoldEquiv.UnitaryGroupMassFormula
