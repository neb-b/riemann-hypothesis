module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Bundle0001

@[expose] public section

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaLUniq

theorem agreeOnH : AgreeOnH := by
  intro E _ _ _ S Λ r T T' F F' F'' β₁ β₂ k _ hLF hLF'' hdim n' n'' hs1 hs2 x hx
  have hX : Xsp F ≤ UUE Λ F F'' := by
    have hflag {t : E} (G : LFlag S r t) : finrank E (Xplus G) ≤ r + 1 := by
      have hXG : finrank E (Xsp G) = r := by
        change finrank E (Submodule.span E (Set.range G.fl.e)) = r
        simpa using finrank_span_eq_card G.fl.e_indep
      have hz : finrank E (Submodule.span E {G.fl.z}) ≤ 1 := by
        classical
        simpa using (finrank_span_le_card (R := E) ({G.fl.z} : Set S.V))
      change finrank E (Xsp G ⊔ Submodule.span E {G.fl.z} : Submodule E S.V) ≤ r + 1
      exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (by rw [hXG]; omega)
    have hlat {t : E} (G : LFlag S r t) (hG : IsLift Λ G) :
        XLam Λ G ⊔ Submodule.span (𝓞 E) {G.zt} ≤ (Xplus G).restrictScalars (𝓞 E) := by
      refine sup_le (fun y hy => ?_) ?_
      · exact (show Xsp G ≤ Xplus G from le_sup_left) hy.2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hG.2]
        exact (show Submodule.span E {G.fl.z} ≤ Xplus G from le_sup_right)
          (Submodule.mem_span_singleton_self _)
    have hU : UUE Λ F F'' ≤ Xplus F ⊔ Xplus F'' := by
      rw [UUE, spanE, Submodule.span_le]
      change UU Λ F F'' ≤ (Xplus F ⊔ Xplus F'').restrictScalars (𝓞 E)
      rw [UU, sup_assoc]
      exact sup_le
        ((hlat F hLF).trans (Submodule.restrictScalars_mono (𝓞 E) le_sup_left))
        ((hlat F'' hLF'').trans (Submodule.restrictScalars_mono (𝓞 E) le_sup_right))
    have hEq := Submodule.eq_of_le_of_finrank_le hU (by
      rw [n''.1]
      have hsum := Submodule.finrank_add_le_finrank_add_finrank (Xplus F) (Xplus F'')
      have h₁ := hflag F
      have h₂ := hflag F''
      omega)
    rw [hEq]
    exact (show Xsp F ≤ Xplus F from le_sup_left).trans le_sup_left
  have hHp : finrank E (Hp Λ F F') + (2 * r + 2) = finrank E S.V := by
    have := finrank_orth_add S (UUE Λ F F')
    rw [n'.1] at this
    exact this
  have hle : ∀ β, Th Λ F F' F'' β ≤ Hp Λ F F' := by
    intro β y hy
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod] at hp
    exact hp.1.1.1
  have hTh : ∀ β, s0 Λ F F' F'' β k = 1 → Th Λ F F' F'' β = Hp Λ F F' := by
    intro β hs
    apply Submodule.eq_of_le_of_finrank_le (hle β)
    simp only [s0] at hs
    omega
  have hx1 : x ∈ Th Λ F F' F'' β₁ := by rw [hTh β₁ hs1]; exact hx
  have hx2 : x ∈ Th Λ F F' F'' β₂ := by rw [hTh β₂ hs2]; exact hx
  obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.mp hx1
  obtain ⟨q, hq, hq1⟩ := Submodule.mem_map.mp hx2
  simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at hp hq hp1 hq1
  subst hp1
  have e : p.2 = q.2 := by
    have hin : p.2 - q.2 ∈ UUE Λ F F'' ⊓ orth S (UUE Λ F F'') := by
      refine ⟨?_, ?_⟩
      · apply hX
        have : p.2 - q.2 = (q.1 - q.2) - (p.1 - p.2) := by rw [hq1]; abel
        rw [this]
        exact (Xsp F).sub_mem hq.1.2 hp.1.2
      · exact (orth S (UUE Λ F F'')).sub_mem hp.1.1.2 hq.1.1.2
    rw [n''.2] at hin
    exact sub_eq_zero.mp ((Submodule.mem_bot E).mp hin)
  have : β₂ p.1 - β₁ p.1 = (β₂ q.1 - q.2) - (β₁ p.1 - p.2) := by rw [hq1, e]; abel
  rw [this]
  exact (Xsp F'').sub_mem hq.2 hp.2

end PI.UnitaryGroupMassFormula.BetaLUniq
