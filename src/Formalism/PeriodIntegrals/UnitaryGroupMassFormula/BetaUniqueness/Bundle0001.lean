module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0022
public import Lemmata.GeneralBFactThirdRest.Imports

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.CMNorm
section
noncomputable section

open NumberField Formalism.BasicNotions

namespace PI.UnitaryGroupMassFormula.BetaLUniq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cm_norm_eq_one (D : D7) (μ : D.host.E) (h : star μ * μ = 1) (φ : D.host.E →+* ℂ) :
    ‖φ μ‖ = 1 := by
  have hφ := D.sp.cm.cmUnram.2.1 φ μ
  have h1 : φ (star μ) * φ μ = 1 := by rw [← map_mul, h, map_one]
  rw [hφ, Complex.conj_mul'] at h1
  have h2 : ‖φ μ‖ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : 0 ≤ ‖φ μ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖φ μ‖ - 1), sq_nonneg (‖φ μ‖ + 1)]

end PI.UnitaryGroupMassFormula.BetaLUniq
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
section
noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaLUniq

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem finrank_orth_add (U : Submodule E S.V) :
    finrank E (orth S U) + finrank E U = finrank E S.V := by
  set d := finrank E U
  let b := Module.finBasis E U
  let f : Fin d → Module.Dual E S.V := fun i => S.hT (b i : S.V)
  have hli : LinearIndependent E f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : S.hT (∑ j, star (g j) • (b j : S.V)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star]
      exact hg
    have h1 : ∑ j, star (g j) • (b j : S.V) = 0 :=
      S.nondeg.1 _ (fun y => by rw [h0]; rfl)
    have hli' : LinearIndependent E (fun j => (b j : S.V)) :=
      b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    have := (Fintype.linearIndependent_iff.mp hli') (fun j => star (g j)) h1 i
    simpa using this
  let Φ : Submodule E (Module.Dual E S.V) := Submodule.span E (Set.range f)
  have hΦ : finrank E Φ = d := by
    rw [finrank_span_eq_card hli]; simp [d]
  have hco : Φ.dualCoannihilator = orth S U := by
    ext v
    rw [Submodule.mem_dualCoannihilator, mem_orth]
    constructor
    · intro h x hx
      have hx' := b.sum_repr ⟨x, hx⟩
      have : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : S.V) := by
        have h2 := congrArg Subtype.val hx'
        rw [Submodule.coe_sum] at h2
        simp only [Submodule.coe_smul] at h2
        exact h2.symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
      have := h (f i) (Submodule.subset_span ⟨i, rfl⟩)
      simp only [f] at this
      rw [this, smul_zero]
    · intro h φ hφ
      induction hφ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact h _ (b i).2
      | zero => rfl
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ
  rw [hco, hΦ] at this
  omega

theorem exists_smul_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsFullLattice E Λ) (x : S.V) :
    ∃ a : 𝓞 E, a ≠ 0 ∧ a • x ∈ Λ :=
  Bl.general_b_fact_third''''.goal1 S Λ hΛ x

theorem span_inf_toO (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsFullLattice E Λ) (U : Submodule E S.V) :
    Submodule.span E ((Λ ⊓ toO S U : Submodule (𝓞 E) S.V) : Set S.V) = U := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro x hx
    obtain ⟨a, ha, hax⟩ := exists_smul_mem S Λ hΛ x
    have hmem : a • x ∈ (Λ ⊓ toO S U : Submodule (𝓞 E) S.V) :=
      ⟨hax, by simpa [toO] using U.smul_mem (a : E) hx⟩
    have hx' : x = ((a : E)⁻¹) • (a • x) := by
      rw [← algebraMap_smul E a x, smul_smul]
      have : (a : E) ≠ 0 := by simpa using ha
      simp [this]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem Xsp_le_UUE (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsFullLattice E Λ) {r : ℕ} {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') : Xsp F ≤ UUE Λ F F' := by
  rw [← span_inf_toO S Λ hΛ (Xsp F)]
  apply Submodule.span_mono
  intro x hx
  simp only [UU]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hx))

theorem Xsp_le_UUE' (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsFullLattice E Λ) {r : ℕ} {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') : Xsp F' ≤ UUE Λ F F' := by
  rw [← span_inf_toO S Λ hΛ (Xsp F')]
  apply Submodule.span_mono
  intro x hx
  simp only [UU]
  exact Submodule.mem_sup_left (Submodule.mem_sup_right hx)

end PI.UnitaryGroupMassFormula.BetaLUniq
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Skeleton
section
noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaLUniq

section Gen

def GramNondeg : Prop :=
  ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V) {r : ℕ} {T T' : E} (F : LFlag S r T) (F' : LFlag S r T'),
    Submodule.IsFullLattice E Λ → IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 →
      finrank E (UUE Λ F F') = 2 * r + 2 ∧ UUE Λ F F' ⊓ orth S (UUE Λ F F') = ⊥

def AgreeOnH : Prop :=
  ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V) {r : ℕ} {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β₁ β₂ : S.V ≃ₗ[E] S.V) (k : ℕ), Submodule.IsFullLattice E Λ → IsLift Λ F → IsLift Λ F'' →
    finrank E S.V = k + 2 * r + 1 →
    (finrank E (UUE Λ F F') = 2 * r + 2 ∧ UUE Λ F F' ⊓ orth S (UUE Λ F F') = ⊥) →
    (finrank E (UUE Λ F F'') = 2 * r + 2 ∧ UUE Λ F F'' ⊓ orth S (UUE Λ F F'') = ⊥) →
    s0 Λ F F' F'' β₁ k = 1 → s0 Λ F F' F'' β₂ k = 1 →
      ∀ x ∈ Hp Λ F F', β₂ x - β₁ x ∈ Xsp F''

def EigenOne {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} (Λ : Submodule (𝓞 E) S.V) {r : ℕ} {T T' : E} (F : LFlag S r T)
    (F' : LFlag S r T') (β₁ β₂ : S.V ≃ₗ[E] S.V) : Prop :=
  ∀ v ∈ orth S (Xplus F'), v ∉ Xsp F' → (∀ h ∈ Hp Λ F F', S.hT h v = 0) →
    ∀ μ : E, β₁.symm (β₂ v) - μ • v ∈ Xsp F' → μ = 1

end Gen

section D7

open PI.BetaLUniq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def WAniso : Prop :=
  ∀ (D : D7) (u' : D.what₂.Word) (F' : Fl D (Tu D u')) (w : (hS D).V),
    w ∈ orth (hS D) (Xplus F') → (hS D).hT w w = 0 → w ∈ Xsp F'

def EigenvalueLastLineOne : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word),
  ∀ (Λ : Lt D) (F : Fl D (Tu D u)) (F' F'' : Fl D (Tu D u')) (β₁ β₂ : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' → IsGeneric Λ (gS D) F F' →
    IsGeneric Λ (gS D) F F'' → IsPair Λ F F' F'' β₁ (gS D) → IsPair Λ F F' F'' β₂ (gS D) →
    Lat.s0 Λ F F' F'' β₁ D.R.k = 1 → Lat.s0 Λ F F' F'' β₂ D.R.k = 1 →
      EigenOne Λ F F' β₁ β₂

theorem finrank_hS (D : D7) : finrank D.host.E (hS D).V = D.R.k + 2 * D.R.rS + 1 := by
  rw [(hS D).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Ranks.rankY, Ranks.r, Ranks.rS, zero_mul, add_zero]
  omega

end D7

end PI.UnitaryGroupMassFormula.BetaLUniq
end
end

