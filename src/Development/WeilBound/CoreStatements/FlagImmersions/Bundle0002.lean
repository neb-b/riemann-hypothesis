module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0005
public import Formalism.DegreeFormula.PointDegree.PowSum

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.DecompositionPowerSumsTopDegree
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top


open GroundTheory.Heights₂.Heights.RestTerms in
theorem RootFieldNumerics.coinv_above_top : CoinvAboveTopGeneral.Statement :=
  CoinvAboveTopGeneral.proof (CoinvAboveTop.proof
    (CoinvPolynomialReduction.proof (CoinvMonomialReduction.proof CoinvStepReduction.proof))
    (CoinvIdealComponent.proof CoinvIdealRepresentation.proof HomogeneousComponentMul.proof)
    (CoinvStaircaseComponent.proof CoinvStaircaseDegree.proof))

theorem RootFieldNumerics.decomposition_power_sums_top_degree : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (F : RP Ψ N), 2 ≤ N → F.IsHomogeneous (dimFl Ψ N + 1) → ∃ Q : Ψ → ℕ → RP Ψ N, (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (dimFl Ψ N + 1 - k)) ∧ F = ∑ τ, ∑ k ∈ Finset.Icc 1 N, pk τ k * Q τ k := by
  intro Ψ _ _ N F _ hF
  have hlt : Fintype.card Ψ * (Fintype.card (Fin N) * (Fintype.card (Fin N) - 1) / 2) < dimFl Ψ N + 1 := by
    simp [dimFl]
  obtain ⟨Q, hQ, hFQ⟩ := RootFieldNumerics.coinv_above_top ℝ Ψ (Fin N) (dimFl Ψ N + 1) F hF hlt
  refine ⟨fun τ k => Q k τ, fun τ k _ _ => hQ k τ, ?_⟩
  rw [hFQ, Fintype.card_fin, Finset.sum_comm]
  rfl
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.DegFlPowerSumMul
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

private theorem coeff_X_pow_mul_flag_immersions {σ : Type*} [DecidableEq σ] (m : σ →₀ ℕ) (x : σ) (k : ℕ)
    (p : MvPolynomial σ ℝ) :
    (X x ^ k * p).coeff m = if k ≤ m x then p.coeff (m - Finsupp.single x k) else 0 := by
  rw [X_pow_eq_monomial, coeff_monomial_mul', one_mul]
  simp only [Finsupp.single_le_iff]

theorem degFl_power_sum_mul : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (k : ℕ) (G : RP Ψ N), 1 ≤ k → degFl (pk τ k * G) = 0 := by
  intro Ψ _ _ N τ k G hk
  have hval : ∀ (σ : Ψ → Equiv.Perm (Fin N)) (x : Ψ × Fin N),
      permExp σ x = N - 1 - ((σ x.1 x.2 : Fin N) : ℕ) := fun σ x => rfl
  have key : ∀ j : Fin N, ∑ σ : Ψ → Equiv.Perm (Fin N),
      (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) *
        (X (τ, (σ τ).symm j) ^ k * G).coeff (permExp σ) = 0 := by
    intro j
    have hjN := j.isLt
    by_cases hj : (j : ℕ) + k < N
    · let j' : Fin N := ⟨j + k, hj⟩
      have hj'v : (j' : ℕ) = j + k := rfl
      have hne : j ≠ j' := fun h => by
        have := congrArg Fin.val h
        rw [hj'v] at this
        omega
      let ρ : Ψ → Equiv.Perm (Fin N) := Pi.mulSingle τ (Equiv.swap j j')
      have hρτ : ρ τ = Equiv.swap j j' := Pi.mulSingle_eq_same _ _
      have hρt : ∀ t, t ≠ τ → ρ t = 1 := fun t ht => Pi.mulSingle_eq_of_ne ht _
      let F : (Ψ → Equiv.Perm (Fin N)) → ℝ := fun σ =>
        (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) * (X (τ, (σ τ).symm j) ^ k * G).coeff (permExp σ)
      have hanti : ∀ σ, F (ρ * σ) = -F σ := by
        intro σ
        have hsign : (∏ t, ((Equiv.Perm.sign ((ρ * σ) t) : ℤ) : ℝ)) =
            -∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ) := by
          have h1 : ∀ t, ((Equiv.Perm.sign ((ρ * σ) t) : ℤ) : ℝ) =
              ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ) * ((Equiv.Perm.sign (σ t) : ℤ) : ℝ) := by
            intro t
            rw [Pi.mul_apply, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
          rw [Finset.prod_congr rfl fun t _ => h1 t, Finset.prod_mul_distrib,
            Finset.prod_eq_single τ (fun t _ ht => by rw [hρt t ht, Equiv.Perm.sign_one]; simp)
              (fun h => absurd (Finset.mem_univ τ) h), hρτ, Equiv.Perm.sign_swap hne]
          simp
        have hsymm : ((ρ * σ) τ).symm j = (σ τ).symm j' := by
          rw [Equiv.symm_apply_eq, Pi.mul_apply, hρτ, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
            Equiv.swap_apply_right]
        have hat : (σ τ) ((σ τ).symm j) = j := Equiv.apply_symm_apply _ _
        have hbt : (σ τ) ((σ τ).symm j') = j' := Equiv.apply_symm_apply _ _
        have hab : (σ τ).symm j ≠ (σ τ).symm j' := fun h => hne ((σ τ).symm.injective h)
        have hexp : permExp (ρ * σ) - Finsupp.single (τ, (σ τ).symm j') k =
            permExp σ - Finsupp.single (τ, (σ τ).symm j) k := by
          ext ⟨t, i⟩
          simp only [Finsupp.coe_tsub, Pi.sub_apply, hval, Finsupp.single_apply, Prod.mk.injEq]
          by_cases ht : t = τ
          · rw [ht, Pi.mul_apply, hρτ, Equiv.Perm.mul_apply]
            by_cases hia : (σ τ).symm j = i
            · rw [← hia, hat, Equiv.swap_apply_left]
              simp only [hab.symm, true_and, and_false, if_true, if_false]
              omega
            · by_cases hib : (σ τ).symm j' = i
              · rw [← hib, hbt, Equiv.swap_apply_right]
                simp only [hab, true_and, and_false, if_true, if_false]
                omega
              · have h1 : (σ τ) i ≠ j := fun h => hia (by rw [← h, Equiv.symm_apply_apply])
                have h2 : (σ τ) i ≠ j' := fun h => hib (by rw [← h, Equiv.symm_apply_apply])
                rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
                simp only [hia, hib, and_false, if_false]
          · rw [Pi.mul_apply, hρt t ht, one_mul]
            simp only [Ne.symm ht, false_and, if_false]
        have hcond : ∀ σ' : Ψ → Equiv.Perm (Fin N), ∀ a : Fin N, σ' τ a = j →
            (k ≤ permExp σ' (τ, a)) := by
          intro σ' a ha
          rw [hval]
          simp only [ha]
          omega
        have hL : (ρ * σ) τ ((σ τ).symm j') = j := by
          rw [Pi.mul_apply, hρτ, Equiv.Perm.mul_apply, hbt, Equiv.swap_apply_right]
        show (∏ t, ((Equiv.Perm.sign ((ρ * σ) t) : ℤ) : ℝ)) *
            (X (τ, ((ρ * σ) τ).symm j) ^ k * G).coeff (permExp (ρ * σ)) =
          -((∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) *
            (X (τ, (σ τ).symm j) ^ k * G).coeff (permExp σ))
        rw [hsign, hsymm, coeff_X_pow_mul_flag_immersions, coeff_X_pow_mul_flag_immersions, if_pos (hcond _ _ hL),
          if_pos (hcond _ _ hat), hexp, neg_mul]
      have h2 : ∑ σ, F (ρ * σ) = ∑ σ, F σ := Equiv.sum_comp (Equiv.mulLeft ρ) F
      rw [Finset.sum_congr rfl fun σ _ => hanti σ, Finset.sum_neg_distrib] at h2
      change ∑ σ, F σ = 0
      linarith
    · refine Finset.sum_eq_zero fun σ _ => ?_
      have hlt : ¬ k ≤ permExp σ (τ, (σ τ).symm j) := by
        rw [hval]
        simp only [Equiv.apply_symm_apply]
        omega
      rw [coeff_X_pow_mul_flag_immersions, if_neg hlt, mul_zero]
  have hsplit : degFl (pk τ k * G) = (-1) ^ dimFl Ψ N * ∑ j : Fin N, ∑ σ : Ψ → Equiv.Perm (Fin N),
      (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) *
        (X (τ, (σ τ).symm j) ^ k * G).coeff (permExp σ) := by
    unfold degFl
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [pk, Finset.sum_mul, coeff_sum, Finset.mul_sum]
    exact (Equiv.sum_comp (σ τ).symm fun i =>
      (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) * (X (τ, i) ^ k * G).coeff (permExp σ)).symm
  rw [hsplit, Finset.sum_eq_zero fun j _ => key j, mul_zero]

end RootFieldNumerics
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.FlagDegreeLinearFunctionals
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

noncomputable def pa_degFlL (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) : RP Ψ N →ₗ[ℝ] ℝ where
  toFun F := degFl F
  map_add' P Q := Formalism.DegreeFormula.PPowSum.degFl_add P Q
  map_smul' c P := by
    rw [smul_eq_C_mul]
    exact Formalism.DegreeFormula.PPowSum.degFl_C_mul c P

theorem pa_degFlL_apply {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (F : RP Ψ N) :
    pa_degFlL Ψ N F = degFl F := rfl

theorem degFl_Sh_Tot_linear_and_degFl_eq_zero_off_dim : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∃ Φ : RP Ψ N →ₗ[ℝ] ℝ, ∀ F, Φ F = degFl F) ∧ (∀ (j : ℕ) (τ : Ψ), ∃ Φ : RP Ψ N →ₗ[ℝ] ℝ, ∀ F, Φ F = Sh j τ F) ∧ (∀ τ : Ψ, ∃ Φ : RP Ψ N →ₗ[ℝ] ℝ, ∀ F, Φ F = Tot τ F) ∧ ∀ (d : ℕ) (F : RP Ψ N), F.IsHomogeneous d → d ≠ dimFl Ψ N → degFl F = 0 := by
  intro Ψ _ _ N
  refine ⟨⟨pa_degFlL Ψ N, fun F => pa_degFlL_apply F⟩, ?_, ?_, ?_⟩
  · intro j τ
    refine ⟨(pa_degFlL Ψ N).comp (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
      ((pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)) : RP Ψ N →ₗ[ℝ] RP Ψ N)), fun F => ?_⟩
    rw [LinearMap.comp_apply, pa_degFlL_apply, LinearMap.sum_apply]
    rfl
  · intro τ
    refine ⟨(pa_degFlL Ψ N).comp (∑ i : Fin N,
      ((pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)) : RP Ψ N →ₗ[ℝ] RP Ψ N)), fun F => ?_⟩
    rw [LinearMap.comp_apply, pa_degFlL_apply, LinearMap.sum_apply]
    rfl
  · intro d F hF hd
    exact Formalism.DegreeFormula.PPowSum.degFlHomog Ψ N d F hF hd

end RootFieldNumerics
end

