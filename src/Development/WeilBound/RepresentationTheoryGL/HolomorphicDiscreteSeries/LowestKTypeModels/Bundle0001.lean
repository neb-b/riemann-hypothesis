module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.OfIntegralHolds

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.ApplyNeZero
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.LowestKTypeUnitIntegral

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.MainNotions.BridgeCSchur

variable {n : ℕ}

theorem apply_ne_zero {ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    {ρ : UJ ε' → (H →L[ℂ] H)} (hirr : IsIrredOn (UJset ε') σ) {j : H' →L[ℂ] H} (hj0 : j ≠ 0)
    (hj : ∀ h : UJ ε', ∀ x, j (σ (um h) x) = ρ h (j x)) {w : H'} (hw : w ≠ 0) : j w ≠ 0 := by
  intro h0
  rcases irr_of hirr (LinearMap.ker (j : H' →ₗ[ℂ] H)) j.isClosed_ker (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      show j (σ (um g) v) = 0
      rw [hj, show j v = 0 from hv, map_zero]) with h | h
  · exact hw ((Submodule.mem_bot ℂ).1 (h ▸ (LinearMap.mem_ker.2 h0 : w ∈ LinearMap.ker (j : H' →ₗ[ℂ] H))))
  · exact hj0 (ContinuousLinearMap.ext fun x => by
      have : x ∈ LinearMap.ker (j : H' →ₗ[ℂ] H) := h ▸ Submodule.mem_top
      simpa using this)

theorem isom_of {ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    {ρ : UJ ε' → (H →L[ℂ] H)} (hU : IsURepOn (UJset ε') σ) (hirr : IsIrredOn (UJset ε') σ) (hρ : URep ρ)
    (j : H' →L[ℂ] H) (hj : ∀ h : UJ ε', ∀ x, j (σ (um h) x) = ρ h (j x)) :
    ∃ c : ℂ, ∀ x, ⟪j x, j x⟫_ℂ = c * ⟪x, x⟫_ℂ := by
  obtain ⟨c, hc⟩ := schur_bounded (Set.range fun k : UJ ε' => σ (um k)) (by
      rintro _ ⟨k, rfl⟩
      refine ⟨k⁻¹, ?_⟩
      rw [ContinuousLinearMap.star_eq_adjoint]
      refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact (u_adj hU k x y).symm)
    (fun S hS hst => irr_of hirr S hS fun k => hst _ ⟨k, rfl⟩) (ContinuousLinearMap.adjoint j ∘L j) (by
      rintro _ ⟨k, rfl⟩
      refine ContinuousLinearMap.ext fun x => ext_inner_left ℂ fun y => ?_
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
      rw [hj]
      have e1 : ⟪j y, ρ k (j x)⟫_ℂ = ⟪ρ k⁻¹ (j y), j x⟫_ℂ := by rw [hρ.adj, inv_inv]
      rw [e1, ← hj, ← ContinuousLinearMap.adjoint_inner_right, u_adj hU, inv_inv])
  refine ⟨c, fun x => ?_⟩
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, hc, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, inner_smul_right]

end PositivityTheory.RgHe.LowestKTypeUnitIntegral
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.LowestQLeRank
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.LowestKTypeUnitIntegral

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.MainNotions.BridgeCSchur

theorem lowest_q_le_rank {m : ℕ} (ε : Fin m → Bool) : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ m := by
  have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ m :=
    (min_le_left _ _).trans (by unfold ReciprocityTheory.ChartRestriction.DS.pOf; exact (Finset.card_filter_le _ _).trans (by simp))
  exact_mod_cast this

theorem models_holds : Models := by
  intro n ε lam ε' mu e hG
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hG.two
  have hx3 : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hx2 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have hbig : 2 * ((n + 1 : ℕ) : ℝ) < 200 * ((n : ℝ) + 1) ^ 3 := by push_cast; linarith
  have hbig' : 2 * (n : ℝ) < 200 * ((n : ℝ) + 1) ^ 3 := by linarith
  constructor
  · rintro ⟨H0, H0', i1, i2, i3, i4, π0, σ0, hπ0, hσ0, j0, hj00, hj0⟩ H H' _ _ _ _ _ _ π σ hπ hσ
    haveI := hπ0.1
    haveI := hσ0.1
    obtain ⟨UG, hUG⟩ := (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap (n + 1) ε lam hG.hc _ hG.gap hbig H0 π0 hπ0).2.2.2.2 H π hπ
    obtain ⟨UH, hUH⟩ := (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap n ε' mu hG.hc' _ hG.gap' hbig' H0' σ0 hσ0).2.2.2.2 H' σ hσ
    refine ⟨(UG : H0 →L[ℂ] H).comp (j0.comp (UH.symm : H' →L[ℂ] H0')), fun h0 => hj00 ?_, fun h x => ?_⟩
    · refine ContinuousLinearMap.ext fun y => ?_
      have := congrArg (fun f => UG.symm (f (UH y))) h0
      simpa using this
    · have e1 : UH.symm (σ (um h) x) = σ0 (um h) (UH.symm x) := by
        apply UH.injective
        rw [hUH _ (umat_mem h), LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
      simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'', ContinuousLinearEquiv.coe_coe]
      show UG (j0 (UH.symm (σ (um h) x))) = π (emb e (um h)) (UG (j0 (UH.symm x)))
      have m1 : emb e (um h) ∈ UJset ε := umat_mem (embU hG.fits h)
      rw [e1, hj0, hUG _ m1]
  · intro hO
    obtain ⟨H, i1, i2, π, hπ⟩ := ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap (n + 1) ε lam hG.hc _ hG.gap (Or.inr (by
      have := lowest_q_le_rank ε
      refine max_lt hbig ?_
      push_cast at this ⊢
      have h1 : 8 * ((n : ℝ) + 1) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ 8 * ((n : ℝ) + 1) * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      nlinarith))
    obtain ⟨H', i1', i2', σ, hσ⟩ := ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap n ε' mu hG.hc' _ hG.gap' (Or.inr (by
      have := lowest_q_le_rank ε'
      refine max_lt hbig' ?_
      have h1 : 8 * (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε' : ℝ) ≤ 8 * (n : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      nlinarith))
    haveI := hπ.1
    haveI := hσ.1
    exact ⟨H, H', i1, i2, i1', i2', π, σ, hπ, hσ, hO H H' π σ hπ hσ⟩

end PositivityTheory.RgHe.LowestKTypeUnitIntegral
end
end

