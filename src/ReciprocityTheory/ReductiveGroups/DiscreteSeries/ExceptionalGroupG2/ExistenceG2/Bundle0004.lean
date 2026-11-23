module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Compact
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.IsDSSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamMemLpOfNe
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaFA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataClosGenEqTop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0014

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FinalExists
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
theorem final_existsG_of (hS7 : ∀ m : ℕ, S7.PsiExistsStatement m) :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        max (2 * (n : ℝ))
          (16 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) +
            8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))) < h →
        ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
          (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ := by
  intro n ε lam hlam h hh hbig
  have hl' := (mir_isHCParam_iff lam).1 hlam
  have hq0 : ((min (pOf ε) (qOf ε) : ℕ) : ℝ) = (S7.q0 ε : ℝ) := rfl
  obtain ⟨T⟩ := HW.kType_exists ε lam hl'
  have hw : T.w ≠ 0 := by
    intro h0; have := T.w_norm; rw [h0, norm_zero] at this; exact zero_ne_one this
  have h2n : 2 * (n : ℝ) < h := lt_of_le_of_lt (le_max_left _ _) hbig
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, h2n⟩
  by_cases hq : 1 ≤ S7.q0 ε
  · have h16 := lt_of_le_of_lt (le_max_right _ _) hbig
    rw [hq0] at h16
    have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
      have : 0 ≤ (n : ℝ) * S7.q0 ε := by positivity
      have := Real.sqrt_nonneg (2 * (S7.q0 ε : ℝ))
      nlinarith
    obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor (hS7 n) T hl' hh hq h8
    exact ⟨Hlam ε Ψ T.w, inferInstance, inferInstance, sigLam ε Ψ T.w, isDS_sigLam hgap hP hw⟩
  · have hpq : pOf ε = 0 ∨ qOf ε = 0 := by
      have h0 : S7.q0 ε = 0 := by omega
      unfold S7.q0 at h0
      omega
    obtain ⟨σ, hσ, -⟩ := isDS_compact hpq hl' T
    exact ⟨T.V, inferInstance, inferInstance, σ, hσ⟩

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamEquivData
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_equiv_data (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    {V : Submodule ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hV0 : V ≠ ⊥) :
    ∃ U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] closGen E V, ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ v₀,
      ((U (sigLam ε Ψ v₀ g x) : closGen E V) : H) = σ g ((U x : closGen E V) : H) := by
  have hσ₁ := rreg_isURepOn ε
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ₁ (isDerivedOn_smE hσ₁) (datumV_isKIrrHW hP hv₀)
    (datumV_casimir hP v₀) (datumV_kStable hP v₀) (datumV_ne_bot hP hv₀) hσ hD hV hc hVK hV0
  exact ⟨U, fun g hg x => hU g hg (sigLam ε Ψ v₀ g x) x (sigLam_coe hgap hP hv₀ hg x)⟩

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

