module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ThmFD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdConsA

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_cd {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : thrStar ε + 1 < h) : fdcD ε lam = dimVlam lam := by
  have hsa : StrictAnti lam := (fdc_stdGap hlam hgap hh).1
  have key : ∀ t : ℕ, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
      (T : KType ε (lowK ε (lamT lam t))) (j : T.V →L[ℂ] H),
      FData ε (lamT lam t) σ T j ∧
      (∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
        (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (w' : H'), Lap.Base.IsHWSmooth ε σ' (lamT lam t) w' ∧
          ∀ z : PCoord ε → ℂ, ⟪w', σ' (NormedSpace.exp (pmat z)) w'⟫_ℂ =
            ⟪T.w, fF ε (lamT lam t) T (pmat z) T.w⟫_ℂ) ∧
      Formalism.MainNotions.S.IsFdeg (muCD ε) σ (fdcD ε (lamT lam t)) := by
    intro t
    have hμ := isHCParam_lamT hlam t
    have hg : GapAtLeast ε (lamT lam t) (h + t) := gap_lamT hsa hgap t
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hh' : thrStar ε + 1 < h + t := by linarith
    have hstd := fdc_stdGap hμ hg hh'
    let T : KType ε (lowK ε (lamT lam t)) := (HW.kType_exists ε _ hμ).some
    obtain ⟨m, hm, hP⟩ := fdc_model hp hq hμ hg hh' T
    obtain ⟨d, H, i1, i2, σ, hDS, hd⟩ := fdc_ds_exists hp hq hμ hg hh'
    haveI : CompleteSpace H := hDS.1
    obtain ⟨j, hiso, hk, -, hform⟩ := anyF hDS hstd hP
    have hΨ : ∀ z : PCoord ε → ℂ, PsiM T m (NormedSpace.exp (pmat z)) = fF ε (lamT lam t) T (pmat z) := by
      intro z
      rw [psiM_exp_pmat, psM_exp_pmat hm T z]
    obtain ⟨H', i1', i2', σ', w', hsm, hlink⟩ := Lap.Base.link n ε _ T (PsiM T m) hstd hP
    refine ⟨H, i1, i2, inferInstance, σ, T, j, ⟨hDS.2.2.1, hiso, hk, fun z => ?_⟩,
      ⟨H', i1', i2', σ', w', hsm, fun z => ?_⟩, ?_⟩
    · rw [hform _ (exp_pmat_inUJ z), hΨ]
    · rw [hlink _ (exp_pmat_inUJ z), hΨ]
    · rw [fdcD_eq hμ hg hh' ⟨H, i1, i2, σ, hDS, hd⟩]
      exact hd
  choose H i1 i2 i3 σ T j hF hsm hd using key
  exact thmFD Lap.Base.b3 hp hq hlam hgap hh (fdcD ε) (fdc_step hp hq hh) H σ T j
    (Filter.Eventually.of_forall hF) (Filter.Eventually.of_forall hsm) (Filter.Eventually.of_forall hd)

theorem fdCons_cd {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : thrStar ε + 1 < h)
    (hΨ : ∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
      ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDS ε lam σ) {v : H} (hv : v ≠ 0) :
    Formalism.MainNotions.S.fdegOf (muCD ε) σ v = dimVlam lam := by
  obtain ⟨d, hd⟩ := fdcGood_of_isDS hσ
  have hgood : FdcGood ε lam d := ⟨H, inferInstance, inferInstance, σ, hσ, hd⟩
  have h1 : fdcD ε lam = d := fdcD_eq hlam hgap hh hgood
  rw [← fdc_cd hp hq hlam hgap hh, h1, fdegOf_of_isFdeg' hd hv]

theorem fdCons_muG (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      thrStar ε + 1 < h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      (∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
        ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ) →
      v ≠ 0 → Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam := by
  haveI := muCD_isHaar ε
  let κ := Measure.haarScalarFactor (muCD ε) (Formalism.REAL.muG ε)
  have hκpos : (0 : ℝ) < κ :=
    NNReal.coe_pos.mpr (Measure.haarScalarFactor_pos_of_isHaarMeasure (muCD ε) (Formalism.REAL.muG ε))
  have hκ : muCD ε = κ • Formalism.REAL.muG ε :=
    Measure.isMulLeftInvariant_eq_smul (muCD ε) (Formalism.REAL.muG ε)
  refine ⟨κ, hκpos, ?_⟩
  intro lam H _ _ _ σ v hlam hσ h hgap hh hp hq hΨ hv
  have hcd := fdCons_cd hp hq hlam hgap hh hΨ hσ hv
  have hfd : Formalism.QuantumDeterminants.fdegHC lam = dimVlam lam := rfl
  rw [hκ] at hcd
  delta Formalism.MainNotions.S.fdegOf at hcd ⊢
  rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at hcd
  rw [hfd, ← hcd]
  rw [div_mul_eq_div_div_swap, mul_comm (κ : ℝ), div_mul_cancel₀ _ hκpos.ne']

end ReciprocityTheory.ChartRestriction.DS
