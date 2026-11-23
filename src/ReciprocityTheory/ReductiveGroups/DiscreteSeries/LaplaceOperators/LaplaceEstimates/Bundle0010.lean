module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalPA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0009

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMF
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace ConjugateTransportSingles

variable {k r : ℕ}

theorem inv_conj (P G : Mat k r) (hP : IsUnit P.det) : (P * G * P⁻¹)⁻¹ = P * G⁻¹ * P⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hP, Matrix.mul_assoc]

theorem cJd_transport (P : Mat k r) (hP : IsUnit P.det) (x1 β : Fin (2 * r + k + 1) → ℂ) (G : Mat k r) :
    cJd (P *ᵥ x1) β (P * G * P⁻¹) = (β ᵥ* P) ⬝ᵥ (G⁻¹ *ᵥ x1) := by
  unfold cJd
  rw [inv_conj P G hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ P⁻¹ P,
    Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec, Matrix.dotProduct_mulVec]

theorem cJd_sinv (P : Mat k r) (hP : IsUnit P.det) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (β : Fin (2 * r + k + 1) → ℂ) (s x : Mat k r) (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z)
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    cJd (xJ P z) β (P * (s * x) * P⁻¹) = cJd (xJ P z) β (P * x * P⁻¹) := by
  unfold xJ
  rw [cJd_transport P hP, cJd_transport P hP]
  exact ((mult k r z hz).1 (0 : Fin (2 * r + k + 1) → ℂ) (β ᵥ* P) s hs x hx).2

theorem cJd_single (P : Mat k r) (hP : IsUnit P.det) (z : Fin (2 * r + k + 1) → ℂ) (d : Fin (2 * r + k + 1))
    (x : Mat k r) :
    cJd (xJ P z) (Pi.single d 1) (P * x * P⁻¹) = (P *ᵥ (x⁻¹ *ᵥ xOne k r z)) d := by
  unfold xJ
  rw [cJd_transport P hP, ← Matrix.dotProduct_mulVec]
  simp [dotProduct, Pi.single_apply]

theorem tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H) (G : Mat k r) :
    tMapD σ x1 x₀ w (Pi.single d m) G = cJd x1 (Pi.single d 1) G * coefX σ x₀ w m G := by
  unfold tMapD
  rw [Finset.sum_eq_single d]
  · simp
  · intro c _ hc
    delta coefX
    simp only [Pi.single_eq_of_ne hc, map_zero, inner_zero_right, mul_zero]
  · simp

theorem tMapD_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (f : Fin (2 * r + k + 1) → H) (G : Mat k r) :
    tMapD σ x1 x₀ w f G = ∑ d, tMapD σ x1 x₀ w (Pi.single d (f d)) G := by
  rw [Finset.sum_congr rfl fun d _ => tMapD_single σ x1 x₀ w d (f d) G]
  rfl

variable {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

theorem perI_tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (P : Mat k r)
    (hP : IsUnit P.det) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    CapelliMinorRestriction.perI P ψ π (tMapD σ (xJ P z) x₀ w (Pi.single d m)) ξ g =ᵐ[μW.prod μN]
      fun p => (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d • CapelliMinorRestriction.perI P ψ π (coefX σ x₀ w m) ξ g p := by
  filter_upwards [CapelliMinorRestriction.ae_S hW hN] with p hp
  delta CapelliMinorRestriction.perI
  rw [tMapD_single, cJd_sinv P hP z hz _ _ g hp hg, cJd_single P hP, mul_smul]

theorem per_tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (P : Mat k r)
    (hP : IsUnit P.det) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    per P μW μN ψ π (tMapD σ (xJ P z) x₀ w (Pi.single d m)) ξ g =
      (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d • per P μW μN ψ π (coefX σ x₀ w m) ξ g := by
  rw [CapelliMinorRestriction.per_eq, CapelliMinorRestriction.per_eq, ← integral_smul]
  exact integral_congr_ae (perI_tMapD_single σ z hz P hP μW μN hW hN ψ π x₀ w d m ξ g hg)

end ConjugateTransportSingles

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinFub
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem finFub (hIS : S0.IntSStatement) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam' : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r) (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN)
    (hp : pOf ε = k + r) (hq : qOf ε = r + 1) (hgap : StepGap ε r h) (hlam : S7.IsHCParam lam')
    (hgl : GapAtLeast ε lam' h) (T' : S7.KType ε (lowK ε lam')) (μ' : Fin (2 * r + k + 1) → ℤ)
    (hμ : S7.IsMu lam' μ') (v₁ v₂ : T'.V) (ξ : Vp) (F : Mat k r → ℂ) (C : ℝ)
    (hFc : ContinuousOn F (UJset ε)) (hFb : ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h))
    (hrep : ∀ x ∈ UJset ε, F x = ∫ y, F (Formalism.MainNotions.S.umat y) *
        ⟪v₂, S7.PsiM T' μ' ((Formalism.MainNotions.S.umat y)⁻¹ * x) v₁⟫_ℂ ∂(Formalism.REAL.muG ε))
    (x : Mat k r) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hne : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x ≠ 0) :
    ∃ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      aaFun T' μ' P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ x₀ x ≠ 0 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hHW := hB.2.2.2.2.1
  have hHN := hB.2.2.2.2.2
  haveI : SigmaFinite μW := hHW.1
  haveI : SigmaFinite μN := hHN.1
  let integrand (y : Formalism.REAL.UJ ε)
      (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : Vp :=
    F (Formalism.MainNotions.S.umat y) • (finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat y) p •
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ)
  have hint : Integrable (Function.uncurry integrand) ((Formalism.REAL.muG ε).prod (μW.prod μN)) :=
    finFub_int' hIS k r ε u lam' h z c Vp π μW μN P hP hB hgap hlam hgl T' μ' hμ v₁ v₂ ξ F C hFc hFb x hx
  by_contra hall
  push Not at hall
  apply hne
  have hae := ae_mem_unitary_nilpotent_product z μW μN hHW hHN
  have step1 : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x =
      ∫ p, ∫ y, integrand y p ∂(Formalism.REAL.muG ε) ∂(μW.prod μN) := by
    delta per sInt
    apply integral_congr_ae
    filter_upwards [hae] with p hp'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      unitary_hermitian_form_mul_mem hp'.1.1 hp'.2.1
    have hJ := cayley_conj_mem_unitary_group hP (unitary_hermitian_form_mul_mem hs hx)
    show F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) • _ = _
    rw [hrep _ hJ, ← integral_smul_const]
    congr 1
    funext y
    exact mul_smul _ _ _
  rw [step1, ← integral_integral_swap hint]
  have hz : ∀ y, ∫ p, integrand y p ∂(μW.prod μN) = 0 := by
    intro y
    dsimp only [integrand]
    rw [integral_smul]
    have hy := unitary_matrix_mem_set ε y
    have h0 := hall _ (cayley_conj_inv_mem_hermitian_group hP hy)
    unfold aaFun sInt psiCoef at h0
    have hfun : (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat y) p •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) =
        fun p => ⟪v₂, S7.PsiM T' μ' (P * ((P⁻¹ * Formalism.MainNotions.S.umat y * P)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹) v₁⟫_ℂ •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ := by
      funext p
      delta finKer
      rw [conj_inv_mul_conj _ _ _ hd]
    rw [hfun, h0, smul_zero]
  simp only [hz, integral_zero]

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

