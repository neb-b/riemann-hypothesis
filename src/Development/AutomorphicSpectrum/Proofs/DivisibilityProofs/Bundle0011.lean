module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0005
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RemainderTermSummable
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem restTerm_bound_and_tendsto : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), (∃ c : ℝ, ∀ p : ℕ, 2 ≤ p → |restTerm j p (frob p τ) k Q| ≤ c * Real.log p / (p : ℝ) ^ 2) ∧ ∀ B₀ : ℕ, Tendsto (fun B : ℕ => ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ bad), restTerm j p (frob p τ) k Q) atTop (𝓝 (restSum j bad frob B₀ τ k Q)) :=
  @RootFieldNumerics.rest_term_bound_convergent

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelCurveDegreeNef
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem nefFib_integral_multiple : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → (∀ W : Ideal (MRing M.ι), (geoNum 1 W (fun _ => (combLine (M.line t) n).a) : ℝ) = q * M.curveDeg lam s W) ∧ (M.NefFib lam s → NefOnFibres M.P (combLine (M.line t) n).a) :=
  RootFieldNumerics.curveDeg_eq_and_nefOnFibres_of_coef

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelSemipositiveConj
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem semipositive_integral_multiple : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.Semipos t lam s → IsSemipositiveH M.P (combLine (M.line t) n) ∧ IsConjInvariantH (combLine (M.line t) n) :=
  RootFieldNumerics.root_model_line_semipositive

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootPowerSumMixedExpansion
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem mixDiff_mul_leibniz {σ : Type} (A B : MvPolynomial σ ℝ) :
    mixDiff (A * B) = mixDiff A * rename Sum.inl B + rename Sum.inr A * mixDiff B := by
  simp only [mixDiff, map_mul]
  ring

theorem mixDiff_eq_zero_of_isHomogeneous_zero {σ : Type} {Q : MvPolynomial σ ℝ}
    (hQ : Q.IsHomogeneous 0) : mixDiff Q = 0 := by
  have h : Q.totalDegree = 0 := Nat.eq_zero_of_le_zero hQ.totalDegree_le
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h
  rw [h]
  simp only [mixDiff, rename_C, sub_self]

theorem rootPs_mul_mixExpansion : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (τ : Ψ) (Q : MvPolynomial (Ψ × Fin N) ℝ), Q.IsHomogeneous (d + 1 - k) → ∃ Hs : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ, (∀ i, (Hs i).IsHomogeneous (d - k)) ∧ (k = d + 1 → ∀ i, Hs i = 0) ∧ IsMixExpansion d (mixDiff (rootPs τ k * Q)) (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i), rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a))) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q + (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) := by
  intro Ψ _ _ N d k hk1 hk2 τ Q hQ
  obtain ⟨Hs, hMix⟩ := GlobalTheory.T.exists_mixed_difference_expansion (Ψ × Fin N) (d + 1 - k) Q hQ
  unfold IsMixExpansion at hMix
  obtain ⟨hHs, hHdeg⟩ := hMix
  have hQl : (rename Sum.inl Q : MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ).IsHomogeneous (d + 1 - k) :=
    hQ.rename_isHomogeneous
  have hE := _root_.GlobalTheory.CompanionTheory.Ar.Num.isMixExpansion_psum_mul (Ψ × Fin N) N k (d + 1 - k) (fun a => (τ, a)) (rename Sum.inl Q) hQl
  unfold IsMixExpansion at hE
  obtain ⟨hE1, hE2⟩ := hE
  obtain ⟨Hs', hz, hmixQ, hdeg'⟩ : ∃ Hs' : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ,
      (k = d + 1 → ∀ i, Hs' i = 0) ∧ mixDiff Q = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Hs' i ∧
        ∀ i, (Hs' i).IsHomogeneous (d - k) := by
    by_cases hkd : k = d + 1
    · refine ⟨fun _ => 0, fun _ _ => rfl, ?_, fun _ => MvPolynomial.isHomogeneous_zero _ _ _⟩
      have h0 : Q.IsHomogeneous 0 := by
        have e : d + 1 - k = 0 := by omega
        rw [e] at hQ
        exact hQ
      simp only [mul_zero, Finset.sum_const_zero]
      exact mixDiff_eq_zero_of_isHomogeneous_zero h0
    · refine ⟨Hs, fun h => absurd h hkd, hHs, fun i => ?_⟩
      have h3 := hHdeg i
      have e : d + 1 - k - 1 = d - k := by omega
      rw [e] at h3
      exact h3
  unfold IsMixExpansion
  refine ⟨Hs', hdeg', hz, ?_, ?_⟩
  · rw [mixDiff_mul_leibniz, hmixQ]
    have h1 : mixDiff (rootPs τ k : MvPolynomial (Ψ × Fin N) ℝ) * rename Sum.inl Q =
        ∑ i, (X (Sum.inl i) - X (Sum.inr i)) *
          ((∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i),
            rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a)))
              (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q) := hE1
    have h2 : (rename Sum.inr (rootPs τ k : MvPolynomial (Ψ × Fin N) ℝ) :
        MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ) = ∑ a : Fin N, X (Sum.inr (τ, a)) ^ k := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [rootPs, map_sum, map_pow, rename_X]
    rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · intro i
    apply MvPolynomial.IsHomogeneous.add
    · have h4 := hE2 i
      have e : k - 1 + (d + 1 - k) = d := by omega
      rw [e] at h4
      exact h4
    · have hS : (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k :
          MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ).IsHomogeneous k :=
        MvPolynomial.IsHomogeneous.sum _ _ _ (fun a _ => MvPolynomial.isHomogeneous_X_pow _ _)
      by_cases hkd : k = d + 1
      · rw [hz hkd i, mul_zero]
        exact MvPolynomial.isHomogeneous_zero _ _ _
      · have h5 := hS.mul (hdeg' i)
        have e : k + (d - k) = d := by omega
        rw [e] at h5
        exact h5

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogPrimeDivPredBound
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem log_div_pred_le_of_lt (B p : ℕ) (hB : 128 ≤ B) (hp : B < p) (hL : 1 ≤ Real.log ((B : ℝ) + 1)) :
    Real.log p / ((p : ℝ) - 1) ≤ Real.log ((B : ℝ) + 1) / B := by
  have hB0 : (0 : ℝ) < B := by
    have : (128 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hpB : (B : ℝ) + 1 ≤ p := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hB1 : (0 : ℝ) < (B : ℝ) + 1 := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : Real.log p ≤ Real.log ((B : ℝ) + 1) + ((p : ℝ) - B - 1) / ((B : ℝ) + 1) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hp0 hB1)
    rw [Real.log_div hp0.ne' hB1.ne'] at h1
    have h2 : (p : ℝ) / ((B : ℝ) + 1) - 1 = ((p : ℝ) - B - 1) / ((B : ℝ) + 1) := by
      field_simp
      ring
    linarith
  rw [div_le_div_iff₀ hp1 hB0]
  have hd : (0 : ℝ) ≤ (p : ℝ) - B - 1 := by linarith
  have hfrac : (B : ℝ) * (((p : ℝ) - B - 1) / ((B : ℝ) + 1)) ≤ ((p : ℝ) - B - 1) * Real.log ((B : ℝ) + 1) := by
    have h3 : (B : ℝ) / ((B : ℝ) + 1) ≤ Real.log ((B : ℝ) + 1) := by
      refine le_trans ?_ hL
      rw [div_le_one hB1]
      linarith
    calc (B : ℝ) * (((p : ℝ) - B - 1) / ((B : ℝ) + 1))
        = ((p : ℝ) - B - 1) * ((B : ℝ) / ((B : ℝ) + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hd
  have h4 : Real.log p * B ≤ (Real.log ((B : ℝ) + 1) + ((p : ℝ) - B - 1) / ((B : ℝ) + 1)) * B :=
    mul_le_mul_of_nonneg_right hlog hB0.le
  nlinarith [h4, hfrac]

theorem sum_log_div_pred_SB :
    ∀ (B : ℕ) (bad S : Finset ℕ), 128 ≤ B → bad.card ≤ B →
      (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ bad)) →
      ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 := by
  intro B bad S hB hcard hS
  have hBR : (128 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hlogB : (4.85 : ℝ) ≤ Real.log B := by
    have h128 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    have h2 := Real.log_two_gt_d9
    have h3 : Real.log 128 ≤ Real.log B := Real.log_le_log (by norm_num) hBR
    rw [h128] at h3
    norm_num at h2 ⊢
    linarith
  have hLle : Real.log ((B : ℝ) + 1) ≤ Real.log B + 1 / B := by
    have hpos : (0 : ℝ) < ((B : ℝ) + 1) / B := by positivity
    have h1 := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by positivity) hB0.ne'] at h1
    have h2 : ((B : ℝ) + 1) / B - 1 = 1 / B := by
      field_simp
      ring
    linarith
  have hLge : 1 ≤ Real.log ((B : ℝ) + 1) := by
    have : Real.log B ≤ Real.log ((B : ℝ) + 1) := Real.log_le_log hB0 (by linarith)
    norm_num at hlogB
    linarith
  have hinv : 1 / (B : ℝ) ≤ 1 := by
    rw [div_le_one hB0]
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ B)]
  have hsmall : ∑ p ∈ S.filter (fun p => p ≤ B), Real.log p / ((p : ℝ) - 1)
      ≤ Real.log B + 17 / 5 := by
    refine GlobalTheory.CompanionTheory.Ar.Small.sum_log_div_pred_le (B : ℝ) _ (by linarith) ?_
    intro p hp
    obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
    exact ⟨(hS p hpS).1, by exact_mod_cast hpB⟩
  have hlarge : ∑ p ∈ S.filter (fun p => ¬ p ≤ B), Real.log p / ((p : ℝ) - 1)
      ≤ Real.log ((B : ℝ) + 1) := by
    have hsub : S.filter (fun p => ¬ p ≤ B) ⊆ bad := by
      intro p hp
      obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
      exact (hS p hpS).2.resolve_left hpB
    have hc : (S.filter (fun p => ¬ p ≤ B)).card ≤ B :=
      (Finset.card_le_card hsub).trans hcard
    have h1 : ∑ p ∈ S.filter (fun p => ¬ p ≤ B), Real.log p / ((p : ℝ) - 1)
        ≤ (S.filter (fun p => ¬ p ≤ B)).card • (Real.log ((B : ℝ) + 1) / B) := by
      refine Finset.sum_le_card_nsmul _ _ _ ?_
      intro p hp
      exact log_div_pred_le_of_lt B p hB (not_le.mp (Finset.mem_filter.mp hp).2) hLge
    have h2 : (S.filter (fun p => ¬ p ≤ B)).card • (Real.log ((B : ℝ) + 1) / B)
        ≤ (B : ℝ) * (Real.log ((B : ℝ) + 1) / B) := by
      rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right (by exact_mod_cast hc) ?_
      exact div_nonneg (by linarith) hB0.le
    have h3 : (B : ℝ) * (Real.log ((B : ℝ) + 1) / B) = Real.log ((B : ℝ) + 1) := by
      field_simp
    linarith
  norm_num at hlogB
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerHeightIdentityExpansion
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem identOnDecomposedForm : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (A₀ b₀ : ℝ) (F : RP Ψ N) (Q : Ψ → ℕ → RP Ψ N), T.IdentAt II hh frob B₀ A₀ b₀ → IsDecomp F Q → T.PPt II B₀ F = T.volT * (hh F - A₀ * ∑ σ, Sh T.j σ F - b₀ * ∑ σ, Tot σ F + ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B₀ τ k (Q τ k)) :=
  @RootFieldNumerics.tower_point_count_identity

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremBAveragedStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_theorem_B_averaged : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.ThmB II hh → T.PropA II → LabelInv (Ψ := Ψ) (N := N) hh → T.ThmBA II hh := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA | exact GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA <;> assumption)
end

