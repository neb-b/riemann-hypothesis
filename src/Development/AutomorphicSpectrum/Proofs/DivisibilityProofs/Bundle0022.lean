module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsMultiProjPrimeExtTo
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3PadicGlobal
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishAtPlaces
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumHeightChangeModel
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.Prop6Model

theorem arNum_mixDiff {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι ℤ)) {σ : Type}
    (A A' : σ → HermLine ι) (F : MvPolynomial σ ℝ) :
    arNum I P (Sum.elim A A') (mixDiff F) = arNum I P A F - arNum I P A' F := by
  obtain ⟨hadd, hsmul, -, -, hren⟩ := arNum_linear_arList_symm.1 K ι I P (σ ⊕ σ) (Sum.elim A A')
  have h : mixDiff F = rename Sum.inl F + C (-1) * rename Sum.inr F := by
    simp [mixDiff, sub_eq_add_neg]
  rw [h, hadd, hsmul, hren, hren, Sum.elim_comp_inl, Sum.elim_comp_inr]
  ring

theorem le_dimFl_succ (Ψ : Type) [Fintype Ψ] (τ : Ψ) (N : ℕ) : N ≤ dimFl Ψ N + 1 := by
  have hc : 1 ≤ Fintype.card Ψ := Fintype.card_pos_iff.2 ⟨τ⟩
  have h1 : N * (N - 1) / 2 ≤ dimFl Ψ N := by
    unfold dimFl
    exact Nat.le_mul_of_pos_left _ hc
  have h2 : N ≤ N * (N - 1) / 2 + 1 := by
    rcases N with _ | _ | n
    · simp
    · simp
    · have h3 : (n + 1) * 2 ≤ (n + 1 + 1) * (n + 1 + 1 - 1) := by
        rw [Nat.add_sub_cancel]
        nlinarith
      have h4 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 h3
      omega
  omega

variable {Ψ : Type} {N : ℕ}

theorem liePs_isHomogeneous (j m : ℕ) (l : Ψ ⊕ Ψ) :
    (liePs j m l : MvPolynomial (Ψ × Fin N) ℝ).IsHomogeneous m := by
  cases l with
  | inl τ =>
    refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℝ (τ, i)).pow m
  | inr τ =>
    refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using ((isHomogeneous_X ℝ (τ, i)).neg).pow m

theorem bracket_isHomogeneous [Fintype Ψ] [DecidableEq Ψ] (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (p k : ℕ) (τ : Ψ) :
    (bracket j φ p k τ : MvPolynomial (Ψ × Fin N) ℝ).IsHomogeneous (k - 1) := by
  unfold bracket
  have h := (isHomogeneous_C (Ψ × Fin N) (k : ℝ)).mul
    (IsHomogeneous.sum Finset.univ (fun τ' => C (co φ p k (Sum.inl τ) τ') * liePs j (k - 1) τ') (k - 1)
      fun τ' _ => by
        simpa using (isHomogeneous_C (Ψ × Fin N) (co φ p k (Sum.inl τ) τ')).mul
          (liePs_isHomogeneous (N := N) j (k - 1) τ'))
  simpa using h

end GlobalTheory.CompanionTheory.Ar.Num.Prop6Model

namespace GlobalTheory.CompanionTheory.Ar.Num


open Prop6Model in
theorem power_sum_height_model_change : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (R : SecondRoots M) (II : IntersectionSystem), IsIntersectionSystem II → ∀ (S : Finset Nat.Primes) (j : ℕ) (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)), R.IsChange S → R.LocalAtPlaces j S φ → ∀ t : ℝ, 0 < t → ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) → M.arFun II t (toA (pk τ k * Q)) = R.model.arFun II t (toA (pk τ k * Q)) + ∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket j (φ p) p k τ * Q)) := by
  intro Ψ _ _ N M R II hII S j φ hCh hLoc t ht τ k hk1 hkN Q hQ
  classical
  have hkd : k ≤ dimFl Ψ N + 1 := hkN.trans (le_dimFl_succ Ψ τ N)
  have hpk : (pk τ k : RP Ψ N).IsHomogeneous k := by
    refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℝ (τ, i)).pow k
  have hF : (pk τ k * Q : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) := by
    have h := hpk.mul hQ
    rwa [Nat.add_sub_cancel' hkd] at h
  have hδ : (M.δ : ℝ) ≠ 0 := by exact_mod_cast M.δ_pos.ne'
  have e1 := arFun_toA_eq_arNum Ψ N M II hII t _ hF
  have e2 : R.model.arFun II t (toA (pk τ k * Q)) =
      arNum (II M.K M.ι) M.P (R.x t) (pk τ k * Q) / (M.δ : ℝ) :=
    arFun_toA_eq_arNum Ψ N R.model II hII t _ hF
  obtain ⟨Hs, hHs, hHs0, hexp⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.rootPs_mul_mixExpansion Ψ N (dimFl Ψ N) k hk1 hkd τ Q hQ
  obtain ⟨hvert, hiso⟩ := hCh
  have hlink := _root_.GlobalTheory.CompanionTheory.Ar.Num.TopLink.arNum_eq_sum_log_val M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII M.K M.ι) (Ψ × Fin N) S R.pairs
    hvert (M.x t) (R.x t) (fun i => M.x_smooth t i) (fun i => R.x_smooth t i) (hiso t ht) _ _ hexp
  obtain ⟨A, i1, i2, i3, i4, hinj, hconst, hloc⟩ := hLoc
  have hdiff : arNum (II M.K M.ι) M.P (M.x t) (pk τ k * Q) - arNum (II M.K M.ι) M.P (R.x t) (pk τ k * Q) =
      ∑ p ∈ S, Real.log (p : ℕ) * ((M.δ : ℝ) * M.geoFun (toA (bracket j (φ p) p k τ * Q))) := by
    rw [← arNum_mixDiff]
    refine Eq.trans hlink (Finset.sum_congr rfl fun p hp => ?_)
    congr 1
    obtain ⟨hirr, hmod, hv⟩ := zp_model M.K M.ι M.P (dimFl Ψ N) M.arith p
    have hm3 := _root_.GlobalTheory.CompanionTheory.Ar.Num.PlacesFlagM3.flag_m3_padic M.K M.ι M.Ω M.y A hinj hconst (dimFl Ψ N) M.arith p Ψ N j (φ p) S R.pairs hvert
      (fun m _ hm O _ _ _ _ _ _ _ => (hloc p hp m hm O).1)
    have hz := _root_.GlobalTheory.CompanionTheory.Ar.Num.powerSumsVanish_extTo_of_atPlacesOver M.K M.ι M.Ω M.y A hinj hconst (dimFl Ψ N) M.arith p N (fun i => R.xdeg (τ, i))
      (fun m _ hm O _ _ _ _ _ _ _ => (hloc p hp m hm O).2 τ)
    have hH : (bracket j (φ p) p k τ * Q : RP Ψ N).IsHomogeneous (dimFl Ψ N) := by
      have h := (bracket_isHomogeneous (N := N) j (φ p) p k τ).mul hQ
      have e : k - 1 + (dimFl Ψ N + 1 - k) = dimFl Ψ N := by omega
      rwa [e] at h
    have h1 := _root_.GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_dvr (ZP p) _ hirr M.K M.ι _ _ hmod p Ψ N j (φ p) k hk1 hkd τ Q Hs hQ hHs hHs0 _
      (hv _ S R.pairs hvert) hm3 hz
    have h2 := _root_.GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const (ZP p) _ hirr M.K M.ι _ _ hmod 1 1 (Ψ × Fin N) M.xdeg
      (bracket j (φ p) p k τ * Q) (dimFl Ψ N) hH [] (by simp)
    simp only [Units.val_one, one_mul, pow_one, Nat.cast_one] at h2
    have h3 := genNum_zp_eq_rat M.K M.ι M.P p (Ψ × Fin N) M.xdeg (bracket j (φ p) p k τ * Q) []
    have h4 := _root_.GlobalTheory.CompanionTheory.Ar.Num.GeoModel.geoFun_toA_eq Ψ N M II hII _ hH
    refine h1.trans ?_
    refine Eq.trans h2 ?_
    rw [h3, h4]
    field_simp
  have hsum : ∑ p ∈ S, Real.log (p : ℕ) * ((M.δ : ℝ) * M.geoFun (toA (bracket j (φ p) p k τ * Q))) =
      (M.δ : ℝ) * ∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket j (φ p) p k τ * Q)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e1, e2]
  rw [hsum] at hdiff
  field_simp
  linarith

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelPointHeightDegree
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem ht_combLine_integral_multiple : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ) (W : Ideal (MRing M.ι)), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.IsPt W → 0 < degC W ∧ II M.K M.ι W 1 ![combLine (M.line t) n] = q * M.ht II t lam s W * degC W := by
  intro II hII Ψ _ N M t lam s q n W hn hW
  have hpos : 0 < degC W := GroundTheory.Heights₂.Heights.LowerBoundFree.degC_pos_of_isArithVar_one hW.1
  refine ⟨hpos, ?_⟩
  have hl : ∀ j, IsSmoothHerm (M.line t j) := by
    intro j
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hupd : ∀ B : HermLine M.ι, Function.update (![M.A] : Fin 1 → HermLine M.ι) 0 B = ![B] := by
    intro B
    funext k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp
  have hL : ∀ i, IsSmoothHerm ((![M.A] : Fin 1 → HermLine M.ι) i) := by
    intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact M.A_smooth
  have h := _root_.GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine II hII M.K M.ι W 1 ![M.A] 0 (Option (Ψ × Fin N)) (M.line t) n hW.1 hL hl
  simp only [hupd] at h
  have hd : (degC W : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [h, RootModel.ht, mul_assoc, div_mul_cancel₀ _ hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hn j, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Top
end

