module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangLowerBoundRational
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem zhang_lower_bound_root_model : SuccessiveMinimaLowerBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ), IsRatWt lam →
      M.Semipos t lam s → M.NefFib lam s → (∀ W, M.IsPt W → e ≤ M.ht II t lam s W) →
      ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) ≤
        M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  intro hZ1 II hII Ψ _ N M t lam s e hrat hsemi hnef hpts
  obtain ⟨q, n, hq, hn⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.clear_rat_weight_coef Ψ N M lam s hrat
  have hp := _root_.GlobalTheory.CompanionTheory.Ar.Top.semipositive_integral_multiple Ψ N M t lam s q n hn hsemi
  have hnf := (_root_.GlobalTheory.CompanionTheory.Ar.Top.nefFib_integral_multiple Ψ N M t lam s q n hn).2 hnef
  have hW : ∀ W, IsArithVar W 1 → M.P ≤ W →
      ((q : ℝ) * e) * degC W ≤ II M.K M.ι W 1 ![combLine (M.line t) n] := by
    intro W h1 h2
    have hpt : M.IsPt W := ⟨h1, h2⟩
    obtain ⟨hd, hI⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple II hII Ψ N M t lam s q n W hn hpt
    rw [hI]
    have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hd' : (0 : ℝ) ≤ degC W := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpts W hpt) hq') hd'
  have key := hZ1 M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) II hII.1 M.arith le_rfl
    hp.1 hnf hp.2 hW
  have hgeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      (M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have := _root_.GlobalTheory.CompanionTheory.Ar.Top.geoFun_comb_mixed II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n) (fun _ j => hn j)
    simpa [geomDeg, Finset.prod_const] using this
  rw [hgeo, _root_.GlobalTheory.CompanionTheory.Ar.Top.top_comb_eq_arFun II hII Ψ N M t lam s q n hn] at key
  have hδ : (0 : ℝ) < M.δ := by exact_mod_cast M.δ_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : (0 : ℝ) < (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) := by positivity
  refine le_of_mul_le_mul_left ?_ hc
  calc (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) * (((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N))
      = ((dimFl Ψ N + 1 : ℕ) : ℝ) * ((q : ℝ) * e) *
          ((M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N)) := by
        push_cast; ring
    _ ≤ _ := key

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangUpperBoundDensePoints
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem zhang_upper_bound_root_model : SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ) (F : Set (Ideal (MRing M.ι))), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → IsZariskiDense M.P F → (∀ W ∈ F, M.IsPt W ∧ M.ht II t lam s W ≤ e) → M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) ≤ ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) := by
  intro hZ II hII Ψ _ N M t lam s e F hrat hsp hnef hF hpt
  obtain ⟨q, n, hq, hn⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.clear_rat_weight_coef Ψ N M lam s hrat
  have hsemi := _root_.GlobalTheory.CompanionTheory.Ar.Top.semipositive_integral_multiple Ψ N M t lam s q n hn hsp
  have hnf := (_root_.GlobalTheory.CompanionTheory.Ar.Top.nefFib_integral_multiple Ψ N M t lam s q n hn).2 hnef
  have hA := _root_.GlobalTheory.CompanionTheory.Ar.Top.top_comb_eq_arFun II hII Ψ N M t lam s q n hn
  have hG := _root_.GlobalTheory.CompanionTheory.Ar.Top.geoFun_comb_mixed II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n)
    (fun _ j => hn j)
  have hGeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have hprod : (∏ _k : Fin (dimFl Ψ N), linA lam (s : ℝ)) = linA lam s ^ dimFl Ψ N := by
      simp
    rw [hprod] at hG
    exact hG
  have key := hZ M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) F II hII.1
    M.arith le_rfl hsemi.1 hnf hsemi.2
    (by
      intro W hW
      obtain ⟨hp, hle⟩ := hpt W hW
      obtain ⟨-, hI⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple II hII Ψ N M t lam s q n W hn hp
      refine ⟨hp.1, hp.2, ?_⟩
      rw [hI]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg q))
        (Nat.cast_nonneg _))
    hF
  rw [hA, hGeo] at key
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hδ : (0 : ℝ) < M.δ := Nat.cast_pos.mpr M.δ_pos
  have hpos : (0 : ℝ) < M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) := mul_pos hδ (pow_pos hqR _)
  refine le_of_mul_le_mul_left ?_ hpos
  calc _ ≤ _ := key
    _ = _ := by push_cast; ring

end GlobalTheory.CompanionTheory.Ar.Top
end

