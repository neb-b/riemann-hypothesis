module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyKottwitzLatticeSeparableMinpoly
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc.SepLat

theorem kottwitz_lattice_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Y : G.Cˣ), (minpoly G.F (Y : G.C)).Separable →
    (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      ∃ z m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (z : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ k⁻¹ = z * m := by
  intro p _ G Y hsep hdeg
  filter_upwards [GlobalTheory.T.eventually_completedTensor_matrix_split_semilocal p G (Y : G.C) hdeg hsep, GlobalTheory.OrbFinAf.isIntV_mul_eventually G,
    GlobalTheory.OrbFinAf.KottLat.eventually_isIntV_map G ((1 : AfP p) ⊗ₜ[ℚ] (Y : G.C))] with w hA _ hY1
  intro k h1 _
  obtain ⟨K, _, R, Φ, hfin, hInt, Q, hQs, hQm⟩ := hA
  let γ₀ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom Y
  have hγv : (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] (Y : G.C) := rfl
  have hγi : (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) = inC G (w.1.adicCompletion ℚ) (Y : G.C) := rfl
  have hγ0 : GlobalTheory.OrbFinAf.IsIntV G w (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at hY1
    rw [hγv]; exact hY1
  have hconj : GlobalTheory.OrbFinAf.IsIntV G w (((k⁻¹)⁻¹ * γ₀ * k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) :
      w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    rw [inv_inv, Units.val_mul, Units.val_mul, hγi]
    exact h1
  obtain ⟨U, hU, hU1, hU2⟩ := GlobalTheory.OrbFinAf.KottLat.conj_integral R Φ hfin Q hQs γ₀ (by rw [hγv]; exact hQm)
    ((hInt _).1 hγ0) k⁻¹ ((hInt _).1 hconj)
  have hcomm : k⁻¹ * U⁻¹ * γ₀ = γ₀ * (k⁻¹ * U⁻¹) := by
    have e : U * (k * γ₀ * k⁻¹) = γ₀ * U := by simpa using hU
    calc k⁻¹ * U⁻¹ * γ₀ = k⁻¹ * U⁻¹ * (γ₀ * U) * U⁻¹ := by group
      _ = k⁻¹ * U⁻¹ * (U * (k * γ₀ * k⁻¹)) * U⁻¹ := by rw [e]
      _ = γ₀ * (k⁻¹ * U⁻¹) := by group
  refine ⟨k⁻¹ * U⁻¹, U, ?_, (hInt _).2 hU1, (hInt _).2 hU2, by group⟩
  show _ * _ = _ * _
  rw [← hγi, ← Units.val_mul, ← Units.val_mul, hcomm]

end GlobalTheory.FinClsLoc.SepLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeOfSmallSectionLogCountUpperBound
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNefAsymp

theorem tendsto_log_nat_div : Tendsto (fun m : ℕ => Real.log m / m) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  refine h.congr' (Eventually.of_forall fun m => ?_)
  simp

theorem tendsto_log_sq_div {X : ℕ → ℝ} {D : ℕ} {L : ℝ} (h1 : ∀ m, 1 ≤ X m)
    (hX : Tendsto (fun m : ℕ => X m / (m : ℝ) ^ (D + 1)) atTop (𝓝 L)) :
    Tendsto (fun m : ℕ => Real.log (X m ^ 2) / m) atTop (𝓝 0) := by
  set C : ℝ := max (L + 1) 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  have hev : ∀ᶠ m : ℕ in atTop, X m / (m : ℝ) ^ (D + 1) < C :=
    hX.eventually (gt_mem_nhds (lt_of_lt_of_le (lt_add_one L) (le_max_left _ _)))
  have hup : Tendsto (fun m : ℕ => 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => 2 * Real.log C * (m : ℝ)⁻¹) atTop (𝓝 (2 * Real.log C * 0)) :=
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul _
    have h2 := tendsto_log_nat_div.const_mul (2 * ((D : ℝ) + 1))
    have := h1.add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun m => ?_)
    simp [div_eq_mul_inv]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · refine Eventually.of_forall fun m => ?_
    exact div_nonneg (Real.log_nonneg (by nlinarith [h1 m])) (Nat.cast_nonneg m)
  · filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hP : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos hm0 _
    have hXle : X m ≤ C * (m : ℝ) ^ (D + 1) := by
      rw [div_lt_iff₀ hP] at hm; exact hm.le
    have hX0 : 0 < X m := lt_of_lt_of_le one_pos (h1 m)
    have hlog : Real.log (X m) ≤ Real.log C + ((D : ℝ) + 1) * Real.log m := by
      have := Real.log_le_log hX0 hXle
      rw [Real.log_mul (by positivity) hP.ne', Real.log_pow] at this
      push_cast at this
      linarith
    rw [Real.log_pow]
    rw [show 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m)
        = (2 * (Real.log C + ((D : ℝ) + 1) * Real.log m)) / m by ring]
    apply div_le_div_of_nonneg_right _ hm0.le
    push_cast
    linarith

theorem tendsto_bound_div (D q : ℕ) (hq : 3 ≤ q) {β g : ℕ → ℝ} {a γ : ℝ} (hβ0 : ∀ m, 0 ≤ β m)
    (hg0 : ∀ m, 0 ≤ g m) (hβ : Tendsto (fun m : ℕ => β m / (m : ℝ) ^ (D + 1)) atTop (𝓝 a))
    (hg : Tendsto (fun m : ℕ => g m / (m : ℝ) ^ D) atTop (𝓝 γ)) :
    Tendsto (fun m : ℕ => bound D q (β m) (g m) / (m : ℝ) ^ (D + 1)) atTop
      (𝓝 (Real.log q * (a / (((D + 1).factorial : ℝ) * Real.log ((q : ℝ) / 2))))) := by
  set Δ : ℝ := Real.log ((q : ℝ) / 2) with hΔdef
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hΔ : 0 < Δ := Real.log_pos (by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith)
  have hF : 0 < F := by rw [hFdef]; exact_mod_cast Nat.factorial_pos _
  have hFΔ : 0 < F * Δ := mul_pos hF hΔ
  set c1 : ℝ := ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2) with hc1
  have hc1p : 0 ≤ c1 := mul_nonneg (by positivity)
    (add_nonneg hΔ.le (div_nonneg (mul_nonneg (Nat.cast_nonneg D) (Real.log_nonneg one_le_two)) zero_le_two))
  set A : ℕ → ℝ := fun m => (β m + c1 * g m) / (F * Δ) with hA
  set B : ℕ → ℝ := fun m => ((D : ℝ) + 1) * g m / (2 * (F * Δ)) with hB
  have hunf : ∀ m, bound D q (β m) (g m) = Real.log q * (A m + B m * Real.log ((A m + 2 * B m + 1) ^ 2)) :=
    fun m => rfl
  have hinv := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hgP : Tendsto (fun m : ℕ => g m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := hg.mul hinv
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by ring)
  have hAP : Tendsto (fun m : ℕ => A m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (a / (F * Δ))) := by
    have := (hβ.add (hgP.const_mul c1)).div_const (F * Δ)
    rw [mul_zero, add_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hA]; ring)
  have hBP : Tendsto (fun m : ℕ => B m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := hgP.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)
  have hA0 : ∀ m, 0 ≤ A m := fun m => div_nonneg (add_nonneg (hβ0 m) (mul_nonneg hc1p (hg0 m))) hFΔ.le
  have hB0 : ∀ m, 0 ≤ B m := fun m => div_nonneg (mul_nonneg (by positivity) (hg0 m)) (by positivity)
  have hX1 : ∀ m, 1 ≤ A m + 2 * B m + 1 := fun m => by linarith [hA0 m, hB0 m]
  have hXP : Tendsto (fun m : ℕ => (A m + 2 * B m + 1) / (m : ℝ) ^ (D + 1)) atTop
      (𝓝 (a / (F * Δ) + 2 * 0 + 0 ^ (D + 1))) := by
    have := (hAP.add (hBP.const_mul 2)).add (hinv.pow (D + 1))
    exact this.congr' (Eventually.of_forall fun m => by ring)
  have hlog := tendsto_log_sq_div hX1 hXP
  have h2 : Tendsto (fun m : ℕ => B m * Real.log ((A m + 2 * B m + 1) ^ 2) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := ((hg.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))).mul hlog)
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)
  have := (hAP.add h2).const_mul (Real.log q)
  rw [add_zero] at this
  exact this.congr' (Eventually.of_forall fun m => by show _ = bound D q (β m) (g m) / _; rw [hunf]; ring)

theorem eventually_le_of_bound : ∀ (D : ℕ) (u β g : ℕ → ℝ) (a γ : ℝ), (∀ m, 0 ≤ β m) → (∀ m, 0 ≤ g m) →
    Tendsto (fun m : ℕ => β m / (m : ℝ) ^ (D + 1)) atTop (𝓝 a) →
    Tendsto (fun m : ℕ => g m / (m : ℝ) ^ D) atTop (𝓝 γ) →
    (∀ m q, 3 ≤ q → u m ≤ bound D q (β m) (g m)) → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ m : ℕ in atTop, u m ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro D u β g a γ hβ0 hg0 hβ hg hu ε hε
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF : 0 < F := by rw [hFdef]; exact_mod_cast Nat.factorial_pos _
  have ha : 0 ≤ a := ge_of_tendsto' hβ (fun m => div_nonneg (hβ0 m) (by positivity))
  set K : ℝ := Real.log 2 * a / (F * ε) with hK
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Real.exp K)
  set q : ℕ := max n 3 with hqdef
  have hq3 : 3 ≤ q := le_max_right _ _
  have hqn : (n : ℝ) ≤ q := by exact_mod_cast le_max_left n 3
  have hq3r : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hKΔ : K < Real.log ((q : ℝ) / 2) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith
  have hΔ : 0 < Real.log ((q : ℝ) / 2) := Real.log_pos (by linarith)
  have hlogq : Real.log q = Real.log ((q : ℝ) / 2) + Real.log 2 := by
    rw [Real.log_div hq0.ne' two_ne_zero]; ring
  have hL : Real.log q * (a / (F * Real.log ((q : ℝ) / 2))) < a / F + ε := by
    have e : Real.log q * (a / (F * Real.log ((q : ℝ) / 2)))
        = a / F + Real.log 2 * a / (F * Real.log ((q : ℝ) / 2)) := by
      rw [hlogq]; field_simp
    rw [e]
    have h1 : Real.log 2 * a < Real.log ((q : ℝ) / 2) * (F * ε) := by
      rw [hK, div_lt_iff₀ (mul_pos hF hε)] at hKΔ; exact hKΔ
    have h2 : Real.log 2 * a / (F * Real.log ((q : ℝ) / 2)) < ε := by
      rw [div_lt_iff₀ (mul_pos hF hΔ)]; nlinarith
    linarith
  have ht := tendsto_bound_div D q hq3 hβ0 hg0 hβ hg
  filter_upwards [ht.eventually (gt_mem_nhds hL), eventually_ge_atTop 1] with m hm hm1
  have hP : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast hm1) _
  rw [div_lt_iff₀ hP] at hm
  exact (hu m q hq3).trans hm.le

end GlobalTheory.HSNefAsymp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNorm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical


open GlobalTheory.LocNormTau in
theorem GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G (β : G.C) = β →
    ∀ (Y : G.Cˣ) (s : ℚ), (Y : G.C) * β * sh G (Y : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) →
      IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) → IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β hβ Y s hY hsep hdeg
  obtain ⟨f, hf0, hfc⟩ := exists_conj_neg G
  set e : G.C := algebraMap G.F G.C f with he_def
  set e' : G.C := algebraMap G.F G.C f⁻¹ with he'_def
  have hecomm : ∀ c : G.C, Commute e c := fun c => Algebra.commutes f c
  have he'comm : ∀ c : G.C, Commute e' c := fun c => Algebra.commutes f⁻¹ c
  have hee' : e * e' = 1 := by rw [he_def, he'_def, ← map_mul, mul_inv_cancel₀ hf0, map_one]
  have hsh_e : sh G e = -e := by
    simp only [sh, he_def, G.star_F, hfc, map_neg]
  have hsh_e' : sh G e' = -e' := by
    simp only [sh, he'_def, G.star_F, map_inv₀, hfc, inv_neg, map_neg]
  have hτe : (β : G.C) * sh G e * ((β⁻¹ : G.Cˣ) : G.C) = -e := by
    rw [hsh_e, mul_neg, neg_mul, (hecomm _).symm.eq, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨L, _, _, _, _, ι, hιinj, hιrange⟩ := GlobalTheory.FixedCentraliserReg.fixed_algebra_exists p G β Y hsep hdeg
  have hee : e * e ∈ Set.range ι := by
    refine (hιrange _).2 ⟨(hecomm _).mul_left (hecomm _), ?_⟩
    rw [sh_mul, hsh_e, neg_mul_neg, ← ((hecomm (β : G.C)).mul_left (hecomm _)).eq, mul_assoc, Units.mul_inv,
      mul_one]
  have hee'' : e' * e' ∈ Set.range ι := by
    refine (hιrange _).2 ⟨(he'comm _).mul_left (he'comm _), ?_⟩
    rw [sh_mul, hsh_e', neg_mul_neg, ← ((he'comm (β : G.C)).mul_left (he'comm _)).eq, mul_assoc, Units.mul_inv,
      mul_one]
  obtain ⟨d, hd⟩ := hee
  obtain ⟨di, hdi⟩ := hee''
  have hddi : d * di = 1 := hιinj (by
    rw [map_mul, hd, hdi, map_one, mul_assoc, ← mul_assoc e e', hee', one_mul, hee'])
  have hne2 : ∀ᶠ w : AwayP p in Filter.cofinite, w.1.asIdeal ≠ Ideal.span {2} := by
    rw [Filter.eventually_cofinite]
    refine Set.Subsingleton.finite ?_
    intro w₁ h₁ w₂ h₂
    simp only [Set.mem_setOf_eq, not_not] at h₁ h₂
    exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext (h₁.trans h₂.symm))
  filter_upwards [hne2, GlobalTheory.T.eventually_isIntegral_of_integralCoordsLocalTensor p G, GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion p G (ι d), GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion p G (ι di)] with w h2 hint hId hId'
  intro m hmY hmI hmI' hmτ
  set K := w.1.adicCompletion ℚ
  obtain ⟨hΦinj, hΦrange⟩ := GlobalTheory.FinClsLoc.baseChange_fixedCentraliser_alg p G β Y L ι hιinj hιrange K
  set Φ := Algebra.TensorProduct.map (AlgHom.id K K) ι with hΦ
  have hmτ' : tauR G β K (m : K ⊗[ℚ] G.C) = m := hmτ
  have hm'τ : tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) = ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) := by
    have h1 : tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) * (m : K ⊗[ℚ] G.C) = 1 := by
      rw [← hmτ', ← tauR_mul, Units.mul_inv, tauR_one]
    calc _ = tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) * ((m : K ⊗[ℚ] G.C) * ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C)) := by
          rw [Units.mul_inv, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  obtain ⟨y, hy⟩ := (hΦrange m).2 ⟨hmY, hmτ⟩
  obtain ⟨y', hy'⟩ := (hΦrange ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C)).2 ⟨hmY.units_inv_left, hm'τ⟩
  have hyy' : y * y' = 1 := hΦinj (by rw [map_mul, hy, hy', Units.mul_inv, map_one])
  set dK : K ⊗[ℚ] L := (1 : K) ⊗ₜ d
  set dK' : K ⊗[ℚ] L := (1 : K) ⊗ₜ di
  have hdd' : dK * dK' = 1 := by
    simp only [dK, dK', Algebra.TensorProduct.tmul_mul_tmul, one_mul, hddi]
    rfl
  have hΦd : Φ dK = inC G K (ι d) := by
    simp only [hΦ, dK, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have hΦd' : Φ dK' = inC G K (ι di) := by
    simp only [hΦ, dK', Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have pull : ∀ z : K ⊗[ℚ] L, IntC G w (Φ z) →
      ∃ g : Polynomial K, g.Monic ∧ (∀ i, g.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval z g = 0 := by
    intro z hz
    obtain ⟨g, hg1, hg2, hg3⟩ := hint _ hz
    refine ⟨g, hg1, hg2, hΦinj ?_⟩
    rw [← Polynomial.aeval_algHom_apply, hg3, map_zero]
  obtain ⟨a', b', hab⟩ := GlobalTheory.OddLocalNormEtale.exists_eq_sq_sub_mul_sq L w.1 h2 y y' dK dK' hyy' hdd'
    (pull y (by rw [hy]; exact hmI)) (pull y' (by rw [hy']; exact hmI'))
    (pull dK (by rw [hΦd]; exact hId)) (pull dK' (by rw [hΦd']; exact hId'))
  set a := Φ a'
  set b := Φ b'
  set E := inC G K e
  have haY := ((hΦrange a).1 ⟨a', rfl⟩).1
  have haτ : tauR G β K a = a := ((hΦrange a).1 ⟨a', rfl⟩).2
  have hbY := ((hΦrange b).1 ⟨b', rfl⟩).1
  have hbτ : tauR G β K b = b := ((hΦrange b).1 ⟨b', rfl⟩).2
  have hE : ∀ x : K ⊗[ℚ] G.C, Commute E x := commute_inC_of_forall G K e hecomm
  have hτE : tauR G β K E = -E := by
    rw [tauR_inC, hτe, map_neg]
  have habc : a * b = b * a := by
    simp only [a, b, ← map_mul, mul_comm a' b']
  have hEE : Φ dK = E * E := by rw [hΦd, hd, map_mul]
  have hm : (m : K ⊗[ℚ] G.C) = a * a - E * E * (b * b) := by
    rw [← hy, hab, map_sub, map_mul, map_mul, map_mul, hEE]
  set vv : K ⊗[ℚ] G.C := a + b * E
  have hτv : tauR G β K vv = a - E * b := by
    rw [tauR_add, tauR_mul, haτ, hbτ, hτE, neg_mul, sub_eq_add_neg]
  obtain ⟨key1, key2⟩ := norm_aux a b E (hE a) (hE b) habc
  rw [← hm] at key1 key2
  have hmv : Commute (m : K ⊗[ℚ] G.C) vv := by
    show (m : K ⊗[ℚ] G.C) * vv = vv * m
    calc (m : K ⊗[ℚ] G.C) * vv = vv * (a - E * b) * vv := by rw [key1]
      _ = vv * m := by rw [mul_assoc, key2]
  refine ⟨⟨vv, (a - E * b) * ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C), ?_, ?_⟩, ?_, ?_⟩
  · rw [← mul_assoc, key1, Units.mul_inv]
  · rw [mul_assoc, hmv.units_inv_left.eq, ← mul_assoc, key2, Units.mul_inv]
  · exact haY.add_left (hbY.mul_left (hE _))
  · change (m : K ⊗[ℚ] G.C) = vv * tauR G β K vv
    rw [hτv, key1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicMulIntegralGLStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockUpperParabolic_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E) (g : GLw n w), ∃ p ∈ GlobalTheory.LeviDesc.parP a n w, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = p * k := by
  first | exact @GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact | exact GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact | (intros; apply GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoZpowLocalUnitsPow
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

open ReciprocityTheory.ChartRestriction.G.Semi

theorem commGroup_mul_inv_zpow {G : Type} [CommGroup G] (x y : G) (a : ℤ) : (x * y⁻¹) ^ a = x ^ a * (y ^ a)⁻¹ := by
  rw [mul_zpow, inv_zpow]

theorem div_pull_pw_g {X Y : Scheme.{0}} (A : LB X) (H : LB Y) (φ : Y ⟶ X) (a : ℤ) (p q : (PUnit → A.ι) × H.ι) :
    (LB.div ((GlobalTheory.AbLaw.pw A a).pull φ) (GlobalTheory.AbLaw.pw H a)).g p q =
      (((LB.div (A.pull φ) H).g p q) ^ a : Γ(Y, (LB.div (A.pull φ) H).U p ⊓ (LB.div (A.pull φ) H).U q)ˣ) := by
  show res _ (∏ _k : PUnit, res _ (pullU φ _ (A.g _ _ ^ a)) ^ (1 : ℤ)) * (res _ (H.g p.2 q.2 ^ a))⁻¹ =
    (res _ (∏ _k : PUnit, res _ (pullU φ _ (A.g _ _)) ^ (1 : ℤ)) * (res _ (H.g p.2 q.2))⁻¹) ^ a
  simp only [Fintype.prod_unique, zpow_one, map_zpow]
  exact (commGroup_mul_inv_zpow _ _ a).symm

theorem lbIso_pw_pull_gw : ∀ (X Y : Scheme.{0}) (φ : Y ⟶ X) (A : LB X) (H : LB Y) (w : LB.Iso H (A.pull φ)), w.IsGen → ∀ a : ℤ, ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw H a) ((GlobalTheory.AbLaw.pw A a).pull φ), wa.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : H.ι), φ (r z) ∈ A.U k → r z ∈ H.U k' → Geo.Tor.gw wa r z k k' = Geo.Tor.gw w r z k k' ^ a := by
  intro X Y φ A H w hw a
  refine ⟨⟨fun p => w.s p ^ a⟩, ?_, ?_⟩
  · intro p q
    have e := congrArg (· ^ a) (hw p q)
    simp only [mul_zpow, ← map_zpow] at e
    exact e.trans (congrArg (· * res _ (w.s q ^ a)) (div_pull_pw_g A H φ a p q).symm)
  · intro Z r z k k' _ _
    exact map_zpow _ _ a

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactBoxOfUnitaryTranslateCompact
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BoxMove

theorem inBox_image_mul : ∀ (D : D7) (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.InBox K (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) → GlobalTheory.Unf.InBox K' x := by
  intro D V n Q hQ K hK
  have hmt : Continuous (Formalism.L2.Theta.mt V) := Units.continuous_val.comp continuous_subtype_val
  have hf : Continuous fun p : GA D V × Mx D V.rank n => (HMul.hMul (Formalism.L2.Theta.mt V p.1) p.2 : Mx D V.rank n) :=
    (hmt.comp continuous_fst).matrix_mul continuous_snd
  refine ⟨(fun p : GA D V × Mx D V.rank n => (HMul.hMul (Formalism.L2.Theta.mt V p.1) p.2 : Mx D V.rank n)) '' (Q ×ˢ K), (hQ.prod hK).image hf, ?_⟩
  rintro y hy x ⟨k, hk, h0⟩
  refine ⟨(HMul.hMul (Formalism.L2.Theta.mt V y) k : Mx D V.rank n), ⟨(y, k), ⟨hy, hk⟩, rfl⟩, ?_⟩
  have hyy : Formalism.L2.Theta.mt V y * Formalism.L2.Theta.mt V y⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hx : x - (HMul.hMul (Formalism.L2.Theta.mt V y) k : Mx D V.rank n) = (HMul.hMul (Formalism.L2.Theta.mt V y) ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) - k) : Mx D V.rank n) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hyy, Matrix.one_mul]
  rw [hx, Matrix.map_mul, h0, Matrix.mul_zero]

end GlobalTheory.BoxMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorBoundMatrixMul
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem denom_bound_mul : ∀ (E κ ι : Type) [Field E] [NumberField E] [Fintype κ] [Fintype ι] (T : Matrix κ ι E), ∃ M : ℕ, 0 < M ∧ ∀ (L : ℕ) (x : ι → E), (∀ i, IsIntegral ℤ ((L : E) * x i)) → ∀ k, IsIntegral ℤ (((M * L : ℕ) : E) * ∑ i, T k i * x i) := by
  intro E κ ι _ _ _ _ T
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image (fun p : κ × ι => T p.1 p.2))
  refine ⟨y.natAbs ^ 2, by positivity, ?_⟩
  intro L x hx k
  have hT : ∀ i, IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : E) * T k i) := by
    intro i
    have h1 := hint (T k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
    have hy' : IsIntegral ℤ ((y : E)) := by
      have := (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E y)); simpa using this
    have : ((y.natAbs ^ 2 : ℕ) : E) * T k i = (y : E) * (y • T k i) := by
      rw [zsmul_eq_mul]
      have : ((y.natAbs ^ 2 : ℕ) : E) = ((y ^ 2 : ℤ) : E) := by
        have hz : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by push_cast; exact sq_abs y
        rw [← hz, Int.cast_natCast]
      rw [this]; push_cast; ring
    rw [this]
    exact hy'.mul h1
  have heq : (((y.natAbs ^ 2 * L : ℕ) : E) * ∑ i, T k i * x i)
      = ∑ i, (((y.natAbs ^ 2 : ℕ) : E) * T k i) * ((L : E) * x i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [heq]
  have := Subalgebra.sum_mem (integralClosure ℤ E) (t := Finset.univ)
    (f := fun i => (((y.natAbs ^ 2 : ℕ) : E) * T k i) * ((L : E) * x i))
    (fun i _ => Subalgebra.mul_mem _ (hT i) (hx i))
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceIsPrimeOfOfHeightOneNormalLocalModelStatement
section
open GlobalTheory GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_isPrimeOf_of_height_one_normal_localModel : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (R : Subring K), IsLocModel cK R → IsIntegrallyClosed R →
    ∀ p : Ideal R, p.IsPrime → p.height = 1 →
    ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ g ∉ p) := by
  first | exact @GlobalTheory.FieldPair.exists_place_isPrimeOf_of_height_eq_one | exact GlobalTheory.FieldPair.exists_place_isPrimeOf_of_height_eq_one | (intros; apply GlobalTheory.FieldPair.exists_place_isPrimeOf_of_height_eq_one <;> assumption)
end

