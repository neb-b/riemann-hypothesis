module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumRangeBlocks
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDetGe
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMixedProj
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DivisionWithBasisOfDivision
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LargeParameterEstimates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0338
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Development.AutomorphicArithmetic.PrimeDiscriminants.ExcSet

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitInterpolationDetWeightFreeBallIndefinite
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.OrbitInterpWeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blockConst_deMul {r : ℕ} (X : Data E r) (s : ℕ) : GlobalTheory.Up.BlockConst X (deMul X.Ψ r X.p0 s) :=
  fun _ _ _ h => if_congr h rfl rfl

theorem gapsPairing_deMul {r : ℕ} (X : Data E r) (h0 : 0 < X.p0) (h1 : X.p0 < r) {s : ℕ} (hs : Even s) :
    GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.GapsPairing X (deMul X.Ψ r X.p0 s - kapW X) ((s : ℝ) - 2 * r + 2) := by
  obtain ⟨k, rfl⟩ := hs
  have hk : (k + k) / 2 = k := by omega
  intro τ
  refine ⟨fun i j hj hp => ?_, fun i0 i1 h0' h1' => ?_⟩
  · have e : ((j : ℕ) < X.p0 ↔ (i : ℕ) < X.p0) := by omega
    have hj' : ((j : ℕ) : ℤ) = (i : ℕ) + 1 := by exact_mod_cast hj
    simp only [Pi.sub_apply, deMul, kapW, hj']
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos (e.2 hi), if_pos hi]; omega
    · rw [if_neg (mt e.1 hi), if_neg hi]; omega
  · simp only [Pi.sub_apply, deMul, kapW, h0', h1', hk]
    rw [if_pos h0, if_neg (by omega)]
    have hr : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    rw [hr]
    push_cast
    linarith

theorem large : ∀ (r : ℕ) (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r), IsOrth X x0 →
    GlobalTheory.Up.FreeBall X G x0 (1 / (49 * (r : ℝ) ^ 2)) → 0 < X.p0 → X.p0 < r → 4 ≤ X.p0 * (r - X.p0) →
    ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s →
    ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x0) = 0 := by
  intro r X G x0 hx0 hFB h0 h1 hq s hs hsb
  have hd : 1 ≤ GlobalTheory.Up.dimX X := (GlobalTheory.Up.one_le_dimX_iff X).2 ⟨h0, h1⟩
  have hD : GlobalTheory.Up.dimX X = X.Ψ.card * (X.p0 * (r - X.p0)) := rfl
  have hOI := GlobalTheory.Up.OrbitInterpolation.orbitInterp (E := E) ⟨normFactor_rightBorel_holds, normFactor_leftAction_holds, pointwiseNorm_invariance_holds⟩
    poin_holds extFStatement_holds measInv_holds
    GlobalTheory.PoleExistence.poleEx_holds (GlobalTheory.PoleDbar.poleSolve measInv_holds)
    GlobalTheory.Up.polePoint_holds
  have hc : 0 < X.Ψ.card := by
    rcases Nat.eq_zero_or_pos X.Ψ.card with h | h
    · rw [hD, h, zero_mul] at hd; omega
    · exact h
  obtain ⟨τ, hτ⟩ := Finset.card_pos.1 hc
  have hr : (0 : ℝ) < r := by exact_mod_cast (h0.trans h1)
  have hρ : (0 : ℝ) < 1 / (49 * (r : ℝ) ^ 2) := by positivity
  have hDq : (4 : ℝ) * X.Ψ.card ≤ GlobalTheory.Up.dimX X := by
    rw [hD, Nat.cast_mul]
    have : (4 : ℝ) ≤ ((X.p0 * (r - X.p0) : ℕ) : ℝ) := by exact_mod_cast hq
    nlinarith [(Nat.cast_nonneg (α := ℝ) X.Ψ.card)]
  have hsR : 2 * (r : ℝ) + 50 * (r : ℝ) ^ 2 * (GlobalTheory.Up.dimX X : ℝ) + 1 ≤ s := by
    rw [hD]; exact_mod_cast hsb
  have hq1 : (GlobalTheory.Up.dimX X : ℝ) / (1 / (49 * (r : ℝ) ^ 2)) = 49 * (r : ℝ) ^ 2 * GlobalTheory.Up.dimX X := by
    field_simp
  have hcurv := (GlobalTheory.DivisionVolume.margin_iff h0 h1 (deMul X.Ψ r X.p0 s) ((s : ℝ) - 2 * r + 2)).2
    (gapsPairing_deMul X h0 h1 hs) x0 hx0
  have hs2 : 1 ≤ s / 2 := by obtain ⟨k, rfl⟩ := hs; omega
  refine hOI r X G x0 _ _ (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) ((s : ℝ) - 2 * r + 2)
    (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) hx0 hd hρ hFB (blockConst_deMul X s) (by linarith)
    (by rw [hq1]; nlinarith [sq_nonneg (r : ℝ)]) hcurv ?_
  refine cuspStatement_holds r X _ ⟨τ, hτ⟩ h0 h1 (fun i j hj hp => ?_) (fun i0 i1 h0' h1' => ?_)
  · have e : ((j : ℕ) < X.p0 ↔ (i : ℕ) < X.p0) := by omega
    simp only [deMul]
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos (e.2 hi), if_pos hi]
    · rw [if_neg (mt e.1 hi), if_neg hi]
  · simp only [deMul]
    rw [if_pos (by omega), if_neg (by omega)]
    omega

theorem orbit_interp_deMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) → ∀ (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r), IsOrth X x0 →
    GlobalTheory.Up.FreeBall X G x0 (1 / (49 * (r : ℝ) ^ 2)) → 0 < X.p0 → X.p0 < r → ∀ s : ℕ, Even s →
    2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s →
    ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x0) = 0 := by
  intro E _ _ _ r X hχ G x0 hx0 hFB h0 h1 s hs hsb
  by_cases hq : 4 ≤ X.p0 * (r - X.p0)
  · exact large r X G x0 hx0 hFB h0 h1 hq s hs hsb
  · exact _root_.GlobalTheory.Up.OrbitInterpSmall.orbit_interp_small E r X hχ G x0 hx0 hFB h0 h1 (by omega) s hs hsb

end GlobalTheory.OrbitInterpWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHeightLtGenus
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

theorem parOf_h_lt_g {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (j : Fin D.R.m) (a : Fin 2) :
    (parOf L j).h < (D.host.g a : ℝ) := by
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL0 : 0 < L.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos hx0 _
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  have hb1 : 1 < L.sc.b := by
    have := Real.add_one_lt_exp (ne_of_gt hL0)
    rw [hb]; linarith
  have hb0 : 0 < L.sc.b := by linarith
  have hb'0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    positivity
  have hS0 : 0 < L.Sc := L.Sc_pos
  have hη0 : 0 < L.etaSz := L.etaSz_pos
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hmk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have ht1 : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega
  have hn1 : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
  have hmR : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm2
  have hmkR : (D.R.m : ℝ) + 3 ≤ (D.R.k : ℝ) := by exact_mod_cast hmk
  have htR : (1 : ℝ) ≤ (D.R.t : ℝ) := by exact_mod_cast ht1
  have hnR : (1 : ℝ) ≤ (D.R.n : ℝ) := by exact_mod_cast hn1

  set den : ℝ := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
    (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) with hden
  have hd1 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
  have hn2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by nlinarith
  have hd2 : (D.R.m : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by
    have h1 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by nlinarith
    have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := by positivity
    nlinarith
  have hdm : (D.R.m : ℝ) ≤ den := by rw [hden]; linarith
  have hden0 : 0 < den := by linarith
  have hls : LevelStarExponents.lStar L = (D.R.m : ℝ) * L.sc.b / den := rfl
  have hl0 : 0 < LevelStarExponents.lStar L := by rw [hls]; positivity
  have hlb : LevelStarExponents.lStar L ≤ L.sc.b := by
    rw [hls, div_le_iff₀ hden0]
    nlinarith
  have hbl : 0 < L.sc.b / LevelStarExponents.lStar L := div_pos hb0 hl0
  have h1 := P.lstar1
  have h2 := P.t_le_eta

  have hh : (parOf L j).h = L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1 := rfl
  have hh3 : (parOf L j).h < 3 * L.sc.b + 1 := by rw [hh]; linarith

  have hkb : 1 ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  have hk8 : (D.R.k : ℝ) * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := le_self_pow₀ hkb (by norm_num)
  have h3 : 3 * L.sc.b + 1 ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
  have := (hg a).1
  linarith

end GlobalTheory.ExpTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPoints
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn
  GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

theorem rows_big_of_largeParameter {D : D7} (L : SizeData₂ D) (P5 : ParameterChoice' D L) (j : Fin D.R.m) (eps C x : ℝ)
    (hx : L.sc.x = x) (heps : L.sc.eps = eps) (hC : 2 * L.Ct + 1 ≤ C) (hC0 : L.Ct ≤ C) (hx2 : 2 ≤ x)
    (hB : Formalism.CohomologicalDescent.LargeParameterEstimates.Big (x ^ eps) x (Real.exp (x ^ (eps / 3))) (x ^ C)) :
    Formalism.CohomologicalDescent.LargeParameterEstimates.Rows (parOf L j) L.sc.X' (x ^ C) ∧
      Formalism.CohomologicalDescent.LargeParameterEstimates.Big (parOf L j).L (parOf L j).x L.sc.X' (x ^ C) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hk2 : (2 : ℝ) ≤ D.R.k := by
    have h1 := D.R.f_le_k
    have h2 : 0 < D.R.ord := Formalism.HC.Frame.ord_pos _
    exact_mod_cast (show 2 ≤ D.R.k by omega)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    exact_mod_cast this
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos

  have hw : L.sc.X' * L.sc.w'' D.R.n = L.sc.b / D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a
    rw [hx]
    field_simp
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a Scale.b
    rw [hx]
    positivity
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hbn : L.sc.b / D.R.n ≤ L.sc.b := div_le_self hb0.le hn1
  have hkS := P5.kS_le
  have hmt := P5.mteta
  have hS_le : L.Sc ≤ L.sc.w'' D.R.n / 2 := by
    have : 2 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := mul_le_mul_of_nonneg_right hk2 hSc.le
    linarith
  have heta_le : L.etaSz ≤ L.sc.w'' D.R.n / 2 := by
    have h1 : (2 : ℝ) ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by nlinarith
    have : 2 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := mul_le_mul_of_nonneg_right h1 heta.le
    linarith

  have htw := L.t_win
  rw [hx] at htw
  have hkt : D.R.k + D.R.m + 4 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hkt' : (D.R.k : ℝ) + D.R.m + 4 ≤ D.R.t := by exact_mod_cast hkt
  have hCt : x ^ L.Ct ≤ x ^ C := Real.rpow_le_rpow_of_exponent_le hx1 hC0
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, rfl, D.R.f_le_k, ?_, ?_⟩, ?_⟩
  ·
    show L.sc.a / L.sc.X' = L.sc.x * Real.exp L.sc.L / L.sc.X'
    rfl
  · show L.sc.X' * (L.Sc + L.etaSz) ≤ Real.exp L.sc.L
    have : L.sc.X' * (L.Sc + L.etaSz) ≤ L.sc.X' * L.sc.w'' D.R.n :=
      mul_le_mul_of_nonneg_left (by linarith) hX.le
    have hb : Real.exp L.sc.L = L.sc.b := rfl
    rw [hb]
    linarith
  · exact hkS
  · show 1 ≤ L.Sc
    rw [L.Sc_eq]
    have hD := P5.Del_ge.2.2.2
    have hN : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      have : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
      exact_mod_cast this
    have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by linarith)
    have h1 : (1 : ℝ) ≤ (D.s.Del : ℝ) := by nlinarith
    nlinarith
  · exact D.R.two_le_m
  · exact htw.2.trans hCt
  ·
    show (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ x ^ C * L.sc.x
    rw [hx]
    have hT := htw.2
    have ht1 := htw.1
    have hN3 : (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 3 * (x ^ L.Ct) ^ 2 := by
      have h3 : (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 3 * (D.R.t : ℝ) ^ 2 := by nlinarith
      have h4 : (D.R.t : ℝ) ^ 2 ≤ (x ^ L.Ct) ^ 2 := pow_le_pow_left₀ ht0 hT 2
      linarith
    have hsq : (x ^ L.Ct) ^ 2 * x ≤ x ^ C := by
      rw [sq, ← Real.rpow_add hx0]
      calc x ^ (L.Ct + L.Ct) * x = x ^ (L.Ct + L.Ct + 1) := by rw [Real.rpow_add hx0 (L.Ct + L.Ct) 1, Real.rpow_one]
        _ ≤ x ^ C := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hpos : 0 ≤ (x ^ L.Ct) ^ 2 := sq_nonneg _
    nlinarith
  · show Formalism.CohomologicalDescent.LargeParameterEstimates.Big (L.sc.x ^ L.sc.eps) L.sc.x (Real.exp (L.sc.x ^ (L.sc.eps / 3))) (x ^ C)
    rw [hx, heps]
    exact hB

end GlobalTheory.ExpTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialCHolInvariantMemNonZeroDivisors
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

theorem isOpen_isPreconnected_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (c : C) : IsOpen M.dom ∧ IsPreconnected M.dom := by
  have key : ∀ (X : Data E r) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (p0 : ℕ),
      X.Ψ = Ψ → X.Gm = Gm → X.p0 = p0 → IsOpen (GG Ψ Gm p0) ∧ IsPreconnected (GG Ψ Gm p0) := by
    intro X Ψ Gm p0 h1 h2 h3
    subst h1 h2 h3
    exact ⟨FourierCoefficientDomain.isOpen_dom X, (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected⟩
  exact key (M.comp c).toData M.Ψ M.Gm M.p0 (M.comp_Ψ c) (M.comp_Gm c) (M.comp_basePoint c)

theorem C_mem_nonZeroDivisors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (D : HA M), (∀ c, ∃ x : M.dom, (D : C → M.dom → ℂ) c x ≠ 0) →
    Polynomial.C D ∈ nonZeroDivisors (Polynomial (HA M)) := by
  intro E _ _ _ r U C _ _ M D hD
  have key : ∀ p : Polynomial (HA M), p * Polynomial.C D = 0 → p = 0 := by
    intro p hp
    apply Polynomial.ext
    intro i
    have hq : p.coeff i * D = 0 := by
      have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q i) hp
      simp only [Polynomial.coeff_mul_C, Polynomial.coeff_zero] at this
      exact this
    have hq' : ((p.coeff i : HA M) : C → M.dom → ℂ) * (D : C → M.dom → ℂ) = 0 := by
      have := congrArg (fun f : HA M => (f : C → M.dom → ℂ)) hq
      exact this
    rw [Polynomial.coeff_zero]
    apply Subtype.ext
    funext c x
    obtain ⟨x0, hx0⟩ := hD c
    obtain ⟨GD, hGD, hGD'⟩ := D.2.1 c
    obtain ⟨Gq, hGq, hGq'⟩ := (p.coeff i).2.1 c
    obtain ⟨hO, hC⟩ := isOpen_isPreconnected_dom M c
    have h0 : GD x0.1 ≠ 0 := by rw [← hGD']; exact hx0
    have hz := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero hO hC hGD hGq
      (fun y hy => by
        have := congrFun (congrFun hq' c) ⟨y, hy⟩
        simp only [Pi.mul_apply, Pi.zero_apply] at this
        rw [← hGD' ⟨y, hy⟩, ← hGq' ⟨y, hy⟩, mul_comm]
        exact this) x0.2 h0 x.1 x.2
    show ((p.coeff i : HA M) : C → M.dom → ℂ) c x = ((0 : HA M) : C → M.dom → ℂ) c x
    rw [hGq' x, hz]
    rfl
  refine mem_nonZeroDivisors_iff.2 ⟨fun x hx => key x ?_, key⟩
  rwa [mul_comm] at hx

end GlobalTheory.CuspEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeOverTypePrimeFixedPlaceOrConj
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimesOnto

theorem prime_eq_plGw_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  intro D k P hP hg
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hg
    have h0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) = ((0 : ℕ) : 𝓞 D.host.E) := by simpa using hg
    have := Nat.cast_injective h0
    exact (D.host.g_prime k).ne_zero this
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP, hne⟩
  have hw : w ∈ Formalism.BasicNotions.placesOver D.host.E (D.host.g k) := hg
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlacesExhaust.eq_plGw_or_isConjPl D k w hw
  · exact ⟨v, Or.inl (congrArg HeightOneSpectrum.asIdeal hv)⟩
  · refine ⟨v, Or.inr ?_⟩
    set c : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
      RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv with hc
    rw [Ideal.map_comap_of_equiv]
    ext y
    rw [Ideal.mem_comap]
    have key : (y : D.host.E) = D.host.conj ((c.symm y : 𝓞 D.host.E) : D.host.E) := by
      rw [← GlobalTheory.HeightCounting.FormsStep.complexConj_eq_hostConj]
      have : c (c.symm y) = y := c.apply_symm_apply y
      rw [← congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) this]
      rfl
    exact ((hv (c.symm y) y key).symm.trans Iff.rfl)
end GlobalTheory.TypePrimesOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEstimateStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}


set_option maxHeartbeats 1000000 in
theorem oneMapRowR_charOf (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : Fin D.R.m → ℂ)
    (i : Fin D.R.m) (h : OneMapRowR J R κ v₀ O ph i) :
    OneMapRowR J (charOf R F) κ v₀ (fun k => reOM (O k) F) ph i := by
  refine ⟨?_, fun hq => ?_⟩
  · obtain ⟨cc, ph', h0⟩ := h.1
    exact ⟨cc, ph', h0⟩
  · obtain ⟨O', h1, h2, h3⟩ := h.2 hq
    refine ⟨{ O' with }, h1, ⟨⟨h2.lift.field, h2.lift.std, h2.lift.v0, h2.lift.c0, h2.lift.lev⟩,
      fun t => ⟨(h2.tuple t).reps, (h2.tuple t).B, (h2.tuple t).xi, (h2.tuple t).phi, (h2.tuple t).half⟩,
      h2.act, h2.bad, h2.reps, h2.ep, h2.io, h2.w, h2.cov, h2.cxi, h2.model₂⟩, h3⟩

end Gen

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem phEff_eq_one : phEff p.R = fun _ => 1 := by
  funext i
  simp [phEff, p.phsOne i]

theorem splitPartRealisation_satisfies_qGuard : QGuard (R2 p) := p.qGuard

end Point

end GlobalTheory.BigOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpTie

theorem not_dvd_discr_host (D : D7) {l : ℕ} (hl : l.Prime) (hS : l ∉ Formalism.MainNotions.JumpSetsAlt.excSet D) :
    ¬ ((l : ℕ) : ℤ) ∣ NumberField.discr D.host.E :=
  UpperTheory.ExcSet.not_dvd_discr D hl hS

end GlobalTheory.ExpTie
end

