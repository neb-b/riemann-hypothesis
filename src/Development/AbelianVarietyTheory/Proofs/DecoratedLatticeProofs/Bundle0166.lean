module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalThetaFunctionsLevelFockDegree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0148
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperators
section
namespace I195MixedCoordinates_784daf8855fd46d1374640e6

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_784daf8855fd46d1374640e6

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.FlatHeis

theorem flatAt_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → (∀ w, evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x y = heisO ψ V₀ W₀ w (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x y)) ∧ (∀ w, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) = heisO ψ V₀ W₀ w (flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ)) ∧ ∀ γ, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ (ratW W₀ V₀ γ) = flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ 0 := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU x y Ψ hΨ
  have hMV := _root_.GlobalTheory.MixValues.mixed_values D ψ hψ
  have hHT := _root_.GlobalTheory.HeisTarget.main D ψ hψ
  have hS : ∀ x', IsThetaFunO ψ V₀ W ((_root_.I195MixedCoordinates_784daf8855fd46d1374640e6.source dV) W ψ vS.μ vS.𝓕 Ψ x') := fun x' =>
    hMV.1 V V₀ W ρ dV vS.μ vS.𝓕 vS.covol Ψ hΨ x'
  have hE : ∀ x', IsThetaFunO ψ V₀ W₀ (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x' y) := fun x' =>
    hMV.2 V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol _ (hS x') y
  have h1 : ∀ x' w, evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x' y =
      heisO ψ V₀ W₀ w (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x' y) := by
    intro x' w
    have a := (_root_.GlobalTheory.HeisMixSource.heis_mixS D ψ hψ V V₀ W ρ dV vS Ψ hΨ).2.2.1 x' (dW.inc0 V₀ w)
    have b := (hHT V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol _ (hS x')).2.1 w y
    change I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ vS.μ vS.𝓕
      (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x' =
      heisO ψ V₀ W (dW.inc0 V₀ w)
        (I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ vS.μ vS.𝓕 Ψ x') at a
    change I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target dW V₀ ψ vT.μ vT.𝓕
      (heisO ψ V₀ W (dW.inc0 V₀ w)
        (I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ vS.μ vS.𝓕 Ψ x')) y =
      heisO ψ V₀ W₀ w (I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target dW V₀ ψ vT.μ vT.𝓕
        (I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ vS.μ vS.𝓕 Ψ x') y) at b
    unfold evalAt
    rw [a, b]
  refine ⟨fun w => h1 x w, fun w => ?_, fun γ => ?_⟩
  · funext w'
    show ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) w' u ∂vU.ν =
      ψ (symplOH V₀ W₀ w' w) * ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ (w' + w) u ∂vU.ν
    rw [← integral_const_mul]
    refine congrArg (fun F : UX D ρ → ℂ => ∫ u, F u ∂vU.ν) (funext fun u => ?_)
    simp only [flatFun, h1, heisO]
    ring
  · show ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ (ratW W₀ V₀ γ) u ∂vU.ν =
      ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ 0 u ∂vU.ν
    refine congrArg (fun F : UX D ρ → ℂ => ∫ u, F u ∂vU.ν) (funext fun u => ?_)
    have q := (hE (x ⬝ u.1.1)).quasi γ 0
    rw [add_zero, symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul] at q
    unfold flatFun
    rw [q]

end GlobalTheory.FlatHeis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPartitionRowsNumericDatumMemIcc
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsRangeS

variable {D : D7}

variable {D : D7}

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.n
    omega
  exact_mod_cast this

theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

theorem uW_numRec (large₂ : SizeData₂ D) (hD : ∃ n : ℕ, D.s.Del = n) (u : D.what₂.Word) (z : RPl D.R) (i : Fin D.R.k) :
    (numDatumOfParameters D large₂).uW (codeRec large₂ u) z i = (D.hcW u (tauPl D z)).u i := by
  obtain ⟨n, hn⟩ := hD
  obtain ⟨r, hr⟩ := i
  unfold NumDatum.uW
  split_ifs with h h1
  · obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by have := h.1; simp only at this; omega⟩
    have h' : l < D.R.k - 2 := by have := h.2; simp only at this; omega
    have a := D.s.u_letter u (tauPl D z) l h'
    have h2 : D.s.letter u ⟨l, h'⟩ = true := h1
    rw [if_pos h2, D.hcW_v] at a
    have h3 : (((numDatumOfParameters D large₂).Del : ℕ) : ℚ) = D.s.Del := by
      show ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del
      rw [hn, Nat.floor_natCast]
    rw [a, h3]
    rfl
  · obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by have := h.1; simp only at this; omega⟩
    have h' : l < D.R.k - 2 := by have := h.2; simp only at this; omega
    have a := D.s.u_letter u (tauPl D z) l h'
    have h2 : ¬ D.s.letter u ⟨l, h'⟩ = true := h1
    rw [if_neg h2, D.hcW_v] at a
    rw [a]
    rfl
  · by_cases h0 : r = 0
    · subst h0
      exact (D.hcW_first u _ hr).symm
    · obtain rfl : r = D.R.k - 1 := by simp only at h; omega
      exact (D.hcW_last u _ (by omega)).symm

theorem nu_numRec (large₂ : SizeData₂ D) (hD : ∃ n : ℕ, D.s.Del = n) (u : D.what₂.Word) (j : ℕ) (z : RPl D.R) (i : ℕ) :
    (((numDatumOfParameters D large₂).nu (codeRec large₂ u) j z i : ℚ) : ℝ) = DV.nuRow D u j (tauPl D z) i := by
  have e1 : (numDatumOfParameters D large₂).srcPar (codeRec large₂ u) z i = DV.srcPar D u (tauPl D z) i := by
    unfold NumDatum.srcPar DV.srcPar
    by_cases h : i < D.R.k
    · rw [dite_eq_left h, dite_eq_left h]
      exact uW_numRec large₂ hD u z ⟨i, h⟩
    · rw [dite_eq_right h, dite_eq_right h, D.hcW_e]
  have e2 : (((numDatumOfParameters D large₂).eQ j z : ℚ) : ℝ) = DV.wSz D j (tauPl D z) := by
    unfold NumDatum.eQ DV.wSz
    by_cases h : 1 ≤ j ∧ j ≤ D.R.m
    · rw [dite_eq_left h, dite_eq_left h]
    · rw [dite_eq_right h, dite_eq_right h, Rat.cast_zero]
  unfold NumDatum.nu DV.nuRow
  rw [e1, ← e2]
  push_cast
  rfl

theorem nuRow_zero_le_three_mul (large₂ : SizeData₂ D) (P : ParameterChoice' D large₂) (hb : ∀ t, (large₂.bT t : ℝ) ≤ 2 * large₂.sc.b')
    (hT : ThickUp large₂) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    DV.nuRow D u (i + 1) τ 0 ≤ 3 * large₂.sc.a := by
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk0 : 0 < D.R.k := by omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hkN : (D.R.k : ℝ) ≤ D.R.N i := by
    have : D.R.k ≤ D.R.N i := by unfold Ranks.N; omega
    exact_mod_cast this
  have hx := large₂.sc.one_lt_alt
  have hb1 := one_le_b large₂
  have hb' := b'_pos large₂
  have hba : large₂.sc.b ≤ large₂.sc.a := le_mul_of_one_le_left (by linarith) hx.le
  have hX : 2 ≤ large₂.sc.X' := by
    have h1 : 1 ≤ large₂.sc.x ^ (large₂.sc.eps / 3) := Real.one_le_rpow hx.le (by linarith [large₂.sc.eps_pos])
    have h2 := Real.add_one_le_exp (large₂.sc.x ^ (large₂.sc.eps / 3))
    unfold Scale.X'
    linarith
  have hb'a : large₂.sc.b' ≤ large₂.sc.a / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hX
  have hw : large₂.sc.w'' D.R.n ≤ large₂.sc.b' :=
    div_le_self hb'.le (one_le_mul_of_one_le_of_one_le hx.le (one_le_n D))
  have he := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have heta : 2 * large₂.etaSz ≤ large₂.sc.b' := by
    have h1 : (2 : ℝ) ≤ D.R.m * ((D.R.t : ℝ) + 1) := by nlinarith
    linarith [P.mteta, mul_le_mul_of_nonneg_right h1 he.le]
  have hSc : 5 * large₂.Sc ≤ large₂.sc.b' := by
    linarith [P.kS_le, mul_le_mul_of_nonneg_right hk' hS.le]
  have hwj : wj D (i + 1) τ = (((D.hc τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (by simpa using hi)]
    rfl
  rw [RowWeightLemmas.nuRow_head D u i hi τ 0 hk0, D.hcW_first u τ hk0, D.hcW_e]
  push_cast
  rw [← hwj]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, htt⟩ := exists_top ha
    rw [(large₂.top_u τ t hk0 htt).1]
    have a1 := (large₂.win_top (i + 1) (by omega) hi τ t htt).2
    have a2 := (large₂.aT_win t).2
    have a3 : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)))
    have a4 : large₂.sc.a / ((D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)) ≤ large₂.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : large₂.sc.b' / large₂.sc.x ≤ large₂.sc.b' := div_le_self hb'.le hx.le
    linarith [hb t]
  · have h1 := P.cloud_place_bound τ (by omega) ha
    have h2 := (large₂.cloud_v τ ⟨0, by omega⟩).2
    push_cast at h1
    by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have a1 := hT (i + 1) (by omega) hi τ hc
      linarith
    · have a1 := (large₂.win_thin (i + 1) (by omega) hi τ ⟨(D.eTau τ).2, ha, hc⟩).2
      linarith

theorem nu_numRec_mem : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), ∀ j ∈ (numDatumOfParameters D L).lifts, ∀ z,
    ∀ i < D.R.N (j - 1), 0 ≤ (numDatumOfParameters D L).nu (codeRec L u) j z i ∧
      (((numDatumOfParameters D L).nu (codeRec L u) j z i : ℚ) : ℝ) ≤ 3 * L.sc.a := by
  rintro D large₂ CY ⟨⟨P⟩, -, -, hN, hD, hT⟩ u j hj z r hr
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := j2
  have hr' : r < D.R.N i := hr
  have e := nu_numRec large₂ hD u (i + 1) z r
  constructor
  · have h := (RowWeightLemmas.nuRow_pos D u i hi (tauPl D z) r hr').le
    rw [← e] at h
    exact_mod_cast h
  · rw [e]
    exact (RowWeightLemmas.nuRow_anti' D u i hi _ r 0 (Nat.zero_le _) hr').trans
      (nuRow_zero_le_three_mul large₂ P hN.2.2.2.2 hT u i hi _)

end GlobalTheory.CoreHt.RowsRangeS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem isKFinVec_of_isFockVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ K : Subgroup (GA D S), IsCompact (K : Set (GA D S)) → (∀ k ∈ K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ f, IsFockVec ψ θ S T sS sT f → IsKFinVec om K f := by
  intro D ψ θ S T χS χT om sS sT hW hθ hS hT K hK hc f hf
  obtain ⟨hth, N, hN⟩ := hf
  obtain ⟨U, hU, hUK⟩ := _root_.GlobalTheory.Core.Rk.Level.exists_common_level D ψ S T χS χT om hW (K : Set (GA D S)) hK f hth
  have hfd := _root_.GlobalTheory.FockLevelDim.finiteDimensional_level_degree D ψ θ S T sS sT hW.std hθ hS hT U hU N
  refine @Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ hfd (Submodule.span_mono ?_)
  rintro g ⟨k, hk, rfl⟩
  exact ⟨hW.om_pres _ f hth, hUK k hk,
    _root_.GlobalTheory.CartanFockDeg.om_keeps_fockDeg D ψ θ S T χS χT om sS sT hW hθ k (hc k hk) N f hth hN⟩

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorsLatticeVacuaOffFiniteSet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.VacOffS

variable {D : D7}

theorem exists_under (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem latO_at_le {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {NS NT : ℕ}
    (hS : ∀ x ∈ L0c D S, (NS : D.host.E) • x ∈ LS) (hT : ∀ x ∈ L0c D T, (NT : D.host.E) • x ∈ LT)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E)) (fun u => u = v) ≤
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  set M : ℕ := NS * NT with hMdef
  have hM0 : (M : D.host.F) ≠ 0 := by
    intro h
    apply hv
    have : (M : 𝓞 D.host.F) = 0 := by
      apply RingOfIntegers.ext; simpa using h
    rw [this]; exact zero_mem _
  have hval : HeightOneSpectrum.valuation D.host.F v (M : D.host.F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F) M, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  obtain ⟨γ, hγ, rfl⟩ : ∃ γ ∈ intAf D.host.F, α = algebraMap D.host.F _ (M : D.host.F) * γ := by
    refine ⟨α * algebraMap D.host.F _ ((M : D.host.F)⁻¹), fun w => ?_, ?_⟩
    · rw [map_mul, AlgHom.commutes]
      by_cases hw : w = v
      · subst hw
        refine mul_mem (hα w) ?_
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀, hval, inv_one]
      · rw [hP w hw, zero_mul]; exact zero_mem _
    · rw [mul_comm α, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]
  have hs' : s ∈ L0c D S := by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact hs
  have ht' : t ∈ L0c D T := by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact ht
  refine AddSubgroup.subset_closure ⟨γ, hγ, fun w hw => (hw trivial).elim, a, ha, _, hS s hs', _, hT t ht', ?_⟩
  ext i j
  simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.VacLat.pairA_smul, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul]
  congr 1
  rw [Algebra.smul_def, map_natCast, hMdef]
  simp only [star_mul', star_natCast, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.ChainOnto.VacOffS


open GlobalTheory.ChainOnto.VacOffS in
theorem GlobalTheory.ChainOnto.fock_vacFin_off :
    ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, ∀ v ∉ c.S, VacFin c.ψ s.V s'.V v (p.pt φ) := by
  intro D _ c hc k _ s s' hs hs' p hp φ v hv
  classical
  obtain ⟨ξ, f₀, hf₀, e, he, hth⟩ := hp.vec
  obtain ⟨NS, hNS, hNSv⟩ := hs.base
  obtain ⟨NT, hNT, hNTv⟩ := hs'.base
  obtain ⟨hr, ξ', hL⟩ := hs.lev
  have hM : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    obtain ⟨P, hP⟩ := exists_under (D := D) v
    have hPv : P.under (𝓞 D.host.F) ∉ c.S := by rw [hP]; exact hv
    have h1 := hNSv P hPv
    have h2 := hNTv P hPv
    intro h
    rw [← hP] at h
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
    rw [map_natCast, Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact h1 h
    · exact h2 h
  have hle := latO_at_le hNS.2.2.2.1 hNT.2.2.2.1 hM
  have hoff : ∀ PP ∈ s.L.Pg ∪ ∅, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := by
    intro PP hPP h0
    rw [Finset.union_empty, hL] at hPP
    exact hv (Finset.mem_image.2 ⟨PP, hPP, h0⟩)
  have hfix : ∀ u ∈ latO s.V s'.V (frameLat s.V : Set (Fin s.V.rank → D.host.E))
      (frameLat s'.V : Set (Fin s'.V.rank → D.host.E)) (fun u => u = v),
      heisO c.ψ s.V s'.V u f₀ = f₀ → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
    GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hc.inf _ _ _ _ p.f hp.theta u
      (GlobalTheory.VacGood.infPart_latO (hle hu))
      (GlobalTheory.Hk3.heisO_fix_thetaAt_off c.ψ _ _ _ _ _ _ _ _ hth u
        (fun i j => GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff hu i j) h0) φ
  refine ⟨hp.theta φ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · exact hfix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hf₀.2.lat.1 u (hle hu))
  · exact hfix u hu (hf₀.2.lat.2 e' he' u (hle hu) hh)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInvStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_weilPairAction_left_inv : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (x : WO S T), frMapO S T βS βT (actO S T g 1 x) = HMul.hMul (frMapO S T βS βT x) ((βS⁻¹ * Lev.finE S g * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
  intro D S T βS βT g x
  have mt_one' : Formalism.L2.Theta.mt T 1 = 1 := by
    show (matHom T 1).1 = 1
    simp
  have finE_inv_val' : ((Lev.finE S g)⁻¹).1 = (Formalism.L2.Theta.mt S g⁻¹).map (toEAf D) := by
    rw [← map_inv]; rfl
  have conj_inv_val' : ((βS⁻¹ * Lev.finE S g * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).1 = (βS⁻¹).1 * ((Lev.finE S g)⁻¹).1 * βS.1 := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
  rw [frMapO, frMapO, actO, mt_one', Matrix.one_mul, Matrix.map_mul, conj_inv_val', finE_inv_val']
  have hb : βS.1 * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1, hb, Matrix.one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramEqOfInst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SBesEx

theorem gram_eq_of_inst {D : D7} (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hId : ∀ x : I.E, HEq (ιE x) x) (hn : (D.sp.Y 0).rank = I.n)
    (k l : Fin (D.sp.Y 0).rank) :
    ιE (I.J (Fin.cast hn k) (Fin.cast hn l)) = (D.sp.Y 0).gram k l := by
  subst hI
  rw [eq_of_heq (hId _)]
  rfl

theorem cY_isom : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), IdE X → ∀ y y' : (VS D).V, star (GlobalTheory.Core.SBesEx.cY X h y') ⬝ᵥ ((D.sp.Y 0).gram *ᵥ GlobalTheory.Core.SBesEx.cY X h y) = (VS D).hT y' y := by
  intro D X h hId y y'
  set b := X.bas.reindex (finCongr (rank_eq X h)).symm with hb
  have hc : ∀ z, cY X h z = b.repr z := by
    intro z; funext k
    simp [cY, HidaSetting.crd, crdOf, hb, Module.Basis.repr_reindex]
  have hG : (D.sp.Y 0).gram = fun k l => (VS D).hT (b k) (b l) := by
    funext k l
    rw [← gram_eq_of_inst X.B.I h X.ιE hId (rank_eq X h) k l, X.J_eq]
    simp [hb]
  rw [hc, hc, hG]
  conv_rhs => rw [← b.sum_repr y', ← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec,
    Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [starRingEnd_apply]
  ring

end GlobalTheory.Core.SBesEx

end
end

