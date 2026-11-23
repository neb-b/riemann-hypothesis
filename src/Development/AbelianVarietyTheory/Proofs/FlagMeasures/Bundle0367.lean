module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallCellRelevantPointsHaarQuotientMajorant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0153

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroCmElementLocalUnitAlmostAll
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitAlmostAll

variable {D : D7}

theorem exists_nat_mul_integral (x : D.host.E) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : D.host.E) * x) := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℤ D.host.E := Algebra.IsAlgebraic.trans ℤ ℚ D.host.E
  obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple

  refine ⟨y.natAbs * y.natAbs, by simpa using hy0, ?_⟩
  have hsq : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := by
    rw [Nat.cast_mul]
    exact Int.natAbs_mul_self' y
  have e : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * x = (y : D.host.E) * (y • x) := by
    rw [zsmul_eq_mul, ← mul_assoc]
    have hc : ((y.natAbs * y.natAbs : ℕ) : D.host.E) = (((y.natAbs * y.natAbs : ℕ) : ℤ) : D.host.E) :=
      (Int.cast_natCast _).symm
    rw [hc, hsq, Int.cast_mul]
  rw [e]
  have hyi : IsIntegral ℤ (y : D.host.E) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ D.host.E y))
  exact hyi.mul hy

theorem iota_mem_O (Z : LocDat D) (p : PlF D) (x : D.host.E) (n : ℕ)
    (hint : IsIntegral ℤ ((n : D.host.E) * x)) (hn : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal)) :
    (D.s.atP p).ιE x ∈ (Z.M p).L.O := by
  rw [(show (Z.M p).L.O = (D.s.atP p).O from (Z.agree p).2.2.2.1), (D.s.atP p).O_def]
  have : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have hcn : (D.s.atP p).ιF (n : D.host.F) = (n : (D.s.atP p).Fp) := map_natCast _ n
  have hc0 : (n : (D.s.atP p).Fp) ≠ 0 := by exact_mod_cast hn0

  have hv : p.valuation D.host.F (n : D.host.F) = 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
      (v := p) (K := D.host.F) (r := (n : 𝓞 D.host.F))).mpr hn
    rwa [map_natCast] at this
  have hle : (1 : (D.s.atP p).Fp) ≤ᵥ (n : (D.s.atP p).Fp) := by
    have := ((D.s.atP p).val 1 (n : D.host.F)).mpr (by rw [hv, map_one])
    rwa [map_one, hcn] at this
  have hinv : (n : (D.s.atP p).Fp)⁻¹ ∈ (ValuativeRel.valuation (D.s.atP p).Fp).integer := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    have h1 := (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (D.s.atP p).Fp) 1
      (n : (D.s.atP p).Fp)).mp hle
    rw [map_one] at h1
    exact inv_le_one_of_one_le₀ h1
  have hx : (D.s.atP p).ιE x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)⁻¹ *
      (D.s.atP p).ιE ((n : D.host.E) * x) := by
    have hE : (n : D.host.E) = algebraMap D.host.F D.host.E (n : D.host.F) := (map_natCast _ n).symm
    rw [map_mul, hE, (D.s.atP p).compat, hcn, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  rw [hx]
  refine IsIntegral.mul ?_ ?_
  · exact isIntegral_algebraMap (R := (ValuativeRel.valuation (D.s.atP p).Fp).integer) (x := ⟨(n : (D.s.atP p).Fp)⁻¹, hinv⟩)
  · exact (hint.map (D.s.atP p).ιE.toIntAlgHom).tower_top

theorem unit_almost_all : ∀ (D : D7) (Z : LocDat D) (x : D.host.E), x ≠ 0 →
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE x)}.Finite := by
  intro D Z x hx
  obtain ⟨n, hn0, hn⟩ := exists_nat_mul_integral x
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul_integral x⁻¹

  have hI : Ideal.span {((n * m : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast Nat.mul_ne_zero hn0 hm0
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hnm
  apply hp
  have hn' : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_right _ _ h)
  have hm' : ¬ ((m : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_left _ _ h)
  refine ⟨iota_mem_O Z p x n hn hn', (D.s.atP p).ιE x⁻¹, iota_mem_O Z p x⁻¹ m hm hm', ?_⟩
  rw [← map_mul, mul_inv_cancel₀ hx, map_one]

end GlobalTheory.UnitAlmostAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorOfHyps
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTK

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem kfin_zero {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ 0 :=
  ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]⟩

theorem isCoef_zero {k r : ℕ} (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) :
    IsCoef (rep L) l l' (fun _ => 0) 0 :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun g _ => by simp, by simp⟩

end GlobalTheory.AmpTK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeFoldrMax
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsRange

theorem one_le_foldr_max (L : List ℝ) : 1 ≤ L.foldr max 1 := by
  induction L with
  | nil => simp
  | cons a L ih => exact le_trans ih (le_max_right _ _)

theorem le_foldr_max (L : List ℝ) (x : ℝ) (hx : x ∈ L) : x ≤ L.foldr max 1 := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    rcases List.mem_cons.1 hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem ratio_le (r k N e : ℕ) (b v g θ θ' ka X Cg : ℝ) (hb : 2 ≤ b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b) (hg : 1 ≤ g)
    (hgb : g ≤ b ^ (2 * Cg)) (hka : ka = Real.pi / v) (hθ0 : 0 < θ) (hθ : θ ≤ b ^ X) (hθ' : b ^ (-X) ≤ θ')
    (hN : N ≤ r ^ 2) (he : e ≤ r * k) :
    (2 * v) ^ (-((r : ℝ) * k)) * θ * 2 ^ (r * (k + 1) + r * (r - 1)) / (θ' * (2 * ka / g / (2 * Real.pi)) ^ N) ≤
      b ^ (2 * X + (2 + 2 * Cg) * (r : ℝ) ^ 2) * v⁻¹ ^ e := by
  have hb0 : 0 < b := by linarith
  have hv0 : 0 < v := by linarith
  have hg0 : 0 < g := by linarith
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'
  have hpi := Real.pi_pos
  have e1 : r * (k + 1) + r * (r - 1) = r * k + r ^ 2 := by
    cases r with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  have e2 : (2 * v) ^ (-((r : ℝ) * k)) = ((2 * v) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast]; push_cast; rfl
  have e3 : 2 * ka / g / (2 * Real.pi) = (v * g)⁻¹ := by
    rw [hka]; field_simp
  have e4 : (2 * v) ^ (-((r : ℝ) * k)) * θ * 2 ^ (r * (k + 1) + r * (r - 1)) / (θ' * (2 * ka / g / (2 * Real.pi)) ^ N)
      = (θ * θ'⁻¹ * (2 ^ (r ^ 2) * (v * g) ^ N)) * v⁻¹ ^ (r * k) := by
    rw [e1, e2, e3, pow_add, mul_pow 2 v, inv_pow, inv_pow]
    field_simp
  rw [e4]
  have h1 : θ'⁻¹ ≤ b ^ X := by
    have := inv_anti₀ (Real.rpow_pos_of_pos hb0 _) hθ'
    rwa [Real.rpow_neg hb0.le, inv_inv] at this
  have h2 : (v * g) ^ N ≤ (b * b ^ (2 * Cg)) ^ (r ^ 2) := by
    refine le_trans (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hv hg) hN) ?_
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul (by linarith) hgb hg0.le hb0.le) _
  have h3 : (2 : ℝ) ^ (r ^ 2) ≤ b ^ (r ^ 2) := pow_le_pow_left₀ (by norm_num) hb _
  have h4 : v⁻¹ ^ (r * k) ≤ v⁻¹ ^ e := pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hv) he
  have e5 : b ^ (2 * X + (2 + 2 * Cg) * (r : ℝ) ^ 2) =
      b ^ X * b ^ X * (b ^ (r ^ 2) * (b * b ^ (2 * Cg)) ^ (r ^ 2)) := by
    rw [← mul_pow, ← mul_assoc, ← Real.rpow_add hb0, Real.rpow_add hb0 (2 * X), Real.rpow_mul hb0.le (2 + 2 * Cg),
      Real.rpow_add hb0 2, Real.rpow_two, two_mul X, sq b, ← Real.rpow_natCast _ (r ^ 2)]
    push_cast; rfl
  rw [e5]
  gcongr

theorem absBd_le (r k : ℕ) (b v Q A De Dd C M m : ℝ) (hr : 1 ≤ r) (hm : m = 2 * r + 2) (hb : Real.exp 1 ≤ b)
    (hv : 0 < v) (hM : 0 ≤ M) (hDe : 1 ≤ De) (hD : 0 ≤ Dd)
    (hQ : Q ≤ b ^ (A * (m * (r : ℝ) ^ 3)) * v⁻¹ ^ (r * (k - 2 - r)))
    (hC : A + 44 + 24 * M ≤ C) (hC1 : 14 ≤ C) (hC2 : 8 * Real.pi * Real.exp 1 ≤ C) :
    Q * absBd k r (b ^ (M * m)) De Dd ≤
      (b ^ (C * m) * De) ^ (C * (r : ℝ) ^ 3) * (C / (k * v)) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹ := by
  have hb1 : 1 ≤ b := le_trans (Real.one_le_exp (by norm_num)) hb
  have hb0 : 0 < b := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hm0 : 0 ≤ m := by linarith
  have hpi := Real.pi_pos
  have h1 : (4 * r : ℝ) ≤ b ^ m := by
    have a1 : Real.exp m ≤ b ^ m := by
      rw [← Real.exp_one_rpow]; exact Real.rpow_le_rpow (Real.exp_pos 1).le hb hm0
    have a2 : (r : ℝ) + 1 + 1 ≤ Real.exp (r + 1) := Real.add_one_le_exp _
    have a3 : Real.exp m = Real.exp (r + 1) * Real.exp (r + 1) := by rw [← Real.exp_add, hm]; ring_nf
    nlinarith
  have h2 : (4 * r : ℝ) ^ (44 * r ^ 3) ≤ b ^ (44 * (m * (r : ℝ) ^ 3)) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) h1 _) (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; push_cast; ring_nf
  have h3 : (b ^ (M * m)) ^ (24 * r ^ 3) = b ^ (24 * M * (m * (r : ℝ) ^ 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; push_cast; ring_nf
  have h4 : De ^ (14 * r ^ 2) ≤ De ^ (C * (r : ℝ) ^ 3) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hDe ?_
    push_cast
    have : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
    exact mul_le_mul hC1 this (by positivity) (by linarith)
  have h5 : (8 * Real.pi * Real.exp 1 / k) ^ (r * (k - 2 - r)) ≤ (C / k) ^ (r * (k - 2 - r)) := by
    gcongr
  have h6 : b ^ (A * (m * (r : ℝ) ^ 3)) * b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3)) ≤
      (b ^ (C * m)) ^ (C * (r : ℝ) ^ 3) := by
    rw [← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_mul hb0.le]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have t : 0 ≤ m * (r : ℝ) ^ 3 := by positivity
    have c : A + 44 + 24 * M ≤ C * C := by nlinarith
    have := mul_le_mul_of_nonneg_right c t
    nlinarith
  have hC0 : 0 ≤ C := by linarith
  calc Q * absBd k r (b ^ (M * m)) De Dd
      ≤ (b ^ (A * (m * (r : ℝ) ^ 3)) * v⁻¹ ^ (r * (k - 2 - r))) *
        (b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3)) * De ^ (C * (r : ℝ) ^ 3) *
          (C / k) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹) := by
        unfold absBd
        rw [h3]
        refine mul_le_mul hQ ?_ (by positivity) (by positivity)
        gcongr
    _ = (b ^ (A * (m * (r : ℝ) ^ 3)) * b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3))) *
          De ^ (C * (r : ℝ) ^ 3) * (C / (k * v)) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹ := by
        rw [show C / (k * v) = C / k * v⁻¹ by rw [← div_div, div_eq_mul_inv], mul_pow]; ring
    _ ≤ _ := by
        rw [Real.mul_rpow (by positivity) (by linarith)]
        gcongr

theorem abs_range : ∀ Cg cb Cu cT CT C0 C1 CMo : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ Cn : ℝ,
    ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo →
      ABSr D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro Cg cb Cu cT CT C0 C1 CMo
  refine ⟨8 * |C1| + 2 * |Cg| + 46 + 24 * max CMo 0 + 8 * Real.pi * Real.exp 1, fun C hC => ⟨4, ?_⟩⟩
  intro Cn D large₂ C' Cl hBig hMom hZ τ w w' hTT θ hθ W hW lam' hlam S hS γ p hp θ' hθ' νR hνR hDr
  obtain ⟨hrd, -, hm4⟩ := hBig
  have hm4' : 4 ≤ D.R.m := by exact_mod_cast hm4
  obtain ⟨-, -, hb, hm, -, -, -, hk, hv, -, hka, hvb, hg, hgb, -⟩ :=
    _root_.GlobalTheory.Amp.SizesProof.sizes_of_hyp D large₂ C' Cl Cg cb Cu cT CT C0 hrd hZ
  have hb2 : 2 ≤ large₂.sc.b := by linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hv0 : 0 < D.host.v := by linarith
  have hg0 : 0 < gg D := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'.1
  have hpi := Real.pi_pos
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hr : 1 ≤ D.R.rS := by omega
  have hk' : 2 * D.R.rS + 6 ≤ D.R.k := by
    have : D.R.m * 2 ≤ D.R.m ^ 4 := by
      rw [show D.R.m ^ 4 = D.R.m * D.R.m ^ 3 by ring]
      exact Nat.mul_le_mul_left _ (le_trans (by norm_num) (Nat.pow_le_pow_left hm4' 3))
    omega
  obtain ⟨hM1, hM2⟩ := _root_.GlobalTheory.Amp.MomBoth.momBd_both D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm4' hMom hZ τ w w' hTT θ hθ W hW
    lam' hlam S hS
  obtain ⟨-, -, hμN, hS1, hS2⟩ := _root_.GlobalTheory.Amp.Side.both_sides D τ w w' θ W lam' S hθ0 hv0 hTT hW hS
  rw [hμN] at hS1 hS2
  have hDr' : Dr D.R.k D.R.rS W.z W.z' γ = ‖DminN W.z W.z' γ D.R.rS‖ := by
    unfold Dr DminN; rw [dite_eq_left (by omega)]
  have hTF : TwoFl D.R.k D.R.rS W.z W.z' γ :=
    ⟨hS1.1, hS2.1, hS1.2.1, hS2.2.1, hp.1, hp.2.2, by rw [hDr']; exact norm_ne_zero_iff.2 hDr⟩
  obtain ⟨hends, -, -, -, hD0, -⟩ := _root_.GlobalTheory.Amp.PtMinor.blockEnds_minors D W.z W.z' γ p hS1.1 hS2.1 hS1.2.1 hS2.2.1 hp
  set De : ℝ := ((ptBlockEnds p).map fun l => max 1 ‖DminN W.z W.z' γ l‖⁻¹).foldr max 1 with hDe
  have hDe1 : 1 ≤ De := one_le_foldr_max _
  have hOK : DeOK D.R.k D.R.rS W.z W.z' γ De := by
    refine ⟨hDe1, fun l _ hl => ?_⟩
    have e : Dmin D.R.k D.R.rS W.z W.z' γ l = DminN W.z W.z' γ l.val := by
      unfold DminN; rw [dite_eq_left l.2]
    rw [e] at hl ⊢
    rcases Nat.eq_zero_or_pos l.val with h0 | h0
    · rw [h0, hD0]; simpa using hDe1
    · exact le_trans (le_max_right 1 _)
        (le_foldr_max _ _ (List.mem_map.2 ⟨l.val, (hends l.val h0).1 hl, rfl⟩))
  obtain ⟨p', μR, hroot, hquot⟩ := hνR
  obtain ⟨hN, hnorm⟩ := _root_.GlobalTheory.Amp.RootNormal.rootMeas_normR D W.z W.z' p' γ μR θ' hTF hroot hθ'0.le (by positivity)
  have hM0 : 0 ≤ max CMo 0 := le_max_right _ _
  have hH : 1 ≤ large₂.sc.b ^ (max CMo 0 * D.R.m) := Real.one_le_rpow (by linarith) (by positivity)
  obtain ⟨hint, hbd⟩ := GlobalTheory.T.amplitude_absolutelyConvergent_operatorNorm_le D.R.k D.R.rS W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' _ νR S.Φ S.Φ' γ
    S.cN _ _ _ De hr hk' (by positivity) (by positivity) hH hS1 hS2 hM1 hM2 hTF hOK hnorm hquot
  refine ⟨hint, le_trans hbd ?_⟩
  rw [hDr']
  have hmr : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast hm
  have hr' : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hr
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg Cg
  have a3 : 0 ≤ 8 * Real.pi * Real.exp 1 := by positivity
  refine absBd_le D.R.rS D.R.k large₂.sc.b D.host.v _ (8 * |C1| + 2 * |Cg| + 2) De _ C (max CMo 0) D.R.m hr hmr hb.le hv0
    hM0 hDe1 (norm_nonneg _) ?_ (by linarith) (by linarith) (by linarith)
  refine le_trans (ratio_le D.R.rS D.R.k _ (D.R.rS * (D.R.k - 2 - D.R.rS)) large₂.sc.b D.host.v (gg D) θ θ' D.host.ka _ Cg
    hb2 hv hvb hg hgb hka hθ0 hθ.2 hθ'.1 hN (Nat.mul_le_mul_left _ (by omega))) ?_
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) (by positivity)
  have r3 : (D.R.rS : ℝ) ≤ (D.R.rS : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
  have r23 : (D.R.rS : ℝ) ^ 2 ≤ (D.R.rS : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
  have m0 : (1 : ℝ) ≤ D.R.m := by linarith
  have b1 : (D.R.m : ℝ) ^ 2 ≤ 4 * (D.R.m * (D.R.rS : ℝ) ^ 3) := by
    have : (D.R.m : ℝ) ≤ 4 * (D.R.rS : ℝ) ^ 3 := by linarith
    nlinarith
  have b2 : (D.R.rS : ℝ) ^ 2 ≤ D.R.m * (D.R.rS : ℝ) ^ 3 := by nlinarith
  have c1 : C1 * (D.R.m : ℝ) ^ 2 ≤ |C1| * (4 * (D.R.m * (D.R.rS : ℝ) ^ 3)) :=
    mul_le_mul (le_abs_self _) b1 (by positivity) a1
  have c2 : Cg * (D.R.rS : ℝ) ^ 2 ≤ |Cg| * (D.R.m * (D.R.rS : ℝ) ^ 3) :=
    mul_le_mul (le_abs_self _) b2 (by positivity) a2
  nlinarith

end GlobalTheory.Amp.AbsRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie

theorem iota_int_cofinite {D : D7} (Z : LocDat D) (x : D.host.E) :
    {p : PlF D | (D.s.atP p).ιE x ∉ (Z.M p).L.O}.Finite := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hint⟩ := halg.exists_integral_multiple
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = y.natAbs := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := by rw [hn]; exact Int.natAbs_ne_zero.2 hy0
  have hint' : IsIntegral ℤ ((n : D.host.E) * x) := by
    rcases Int.natAbs_eq y with h | h <;> rw [← hn] at h
    · have e : y • x = (n : D.host.E) * x := by
        rw [zsmul_eq_mul, h, Int.cast_natCast]
      rw [← e]; exact hint
    · have e : y • x = -((n : D.host.E) * x) := by
        rw [zsmul_eq_mul, h, Int.cast_neg, Int.cast_natCast, neg_mul]
      have := hint.neg
      rw [e, neg_neg] at this
      exact this
  let w : 𝓞 D.host.E := ⟨(n : D.host.E) * x, hint'⟩
  have hfin : {p : PlF D | Loc.resChar p ∣ n}.Finite := by
    have hne : (Ideal.span {((n : ℕ) : 𝓞 D.host.F)} : Ideal (𝓞 D.host.F)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hn0
    refine (Ideal.finite_factors hne).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton, bt_natCast_mem_iff]
    exact hp
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  by_contra hnd
  apply hp
  obtain ⟨_, w', hw'O, hw'⟩ := bt_nat_unit Z p n hnd
  have hwO := bt_iota_int Z p w
  have e : (D.s.atP p).ιE x = w' * (D.s.atP p).ιE (w : D.host.E) := by
    show _ = w' * (D.s.atP p).ιE ((n : D.host.E) * x)
    rw [map_mul, map_natCast, ← mul_assoc, hw', one_mul]
  rw [e]
  exact Subring.mul_mem _ hw'O hwO

theorem tri_scaled : ∀ (D : D7) (Z : LocDat D), ∀ (f g : Fin (D.R.rS + 1) → (VS D).V)
    (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Chg f A g →
    ∃ Ap : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ p, Uni (Ap p) ∧ Chg (scaled Z p f) (Ap p) (scaled Z p g)) ∧
      {p : PlF D | ¬ ∀ a b, Ap p a b ∈ (Z.M p).L.O}.Finite := by
  intro D Z f g A hA hg
  refine ⟨fun p a b => Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b), ?_, ?_⟩
  · intro p
    refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩
    · simp [hA.1 a b hab]
    · show Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a * (D.s.atP p).ιE (A a a) = 1
      rw [hA.2 a, map_one, mul_one, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)]
    · simp only [scaled]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hg b, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [baseChange_smul₂, smul_smul, smul_smul]
      congr 1
      have h := Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a)
      linear_combination (-(frFac Z.δ p b * (D.s.atP p).ιE (A a b))) * h
  · have hD := locDiffC_holds D Z
    refine (Set.Finite.biUnion (Set.finite_univ (α := Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
      (fun ab _ => iota_int_cofinite Z (A ab.1 ab.2))).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq, not_forall] at hp
    obtain ⟨a, b, hab⟩ := hp
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, exists_true_left]
    refine ⟨(a, b), ?_⟩
    intro hι
    apply hab
    rcases lt_or_ge b a with h | h
    · simp [hA.1 a b h]
    · obtain ⟨k, hk, hkb⟩ := bt_frFac_step Z p hD a b h
      have e : Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b) =
          k * (D.s.atP p).ιE (A a b) := by
        rw [hkb, mul_comm k, ← mul_assoc, Ring.inverse_mul_cancel _ (bt_frFac_unit Z p a), one_mul]
      rw [e]
      exact Subring.mul_mem _ hk hι

end GlobalTheory.LocOver
end
end

