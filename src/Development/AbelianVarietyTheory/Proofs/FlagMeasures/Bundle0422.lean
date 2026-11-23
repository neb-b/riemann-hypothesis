module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableRootCoords
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0421
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0405
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0212
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPair
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0245
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0420
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0098
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0388

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGaps
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpBesselGap

section scale

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants

theorem exists_bessel_scale (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ}
    {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ} {μW μN μG νq : Measure (Mt k r)} (hc : c ≠ 0)
    (hS : SideG k r z π u μW μN μG νq) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) (hR : R.IsDG ε mu) (hU : Formalism.MainNotions.S.IsURepOn (GG k r) R.σ) (hg : GapAtLeast ε mu h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) :
    ∃ l : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π l ∧
      ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by
  obtain ⟨t, ht, hN, hz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, hW, hψ⟩ := hz z hS.1
  obtain ⟨hS', hm⟩ := GlobalTheory.BesselMoveGap.bessel_move_gap hH k r Wp z π u c μW μN μG νq t ht hN hW hψ hS
  obtain ⟨l₁, hl⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r ε mu h R Wp _ _ _ _ _ _ _ hR hg hok hS'
  obtain ⟨h1, h2⟩ := hm R hU
  refine ⟨fun v => l₁ (R.σ t⁻¹ v), (h1 _).2 ?_, h2 l₁ hl⟩
  have e : (fun v => l₁ (R.σ t⁻¹ (R.σ t v))) = l₁ := by
    funext v
    have h3 := hU.1.2 _ (PI.HwUniqW.inv_mem_UH ht) _ ht
    rw [show t⁻¹ * t = 1 from PI.HwUniqW.inv_mul_UH' ht, hU.1.1] at h3
    exact congrArg l₁ (congrArg (fun T : R.H →L[ℂ] R.H => T v) h3).symm
  show IsBes R z π (fun v => l₁ (R.σ t⁻¹ (R.σ t v)))
  rw [e]
  exact hl.1

end scale


open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions in
theorem exists_coef (hH : GlobalTheory.GapIn.Hyp) {Cg cb Cu cT CT C0 Cn : ℝ} (D : D7) (large₂ : SizeData₂ D) {C' Cl : ℝ}
    (hCl : 1000 ≤ Cl) (hm₀ : Cn ≤ D.R.m) (hcd : cdScaleTie D) (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0) τ w w'
    (hTT : HypTT D w w') {θ : ℝ} (hθ : 0 < θ)
    (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (hl : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3) (A : LocS W) (hA : GoodS D lam' A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') :
    0 < A.deg ∧ ∃ f, IsKFinCoefH (toBessel D τ w w' θ W lam' A hW hA hT hT').σ f ∧
      ∀ γ μR νR ν, CellData (toBessel D τ w w' θ W lam' A hW hA hT hT') W.μG γ μR νR ν →
        νR {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 →
        A.J νR γ = OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT') f γ ν := by
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv : 0 < D.host.v := by linarith
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hv
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have hkg : 0 < D.host.ka / gg D := div_pos hka (mul_pos hg0 hg1)
  have hc : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  obtain ⟨hU, -, -, o1, -⟩ := _root_.GlobalTheory.Amp.Side.both_sides D τ w w' θ W lam' A hθ hv hTT hW hA
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := o1.2.2.2.2.2.2.2.2.1
  have hW' := hW
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW'
  let sq : (Fin D.R.k → ℝ) → ℕ → ℝ := fun u n => if h : n - 1 < D.R.k then u ⟨n - 1, h⟩ else 0
  have hsq : ∀ u (i : Fin D.R.k), sq u (i.val + 1) = u i := fun u i => by simp [sq]
  have s1 : SideG D.R.k D.R.rS W.z W.π (sq (uS D w τ)) W.μW W.μN W.μG W.νS :=
    ⟨z1, t1 ▸ hT, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z1 (t1 ▸ hT) c1 (hsq _), w1, hNH, hG, q1⟩
  have s2 : SideG D.R.k D.R.rS W.z' W.π' (sq (uS D w' τ)) W.μW' W.μN W.μG W.νS' :=
    ⟨z2, t2 ▸ hT', ⟨_, c2⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z2 (t2 ▸ hT') c2 (hsq _), w2, hNH, hG, q2⟩
  obtain ⟨hNum, hcell, heps⟩ := _root_.GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w _ (hsq _)
  obtain ⟨⟨-, -, -, -, hok⟩, hν⟩ := GlobalTheory.NumFam.num_fam _ _ _ _ _ _ _ _ _ hNum
  obtain ⟨ν, hlam, hn1, -⟩ := GlobalTheory.hcParam_sub_integral _ (lamD D τ) lam' hNum.2.1 hA.1
  have hq : n1 ν ≤ D.R.k * D.R.m ^ 5 := by
    have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
    have h1 : Cn ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have h2 : ((n1 ν : ℕ) : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 5 := by
      rw [hn1]
      calc _ ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := hl
        _ ≤ (D.R.m : ℝ) ^ 2 * D.R.k * (D.R.m : ℝ) ^ 3 := by gcongr
        _ = _ := by ring
    exact_mod_cast h2
  have hgap : GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) := by
    rw [hlam, ← heps]; exact (hν ν hq).2.2.1
  have hDS : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).IsDS (epsSH D.R) lam' := ⟨hA.1, hA.2.1⟩
  have hDG : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).IsDG (epsSH D.R) lam' := ⟨hA.1, hA.2.1, _, hgap, hok⟩
  obtain ⟨l, b1, e1⟩ := exists_bessel_scale hH hc s1 ⟨A.H, A.σ⟩ hDG hU hgap hok
  obtain ⟨l', b2, e2⟩ := exists_bessel_scale hH hc s2 ⟨A.H, A.σ⟩ hDG hU hgap hok
  obtain ⟨⟨v, k1, n1⟩, ⟨v', k2, n2⟩, w0, η, hw0, -, hJ⟩ :=
    GlobalTheory.T.amplitude_eq_smul_normalisedAmplitude_largeGap hH D τ w w' θ W lam' A _ l l' hθ hkg hT hT' hW hA hgap hok b1 b2 e1 e2
  have hw0' : w0 ≠ 0 := by
    obtain ⟨P, -, h1, -⟩ := hw0
    rintro rfl
    simp at h1
  obtain ⟨κ, hκ, hdeg⟩ := GlobalTheory.GapDegreeTie.deg_eq_mul_fdegH hH D τ w w' θ W hcd hW
  obtain ⟨d1, d2⟩ := hdeg lam' A hA ⟨_, hgap, hok⟩ w0 hw0'
  have hfd : 0 < PI.BesselPeriodGGP.fdegH W.μG A.σ w0 := by
    rw [d1] at d2; exact (mul_pos_iff_of_pos_left hκ).1 d2
  have hd : (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hfd.ne'
  rw [hN] at e1 e2
  set d : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hd'
  have i1 : ⟪l v, l v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 n1
  have i2 : ⟪l' v', l' v'⟫_ℂ ≠ 0 := inner_self_ne_zero.2 n2
  refine ⟨d2, coefF (toBessel D τ w w' θ W lam' A hW hA hT hT') v v' ((η / (d * (⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ))) • l v)
    (l' v'), GlobalTheory.AmpBessel.isKFinCoefH_coefF (toBessel D τ w w' θ W lam' A hW hA hT hT') k1 k2 _ _, fun γ μR νR ν hD h0 => ?_⟩
  have key := (GlobalTheory.CellPieriG.amp_eq_orb hH (_root_.GlobalTheory.AmpOrbGap.ampKF hH) GlobalTheory.CellMaj.cellConv (toBessel D τ w w' θ W lam' A hW hA hT hT')
    ⟨A.H, A.σ⟩ lam' _ W.μG l l' w0 hDS hgap hok hcell hc ENNReal.ofReal_ne_top hG e1 e2 hw0 γ μR νR ν hD v v' k1 k2
    ((η / (d * (⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ))) • l v) (l' v')).2
  rw [hJ νR γ hD.1 h0]
  refine Eq.trans ?_ key
  congr 1
  show η = d * (⟪l v, (η / (d * (⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ))) • l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ)
  rw [inner_smul_right]
  field_simp


open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Amp in
theorem ampIsBessel : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → D.host.rdE ≤ large₂.sc.b → m₀ ≤ D.R.m → cdScaleTie D → Bridge.AmpIsBessel D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Ca := by
  intro hH Cg cb Cu cT CT C0 C1
  refine ⟨2 * |C1|, by positivity, fun Cn => ?_⟩
  obtain ⟨m₁, hm₁⟩ := _root_.GlobalTheory.Amp.OpenCellNormGap.norm_eq_const_div_deg_gap hH (_root_.GlobalTheory.AmpOrbGap.ampKF hH) GlobalTheory.CellMaj.cellConv Cg cb Cu cT CT C0 C1 Cn
  refine ⟨max Cn m₁, fun D large₂ C' Cl hCl hb hm hcd hZ τ w w' hTT θ hθw W hW lam' hl A hA hT hT' => ?_⟩
  have hb0 : 0 < large₂.sc.b := Real.exp_pos _
  have hθ : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθw.1
  have hm1 : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hb1 : 1 ≤ large₂.sc.b := by
    have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    unfold Host.v at hv1
    linarith
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  obtain ⟨hdpos, f, hf, hJ⟩ := exists_coef hH D large₂ hCl ((le_max_left _ _).trans hm) hcd hZ τ w w' hTT hθ W hW lam' hl A hA hT hT'
  refine ⟨f, 1, one_pos, hf, fun μsec hsec => ?_, fun γ p hp θ' hθ'w νR hν => ?_⟩
  · have e : ThB.jNorm2 (toBessel D τ w w' θ W lam' A hW hA hT hT') f μsec = MMv D w w' A μsec := by
      unfold ThB.jNorm2 jNormSq MMv
      rw [← hW.2.2.2.2.1, ← hW.2.2.2.2.2.1]
      refine lintegral_congr_ae ?_
      filter_upwards [GlobalTheory.AmpBessel.ae_cellData hk (toBessel D τ w w' θ W lam' A hW hA hT hT') W.μG hsec] with q hq
      rcases hq with hq | hq
      · have hq' : bcWeight _ _ (Tz _ _ W.z) (Tz _ _ W.z') q = 0 := hq
        rw [hq, hq', zero_mul, zero_mul]
      · rw [hJ _ _ _ _ hq hG.2.2.1, Real.norm_of_nonneg (Real.sqrt_nonneg _),
          Real.sq_sqrt (GlobalTheory.AmpBessel.hs_nonneg _)]
        rfl
    obtain ⟨K, hK, hM⟩ := hm₁ D large₂ C' Cl hCl ⟨hb, by nlinarith, (le_max_right _ _).trans hm⟩ hcd hZ τ w w' hTT θ hθw W hW
      μsec hsec
    rw [e, ENNReal.ofReal_one, one_mul, hM lam' hl A hA]
    exact ⟨(ENNReal.ofReal_pos.2 (div_pos hK hdpos)).ne', le_rfl⟩
  · have hθ' : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'w.1
    obtain ⟨g, μR, ν₀, ν, s, hD, h0, hrep, hroot, hs, hA'⟩ := GlobalTheory.AmpBessel.amp_at_root D τ w w' θ W hW lam' A hA hT hT' hp hθ' hν
    have hle : ENNReal.ofReal (hsNormSq (OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT') f g (ENNReal.ofReal θ' • ν))) ≤
        Bridge.orbSqO (toBessel D τ w w' θ W lam' A hW hA hT hT') f p :=
      le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le _
        (le_iSup_of_le ⟨hrep, hD.2.2.2.1, hroot, GlobalTheory.AmpBessel.isOrbQuot_smul hD.2.2.2.2.2.1⟩ le_rfl)))
    have e : OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT') f g (ENNReal.ofReal θ' • ν) =
        (θ' : ℂ) • OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT') f g ν := by
      unfold OrbInt
      rw [integral_smul_measure, ENNReal.toReal_ofReal hθ'.le, Complex.coe_smul]
    refine le_trans ?_ (mul_le_mul_right hle _)
    rw [hA', GlobalTheory.AmpNorm.hsNormSq_smul, hJ _ _ _ _ hD h0, e, GlobalTheory.AmpNorm.hsNormSq_smul, hs,
      ← ENNReal.ofReal_mul (by positivity), Complex.norm_real, Real.norm_of_nonneg hθ'.le, one_mul, ← mul_assoc]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (GlobalTheory.AmpBessel.hs_nonneg _))
    have h1 : 1 ≤ large₂.sc.b ^ (|C1| * (D.R.m : ℝ) ^ 2) * θ' := by
      calc (1 : ℝ) ≤ large₂.sc.b ^ (|C1| * (D.R.m : ℝ) ^ 2 + -(C1 * (D.R.m : ℝ) ^ 2)) :=
            Real.one_le_rpow hb1 (by nlinarith [le_abs_self C1, sq_nonneg (D.R.m : ℝ)])
        _ ≤ _ := by
            rw [Real.rpow_add hb0]
            exact mul_le_mul_of_nonneg_left hθ'w.1 (by positivity)
    rw [show 2 * |C1| * (D.R.m : ℝ) ^ 2 = |C1| * (D.R.m : ℝ) ^ 2 * (2 : ℕ) by push_cast; ring, Real.rpow_mul_natCast hb0.le,
      ← mul_pow]
    exact pow_le_pow_left₀ zero_le_one h1 2

end GlobalTheory.AmpBesselGap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeNormDegreeAlongFamilyOfKFiniteIdentity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.AmpFamGap

theorem cellConv : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence

theorem amplitudeNormDegree_along_family_of_kFiniteIdentity : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT →
      VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 := by
  intro hH hA Cg cb Cu cT CT C0 C1
  refine ⟨1000, fun eps Fm hC' hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := _root_.GlobalTheory.Amp.OpenCellNormGap.norm_eq_const_div_deg_gap hH hA cellConv Cg cb Cu cT CT C0 C1 Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  refine ⟨x0, fun x hx i hZ => ?_⟩
  obtain ⟨-, hm0, -, -, hrd, -⟩ := hx0 x hx i
  have hm2 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by
    have := (Fm.D x i).R.two_le_m
    exact_mod_cast (by omega : 1 ≤ (Fm.D x i).R.m)
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hm0⟩
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hZ

theorem amplitudeNormDegree_along_family_largeGaps : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT →
      VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 := by
  intro _ hH _
  exact amplitudeNormDegree_along_family_of_kFiniteIdentity hH (_root_.GlobalTheory.AmpOrbGap.ampKF hH)

end GlobalTheory.AmpFamGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseDataOfGlobalTerm
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.BaseTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tri_symm {K W : Type} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ} {f g : Fin n → W}
    (h : Tri K f g) : Tri K g f := by
  obtain ⟨A, hA, hc⟩ := h
  have hinv := inv_unitri A hA.1 hA.2
  have hbt : A.BlockTriangular id := fun i j hij => hA.1 i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]; simp [hA.2]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  refine ⟨A⁻¹, hinv, fun b => ?_⟩
  have hm := Matrix.mul_nonsing_inv A hu
  have key : ∀ c, ∑ a, A c a * A⁻¹ a b = if c = b then (1 : K) else 0 := fun c => by
    rw [← Matrix.mul_apply, hm, Matrix.one_apply]
  calc f b = ∑ c, (if c = b then (1 : K) else 0) • f c := by simp
    _ = ∑ c, (∑ a, A c a * A⁻¹ a b) • f c := by simp only [key]
    _ = ∑ a, A⁻¹ a b • ∑ c, A c a • f c := by
      simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]
    _ = ∑ a, A⁻¹ a b • g a := Finset.sum_congr rfl fun a _ => by rw [hc a]

theorem tri_refl (K : Type) {W : Type} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ} (f : Fin n → W) :
    Tri K f f := by
  refine ⟨1, ⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a⟩, fun b => ?_⟩
  simp [Matrix.one_apply, ite_smul, Finset.sum_ite_eq']

theorem finrank_Vp_eq {D : D7} (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  unfold Ranks.r Ranks.rS
  obtain ⟨j, hj⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

end GlobalTheory.BaseTerm

namespace GlobalTheory.BaseTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem base_data_of_global_term : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ w : Point D.host.E (D.R.rS + 1), IsInCell (ZhatOM (ZhatL (lf D F0) F')) w → ∃ (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 F'1 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (d0 : ∀ p, LocNG.Datum (FP p)), (∃ n ∈ Formalism.L2.SG.NGData.NRat (lf D F0), ∀ a, frame F00 a = n (frame (lf D F0) a)) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w ∧ Gval F00 F'0 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL (lf D F0) F'1)) w ∧ (∀ p, AtBase Z p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Z.M p)) ∧ LocNG.IsTermOver (FP p) (d0 p) (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) ∧ (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' = scaled Z p (frame F'1)) ∧ {p : PlF D | ¬ ((FP p).PrimeTo ∧ LocNG.IsTermOver (FP p) (d0 p) ⟨lattice₂ D Z.M p Λ, scaled Z p (frame F00), scaled Z p (frame F'0), ((Tu D u : ℕ) : (D.s.atP p).Fp), ((Tu D u' : ℕ) : (D.s.atP p).Fp)⟩)}.Finite := by
  intro D Z u u' F0 Λ hR F' hPD hG w hw
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (Formalism.L2.SG.GramJoint.Tu_pos D u).ne'
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (Formalism.L2.SG.GramJoint.Tu_pos D u').ne'

  have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
  have hinv := inv_unitri _ hu.1 hu.2
  have hA1 : Uni ((admXi D Λ (lf D F0) F')⁻¹.map (fun x : 𝓞 D.host.E => (x : D.host.E))) :=
    ⟨fun a b h => by simp [hinv.1 a b h], fun a => by simp [hinv.2 a]⟩
  obtain ⟨F'1, hF'1⟩ := (GlobalTheory.FlagChange.flag_change D F' hT').1 _ hA1
  have hfr1 : frame F'1 = frameAct (frame F') (admXi D Λ (lf D F0) F')⁻¹ := funext fun b => (hF'1 b).trans rfl
  have hTri1 : Tri D.host.E (frame F') (frame F'1) := ⟨_, hA1, hF'1⟩

  obtain ⟨-, hB1⟩ := _root_.GlobalTheory.LocOver.base_frames_at_point D (lf D F0) F' w hT hT' hw
  obtain ⟨hw1, hG1⟩ := hB1 (lf D F0) F'1 (tri_refl _ _) hTri1
  obtain ⟨⟨F00, F'0, hTa, hTb, hpt⟩, hB2⟩ := _root_.GlobalTheory.LocOver.base_frames_at_point D (lf D F0) F'1 w hT hT' hw1
  have hG0 : Gval F00 F'0 ≠ 0 := by rw [(hB2 F00 F'0 hTa hTb).2, hG1]; exact hG
  obtain ⟨n, hn, hnf⟩ := ((GlobalTheory.FlagChange.flag_change D (lf D F0) hT).2 F00).1 hTa

  have hFP := _root_.GlobalTheory.LocBaseRel.atBase_relG D Z u u' w F00 F'0 hpt hG0
  choose FP hFPb using fun p => (hFP p).1
  have hFPr : ∀ p, (FP p).RelG (LocNG.theta (Z.M p)) := fun p => (hFP p).2 _ (hFPb p)
  have hIT := GlobalTheory.LocOver.locU_isTerm D Z u u' F0 Λ hR F' hPD hG
  have hf'eq : ∀ p, (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' = scaled Z p (frame F'1) := by
    intro p
    funext b
    show frFac Z.δ p b • baseChange₂ D p (frameAct (frame F') (admXi D Λ (lf D F0) F')⁻¹ b) =
      frFac Z.δ p b • baseChange₂ D p (frame F'1 b)
    rw [hfr1]

  obtain ⟨Ba, hBa, hBac⟩ := tri_symm hTa
  obtain ⟨Bb, hBb, hBbc⟩ := tri_symm hTb
  obtain ⟨Pa, hPa, -⟩ := GlobalTheory.LocOver.tri_scaled D Z _ _ Ba hBa hBac
  obtain ⟨Pb, hPb, -⟩ := GlobalTheory.LocOver.tri_scaled D Z _ _ Bb hBb hBbc
  have hd : ∀ p, ∃ d : LocNG.Datum (FP p), LocNG.IsTermOver (FP p) d (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
    intro p
    refine _root_.GlobalTheory.LocOver.TermOver.exists_datum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p) _ (hIT p).1 ?_ ?_ ?_ ?_
    · exact (hFPb p).2.2.1.symm
    · exact (hFPb p).2.2.2.symm
    · rw [(hFPb p).1]; exact ⟨Pa p, (hPa p).1, (hPa p).2⟩
    · rw [(hFPb p).2.1, hf'eq p]; exact ⟨Pb p, (hPb p).1, (hPb p).2⟩
  choose d0 hd0 using hd
  refine ⟨F00, F'0, F'1, FP, d0, ⟨n, hn, hnf⟩, hpt, hG0, hw1, fun p => ⟨hFPb p, hFPr p, hd0 p, hf'eq p⟩, ?_⟩

  obtain ⟨Aa, hAa, hAac⟩ := hTa
  obtain ⟨Ab, hAb, hAbc⟩ := hTb
  obtain ⟨Qa, hQa, hQaf⟩ := GlobalTheory.LocOver.tri_scaled D Z _ _ Aa hAa hAac
  obtain ⟨Qb, hQb, hQbf⟩ := GlobalTheory.LocOver.tri_scaled D Z _ _ Ab hAb hAbc
  have hPr := _root_.GlobalTheory.PrimeAlmostAll.primeTo_finite D Z u u' F00 F'0 hG0 FP hFPb
  refine ((hPr.union hQaf).union hQbf).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra hc
  push_neg at hc
  obtain ⟨⟨hpr, hqa⟩, hqb⟩ := hc
  apply hp
  refine ⟨hpr, ?_⟩
  have hsplit : (Z.M p).split = none := hpr.1
  have hth : LocNG.theta (Z.M p) = 1 := by unfold LocNG.theta; rw [hsplit]
  refine _root_.GlobalTheory.LocOver.WitChange.witness_change (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq p) (hFPr p) (d0 p)
    (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) (hd0 p) (Qa p) (Qb p) _ _ (hQa p).1 (hQb p).1 ?_ (hQa p).2 ?_
  · intro a b
    refine ⟨hqa a b, hqb a b, ?_⟩
    rw [hth, map_one]
    exact Submodule.mem_span_singleton.mpr ⟨⟨Qa p a b - Qb p a b, sub_mem (hqa a b) (hqb a b)⟩, by
      first
        | exact (Subring.smul_def _ _).trans (mul_one _)
        | exact mul_one _
        | (show _ * _ = _; exact mul_one _)
        | rfl⟩
  · rw [hf'eq p]; exact (hQb p).2

end GlobalTheory.BaseTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionMovedLatticeEqLocalCoordinatesStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_moved_lattice_eq_local_coordinates : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (𝓞 D.host.E) (VS D).V), GlobalTheory.LocOver.Ext p σ g → (placesOf Z).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ)) := by
  first | exact @GlobalTheory.HL.placesLat_gcoordLat_eq | exact GlobalTheory.HL.placesLat_gcoordLat_eq | (intros; apply GlobalTheory.HL.placesLat_gcoordLat_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnipotentFrameCorrespondsUnderIsometryStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnipotent_frame_corresponds_under_isometry : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} {P : LocNG.FPair H r} {S : Frames M.L r k} (c : WCoord P S) (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V), g ∈ NU H f ↔ (c.e.symm.trans g).trans c.e ∈ S.Nof (fun a => c.e (f a)) := by
  first | exact @GlobalTheory.HL.NUTransport.mem_NU_iff_mem_Nof | exact GlobalTheory.HL.NUTransport.mem_NU_iff_mem_Nof | (intros; apply GlobalTheory.HL.NUTransport.mem_NU_iff_mem_Nof <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepChoiceConstantsCOfSiegelWeilAtInfinity
section
namespace GlobalTheory.St

theorem stepChoiceDataC_of_siegelWeil_inInfinity :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
    (∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word),
      Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.RealObj.InInfinityX X u u' 1) →
    Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC :=
  fun h hI => Formalism.L2.SG.Pf.choice_massData (GlobalTheory.St.swxs_of_siegelWeil h)
    Formalism.L2.SG.Pf.ProdConvCut2.prodConv_onTied hI

end GlobalTheory.St
end

