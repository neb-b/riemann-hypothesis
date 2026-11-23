module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0367
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallCellRelevantPointsHaarQuotientMajorant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0406
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0361
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0415
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGap
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTKGapOne

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp GlobalTheory.AmpTK

theorem oneBesselTor_of_gapHyp : GlobalTheory.GapIn.Hyp → ∃ Cgf : ℝ, ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf := by
  intro H
  obtain ⟨Cgf, hCgf⟩ := _root_.GlobalTheory.GapConstant.gap_constant_exists
  refine ⟨Cgf, fun D => ?_⟩
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hκN hκNt hε hgap hf
  obtain ⟨h, hg, hok, hgc⟩ := hCgf D L.ε L.lam hgap
  have hc0 : L.c ≠ 0 := by
    rw [hc]; unfold cOfDpsi
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by exact_mod_cast hκ₀.ne')
  obtain ⟨μG, hμG⟩ := GlobalTheory.SnMass.Inhab.exists_isHaarOn D.R.k D.R.rS
  obtain ⟨l, l', hBe, hl, hl'⟩ := _root_.GlobalTheory.AmpTKGap.exists_besselTK H _ _ L h hg hok hc0 hκN hκNt
  have hBig : ∀ (c : Fin D.R.rS → ℂ) (μ : Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), (∀ a, c a ≠ 0) →
      μᴴ * Hb D.R.k * μ = Hb D.R.k → OneAt L l l' (bigCell D.R.k D.R.rS c μ) (pairMeas L) := by
    intro c μ hc' hμ
    obtain ⟨h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.AmpTK.bigCell_data _ _ L μG hok.1 hκNt hκN hc0 hμG c μ hc' hμ
    obtain ⟨b, hb0, hb, hint⟩ := _root_.GlobalTheory.BigConv.bigConv _ _ L h hok hgc hκNt hκN hc0 c μ hc' hμ
    exact _root_.GlobalTheory.AmpTKOneGap.oneAt H _ _ L h μG l l' hg hok hc0 hμG hBe _ _ _ _ h1 h2 h3 h4 h5 b hb0 hb hint
  have hCell : ∀ (γ : Point ℂ (D.R.rS + 1)) (g : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)
      (μR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.ThB.Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g →
      IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OneAt L l l' g ν := by
    intro γ g μR ν h0 h1 h2 h3 h4
    obtain ⟨hR, ⟨νR, hQ⟩, b, hb0, hb, hint⟩ := _root_.GlobalTheory.CellPts.cell_points _ _ L h μG hok hgc hκNt hκN hc0 hμG γ g μR ν h0 h1 h2 h3 h4
    exact _root_.GlobalTheory.AmpTKOneGap.oneAt H _ _ L h μG l l' hg hok hc0 hμG hBe g μR νR ν h1.1 h2 hR h4 hQ b hb0 hb hint
  obtain ⟨⟨s, hs⟩, -⟩ := _root_.GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate H _ _ L l l' κ τ hκ hτ f hf
  by_cases hs0 : s = 0
  · subst hs0
    refine ⟨fun _ => 0, 1, one_ne_zero, ⟨0, 0, fun _ => by simpa using GlobalTheory.AmpTK.kfin_zero L.σ,
      fun _ => by simpa using GlobalTheory.AmpTK.kfin_zero L.σ, fun _ => by simp⟩, ?_, ?_⟩
    · intro c μ hc' hμ
      obtain ⟨A, hA⟩ := hBig c μ hc' hμ
      rw [J_eq_orbInt, J_eq_orbInt, hA _ 0 (GlobalTheory.AmpTK.isCoef_zero L l l'), hA f 0 hs]
      simp
    · intro γ g μR ν h0 h1 h2 h3 h4
      obtain ⟨A, hA⟩ := hCell γ g μR ν h0 h1 h2 h3 h4
      rw [hA _ 0 (GlobalTheory.AmpTK.isCoef_zero L l l'), hA f 0 hs]
      simp
  · have hs' := hs
    obtain ⟨m, x, y, X, hxy, -, hsdef⟩ := hs'
    have hx : ∃ x ∈ (rep L).TK, l x ≠ 0 := by
      by_contra hne
      push_neg at hne
      apply hs0
      rw [hsdef]
      exact Finset.sum_eq_zero fun i _ => by rw [hne _ (hxy i).1, inner_zero_left]
    have hy : ∃ y ∈ (rep L).TK, l' y ≠ 0 := by
      by_contra hne
      push_neg at hne
      apply hs0
      rw [hsdef]
      exact Finset.sum_eq_zero fun i _ => by rw [hne _ (hxy i).2, map_zero, inner_zero_right]
    obtain ⟨f₁, s₁, hf₁, hc₁, hs₁⟩ := GlobalTheory.GapAmpTK.exists_kFinCoef_torus_ne H _ _ L l l' κ τ hκ hτ hl hl' hx hy
    refine ⟨f₁, s₁ / s, div_ne_zero hs₁ hs0, hf₁, ?_, ?_⟩
    · intro c μ hc' hμ
      obtain ⟨A, hA⟩ := hBig c μ hc' hμ
      rw [J_eq_orbInt, J_eq_orbInt, hA _ _ hc₁, hA f s hs, smul_smul, div_mul_cancel₀ _ hs0]
    · intro γ g μR ν h0 h1 h2 h3 h4
      obtain ⟨A, hA⟩ := hCell γ g μR ν h0 h1 h2 h3 h4
      rw [hA _ _ hc₁, hA f s hs, smul_smul, div_mul_cancel₀ _ hs0]

end GlobalTheory.AmpTKGapOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OpenCellAmplitudeNormEqConstDivDegreeLargeGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OpenCellNormGap

open GlobalTheory.Amp.OpenCellNorm

theorem exists_bessel_scale_gap (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ}
    {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ} {μW μN μG νq : Measure (Mt k r)} (hc : c ≠ 0)
    (hS : SideG k r z π u μW μN μG νq) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) (hR : R.IsDS ε mu) (hU : Formalism.MainNotions.S.IsURepOn (GG k r) R.σ) (hg : GapAtLeast ε mu h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) :
    ∃ l : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π l ∧
      ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by
  obtain ⟨t, ht, hN, hz, -⟩ := _root_.GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, hW, hψ⟩ := hz z hS.1
  obtain ⟨hS', hm⟩ := GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne hH k r Wp z π u c μW μN μG νq t ht hN hW hψ hS
  have hRG : R.IsDG ε mu := ⟨hR.1, hR.2, ⟨h, hg, hok⟩⟩
  obtain ⟨l₁, hl⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r ε mu h R Wp _ _ _ _ _ _ _ hRG hg hok hS'
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

theorem norm_eq_const_div_deg_gap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ Cg cb Cu cT CT C0 C1 Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → cdScaleTie D → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∃ K : ℝ, 0 < K ∧ ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A → MMv D w w' A μsec = ENNReal.ofReal (K / A.deg) := by
  intro hH hKF hCC Cg cb Cu cT CT C0 C1 Cn
  refine ⟨Cn, fun D large₂ C' Cl hCl hBig hcd hZ τ w w' hTT θ hθw W hW μsec hsec => ?_⟩
  by_cases hex : ∃ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A
  swap
  · exact ⟨1, one_pos, fun lam' _ A hA => absurd ⟨lam', A, hA⟩ hex⟩
  obtain ⟨lam₀, A₀, hA₀⟩ := hex
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  have hθ : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos (Real.exp_pos _) _) hθw.1
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv : 0 < D.host.v := by linarith
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hv
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have hkg : 0 < D.host.ka / gg D := div_pos hka (mul_pos hg0 hg1)
  have hc : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  have hT : 0 < Tr D w := by unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by unfold Tr; exact_mod_cast hTT.2.1.pos
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hκN : kapN D θ ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨-, -, -, o1, o2⟩ := _root_.GlobalTheory.Amp.Side.both_sides D τ w w' θ W lam₀ A₀ hθ hv hTT hW hA₀
  have n1' : 0 < Module.finrank ℂ W.Wp := by haveI := o1.2.2.1; exact Module.finrank_pos
  have n2' : 0 < Module.finrank ℂ W.Wq := by haveI := o2.2.2.1; exact Module.finrank_pos
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := o1.2.2.2.2.2.2.2.2.1
  obtain ⟨κ, hκ, hdeg⟩ := _root_.GlobalTheory.GapDegreeTie.deg_eq_mul_fdegH hH D τ w w' θ W hcd hW
  obtain ⟨c, hc0, hnorm⟩ := GlobalTheory.T.lintegral_amplitudeNormSq_bigCell_gap hH hKF hCC _ _ (toBessel D τ w w' θ W lam₀ A₀ hW hA₀ hT hT') W.μG μsec hk hc
    hκN ENNReal.ofReal_ne_top hW.2.2.2.2.2.2.1 hsec
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
  refine ⟨c * κ * (Module.finrank ℂ W.Wp * Module.finrank ℂ W.Wq), by positivity, fun lam' hl A hA => ?_⟩
  obtain ⟨ν, hlam, hn1, -⟩ := GlobalTheory.hcParam_sub_integral _ (lamD D τ) lam' hNum.2.1 hA.1
  have hq : n1 ν ≤ D.R.k * D.R.m ^ 5 := by
    have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
    have h1 : Cn ≤ (D.R.m : ℝ) ^ 2 := by have := hBig.2.2; nlinarith
    have h2 : ((n1 ν : ℕ) : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 5 := by
      rw [hn1]
      calc _ ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := hl
        _ ≤ (D.R.m : ℝ) ^ 2 * D.R.k * (D.R.m : ℝ) ^ 3 := by gcongr
        _ = _ := by ring
    exact_mod_cast h2
  have hgap : GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) := by
    rw [hlam, ← heps]; exact (hν ν hq).2.2.1
  have hDS : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).IsDS (epsSH D.R) lam' := ⟨hA.1, hA.2.1⟩
  have hU := (_root_.GlobalTheory.Amp.Side.both_sides D τ w w' θ W lam' A hθ hv hTT hW hA).1
  obtain ⟨l, b1, e1⟩ := exists_bessel_scale_gap hH hc s1 ⟨A.H, A.σ⟩ hDS hU hgap hok
  obtain ⟨l', b2, e2⟩ := exists_bessel_scale_gap hH hc s2 ⟨A.H, A.σ⟩ hDS hU hgap hok
  obtain ⟨k1, k2, w0, η, hw0, hη, hJ⟩ :=
    GlobalTheory.T.amplitude_eq_smul_normalisedAmplitude_largeGap hH D τ w w' θ W lam' A _ l l' hθ hkg hT hT' hW hA hgap hok b1 b2 e1 e2
  have hw0' : w0 ≠ 0 := by
    obtain ⟨P, -, h1, -⟩ := hw0
    rintro rfl
    simp at h1
  obtain ⟨d1, d2⟩ := hdeg lam' A hA ⟨_, hgap, hok⟩ w0 hw0'
  have hd : 0 < PI.BesselPeriodGGP.fdegH W.μG A.σ w0 := by
    rw [d1] at d2; exact (mul_pos_iff_of_pos_left hκ).1 d2
  rw [hN] at e1 e2
  have key := hnorm ⟨A.H, A.σ⟩ lam' _ l l' w0 hDS hgap hok hcell e1 e2 k1 k2 hw0
  have h5 := lintegral_weight_smul hk hsec (J := A.J W.μG)
    (J' := amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 W.μG) (η := η) fun γ hγ => hJ W.μG γ hγ hG.2.2.1
  unfold MMv
  rw [← t1, ← t2, h5]
  refine (congrArg _ key).trans ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _), hη, mul_pow, Real.sq_sqrt (by positivity), d1]
  congr 1
  show _ * (c / PI.BesselPeriodGGP.fdegH W.μG A.σ w0 ^ 3) = _
  field_simp

end GlobalTheory.Amp.OpenCellNormGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentConjIffOfUnitriangularIsometry
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlagMove

variable {D : D7}

theorem Xsp_eq_Xflag {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Xsp F = Xflag F D.R.rS := by
  unfold Xsp Xflag
  simp only [Formalism.MainNotions.S.FlagG.X, Formalism.MainNotions.S.FlagG.Xa]
  congr 1
  ext v
  simp

private lemma finrank_Xflag {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Fintype.card {i : Fin D.R.rS // i.1 < j} := by
  have h : Xflag F j = Submodule.span D.host.E
      (Set.range (fun i : {i : Fin D.R.rS // i.1 < j} => F.fl.e i.1)) := by
    unfold Xflag
    simp only [Formalism.MainNotions.S.FlagG.Xa]
    congr 1
    ext v
    simp
  rw [h, finrank_span_eq_card]
  exact F.fl.e_indep.comp _ Subtype.val_injective

theorem finrank_Xflag_eq {T T0 : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F0 : LFlag (D.sp.Y 0) D.R.rS T0) (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Module.finrank D.host.E (Xflag F0 j) := by
  rw [finrank_Xflag, finrank_Xflag]

theorem orth_iff {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {U U' : Submodule D.host.E (VS D).V} (hU : ∀ x, β x ∈ U' ↔ x ∈ U) (y : (VS D).V) :
    β y ∈ orth (VS D) U' ↔ y ∈ orth (VS D) U := by
  have hiso : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y := hi
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h x hx
    rw [← hiso]
    exact h (β x) ((hU x).2 hx)
  · intro h x hx
    have hx' : β.symm x ∈ U := (hU _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hx)
    have h' := h _ hx'
    rw [← hiso, LinearEquiv.apply_symm_apply] at h'
    exact h'

private lemma frame_mem_Xflag {T0 : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T0) (j : ℕ)
    (a : Fin (D.R.rS + 1)) (ha : a.1 < j) (hr : a.1 < D.R.rS) : frame F0 a ∈ Xflag F0 j := by
  have e : a = Fin.castSucc ⟨a.1, hr⟩ := Fin.ext rfl
  rw [e]
  unfold frame Xflag
  simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, Formalism.MainNotions.S.FlagG.Xa]
  exact Submodule.subset_span ⟨⟨a.1, hr⟩, ha, rfl⟩

theorem map_Xflag_le {T T0 : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F0 : LFlag (D.sp.Y 0) D.R.rS T0)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hU : IsUpUni U) (hf : ∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) (j : ℕ) :
    ∀ x ∈ Xflag F j, σ x ∈ Xflag F0 j := by
  intro x hx
  have key : Submodule.span D.host.E (F.fl.e '' {i | i.1 < j}) ≤
      (Xflag F0 j).comap (σ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i.1 < j := hi
    show σ (F.fl.e i) ∈ Xflag F0 j
    have he : F.fl.e i = frame F (Fin.castSucc i) := by
      unfold frame
      simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [he, hf]
    refine Submodule.sum_mem _ (fun a _ => ?_)
    by_cases hab : Fin.castSucc i < a
    · rw [(hU a (Fin.castSucc i)).1 hab, zero_smul]
      exact Submodule.zero_mem _
    · have h1 : a.1 ≤ i.1 := by
        simpa [Fin.lt_def] using hab
      have h2 := i.2
      exact Submodule.smul_mem _ _ (frame_mem_Xflag F0 j a (by omega) (by omega))
  exact key hx

theorem mem_Xflag_iff {T T0 : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F0 : LFlag (D.sp.Y 0) D.R.rS T0)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hU : IsUpUni U) (hf : ∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) (j : ℕ) (x : (VS D).V) :
    σ x ∈ Xflag F0 j ↔ x ∈ Xflag F j := by
  have hle : (Xflag F j).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag F0 j := by
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    exact map_Xflag_le F F0 σ U hU hf j y hy
  have hfin : FiniteDimensional D.host.E (Xflag F0 j) := by
    show FiniteDimensional D.host.E (Submodule.span D.host.E (F0.fl.e '' {i | i.1 < j}))
    exact FiniteDimensional.span_of_finite D.host.E ((Set.toFinite _).image _)
  have heq : (Xflag F j).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag F0 j := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    exact le_of_eq ((finrank_Xflag_eq F0 F j).trans (LinearEquiv.finrank_map_eq σ (Xflag F j)).symm)
  constructor
  · intro h
    rw [← heq, Submodule.mem_map] at h
    obtain ⟨y, hy, hyx⟩ := h
    have hyx' : y = x := σ.injective hyx
    rw [hyx'] at hy
    exact hy
  · exact map_Xflag_le F F0 σ U hU hf j x

theorem nrat_conj_iff : ∀ (D : D7) {T : D.host.E} (F F0 : LFlag (D.sp.Y 0) D.R.rS T)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E),
    σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → IsUpUni U → (∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) →
    ∀ n, n ∈ NRat F ↔ σ * n * σ⁻¹ ∈ NRat F0 := by
  intro D T F F0 σ U hσ hU hf n
  have hX : ∀ j x, σ x ∈ Xflag F0 j ↔ x ∈ Xflag F j := fun j x => mem_Xflag_iff F F0 σ U hU hf j x
  have hS : ∀ x, σ x ∈ Xsp F0 ↔ x ∈ Xsp F := by
    intro x
    rw [Xsp_eq_Xflag, Xsp_eq_Xflag]
    exact hX _ x
  have hO : ∀ x, σ x ∈ orth (VS D) (Xsp F0) ↔ x ∈ orth (VS D) (Xsp F) := orth_iff hσ hS
  have hc : ∀ x, (σ * n * σ⁻¹) (σ x) = σ (n x) := by
    intro x
    show σ (n (σ.symm (σ x))) = σ (n x)
    rw [LinearEquiv.symm_apply_apply]
  have hsub : ∀ x, σ (n x) - σ x = σ (n x - x) := fun x => (map_sub σ _ _).symm
  unfold NRat
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨mul_mem (mul_mem hσ h1) (inv_mem hσ), ?_, ?_⟩
    · intro j x hx
      obtain ⟨y, rfl⟩ := σ.surjective x
      rw [hc, hsub, hX]
      exact h2 j y ((hX _ y).1 hx)
    · intro x hx
      obtain ⟨y, rfl⟩ := σ.surjective x
      rw [hc, hsub, hS]
      exact h3 y ((hO y).1 hx)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · have e : n = σ⁻¹ * (σ * n * σ⁻¹) * σ := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hσ) h1) hσ
    · intro j x hx
      have h' := h2 j (σ x) ((hX _ x).2 hx)
      rw [hc, hsub, hX] at h'
      exact h'
    · intro x hx
      have h' := h3 (σ x) ((hO x).2 hx)
      rw [hc, hsub, hS] at h'
      exact h'

end GlobalTheory.FlagMove
end
end

