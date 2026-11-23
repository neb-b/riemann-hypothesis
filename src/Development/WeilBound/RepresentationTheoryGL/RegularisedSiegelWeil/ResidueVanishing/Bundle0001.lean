module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Leaves
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0456
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Assembly
section
noncomputable section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace PositivityTheory.Rg.Rsw.Kplug

set_option maxHeartbeats 1000000 in
theorem residue_vanishes_of_siegel_eisenstein : K0 → K1 → K2 → SimplePoleRescaling → ContinuousInvariantCoefficients → KillingPolyConst → ContinuationThroughChart → K4 →
    GlobalTheory.Published.SiegelEisensteinContinuation → PositivityTheory.Rg.Rsw.ResCore → ResidueVanishing := by
  intro k0 k1 k2 k2b k2c k3a k3b k4 hP hC D ψ θ A cA a hDef _ B W t hd _ _ hW0 _ hA h2 hlt χ omB omW hWB hWW ν 𝓕 hν m hm u hu hinv hK φ hφ hKφ
  have hrk := hd.rank_add
  have hIw := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a hDef.maj
  have hχ := _root_.GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ W.rank hWW.hecT hWW.resT
  obtain ⟨hEC, hReg⟩ := hP D A (by omega) a hDef.maj hIw χ⁻¹ W.rank hχ.1 hχ.2 _ _
    (k0 D ψ A B χ omB hWB ν 𝓕 hν a hDef.maj φ hφ hKφ)
  obtain ⟨U, d, E, ε, hU, hR, hs, hd0, hhol, hc, hi, he, hrad⟩ :=
    k1 D A _ hEC hReg (fun g => hEC.1.analyticOnNhd_flat g) (sZero A B)
  obtain ⟨m0, hm0, hp0⟩ := _root_.GlobalTheory.StdUnn.ConjElt.exists_isConj D
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.StdUnn.chart_exists D A m0 hm0
  obtain ⟨p, hp⟩ := hp0 A a hDef.maj κ hκ
  obtain ⟨lam, hlam, hψ', -⟩ := _root_.GlobalTheory.StdUnn.shift_char_realPar D ψ hWB.std θ hDef.inf m0 hm0
  obtain ⟨oB, hTB⟩ := _root_.GlobalTheory.StdUnn.exists_transport_std D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf κ
  obtain ⟨νW, 𝓨, hνW⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank A.rank
  obtain ⟨oW, hTW⟩ := _root_.GlobalTheory.StdUnn.exists_transport_std D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf κ
  have hSB : IsWeilSch (shift ψ lam) χ⁻¹ θ B ν oB :=
    ⟨_root_.GlobalTheory.StdUnn.transport_levi D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam,
     _root_.GlobalTheory.StdUnn.Unip.transport_unip D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam,
     _root_.GlobalTheory.StdUnn.WeylStd.main D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam⟩
  have hSW : IsWeilSch (shift ψ lam) χ⁻¹ θ W νW oW :=
    ⟨_root_.GlobalTheory.StdUnn.transport_levi D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf m0 hm0 κ hκ oW hTW lam hlam,
     _root_.GlobalTheory.StdUnn.Unip.transport_unip D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf m0 hm0 κ hκ oW hTW lam hlam,
     _root_.GlobalTheory.StdUnn.WeylStd.main D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf m0 hm0 κ hκ oW hTW lam hlam⟩
  let Φ : schwartzA θ B.rank A.rank :=
    ⟨sch ψ A B ν 𝓕 (omB ((p : GA D (dblSp A))⁻¹, 1) φ),
      (_root_.GlobalTheory.SchSchwartzAll.schSchwartz D ψ hWB.std θ hDef.inf A B ν 𝓕 hν).1 _ (hWB.om_pres _ φ hφ)⟩
  obtain ⟨-, hCont, hser⟩ := k3b D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam a hDef.maj p hp φ hφ hKφ Φ rfl
    U d E hU hR hs hd0 hhol hc hi he
  obtain ⟨hH, hL⟩ := k3a D A m0 hm0 κ hκ a hDef.maj p hp
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    have hBr : B.rank = W.rank + 2 * t := by omega
    simp only [sZero]; rw [hBr, hA]; push_cast; ring
  obtain ⟨hcc, hcl⟩ := k2c D _ _ _ _ _ _ _ _ hCont ε hrad 1
  have hCont' := hCont
  have hrad' := hrad
  rw [hs0] at hCont' hrad'
  obtain ⟨hv, hkill⟩ := hC D A.rank t B W ⟨hd⟩ hA.symm h2 hlt hW0 (shift ψ lam) hψ' χ⁻¹ hχ.1 hχ.2 θ hDef.inf ν νW
    ⟨𝓕, hν⟩ ⟨𝓨, hνW⟩ oB oW hSB hSW _ hH hL Φ U d _ _ hCont' ε hrad'
  rw [← hs0] at hv hkill
  refine ⟨fun g => cf d (fun z g => npow (absA D (aP A p)) (z - sZero A B) * E z (κ.symm g * ((p : GA D (dblSp A))⁻¹)))
    (sZero A B) ε 1 (κ (g * p)), ⟨hEC.1, fun g => ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := k2 _ _ U d (sZero A B) ε _ hU hR (hCont.hol (κ (g * p))) hd0 hrad
      (fun z hz => hCont.eq z hz (κ (g * p))) (fun k hk => congrFun (hv k hk) (κ (g * p)))
    exact k2b _ _ _ _ _ _ (hom_pos _ _) h1 h2 (fun s hs => hser s hs g)
  · exact k4 D ψ θ A cA a hDef W χ omW hWW νW 𝓨 hνW m0 hm0 κ hκ oW hTW p m hm u hu hinv hK _ hcc hcl
      (fun X _ νX _ c hc hcp w hw h0 => hkill X νX c w hc hcp hw h0)

end PositivityTheory.Rg.Rsw.Kplug

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.ContinuationPoleOrder
section
noncomputable section

open Filter Topology Set Metric GlobalTheory.Cont

namespace PositivityTheory.Rg.Rsw.Kplug

theorem k2b2_tendsto {s₀ : ℂ} : ∀ (k : ℕ) {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}, HasFPowerSeriesAt g p s₀ →
    (∀ i < k, p.coeff i = 0) → Tendsto (fun s => g s / (s - s₀) ^ k) (𝓝[≠] s₀) (𝓝 (p.coeff k)) := by
  intro k g p hp hk
  have hG := hp.has_fpower_series_iterate_dslope_fslope k
  have hval : ∀ j, (Function.swap dslope s₀)^[j] g s₀ = p.coeff j := fun j => by
    rw [← (hp.has_fpower_series_iterate_dslope_fslope j).coeff_zero 1]
    have := FormalMultilinearSeries.coeff_iterate_fslope (p := p) j 0
    rw [zero_add] at this
    exact this
  have hz : ∀ j < k, (Function.swap dslope s₀)^[j] g s₀ = 0 := fun j hj => by
    rw [hval j, hk j hj]
  have heq := pow_sub_smul_iterate_dslope_of_zero k hz
  have hc : Tendsto ((Function.swap dslope s₀)^[k] g) (𝓝[≠] s₀) (𝓝 (p.coeff k)) := by
    rw [← hval k]
    exact hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : (s - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
  rw [← heq s, smul_eq_mul, mul_div_cancel_left₀ _ hne]

theorem k2b2_cps (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (n : ℕ) :
    (cauchyPowerSeries f c R).coeff n =
      (2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(c, R), (1 / (z - c)) ^ n • (z - c)⁻¹ • f z :=
  cauchyPowerSeries_apply f c R n 1

theorem continuation_pole_order : PositivityTheory.Rg.Rsw.Kplug.K2 := by
  intro h e U d s₀ ε σ hU hRD he hd hrad hED hres
  obtain ⟨hε, hball, hdne⟩ := hrad
  set c : ℂ := (2 * ↑Real.pi * Complex.I)⁻¹ *
    ∮ (z : ℂ) in C(s₀, ε), (z - s₀) ^ (1 - 1) * (e z / Polynomial.eval z d) with hc
  set H : ℂ → ℂ := fun z => e z / Polynomial.eval z d with hH
  have hs₀U : s₀ ∈ U := hball (mem_closedBall_self hε.le)
  have hdan : ∀ z, AnalyticAt ℂ (fun z => Polynomial.eval z d) z := fun z =>
    Differentiable.analyticAt (Polynomial.differentiable d) z
  have hean : AnalyticOnNhd ℂ e U := he.analyticOnNhd hU
  have hHmer : ∀ z ∈ U, MeromorphicAt H z := fun z hz =>
    (hean z hz).meromorphicAt.div (hdan z).meromorphicAt
  have hext : IsExtAt h s₀ H := by
    refine ⟨U, hs₀U, hRD, hHmer, ?_⟩
    obtain ⟨M, hM⟩ := ((Polynomial.finite_setOf_isRoot hd).image Complex.re).bddAbove
    refine ⟨max σ M, fun z hz => ?_⟩
    have hz' : max σ M < z.re := hz
    have hdz : Polynomial.eval z d ≠ 0 := by
      intro h0
      have : z.re ≤ M := hM ⟨z, h0, rfl⟩
      exact absurd hz' (not_lt.mpr (le_max_of_le_right this))
    simp only [hH, hED z (lt_of_le_of_lt (le_max_left _ _) hz')]
    field_simp
  have hT : Tendsto (fun s => (s - s₀) * H s) (𝓝[≠] s₀) (𝓝 c) := by
    obtain ⟨q, hdq, hndvd⟩ := d.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hd s₀
    generalize hm : Polynomial.rootMultiplicity s₀ d = m at hdq
    have hq0 : q.eval s₀ ≠ 0 := fun h0 => hndvd (Polynomial.dvd_iff_isRoot.mpr h0)
    have hdeval : ∀ z, Polynomial.eval z d = (z - s₀) ^ m * q.eval z := fun z => by
      have := congrArg (Polynomial.eval z) hdq
      simpa using this
    have hqne : ∀ z ∈ closedBall s₀ ε, q.eval z ≠ 0 := by
      intro z hz h0
      by_cases hzs : z = s₀
      · exact hq0 (hzs ▸ h0)
      · exact hdne z hz hzs (by rw [hdeval, h0, mul_zero])
    set F : ℂ → ℂ := fun z => e z / q.eval z with hF
    have hFd : DifferentiableOn ℂ F (closedBall s₀ ε) :=
      (he.mono hball).div q.differentiable.differentiableOn hqne
    set R : NNReal := ε.toNNReal with hRdef
    have hR : (R : ℝ) = ε := Real.coe_toNNReal _ hε.le
    have hRpos : 0 < R := Real.toNNReal_pos.mpr hε
    have hFps := (show DifferentiableOn ℂ F (closedBall s₀ (R : ℝ)) by rw [hR]; exact hFd).hasFPowerSeriesOnBall hRpos
    have hcf : ∀ j, j + 1 ≤ m → (cauchyPowerSeries F s₀ (R : ℝ)).coeff j =
        (2 * ↑Real.pi * Complex.I)⁻¹ *
          ∮ (z : ℂ) in C(s₀, ε), (z - s₀) ^ (m - 1 - j) * (e z / Polynomial.eval z d) := by
      intro j hj
      rw [k2b2_cps, hR, smul_eq_mul]
      congr 1
      apply circleIntegral.integral_congr hε.le
      intro z hz
      have hzs : z - s₀ ≠ 0 := sub_ne_zero.mpr (ne_of_mem_sphere hz hε.ne')
      obtain ⟨r, hr⟩ : ∃ r, m = r + j + 1 := ⟨m - 1 - j, by omega⟩
      have hr' : m - 1 - j = r := by omega
      simp only [smul_eq_mul, hdeval, hF, hr', hr]
      by_cases hqz : q.eval z = 0
      · simp [hqz]
      · generalize z - s₀ = w at hzs ⊢
        generalize e z = a
        generalize Polynomial.eval z q = b at hqz ⊢
        rw [show r + j + 1 - 1 - j = r by omega, pow_succ, pow_add, one_div, inv_pow]
        field_simp
    have hFan := hFps.hasFPowerSeriesAt
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have hc0 : c = 0 := by
        have hI : ∮ (z : ℂ) in C(s₀, ε), (z - s₀) ^ (1 - 1) * (e z / Polynomial.eval z d) =
            ∮ (z : ℂ) in C(s₀, ε), F z := by
          apply circleIntegral.integral_congr hε.le
          intro z hz
          simp [hdeval, hm0, hF]
        rw [hc, hI, Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le
          Set.countable_empty hFd.continuousOn, mul_zero]
        intro z hz
        exact hFd.differentiableAt (Filter.mem_of_superset (isOpen_ball.mem_nhds hz.1) ball_subset_closedBall)
      rw [hc0]
      have hlim : Tendsto (fun s => (s - s₀) * F s) (𝓝 s₀) (𝓝 ((s₀ - s₀) * F s₀)) :=
        ((continuous_id.sub continuous_const).continuousAt.mul hFan.continuousAt).tendsto
      rw [sub_self, zero_mul] at hlim
      refine (hlim.mono_left nhdsWithin_le_nhds).congr' (Filter.Eventually.of_forall fun s => ?_)
      simp [hH, hF, hdeval, hm0]
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hcoef : ∀ i < n, (cauchyPowerSeries F s₀ (R : ℝ)).coeff i = 0 := by
        intro i hi
        rw [hcf i (by omega)]
        have := hres (n + 1 - i) (by omega)
        rwa [show n + 1 - i - 1 = n + 1 - 1 - i by omega] at this
      have hlim := k2b2_tendsto n hFan hcoef
      rw [hcf n (by omega), show n + 1 - 1 - n = 1 - 1 by omega] at hlim
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hw : s - s₀ ≠ 0 := sub_ne_zero.mpr hs
      simp only [hH, hF, hdeval]
      by_cases hqs : Polynomial.eval s q = 0
      · simp [hqs]
      · rw [pow_succ]
        field_simp
  refine ⟨⟨H, hext, 0, by simp, ?_⟩, ⟨H, hext, ?_⟩⟩
  · refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp
  · have hmer : MeromorphicAt ((fun s => s - s₀) * H) s₀ :=
      (by fun_prop : MeromorphicAt (fun s => s - s₀) s₀).mul (hHmer s₀ hs₀U)
    have h0 : 0 ≤ meromorphicOrderAt ((fun s => s - s₀) * H) s₀ :=
      (tendsto_nhds_iff_meromorphicOrderAt_nonneg hmer).mp ⟨c, hT⟩
    rw [meromorphicOrderAt_mul (by fun_prop) (hHmer s₀ hs₀U), meromorphicOrderAt_id_sub_const] at h0
    cases ho : meromorphicOrderAt H s₀ with
    | top => exact le_top
    | coe n =>
      rw [ho] at h0
      have : (0 : WithTop ℤ) ≤ ((1 + n : ℤ) : WithTop ℤ) := by exact_mod_cast h0
      have h1 : (0 : ℤ) ≤ 1 + n := by exact_mod_cast this
      exact_mod_cast (by omega : (-(1 : ℕ) : ℤ) ≤ n)

end PositivityTheory.Rg.Rsw.Kplug

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.ContinuousInvariantCoefficients
section
noncomputable section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace PositivityTheory.Rg.Rsw.Kplug

set_option maxHeartbeats 1000000 in
theorem continuation_through_chart : ContinuationThroughChart := by
  intro D ψ A B χ omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam a ha p hp f hf hK Φ hΦ U d E hU hR hs hd hhol hc hi he
  obtain ⟨h0, hflat, hact⟩ := _root_.GlobalTheory.StdUnn.flat_swSec_eq_sect D ψ A B χ omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam a p f hf Φ hΦ
  have hIw := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  have hmem := GlobalTheory.SwSecMem.swSec_mem_degPS GlobalTheory.weilRepresentationUnitaryPair D ψ A B χ omh hW ν 𝓨 hν f hf a hK
  have hχ := _root_.GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ B.rank hW.hecT hW.resT
  have hP' := _root_.GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ hμ κ hκ
  have hG' := _root_.GlobalTheory.StdUnn.chart_mem_GF_iff D A μ hμ κ hκ
  obtain ⟨hκc, hκc'⟩ := _root_.GlobalTheory.StdUnn.chart_continuous D A μ hμ κ hκ
  have hr : 0 < absA D (aP A p) := hom_pos _ _
  have hfs : ∀ z, fam (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) z = sect omS (hgtStd A a κ p) Φ z := fun z => by
    funext g; simp only [fam, sect, h0]
  have hback : ∀ g : G D A.rank, κ (κ.symm g * (p : GA D (dblSp A))⁻¹ * p) = g := fun g => by simp
  have hone : ∀ z : ℂ, npow (absA D (aP A p)) (z - sZero A B) * npow (absA D (aP A p)) (sZero A B - z) = 1 := fun z => by
    rw [← npow_add hr]; simp
  have hsect : ∀ z g, sect omS (hgtStd A a κ p) Φ z g = npow (absA D (aP A p)) (z - sZero A B) *
      flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z (κ.symm g * (p : GA D (dblSp A))⁻¹) := fun z g => by
    rw [hflat, hback, ← mul_assoc, hone, one_mul]
  have hL : ∀ z, LeftInv (P D A.rank ⊓ GF D A.rank) (sect omS (hgtStd A a κ p) Φ z) := fun z q hq g => by
    rw [hsect, hsect, map_mul, mul_assoc (κ.symm q)]
    congr 1
    exact GlobalTheory.Eis.leftInv_of_mem hχ.1 (GlobalTheory.Eis.flat_mem hIw hmem z) _
      ⟨(hP' _).2 (by simpa using hq.1), (hG' _).2 (by simpa using hq.2)⟩ _
  have h3 : ∀ (z : ℂ) (g : GA D (dblSp A)), GlobalTheory.Eis.eisSer A (flat A a (swSec A B omh ν 𝓨 f) (sZero A B)) g z =
      npow (absA D (aP A p)) (sZero A B - z) * eisS (fam (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) z) (κ (g * p)) :=
    fun z g => by
      rw [hfs]
      exact ((_root_.GlobalTheory.StdUnn.cosetSum_along_mulEquiv _ _ κ (siegel A) (GQ (dblSp A)) (P D A.rank) (GF D A.rank) hP' hG' _ _ _ _ (fun g => hflat z g) (hL z)).2 g).2
  refine ⟨?_, ⟨hU, hR, hs, hd, fun g => ?_, ?_, fun z hz γ hγ g => ?_, fun z hz g => ?_⟩, fun z _ g => h3 z g⟩
  · have e : (fun g => (omS g Φ).1 0) = fun g => swSec A B omh ν 𝓨 f (κ.symm g * (p : GA D (dblSp A))⁻¹) := by
      funext g
      have := hsect (sZero A B) g
      simpa [sect, h0, flatH_self] using this
    rw [e]
    exact (hmem.2.1 : Continuous _).comp (hκc'.mul continuous_const)
  · refine DifferentiableOn.mul ?_ (hhol _)
    simp only [npow_eq_exp hr]
    fun_prop
  · refine ContinuousOn.mul ?_ (hc.comp (f := fun y : ℂ × G D A.rank => (y.1, κ.symm y.2 * (p : GA D (dblSp A))⁻¹))
      (continuous_fst.prodMk ((hκc'.comp continuous_snd).mul continuous_const)).continuousOn fun y hy => ⟨hy.1, trivial⟩)
    simp only [npow_eq_exp hr]
    fun_prop
  · rw [map_mul, mul_assoc (κ.symm γ), hi z hz _ ((hG' _).2 (by simpa using hγ))]
  · rw [he z hz, h3, hback]
    linear_combination (d.eval z * eisS (fam (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) z) g) * hone z

theorem mem_section_space : K0 := fun D ψ A B χ om hW ν 𝓨 hν a _ f hf hK =>
  GlobalTheory.SwSecMem.swSec_mem_degPS GlobalTheory.weilRepresentationUnitaryPair D ψ A B χ om hW ν 𝓨 hν f hf a hK

theorem continuation_chart_defined : KillingPolyConst := by
  intro D A μ hμ κ hκ a ha p hp
  have hI := GlobalTheory.Eis.isIwasawa_Khat (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha)
  have hIw := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  obtain ⟨-, hκc'⟩ := _root_.GlobalTheory.StdUnn.chart_continuous D A μ hμ κ hκ
  haveI := t2Space_adeleRing' (F := D.host.F)
  have h1 : Continuous (hgt A a) := hIw.continuous_hgtH continuous_absE (isCompact_Khat A a)
  refine ⟨⟨(h1.comp (hκc'.mul continuous_const)).mul continuous_const, fun g => mul_pos (hgtH_pos _) (hom_pos _ _),
    fun q hq α hα g => ?_⟩, ?_⟩
  · have hq' : κ.symm q ∈ siegel A := (_root_.GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ hμ κ hκ (κ.symm q)).2 (by simpa using hq)
    have hdet : aP A ⟨κ.symm q, hq'⟩ = Matrix.GeneralLinearGroup.det α :=
      _root_.GlobalTheory.StdUnn.chart_aP_eq_det D A μ hμ κ hκ ⟨κ.symm q, hq'⟩ α (by simpa using hα)
    have e : hgt A a (κ.symm q * (κ.symm g * (p : GA D (dblSp A))⁻¹)) =
        absA D (aP A ⟨κ.symm q, hq'⟩) * hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹) := hI.iwAbs_left ⟨κ.symm q, hq'⟩ _
    simp only [hgtStd]
    rw [map_mul, mul_assoc (κ.symm q), e, hdet, mul_assoc]
  · haveI : Submodule.IsFullLattice D.host.E (stdLattice D.host.E (A.rank + A.rank)) := isLattice_stdLattice
    refine ⟨levelOpen D.sp.cm.sig (Jst D A.rank) (stdLattice D.host.E (A.rank + A.rank)), isOpen_levelOpen _ _ _,
      fun k hk hf g => ?_⟩
    have hkK : k ∈ K D A.rank := mem_levelAll.2 ⟨mem_levelOpen.1 hk, fun w => by
      rw [mem_finPts_iff_forall.1 hf w]; exact one_mem _⟩
    have hk' : (p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
      rw [hp]; simpa [mul_assoc] using hkK
    have e : hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹ * ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹)) =
        hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹) := hI.iwAbs_right _ hk'
    simp only [hgtStd]
    rw [← e]; simp [mul_assoc]

theorem simple_pole_rescaling : SimplePoleRescaling := by
  intro h h' s₀ c r σ hr hc hp e
  have ha : AnalyticOnNhd ℂ (fun s => npow r (s₀ - s)) (rightOf (s₀.re - 1)) := by
    intro s _
    rw [funext fun s => npow_eq_exp hr (s₀ - s)]
    fun_prop
  have hg := holValueAt_self ha (s₀ := s₀) (by linarith)
  have h1 : npow r (s₀ - s₀) = 1 := by simp
  have hm := (hp.mul_hol (by simpa using hc) hg).2
  simp only [h1, mul_one] at hm
  exact CoeffAt.congr (by simpa using hm) ⟨σ, fun s hs => by rw [e s hs, mul_comm]⟩

theorem continuous_invariant_coefficients : ContinuousInvariantCoefficients := by
  intro D n H φ s₀ U d E σ hC ε hε k
  have hm : ∀ x : ℝ, circleMap s₀ ε x ∈ Metric.closedBall s₀ ε := fun x => circleMap_mem_closedBall s₀ hε.1.le x
  have hne : ∀ x : ℝ, d.eval (circleMap s₀ ε x) ≠ 0 := fun x => hε.2.2 _ (hm x) (circleMap_ne_center hε.1.ne')
  refine ⟨continuous_const.mul ?_, fun γ hγ g => ?_⟩
  · have hE : Continuous fun y : G D n × ℝ => E (circleMap s₀ ε y.2) y.1 :=
      hC.cont.comp_continuous (f := fun y : G D n × ℝ => (circleMap s₀ ε y.2, y.1))
        (((continuous_circleMap s₀ ε).comp continuous_snd).prodMk continuous_fst) fun y => ⟨hε.2.1 (hm y.2), trivial⟩
    have hc : Continuous fun y : G D n × ℝ => circleMap s₀ ε y.2 := (continuous_circleMap s₀ ε).comp continuous_snd
    simp only [circleIntegral, deriv_circleMap]
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun (g : G D n) (x : ℝ) => (circleMap 0 ε x * Complex.I) •
        ((circleMap s₀ ε x - s₀) ^ (k - 1) * (E (circleMap s₀ ε x) g / d.eval (circleMap s₀ ε x)))) ?_ _ _
    exact (((continuous_circleMap 0 ε).comp continuous_snd).mul continuous_const).smul
      (((hc.sub continuous_const).pow _).mul (hE.div (d.continuous.comp hc) fun y => hne y.2))
  · simp only [cf, circleIntegral, hC.inv _ (hε.2.1 (hm _)) γ hγ g]

theorem theta_kernel_identity (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (A W : HSp D) (χ : (AE D)ˣ →* Circle)
    (omh : GA D (dblSp A) × GA D W →* Module.End ℂ (WO (dblSp A) W → ℂ)) (hW : IsWeilDatumO ψ (dblSp A) W 1 χ omh)
    (ν : Measure (WO A W)) (𝓨 : Set (WO A W)) (hν : IsCovolOne (ratL W A) ν 𝓨) (κ : GA D (dblSp A) ≃* G D A.rank)
    (omS : G D A.rank →* Module.End ℂ (schwartzA θ W.rank A.rank)) (hT : IsTransport ψ θ A W ν 𝓨 omh κ omS)
    (p : GA D (dblSp A)) (Ψ : schwartzA θ W.rank A.rank) :
    ∃ f, IsThetaFunO ψ (dblSp A) W f ∧ ∀ g h, theta omS Ψ (κ (g * p)) h = thetaKO omh g h f := by
  obtain ⟨f, hf, e⟩ := (_root_.GlobalTheory.SchSchwartzAll.schSchwartz D ψ hW.std θ hθ A W ν 𝓨 hν).2.1 Ψ.1 Ψ.2
  refine ⟨omh (p, 1) f, hW.om_pres _ f hf, fun g h => ?_⟩
  rw [theta, hT (g * p) f hf Ψ e.symm, ← _root_.GlobalTheory.StdUnn.thetaKO_eq_tsum_sch D ψ A W χ omh hW ν 𝓨 hν f hf (g * p) h]
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

end PositivityTheory.Rg.Rsw.Kplug

end
end

