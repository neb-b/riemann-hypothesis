module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsPadicIntMatrixChange
section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.MomN

def zcHom (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zc_eq_zcHom {q : ℕ} [Fact q.Prime] (x : ℤ_[q]) : zc x = zcHom q x := rfl

theorem zc_continuous' {q : ℕ} [Fact q.Prime] : Continuous (zc : ℤ_[q] → ℂ_[q]) :=
  (continuous_algebraMap ℚ_[q] ℂ_[q]).comp continuous_subtype_val

def linZ {q : ℕ} [Fact q.Prime] {κ κ' : Type} [Fintype κ] (a : κ' → κ → ℤ_[q]) :
    C(κ → ℤ_[q], κ' → ℤ_[q]) :=
  ⟨fun x i => ∑ j, a i j * x j, by fun_prop⟩

def pullCLM {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) : C(Y, ℂ_[q]) →L[ℂ_[q]] C(X, ℂ_[q]) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.comp A
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } 1 (fun f => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
        exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => f.norm_coe_le_norm (A x))

theorem pullCLM_norm_le {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) : ‖(pullCLM (q := q) A)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem pullCLM_apply {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) (f : C(Y, ℂ_[q])) : pullCLM A f = f.comp A := rfl

def monoC {q : ℕ} [Fact q.Prime] {κ : Type} {k : ℕ} (σ : Fin k → κ) : C(κ → ℤ_[q], ℂ_[q]) :=
  ⟨fun x => ∏ l, zc (x (σ l)), by
    exact continuous_finsetProd _ fun l _ => zc_continuous'.comp (continuous_apply (σ l))⟩

theorem momInt_push (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (v : κ → V) (w : κ' → V) (c : κ' → κ → ℂ) (a : κ' → κ → ℤ_[q])
    (G : V → ℂ) (hc : ∀ i j, ι (c i j) = zc (a i j)) (hw : ∀ i, w i = ∑ j, c i j • v j) (h : MomInt ι v G) :
    MomInt ι w G := by
  classical
  obtain ⟨μ, hμ, hm⟩ := h
  refine ⟨μ.comp (pullCLM (linZ a)), ?_, ?_⟩
  · calc ‖μ.comp (pullCLM (linZ a))‖ ≤ ‖μ‖ * ‖pullCLM (q := q) (linZ a)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hμ (pullCLM_norm_le _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro k j f hf
    have hfe : pullCLM (linZ a) f = ∑ σ : Fin k → κ, (∏ l, zc (a (j l) (σ l))) • monoC σ := by
      ext x
      rw [pullCLM_apply, ContinuousMap.comp_apply, hf]
      simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        monoC, ContinuousMap.coe_mk, linZ]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [zc_eq_zcHom, map_sum, map_mul]
      rw [Finset.prod_univ_sum]
      simp [Fintype.piFinset_univ, Finset.prod_mul_distrib]
    have hd : iteratedFDeriv ℂ k G 0 (fun l => w (j l)) =
        ∑ σ : Fin k → κ, (∏ l, c (j l) (σ l)) • iteratedFDeriv ℂ k G 0 (fun l => v (σ l)) := by
      simp only [hw]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ContinuousMultilinearMap.map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      exact ContinuousMultilinearMap.map_smul_univ _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ContinuousLinearMap.comp_apply, hfe, hd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_eq_mul, map_mul, map_prod, map_smul, smul_eq_mul, ← hm k σ (monoC σ) (fun _ => rfl)]
    simp only [hc]

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionNearZero
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.LAtZero

theorem norm_limit_le (F h e : ℂ → ℂ) (P : ℂ → Prop) (Z : Finset ℂ) (m : ℂ → ℕ) (B : ℝ)
    (hh : ContinuousAt h 0) (he : ContinuousAt e 0) (h0 : 0 ∉ Z → m 0 = 0)
    (hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), P s ∧ F s = (m 0 : ℂ) / s + h s)
    (hloc : ∀ s : ℝ, 0 < s → s < 1 → P s → ‖F s + e s - ∑ w ∈ Z, (m w : ℂ) / (s - w)‖ ≤ B) :
    ‖h 0 + e 0 - ∑ w ∈ Z.erase 0, (m w : ℂ) / (0 - w)‖ ≤ B := by
  have hc : ContinuousAt (fun s : ℂ => ‖h s + e s - ∑ w ∈ Z.erase 0, (m w : ℂ) / (s - w)‖) 0 := by
    refine ((hh.add he).sub ?_).norm
    refine tendsto_finsetSum _ fun w hw => ?_
    refine ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) ?_
    simpa using Finset.ne_of_mem_erase hw
  have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using (ne_of_gt hs)
  refine le_of_tendsto (hc.tendsto.comp (ht.mono_right nhdsWithin_le_nhds)) ?_
  filter_upwards [ht.eventually hev, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs hs1
  have h1 := hloc s hs1.1 hs1.2 hs.1
  have h2 : ∑ w ∈ Z, (m w : ℂ) / (s - w) =
      (m 0 : ℂ) / s + ∑ w ∈ Z.erase 0, (m w : ℂ) / (s - w) := by
    by_cases hz : (0 : ℂ) ∈ Z
    · rw [← Finset.add_sum_erase _ _ hz, sub_zero]
    · rw [h0 hz, Finset.erase_eq_of_notMem hz]; simp
  rw [hs.2, h2] at h1
  refine le_trans (le_of_eq ?_) h1
  simp only [Function.comp]
  congr 1
  ring

theorem exists_regular_part (f e : ℂ → ℂ) (S : Set ℂ) (B : ℝ) (hS : S.Finite)
    (he : ContinuousAt e 0) (han : AnalyticAt ℂ f 0) (hne : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), f s = 0)
    (hS0 : f 0 = 0 → 0 ∈ S) (hSz : ∀ w ∈ S, f w = 0)
    (hT : ∀ w : ℂ, 0 < w.re → w.re < 1 → |w.im| < 1 → f w = 0 → w ∈ S)
    (hbig : ∀ w ∈ S, w.re ≤ 0 → w ≠ 0 → 1 ≤ ‖w‖)
    (hcount : ∑ᶠ w ∈ S, (analyticOrderNatAt f w : ℝ) ≤ B)
    (hloc : ∀ s : ℝ, 0 < s → s < 1 → f s ≠ 0 →
      ‖deriv f s / f s + e s - ∑ᶠ w ∈ S, (analyticOrderNatAt f w : ℂ) / (s - w)‖ ≤ B) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
      (∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv f s / f s = (analyticOrderNatAt f 0 : ℂ) / s + h s) ∧
      ‖h 0‖ ≤ 2 * B + ‖e 0‖ +
        ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ f ρ = 0},
          ((analyticOrderNatAt f ρ : ℕ) : ℝ) / ‖ρ‖ := by
  classical
  obtain ⟨h, hh, hev⟩ := GlobalTheory.logDeriv_eq_order_div_add_analytic f 0 han hne
  simp only [sub_zero] at hev
  refine ⟨h, hh, hev.mono fun s hs => hs.2, ?_⟩
  simp only [finsum_mem_eq_finite_toFinset_sum _ hS] at hcount hloc
  have key := norm_limit_le (fun s => deriv f s / f s) h e (fun s => f s ≠ 0) hS.toFinset
    (analyticOrderNatAt f) B hh.continuousAt he ?_ hev hloc
  swap
  · intro hz
    have : f 0 ≠ 0 := fun h0 => hz (by simpa using hS0 h0)
    rw [analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr this]; rfl
  have hset : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ f ρ = 0} =
      ↑(hS.toFinset.filter fun ρ => 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1) := by
    ext w
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨hT w a b c d, a, b, c⟩,
      fun ⟨d, a, b, c⟩ => ⟨a, b, c, hSz w d⟩⟩
  rw [hset, finsum_mem_coe_finset, Finset.sum_filter]
  have hsum : ‖∑ w ∈ hS.toFinset.erase 0, (analyticOrderNatAt f w : ℂ) / (0 - w)‖ ≤
      ∑ w ∈ hS.toFinset, ((analyticOrderNatAt f w : ℝ) +
        if 0 < w.re ∧ w.re < 1 ∧ |w.im| < 1 then (analyticOrderNatAt f w : ℝ) / ‖w‖ else 0) := by
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun w hw => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset 0 _) fun w _ _ => ?_)
    · rw [norm_div, zero_sub, norm_neg, Complex.norm_natCast]
      split_ifs with hc
      · exact le_add_of_nonneg_left (Nat.cast_nonneg _)
      · rw [add_zero]
        refine div_le_self (Nat.cast_nonneg _) ?_
        rcases le_or_gt w.re 0 with h1 | h1
        · exact hbig w (by simpa using Finset.mem_of_mem_erase hw) h1 (Finset.ne_of_mem_erase hw)
        rcases le_or_gt 1 w.re with h2 | h2
        · exact h2.trans (re_le_norm w)
        · have h3 : 1 ≤ |w.im| := not_lt.mp fun h3 => hc ⟨h1, h2, h3⟩
          exact h3.trans (abs_im_le_norm w)
    · split_ifs <;> positivity
  rw [Finset.sum_add_distrib] at hsum
  set X := ∑ w ∈ hS.toFinset.erase 0, (analyticOrderNatAt f w : ℂ) / (0 - w)
  have : ‖h 0‖ ≤ ‖h 0 + e 0 - X‖ + ‖e 0‖ + ‖X‖ := by
    calc ‖h 0‖ = ‖(h 0 + e 0 - X) - e 0 + X‖ := by congr 1; ring
      _ ≤ ‖(h 0 + e 0 - X) - e 0‖ + ‖X‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_sub_le _ _
  linarith

theorem norm_sub_two_le {w : ℂ} (h1 : 0 ≤ w.re) (h2 : w.re < 1) (h3 : |w.im| < 1) :
    ‖w - 2‖ ≤ 7 / 2 := by
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  have : |w.re - 2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [sub_re, sub_im, re_ofNat, im_ofNat, sub_zero]
  linarith

theorem logDeriv_LFunction_near_zero : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∃ (m : ℕ) (h : ℂ → ℂ), m ≤ 1 ∧ AnalyticAt ℂ h 0 ∧ (∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv (LFunction χ) s / LFunction χ s = (m : ℂ) / s + h s) ∧ ‖h 0‖ ≤ C * (Real.log (2 * N) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by
  obtain ⟨C₁, hC₁, H₁⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  obtain ⟨C₂, hC₂, H₂⟩ := GlobalTheory.ZetaWide.main
  refine ⟨2 * C₁ + 2 * C₂ + 2, by positivity, fun N _ χ hχ => ?_⟩
  have han : AnalyticAt ℂ (LFunction χ) 0 := by
    refine DifferentiableOn.analyticAt (s := {1}ᶜ)
      (fun z hz => (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt) ?_
    exact isOpen_compl_singleton.mem_nhds (by simp)
  have hord : ∀ hL : LFunction χ 0 = 0, analyticOrderNatAt (LFunction χ) 0 = 1 := fun hL =>
    (GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ 0 (by simp) hL).2.1
  have hm : analyticOrderNatAt (LFunction χ) 0 ≤ 1 := by
    by_cases hL : LFunction χ 0 = 0
    · exact (hord hL).le
    · rw [analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr hL]; simp
  have hne : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), LFunction χ s = 0 := by
    intro hz
    have h1 := hord hz.self_of_nhds
    rw [analyticOrderNatAt, analyticOrderAt_eq_top.mpr hz] at h1
    simp at h1
  have hbig : ∀ w : ℂ, LFunction χ w = 0 → w.re ≤ 0 → w ≠ 0 → 1 ≤ ‖w‖ := by
    intro w hw hre h0
    obtain ⟨n, rfl⟩ := (GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ w hre hw).1
    rw [norm_neg, Complex.norm_natCast]
    have : n ≠ 0 := by rintro rfl; simp at h0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hL2 : LFunction χ 2 ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by simp)
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog : 1 / 2 ≤ Real.log (2 * N) := by
    have h1 : Real.log 2 ≤ Real.log (2 * N) := Real.log_le_log (by norm_num) (by linarith)
    have := Real.log_two_gt_d9
    linarith
  have hnn : 0 ≤ ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  by_cases h1 : χ = 1
  · have hq : N = 1 := by
      rw [IsPrimitive, h1, conductor_one] at hχ
      exact hχ.symm
    subst hq
    have hf : LFunction χ = riemannZeta := LFunction_modOne_eq
    rw [hf] at han hm hne hbig hL2 hnn ⊢
    have A := H₂ 2 (by norm_num) (by simp) (by norm_num) hL2
    simp only [im_ofNat, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at A
    obtain ⟨h, ha, hb, hc⟩ := exists_regular_part riemannZeta (fun s => 1 / (s - 1)) _
      (C₂ * Real.log 2) A.1
      (ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) (by simp))
      han hne (fun h => ⟨norm_sub_two_le (by simp) (by simp) (by simp), by simp, h⟩)
      (fun w hw => hw.2.2)
      (fun w a b c d => ⟨norm_sub_two_le a.le b c, by rintro rfl; simp at b, d⟩)
      (fun w hw => hbig w hw.2.2) A.2.1 (fun s hs0 hs1 hs => by
        have B := (H₂ s (by simp; linarith) (by simp; linarith)
          (by exact_mod_cast hs1.ne) hs).2.2
        simpa only [ofReal_im, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] using B)
    refine ⟨_, h, hm, ha, hb, hc.trans ?_⟩
    simp only [Nat.cast_one, mul_one] at hlog ⊢
    have e1 : ‖(1 : ℂ) / (0 - 1)‖ = 1 := by simp
    rw [e1]
    nlinarith [mul_nonneg hC₁.le hnn, mul_nonneg hC₂.le hnn]
  · have A := H₁ N χ h1 2 (by norm_num) (by simp) hL2
    simp only [im_ofNat, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at A
    obtain ⟨h, ha, hb, hc⟩ := exists_regular_part (LFunction χ) (fun _ => 0) _
      (C₁ * Real.log (N * 2)) A.1 continuousAt_const
      han hne (fun h => ⟨norm_sub_two_le (by simp) (by simp) (by simp), h⟩)
      (fun w hw => hw.2)
      (fun w a b c d => ⟨norm_sub_two_le a.le b c, d⟩)
      (fun w hw => hbig w hw.2) A.2.1 (fun s hs0 hs1 hs => by
        have B := (H₁ N χ h1 s (by simp; linarith) (by simp; linarith) hs).2.2
        simpa only [ofReal_im, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] using B)
    refine ⟨_, h, hm, ha, hb, hc.trans ?_⟩
    rw [norm_zero, mul_comm (N : ℝ) 2]
    nlinarith [mul_nonneg hC₁.le hnn, mul_nonneg hC₂.le hnn]

end GlobalTheory.LAtZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientOfFamilyZeroOffEmbedding
section
open GlobalTheory.MomN
open scoped ContDiff

noncomputable section

namespace GlobalTheory.MomEmbed

open MvPolynomial

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem monoJet_eq_listJet {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (m : κ →₀ ℕ) :
    monoJet v G m = ReciprocityTheory.ChartRestriction.G.PullbackSections.lD G 0 (m.toMultiset.toList.map v) := by
  unfold monoJet
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_eq G 0 _ (List.length_map _)]
  congr 1
  funext i
  simp [List.get_eq_getElem]

theorem monoJet_mapDomain {κ ι' : Type} [Fintype κ] [Fintype ι'] (e : κ ↪ ι') (w : κ → V) (u : ι' → V)
    (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (hw : ∀ i, u (e i) = w i) (m : κ →₀ ℕ) :
    monoJet u G (Finsupp.mapDomain e m) = monoJet w G m := by
  rw [monoJet_eq_listJet, monoJet_eq_listJet]
  apply ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_perm (hG.contDiffAt)
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, ← Multiset.map_coe, Multiset.coe_toList,
    Multiset.coe_toList, ← Finsupp.toMultiset_map m e, Multiset.map_map]
  congr 1
  funext i
  exact hw i

theorem mahler_embed : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι']
    (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ i, u (e i) = w i) →
    (∀ p, p ∉ Set.range e → u p = 0) →
    (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u G k = 0) ∧
    (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → GlobalTheory.MomN.mahler u G k = GlobalTheory.MomN.mahler w G (fun i => k (e i))) := by
  intro V _ _ κ ι' _ _ e w u G hG hw hu
  classical
  constructor
  · rintro k ⟨p, hp, hkp⟩
    simp only [GlobalTheory.MomN.mahler]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hkp
    have hP : (∏ i, C (((k i).factorial : ℂ)⁻¹) * Polynomial.aeval (X i : MvPolynomial ι' ℂ) (descPochhammer ℂ (k i))) =
        X p * (C (((k p).factorial : ℂ)⁻¹) *
          Polynomial.aeval (X p : MvPolynomial ι' ℂ) ((descPochhammer ℂ n).comp (Polynomial.X - 1)) *
          ∏ i ∈ Finset.univ.erase p, C (((k i).factorial : ℂ)⁻¹) *
            Polynomial.aeval (X i : MvPolynomial ι' ℂ) (descPochhammer ℂ (k i))) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p)]
      simp only [hn, descPochhammer_succ_left, map_mul, Polynomial.aeval_X]
      ring
    rw [hP]
    apply Finset.sum_eq_zero
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul'] at hm
    have hpm : p ∈ m.support := by
      by_contra h
      exact hm (if_neg h)
    have hmem : p ∈ m.toMultiset.toList := by
      rw [Multiset.mem_toList]
      simpa using hpm
    obtain ⟨idx, hidx⟩ := List.get_of_mem hmem
    have hz : monoJet u G m = 0 := by
      unfold monoJet
      exact ContinuousMultilinearMap.map_coord_zero _ idx (by
        show u ((Finsupp.toMultiset m).toList.get idx) = 0
        rw [hidx]
        exact hu p hp)
    rw [hz, mul_zero]
  · intro k hk
    simp only [GlobalTheory.MomN.mahler]
    have hprod : (∏ p : ι', C (((k p).factorial : ℂ)⁻¹) *
        Polynomial.aeval (X p : MvPolynomial ι' ℂ) (descPochhammer ℂ (k p))) =
        rename e (∏ i : κ, C (((k (e i)).factorial : ℂ)⁻¹) *
          Polynomial.aeval (X i : MvPolynomial κ ℂ) (descPochhammer ℂ (k (e i)))) := by
      rw [map_prod]
      symm
      apply Fintype.prod_of_injective e e.injective
      · intro b hb
        simp [hk b hb]
      · intro a
        simp [← Polynomial.aeval_algHom_apply, rename_X]
    rw [hprod, MvPolynomial.support_rename_of_injective e.injective,
      Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective e.injective h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_rename_mapDomain _ e.injective, monoJet_mapDomain e w u G hG hw]

end GlobalTheory.MomEmbed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
section
open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

def qPoch (t : ℂ) (m : ℕ) : ℂ := ∏ i ∈ Finset.range m, (1 - t ^ (i + 1))

def qPochInf (t : ℂ) : ℂ := ∏' i : ℕ, (1 - t ^ (i + 1))

def qBinom (t : ℂ) (m k : ℕ) : ℂ := qPoch t m / (qPoch t k * qPoch t (m - k))

def finCoeff (t : ℂ) (n : ℕ) (j : ℤ) : ℂ :=
  if j.natAbs ≤ n then qBinom t (2 * n) ((n : ℤ) + j).toNat else 0

theorem qPoch_tendsto (t : ℂ) (ht : ‖t‖ < 1) :
    Filter.Tendsto (qPoch t) Filter.atTop (nhds (qPochInf t)) ∧ qPochInf t ≠ 0 ∧
      ∀ m, qPoch t m ≠ 0 := by
  have hg : Summable (fun i : ℕ => ‖t‖ * ‖t‖ ^ i) :=
    (summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left ‖t‖
  have hsum : Summable (fun i : ℕ => ‖-(t ^ (i + 1))‖) :=
    hg.congr (fun i => by rw [norm_neg, norm_pow, pow_succ, mul_comm])
  have hne : ∀ i : ℕ, 1 + -(t ^ (i + 1)) ≠ 0 := by
    intro i h
    have h1 : t ^ (i + 1) = 1 := by linear_combination -h
    have h2 : ‖t‖ ^ (i + 1) < 1 := pow_lt_one₀ (norm_nonneg t) ht (by omega)
    rw [← norm_pow, h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hm := multipliable_one_add_of_summable hsum
  have h0 := tprod_one_add_ne_zero_of_summable hne hsum
  simp only [← sub_eq_add_neg] at hm h0 hne
  refine ⟨hm.hasProd.tendsto_prod_nat, h0, fun m => Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)⟩

theorem tpFactor_eq (τ : ℍ) (z : ℂ) (k : ℕ) :
    GlobalTheory.ThetaWeberRoad.tpFactor τ z k = (1 - (cexp (π * I * (τ : ℂ)) ^ 2) ^ (k + 1)) *
      ((1 + cexp (2 * π * I * z) * cexp (π * I * (τ : ℂ)) ^ (2 * k + 1)) *
        (1 + (cexp (2 * π * I * z))⁻¹ * cexp (π * I * (τ : ℂ)) ^ (2 * k + 1))) := by
  unfold GlobalTheory.ThetaWeberRoad.tpFactor
  rw [← pow_mul, ← exp_nat_mul, ← exp_nat_mul, ← exp_neg, ← exp_add, ← exp_add]
  rw [mul_assoc]
  congr 3 <;> push_cast <;> ring_nf

theorem jacobiTheta₂_term_eq_zpow (τ z : ℂ) (j : ℤ) :
    jacobiTheta₂_term j z τ = cexp (2 * π * I * z) ^ j * cexp (π * I * τ) ^ (j ^ 2) := by
  unfold jacobiTheta₂_term
  rw [← exp_int_mul, ← exp_int_mul, ← exp_add]
  congr 1
  push_cast
  ring

theorem norm_exp_pi_I_lt_one (τ : ℂ) (hτ : 0 < τ.im) : ‖cexp (π * I * τ)‖ < 1 := by
  rw [norm_exp, ← Real.exp_zero, Real.exp_lt_exp]
  have : (π * I * τ).re = -(π * τ.im) := by simp
  rw [this]
  have := Real.pi_pos
  nlinarith

theorem multipliable_tpFactor (τ : ℍ) (z : ℂ) :
    Multipliable (GlobalTheory.ThetaWeberRoad.tpFactor τ z) := by
  set s := cexp (π * I * (τ : ℂ)) with hs
  set x := cexp (2 * π * I * z) with hx
  have hs1 : ‖s‖ < 1 := norm_exp_pi_I_lt_one (τ : ℂ) τ.2
  have g : Summable (fun k : ℕ => (‖s‖ ^ 2) ^ k) :=
    summable_geometric_of_lt_one (by positivity) (by nlinarith [norm_nonneg s])
  have h1 : Multipliable (fun k : ℕ => 1 + -((s ^ 2) ^ (k + 1))) :=
    multipliable_one_add_of_summable ((g.mul_left (‖s‖ ^ 2)).congr (fun k => by
      rw [norm_neg, norm_pow, norm_pow, pow_succ]; ring))
  have h2 : Multipliable (fun k : ℕ => 1 + x * s ^ (2 * k + 1)) :=
    multipliable_one_add_of_summable ((g.mul_left (‖x‖ * ‖s‖)).congr (fun k => by
      rw [norm_mul, norm_pow]; ring))
  have h3 : Multipliable (fun k : ℕ => 1 + x⁻¹ * s ^ (2 * k + 1)) :=
    multipliable_one_add_of_summable ((g.mul_left (‖x⁻¹‖ * ‖s‖)).congr (fun k => by
      rw [norm_mul, norm_pow]; ring))
  convert h1.mul (h2.mul h3) using 1
  funext k
  rw [tpFactor_eq]
  ring

end GlobalTheory.JacobiTriple
end
end

