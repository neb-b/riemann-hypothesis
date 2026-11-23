module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IsogenyP
section
noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F
namespace IsogenyPAux

lemma P_local (L : PeriodPair) (ω : ℂ) (hω : ω ∈ L.lattice) (w : ℂ) :
    L.weierstrassP w = L.weierstrassPExcept 0 (w - ω) + 1 / (w - ω) ^ 2 := by
  have h1 := L.weierstrassPExcept_add (0 : L.lattice) (w - ω)
  have h2 := L.weierstrassP_sub_coe w ⟨ω, hω⟩
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h1 h2
  rw [← h2, ← h1]

lemma analyticAt_P (L : PeriodPair) (a b z : ℂ) (hz : a * z + b ∉ L.lattice) :
    AnalyticAt ℂ (fun w => L.weierstrassP (a * w + b)) z :=
  AnalyticAt.fun_comp (f := fun w : ℂ => a * w + b) (g := L.weierstrassP)
    (L.analyticOnNhd_weierstrassP _ hz) (by fun_prop)

lemma analyticAt_PExcept (L : PeriodPair) (a z : ℂ) :
    AnalyticAt ℂ (fun w => L.weierstrassPExcept 0 (a * (w - z))) z := by
  refine AnalyticAt.fun_comp (f := fun w : ℂ => a * (w - z)) (g := L.weierstrassPExcept 0) ?_
    (by fun_prop)
  simpa using L.analyticAt_weierstrassPExcept 0

lemma eventually_notMem (L : PeriodPair) (α z : ℂ) (hα : α ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z, α * w ∉ L.lattice := by
  have h1 : ∀ᶠ w in 𝓝 z, α * w ∈ ((L.lattice : Set ℂ) \ {α * z})ᶜ :=
    ((continuous_const.mul continuous_id).tendsto z).eventually
      (L.compl_lattice_sdiff_singleton_mem_nhds (α * z))
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hne hmem
  refine hw ⟨hmem, ?_⟩
  simpa [hα] using hne

lemma ext_at (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hst : MulStable L α)
    (h1 : ∀ P ∈ T, α * P ∈ L.lattice)
    (h2 : ∀ P ∈ T, ∀ Q ∈ T, P - Q ∈ L.lattice → P = Q)
    (z₀ P' : ℂ) (hP' : P' ∈ T) (hz : z₀ + P' ∈ L.lattice) :
    AnalyticAt ℂ (fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P)) z₀ ∧
    (fun w => α ^ 2 * L.weierstrassP (α * w) - ∑ P ∈ T, L.weierstrassP (w + P)) =ᶠ[𝓝[≠] z₀]
      (fun w => α ^ 2 * L.weierstrassPExcept 0 (α * (w - z₀))
        - L.weierstrassPExcept 0 (1 * (w - z₀)) - ∑ P ∈ T.erase P', L.weierstrassP (1 * w + P)) := by
  constructor
  · refine ((analyticAt_const.mul (analyticAt_PExcept L α z₀)).sub (analyticAt_PExcept L 1 z₀)).sub ?_
    refine Finset.analyticAt_fun_sum _ fun P hP => analyticAt_P L 1 P z₀ ?_
    intro hmem
    rw [one_mul] at hmem
    refine (Finset.mem_erase.1 hP).1 (h2 P (Finset.mem_erase.1 hP).2 P' hP' ?_)
    have := L.lattice.sub_mem hmem hz
    simpa using this
  · have hαz : α * z₀ ∈ L.lattice := by
      have := L.lattice.sub_mem (hst _ hz) (h1 P' hP')
      have e : α * (z₀ + P') - α * P' = α * z₀ := by ring
      rwa [e] at this
    filter_upwards [self_mem_nhdsWithin] with w hne
    have hne' : w - z₀ ≠ 0 := sub_ne_zero.2 hne
    rw [← Finset.add_sum_erase T _ hP', P_local L (α * z₀) hαz (α * w),
      P_local L (z₀ + P') hz (w + P')]
    have e1 : α * w - α * z₀ = α * (w - z₀) := by ring
    have e2 : w + P' - (z₀ + P') = w - z₀ := by ring
    rw [e1, e2]
    simp only [one_mul]
    field_simp
    ring

end IsogenyPAux

open IsogenyPAux

theorem isogenyWeierstrassP_of_ellipticNoPole (hN : EllipticNoPole) : IsogenyP := by
  intro L α S hα hst hS z hz
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have h0S : (0 : ℂ) ∉ S := fun h => (hS1 0 h).2 L.lattice.zero_mem
  set T : Finset ℂ := insert 0 S with hT
  have h1 : ∀ P ∈ T, α * P ∈ L.lattice := by
    intro P hP
    rcases Finset.mem_insert.1 hP with rfl | hP
    · simp
    · exact (hS1 P hP).1
  have h2 : ∀ P ∈ T, ∀ Q ∈ T, P - Q ∈ L.lattice → P = Q := by
    intro P hP Q hQ hPQ
    rcases Finset.mem_insert.1 hP with rfl | hP <;> rcases Finset.mem_insert.1 hQ with rfl | hQ
    · rfl
    · exact absurd (by simpa using hPQ) (hS1 Q hQ).2
    · exact absurd (by simpa using hPQ) (hS1 P hP).2
    · exact hS2 P hP Q hQ hPQ
  have h3 : ∀ z₀, α * z₀ ∈ L.lattice → ∃ P ∈ T, z₀ + P ∈ L.lattice := by
    intro z₀ hz₀
    by_cases hm : z₀ ∈ L.lattice
    · exact ⟨0, Finset.mem_insert_self _ _, by simpa using hm⟩
    · obtain ⟨P, hP, hPz⟩ := hS3 (-z₀) (by simpa using L.lattice.neg_mem hz₀)
        (fun h => hm (by simpa using L.lattice.neg_mem h))
      refine ⟨P, Finset.mem_insert_of_mem hP, ?_⟩
      have := L.lattice.neg_mem hPz
      have e : -(-z₀ - P) = z₀ + P := by ring
      rwa [e] at this
  set f : ℂ → ℂ := fun w => α ^ 2 * L.weierstrassP (α * w) - ∑ P ∈ T, L.weierstrassP (w + P) with hf

  have han : ∀ z₀, α * z₀ ∉ L.lattice → AnalyticAt ℂ f z₀ := by
    intro z₀ hz₀
    have a1 : AnalyticAt ℂ (fun w => L.weierstrassP (α * w)) z₀ := by
      simpa using analyticAt_P L α 0 z₀ (by simpa using hz₀)
    refine (analyticAt_const.mul a1).sub (Finset.analyticAt_fun_sum _ fun P hP => ?_)
    have := analyticAt_P L 1 P z₀ (by
      intro hmem
      rw [one_mul] at hmem
      apply hz₀
      have := L.lattice.sub_mem (hst _ hmem) (h1 P hP)
      have e : α * (z₀ + P) - α * P = α * z₀ := by ring
      rwa [e] at this)
    simpa using this
  have hext : ∀ z₀, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
    intro z₀
    by_cases hz₀ : α * z₀ ∈ L.lattice
    · obtain ⟨P', hP', hzP⟩ := h3 z₀ hz₀
      exact ⟨_, ext_at L α T hα hst h1 h2 z₀ P' hP' hzP⟩
    · exact ⟨f, han z₀ hz₀, EventuallyEq.rfl⟩
  have hmer : ∀ z, MeromorphicAt f z := by
    intro z
    obtain ⟨g, hg, hfg⟩ := hext z
    exact hg.meromorphicAt.congr hfg.symm
  have hord : ∀ z, 0 ≤ meromorphicOrderAt f z := fun z =>
    (hmer z).meromorphicOrderAt_nonneg_iff.2 (hext z)
  have hper : IsPeriodic L f := by
    intro ω hω w
    simp only [hf]
    have e1 : α * (w + ω) = α * w + α * ω := by ring
    rw [e1, L.weierstrassP_add_coe (α * w) ⟨α * ω, hst ω hω⟩]
    congr 1
    refine Finset.sum_congr rfl fun P _ => ?_
    have e2 : w + ω + P = w + P + ω := by ring
    rw [e2, L.weierstrassP_add_coe (w + P) ⟨ω, hω⟩]
  obtain ⟨c, hc⟩ := hN L f hmer hper hord

  have hc0 : c = -∑ P ∈ S, L.weierstrassP P := by
    obtain ⟨ha, he⟩ := ext_at L α T hα hst h1 h2 0 0 (Finset.mem_insert_self _ _) (by simp)
    have hev : (fun _ : ℂ => c) =ᶠ[𝓝[≠] 0] f := by
      filter_upwards [eventually_notMem L α 0 hα] with w hw
      exact (hc w (han w hw).continuousAt).symm
    have := Elliptic.eq_of_eventuallyEq_nhdsNE continuousAt_const ha.continuousAt (hev.trans he)
    rw [this, hT, Finset.erase_insert h0S]
    simp
  have hfz := hc z (han z hz).continuousAt
  rw [hc0] at hfz
  simp only [hf, hT, Finset.sum_insert h0S, add_zero] at hfz
  rw [Finset.sum_sub_distrib]
  linear_combination hfz

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassPSecondDerivative
section
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter

namespace Formalism.L2.Th1.F
namespace HalfPeriodDerivative

lemma hasDerivAt_P (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have h := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  rwa [L.deriv_weierstrassP] at h

lemma isOpen_compl (L : PeriodPair) : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl

lemma isPreconnected_compl (L : PeriodPair) : IsPreconnected ((L.lattice : Set ℂ)ᶜ) := by
  have hc : (L.lattice : Set ℂ).Countable := by
    have : Countable L.lattice := L.latticeEquivProd.toEquiv.injective.countable
    exact Set.to_countable _
  exact (hc.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected

lemma derivWeierstrassP_not_eventually_zero (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    ¬ ∀ᶠ w in 𝓝 z, L.derivWeierstrassP w = 0 := by
  intro h
  have h0 : Set.EqOn L.derivWeierstrassP 0 (L.lattice : Set ℂ)ᶜ :=
    L.analyticOnNhd_derivWeierstrassP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_compl L) hz h
  obtain ⟨c, hc⟩ : ∃ c, ∀ w ∈ (L.lattice : Set ℂ)ᶜ, L.weierstrassP w = c :=
    (isOpen_compl L).exists_is_const_of_deriv_eq_zero (isPreconnected_compl L)
      L.differentiableOn_weierstrassP (fun w hw => by rw [L.deriv_weierstrassP]; exact h0 hw)
  have h1 : L.weierstrassP =ᶠ[𝓝[≠] 0] fun _ => c := by
    have h2 : ((L.lattice : Set ℂ) \ {0})ᶜ ∈ 𝓝[≠] (0 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0)
    filter_upwards [h2, self_mem_nhdsWithin] with w hw hw0
    exact hc w (fun hwL => hw ⟨hwL, hw0⟩)
  have h3 := meromorphicOrderAt_congr h1
  rw [L.order_weierstrassP 0 (zero_mem _)] at h3
  classical
  rw [meromorphicOrderAt_const] at h3
  split_ifs at h3
  · exact absurd h3 (by simp)
  · exact absurd h3 (by decide)

lemma derivP_half (L : PeriodPair) {t : ℂ} (h2 : 2 * t ∈ L.lattice) : L.derivWeierstrassP t = 0 := by
  have h := L.derivWeierstrassP_sub_coe t ⟨2 * t, h2⟩
  have e : t - 2 * t = -t := by ring
  simp only [e, L.derivWeierstrassP_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

lemma prod_const (ha : SigmaAdd) (hq : SigmaQuasi) (hz : SigmaZero) (L : PeriodPair) {t z : ℂ}
    (ht : t ∉ L.lattice) (h2 : 2 * t ∈ L.lattice) (hzL : z ∉ L.lattice) (hzt : z + t ∉ L.lattice) :
    (L.weierstrassP (z + t) - L.weierstrassP t) * (L.weierstrassP z - L.weierstrassP t)
      * wSigma L t ^ 4 = Complex.exp (wEta L (2 * t) * t) := by
  have a1 := ha L (z + t) t hzt ht
  have a2 := ha L z t hzL ht
  have q1 := hq L (2 * t) z h2
  have q2 := hq L (2 * t) (z - t) h2
  have e1 : z + t + t = z + 2 * t := by ring
  have e2 : z + t - t = z := by ring
  have e3 : z - t + 2 * t = z + t := by ring
  have e4 : z + 2 * t / 2 = z + t := by ring
  have e5 : z - t + 2 * t / 2 = z := by ring
  rw [e1, e2] at a1
  rw [e4] at q1
  rw [e3, e5] at q2
  have hs1 : wSigma L z ≠ 0 := mt (hz L z).1 hzL
  have hs2 : wSigma L (z + t) ≠ 0 := mt (hz L (z + t)).1 hzt
  have hE : Complex.exp (wEta L (2 * t) * (z + t))
      = Complex.exp (wEta L (2 * t) * z) * Complex.exp (wEta L (2 * t) * t) := by
    rw [← Complex.exp_add, mul_add]
  have hK : wSigma L (z + t) ^ 2 * wSigma L z ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hs2) (pow_ne_zero _ hs1)
  apply mul_right_cancel₀ hK
  linear_combination (wSigma L z ^ 2 * wSigma L t ^ 2 * (L.weierstrassP z - L.weierstrassP t)) * a1
    - (wSigma L (z + 2 * t) * wSigma L z) * a2
    + (wSigma L z * wSigma L (z + t)) * (wSigma L (z - t) * q1
      - Complex.exp (wEta L (2 * t) * t) * wSigma L z * q2
      + semiChar L (2 * t) * wSigma L z * wSigma L (z - t) * hE)

lemma notMem_of_comb (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) (h2 : 2 * t ∈ L.lattice) (x : ℂ)
    (n m : ℤ) (hx : (n : ℂ) * x + (m : ℂ) * (2 * t) = t) : x ∉ L.lattice := by
  intro h
  apply ht
  rw [← hx, ← zsmul_eq_mul, ← zsmul_eq_mul]
  exact add_mem (zsmul_mem h n) (zsmul_mem h2 m)

end HalfPeriodDerivative

open HalfPeriodDerivative

theorem weierstrass_p_second_derivative : PSecond := by
  intro L z hz
  have hA := L.analyticOnNhd_derivWeierstrassP z hz
  have hd := hA.differentiableAt.hasDerivAt
  set D : ℂ → ℂ := fun w => deriv L.derivWeierstrassP w - (6 * L.weierstrassP w ^ 2 - L.g₂ / 2) with hD
  have hDan : AnalyticAt ℂ D z := by
    have h1 := hA.deriv
    have h2 := L.analyticOnNhd_weierstrassP z hz
    exact h1.sub (((analyticAt_const).mul (h2.pow 2)).sub analyticAt_const)
  have hmem : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := (isOpen_compl L).mem_nhds hz
  have hmul : ∀ᶠ w in 𝓝 z, L.derivWeierstrassP w * D w = 0 := by
    have hev : ∀ᶠ w in 𝓝 z, ∀ᶠ v in 𝓝 w, v ∉ L.lattice := hmem.eventually_nhds
    filter_upwards [hev] with w hw
    have hwL : w ∉ L.lattice := hw.self_of_nhds
    have e1 : HasDerivAt (fun v => L.derivWeierstrassP v ^ 2)
        (2 * L.derivWeierstrassP w * deriv L.derivWeierstrassP w) w := by
      simpa using ((L.analyticOnNhd_derivWeierstrassP w hwL).differentiableAt.hasDerivAt).fun_pow 2
    have e2 : HasDerivAt (fun v => 4 * L.weierstrassP v ^ 3 - L.g₂ * L.weierstrassP v - L.g₃)
        (4 * (3 * L.weierstrassP w ^ 2 * L.derivWeierstrassP w) - L.g₂ * L.derivWeierstrassP w) w := by
      simpa using ((((hasDerivAt_P L hwL).fun_pow 3).const_mul 4).sub
        ((hasDerivAt_P L hwL).const_mul L.g₂)).sub_const L.g₃
    have e3 : (fun v => L.derivWeierstrassP v ^ 2) =ᶠ[𝓝 w]
        fun v => 4 * L.weierstrassP v ^ 3 - L.g₂ * L.weierstrassP v - L.g₃ := by
      filter_upwards [hw] with v hv using L.derivWeierstrassP_sq v hv
    have e4 := (e2.congr_of_eventuallyEq e3).unique e1
    simp only [hD]
    linear_combination (-1 / 2 : ℂ) * e4
  have hD0 : D z = 0 := by
    rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd h (derivWeierstrassP_not_eventually_zero L hz)
    · have h5 : ∀ᶠ w in 𝓝[≠] z, D w = 0 := by
        filter_upwards [h, hmul.filter_mono nhdsWithin_le_nhds] with w h1 h2
        exact (mul_eq_zero.mp h2).resolve_left h1
      have h6 : Tendsto D (𝓝[≠] z) (𝓝 (D z)) := hDan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h7 : Tendsto D (𝓝[≠] z) (𝓝 0) := tendsto_const_nhds.congr' (h5.mono fun w hw => hw.symm)
      exact tendsto_nhds_unique h6 h7
  have : deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
    simpa [hD, sub_eq_zero] using hD0
  rwa [this] at hd

theorem translateProduct_of (h : SgStarAdd) : TranslateProduct := by
  intro L P Q z hQ hzP
  have h1 := h L (z + P) Q hzP hQ
  simp only [opU]
  have e1 : z + (P + Q) = z + P + Q := by ring
  have e2 : z + (P - Q) = z + P - Q := by ring
  rw [e1, e2, zero_add]
  have hexp : Complex.exp (-(Real.pi : ℂ) * herm L z (P + Q) - (Real.pi : ℂ) * herm L (P + Q) (P + Q) / 2)
      * Complex.exp (-(Real.pi : ℂ) * herm L z (P - Q) - (Real.pi : ℂ) * herm L (P - Q) (P - Q) / 2)
      = Complex.exp (-(Real.pi : ℂ) * herm L 0 Q - (Real.pi : ℂ) * herm L Q Q / 2) ^ 2
        * Complex.exp (-(Real.pi : ℂ) * herm L z P - (Real.pi : ℂ) * herm L P P / 2) ^ 2 := by
    rw [← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [herm, map_add (f := _), map_sub]
    push_cast
    ring
  linear_combination
    (Complex.exp (-(Real.pi : ℂ) * herm L z (P + Q) - (Real.pi : ℂ) * herm L (P + Q) (P + Q) / 2)
      * Complex.exp (-(Real.pi : ℂ) * herm L z (P - Q) - (Real.pi : ℂ) * herm L (P - Q) (P - Q) / 2)) * h1
    + (sgStar L Q ^ 2 * sgStar L (z + P) ^ 2 * (L.weierstrassP Q - L.weierstrassP (z + P))) * hexp

theorem halfShift_of (ha : SigmaAdd) (hq : SigmaQuasi) (hz : SigmaZero) (hi : PInjective) :
    HalfShift := by
  intro L t z ht h2 hzL hzt
  have hσt : wSigma L t ≠ 0 := mt (hz L t).1 ht
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = Complex.exp (wEta L (2 * t) * t) / wSigma L t ^ 4 := ⟨_, rfl⟩
  have hκ0 : κ ≠ 0 := by
    rw [hκdef]; exact div_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero _ hσt)
  have hconst : ∀ w, w ∉ L.lattice → w + t ∉ L.lattice →
      (L.weierstrassP (w + t) - L.weierstrassP t) * (L.weierstrassP w - L.weierstrassP t) = κ := by
    intro w hw hwt
    rw [hκdef, eq_div_iff (pow_ne_zero _ hσt)]
    exact prod_const ha hq hz L ht h2 hw hwt
  suffices hκ : κ = 3 * L.weierstrassP t ^ 2 - L.g₂ / 4 by rw [hconst z hzL hzt, hκ]
  have n1 : t / 4 ∉ L.lattice := notMem_of_comb L ht h2 _ 4 0 (by push_cast; ring)
  have n2 : t / 4 + t ∉ L.lattice := notMem_of_comb L ht h2 _ 4 (-2) (by push_cast; ring)
  have n3 : t / 4 + t + t / 4 ∉ L.lattice := notMem_of_comb L ht h2 _ 2 (-1) (by push_cast; ring)
  have hne : L.weierstrassP (t / 4 + t) - L.weierstrassP (t / 4) ≠ 0 := by
    intro h
    rcases (hi L _ _ n2 n1).1 (sub_eq_zero.mp h) with h | h
    · exact ht (by simpa using h)
    · exact n3 h
  have hev : ∀ᶠ w in 𝓝 (t / 4), (L.weierstrassP (w + t) - L.weierstrassP t)
      * (L.weierstrassP w - L.weierstrassP t) = κ := by
    have c1 : ∀ᶠ w in 𝓝 (t / 4), w ∉ L.lattice := (isOpen_compl L).mem_nhds n1
    have c2 : ∀ᶠ w in 𝓝 (t / 4), w + t ∉ L.lattice :=
      ((continuous_id.add continuous_const).tendsto (t / 4)).eventually ((isOpen_compl L).mem_nhds n2)
    filter_upwards [c1, c2] with w h1 h2 using hconst w h1 h2
  have hder : HasDerivAt (fun w => (L.weierstrassP (w + t) - L.weierstrassP t)
      * (L.weierstrassP w - L.weierstrassP t))
      (L.derivWeierstrassP (t / 4 + t) * (L.weierstrassP (t / 4) - L.weierstrassP t)
        + (L.weierstrassP (t / 4 + t) - L.weierstrassP t) * L.derivWeierstrassP (t / 4)) (t / 4) :=
    (((hasDerivAt_P L n2).comp_add_const (t / 4) t).sub_const _).mul
      ((hasDerivAt_P L n1).sub_const _)
  have d := hder.unique ((hasDerivAt_const (t / 4) κ).congr_of_eventuallyEq hev)
  have s1 := L.derivWeierstrassP_sq _ n2
  have s2 := L.derivWeierstrassP_sq _ n1
  have s0 := L.derivWeierstrassP_sq _ ht
  rw [derivP_half L h2] at s0
  have k := hconst _ n1 n2
  have key : κ * (L.weierstrassP (t / 4 + t) - L.weierstrassP (t / 4))
      * (4 * κ - (12 * L.weierstrassP t ^ 2 - L.g₂)) = 0 := by
    rw [← k]
    linear_combination
      (L.derivWeierstrassP (t / 4 + t) * (L.weierstrassP (t / 4) - L.weierstrassP t)
        - (L.weierstrassP (t / 4 + t) - L.weierstrassP t) * L.derivWeierstrassP (t / 4)) * d
      - (L.weierstrassP (t / 4) - L.weierstrassP t) ^ 2 * s1
      + (L.weierstrassP (t / 4 + t) - L.weierstrassP t) ^ 2 * s2
      + ((L.weierstrassP (t / 4) - L.weierstrassP t) ^ 2
        - (L.weierstrassP (t / 4 + t) - L.weierstrassP t) ^ 2) * s0
  have h4 := (mul_eq_zero.mp key).resolve_left (mul_ne_zero hκ0 hne)
  linear_combination (1 / 4 : ℂ) * h4

end Formalism.L2.Th1.F
end
end

