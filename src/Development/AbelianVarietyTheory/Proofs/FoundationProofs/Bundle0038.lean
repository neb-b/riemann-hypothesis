module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetRelOfWeierstrassSystem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffPeriodOneEqOfHasSum
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory Filter Topology
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem hasSum_cuspFunction_of_hasSum {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hs : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ))
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    HasSum (fun m => a m • q ^ m) (cuspFunction 1 f q) := by
  have h1 := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq1 hq0
  let τ : ℍ := ⟨Function.Periodic.invQParam 1 q, h1⟩
  have h2 := Function.Periodic.cuspFunction_eq_of_nonzero 1 (f ∘ ofComplex) hq0
  have h3 : cuspFunction 1 f q = f τ := by
    simpa [cuspFunction, UpperHalfPlane.ofComplex_apply_of_im_pos h1] using h2
  have h4 : Function.Periodic.qParam 1 (τ : ℂ) = q :=
    Function.Periodic.qParam_right_inv one_ne_zero hq0
  rw [h3, ← h4]
  exact hs τ

theorem analyticAt_cuspFunction_of_hasSum {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hs : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) :
    AnalyticAt ℂ (cuspFunction 1 f) 0 := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hrad : 1 ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    have hq0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0
    have hq1 : ‖((r : ℝ) : ℂ)‖ < 1 := by
      have : (r : ℝ) < 1 := by exact_mod_cast hr
      simpa using this
    have ht := (hasSum_cuspFunction_of_hasSum hs hq0 hq1).summable.tendsto_atTop_zero.norm
    refine p.le_radius_of_tendsto (l := 0) ?_
    have ht' : Tendsto (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n) atTop (𝓝 0) := by simpa using ht
    convert ht' using 2 with n
    simp [hp, FormalMultilinearSeries.ofScalars_norm]
  have hpos : 0 < p.radius := lt_of_lt_of_le zero_lt_one hrad
  have hP := p.hasFPowerSeriesOnBall hpos
  have hAn : AnalyticAt ℂ p.sum 0 := hP.analyticAt
  have hne : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → cuspFunction 1 f q = p.sum q := by
    intro q hq0 hq1
    rw [hp, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq a q,
      (hasSum_cuspFunction_of_hasSum hs hq0 hq1).tsum_eq]
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 one_pos
  have hev : ∀ᶠ q in 𝓝[≠] (0 : ℂ), cuspFunction 1 f q = p.sum q := by
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with q hq hq0
    exact hne q hq0 (by simpa using hq)
  have h0 : cuspFunction 1 f 0 = p.sum 0 := by
    have ht : Tendsto (cuspFunction 1 f) (𝓝[≠] 0) (𝓝 (p.sum 0)) :=
      (hAn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun q hq => hq.symm)
    simp only [cuspFunction, Function.Periodic.cuspFunction, Function.update_self]
    refine Tendsto.limUnder_eq ?_
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq0
    simp [cuspFunction, Function.Periodic.cuspFunction, Function.update_of_ne hq0]
  refine hAn.congr ?_
  filter_upwards [hball] with q hq
  rcases eq_or_ne q 0 with rfl | hq0
  · exact h0.symm
  · exact (hne q hq0 (by simpa using hq)).symm

theorem coef_of_hasSum : ∀ (f : ℍ → ℂ) (a : ℕ → ℂ),
    (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) →
      ∀ n, GlobalTheory.Hk.coef f n = a n := by
  intro f a hs n
  have han := analyticAt_cuspFunction_of_hasSum hs
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos han hs).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction 1 f)
      (FormalMultilinearSeries.ofScalars ℂ fun m => coef f m) 0 := by
    simpa [coef, qExpansion_coeff, div_eq_mul_inv, mul_comm] using han.hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · n) (h2.eq_formalMultilinearSeries h1)

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SecondDerivSigmaProductAtZero
section
open Filter Topology PeriodPair

namespace GlobalTheory.JetConj

noncomputable def wr (f : ℂ → ℂ) (z : ℂ) : ℂ := f z * deriv (deriv f) z - deriv f z ^ 2

lemma wr_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : wr f z = wr g z := by
  unfold wr
  rw [h.eq_of_nhds, h.deriv.eq_of_nhds, h.deriv.deriv.eq_of_nhds]

lemma wr_mul {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    wr (fun w => f w * g w) z = wr f z * g z ^ 2 + f z ^ 2 * wr g z := by
  have e : deriv (fun w => f w * g w) =ᶠ[𝓝 z] fun w => deriv f w * g w + f w * deriv g w := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with w a b
    exact (a.differentiableAt.hasDerivAt.fun_mul b.differentiableAt.hasDerivAt).deriv
  have a := hf.differentiableAt.hasDerivAt
  have b := hg.differentiableAt.hasDerivAt
  have a' := hf.deriv.differentiableAt.hasDerivAt
  have b' := hg.deriv.differentiableAt.hasDerivAt
  unfold wr
  rw [e.deriv.eq_of_nhds, e.eq_of_nhds, ((a'.fun_mul b).fun_add (a.fun_mul b')).deriv]
  ring

lemma wr_pow {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (k : ℕ) :
    wr (fun w => f w ^ k) z * f z ^ 2 = k * (f z ^ k) ^ 2 * wr f z := by
  induction k with
  | zero => simp [wr]
  | succ k ih =>
    simp only [pow_succ (n := k)]
    rw [wr_mul (hf.fun_pow k) hf]
    push_cast
    linear_combination f z ^ 2 * ih

lemma wr_affine {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c d z : ℂ) :
    wr (fun w => f (c * w + d)) z = c ^ 2 * wr f (c * z + d) := by
  have key : ∀ {g : ℂ → ℂ}, Differentiable ℂ g →
      deriv (fun w => g (c * w + d)) = fun w => c * deriv g (c * w + d) := by
    intro g hg
    funext w
    have := (hg (c * w + d)).hasDerivAt.comp w (((hasDerivAt_id w).const_mul c).add_const d)
    rw [show (fun w => g (c * w + d)) = g ∘ fun w => c * id w + d from rfl, this.deriv]
    ring
  unfold wr
  rw [key hf, deriv_const_mul_field', key hf.deriv]
  ring

structure IsSigmaLike (L : PeriodPair) (σ : ℂ → ℂ) : Prop where
  diff : Differentiable ℂ σ
  deriv_zero : deriv σ 0 = 1
  zero_iff : ∀ z, σ z = 0 ↔ z ∈ L.lattice
  add : ∀ u v, u ∉ L.lattice → v ∉ L.lattice →
    (℘[L] u - ℘[L] v) * (σ u ^ 2 * σ v ^ 2) = -(σ (u + v) * σ (u - v))

variable {L : PeriodPair} {σ : ℂ → ℂ}

lemma eq_of_eqOn_compl_lattice (L : PeriodPair) {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ z ∉ L.lattice, f z = g z) : f = g :=
  Continuous.ext_on ((countable_periodLattice L).dense_compl ℂ) hf hg h

lemma second_deriv_sigma_product_at_zero (hσ : Differentiable ℂ σ) (a k l : ℂ) :
    deriv (deriv fun v => σ (a + v) * σ (a - v) * k + l * σ v ^ 2) 0 =
      2 * wr σ a * k + l * (2 * (deriv σ 0 ^ 2 + σ 0 * deriv (deriv σ) 0)) := by
  have p : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → ∀ v, HasDerivAt (fun v => g (a + v)) (deriv g (a + v)) v :=
    fun hg v => (hg _).hasDerivAt.comp_const_add a v
  have m : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → ∀ v, HasDerivAt (fun v => g (a - v)) (-deriv g (a - v)) v :=
    fun hg v => (hg _).hasDerivAt.comp_const_sub a v
  have e : (deriv fun v => σ (a + v) * σ (a - v) * k + l * σ v ^ 2) = fun v =>
      (deriv σ (a + v) * σ (a - v) - σ (a + v) * deriv σ (a - v)) * k + l * (2 * (σ v * deriv σ v)) := by
    funext v
    rw [((((p hσ v).fun_mul (m hσ v)).mul_const k).fun_add
      (((hσ v).hasDerivAt.fun_pow 2).const_mul l)).deriv]
    simp
    ring
  rw [e, (((((p hσ.deriv 0).fun_mul (m hσ 0)).fun_sub ((p hσ 0).fun_mul (m hσ.deriv 0))).mul_const k).fun_add
    ((((hσ 0).hasDerivAt.fun_mul (hσ.deriv 0).hasDerivAt).const_mul 2).const_mul l)).deriv]
  simp only [wr, add_zero, sub_zero]
  ring

lemma IsSigmaLike.add_wr (H : IsSigmaLike L σ) (a : ℂ) {b : ℂ} (hb : b ∉ L.lattice) :
    σ (a + b) * σ (a - b) = wr σ a * σ b ^ 2 - wr σ b * σ a ^ 2 := by
  have hσ := H.diff
  have hc := hσ.continuous
  have h1 := hσ.deriv.continuous
  have h2 := hσ.deriv.deriv.continuous
  refine congrFun (eq_of_eqOn_compl_lattice L (f := fun a => σ (a + b) * σ (a - b))
    (g := fun a => wr σ a * σ b ^ 2 - wr σ b * σ a ^ 2) (by fun_prop) (by unfold wr; fun_prop) ?_) a
  intro a ha
  have e : (fun v => σ (a + v) * σ (a - v) * σ b ^ 2 + (℘[L] a * (σ a ^ 2 * σ b ^ 2)) * σ v ^ 2) =
      fun v => σ (b + v) * σ (b - v) * σ a ^ 2 + (℘[L] b * (σ a ^ 2 * σ b ^ 2)) * σ v ^ 2 := by
    refine eq_of_eqOn_compl_lattice L (by fun_prop) (by fun_prop) fun v hv => ?_
    linear_combination σ b ^ 2 * H.add a v ha hv - σ a ^ 2 * H.add b v hb hv
  have e2 := congrArg (fun f => deriv (deriv f) 0) e
  simp only [second_deriv_sigma_product_at_zero hσ, H.deriv_zero, (H.zero_iff 0).2 (zero_mem _)] at e2
  linear_combination H.add a b ha hb - e2 / 2

lemma IsSigmaLike.double (H : IsSigmaLike L σ) {u : ℂ} (hu : u ∉ L.lattice) :
    σ (u + u) = -℘'[L] u * σ u ^ 4 := by
  have hσ := H.diff
  have e : (fun v => (℘[L] u - ℘[L] v) * (σ u ^ 2 * σ v ^ 2)) =ᶠ[𝓝 u] fun v => -(σ (u + v) * σ (u - v)) := by
    filter_upwards [eventually_notMem_periodLattice L hu] with v hv using H.add u v hu hv
  have d1 := ((hasDerivAt_weierstrassP L hu).const_sub (℘[L] u)).fun_mul
    (((hσ u).hasDerivAt.fun_pow 2).const_mul (σ u ^ 2))
  have d2 := (((hσ _).hasDerivAt.comp_const_add u u).fun_mul
    ((hσ _).hasDerivAt.comp_const_sub u u)).fun_neg
  have := d1.unique (d2.congr_of_eventuallyEq e)
  simp only [sub_self, H.deriv_zero, (H.zero_iff 0).2 (zero_mem _)] at this
  linear_combination -this

noncomputable def divQuot (σ : ℂ → ℂ) (u : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  σ (n * z + n * u) / σ (z + u) ^ (n ^ 2)

lemma IsSigmaLike.analyticAt_divQuot (H : IsSigmaLike L σ) {u z : ℂ} (hz : z + u ∉ L.lattice) (n : ℕ) :
    AnalyticAt ℂ (divQuot σ u n) z := by
  have hσ := H.diff
  have a : Differentiable ℂ fun z => σ (n * z + n * u) := by fun_prop
  have b : Differentiable ℂ fun z => σ (z + u) ^ (n ^ 2) := by fun_prop
  exact (a.analyticAt z).fun_div (b.analyticAt z) (pow_ne_zero _ (mt (H.zero_iff _).1 hz))

lemma eventually_add_notMem (L : PeriodPair) {u z : ℂ} (hz : z + u ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, w + u ∉ L.lattice :=
  (continuous_add_const u).continuousAt.eventually (eventually_notMem_periodLattice L hz)

lemma IsSigmaLike.divQuot_rec (H : IsSigmaLike L σ) {u z : ℂ} (hz : z + u ∉ L.lattice) (n : ℕ) :
    divQuot σ u (n + 2) z * (((n + 1 : ℕ) : ℂ) ^ 2 * divQuot σ u n z) = wr (divQuot σ u (n + 1)) z := by
  have hσ := H.diff
  have h0 : σ (z + u) ≠ 0 := mt (H.zero_iff _).1 hz
  have b : Differentiable ℂ fun z => σ (z + u) := by fun_prop
  have e : (fun w => σ ((n + 1 : ℕ) * w + (n + 1 : ℕ) * u)) =ᶠ[𝓝 z]
      fun w => divQuot σ u (n + 1) w * σ (w + u) ^ ((n + 1) ^ 2) := by
    filter_upwards [eventually_add_notMem L hz] with w hw
    rw [divQuot, div_mul_cancel₀ _ (pow_ne_zero _ (mt (H.zero_iff _).1 hw))]
  have e1 := wr_congr e
  rw [wr_affine hσ, wr_mul (H.analyticAt_divQuot hz _) ((b.analyticAt z).fun_pow _)] at e1
  have e2 := wr_pow (b.analyticAt z) ((n + 1) ^ 2)
  have e3 := wr_affine hσ 1 u z
  simp only [one_mul, one_pow] at e3
  rw [e3] at e2
  have e4 := H.add_wr ((n + 1 : ℕ) * z + (n + 1 : ℕ) * u) hz
  have e5 := e.eq_of_nhds
  rw [show ((n + 1 : ℕ) : ℂ) * z + (n + 1 : ℕ) * u + (z + u) = (n + 2 : ℕ) * z + (n + 2 : ℕ) * u by
    push_cast; ring, show ((n + 1 : ℕ) : ℂ) * z + (n + 1 : ℕ) * u - (z + u) = n * z + n * u by
    push_cast; ring, e5] at e4
  have e6 : σ (z + u) ^ ((n + 2) ^ 2) * σ (z + u) ^ (n ^ 2) =
      (σ (z + u) ^ ((n + 1) ^ 2)) ^ 2 * σ (z + u) ^ 2 := by ring
  have h7 : σ (z + u) ^ ((n + 1) ^ 2) ≠ 0 := pow_ne_zero _ h0
  rw [divQuot, divQuot, div_mul_eq_mul_div, ← mul_div_assoc, ← mul_div_assoc, div_div, mul_comm (σ (z + u) ^ (n ^ 2)), e6,
    div_eq_iff (mul_ne_zero (pow_ne_zero _ h7) (pow_ne_zero _ h0))]
  push_cast at *
  linear_combination ((n : ℂ) + 1) ^ 2 * e4 + σ (z + u) ^ 2 * e1 + divQuot σ u (n + 1) z ^ 2 * e2

lemma IsSigmaLike.divQuot_ne (H : IsSigmaLike L σ) {u : ℂ} (hu : u ∉ L.lattice) {n : ℕ} (hn : n ≠ 0) :
    ¬ divQuot σ u n =ᶠ[𝓝 0] 0 := by
  intro h
  have hσ := H.diff
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have a : Differentiable ℂ fun z => σ (n * z + n * u) := by fun_prop
  have e : (fun z => σ (n * z + n * u)) =ᶠ[𝓝 0] 0 := by
    filter_upwards [h, eventually_add_notMem L (z := 0) (by simpa using hu)] with w hw hw'
    simpa [divQuot, mt (H.zero_iff _).1 hw'] using hw
  have e2 := (a.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ 0) e (Set.mem_univ (u / n - u))
  simp only [Pi.zero_apply] at e2
  rw [show (n : ℂ) * (u / n - u) + n * u = u by field_simp; ring] at e2
  exact hu ((H.zero_iff _).1 e2)

lemma JetRel.wr {S : Subring (ℂ × ℂ)} {f f' : ℂ → ℂ} (H : JetRel S f f') : JetRel S (wr f) (wr f') :=
  (H.mul H.deriv.deriv).sub (H.deriv.pow 2)

theorem jetRel_divQuot {S : Subring (ℂ × ℂ)} (hS : IsFieldGraph S) {L L' : PeriodPair} {σ σ' : ℂ → ℂ}
    (H : IsSigmaLike L σ) (H' : IsSigmaLike L' σ') {u u' : ℂ} (hu : u ∉ L.lattice) (hu' : u' ∉ L'.lattice)
    (hg : (L.g₂, L'.g₂) ∈ S) (hp : (℘[L] u, ℘[L'] u') ∈ S) (hq : (℘'[L] u, ℘'[L'] u') ∈ S) (n : ℕ) :
    JetRel S (divQuot σ u n) (divQuot σ' u' n) := by
  have z0 : ∀ {L : PeriodPair} {u : ℂ}, u ∉ L.lattice → 0 + u ∉ L.lattice := fun h => by simpa using h
  have c0 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ →
      (fun _ => (0 : ℂ)) =ᶠ[𝓝 0] divQuot σ u 0 := fun H =>
    .of_forall fun z => by simp [divQuot, (H.zero_iff 0).2 (zero_mem _)]
  have c1 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ → u ∉ L.lattice →
      (fun _ => (1 : ℂ)) =ᶠ[𝓝 0] divQuot σ u 1 := fun H hu => by
    filter_upwards [eventually_add_notMem _ (z0 hu)] with w hw
    simp [divQuot, mt (H.zero_iff _).1 hw]
  have c2 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ → u ∉ L.lattice →
      (fun z => 0 - ℘'[L] (z + u)) =ᶠ[𝓝 0] divQuot σ u 2 := @fun L σ u H hu => by
    filter_upwards [eventually_add_notMem _ (z0 hu)] with w hw
    rw [divQuot, show ((2 : ℕ) : ℂ) * w + (2 : ℕ) * u = (w + u) + (w + u) by push_cast; ring, H.double hw]
    have := mt (H.zero_iff _).1 hw
    field_simp
    ring
  have c3 : ∀ {L : PeriodPair} {u : ℂ}, u ∉ L.lattice →
      AnalyticAt ℂ (fun z => ℘'[L] (z + u)) 0 ∧
      (deriv (fun z => ℘[L] (z + u)) =ᶠ[𝓝 0] fun z => ℘'[L] (z + u)) ∧
      (deriv (fun z => ℘'[L] (z + u)) =ᶠ[𝓝 0] fun z => 6 * ℘[L] (z + u) * ℘[L] (z + u) - L.g₂ * (2 : ℂ)⁻¹) :=
    @fun L u hu => by
    refine ⟨(L.analyticOnNhd_derivWeierstrassP _ (z0 hu)).comp (f := (· + u)) (by fun_prop), ?_, ?_⟩
    · filter_upwards [weierstrass_system_add_const L u (z0 hu)] with w hw using hw.1.deriv
    · filter_upwards [weierstrass_system_add_const L u (z0 hu)] with w hw
      rw [hw.2.deriv]; ring
  have hq2 : JetRel S (fun z => ℘'[L] (z + u)) (fun z => ℘'[L'] (z + u')) :=
    jetRel_of_weierstrass_system (pair_mul hg (hS.2 _ _ (pair_natCast S 2)))
      (analyticAt_weierstrassP_add L u (z0 hu)) (analyticAt_weierstrassP_add L' u' (z0 hu'))
      (c3 hu).1 (c3 hu').1 (c3 hu).2.1 (c3 hu').2.1 (c3 hu).2.2 (c3 hu').2.2
      (by simpa using hp) (by simpa using hq)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => exact (JetRel.const S.zero_mem).congr (c0 H) (c0 H')
  | 1 => exact (JetRel.const S.one_mem).congr (c1 H hu) (c1 H' hu')
  | 2 => exact ((JetRel.const S.zero_mem).sub hq2).congr (c2 H hu) (c2 H' hu')
  | n + 3 =>
    have c4 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ → u ∉ L.lattice →
        wr (divQuot σ u (n + 2)) =ᶠ[𝓝 0] fun z =>
          divQuot σ u (n + 3) z * (((n + 2 : ℕ) : ℂ) ^ 2 * divQuot σ u (n + 1) z) := fun H hu => by
      filter_upwards [eventually_add_notMem _ (z0 hu)] with w hw using (H.divQuot_rec hw (n + 1)).symm
    refine JetRel.of_mul hS (H.analyticAt_divQuot (z0 hu) _) (H'.analyticAt_divQuot (z0 hu') _)
      (((JetRel.const (pair_natCast S (n + 2))).pow 2).mul (ih (n + 1) (by omega))) ?_
      ((ih (n + 2) (by omega)).wr.congr (c4 H hu) (c4 H' hu'))
    intro e
    apply H.divQuot_ne hu (n := n + 1) (by omega)
    have hn : ((n + 2 : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n + 2 ≠ 0))
    filter_upwards [e] with w hw using (mul_eq_zero.1 hw).resolve_left hn

end GlobalTheory.JetConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashQExpansionCoeffWidthTransform
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

theorem slash_periodic_comp {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ}
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) (x : SL(2, ℤ)) :
    Function.Periodic ((f ∣[k] x) ∘ ofComplex) (M : ℝ) := by
  have key : ∀ τ : ℍ, (f ∣[k] x) ((M : ℝ) +ᵥ τ) = (f ∣[k] x) τ := by
    intro τ
    have hT : (ModularGroup.T ^ (M : ℤ)) • τ = (M : ℝ) +ᵥ τ := by
      rw [modular_T_zpow_smul]; simp
    have hδ : x * ModularGroup.T ^ (M : ℤ) * x⁻¹ ∈ Γ := by
      have h1 : ModularGroup.T ^ (M : ℤ) ∈ CongruenceSubgroup.Gamma M := by
        simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (M : ℤ) (M : ℤ) dvd_rfl
      exact hΓ ((CongruenceSubgroup.Gamma_normal M).conj_mem _ h1 x)
    have e : (f ∣[k] x) ∣[k] (ModularGroup.T ^ (M : ℤ)) = f ∣[k] x := by
      rw [← SlashAction.slash_mul,
        (inv_mul_cancel_right (x * ModularGroup.T ^ (M : ℤ)) x).symm,
        SlashAction.slash_mul, hf.1 _ hδ]
    have h := congrFun e τ
    have hden : denom (ModularGroup.T ^ (M : ℤ) : SL(2, ℤ)) τ = 1 := by
      rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
    rw [ModularForm.SL_slash_apply (f := f ∣[k] x), hT, hden, one_zpow, mul_one] at h
    exact h
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simp [hw]
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    convert key ⟨w, hw⟩ using 2
    ext
    simp [ofComplex_apply_of_im_pos hw', add_comm]
  · push_neg at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

theorem analyticAt_cuspFunction_slash {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ}
    (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) (x : SL(2, ℤ)) :
    AnalyticAt ℂ (cuspFunction (M : ℝ) (f ∣[k] x)) 0 :=
  analyticAt_cuspFunction_zero (by exact_mod_cast hM) (slash_periodic_comp hΓ hf x)
    (mdiff_slash hf.2.1 k x) (hf.2.2 x)

theorem qParam_one_vadd_eq_exp_mul (M : ℕ) (τ : ℍ) :
    Function.Periodic.qParam (M : ℝ) (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I / M) * Function.Periodic.qParam (M : ℝ) (τ : ℂ) := by
  simp only [Function.Periodic.qParam, coe_vadd, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coeff_unique_of_hasSum {h : ℝ} {g : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hs : ∀ τ : ℍ, HasSum (fun m => c m • Function.Periodic.qParam h (τ : ℂ) ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hs).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

theorem co_transform (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) (hM : 0 < M)
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hf : IsMF Γ k f) :
    (∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (x * ModularGroup.T) n =
        Complex.exp (2 * Real.pi * Complex.I / M) ^ n * co M k f x n) ∧
      (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (γ * x) n = co M k f x n) ∧
      (Odd k → ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (-x) n = -co M k f x n) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨fun x n => ?_, fun γ hγ x n => ?_, fun hk x n => ?_⟩
  · set ζ := Complex.exp (2 * Real.pi * Complex.I / M)
    have happ : ∀ τ : ℍ, (f ∣[k] (x * ModularGroup.T)) τ = (f ∣[k] x) ((1 : ℝ) +ᵥ τ) := by
      intro τ
      rw [slash_mul_apply, modular_T_smul]
      have hden : denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = 1 := by
        rw [ModularGroup.denom_apply]; simp [ModularGroup.T]
      rw [hden, one_zpow, mul_one]
    have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => (ζ ^ m * co M k f x m) •
        Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ m) ((f ∣[k] (x * ModularGroup.T)) τ) := by
      intro τ
      have h := hasSum_qExpansion hM' (slash_periodic_comp hΓ hf x) (mdiff_slash hf.2.1 k x)
        (hf.2.2 x) ((1 : ℝ) +ᵥ τ)
      rw [happ]
      convert h using 1
      funext m
      rw [qParam_one_vadd_eq_exp_mul, co, smul_eq_mul, smul_eq_mul, mul_pow]
      ring
    exact (coeff_unique_of_hasSum hM'
      (analyticAt_cuspFunction_slash hM hΓ hf (x * ModularGroup.T)) hsum n).symm
  · simp only [co, hf.slash_mul hγ x]
  · simp only [co, slash_neg_of_odd hk f x]
    rw [qExpansion_neg (analyticAt_cuspFunction_slash hM hΓ hf x)]
    simp

end GlobalTheory.OddFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashRatIsBoundedAtGamma1InterGamma0Level
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_finiteIndex_of_pos (N l : ℕ) (hN : 0 < N) (hl : 0 < l) : (lev N l).FiniteIndex := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

theorem isCusp_SL2Z_smul_ratGL (g : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  refine ⟨g • c, ?_⟩
  rw [← Rat.coe_castHom, OnePoint.map_smul]

theorem slash_rat_isBoundedAt :
    ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l → 0 < (g.det : ℚ) →
      ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ, IsCusp c (GlobalTheory.Hk.lev N l) →
        c.IsBoundedAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  intro N l k g hN hl _ f c hc
  haveI := lev_finiteIndex_of_pos N l hN hl
  have key : IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) (GlobalTheory.Hk.lev N l) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact isCusp_SL2Z_smul_ratGL g hc
  exact OnePoint.IsBoundedAt.smul_iff.1 (f.bdd_at_cusps' key)

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashSubQExpansionPartialSumIsBigO
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem slash_sub_partialSum_isBigO : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M →
    CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → ∀ x : SL(2, ℤ),
    (fun τ : ℍ => (f ∣[k] x) τ - ∑ n ∈ Finset.range M, co M k f x n * Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ n)
      =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  intro M Γ k f hM hΓ hf x
  haveI : NeZero M := ⟨hM.ne'⟩
  have hg : IsMF (CongruenceSubgroup.Gamma M) k (f ∣[k] x) := by
    refine ⟨fun γ hγ => ?_, mdiff_slash hf.2.1 k x, fun y => ?_⟩
    · have h1 : x * γ * x⁻¹ ∈ Γ := hΓ ((CongruenceSubgroup.Gamma_normal M).conj_mem γ hγ x)
      rw [← SlashAction.slash_mul, show x * γ = (x * γ * x⁻¹) * x by group]
      exact hf.slash_mul h1 x
    · rw [← SlashAction.slash_mul]; exact hf.2.2 _
  have hper : (M : ℝ) ∈ ((CongruenceSubgroup.Gamma M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma]; exact AddSubgroup.mem_zmultiples _
  have hperiodic : Function.Periodic ((f ∣[k] x) ∘ ofComplex) (M : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex hg.toMF hper
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum := hasSum_qExpansion hMpos hperiodic hg.2.1 (hf.2.2 x)
  have ha := analyticAt_cuspFunction_zero hMpos hperiodic hg.2.1 (hf.2.2 x)
  have hps := hasFPowerSeriesOnBall_cuspFunction hMpos ha hsum
  have hbig := (hps.hasFPowerSeriesAt.isBigO_sub_partialSum_pow M).comp_tendsto (qParam_tendsto_atImInfty hMpos)
  refine hbig.congr (fun τ => ?_) (fun τ => ?_)
  · simp only [Function.comp_apply, zero_add, FormalMultilinearSeries.partialSum,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, co]
    rw [eq_cuspFunction τ (by positivity) hperiodic]
  · simp only [Function.comp_apply, Function.Periodic.norm_qParam, coe_im]
    rw [← Real.exp_nat_mul]; congr 1; field_simp

end GlobalTheory.OddFrame
end

