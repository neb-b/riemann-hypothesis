module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BlocksRel
section
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem ext_mR {g h : GR n} (e : mR g = mR h) : g = h := Subtype.ext (Units.ext e)

def dg (X : Fin n → ℝ) (s : ℝ) : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((Real.exp (s * X j) : ℝ) : ℂ)

theorem dg_mul (X : Fin n → ℝ) (s s' : ℝ) : dg X s * dg X s' = dg X (s + s') := by
  rw [dg, dg, dg, diagonal_mul_diagonal]
  congr 1
  funext j
  rw [← Complex.ofReal_mul, ← Real.exp_add, add_mul]

theorem dg_zero (X : Fin n → ℝ) : dg X 0 = 1 := by
  simp [dg]

theorem isDil_iff {X : Fin n → ℝ} {s : ℝ} {g : GR n} (h : IsDil X s g) :
    mR g = fromBlocks (dg X s) 0 0 (dg X (-s)) := by
  rw [h]
  simp only [dg, neg_mul]

theorem dil_mul {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s s' : ℝ) :
    a (s + s') = a s * a s' := by
  apply ext_mR
  rw [mR_mul, isDil_iff (ha _), isDil_iff (ha _), isDil_iff (ha _), fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, dg_mul, neg_add]

theorem dil_zero {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) : a 0 = 1 := by
  apply ext_mR
  rw [isDil_iff (ha _), mR_one, neg_zero, dg_zero, fromBlocks_one]

theorem dil_up {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s : ℝ) : IsUp (a s) := by
  show toBlocks₂₁ (mR (a s)) = 0
  rw [isDil_iff (ha s), toBlocks_fromBlocks₂₁]

theorem dil_inv {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s : ℝ) : (a s)⁻¹ = a (-s) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← dil_mul ha, add_neg_cancel, dil_zero ha]

theorem up_mul {y g : GR n} (hy : IsUp y) (hg : IsUp g) : IsUp (y * g) := by
  show toBlocks₂₁ (mR (y * g)) = 0
  have hy' : toBlocks₂₁ (mR y) = 0 := hy
  have hg' : toBlocks₂₁ (mR g) = 0 := hg
  rw [mR_mul, ← fromBlocks_toBlocks (mR y), ← fromBlocks_toBlocks (mR g), hy', hg',
    fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp

theorem cont_dil {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) : Continuous a := by
  have hc : Continuous fun s : ℝ => fromBlocks (dg X s) 0 0 (dg X (-s)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        dg, diagonal_apply, Matrix.zero_apply] <;> (try split_ifs) <;> fun_prop
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨hc.congr fun s => (isDil_iff (ha s)).symm, ?_⟩
  refine (hc.comp continuous_neg).congr fun s => ?_
  simp only [Function.comp_apply]
  rw [← isDil_iff (ha (-s)), ← dil_inv ha s]
  rfl

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add]
  rw [← fromBlocks_one, fromBlocks_neg, neg_zero]

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ClmCircleIntegral
section
noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Real

namespace PositivityTheory.Rg.Sw.AbsSt

theorem clm_circleIntegral {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) : L (∮ z in C(c, R), f z) = ∮ z in C(c, R), L (f z) := by
  unfold circleIntegral
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm L hf.out]
  congr 1
  funext θ
  exact L.map_smul _ _

theorem banachHol : BanachHol := by
  intro X _ _ U F hU hF hd
  have hG : Continuous (fun p : U × X => F p.1.1 p.2) :=
    hF.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.2, mem_univ _⟩)
  let K : C(U, C(X, ℂ)) := (⟨_, hG⟩ : C(U × X, ℂ)).curry
  classical
  let Φ : ℂ → C(X, ℂ) := fun z => if h : z ∈ U then K ⟨z, h⟩ else 0
  have hΦ : ∀ z ∈ U, ∀ x, Φ z x = F z x := by
    intro z hz x
    simp [Φ, K, hz]
  have hc : ContinuousOn Φ U := by
    rw [continuousOn_iff_continuous_restrict]
    convert K.continuous using 1
    funext z
    show Φ z = K z
    simp only [Φ, dif_pos z.2, Subtype.coe_eta]
  refine ⟨Φ, ?_, hΦ⟩
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨R, hR0, hRU⟩ : ∃ R > 0, closedBall w R ⊆ U := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU w hw
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  let R' : NNReal := ⟨R, hR0.le⟩
  have hsph : sphere w R ⊆ U := sphere_subset_closedBall.trans hRU
  have hint : CircleIntegrable Φ w R' := (hc.mono hsph).circleIntegrable hR0.le
  have hps := hasFPowerSeriesOn_cauchy_integral hint (show (0 : NNReal) < R' from hR0)
  have heq : Φ =ᶠ[𝓝 w] (fun v => (2 * ↑π * I)⁻¹ • ∮ z in C(w, ↑R'), (z - v)⁻¹ • Φ z) := by
    filter_upwards [ball_mem_nhds w hR0] with v hv
    ext x
    show Φ v x = ((2 * ↑π * I)⁻¹ • ∮ z in C(w, R), (z - v)⁻¹ • Φ z) x
    have ha : ContinuousOn (fun z : ℂ => (z - v)⁻¹) (sphere w R) := by
      apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro z hz h
      have hzv : z = v := sub_eq_zero.mp h
      subst hzv
      rw [mem_sphere] at hz
      rw [mem_ball] at hv
      linarith
    have hcv : ContinuousOn (fun z => (z - v)⁻¹ • Φ z) (sphere w R) :=
      ContinuousOn.smul (f := fun z : ℂ => (z - v)⁻¹) (g := Φ) ha (hc.mono hsph)
    have h1 := clm_circleIntegral (ContinuousMap.evalCLM ℂ x) (hcv.circleIntegrable hR0.le)
    simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply] at h1
    have h2 : (∮ z in C(w, R), (z - v)⁻¹ • Φ z) x = ∮ z in C(w, R), (z - v)⁻¹ • F z x := by
      rw [h1]
      apply circleIntegral.integral_congr hR0.le
      intro z hz
      simp only
      rw [hΦ z (hsph hz) x]
    have h3 := ((hd x).mono hRU).circleIntegral_sub_inv_smul hv
    rw [ContinuousMap.smul_apply, h2, h3, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul,
      hΦ v (hRU (ball_subset_closedBall hv))]
  exact hps.analyticAt.differentiableAt.congr_of_eventuallyEq heq

theorem dslopeFam : DslopeFam := by
  intro X _ _ U s₀ F hU hs hF hd h0
  have hU0 : U ∈ 𝓝 s₀ := hU.mem_nhds hs
  refine ⟨?_, fun x => (differentiableOn_dslope hU0).mpr (hd x)⟩
  rintro ⟨z₀, x₀⟩ hp
  have hz₀ : z₀ ∈ U := hp.1
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x₀
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hF' : ContinuousOn (fun y : ℂ × K => F y.1 y.2) (U ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := banachHol (↥K) U (fun z (y : ↥K) => F z y) hU hF' (fun y => hd y)
  have hD : ContinuousOn (dslope Φ s₀) U := ((differentiableOn_dslope hU0).mpr hΦd).continuousOn
  have hval : ∀ z ∈ U, ∀ y : K, dslope Φ s₀ z y = dslope (fun z => F z y) s₀ z := by
    intro z hz y
    have heqon : EqOn (fun z => F z y) ((ContinuousMap.evalCLM ℂ y) ∘ Φ) U := by
      intro u hu
      simp [hΦ u hu y]
    rw [show dslope Φ s₀ z y = ContinuousMap.evalCLM ℂ y (dslope Φ s₀ z) from rfl,
      ← ContinuousLinearMap.dslope_comp _ _ _ _ (fun _ => (hΦd s₀ hs).differentiableAt hU0)]
    by_cases hzs : z = s₀
    · rw [hzs, dslope_same, dslope_same]
      exact (Filter.eventuallyEq_of_mem hU0 heqon).deriv_eq.symm
    · rw [dslope_of_ne _ hzs, dslope_of_ne _ hzs]
      simp [slope_def_field, hΦ z hz y, hΦ s₀ hs y]
  have hcont : ContinuousOn (fun y : ℂ × X => dslope (fun z => F z y.2) s₀ y.1) (U ×ˢ K) := by
    rw [continuousOn_iff_continuous_restrict]
    have hDr : Continuous (fun q : ↥(U ×ˢ K) => dslope Φ s₀ q.1.1) :=
      hD.comp_continuous (continuous_fst.comp continuous_subtype_val) (fun q => q.2.1)
    have hKr : Continuous (fun q : ↥(U ×ˢ K) => (⟨q.1.2, q.2.2⟩ : K)) :=
      (continuous_snd.comp continuous_subtype_val).subtype_mk _
    convert continuous_eval.comp (hDr.prodMk hKr) using 1
    funext q
    exact (hval q.1.1 q.2.1 ⟨q.1.2, q.2.2⟩).symm
  have hmem : U ×ˢ K ∈ 𝓝[U ×ˢ univ] (z₀, x₀) := by
    have hsub : (U ×ˢ univ) ∩ (univ ×ˢ K) ⊆ U ×ˢ K := fun q hq => ⟨hq.1.1, hq.2.2⟩
    exact mem_of_superset (inter_mem_nhdsWithin _ (prod_mem_nhds univ_mem hKn)) hsub
  exact (hcont (z₀, x₀) ⟨hz₀, mem_of_mem_nhds hKn⟩).mono_of_mem_nhdsWithin hmem

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousEvX
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def ept (x : Fin m → Fin n → ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1

theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (ept x) P := rfl

theorem norm_ept_le (x : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ‖ept x k‖ ≤ ‖x‖ := by
  have h : ‖x k.1 k.2.1‖ ≤ ‖x‖ := (norm_le_pi_norm (x k.1) k.2.1).trans (norm_le_pi_norm x k.1)
  unfold ept
  split_ifs
  · simpa using h
  · exact h

theorem continuous_ept : Continuous (ept : (Fin m → Fin n → ℂ) → _) := by
  refine continuous_pi fun k => ?_
  unfold ept
  split_ifs
  · exact continuous_star.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  · exact (continuous_apply k.2.1).comp (continuous_apply k.1)

theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x :=
  (MvPolynomial.continuous_eval P).comp continuous_ept

theorem poly_bound (P : PX m n) : ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧ ∀ x, ‖evX P x‖ ≤ C * (1 + ‖x‖) ^ k := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun x => by simp [evX_eq]⟩
  | add p q hp hq =>
    obtain ⟨C₁, k₁, h₁, hb₁⟩ := hp
    obtain ⟨C₂, k₂, h₂, hb₂⟩ := hq
    refine ⟨C₁ + C₂, k₁ + k₂, add_nonneg h₁ h₂, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
    have e1 : (1 + ‖x‖) ^ k₁ ≤ (1 + ‖x‖) ^ (k₁ + k₂) := pow_le_pow_right₀ h1 (Nat.le_add_right _ _)
    have e2 : (1 + ‖x‖) ^ k₂ ≤ (1 + ‖x‖) ^ (k₁ + k₂) := pow_le_pow_right₀ h1 (Nat.le_add_left _ _)
    rw [evX_eq, map_add (f := _)]
    calc ‖eval (ept x) p + eval (ept x) q‖ ≤ ‖eval (ept x) p‖ + ‖eval (ept x) q‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + ‖x‖) ^ k₁ + C₂ * (1 + ‖x‖) ^ k₂ := add_le_add (hb₁ x) (hb₂ x)
      _ ≤ C₁ * (1 + ‖x‖) ^ (k₁ + k₂) + C₂ * (1 + ‖x‖) ^ (k₁ + k₂) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 h₁) (mul_le_mul_of_nonneg_left e2 h₂)
      _ = (C₁ + C₂) * (1 + ‖x‖) ^ (k₁ + k₂) := by ring
  | mul_X p i hp =>
    obtain ⟨C, k, h0, hb⟩ := hp
    refine ⟨C, k + 1, h0, fun x => ?_⟩
    rw [evX_eq, map_mul, eval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (hb x) ((norm_ept_le x i).trans (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _)
      (mul_nonneg h0 (pow_nonneg (by positivity) _))

theorem sq_norm_le_sum (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ j, ‖x a j‖ ^ 2 :=
  _root_.UpperTheory.Reformulated.B.Yhb3.main x

theorem decay (k : ℕ) (κ : ℝ) (hκ : 0 < κ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ k * Real.exp (-(κ * s ^ 2)) ≤ C * (1 + s) ^ (-r) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((k : ℝ) + r)
  refine ⟨2 ^ N * (1 + N.factorial / κ ^ N), by positivity, fun s hs => ?_⟩
  have h1 : (1 : ℝ) ≤ 1 + s := le_add_of_nonneg_right hs
  have hpos : 0 < 1 + s := by linarith
  have hE : 0 < Real.exp (-(κ * s ^ 2)) := Real.exp_pos _

  have hA : (1 + s) ^ N ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := by
    rcases le_total s 1 with h | h
    · calc (1 + s) ^ N ≤ 2 ^ N := pow_le_pow_left₀ hpos.le (by linarith) N
        _ ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := le_mul_of_one_le_right (by positivity)
            (le_add_of_nonneg_right (by positivity))
    · have : 1 + s ≤ 2 * s ^ 2 := by nlinarith
      calc (1 + s) ^ N ≤ (2 * s ^ 2) ^ N := pow_le_pow_left₀ hpos.le this N
        _ = 2 ^ N * (s ^ 2) ^ N := by rw [mul_pow]
        _ ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := by nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 2) N]
  have hB : (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) ≤ N.factorial / κ ^ N := by
    have := Real.pow_div_factorial_le_exp (x := κ * s ^ 2) (by positivity) N
    rw [div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by positivity)]
    have e : Real.exp (-(κ * s ^ 2)) * Real.exp (κ * s ^ 2) = 1 := by rw [← Real.exp_add]; simp
    calc (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) * κ ^ N = (κ * s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) := by ring
      _ ≤ (Real.exp (κ * s ^ 2) * N.factorial) * Real.exp (-(κ * s ^ 2)) :=
          mul_le_mul_of_nonneg_right this hE.le
      _ = N.factorial := by rw [mul_comm (Real.exp _), mul_assoc, mul_comm (Real.exp _), e, mul_one]
  have hC : (1 + s) ^ N * Real.exp (-(κ * s ^ 2)) ≤ 2 ^ N * (1 + N.factorial / κ ^ N) := by
    calc (1 + s) ^ N * Real.exp (-(κ * s ^ 2)) ≤ 2 ^ N * (1 + (s ^ 2) ^ N) * Real.exp (-(κ * s ^ 2)) :=
          mul_le_mul_of_nonneg_right hA hE.le
      _ = 2 ^ N * (Real.exp (-(κ * s ^ 2)) + (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2))) := by ring
      _ ≤ 2 ^ N * (1 + N.factorial / κ ^ N) := by
          gcongr
          · exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg s])
  have hR : (1 + s) ^ k * (1 + s) ^ r ≤ (1 + s) ^ N := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 hN
  have hr : (1 + s) ^ r * (1 + s) ^ (-r) = 1 := by
    rw [← Real.rpow_add hpos]; simp
  calc (1 + s) ^ k * Real.exp (-(κ * s ^ 2))
      = ((1 + s) ^ k * (1 + s) ^ r * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) := by
        rw [show ((1 + s) ^ k * (1 + s) ^ r * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) =
          (1 + s) ^ k * Real.exp (-(κ * s ^ 2)) * ((1 + s) ^ r * (1 + s) ^ (-r)) by ring, hr, mul_one]
    _ ≤ ((1 + s) ^ N * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) := by
        gcongr
    _ ≤ (2 ^ N * (1 + N.factorial / κ ^ N)) * (1 + s) ^ (-r) := by gcongr

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMapBis
section
noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_group_lower_left_block : Continuous (fun g : GR n => (mR g).toBlocks₂₁) := by
  exact continuous_mR.matrix_submatrix Sum.inr Sum.inl

theorem continuous_group_lower_right_block : Continuous (fun g : GR n => (mR g).toBlocks₂₂) := by
  exact continuous_mR.matrix_submatrix Sum.inr Sum.inr

theorem continuous_first_cayley_block_map : Continuous (fun g : GR n => u1 (mR g)) := by
  unfold u1
  exact ((continuous_group_lower_left_block (n := n)).const_smul Complex.I).add continuous_group_lower_right_block

theorem continuous_second_cayley_block_map : Continuous (fun g : GR n => u2 (mR g)) := by
  unfold u2
  exact ((continuous_group_lower_left_block (n := n)).const_smul Complex.I).neg.add continuous_group_lower_right_block

theorem continuous_weight_factor (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have hdet : Continuous (fun g : GR n => (mR g).det) := continuous_mR.matrix_det
  have h1 : Continuous (fun g : GR n => (u1 (mR g)).det) := continuous_first_cayley_block_map.matrix_det
  have h2 : Continuous (fun g : GR n => (u2 (mR g)).det) := continuous_second_cayley_block_map.matrix_det
  have hne : ∀ g : GR n, (mR g).det ≠ 0 := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g : GL (Fin n ⊕ Fin n) ℂ))).ne_zero
  show Continuous (fun g : GR n =>
    (mR g).det ^ e * ((u1 (mR g)).det ^ (-(p : ℤ)) * (u2 (mR g)).det ^ (-(q : ℤ))))
  exact (hdet.zpow₀ e fun g => Or.inl (hne g)).mul
    ((h1.zpow₀ _ fun g => Or.inl (hD n g).1).mul (h2.zpow₀ _ fun g => Or.inl (hD n g).2))

theorem continuous_hLoc (hD : CayleyBlocksInvertible) : Continuous (hLoc (n := n)) := by
  unfold hLoc
  exact ((continuous_first_cayley_block_map.matrix_det).norm.pow 2).inv₀ fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hD n g).1)

theorem hLoc_nonneg (g : GR n) : 0 ≤ hLoc g := by
  unfold hLoc
  positivity

theorem hLoc_pos (hD : CayleyBlocksInvertible) (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (hD n g).1) 2)

theorem first_cayley_block_one : u1 (mR (1 : GR n)) = 1 := by
  ext i j
  simp [u1, mR, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem second_cayley_block_one : u2 (mR (1 : GR n)) = 1 := by
  ext i j
  simp [u2, mR, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]

theorem weight_factor_one (p q : ℕ) (e : ℤ) : F0 (n := n) p q e 1 = 1 := by
  simp only [F0, f0, first_cayley_block_one, second_cayley_block_one]
  simp [mR]

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL
section
noncomputable section

open MeasureTheory Set Filter Topology Matrix

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem factorL : FactorL := by
  intro G _ S l C hC hcont hlin hbd
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hl0 : l 0 = 0 := by
    have h := hbd 0 S.zero_mem 0 (by simp)
    simpa using h
  let lS : S →ₗ[ℂ] ℂ :=
    { toFun := fun F => l F.1
      map_add' := fun F₁ F₂ => by
        have h := hlin 1 F₁.1 F₁.2 F₂.1 F₂.2
        simpa using h
      map_smul' := fun a F => by
        have h := hlin a F.1 F.2 0 S.zero_mem
        simpa [hl0] using h }
  let R : S →ₗ[ℂ] C(C, ℂ) :=
    { toFun := fun F => ⟨fun x => F.1 x, (hcont F.1 F.2).comp continuous_subtype_val⟩
      map_add' := fun F₁ F₂ => by
        ext x
        simp
      map_smul' := fun a F => by
        ext x
        simp }
  have hRnorm : ∀ F : S, ‖l F.1‖ ≤ ‖R F‖ := by
    intro F
    apply hbd F.1 F.2
    intro x hx
    exact (R F).norm_coe_le_norm ⟨x, hx⟩
  have hker : LinearMap.ker R ≤ LinearMap.ker lS := by
    intro F hF
    rw [LinearMap.mem_ker] at hF ⊢
    have h := hRnorm F
    rw [hF, norm_zero] at h
    exact norm_le_zero_iff.mp h
  let f : LinearMap.range R →ₗ[ℂ] ℂ :=
    ((LinearMap.ker R).liftQ lS hker).comp
      (R.quotKerEquivRange.symm : LinearMap.range R →ₗ[ℂ] S ⧸ LinearMap.ker R)
  have hf : ∀ F : S, f ⟨R F, LinearMap.mem_range_self R F⟩ = l F.1 := by
    intro F
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl
  have hfb : ∀ v : LinearMap.range R, ‖f v‖ ≤ 1 * ‖v‖ := by
    rintro ⟨v, F, rfl⟩
    rw [hf F, one_mul]
    exact hRnorm F
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range R) (f.mkContinuous 1 hfb)
  refine ⟨g, fun F hFS hF => ?_⟩
  have h1 := hg ⟨R ⟨F, hFS⟩, LinearMap.mem_range_self R _⟩
  rw [LinearMap.mkContinuous_apply, hf] at h1
  exact h1.symm

theorem kRCpt : KRCpt := by
  intro n
  let S : Set (M2 n) := {g | InG g ∧ gᴴ * g = 1}
  have hcl : IsClosed S := by
    show IsClosed ({g : M2 n | InG g} ∩ {g : M2 n | gᴴ * g = 1})
    apply IsClosed.inter
    · exact isClosed_eq
        ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
    · exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hsub : S ⊆ univ.pi (fun _ => univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1)) := by
    intro g hg i _ j _
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu : g ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact hg.2
    exact entry_norm_bound_of_unitary hu i j
  have hcpt : IsCompact S :=
    (isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall (0 : ℂ) 1))).of_isClosed_subset
      hcl hsub
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hcpt
  have hinv : ∀ g : S, g.1 * g.1ᴴ = 1 := fun g => mul_eq_one_comm.mp g.2.2
  let u : S → GL (Fin n ⊕ Fin n) ℂ := fun g => ⟨g.1, g.1ᴴ, hinv g, g.2.2⟩
  have hu : Continuous u :=
    Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩
  let ψ : S → KR n := fun g => ⟨⟨u g, g.2.1⟩, g.2⟩
  have hψ : Continuous ψ := (hu.subtype_mk _).subtype_mk _
  have hsurj : Function.Surjective ψ := by
    intro k
    refine ⟨⟨mR k.1, k.2⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl
  exact Function.Surjective.compactSpace hψ hsurj

end PositivityTheory.Rg.Sw.AbsSt
end
end

