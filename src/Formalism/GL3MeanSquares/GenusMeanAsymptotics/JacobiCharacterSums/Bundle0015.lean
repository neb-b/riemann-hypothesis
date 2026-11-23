module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0013
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0001
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0003

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHCauchy
section
open Finset Complex Classical Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhc_removable (Z : Finset ℂ) : ∀ (U : Set ℂ) (G : ℂ → ℂ) (C : ℝ), IsOpen U →
    DifferentiableOn ℂ G (U \ (Z : Set ℂ)) → (∀ z ∈ U \ (Z : Set ℂ), ‖G z‖ ≤ C) →
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧ (∀ z ∈ U \ (Z : Set ℂ), H z = G z) ∧
      ∀ z ∈ U, ‖H z‖ ≤ C := by
  induction Z using Finset.induction_on with
  | empty =>
    intro U G C _ hd hb
    exact ⟨G, by simpa using hd, fun _ _ => rfl, by simpa using hb⟩
  | insert a Z ha ih =>
    intro U G C hU hd hb
    have hset : U \ ((insert a Z : Finset ℂ) : Set ℂ) = (U \ {a}) \ (Z : Set ℂ) := by
      ext z
      simp [not_or, and_assoc]
    rw [hset] at hd hb
    obtain ⟨H₁, hH₁d, hH₁e, hH₁b⟩ := ih (U \ {a}) G C (hU.sdiff isClosed_singleton) hd hb
    rw [hset]
    by_cases haU : a ∈ U
    · have hUa : U ∈ 𝓝 a := hU.mem_nhds haU
      have hbd : BddAbove (norm ∘ H₁ '' (U \ {a})) :=
        ⟨C, by rintro _ ⟨z, hz, rfl⟩; exact hH₁b z hz⟩
      have hD := differentiableOn_update_limUnder_of_bddAbove hUa hH₁d hbd
      have hne : ∀ z, z ≠ a → Function.update H₁ a (limUnder (𝓝[≠] a) H₁) z = H₁ z :=
        fun z hz => Function.update_of_ne hz _ _
      refine ⟨_, hD, ?_, ?_⟩
      · intro z hz
        rw [hne z hz.1.2]
        exact hH₁e z hz
      · intro z hz
        by_cases hza : z = a
        · rw [hza]
          have hc := (hD.differentiableAt hUa).continuousAt
          have ht := (hc.norm).tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))
          refine le_of_tendsto ht ?_
          filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hUa] with w hw hwU
          rw [hne w hw]
          exact hH₁b w ⟨hwU, hw⟩
        · rw [hne z hza]
          exact hH₁b z ⟨hz, hza⟩
    · have hUe : U \ {a} = U := Set.sdiff_singleton_eq_self haU
      rw [hUe] at hH₁d hH₁b hH₁e ⊢
      exact ⟨H₁, hH₁d, hH₁e, hH₁b⟩

lemma dhc_iter (c ρ : ℂ) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun z => c / (z - ρ)) s =
      c * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ := by
  have h : (fun z : ℂ => c / (z - ρ)) = fun z => c * (fun z : ℂ => (1 * z - ρ)⁻¹) z := by
    ext z
    simp [div_eq_mul_inv]
  have hk : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
  simp only [one_pow, mul_one, one_mul]
  rw [hk, zpow_neg, zpow_natCast]
  ring

lemma dhc_cauchy (H : ℂ → ℂ) (z₀ s : ℂ) (ϱ C : ℝ) (hϱ : 0 < ϱ)
    (hHd : DifferentiableOn ℂ H (Metric.ball z₀ (2 * ϱ))) (hHb : ∀ z ∈ Metric.ball z₀ (2 * ϱ), ‖H z‖ ≤ C)
    (hs : s ∈ Metric.closedBall z₀ ϱ) (k : ℕ) :
    ‖iteratedDeriv k H s‖ ≤ k.factorial * C / ϱ ^ k := by
  have hcont : ContinuousAt (fun R : ℝ => (k.factorial : ℝ) * C / R ^ k) ϱ :=
    continuousAt_const.div (continuousAt_id.pow k) (pow_pos hϱ k).ne'
  have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio ϱ))
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hϱ] with R hR
  have hsub : Metric.closedBall s R ⊆ Metric.ball z₀ (2 * ϱ) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz hs
    rw [Metric.mem_ball]
    have := dist_triangle z s z₀
    linarith [hR.2]
  exact norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR.1 (hHd.diffContOnCl_ball hsub)
    (fun z hz => hHb z (hsub (Metric.sphere_subset_closedBall hz)))

theorem deuring_heilbronn_cauchy : DHCauchy := by
  intro f z₀ r B hr hB hfd hf0 hfb
  obtain ⟨Z, m, hZ, hm1, -, -, hsum, hbd⟩ := landau_local3 f z₀ r B hr hB hfd hf0 hfb
  refine ⟨Z, m, hZ, hm1, hsum, ?_⟩
  have hfan : ∀ z ∈ Metric.ball z₀ (r / 6), AnalyticAt ℂ f z := fun z hz =>
    (hfd.mono Metric.ball_subset_closedBall).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (by linarith) hz))
  have hnz : ∀ z ∈ Metric.ball z₀ (r / 6) \ (Z : Set ℂ), f z ≠ 0 := fun z hz h0 =>
    hz.2 (Finset.mem_coe.2 ((hZ z).2
      ⟨Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hz.1), h0⟩))
  have hGd : DifferentiableOn ℂ (fun z => deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ))
      (Metric.ball z₀ (r / 6) \ (Z : Set ℂ)) := by
    intro z hz
    have h1 := hfan z hz.1
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (h1.deriv.differentiableAt.div h1.differentiableAt (hnz z hz)).sub ?_
    refine DifferentiableAt.fun_sum (fun ρ hρ => ?_)
    exact (differentiableAt_const _).div (differentiableAt_id.sub_const ρ)
      (sub_ne_zero.2 (fun h => hz.2 (h ▸ Finset.mem_coe.2 hρ)))
  obtain ⟨H, hHd, hHe, hHb⟩ := dhc_removable Z _ _ (72 * Real.log B / r) Metric.isOpen_ball hGd
    (fun z hz => hbd z (Metric.ball_subset_closedBall hz.1) (hnz z hz))
  intro k s hs hfs
  have hsZ : s ∉ (Z : Set ℂ) := fun h => hfs ((hZ s).1 (Finset.mem_coe.1 h)).2
  have hsU : s ∈ Metric.ball z₀ (r / 6) := by
    rw [Metric.mem_closedBall] at hs
    rw [Metric.mem_ball]
    linarith
  have hev : (fun z => -(deriv f z / f z)) =ᶠ[𝓝 s]
      fun z => -(∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) - H z := by
    have hn : Metric.ball z₀ (r / 6) \ (Z : Set ℂ) ∈ 𝓝 s :=
      (Metric.isOpen_ball.sdiff Z.finite_toSet.isClosed).mem_nhds ⟨hsU, hsZ⟩
    filter_upwards [hn] with z hz
    rw [hHe z hz]
    ring
  have hHan : AnalyticAt ℂ H s := hHd.analyticAt (Metric.isOpen_ball.mem_nhds hsU)
  have hcd : ∀ ρ ∈ Z, ContDiffAt ℂ k (fun z => (m ρ : ℂ) / (z - ρ)) s := fun ρ hρ =>
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const)
      (sub_ne_zero.2 (fun h => hsZ (h ▸ Finset.mem_coe.2 hρ)))
  have hkey : ‖iteratedDeriv k H s‖ ≤ k.factorial * (72 * Real.log B / r) / (r / 12) ^ k := by
    have h2 : 2 * (r / 12) = r / 6 := by ring
    exact dhc_cauchy H z₀ s (r / 12) _ (by positivity) (h2 ▸ hHd) (h2 ▸ hHb) hs k
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpm : ((-1 : ℂ) ^ k * (-1) ^ k) = 1 := by rw [← mul_pow]; simp
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_fun_sub (ContDiffAt.neg (ContDiffAt.sum hcd)) hHan.contDiffAt,
    iteratedDeriv_fun_neg, iteratedDeriv_fun_sum hcd]
  simp_rw [dhc_iter]
  have he : (-1 : ℂ) ^ k / (k.factorial : ℂ) *
        (-∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ -
          iteratedDeriv k H s) + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) =
      -((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k H s) := by
    have : ∑ ρ ∈ Z, (m ρ : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ =
        ((-1) ^ k * (k.factorial : ℂ)) * ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [div_eq_mul_inv]
      ring
    rw [this]
    generalize (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)) = S
    field_simp
    linear_combination (-(k.factorial : ℂ) * S) * hpm
  rw [he, norm_neg, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hfr : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  calc 1 / (k.factorial : ℝ) * ‖iteratedDeriv k H s‖
      ≤ 1 / (k.factorial : ℝ) * (k.factorial * (72 * Real.log B / r) / (r / 12) ^ k) := by gcongr
    _ = 72 * Real.log B / r * (12 / r) ^ k := by
      rw [div_pow, div_pow]
      field_simp

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHFinish
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

namespace DHF

theorem logMT_ge_one (M : ℕ) (T : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) : 1 ≤ Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : (6 : ℝ) ≤ M * T := by nlinarith
  have he := Real.exp_one_lt_d9
  have h1 : Real.exp 1 ≤ (M : ℝ) * T := by linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) h1

theorem region_gap : ∃ cR : ℝ, 0 < cR ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T c₁ : ℝ)
    (ρ : ℂ), 3 ≤ M → 2 ≤ T → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 → 0 < c₁ → c₁ ≤ cR →
    1 - c₁ / Real.log ((M : ℝ) * T) < β₁ → IsLZero χ ρ → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    cR / 2 ≤ (1 - ρ.re) * Real.log ((M : ℝ) * T) := by
  obtain ⟨cR, hcR, hZ⟩ := Formalism.ZeroFreeDirichlet.zFRDirichlet
  refine ⟨cR, hcR, ?_⟩
  intro M _ χ₁ χ β₁ T c₁ ρ hM hT2 hχ1ne hLz hc₁0 hc₁ hβ₁ hρ hρim hne
  have hLg1 := logMT_ge_one M T hM hT2
  have hLg0 : 0 < Real.log ((M : ℝ) * T) := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog2M : Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) ≤ Real.log ((M : ℝ) * T) := by
    simp only [Complex.ofReal_im, abs_zero, zero_add]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlog2M0 : 0 < Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) := by
    apply Real.log_pos; simp only [Complex.ofReal_im, abs_zero, zero_add]; nlinarith
  have hreg : InRegion cR M (β₁ : ℂ) := by
    unfold InRegion
    have h1 : c₁ / Real.log ((M : ℝ) * T) ≤ cR / Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) := by
      rw [div_le_div_iff₀ hLg0 hlog2M0]
      have h2 := mul_le_mul_of_nonneg_left hlog2M hc₁0.le
      have h3 := mul_le_mul_of_nonneg_right hc₁ hLg0.le
      linarith only [h2, h3]
    rw [Complex.ofReal_re]; linarith only [h1, hβ₁]
  have hLz' : IsLZero χ₁ (β₁ : ℂ) := ⟨Or.inl hχ1ne, hLz⟩
  have hZ1 := (hZ M χ₁ (β₁ : ℂ) hreg hLz').2.2.2.2
  have hnreg : ¬ InRegion cR M ρ := by
    intro h
    obtain ⟨h1, h2⟩ := hZ1 χ ρ h hρ
    exact hne (Prod.ext h1 h2)
  unfold InRegion at hnreg
  push Not at hnreg
  have hlogρ0 : 0 < Real.log ((M : ℝ) * (|ρ.im| + 2)) := by
    apply Real.log_pos; have := abs_nonneg ρ.im; nlinarith
  have hlogρ : Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) := by
    rw [show (2 : ℝ) * Real.log ((M : ℝ) * T) = Real.log (((M : ℝ) * T) ^ 2) by
      rw [Real.log_pow]; push_cast; ring]
    apply Real.log_le_log (by have := abs_nonneg ρ.im; positivity)
    have : |ρ.im| + 2 ≤ 2 * T := by linarith
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have hMT : (2 : ℝ) ≤ M * T := by nlinarith
    have hMT2 := mul_le_mul_of_nonneg_left hMT (by positivity : (0 : ℝ) ≤ M * T)
    calc (M : ℝ) * (|ρ.im| + 2) ≤ M * (2 * T) := mul_le_mul_of_nonneg_left this hM0
      _ ≤ _ := by rw [sq]; linarith
  have h1 : cR / Real.log ((M : ℝ) * (|ρ.im| + 2)) < 1 - ρ.re := by linarith
  rw [div_lt_iff₀ hlogρ0] at h1
  have hδ0 : 0 < 1 - ρ.re := by
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hlogρ0.le
    linarith
  have := mul_le_mul_of_nonneg_left hlogρ hδ0.le
  linarith

end DHF

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHIneqA
section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

def dhFam (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) : Multiset ℂ :=
  Z.val.bind (fun ρ => Multiset.replicate (m ρ) (s - ρ))

theorem dhFam_mem (Z : Finset ℂ) (m : ℂ → ℕ) (s ρ : ℂ) (h : ρ ∈ Z) (hm : 1 ≤ m ρ) :
    s - ρ ∈ dhFam Z m s := by
  unfold dhFam
  rw [Multiset.mem_bind]
  exact ⟨ρ, h, Multiset.mem_replicate.2 ⟨by omega, rfl⟩⟩

theorem dhFlat (S : Multiset ℂ) : ∃ (N : ℕ) (w : Fin N → ℂ), Finset.univ.val.map w = S := by
  refine ⟨S.toList.length, S.toList.get, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]

theorem dhFlat_sum {β : Type*} [AddCommMonoid β] {N : ℕ} (w : Fin N → ℂ) (S : Multiset ℂ)
    (h : Finset.univ.val.map w = S) (g : ℂ → β) : ∑ i, g (w i) = (S.map g).sum := by
  rw [← h, Multiset.map_map]
  rfl

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHLocalA
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhl_prod_le (M : ℕ) [NeZero M] (s : ℂ) (hs : 0 ≤ s.re) :
    ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ M := by
  rw [norm_prod]
  have h1 : ∀ p ∈ M.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
    have hn : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp'.pos]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      simpa using hs
    calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ ≤ p := by rw [norm_one]; linarith
  calc ∏ p ∈ M.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ ≤ ∏ p ∈ M.primeFactors, (p : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) h1
    _ = ((∏ p ∈ M.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ M := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos M) (Nat.prod_primeFactors_dvd M)

lemma dhl_triv_growth (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.LFunctionTrivChar₁ M s‖ ≤ 4 * M * (1 + ‖s‖) ^ 2 := by
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
  have hs0 := norm_nonneg s
  by_cases h1 : s = 1
  · subst h1
    have := dhl_prod_le M 1 (by simp)
    simp only [Function.update_self]
    have e : ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) = ∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ))) := by
      refine Finset.prod_congr rfl (fun p _ => ?_)
      rw [cpow_neg_one]
    rw [e]
    refine this.trans ?_
    rw [norm_one]
    nlinarith
  · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne h1,
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta h1, norm_mul, norm_mul]
    have hP := dhl_prod_le M s (by linarith)
    have hz := Formalism.ZF.growthBound s (by linarith) h1
    have hpos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
    have hle : ‖s - 1‖ ≤ 1 + ‖s‖ := by
      have := norm_sub_le s 1; rw [norm_one] at this; linarith
    have hb : 1 / s.re ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hz2 : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 4 * (1 + ‖s‖) ^ 2 := by
      calc ‖s - 1‖ * ‖riemannZeta s‖
          ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) := by gcongr
        _ = ‖s - 1‖ + 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by field_simp
        _ ≤ (1 + ‖s‖) + 1 + (1 + ‖s‖) * (‖s‖ * (1 + 2)) := by gcongr
        _ ≤ 4 * (1 + ‖s‖) ^ 2 := by nlinarith
    calc ‖s - 1‖ * (‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * ‖riemannZeta s‖)
        = ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * (‖s - 1‖ * ‖riemannZeta s‖) := by ring
      _ ≤ M * (4 * (1 + ‖s‖) ^ 2) := by gcongr
      _ = 4 * M * (1 + ‖s‖) ^ 2 := by ring

lemma dhl_pole (k : ℕ) (s : ℂ) (hs : s ≠ 1) :
    (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z : ℂ => 1 / (z - 1)) s
      = 1 / (s - 1) ^ (k + 1) := by
  have h := congrFun (iter_deriv_inv_linear_sub k (1 : ℂ) 1) s
  have e : (fun z : ℂ => 1 / (z - 1)) = fun x : ℂ => (1 * x - 1)⁻¹ := by
    funext z; simp
  rw [iteratedDeriv_eq_iterate, e, h]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have e2 : (1 * s - 1) ^ (-1 - (k : ℤ)) = ((s - 1) ^ (k + 1))⁻¹ := by
    rw [one_mul, show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [e2, one_pow]
  have h1 : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow]; simp
  field_simp
  linear_combination h1

lemma dhl_log (K X : ℝ) (hK : 1 ≤ K) (hX : 3 ≤ X) :
    Real.log (K * X ^ 2) ≤ (Real.log K + 2) * Real.log X := by
  have hl : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hk : 0 ≤ Real.log K := Real.log_nonneg hK
  rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
  push_cast
  nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTGlue
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem glue_aux {S A B y η E E' F : ℝ} (h : S ≤ A * y * η * E) (hy : 0 ≤ y) (hη : 0 ≤ η)
    (hE : 0 ≤ E) (hEE : E ≤ E') (hF : 0 ≤ F) (hAB : A ≤ B) (hB : 0 ≤ B) :
    S ≤ B * y * η * (E' + F) := by
  have h1 : A * y * η * E ≤ B * y * η * E := by
    have : 0 ≤ y * η * E := by positivity
    nlinarith
  have h2 : B * y * η * E ≤ B * y * η * (E' + F) := by
    have : 0 ≤ B * y * η := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  linarith

theorem glue_ranges : GlueOf := by
  rintro ⟨cA, c, A, hcA, hc, hA⟩ hB
  obtain ⟨c', A', C₀, hc', hB'⟩ := hB cA hcA
  refine ⟨min c c', max A 0 + max A' 0, C₀, lt_min hc hc', ?_⟩
  intro M _ h8 y hy hC
  have hM : 2 ≤ M := by
    have : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    have := Nat.le_of_dvd this h8
    omega
  have hη : 0 ≤ etaOf M := (etaOf_pos M hM).le
  have hy0 : 0 ≤ y := by linarith
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hA0 : 0 ≤ max A 0 := le_max_right _ _
  have hA0' : 0 ≤ max A' 0 := le_max_right _ _
  by_cases hr : Real.log M ≤ cA * Real.sqrt (Real.log y)
  · have h := hA M h8 y hy hr
    rw [add_comm (Real.exp _)]
    refine glue_aux h hy0 hη (Real.exp_pos _).le ?_ (Real.exp_pos _).le ?_ (by positivity)
    · apply Real.exp_le_exp.mpr
      have : min c c' * Real.sqrt (Real.log y) ≤ c * Real.sqrt (Real.log y) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
      linarith
    · have := le_max_left A 0
      linarith
  · have h := hB' M h8 y hy hC (not_le.mp hr)
    refine glue_aux h hy0 hη (Real.exp_pos _).le ?_ (Real.exp_pos _).le ?_ (by positivity)
    · apply Real.exp_le_exp.mpr
      have h1 : min c c' * Real.log y ≤ c' * Real.log y :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hL
      have h2 : min c c' * Real.log y / Real.log M ≤ c' * Real.log y / Real.log M :=
        div_le_div_of_nonneg_right h1 hlM.le
      linarith
    · have := le_max_left A' 0
      linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

