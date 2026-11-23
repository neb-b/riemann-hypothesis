module

public import Formalism.HermitianCurvature.StatementG
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Formalism.HermitianCurvature.StatementSz

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntegralPsiMoving
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem norm_psi (β w : ℂ) : ‖G.psi β w‖ = 1 := by
  unfold G.psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_psi (β : ℂ) : Continuous (G.psi β) := by
  unfold G.psi
  fun_prop

def freq (β w : ℂ) : ℂ := ((2 * Real.pi)⁻¹ : ℝ) • (-(conj (β * w)))

theorem psi_eq_fourierChar (β w z : ℂ) :
    G.psi β (w * z) = ((Real.fourierChar (-⟪z, freq β w⟫_ℝ) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, G.psi, freq, real_inner_smul_right, Complex.inner]
  congr 1
  have hre : (-conj (β * w) * conj z).re = -(β * (w * z)).re := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    ring
  rw [hre]
  push_cast
  field_simp

theorem tendsto_freq (β : ℂ) (hβ : β ≠ 0) : Tendsto (freq β) (cocompact ℂ) (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded, Metric.cobounded_eq_cocompact]
  have hn : ∀ w, ‖freq β w‖ = ((2 * Real.pi)⁻¹ * ‖β‖) * ‖w‖ := by
    intro w
    rw [freq, norm_smul, norm_neg, Complex.norm_conj, norm_mul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  simp_rw [hn]
  exact (tendsto_norm_cocompact_atTop).const_mul_atTop (by positivity)

theorem tendsto_integral_psi (β : ℂ) (hβ : β ≠ 0) (f : ℂ → E) :
    Tendsto (fun w => ∫ z, G.psi β (w * z) • f z) (cocompact ℂ) (𝓝 0) := by
  have RL := (tendsto_integral_exp_inner_smul_cocompact f).comp (tendsto_freq β hβ)
  refine RL.congr fun w => ?_
  simp only [Function.comp_apply]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [psi_eq_fourierChar, Circle.smul_def]

theorem norm_integral_psi_sub_le (β w : ℂ) (f g : ℂ → E) (hf : Integrable f) (hg : Integrable g) :
    ‖(∫ z, G.psi β (w * z) • f z) - ∫ z, G.psi β (w * z) • g z‖ ≤ ∫ z, ‖f z - g z‖ := by
  have hfi : Integrable (fun z => G.psi β (w * z) • f z) :=
    hf.bdd_smul 1 ((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => (norm_psi β _).le)
  have hgi : Integrable (fun z => G.psi β (w * z) • g z) :=
    hg.bdd_smul 1 ((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => (norm_psi β _).le)
  rw [← integral_sub hfi hgi]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) (hf.sub hg).norm (Eventually.of_forall fun z => ?_))
  simp only [← smul_sub, norm_smul, norm_psi, one_mul, le_refl]

theorem tendsto_integral_psi_moving {α : Type} {l : Filter α} (β : ℂ) (hβ : β ≠ 0) (f : α → ℂ → E)
    (f0 : ℂ → E) (hf0 : Integrable f0) (hfi : ∀ᶠ x in l, Integrable (f x))
    (hf : Tendsto (fun x => ∫ z, ‖f x z - f0 z‖) l (𝓝 0)) (w : α → ℂ) (hw : Tendsto w l (cocompact ℂ)) :
    Tendsto (fun x => ∫ z, G.psi β (w x * z) • f x z) l (𝓝 0) := by
  have h0 := (tendsto_integral_psi β hβ f0).comp hw
  rw [← add_zero (0 : E)]
  have hsplit : ∀ᶠ x in l, ∫ z, G.psi β (w x * z) • f x z =
      ((∫ z, G.psi β (w x * z) • f x z) - ∫ z, G.psi β (w x * z) • f0 z) +
        ∫ z, G.psi β (w x * z) • f0 z := by
    filter_upwards with x
    abel
  refine Tendsto.congr' (EventuallyEq.symm hsplit) (Tendsto.add ?_ h0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hf
  filter_upwards [hfi] with x hx
  exact norm_integral_psi_sub_le β (w x) (f x) f0 hx hf0

theorem continuous_integral_psi (β : ℂ) (f : ℂ → E) (hf : Integrable f) :
    Continuous (fun w => ∫ z, G.psi β (w * z) • f z) := by
  refine continuous_of_dominated (bound := fun z => ‖f z‖) (fun w => ?_) (fun w => ?_) hf.norm ?_
  · exact (((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable).smul hf.1
  · exact Eventually.of_forall fun z => by rw [norm_smul, norm_psi, one_mul]
  · exact Eventually.of_forall fun z =>
      ((continuous_psi β).comp (continuous_id.mul continuous_const)).smul continuous_const

theorem tendsto_integral_psi_conv {α : Type} {l : Filter α} (β : ℂ) (f : α → ℂ → E)
    (f0 : ℂ → E) (hf0 : Integrable f0) (hfi : ∀ᶠ x in l, Integrable (f x))
    (hf : Tendsto (fun x => ∫ z, ‖f x z - f0 z‖) l (𝓝 0)) (w : α → ℂ) (σ : ℂ) (hw : Tendsto w l (𝓝 σ)) :
    Tendsto (fun x => ∫ z, G.psi β (w x * z) • f x z) l (𝓝 (∫ z, G.psi β (σ * z) • f0 z)) := by
  have h0 := ((continuous_integral_psi β f0 hf0).tendsto σ).comp hw
  rw [← zero_add (∫ z, G.psi β (σ * z) • f0 z)]
  have hsplit : ∀ᶠ x in l, ∫ z, G.psi β (w x * z) • f x z =
      ((∫ z, G.psi β (w x * z) • f x z) - ∫ z, G.psi β (w x * z) • f0 z) +
        ∫ z, G.psi β (w x * z) • f0 z := by
    filter_upwards with x
    abel
  refine Tendsto.congr' (EventuallyEq.symm hsplit) (Tendsto.add ?_ h0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hf
  filter_upwards [hfi] with x hx
  exact norm_integral_psi_sub_le β (w x) (f x) f0 hx hf0

end

end Formalism.FourierDecayAlt.P.PBK
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.VandermondeRatioHarmonic
section
namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz

lemma b_lt (c : Cfg) (hc : c.Ok) (j : ℕ) (hj : 1 ≤ j) :
    ∀ j' : ℕ, j < j' → j' ≤ c.m → c.b j < c.b j' := by
  intro j' hjj'
  induction j', hjj' using Nat.le_induction with
  | base =>
    intro h
    have := hc.hgap j hj (by omega)
    linarith
  | succ n hn ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hc.hgap n (by omega) (by omega)
    linarith

lemma b_ge_one (c : Cfg) (hc : c.Ok) (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.eq_or_lt_of_le hj with h | h
  · rw [← h]; exact hc.hb1
  · have := b_lt c hc 1 le_rfl j h hjm
    linarith [hc.hb1]

end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz

theorem interlacing : Formalism.FourierDecayAlt.Sz.Interlacing := by
  intro c de hc hw
  obtain ⟨hk, hm, hDel, hv0, hv1, hb1, hgap, ha, htop⟩ := hc
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · intro i hi1 hik
    have hl : c.lam i = c.v i := by simp [Cfg.lam, hik]
    rw [hl]
    constructor
    · by_cases h1 : i = 1
      · subst h1
        have : c.u de 1 = c.a := by simp [Cfg.u]
        rw [this]; nlinarith
      · have hne : i ≠ c.k := by omega
        have : c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del := by simp [Cfg.u, h1, hne]
        rw [this]
        have hc1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
          rw [Nat.cast_sub hi1]; simp
        unfold Cfg.v; rw [hc1]
        rcases hw.1 (i - 1) with h | h <;> rw [h] <;> nlinarith
    · have h1 : i + 1 ≠ 1 := by omega
      by_cases hlast : i + 1 = c.k
      · have : c.u de (i + 1) = c.ulast := by
          unfold Cfg.u; rw [if_neg h1, if_pos hlast]
        rw [this]
        have hiR : (i : ℝ) + 1 = c.k := by exact_mod_cast hlast
        have hvi : c.v i = c.vlast := by unfold Cfg.v; rw [← hiR]; ring
        rw [hvi]; unfold Cfg.ulast
        by_cases ht : c.top = true
        · have := htop ht; simp [ht]; linarith [this.1]
        · simp [ht]
      · have : c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by
          unfold Cfg.u; rw [if_neg h1, if_neg hlast]; simp
        rw [this]
        rcases hw.1 i with h | h <;> rw [h] <;> nlinarith
  · have hl : c.lam c.k = -c.b 1 := by simp [Cfg.lam]
    have hu : c.u de c.k = c.ulast := by
      have : c.k ≠ 1 := by omega
      simp [Cfg.u, this]
    rw [hl, hu]; unfold Cfg.ulast
    by_cases ht : c.top = true
    · have := htop ht; simp [ht]; linarith [this.2]
    · simp [ht]; linarith

theorem lamStrictAnti : Formalism.FourierDecayAlt.Sz.LamAnti := by
  intro c hc s t hs hst ht
  have hDel := hc.hDel
  have hstR : (s : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hst
  by_cases htk : t < c.k
  · have hsk : s < c.k := by omega
    have h1 : c.lam t = c.v t := by simp [Cfg.lam, htk]
    have h2 : c.lam s = c.v s := by simp [Cfg.lam, hsk]
    rw [h1, h2]; unfold Cfg.v
    nlinarith
  · have h1 : c.lam t = -c.b (t + 1 - c.k) := by simp [Cfg.lam, htk]
    rw [h1]
    by_cases hsk : s < c.k
    · have h2 : c.lam s = c.v s := by simp [Cfg.lam, hsk]
      rw [h2]
      have hb := Sz3.b_ge_one c hc (t + 1 - c.k) (by omega) (by omega)
      have hskR : (s : ℝ) + 1 ≤ (c.k : ℝ) := by exact_mod_cast hsk
      have hv0 := hc.hv0
      unfold Cfg.v
      nlinarith
    · have h2 : c.lam s = -c.b (s + 1 - c.k) := by simp [Cfg.lam, hsk]
      rw [h2]
      have := Sz3.b_lt c hc (s + 1 - c.k) (by omega) (t + 1 - c.k) (by omega) (by omega)
      linarith

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz

end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz

noncomputable def hs (n : ℕ) : ℝ := ∑ d ∈ Ioc 0 n, 1 / (d : ℝ)

end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Sz3

end Formalism.FourierDecayAlt.P
end

