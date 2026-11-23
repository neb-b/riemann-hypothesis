module

public import Formalism.HermitianCurvature.Bundle0009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.Bundle0004

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GramLocTendsto
section
open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBB.K8

noncomputable section

def dw (c : ℂ) : ℝ := ((1 + ‖c‖) ^ 3)⁻¹

theorem dw_cont : Continuous dw :=
  ((continuous_const.add continuous_norm).pow 3).inv₀ fun c => pow_ne_zero _ (add_pos_of_pos_of_nonneg one_pos (norm_nonneg c)).ne'

theorem dw_integrable : Integrable dw := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  show (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹
  rw [Real.rpow_neg (by positivity)]
  norm_cast

theorem bound_all {f : ℂ → ℂ} (hf : Continuous f) {C : ℝ} (h : ∀ c, c ≠ 0 → ‖f c‖ ≤ C * dw c) (c : ℂ) :
    ‖f c‖ ≤ C * dw c := by
  have hs : IsClosed {c : ℂ | ‖f c‖ ≤ C * dw c} :=
    isClosed_le (continuous_norm.comp hf) (continuous_const.mul dw_cont)
  have hsub : ({0}ᶜ : Set ℂ) ⊆ {c | ‖f c‖ ≤ C * dw c} := fun c hc => h c hc
  have := hs.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : ℂ)).closure_eq] at this
  exact this (Set.mem_univ c)

theorem fourier_cont {f : ℂ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

theorem ae_ne_zero : ∀ᵐ c : ℂ ∂volume, c ≠ 0 := by
  simp [ae_iff]

theorem limit_fourier (g : ℕ → ℂ → ℂ) (g0 : ℂ → ℂ) (φ : ℕ → ℂ → ℂ) (C C' : ℝ)
    (hφc : ∀ n, Continuous (φ n)) (hφg : ∀ n c, c ≠ 0 → φ n c = g n c)
    (hconv : ∀ c, Tendsto (fun n => g n c) atTop (𝓝 (g0 c)))
    (hb : ∀ n c, c ≠ 0 → ‖g n c‖ ≤ C * dw c)
    (hT : ∀ n w, ‖𝓕 (φ n) w‖ ≤ C' * dw w) :
    ∃ ψ : ℂ → ℂ, Continuous ψ ∧ (∀ c, c ≠ 0 → ψ c = g0 c) ∧ (∀ c, ‖ψ c‖ ≤ C * dw c) ∧
      Tendsto (fun n => ∫ c, φ n c) atTop (𝓝 (∫ c, ψ c)) := by
  have hφb : ∀ n c, ‖φ n c‖ ≤ C * dw c := fun n =>
    bound_all (hφc n) fun c hc => by rw [hφg n c hc]; exact hb n c hc
  have hBi : Integrable (fun c => C * dw c) := dw_integrable.const_mul C
  have hB'i : Integrable (fun c => C' * dw c) := dw_integrable.const_mul C'
  have hφi : ∀ n, Integrable (φ n) := fun n =>
    hBi.mono' (hφc n).aestronglyMeasurable (Eventually.of_forall (hφb n))
  have hFt : ∀ w, Tendsto (fun n => 𝓕 (φ n) w) atTop (𝓝 (𝓕 g0 w)) := by
    intro w
    show Tendsto (fun n => ∫ v, 𝐞 (-⟪v, w⟫) • φ n v) atTop (𝓝 (∫ v, 𝐞 (-⟪v, w⟫) • g0 v))
    refine tendsto_integral_of_dominated_convergence (fun c => C * dw c) (fun n => ?_) hBi (fun n => ?_) ?_
    · exact ((Real.fourierIntegral_convergent_iff w).mpr (hφi n)).aestronglyMeasurable
    · exact Eventually.of_forall fun c => by rw [Circle.norm_smul]; exact hφb n c
    · filter_upwards [ae_ne_zero] with c hc
      simp only [hφg _ c hc]
      exact (hconv c).const_smul _
  have hGm : AEStronglyMeasurable (𝓕 g0) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (fourier_cont (hφi n)).aestronglyMeasurable)
      (ae_of_all _ hFt)
  have hGb : ∀ w, ‖𝓕 g0 w‖ ≤ C' * dw w := fun w => le_of_tendsto' (hFt w).norm fun n => hT n w
  have hGi : Integrable (𝓕 g0) := hB'i.mono' hGm (Eventually.of_forall hGb)
  have hinv : ∀ n, 𝓕⁻ (𝓕 (φ n)) = φ n := fun n =>
    (hφc n).fourierInv_fourier_eq (hφi n)
      (hB'i.mono' (fourier_cont (hφi n)).aestronglyMeasurable (Eventually.of_forall (hT n)))
  set ψ : ℂ → ℂ := 𝓕⁻ (𝓕 g0) with hψ
  have hψlim : ∀ c, Tendsto (fun n => φ n c) atTop (𝓝 (ψ c)) := by
    intro c
    have : (fun n => φ n c) = fun n => 𝓕⁻ (𝓕 (φ n)) c := funext fun n => by rw [hinv n]
    rw [this, hψ]
    simp only [Real.fourierInv_eq]
    refine tendsto_integral_of_dominated_convergence (fun w => C' * dw w) (fun n => ?_) hB'i (fun n => ?_) ?_
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
        (fourier_cont (hφi n))).aestronglyMeasurable
    · exact Eventually.of_forall fun w => by rw [Circle.norm_smul]; exact hT n w
    · exact ae_of_all _ fun w => (hFt w).const_smul _
  refine ⟨ψ, ?_, fun c hc => ?_, fun c => le_of_tendsto' (hψlim c).norm fun n => hφb n c, ?_⟩
  · have : ψ = fun c => 𝓕 (𝓕 g0) (-c) := funext fun c => Real.fourierInv_eq_fourier_neg _ c
    rw [this]
    exact (fourier_cont hGi).comp continuous_neg
  · refine tendsto_nhds_unique (hψlim c) ?_
    have : (fun n => φ n c) = fun n => g n c := funext fun n => hφg n c hc
    rw [this]
    exact hconv c
  · exact tendsto_integral_of_dominated_convergence (fun c => C * dw c)
      (fun n => (hφc n).aestronglyMeasurable) hBi (fun n => ae_of_all _ (hφb n)) (ae_of_all _ hψlim)

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def Lm (g : ℕ) (l : ℂ) : ℂ := -(((2 / (g : ℝ) : ℝ)) : ℂ) * conj l

theorem psiL_eq (S : C.HidaSetting E Wp Wq) (l c z : ℂ) :
    z * KB.psiL S l c = 𝐞 (-⟪c, Lm S.g l⟫) • z := by
  rw [Circle.smul_def, Real.fourierChar_apply, KB.psiL, mul_comm z]
  congr 2
  have hi : ⟪c, Lm S.g l⟫ = -(2 / (S.g : ℝ)) * (l * c).re := by
    simp [Lm, Complex.inner, Complex.mul_re]
    ring
  rw [hi]
  push_cast
  ring

theorem Lm_inv (g : ℕ) (hg : (g : ℝ) ≠ 0) (w : ℂ) : Lm g ((((-(g : ℝ) / 2 : ℝ)) : ℂ) * conj w) = w := by
  simp only [Lm, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  rw [← mul_assoc, ← Complex.ofReal_neg, ← Complex.ofReal_mul]
  have : (-(2 / (g : ℝ)) * (-(g : ℝ) / 2)) = 1 := by field_simp
  rw [this]
  simp

theorem decay_scale (g : ℝ) (hg : 1 ≤ g) (w : ℂ) :
    ((1 + ‖(((-g / 2 : ℝ)) : ℂ) * conj w‖) ^ 3)⁻¹ ≤ 8 * dw w := by
  have hn : ‖(((-g / 2 : ℝ)) : ℂ) * conj w‖ = g / 2 * ‖w‖ := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (by linarith : (0:ℝ) < g)]
    norm_num
  rw [hn]
  have h0 : 0 < (1 + ‖w‖) / 2 := by positivity
  have h1 : (1 + ‖w‖) / 2 ≤ 1 + g / 2 * ‖w‖ := by nlinarith [norm_nonneg w]
  calc ((1 + g / 2 * ‖w‖) ^ 3)⁻¹ ≤ (((1 + ‖w‖) / 2) ^ 3)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le h1 3)
    _ = 8 * dw w := by unfold dw; field_simp; ring

theorem g_ge_one (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : (1 : ℝ) ≤ S.g := by
  have : 1 ≤ S.g := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hg1.ne' hg2.ne')
  exact_mod_cast this

theorem gramLoc_tendsto (S : C.HidaSetting E Wp Wq)
    (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    (v : Fin S.f) {ε : ℝ} (hε : 0 < ε) (i : ℕ) (w : S.W) (p q : C.LPt) :
    Tendsto (fun n => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) p q) atTop
      (𝓝 (S.gramLoc v ε i (w.1 v) p q)) :=
  (hconv v ε hε i _ ⟨w, rfl⟩ p q).const_mul _

theorem intAll_limit (S : C.HidaSetting E Wp Wq)
    (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2)
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    (hInt : ∀ n, KB.IntAll (KB.withRR S (RR n)))
    (hB : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 →
      D.ptSize h' = i - 1 →
      ∃ C : ℝ, ∀ n, (∀ c : ℂ, c ≠ 0 →
          ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹) ∧
        ∀ l : ℂ, ‖∫ c : ℂ, (KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S l c‖ ≤
          C * ((1 + ‖l‖) ^ 3)⁻¹) :
    KB.IntAll S := by
  intro v ε hε i hi1 hi2 w h h' hh hh'
  obtain ⟨C, hC⟩ := hB v ε hε i hi1 hi2 (w.1 v) ⟨w, rfl⟩ h h' hh hh'
  have hC0 : 0 ≤ C := by
    have := ((hC 0).2 0).trans' (norm_nonneg _)
    simpa using this
  have H := fun n => hInt n v ε hε i hi1 hi2 w h h' hh hh'
  choose φ hφc hφe hφb hφi using H
  have hg := g_ge_one S hg1 hg2
  have hT : ∀ n w', ‖𝓕 (φ n) w'‖ ≤ 8 * C * dw w' := by
    intro n w'
    set l : ℂ := (((-(S.g : ℝ) / 2 : ℝ)) : ℂ) * conj w' with hl
    have hLm : Lm S.g l = w' := Lm_inv S.g (by linarith) w'
    have he : 𝓕 (φ n) w' = ∫ c : ℂ, (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) *
        KB.psiL S l c := by
      rw [Real.fourier_eq]
      refine integral_congr_ae ?_
      filter_upwards [ae_ne_zero] with c hc
      rw [psiL_eq, hLm, hφe n c hc]
    rw [he]
    have h8 := mul_le_mul_of_nonneg_left (decay_scale S.g hg w') hC0
    calc _ ≤ C * ((1 + ‖l‖) ^ 3)⁻¹ := (hC n).2 l
      _ ≤ C * (8 * dw w') := h8
      _ = 8 * C * dw w' := by ring
  obtain ⟨ψ, hψc, hψe, hψb, hψi⟩ := limit_fourier
    (fun n c => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]))
    (fun c => S.gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) φ C (8 * C) hφc hφe
    (fun c => gramLoc_tendsto S RR hconv v hε i w _ _) (fun n c hc => (hC n).1 c hc) hT
  refine ⟨ψ, hψc, hψe, ⟨C, hψb⟩, ?_⟩
  have h1 : Tendsto (fun n => ∫ c, φ n c) atTop
      (𝓝 (((KB.dlB S i 1 : ℝ) : ℂ) * S.gramLoc v ε (i - 1) (w.1 v) h h')) := by
    have : (fun n => ∫ c, φ n c) =
        fun n => ((KB.dlB S i 1 : ℝ) : ℂ) * (KB.withRR S (RR n)).gramLoc v ε (i - 1) (w.1 v) h h' :=
      funext fun n => hφi n
    rw [this]
    exact (gramLoc_tendsto S RR hconv v hε (i - 1) w h h').const_mul _
  exact tendsto_nhds_unique hψi h1

end setting

end

end Formalism.FourierDecayAlt.P.PBB.K8
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp
section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace GroupGeneratedByExp

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem norm_pow_mul_le (x u : 𝔸) (n : ℕ) : ‖x ^ n * u‖ ≤ ‖x‖ ^ n * ‖u‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

theorem norm_exp_mul_le (x u : 𝔸) : ‖NormedSpace.exp x * u‖ ≤ Real.exp ‖x‖ * ‖u‖ := by
  have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • x ^ n) * u) (NormedSpace.exp x * u) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x).mul_right u
  have h2 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • ‖x‖ ^ n) * ‖u‖) (Real.exp ‖x‖ * ‖u‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖).mul_right ‖u‖
  refine h1.norm_le_of_bounded h2 fun n => ?_
  rw [smul_mul_assoc, norm_smul, smul_eq_mul, mul_assoc, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_mul_le x u n) (by positivity)

theorem norm_pow_mul_le' {a : 𝔸} {q : ℝ} (hq : 0 ≤ q) (ha : ∀ u, ‖a * u‖ ≤ q * ‖u‖) (m : ℕ) (u : 𝔸) :
    ‖a ^ m * u‖ ≤ q ^ m * ‖u‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (ha _).trans (mul_le_mul_of_nonneg_left ih hq)

theorem norm_pow_sub_pow_le {a b : 𝔸} {q : ℝ} (hq : 1 ≤ q) (ha : ∀ u, ‖a * u‖ ≤ q * ‖u‖)
    (hb : ∀ u, ‖b * u‖ ≤ q * ‖u‖) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ (m : ℝ) * q ^ m * (‖a - b‖ * ‖(1 : 𝔸)‖) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by
      rw [pow_succ', pow_succ']; noncomm_ring
    have h1 : ‖a * (a ^ m - b ^ m)‖ ≤ q * ((m : ℝ) * q ^ m * (‖a - b‖ * ‖(1 : 𝔸)‖)) :=
      (ha _).trans (mul_le_mul_of_nonneg_left ih hq0)
    have h2 : ‖b ^ m‖ ≤ q ^ (m + 1) * ‖(1 : 𝔸)‖ := by
      have := norm_pow_mul_le' hq0 hb m 1
      rw [mul_one] at this
      refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact pow_le_pow_right₀ hq (Nat.le_succ m)
    have h3 : ‖(a - b) * b ^ m‖ ≤ ‖a - b‖ * (q ^ (m + 1) * ‖(1 : 𝔸)‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add h1 h3).trans (le_of_eq ?_))
    push_cast
    ring

theorem diff_hasDerivAt (X Y : 𝔸) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) - NormedSpace.exp (t • (X + Y))) 0 0 := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
  have h3 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X + Y) 0
  have h := (h1.mul h2).sub h3
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, sub_self] at h
  exact h

theorem trotter (X Y : 𝔸) :
    Tendsto (fun n : ℕ => (NormedSpace.exp (((n : ℝ)⁻¹) • X) * NormedSpace.exp (((n : ℝ)⁻¹) • Y)) ^ n) atTop
      (𝓝 (NormedSpace.exp (X + Y))) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  set s : ℝ := ‖X‖ + ‖Y‖ with hs
  have hs0 : 0 ≤ s := by positivity
  set F : ℝ → 𝔸 := fun t : ℝ =>
    NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) - NormedSpace.exp (t • (X + Y)) with hF
  have hF0 : F 0 = 0 := by simp [hF, NormedSpace.exp_zero]
  have hsl := (diff_hasDerivAt X Y).tendsto_slope_zero
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact (inv_pos.2 this).ne'
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) • F ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
    have := hsl.comp hinv
    refine this.congr fun n => ?_
    simp only [Function.comp, zero_add, inv_inv]
    rw [show NormedSpace.exp ((0 : ℝ) • X) * NormedSpace.exp ((0 : ℝ) • Y) - NormedSpace.exp ((0 : ℝ) • (X + Y)) = 0
      from hF0, sub_zero]
  have h2 : Tendsto (fun n : ℕ => Real.exp s * ‖(1 : 𝔸)‖ * ‖(n : ℝ) • F ((n : ℝ)⁻¹)‖) atTop (𝓝 0) := by
    have := (h1.norm).const_mul (Real.exp s * ‖(1 : 𝔸)‖)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ h2
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hni : (0 : ℝ) ≤ (n : ℝ)⁻¹ := (inv_pos.2 hn0).le
  have hb : NormedSpace.exp (X + Y) = NormedSpace.exp (((n : ℝ)⁻¹) • (X + Y)) ^ n := by
    rw [← NormedSpace.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
  have hq : (1 : ℝ) ≤ Real.exp ((n : ℝ)⁻¹ * s) := Real.one_le_exp (by positivity)
  have ha : ∀ u : 𝔸, ‖NormedSpace.exp (((n : ℝ)⁻¹) • X) * NormedSpace.exp (((n : ℝ)⁻¹) • Y) * u‖ ≤
      Real.exp ((n : ℝ)⁻¹ * s) * ‖u‖ := by
    intro u
    rw [mul_assoc]
    refine (norm_exp_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left (norm_exp_mul_le _ _) (Real.exp_pos _).le).trans (le_of_eq ?_)
    rw [← mul_assoc, ← Real.exp_add, norm_smul, norm_smul, Real.norm_of_nonneg hni, hs, mul_add]
  have hb' : ∀ u : 𝔸, ‖NormedSpace.exp (((n : ℝ)⁻¹) • (X + Y)) * u‖ ≤ Real.exp ((n : ℝ)⁻¹ * s) * ‖u‖ := by
    intro u
    refine (norm_exp_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [Real.exp_le_exp, norm_smul, Real.norm_of_nonneg hni]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hni
  rw [hb]
  refine (norm_pow_sub_pow_le hq ha hb' n).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul, show (n : ℝ) * ((n : ℝ)⁻¹ * s) = s by field_simp, norm_smul, Real.norm_of_nonneg hn0.le]
  ring

end Banach

theorem trotterMx (N : ℕ) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    Tendsto (fun n : ℕ => (NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • X) * NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • Y)) ^ n) atTop
      (𝓝 (NormedSpace.exp (X + Y))) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin N) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℂ)
  have hc : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℝ _
  have h := trotter X Y
  simp only [Complex.coe_smul]
  exact h

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem group_eq_exp (φ : ℝ → (W →L[ℂ] W)) (A : W →L[ℂ] W) (h0 : φ 0 = 1)
    (hA : ∀ t, HasDerivAt φ ((φ t).comp A) t) (t : ℝ) : φ t = NormedSpace.exp (t • A) := by
  have hcW : CompleteSpace W := FiniteDimensional.complete ℂ W
  let _ : NormedAlgebra ℚ (W →L[ℂ] W) := NormedAlgebra.restrictScalars ℚ ℂ (W →L[ℂ] W)
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-A)))
      ((-A) * NormedSpace.exp (s • (-A))) s := fun s => hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) s
  have hψ : ∀ s : ℝ, HasDerivAt (fun u : ℝ => φ u * NormedSpace.exp (u • (-A))) 0 s := by
    intro s
    have h := (hA s).mul (hE s)
    have e : (φ s).comp A * NormedSpace.exp (s • (-A)) + φ s * ((-A) * NormedSpace.exp (s • (-A))) = 0 := by
      show φ s * A * _ + _ = 0
      noncomm_ring
    rwa [e] at h
  have hconst := is_const_of_deriv_eq_zero (𝕜 := ℝ) (fun s => (hψ s).differentiableAt) (fun s => (hψ s).deriv) t 0
  simp only [zero_smul, NormedSpace.exp_zero, h0, mul_one] at hconst
  have hinv : NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A) = 1 := by
    rw [← NormedSpace.exp_add_of_commute, smul_neg, neg_add_cancel, NormedSpace.exp_zero]
    exact (((Commute.refl A).neg_left).smul_left _).smul_right _
  calc φ t = φ t * (NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A)) := by rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst, one_mul]

end Rep

end GroupGeneratedByExp

theorem trotter_product_formula : Qr.Trotter := by
  intro 𝔸 _ _ _ X Y
  exact GroupGeneratedByExp.trotter X Y

theorem trotter_product_matrices : Qr.TrotterMx := by
  intro N X Y
  exact GroupGeneratedByExp.trotterMx N X Y

theorem representation_exp : Qr.PiExp := by
  intro W _ _ _ k r z π hπ X hX t
  have hcont : Continuous fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    have h1 := Qx8.lcurve_cont X (1 : Mx k r)
    simp only [Matrix.mul_one] at h1
    exact hπ.2.comp_continuous h1 (QrD.exp_uw hX)
  have h0 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) 0 = 1 := by
    simp [NormedSpace.exp_zero, hπ.1.1]
  obtain ⟨A, hA⟩ := one_parameter_differentiable W (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) h0
    (fun s t => by
      show π (NormedSpace.exp (((s + t : ℝ) : ℂ) • X)) = _
      rw [B5.exp_add', hπ.1.2 _ (QrD.exp_uw hX s) _ (QrD.exp_uw hX t)]) hcont
  have hAd : QrD.dOp π X = A := by
    have h := (QrD.dOp_hasDeriv hπ.1 hπ.2 hX).unique (hA 0)
    have h0' : π (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := h0
    rw [h, h0']
    exact ContinuousLinearMap.id_comp A
  have h := GroupGeneratedByExp.group_eq_exp _ A h0 hA t
  rw [hAd]
  exact h

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStmt
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory

noncomputable section

open Classical

def Lstd (f : ℕ) (R : ℝ) : Submodule ℤ (crystallineComparison.V f) :=
  Submodule.span ℤ (Set.range fun p : Fin f × Bool =>
    (Pi.single p.1 (if p.2 then (R : ℂ) * Complex.I else (R : ℂ)) : crystallineComparison.V f))

def LstdFacts : Prop :=
  ∀ (f : ℕ) (R : ℝ), 0 < R →
    ∃ (_ : DiscreteTopology (Lstd f R)) (_ : IsZLattice ℝ (Lstd f R)),
      ZLattice.covolume (Lstd f R) = R ^ (2 * f) ∧
      ∀ σ : crystallineComparison.V f, σ ∈ crystallineComparison.dualSet (Lstd f R) ↔
        ∀ v, ∃ a b : ℤ, σ v = ((a : ℂ) + (b : ℂ) * Complex.I) / (2 * (R : ℂ))

def LstdSum : Prop :=
  ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ (f : ℕ) (R g : ℝ) (L : Fin f → ℝ), 0 < R → 0 < g → (∀ v, 0 ≤ L v) →
    Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f))) ∧
    ∑' σ : crystallineComparison.dualSet (Lstd f R), crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f)) ≤
      ∏ v, Cs * (1 + (R * L v / g) ^ 2)

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def embV (S : C.HidaSetting E Wp Wq) : E →+ crystallineComparison.V S.f where
  toFun t := fun v => S.σ v t
  map_zero' := by funext v; simp
  map_add' a b := by funext v; simp

def latV (S : C.HidaSetting E Wp Wq) (L : AddSubgroup E) : Submodule ℤ (crystallineComparison.V S.f) :=
  (AddSubgroup.toIntSubmodule L).map (embV S).toIntLinearMap

def thr (S : C.HidaSetting E Wp Wq) (b s : ℕ) (v : Fin S.f) : ℝ :=
  J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s (S.pl v)

end setting

def SizesSup : Prop :=
  ∀ Cs : ℝ, 1 ≤ Cs → ∃ B : ℝ, 1 ≤ B ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
      [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
      [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
      0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → ∀ b n, 1 ≤ b → 1 ≤ n → (∀ v, 0 < thr S b n v) →
        ∃ R : ℝ, 0 < R ∧
          (∏ _v : Fin S.f, KB.dlB S b n) * (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
            B ^ S.f * S.base.vol b n

def BlockLatV : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
      [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
      [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
      0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → ∀ b s, 1 ≤ b → 1 ≤ s →
        ∃ (_ : DiscreteTopology (latV S (J.LaB E S.g S.G.r b s)))
          (_ : IsZLattice ℝ (latV S (J.LaB E S.g S.G.r b s))),
          ZLattice.covolume (latV S (J.LaB E S.g S.G.r b s)) = ∏ _v : Fin S.f, KB.dlB S b s ∧
          (∃ (Lm : Submodule ℤ (crystallineComparison.V S.f)) (_ : DiscreteTopology Lm) (_ : IsZLattice ℝ Lm),
            ∀ σ ∈ crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)), (S.g : ℝ) • σ ∈ Lm) ∧
          ∀ Λ : Fin S.f → ℝ, (∀ v, 0 ≤ Λ v ∧ Λ v ≤ thr S b s v) → S.base.vol b s ≤ 1 →
            Summable (fun σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)) =>
              crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) ∧
            ∑' σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)),
              crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) ≤ A ^ S.f

end

end Formalism.FourierDecayAlt.P.PBC
end

