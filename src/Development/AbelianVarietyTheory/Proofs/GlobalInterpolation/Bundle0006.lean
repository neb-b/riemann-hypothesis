module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemPowOfCoeffMem
section
namespace GlobalTheory.PowerSeriesIdealPowers

open MvPowerSeries IsLocalRing

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem mem_max_iff {σ : Type} (f : MvPowerSeries σ O) :
    f ∈ maximalIdeal (MvPowerSeries σ O) ↔ constantCoeff f ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]

theorem mem_smul_top_iff {S : Type} [CommRing S] (I : Ideal S) (x : S) :
    x ∈ (I • ⊤ : Submodule S S) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem coeff_mem_of_mem_pow {σ : Type} (n : ℕ) :
    ∀ f ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n, ∀ d : σ →₀ ℕ,
      coeff d f ∈ (maximalIdeal O) ^ (n - d.degree) := by
  classical
  induction n with
  | zero => intro f _ d; simp
  | succ n ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro x hx y hy d
      rw [coeff_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have h1 := ih x hx p.1
      have h2 : coeff p.2 y ∈ (maximalIdeal O) ^ (1 - p.2.degree) := by
        by_cases h0 : p.2.degree = 0
        · rw [Finsupp.degree_eq_zero_iff] at h0
          rw [h0, coeff_zero_eq_constantCoeff_apply]
          simpa using (mem_max_iff y).1 hy
        · rw [show 1 - p.2.degree = 0 by omega]; simp
      have hdeg : d.degree = p.1.degree + p.2.degree := by rw [← hp, map_add (f := _)]
      have hle : n + 1 - d.degree ≤ (n - p.1.degree) + (1 - p.2.degree) := by omega
      exact Ideal.pow_le_pow_right hle (by rw [pow_add]; exact Ideal.mul_mem_mul h1 h2)
    · intro x y hx hy d
      rw [map_add (f := coeff d)]; exact add_mem (hx d) (hy d)

theorem coeff_X_mul_add {σ : Type} [DecidableEq σ] (i : σ) (g : MvPowerSeries σ O) (d : σ →₀ ℕ) :
    coeff (d + Finsupp.single i 1) (X i * g) = coeff d g := by
  rw [X, coeff_monomial_mul]
  simp

theorem C_mem_pow {σ : Type} (n : ℕ) (c : O) (hc : c ∈ (maximalIdeal O) ^ n) :
    C c ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n := by
  have h1 : C c ∈ Ideal.map (C (σ := σ)) ((maximalIdeal O) ^ n) := Ideal.mem_map_of_mem _ hc
  rw [Ideal.map_pow] at h1
  refine Ideal.pow_right_mono ?_ n h1
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_max_iff, constantCoeff_C]
  exact hx

theorem X_mem_max {σ : Type} (i : σ) : (X i : MvPowerSeries σ O) ∈ maximalIdeal (MvPowerSeries σ O) := by
  rw [mem_max_iff, constantCoeff_X]; exact zero_mem _

theorem mem_pow_of_coeff_mem (a n : ℕ) :
    ∀ f : MvPowerSeries (Fin a) O, (∀ d : Fin a →₀ ℕ, coeff d f ∈ (maximalIdeal O) ^ (n - d.degree)) →
      f ∈ (maximalIdeal (MvPowerSeries (Fin a) O)) ^ n := by
  classical
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    let P : Fin a → (Fin a →₀ ℕ) → Prop := fun i d => d i ≠ 0 ∧ ∀ j < i, d j = 0
    let fi : Fin a → MvPowerSeries (Fin a) O := fun i d => if P i d then coeff d f else 0
    have hfi : ∀ i d, coeff d (fi i) = if P i d then coeff d f else 0 := fun i d => rfl
    have huniq : ∀ i j d, P i d → P j d → i = j := by
      intro i j d hi hj
      rcases lt_trichotomy i j with h | h | h
      · exact absurd (hj.2 i h) hi.1
      · exact h
      · exact absurd (hi.2 j h) hj.1
    have hexists : ∀ d : Fin a →₀ ℕ, d ≠ 0 → ∃ i, P i d := by
      intro d hd
      have hs : d.support.Nonempty := Finsupp.support_nonempty_iff.2 hd
      refine ⟨d.support.min' hs, Finsupp.mem_support_iff.1 (Finset.min'_mem _ hs), fun j hj => ?_⟩
      by_contra hne
      exact absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.2 hne)) (not_le.2 hj)
    have hdecomp : f = C (constantCoeff f) + ∑ i, fi i := by
      ext d
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, coeff_C]
      simp only [hfi]
      by_cases hd : d = 0
      · subst hd
        have : ∀ i, ¬ P i 0 := fun i h => h.1 rfl
        simp [this, coeff_zero_eq_constantCoeff_apply]
      · obtain ⟨i, hi⟩ := hexists d hd
        rw [if_neg hd, zero_add, Finset.sum_eq_single i (fun j _ hj => by
          rw [if_neg (fun h => hj (huniq _ _ _ h hi))]) (fun h => absurd (Finset.mem_univ i) h),
          if_pos hi]
    rw [hdecomp]
    refine add_mem (C_mem_pow _ _ ?_) (Ideal.sum_mem _ fun i _ => ?_)
    · simpa [coeff_zero_eq_constantCoeff_apply] using hf 0
    · have hdvd : (X i : MvPowerSeries (Fin a) O) ∣ fi i := by
        rw [X_dvd_iff]
        intro m hm
        rw [hfi, if_neg (fun h => h.1 hm)]
      obtain ⟨g, hg⟩ := hdvd
      rw [hg, pow_succ']
      refine Ideal.mul_mem_mul (X_mem_max i) (ih g fun d => ?_)
      rw [← coeff_X_mul_add i g d, ← hg, hfi]
      split_ifs
      · have := hf (d + Finsupp.single i 1)
        rwa [map_add, Finsupp.degree_single, show n + 1 - (d.degree + 1) = n - d.degree by omega] at this
      · exact zero_mem _

theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O]
    [IsPrecomplete (IsLocalRing.maximalIdeal O) O] (a : ℕ),
    IsPrecomplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) := by
  intro O _ _ hO a
  constructor
  intro f hf
  simp only [SModEq.sub_mem, mem_smul_top_iff] at hf ⊢
  let s : (Fin a →₀ ℕ) → ℕ → O := fun d k => coeff d (f (k + d.degree))
  have hs : ∀ d, ∃ L : O, ∀ k, s d k ≡ L [SMOD ((maximalIdeal O) ^ k • ⊤ : Submodule O O)] := by
    intro d
    refine IsPrecomplete.prec hO ?_
    intro k l hkl
    rw [SModEq.sub_mem, mem_smul_top_iff]
    have h := coeff_mem_of_mem_pow (k + d.degree) _ (hf (Nat.add_le_add_right hkl _)) d
    rwa [map_sub, Nat.add_sub_cancel] at h
  choose L hL using hs
  let Lim : MvPowerSeries (Fin a) O := fun d => L d
  have hLim : ∀ d, coeff d Lim = L d := fun d => rfl
  refine ⟨Lim, fun n => mem_pow_of_coeff_mem a n _ fun d => ?_⟩
  rw [map_sub, hLim]
  by_cases hd : d.degree ≤ n
  · have h := hL d (n - d.degree)
    rw [SModEq.sub_mem, mem_smul_top_iff] at h
    simp only [s, Nat.sub_add_cancel hd] at h
    exact h
  · rw [show n - d.degree = 0 by omega]; simp
end GlobalTheory.PowerSeriesIdealPowers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormSubOneMulRiemannZetaLe
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology

namespace GlobalTheory.ZetaLeft

noncomputable def emT (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (1 - s) - (1 - s) * (x : ℂ) ^ (1 - s - 1) / 2
    + (1 - s) * (1 - s - 1) * (x : ℂ) ^ (1 - s - 1 - 1) / 12

noncomputable def emE (x : ℝ) (s : ℂ) : ℂ :=
  emT (x + 1) s - emT x s - (1 - s) * (x : ℂ) ^ (1 - s - 1)

lemma hasDerivAt_shift_cpow {a t : ℝ} (h : 0 < a + t) (c : ℂ) :
    HasDerivAt (fun z : ℂ => ((a : ℂ) + z) ^ c) (c * ((a : ℂ) + t) ^ (c - 1)) (t : ℂ) := by
  have h1 : HasDerivAt (fun z : ℂ => (a : ℂ) + z) 1 (t : ℂ) := (hasDerivAt_id _).const_add _
  have h2 : ((a : ℂ) + t) ∈ slitPlane := by
    left; simpa using h
  simpa using h1.cpow_const (c := c) h2

lemma norm_emE_le {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : -(15/8 : ℝ) ≤ s.re) :
    ‖emE a s‖ ≤ (‖s‖ + 2) ^ 4 * a ^ (-(9/8 : ℝ)) := by
  set w : ℂ := 1 - s with hw
  let G : ℂ → ℂ := fun z => ((a : ℂ) + z) ^ w - (z - 1/2) * (w * ((a : ℂ) + z) ^ (w - 1))
    + (z ^ 2 - z + 1/6) / 2 * (w * (w - 1) * ((a : ℂ) + z) ^ (w - 1 - 1))
    - (z ^ 3 - 3/2 * z ^ 2 + z / 2) / 6 * (w * (w - 1) * (w - 1 - 1) * ((a : ℂ) + z) ^ (w - 1 - 1 - 1))
  let G' : ℝ → ℂ := fun t => - (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6) *
    (w * (w - 1) * (w - 1 - 1) * (w - 1 - 1 - 1) * ((a : ℂ) + t) ^ (w - 1 - 1 - 1 - 1))
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun y : ℝ => G y) (G' t) t := by
    intro t ht
    have h : 0 < a + t := by linarith
    have p1 : HasDerivAt (fun z : ℂ => z - 1/2) 1 (t : ℂ) := (hasDerivAt_id _).sub_const _
    have p2 : HasDerivAt (fun z : ℂ => (z ^ 2 - z + 1/6) / 2) ((t : ℂ) - 1/2) (t : ℂ) := by
      have := ((((hasDerivAt_id (t : ℂ)).pow 2).sub (hasDerivAt_id _)).add_const (1/6)).div_const 2
      exact this.congr_deriv (by simp; ring)
    have p3 : HasDerivAt (fun z : ℂ => (z ^ 3 - 3/2 * z ^ 2 + z / 2) / 6)
        (((t : ℂ) ^ 2 - t + 1/6) / 2) (t : ℂ) := by
      have := ((((hasDerivAt_id (t : ℂ)).pow 3).sub
        (((hasDerivAt_id (t : ℂ)).pow 2).const_mul (3/2))).add
        ((hasDerivAt_id (t : ℂ)).div_const 2)).div_const 6
      exact this.congr_deriv (by simp; ring)
    have hG : HasDerivAt G (G' t) (t : ℂ) := by
      have := (((hasDerivAt_shift_cpow h w).sub
        (p1.mul ((hasDerivAt_shift_cpow h (w - 1)).const_mul w))).add
        (p2.mul ((hasDerivAt_shift_cpow h (w - 1 - 1)).const_mul (w * (w - 1))))).sub
        (p3.mul ((hasDerivAt_shift_cpow h (w - 1 - 1 - 1)).const_mul (w * (w - 1) * (w - 1 - 1))))
      exact this.congr_deriv (by simp only [G']; ring)
    exact hG.comp_ofReal
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖G' t‖ ≤ (‖s‖ + 2) ^ 4 * a ^ (-(9/8 : ℝ)) := by
    intro t ht
    have h : 0 < a + t := by linarith [ht.1]
    have b1 : ‖- (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6)‖ ≤ 1 := by
      have : - (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6)
          = ((- ((t ^ 3 - 3/2 * t ^ 2 + t / 2) / 6) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have h2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2.le
      have h3 : t ^ 3 ≤ 1 := pow_le_one₀ ht.1 ht.2.le
      have h4 : 0 ≤ t ^ 2 := by positivity
      have h5 : 0 ≤ t ^ 3 := pow_nonneg ht.1 _
      constructor <;> linarith [ht.1, ht.2]
    have key : ∀ c : ℝ, |c| ≤ 2 → ‖(c : ℂ) - s‖ ≤ ‖s‖ + 2 := by
      intro c hc
      have := norm_sub_le (c : ℂ) s
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have c0 : ‖w‖ ≤ ‖s‖ + 2 := by simpa using key 1 (by norm_num)
    have c1 : ‖w - 1‖ ≤ ‖s‖ + 2 := by
      convert key 0 (by norm_num) using 2; rw [hw]; push_cast; ring
    have c2 : ‖w - 1 - 1‖ ≤ ‖s‖ + 2 := by
      convert key (-1) (by norm_num) using 2; rw [hw]; push_cast; ring
    have c3 : ‖w - 1 - 1 - 1‖ ≤ ‖s‖ + 2 := by
      convert key (-2) (by norm_num) using 2; rw [hw]; push_cast; ring
    have c4 : ‖((a : ℂ) + t) ^ (w - 1 - 1 - 1 - 1)‖ ≤ a ^ (-(9/8 : ℝ)) := by
      rw [← Complex.ofReal_add, Complex.norm_cpow_eq_rpow_re_of_pos h]
      have e : (w - 1 - 1 - 1 - 1).re ≤ -(9/8 : ℝ) := by
        simp [hw]; linarith
      calc _ ≤ (a + t) ^ (-(9/8 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) e
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [ht.1]) (by norm_num)
    simp only [G', norm_mul]
    calc _ ≤ 1 * ((‖s‖ + 2) * (‖s‖ + 2) * (‖s‖ + 2) * (‖s‖ + 2) * a ^ (-(9/8 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun y : ℝ => G y) (f' := G')
    (fun t ht => (hd t ht.1).hasDerivWithinAt) hb
  refine le_of_eq_of_le (congrArg _ ?_) this
  simp only [G, emE, emT, ← hw]
  push_cast
  simp only [add_zero]
  ring

lemma summable_nine_pow_mul_inv_sq_succ : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(9/8 : ℝ))) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num : -(9/8 : ℝ) < -1))
  simpa using this

lemma differentiable_emT {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emT x) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have : NeZero (x : ℂ) := ⟨hx'⟩
  unfold emT
  fun_prop

lemma differentiable_emE {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emE x) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have : NeZero (x : ℂ) := ⟨hx'⟩
  have h1 := differentiable_emT hx
  have h2 := differentiable_emT (x := x + 1) (by linarith)
  unfold emE
  fun_prop

lemma differentiableOn_tsum_emE :
    DifferentiableOn ℂ (fun s => ∑' n : ℕ, emE ((n : ℝ) + 1) s) {s : ℂ | -(15/8 : ℝ) < s.re} := by
  intro s hs
  have ho : IsOpen ({z : ℂ | -(15/8 : ℝ) < z.re} ∩ Metric.ball 0 (‖s‖ + 1)) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (n : ℕ) (z : ℂ) => emE ((n : ℝ) + 1) z)
    (summable_nine_pow_mul_inv_sq_succ.mul_left ((‖s‖ + 3) ^ 4))
    (fun n => (differentiable_emE (by positivity)).differentiableOn) ho (by
      intro n z hz
      have h1 : ‖z‖ < ‖s‖ + 1 := by simpa using hz.2
      refine (norm_emE_le (by simp) (le_of_lt hz.1)).trans ?_
      have h2 : ‖z‖ + 2 ≤ ‖s‖ + 3 := by linarith
      gcongr)
  exact (this.differentiableAt (ho.mem_nhds ⟨hs, by simp⟩)).differentiableWithinAt

lemma tendsto_cpow_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have := (tendsto_rpow_neg_atTop (y := -c.re) (by linarith)).comp h1
  refine this.congr fun n => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

lemma eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * riemannZeta s = emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s := by
  have hsum : Summable (fun n : ℕ => emE ((n : ℝ) + 1) s) :=
    Summable.of_norm_bounded (summable_nine_pow_mul_inv_sq_succ.mul_left ((‖s‖ + 2) ^ 4))
      (fun n => norm_emE_le (by simp) (by linarith))
  have hT : Tendsto (fun n : ℕ => emT ((n : ℝ) + 1) s) atTop (𝓝 0) := by
    have := ((tendsto_cpow_zero (c := 1 - s) (by simp; linarith)).sub
      (((tendsto_cpow_zero (c := 1 - s - 1) (by simp; linarith)).const_mul (1 - s)).div_const 2)).add
      (((tendsto_cpow_zero (c := 1 - s - 1 - 1) (by simp; linarith)).const_mul
        ((1 - s) * (1 - s - 1))).div_const 12)
    simpa [emT] using this
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
    exact (by simpa using this : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s)).hasSum
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, emE ((n : ℝ) + 1) s =
      emT ((N : ℝ) + 1) s - emT 1 s + (s - 1) * ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ s := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, emE]
      have : (1 - s - 1) = -s := by ring
      rw [this, Complex.cpow_neg]
      push_cast
      ring
  have h1 := (hT.sub_const (emT 1 s)).add (hz.tendsto_sum_nat.const_mul (s - 1))
  have h2 := hsum.hasSum.tendsto_sum_nat
  simp only [hpart] at h2
  rw [tendsto_nhds_unique h2 h1]
  ring

lemma eq_of_lt {s : ℂ} (hs : -(15/8 : ℝ) < s.re) (h1 : s ≠ 1) :
    (s - 1) * riemannZeta s = emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s := by
  have ho : IsOpen {z : ℂ | -(15/8 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : ∀ z : ℂ, z ≠ 1 → LFunctionTrivChar₁ 1 z = (z - 1) * riemannZeta z := by
    intro z hz
    rw [LFunctionTrivChar₁, Function.update_of_ne hz, LFunctionTrivChar, LFunction_modOne_eq]
  have hA : AnalyticOnNhd ℂ (LFunctionTrivChar₁ 1) {z : ℂ | -(15/8 : ℝ) < z.re} :=
    (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd ho
  have hB : AnalyticOnNhd ℂ (fun s => emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s)
      {z : ℂ | -(15/8 : ℝ) < z.re} :=
    ((differentiable_emT one_pos).differentiableOn.add differentiableOn_tsum_emE).analyticOnNhd ho
  have := hA.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_halfSpace_re_gt _).isPreconnected (z₀ := 2) (by simp; norm_num) (by
      have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
      filter_upwards [this] with z hz
      rw [hf z (by rintro rfl; simp at hz), eq_of_one_lt hz])
  rw [← hf s h1]
  exact this hs

theorem norm_sub_one_mul_riemannZeta_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(7/4 : ℝ) ≤ s.re → s ≠ 1 →
      ‖(s - 1) * riemannZeta s‖ ≤ C * (‖s‖ + 2) ^ 5 := by
  set K : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(9/8 : ℝ)) with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun n => by positivity
  refine ⟨3 + K, by linarith, fun s hs h1 => ?_⟩
  rw [eq_of_lt (by linarith) h1]
  set R := ‖s‖ + 2 with hR
  have hR1 : 1 ≤ R := by have := norm_nonneg s; linarith
  have h2 : ‖∑' n : ℕ, emE ((n : ℝ) + 1) s‖ ≤ R ^ 4 * K :=
    tsum_of_norm_bounded (summable_nine_pow_mul_inv_sq_succ.hasSum.mul_left (R ^ 4))
      (fun n => norm_emE_le (by simp) (by linarith))
  have c0 : ‖1 - s‖ ≤ R := by
    have := norm_sub_le 1 s
    rw [norm_one] at this; linarith
  have c1 : ‖1 - s - 1‖ ≤ R := by simp [hR]
  have h3 : ‖emT 1 s‖ ≤ 1 + R / 2 + R * R / 12 := by
    simp only [emT, Complex.ofReal_one, Complex.one_cpow, mul_one]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
    · simp only [norm_one, norm_div, Complex.norm_ofNat]; gcongr
    · simp only [norm_mul, norm_div, Complex.norm_ofNat]; gcongr
  have p0 : 1 ≤ R ^ 5 := one_le_pow₀ hR1
  have p1 : R ^ 1 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p2 : R ^ 2 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p5 : R ^ 4 * K ≤ R ^ 5 * K := by gcongr
  refine (norm_add_le _ _).trans ?_
  nlinarith

end GlobalTheory.ZetaLeft
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlaneLatticeShortBasisOfBoundPowTwo
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem plane_lattice_reduction_step (e₁ e₂ : ℂ)
    (h : 2 * |((starRingEnd ℂ) e₁ * e₂).im| < ‖e₁‖ ^ 2) :
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      2 * ‖f₁‖ ^ 2 ≤ ‖e₁‖ ^ 2 := by
  have hN : 0 < ‖e₁‖ ^ 2 := lt_of_le_of_lt (by positivity) h
  set k : ℤ := round (((starRingEnd ℂ) e₁ * e₂).re / ‖e₁‖ ^ 2) with hk
  refine ⟨e₂ - k • e₁, e₁, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · have : x = (x - k • e₁) + k • e₁ := by ring
        rw [SetLike.mem_coe]
        nth_rewrite 2 [this]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · have : ((starRingEnd ℂ) (e₂ - k • e₁) * e₁).im = -((starRingEnd ℂ) e₁ * e₂).im := by
      simp
      ring
    rw [this, abs_neg]
  · have hr := abs_sub_round (((starRingEnd ℂ) e₁ * e₂).re / ‖e₁‖ ^ 2)
    rw [← hk] at hr
    have key : ‖e₁‖ ^ 2 * ‖e₂ - k • e₁‖ ^ 2 =
        (((starRingEnd ℂ) e₁ * e₂).re - k * ‖e₁‖ ^ 2) ^ 2 +
          ((starRingEnd ℂ) e₁ * e₂).im ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    generalize ((starRingEnd ℂ) e₁ * e₂).re = R at *
    generalize ((starRingEnd ℂ) e₁ * e₂).im = J at *
    generalize ‖e₁‖ ^ 2 = N at *
    generalize ‖e₂ - k • e₁‖ ^ 2 = M at *
    have h1 : (R - k * N) ^ 2 ≤ N ^ 2 / 4 := by
      have e : R - k * N = (R / N - k) * N := by field_simp
      have h2 : (R / N - k) ^ 2 ≤ 1 / 4 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (R / N - k)]
      rw [e, mul_pow]
      nlinarith [sq_nonneg N]
    have h3 : J ^ 2 ≤ N ^ 2 / 4 := by
      rw [← sq_abs J]
      nlinarith [abs_nonneg J]
    have h4 : N * (2 * M) ≤ N * N := by nlinarith
    exact le_of_mul_le_mul_left h4 hN

theorem plane_lattice_short_basis_of_bound_pow_two (n : ℕ) : ∀ e₁ e₂ : ℂ,
    ‖e₁‖ ^ 2 ≤ 2 ^ n * (2 * |((starRingEnd ℂ) e₁ * e₂).im|) →
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      ‖f₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by
  induction n with
  | zero =>
    intro e₁ e₂ h
    exact ⟨e₁, e₂, rfl, rfl, by simpa using h⟩
  | succ n ih =>
    intro e₁ e₂ h
    by_cases hc : ‖e₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im|
    · exact ⟨e₁, e₂, rfl, rfl, hc⟩
    · obtain ⟨g₁, g₂, hs, hi, hn⟩ := plane_lattice_reduction_step e₁ e₂ (not_le.mp hc)
      obtain ⟨f₁, f₂, hs', hi', hn'⟩ := ih g₁ g₂ (by
        rw [hi]
        rw [pow_succ (2 : ℝ) n] at h
        linarith)
      exact ⟨f₁, f₂, hs'.trans hs, hi'.trans hi, hi ▸ hn'⟩

theorem plane_lattice_short_basis : ∀ e₁ e₂ : ℂ, ((starRingEnd ℂ) e₁ * e₂).im ≠ 0 →
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      ‖f₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by
  intro e₁ e₂ h
  have hD : 0 < 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (‖e₁‖ ^ 2 / (2 * |((starRingEnd ℂ) e₁ * e₂).im|)) (one_lt_two (α := ℝ))
  exact plane_lattice_short_basis_of_bound_pow_two n e₁ e₂ ((div_lt_iff₀ hD).mp hn).le

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumRangeMulOfPeriodic
section
namespace GlobalTheory.PeriodicSumShift

theorem periodic_shift {K : Type} (g : ℕ → K) (N : ℕ) (h : ∀ i, g (N + i) = g i) :
    ∀ k i, g (N * k + i) = g i := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih => intro i; rw [Nat.mul_succ, add_assoc, ih, h]

theorem sum_range_mul_of_periodic : ∀ {K : Type} [inst : Field K] (g : ℕ → K) (N : ℕ),
    (∀ (i : ℕ), g (N + i) = g i) → ∀ (k : ℕ),
      ∑ i ∈ Finset.range (N * k), g i = (↑k : K) * ∑ i ∈ Finset.range N, g i := by
  intro K _ g N h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [periodic_shift g N h k]
    push_cast; ring

end GlobalTheory.PeriodicSumShift
end

