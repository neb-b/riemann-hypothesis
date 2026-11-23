module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmoothedIdealCharacterSumMainTermIdealClassRepre
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEntireMellinSmoothedDirichletSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLSeriesContinuation
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
open Filter Topology Set Asymptotics in
private theorem eq_of_norm_sub_div_le {f : ℝ → ℂ} {R R' : ℂ} {C C' : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖f t - R / t‖ ≤ C)
    (h' : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖f t - R' / t‖ ≤ C') : R = R' := by
  by_contra hne
  have hd : 0 < ‖R - R'‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set D := |C| + |C'| + 1 with hD_def
  have hD : 0 < D := by positivity
  set t := min 1 (‖R - R'‖ / (2 * D)) with ht_def
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htD : t * D ≤ ‖R - R'‖ / 2 := by
    calc t * D ≤ ‖R - R'‖ / (2 * D) * D := by gcongr; exact min_le_right _ _
      _ = ‖R - R'‖ / 2 := by field_simp
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
  have key : R - R' = (t : ℂ) * ((f t - R' / t) - (f t - R / t)) := by
    field_simp
    ring
  have hle : ‖R - R'‖ ≤ t * (C' + C) := by
    rw [key, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add (h' t ht0 ht1) (h t ht0 ht1))
  have : t * (C' + C) ≤ t * D :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self C, le_abs_self C']) ht0.le
  linarith

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
open Filter Topology Set Asymptotics in
private theorem exists_differentiable_eq_div_of_family {ι : Type} (M G : ι → ℂ → ℂ)
    (F : ℂ → ℂ) (hM : ∀ i, Differentiable ℂ (M i)) (hG : ∀ i, Differentiable ℂ (G i))
    (hGF : ∀ i s, 1 < s.re → G i s = M i s * F s) (hne : ∀ s, ∃ i, M i s ≠ 0) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s, 1 < s.re → Z s = F s) ∧
      ∀ i s, M i s ≠ 0 → Z s = G i s / M i s := by
  have hcross : ∀ i j s, G i s * M j s = G j s * M i s := by
    intro i j s
    have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (fun s => G i s * M j s) =ᶠ[𝓝 (2 : ℂ)] fun s => G j s * M i s := by
      filter_upwards [hU.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
      rw [hGF i s hs, hGF j s hs]
      ring
    have hf : AnalyticOnNhd ℂ (fun s => G i s * M j s) univ :=
      fun z _ => ((hG i).mul (hM j)).analyticAt z
    have hg : AnalyticOnNhd ℂ (fun s => G j s * M i s) univ :=
      fun z _ => ((hG j).mul (hM i)).analyticAt z
    exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ _) h2
      (mem_univ s)
  choose w hw using hne
  have hZ : ∀ i s, M i s ≠ 0 → G (w s) s / M (w s) s = G i s / M i s := by
    intro i s hi
    rw [div_eq_div_iff (hw s) hi]
    exact hcross (w s) i s
  refine ⟨fun s => G (w s) s / M (w s) s, ?_, ?_, hZ⟩
  · intro s₀
    have hev : ∀ᶠ s in 𝓝 s₀, M (w s₀) s ≠ 0 :=
      (hM (w s₀)).continuous.continuousAt.eventually_ne (hw s₀)
    exact (((hG _) s₀).div ((hM _) s₀) (hw s₀)).congr_of_eventuallyEq
      (hev.mono fun s hs => hZ _ s hs)
  · intro s hs
    simp only
    rw [hGF _ s hs, mul_div_cancel_left₀ _ (hw s)]

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
open Filter Topology Set Asymptotics in
private theorem differentiable_mellin_of_support_in_Icc_pos {w : ℝ → ℂ} (hw : Continuous w) {a b : ℝ}
    (ha : 0 < a) (hab : ∀ y, w y ≠ 0 → a ≤ y ∧ y ≤ b) : Differentiable ℂ (mellin w) := by
  intro s
  have htop : w =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra h
    exact absurd (hab y h).2 (not_le.2 hy)
  have hzero : w =ᶠ[𝓝[>] 0] 0 := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra h
    exact absurd (hab y h).1 (not_le.2 hy.2)
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (hw.locallyIntegrable.locallyIntegrableOn _)
    ((isBigO_zero _ _).congr' htop.symm EventuallyEq.rfl) (by linarith)
    ((isBigO_zero _ _).congr' hzero.symm EventuallyEq.rfl) (by linarith)

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
open Filter Topology Set Asymptotics in
private theorem exists_weight_mellin_ne_zero (s₀ : ℂ) :
    ∃ w : ℝ → ℂ, ContDiff ℝ ∞ w ∧ (∃ a b : ℝ, 0 < a ∧ ∀ y, w y ≠ 0 → a ≤ y ∧ y ≤ b) ∧
      mellin w s₀ ≠ 0 := by
  let ψ : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hψ0 : ∀ y : ℝ, y ≤ 0 → ψ y = 0 := fun y hy => ψ.zero_of_le_dist (by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    show (1 : ℝ) ≤ _
    linarith)
  refine ⟨fun y => Complex.exp (-(s₀ - 1) * (Real.log y : ℂ)) * (ψ y : ℂ), ?_,
    ⟨1, 3, one_pos, ?_⟩, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport ψ
    · have hx0 : x ≠ 0 := by
        rintro rfl
        rw [ψ.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hx
        norm_num at hx
      have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => Complex.exp (-(s₀ - 1) * (Real.log y : ℂ))) x :=
        Complex.contDiff_exp.contDiffAt.comp x (contDiffAt_const.mul
          (ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.2 hx0)))
      exact h1.mul (ofRealCLM.contDiff.comp ψ.contDiff).contDiffAt
    · have hev : (fun y => Complex.exp (-(s₀ - 1) * (Real.log y : ℂ)) * (ψ y : ℂ)) =ᶠ[𝓝 x]
          fun _ => 0 :=
        (notMem_tsupport_iff_eventuallyEq.1 hx).mono fun y hy => by simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro y hy
    have hψy : ψ y ≠ 0 := fun h => hy (by simp [h])
    have hmem : y ∈ Metric.ball (2 : ℝ) 1 := by
      rw [← ψ.support_eq]
      exact hψy
    rw [Real.ball_eq_Ioo] at hmem
    constructor <;> linarith [hmem.1, hmem.2]
  · have hint : ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s₀ - 1) •
        (Complex.exp (-(s₀ - 1) * (Real.log y : ℂ)) * (ψ y : ℂ)) =
        ∫ y in Ioi (0 : ℝ), ((ψ y : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      simp only [smul_eq_mul]
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.2 (ne_of_gt hy)),
        ← Complex.ofReal_log (le_of_lt hy), ← mul_assoc, ← Complex.exp_add,
        show (Real.log y : ℂ) * (s₀ - 1) + -(s₀ - 1) * (Real.log y : ℂ) = 0 by ring,
        Complex.exp_zero, one_mul]
    unfold mellin
    rw [hint, integral_complex_ofReal, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y (hy : y ∉ Ioi (0 : ℝ)) => hψ0 y (not_lt.1 hy))]
    exact ofReal_ne_zero.2 ψ.integral_pos.ne'


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
open Filter Topology Set Asymptotics in
theorem _root_.GlobalTheory.idealCharacter_LSeries_continuation : ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (φ : mixedSpace K → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ I J, X (I * J) = X I * X J) → (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) → (∀ I, I ⊔ m ≠ ⊤ → X I = 0) → (∀ x y, φ (x * y) = φ x * φ y) → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) → ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} → (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ∧ ((∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → Z 1 = 0) := by
  intro K _ _ m X φ hm hX0 hXmul hXn hXz hφmul hφh hφs hφn hβ
  have hmain := _root_.GlobalTheory.smoothedSum_main_term_representatives K m X φ hm hX0 hXmul
    hXn hXz hφmul hφh hφs hφn hβ
  obtain ⟨hcount, hsum⟩ := _root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K
  haveI := hcount
  choose b hb using _root_.GlobalTheory.exists_integral_ideal_in_class_coprime K m hm
  have hbij : Function.Bijective fun c => ClassGroup.mk0 (b c) := by
    have : (fun c => ClassGroup.mk0 (b c)) = id := funext fun c => (hb c).1
    rw [this]
    exact Function.bijective_id
  have hbm : ∀ c, (b c : Ideal (𝓞 K)) ⊔ m = ⊤ := fun c => (hb c).2
  have hXle : ∀ I, ‖X I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · rw [hI, hX0, norm_zero]
      exact zero_le_one
    by_cases hIm : I ⊔ m = ⊤
    · rw [hXn I hI hIm]
    · rw [hXz I hIm, norm_zero]
      exact zero_le_one
  have hN : ∀ I, X I ≠ 0 → (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
    intro I hI
    have hI0 : I ≠ ⊥ := fun h => hI (h ▸ hX0)
    have : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hsumm : ∀ σ : ℝ, 1 < σ → Summable fun I => ‖X I‖ * (Ideal.absNorm I : ℝ) ^ (-σ) := by
    intro σ hσ
    refine ((hsum σ hσ).1).of_nonneg_of_le
      (fun I => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) fun I => ?_
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hXle I)
  set S := ∑ c, (X (b c : Ideal (𝓞 K)))⁻¹ with hS
  set F : ℂ → ℂ := fun s => (s - 1) * ∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) with hF
  have hweight : ∀ w : {w : ℝ → ℂ // ContDiff ℝ ∞ w ∧
      ∃ a b : ℝ, 0 < a ∧ ∀ y, w y ≠ 0 → a ≤ y ∧ y ≤ b},
      ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ s, 1 < s.re → G s = mellin w.1 s * F s) ∧
        ((∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → G 1 = 0) := by
    rintro ⟨w, hw, hwsupp⟩
    obtain ⟨κ, hκ⟩ := hmain w hw hwsupp
    obtain ⟨G, hGd, hG1, hGs⟩ := _root_.GlobalTheory.SmoothedSumMellin.exists_entire_mellin (Ideal (𝓞 K)) X
      (fun I => (Ideal.absNorm I : ℝ)) (κ * S) w hw hwsupp hN hsumm (hκ b hbij hbm)
    refine ⟨G, hGd, fun s hs => ?_, fun hJ => ?_⟩
    · rw [hGs s hs]
      simp only [F, Complex.ofReal_natCast]
    · rw [hG1]
      obtain ⟨J, hJ0, hJm, hXJ⟩ := hJ
      let J' : (Ideal (𝓞 K))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩
      let b' : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰ :=
        fun c => b (c * (ClassGroup.mk0 J')⁻¹) * J'
      have hb'mk : ∀ c, ClassGroup.mk0 (b' c) = c := by
        intro c
        simp only [b', map_mul, (hb _).1, inv_mul_cancel_right]
      have hbij' : Function.Bijective fun c => ClassGroup.mk0 (b' c) := by
        have : (fun c => ClassGroup.mk0 (b' c)) = id := funext hb'mk
        rw [this]
        exact Function.bijective_id
      have hbm' : ∀ c, (b' c : Ideal (𝓞 K)) ⊔ m = ⊤ := by
        intro c
        simp only [b', Submonoid.coe_mul]
        rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rw [sup_comm]; exact hbm _), sup_comm]
        exact hJm
      have hS' : ∑ c, (X (b' c : Ideal (𝓞 K)))⁻¹ = (X J)⁻¹ * S := by
        simp only [b', Submonoid.coe_mul, hXmul, mul_inv, hS, Finset.mul_sum]
        exact Fintype.sum_equiv (Equiv.mulRight (ClassGroup.mk0 J')⁻¹) _ _ fun c => by
          simp only [Equiv.coe_mulRight]
          ring
      have heq : κ * S = κ * ((X J)⁻¹ * S) := by
        obtain ⟨C, hC⟩ := hκ b hbij hbm 0
        obtain ⟨C', hC'⟩ := hκ b' hbij' hbm' 0
        rw [← hS']
        refine eq_of_norm_sub_div_le (f := fun t => ∑' I, X I * w (t * (Ideal.absNorm I : ℝ))) (C := C) (C' := C') (fun t h0 h1 => ?_) (fun t h0 h1 => ?_)
        · have := hC t h0 h1
          rwa [pow_zero, mul_one] at this
        · have := hC' t h0 h1
          rwa [pow_zero, mul_one] at this
      have hinv : (X J)⁻¹ ≠ 1 := fun h => hXJ (inv_eq_one.1 h)
      have h0 : κ * S * (1 - (X J)⁻¹) = 0 := by linear_combination heq
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h).symm hinv
  choose G hGd hGF hG1 using hweight
  obtain ⟨Z, hZd, hZF, hZdiv⟩ := exists_differentiable_eq_div_of_family (fun w => mellin w.1) G F
    (fun w => by
      obtain ⟨a, c, ha, hac⟩ := w.2.2
      exact differentiable_mellin_of_support_in_Icc_pos w.2.1.continuous ha hac)
    hGd hGF (fun s => by
      obtain ⟨w, hw, hws, hne⟩ := exists_weight_mellin_ne_zero s
      exact ⟨⟨w, hw, hws⟩, hne⟩)
  refine ⟨Z, hZd, hZF, fun hJ => ?_⟩
  obtain ⟨w, hw, hws, hne⟩ := exists_weight_mellin_ne_zero 1
  rw [hZdiv ⟨w, hw, hws⟩ 1 hne, hG1 _ hJ, zero_div]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdempotentAdelesAndSmallAdelicMatrices
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.SmallMat

open GlobalTheory.AdLat.Translate

theorem exists_dvd_pow_mul_coprime (N m : ℕ) (hm : m ≠ 0) :
    ∃ t k : ℕ, t.Coprime N ∧ m ∣ N ^ k * t := by
  induction m using induction_on_primes with
  | zero => exact absurd rfl hm
  | one => exact ⟨1, 0, by simp, by simp⟩
  | prime_mul p a hp ih =>
    obtain ⟨t, k, ht, h⟩ := ih (right_ne_zero_of_mul hm)
    by_cases hpN : p ∣ N
    · refine ⟨t, k + 1, ht, ?_⟩
      rw [pow_succ', mul_assoc]
      exact mul_dvd_mul hpN h
    · refine ⟨p * t, k, Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN) ht, ?_⟩
      rw [mul_left_comm]
      exact mul_dvd_mul_left p h

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem exists_indicator (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v ∈ S, e v = 1) ∧ ∀ v ∉ S, e v = 0 := by
  classical
  refine ⟨⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => ?_⟩,
    fun v hv => if_pos hv, fun v hv => if_neg hv⟩
  beta_reduce
  split_ifs
  · exact one_mem (v.adicCompletionIntegers F)
  · exact zero_mem (v.adicCompletionIntegers F)

theorem exists_nsmul_integral (b : FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ v, (m • b) v ∈ v.adicCompletionIntegers F := by
  obtain ⟨x, a, ha, rfl⟩ := exists_eq_algebraMap_add_nsmul F 1 one_pos b
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset F)
  have hc : IsIntegral ℤ (y • x) := hy x (by simp)
  have hc' : IsIntegral ℤ (y.natAbs • x) := by
    rcases Int.natAbs_eq y with h | h
    · have : y.natAbs • x = y • x := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact hc
    · have : y.natAbs • x = -(y • x) := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact hc.neg
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, fun v => ?_⟩
  rw [smul_add, ← map_nsmul]
  refine add_mem ?_ (nsmul_mem (nsmul_mem (ha v) 1) _)
  exact v.coe_mem_adicCompletionIntegers (K := F) (⟨y.natAbs • x, hc'⟩ : 𝓞 F)

theorem exists_coprime_nsmul_integral (N : ℕ) (b : FiniteAdeleRing (𝓞 F) F)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → b v = 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∀ v, (t • b) v ∈ v.adicCompletionIntegers F := by
  obtain ⟨m, hm, h⟩ := exists_nsmul_integral b
  obtain ⟨t, k, ht, c, hc⟩ := exists_dvd_pow_mul_coprime N m hm
  refine ⟨t, ht, fun v => ?_⟩
  change t • b v ∈ _
  by_cases hv : (N : 𝓞 F) ∈ v.asIdeal
  · rw [hb v hv, smul_zero]; exact zero_mem _
  · have h1 : c • (m • b v) ∈ v.adicCompletionIntegers F := nsmul_mem (h v) c
    rw [smul_smul, mul_comm, ← hc, mul_smul, nsmul_eq_mul,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, Nat.cast_pow, map_pow] at h1
    have hN : Valued.v ((N : ℕ) : v.adicCompletion F) = 1 := by
      have h1 := (v.valuation_eq_one_iff_notMem (K := F)).mpr hv
      have h2 := v.valuedAdicCompletion_eq_valuation' (K := F) ((N : ℕ) : F)
      have h3 : (algebraMap F (v.adicCompletion F)) ((N : ℕ) : F) =
        ((N : ℕ) : v.adicCompletion F) := map_natCast _ _
      rw [← h3]
      have h4 : (((N : ℕ) : 𝓞 F) : F) = ((N : ℕ) : F) :=
        map_natCast (algebraMap (𝓞 F) F) _
      exact h2.trans (h4 ▸ h1)
    rw [hN, one_pow, one_mul] at h1
    exact h1

theorem fm_add (A B : Matrix (Fin n) (Fin n) E) : fm F (A + B) = fm F A + fm F B := by
  ext i j
  simp [fm, TensorProduct.tmul_add]

theorem fm_zero : fm F (0 : Matrix (Fin n) (Fin n) E) = 0 := by
  ext i j
  simp [fm]

theorem nsmul_tmul_one (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) :
    ((d • a) ⊗ₜ[F] (1 : E) : RA F E) = d • (a ⊗ₜ[F] (1 : E) : RA F E) := by
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, succ_nsmul, TensorProduct.add_tmul, ih]

theorem exists_approx (S : Set (Fin n → E))
    (hS : ∀ M : Matrix (Fin n) (Fin n) (RA F E), ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F S, d • (M *ᵥ z) ∈ hat F S)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ) (hD : 0 < D) :
    ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F S, ∃ w ∈ hat F S, (M - fm F M₀) *ᵥ z = D • w := by
  let P : Matrix (Fin n) (Fin n) (RA F E) → Prop := fun M =>
    ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F S, ∃ w ∈ hat F S, (M - fm F M₀) *ᵥ z = D • w
  have hadd : ∀ A B, P A → P B → P (A + B) := by
    rintro A B ⟨A₀, hA⟩ ⟨B₀, hB⟩
    refine ⟨A₀ + B₀, fun z hz => ?_⟩
    obtain ⟨u, hu, hu'⟩ := hA z hz
    obtain ⟨w, hw, hw'⟩ := hB z hz
    refine ⟨u + w, add_mem hu hw, ?_⟩
    rw [smul_add, ← hu', ← hw', ← Matrix.add_mulVec, fm_add, add_sub_add_comm]
  have hzero : P 0 := ⟨0, fun z _ => ⟨0, zero_mem _, by simp [fm_zero]⟩⟩
  have hgen : ∀ (a : FiniteAdeleRing (𝓞 F) F) (B : Matrix (Fin n) (Fin n) E),
      P ((a ⊗ₜ[F] (1 : E) : RA F E) • fm F B) := by
    intro a B
    obtain ⟨d, hd, hB⟩ := hS (fm F B)
    obtain ⟨r, a', ha', rfl⟩ := exists_eq_algebraMap_add_nsmul F (D * d) (Nat.mul_pos hD hd) a
    refine ⟨r • B, fun z hz => ⟨_, hat_smul_int ha' (hB z hz), ?_⟩⟩
    have h1 : fm F (r • B) =
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) r ⊗ₜ[F] (1 : E) : RA F E) • fm F B := by
      ext i j
      simp only [fm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [h1, TensorProduct.add_tmul, add_smul, add_sub_cancel_left, Matrix.smul_mulVec,
      nsmul_tmul_one, smul_assoc, mul_smul, smul_comm d]
  have hsingle : ∀ i j (t : RA F E), P (Matrix.single i j t) := by
    intro i j t
    induction t using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact hzero
    | tmul a y =>
      have := hgen a (Matrix.single i j y)
      convert this using 1
      ext k l
      simp only [fm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Matrix.single_apply]
      split_ifs <;> simp
    | add s t hs ht => rw [Matrix.single_add]; exact hadd _ _ hs ht
  change P M
  rw [Matrix.matrix_eq_sum_single M]
  exact Finset.sum_induction _ P hadd hzero fun i _ =>
    Finset.sum_induction _ P hadd hzero fun j _ => hsingle i j _

theorem exists_coprime_small (S : Set (Fin n → E)) (N D : ℕ) (e : FiniteAdeleRing (𝓞 F) F)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (hD : 0 < D)
    (hM : ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F S, d • (M *ᵥ z) ∈ hat F S)
    (he : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F S, ∃ w ∈ hat F S,
      t • (((e ⊗ₜ[F] (1 : E) : RA F E) • M) *ᵥ z) = D • w := by
  obtain ⟨d, hd, hM⟩ := hM
  have hK : ((D * d : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hD hd).ne'
  set b : FiniteAdeleRing (𝓞 F) F :=
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ((D * d : ℕ) : F)⁻¹ * e with hb
  have hbe : e = (D * d) • b := by
    rw [hb, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)),
      ← map_mul, mul_inv_cancel₀ hK, map_one, one_mul]
  obtain ⟨t, ht, h⟩ := exists_coprime_nsmul_integral N b fun v hv => by
    change _ * e v = 0
    rw [he v hv, mul_zero]
  refine ⟨t, ht, fun z hz => ⟨_, hat_smul_int h (hM z hz), ?_⟩⟩
  rw [hbe, Matrix.smul_mulVec, nsmul_tmul_one, nsmul_tmul_one, smul_assoc, smul_assoc, mul_smul,
    smul_comm t D, smul_comm d]

end GlobalTheory.UnRep.SmallMat


open GlobalTheory.UnRep.SmallMat GlobalTheory.AdLat.Translate in
theorem GlobalTheory.UnRep.idempotent_adeles_small_matrices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ), ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v ∈ S, e v = 1) ∧ ∀ v ∉ S, e v = 0) ∧ (∀ M : Matrix (Fin n) (Fin n) (RA F E), ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), d • (M *ᵥ z) ∈ hat F (L : Set (Fin n → E))) ∧ (∀ (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), (M - fm F M₀) *ᵥ z = D • w) ∧ (∀ (N D : ℕ) (e : FiniteAdeleRing (𝓞 F) F) (M : Matrix (Fin n) (Fin n) (RA F E)), 0 < D → (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0) → ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), t • (((e ⊗ₜ[F] (1 : E)) • M) *ᵥ z) = D • w) ∧ ∀ (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ z ∈ hat F (L : Set (Fin n → E)), (a ⊗ₜ[F] (1 : E)) • z ∈ hat F (L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ n L hL hsp
  have h4 := (GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hL hsp).2.2.2
  have h2 := fun M : Matrix (Fin n) (Fin n) (RA F E) => exists_bound M hL h4
  exact ⟨exists_indicator, h2, exists_approx _ h2,
    fun N D e M hD he => exists_coprime_small _ N D e M hD (h2 M) he,
    fun a ha z hz => hat_smul_int ha hz⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsUnionSupPowersEqTopAtPlaces
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem sUnits_union_sup_finPow_eq_top :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → AdmP p F S → Disjoint S T → (∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F))) → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ := by
  intro p F _ _ _ S T hp hS hST hA
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS.1
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  have key : ∀ v ∈ T, ∃ w ∈ sUnits F S,
      w⁻¹ * (a * x) ∈ powSub p (algebraMap F (v.adicCompletion F)) ∧
        ∀ v' ∈ T, v' ≠ v → w ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
    intro v hv
    obtain ⟨u, hu, hnu, hu'⟩ := hA v hv
    obtain ⟨k, r, hr⟩ := _root_.GlobalTheory.CNorm.exists_eq_pow_mul_pow_of_unit p F v (algebraMap F (v.adicCompletion F) (u : F))
      (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)) hp (hS.2 v (hTS v hv))
      (by rw [hval]; exact (mem_sUnits F S u).1 hu v (hTS v hv))
      (by rw [hval]; exact hy v hv) (fun r h => hnu ⟨r, h⟩)
    refine ⟨u ^ k, pow_mem hu k, ⟨r, ?_⟩, fun v' hv' hne => pow_mem (hu' v' hv' hne) k⟩
    have hu0 : algebraMap F (v.adicCompletion F) (u : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, hr, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀,
      map_pow, inv_mul_cancel_left₀ (pow_ne_zero k hu0)]
  choose! w hwS hw1 hw2 using key
  have huU : ∏ v ∈ T, w v ∈ sUnits F (S ∪ T) := by
    refine prod_mem fun t ht => ?_
    rw [mem_sUnits]
    intro v hv
    exact (mem_sUnits F S _).1 (hwS t ht) v fun h => hv (Finset.mem_union_left _ h)
  have hsq : (∏ v ∈ T, w v)⁻¹ * (a * x) ∈ finPow p F T := by
    simp only [finPow, Subgroup.mem_iInf]
    intro v hv
    rw [← Finset.mul_prod_erase T w hv, mul_inv, mul_right_comm]
    refine mul_mem (hw1 v hv) (inv_mem (prod_mem fun t ht => ?_))
    exact hw2 t (Finset.mem_of_mem_erase ht) v hv (Finset.ne_of_mem_erase ht).symm
  have hx : x = ((∏ v ∈ T, w v) * a⁻¹) * ((∏ v ∈ T, w v)⁻¹ * (a * x)) := by
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, inv_mul_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup (mul_mem huU (inv_mem haU)) hsq

end GlobalTheory.CNorm
end

