module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.DetMEq
section
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

theorem detM_eq (Y : GT ι) (b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι)) :
    |b₀.toBasis.det Y.b| = 1 := by
  have hM : ∀ i k, ∃ m : ℤ, (Hf (Y.b i) (Y.b k)).im = m := fun i k =>
    Y.integral _ _ (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  choose m hm using hM
  have hG : lemSG Y.b = (Matrix.of m).map (Int.cast : ℤ → ℝ) := by
    ext i k; simp [lemSG, hm]
  obtain ⟨C, hC⟩ := lemSG_inv Y
  have h1 := congrArg Matrix.det hC
  rw [Matrix.det_mul, Matrix.det_one] at h1
  have h2 := h1
  rw [hG, ← Int.cast_det, ← Int.cast_det] at h2
  have h3 : C.det * (Matrix.of m).det = 1 := by exact_mod_cast h2
  have h4 : |(Matrix.of m).det| = 1 := by
    have h3' : (Matrix.of m).det * C.det = 1 := by rw [mul_comm]; exact h3
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h3' with h | h <;> rw [h] <;> rfl
  have h5 : |(lemSG Y.b).det| = 1 := by
    rw [hG, ← Int.cast_det, ← Int.cast_abs, h4, Int.cast_one]
  rw [lemSG_det Y.b b₀, abs_mul, abs_mul, lemSJ_det, one_mul] at h5
  have hd := abs_nonneg (b₀.toBasis.det Y.b)
  nlinarith

theorem vol_eq (Y : GT ι) : volume (ZSpan.fundamentalDomain Y.b) = 1 := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
    first
      | (rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
          finrank_euclideanSpace])
      | simp [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι)]
  let b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι) :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℂ ι)).reindex (finCongr hfr)
  rw [ZSpan.measure_fundamentalDomain Y.b volume b₀.toBasis, detM_eq Y b₀,
    measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀.toBasis volume),
    OrthonormalBasis.coe_toBasis, b₀.volume_parallelepiped]
  simp

theorem paU_pt {q c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a v : EuclideanSpace ℂ ι, ‖paU q a F v‖ ≤
      C * (1 + ‖v‖) ^ c * Real.exp ((q * Real.pi) * ‖v‖ ^ 2) *
        ((1 + ‖a‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) := by
  obtain ⟨C1, hC1, h1⟩ := paPoly_growth hF
  refine ⟨C1, hC1, fun a v => ?_⟩
  have hn := paU_norm_mul q a v F
  have hW : paW q v * Real.exp ((q * Real.pi) * ‖v‖ ^ 2) = 1 := by
    rw [paW, ← Real.exp_add]; simp
  have hE1 : Real.exp (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (q : ℝ) * Real.pi := by positivity
    nlinarith [sq_nonneg ‖v - (1 / 2 : ℂ) • a‖]
  have hva : 1 + ‖v - a‖ ≤ (1 + ‖v‖) * (1 + ‖a‖) := by
    nlinarith [norm_sub_le v a, norm_nonneg v, norm_nonneg a, mul_nonneg (norm_nonneg v) (norm_nonneg a)]
  have ha : (1 + ‖a‖) ^ c ≤ (1 + ‖a‖) ^ (2 * c) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg a]) (by omega)
  have E2 := Real.exp_pos (-(q * Real.pi) * ‖a‖ ^ 2 / 4)
  have EV := Real.exp_pos ((q * Real.pi) * ‖v‖ ^ 2)
  have hU : ‖paU q a F v‖ = (‖paU q a F v‖ * paW q v) * Real.exp ((q * Real.pi) * ‖v‖ ^ 2) := by
    rw [mul_assoc, hW, mul_one]
  rw [hU, hn]
  have k1 : ‖F (v - a)‖ ≤ C1 * ((1 + ‖v‖) ^ c * (1 + ‖a‖) ^ (2 * c)) := by
    refine (h1 _).trans (mul_le_mul_of_nonneg_left ?_ hC1)
    calc (1 + ‖v - a‖) ^ c ≤ ((1 + ‖v‖) * (1 + ‖a‖)) ^ c :=
          pow_le_pow_left₀ (by linarith [norm_nonneg (v - a)]) hva c
      _ = (1 + ‖v‖) ^ c * (1 + ‖a‖) ^ c := mul_pow _ _ _
      _ ≤ (1 + ‖v‖) ^ c * (1 + ‖a‖) ^ (2 * c) :=
          mul_le_mul_of_nonneg_left ha (by positivity)
  have hFn := norm_nonneg (F (v - a))
  have hE1p := Real.exp_pos (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2)
  calc ‖F (v - a)‖ * (Real.exp (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2) *
        Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) * Real.exp ((q * Real.pi) * ‖v‖ ^ 2)
      ≤ ‖F (v - a)‖ * (1 * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) *
          Real.exp ((q * Real.pi) * ‖v‖ ^ 2) := by gcongr
    _ ≤ C1 * ((1 + ‖v‖) ^ c * (1 + ‖a‖) ^ (2 * c)) * (1 * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) *
          Real.exp ((q * Real.pi) * ‖v‖ ^ 2) := by gcongr
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.IteratedFDerivTailZero
section
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

def expN (N : ℕ) (z : ℂ) : ℂ := ∑ n ∈ Finset.range (N + 1), z ^ n / (n.factorial : ℂ)

def gN (N : ℕ) (z : ℂ) : ℂ := cexp z - expN N z

theorem expN_hasDerivAt (N : ℕ) (z : ℂ) : HasDerivAt (expN (N + 1)) (expN N z) z := by
  induction N with
  | zero =>
    show HasDerivAt (expN 1) (expN 0 z) z
    have h0 : expN 1 = fun w => 1 + w := by
      funext w; simp [expN, Finset.sum_range_succ]
    have h1 : expN 0 z = 1 := by simp [expN]
    rw [h0, h1]
    exact (hasDerivAt_id z).const_add 1
  | succ N ih =>
    have hf : expN (N + 1 + 1) = fun w => expN (N + 1) w + w ^ (N + 1 + 1) / ((N + 1 + 1).factorial : ℂ) := by
      funext w; simp only [expN]; exact Finset.sum_range_succ _ (N + 1 + 1)
    rw [hf]
    have h2 := ih.add ((hasDerivAt_pow (N + 1 + 1) z).div_const ((N + 1 + 1).factorial : ℂ))
    refine h2.congr_deriv ?_
    have hf1 : ((N + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N + 1)
    have hne : ((N + 1 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (N + 1)
    simp only [expN, Finset.sum_range_succ _ (N + 1), Nat.factorial_succ (N + 1), Nat.add_sub_cancel]
    first
      | (congr 1; rw [Nat.cast_mul]; exact mul_div_mul_left _ _ hne)
      | (push_cast; field_simp; ring)
      | (push_cast; field_simp)

theorem contDiff_expN (N : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (expN N) := by
  unfold expN
  first
    | exact ContDiff.sum fun n _ => (contDiff_id.pow n).div_const _
    | fun_prop

theorem contDiff_gN (N : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (gN N) := by
  unfold gN
  exact Complex.contDiff_exp.sub (contDiff_expN N)

theorem deriv_gN (N : ℕ) : deriv (gN (N + 1)) = gN N := by
  funext z
  have h : HasDerivAt (gN (N + 1)) (cexp z - expN N z) z := by
    unfold gN
    exact (Complex.hasDerivAt_exp z).sub (expN_hasDerivAt N z)
  rw [h.deriv]
  rfl

theorem gN_zero (N : ℕ) : gN N 0 = 0 := by
  simp [gN, expN, Finset.sum_range_succ']

theorem iteratedDeriv_gN : ∀ i N : ℕ, i ≤ N → iteratedDeriv i (gN N) 0 = 0 := by
  intro i
  induction i with
  | zero => intro N _; rw [iteratedDeriv_zero]; exact gN_zero N
  | succ i ih =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [iteratedDeriv_succ', deriv_gN]
    exact ih M (by omega)

def ellL (q : ℕ) (a : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι →L[ℂ] ℂ :=
  ((q : ℂ) * (Real.pi : ℂ)) • innerSL ℂ a

theorem ellL_apply (q : ℕ) (a v : EuclideanSpace ℂ ι) : ellL q a v = q * Real.pi * Hf v a := by
  simp [ellL, Hf]
  left
  first
    | (rw [PiLp.inner_apply]; exact Finset.sum_congr rfl fun x _ => by simp [mul_comm])
    | (simp [PiLp.inner_apply, mul_comm]; done)
    | (simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]; done)

theorem iteratedFDeriv_tail_zero (q : ℕ) (a : EuclideanSpace ℂ ι) (N : ℕ) {P : EuclideanSpace ℂ ι → ℂ}
    (hP : ContDiff ℂ (⊤ : ℕ∞) P) {k : ℕ} (hk : k ≤ N) :
    iteratedFDeriv ℂ k (fun v => gN N (ellL q a v) * P v) 0 = 0 := by
  have hg : ContDiff ℂ (⊤ : ℕ∞) (fun v => gN N (ellL q a v)) := (contDiff_gN N).comp (ellL q a).contDiff
  have hz : ∀ i, i ≤ N → ‖iteratedFDeriv ℂ i (fun v => gN N (ellL q a v)) 0‖ = 0 := by
    intro i hi
    have h1 := (ellL q a).iteratedFDeriv_comp_right (contDiff_gN N) (0 : EuclideanSpace ℂ ι)
      (i := i) (by first | exact le_top | exact WithTop.coe_le_coe.mpr le_top | exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤) | simp)
    have h2 : iteratedFDeriv ℂ i (gN N) 0 = 0 := by
      rw [← norm_eq_zero, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_gN i N hi, norm_zero]
    rw [map_zero, h2] at h1
    rw [show (fun v => gN N (ellL q a v)) = gN N ∘ ellL q a from rfl, h1, norm_eq_zero]
    ext m
    simp
  refine norm_le_zero_iff.mp ((norm_iteratedFDeriv_mul_le hg hP 0
    (by first | exact le_top | simp | exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).trans_eq ?_)
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hz i (by have := Finset.mem_range.mp hi; omega)]
  simp

theorem paD_tail_zero (q : ℕ) (a : EuclideanSpace ℂ ι) (N : ℕ) {P : EuclideanSpace ℂ ι → ℂ}
    (hP : ContDiff ℂ (⊤ : ℕ∞) P) {α : ι →₀ ℕ} (hα : α.degree ≤ N) :
    paD α (fun v => gN N (ellL q a v) * P v) = 0 := by
  unfold paD polyDeriv
  refine Finset.sum_eq_zero fun m hm => ?_
  have hmα : m = α := by
    first
      | (simp [MvPolynomial.support_monomial] at hm; exact hm)
      | (rw [MvPolynomial.support_monomial] at hm; split_ifs at hm with h
         · simp at hm
         · simpa using hm)
  subst hmα
  have hk : Multiset.card (Finsupp.toMultiset m) ≤ N := by
    rw [Finsupp.card_toMultiset]
    first
      | exact hα
      | simpa [Finsupp.degree, Finsupp.sum] using hα
  rw [iteratedFDeriv_tail_zero q a N hP hk]
  simp

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaIPZeroRight
section
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

theorem paD_add (α : ι →₀ ℕ) {H1 H2 : EuclideanSpace ℂ ι → ℂ} (h1 : ContDiff ℂ (⊤ : ℕ∞) H1)
    (h2 : ContDiff ℂ (⊤ : ℕ∞) H2) : paD α (H1 + H2) = paD α H1 + paD α H2 := by
  unfold paD polyDeriv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_add_apply (h1.contDiffAt.of_le (by exact_mod_cast le_top))
    (h2.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp [mul_add]

theorem paD_smul (α : ι →₀ ℕ) (a : ℂ) {H : EuclideanSpace ℂ ι → ℂ}
    (h : ContDiff ℂ (⊤ : ℕ∞) H) : paD α (a • H) = a * paD α H := by
  unfold paD polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_const_smul_apply (h.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem paD_zero (α : ι →₀ ℕ) : paD α (0 : EuclideanSpace ℂ ι → ℂ) = 0 := by
  simp [paD, polyDeriv, iteratedFDeriv_fun_zero]

theorem paFact_ne (α : ι →₀ ℕ) : (paFact α : ℂ) ≠ 0 := by
  unfold paFact
  exact Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _)

theorem paJet_add (c : ℕ) {H1 H2 : EuclideanSpace ℂ ι → ℂ} (h1 : ContDiff ℂ (⊤ : ℕ∞) H1)
    (h2 : ContDiff ℂ (⊤ : ℕ∞) H2) : paJet c (H1 + H2) = paJet c H1 + paJet c H2 := by
  unfold paJet
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [paD_add α h1 h2, add_div, add_smul]

theorem paJet_smul (c : ℕ) (r : ℂ) {H : EuclideanSpace ℂ ι → ℂ} (h : ContDiff ℂ (⊤ : ℕ∞) H) :
    paJet c (r • H) = r • paJet c H := by
  unfold paJet
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [paD_smul α r h, mul_div_assoc, smul_smul]

theorem paJet_zero (c : ℕ) : paJet c (0 : EuclideanSpace ℂ ι → ℂ) = 0 := by
  unfold paJet
  simp [paD_zero]

theorem paJet_mono (c : ℕ) (m : ι →₀ ℕ) :
    paJet c (paMono m) = if m ∈ paS c then paMono m else 0 := by
  unfold paJet
  simp only [paD_mono]
  have e : ∀ α, ((if α = m then (paFact α : ℂ) else 0) / paFact α) • paMono α =
      if α = m then paMono m else 0 := fun α => by
    split_ifs with h
    · subst h
      rw [div_self (paFact_ne α), one_smul]
    · rw [zero_div, zero_smul]
  simp only [e]
  rw [Finset.sum_ite_eq']

theorem gaussianInner_zero_left (q : ℕ) (G : EuclideanSpace ℂ ι → ℂ) : paIP q 0 G = 0 := by
  simp [paIP]

theorem gaussianInner_zero_right (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : paIP q F 0 = 0 := by
  simp [paIP]

theorem gaussianInner_monomial_high {q c : ℕ} (hq : 1 ≤ q) {m : ι →₀ ℕ} (hm : m ∉ paS c)
    {G : EuclideanSpace ℂ ι → ℂ} (hG : G ∈ paPoly c) : paIP q (paMono m) G = 0 := by
  have hmm : paMono m ∈ paPoly (ι := ι) (max c m.degree) :=
    paMono_mem (mem_paS.2 (le_max_right _ _))
  have hup : paPoly (ι := ι) c ≤ paPoly (max c m.degree) := paPoly_mono (le_max_left _ _)
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact gaussianInner_monomial_orthogonal q (by rintro rfl; exact hm hβ)
  | zero => exact gaussianInner_zero_right q _
  | add x y hx hy ihx ihy =>
    rw [gaussianInner_conj_symm q (x + y) (paMono m), gaussianInner_add_left hq (hup hx) (hup hy) hmm, map_add (f := _),
      ← gaussianInner_conj_symm, ← gaussianInner_conj_symm, ihx, ihy, add_zero]
  | smul r x hx ihx =>
    rw [gaussianInner_conj_symm q (r • x) (paMono m), gaussianInner_smul_left, map_mul, ← gaussianInner_conj_symm, ihx, mul_zero]

theorem gaussianInner_polynomial_jet {q c d : ℕ} (hq : 1 ≤ q) {S G : EuclideanSpace ℂ ι → ℂ} (hS : S ∈ paPoly d)
    (hG : G ∈ paPoly c) : paIP q S G = paIP q (paJet c S) G := by
  have hupd : paPoly (ι := ι) d ≤ paPoly (max d c) := paPoly_mono (le_max_left _ _)
  have hupc : paPoly (ι := ι) c ≤ paPoly (max d c) := paPoly_mono (le_max_right _ _)
  induction hS using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [paJet_mono]
    split_ifs with h
    · rfl
    · rw [gaussianInner_monomial_high hq h hG, gaussianInner_zero_left]
  | zero => rw [paJet_zero]
  | add x y hx hy ihx ihy =>
    rw [paJet_add c (paPoly_contDiff hx) (paPoly_contDiff hy),
      gaussianInner_add_left hq (hupd hx) (hupd hy) (hupc hG),
      gaussianInner_add_left hq (hupc (paJet_mem c x)) (hupc (paJet_mem c y)) (hupc hG), ihx, ihy]
  | smul r x hx ihx =>
    rw [paJet_smul c r (paPoly_contDiff hx), gaussianInner_smul_left, gaussianInner_smul_left, ihx]

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

