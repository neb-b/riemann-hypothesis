module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LocalAlgebraPowers
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LocalAlgebraPowers

theorem pad_self {k : ℕ} (l : Fin k → ℤ) : pad k l = l := by
  funext a
  simp [pad, a.2]

theorem rhoPair_pad {m k : ℕ} (hkm : k ≤ m) (l : Fin k → ℤ) :
    rhoPair (pad m l) = rhoPair l + ((m : ℤ) - k) * ∑ i, l i := by
  obtain ⟨d, rfl⟩ : ∃ d, m = k + d := ⟨m - k, by omega⟩
  simp only [rhoPair, pad, Fin.sum_univ_add, Fin.coe_castAdd, Fin.coe_natAdd, Fin.is_lt, dif_pos]
  simp only [show ∀ j : Fin d, ¬ (k + (j : ℕ) < k) from fun j => by omega, dif_neg, not_false_eq_true,
    mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem antitone_pad {m k : ℕ} (hkm : k < m) (l : Fin k → ℤ) :
    Antitone (pad m l) ↔ Antitone l ∧ ∀ i, 0 ≤ l i := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := h (show (⟨i, by omega⟩ : Fin m) ≤ ⟨j, by omega⟩ from hij)
      simpa [pad, i.isLt, j.isLt] using this
    · have := h (show (⟨i, by omega⟩ : Fin m) ≤ ⟨k, hkm⟩ from Fin.mk_le_mk.mpr i.isLt.le)
      simpa [pad, i.isLt] using this
  · rintro ⟨hl, h0⟩ a b hab
    have hab' : (a : ℕ) ≤ b := hab
    by_cases hb : (b : ℕ) < k
    · have ha : (a : ℕ) < k := lt_of_le_of_lt hab' hb
      simp only [pad, ha, hb, dif_pos]
      exact hl (Fin.mk_le_mk.mpr hab')
    · simp only [pad, hb, dif_neg, not_false_eq_true]
      split_ifs
      · exact h0 _
      · exact le_rfl

theorem antitone_pad_iff {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (l : Fin k → ℤ) (hl : Antitone l)
    (h : k < m ∨ ∀ i : Fin k, (i : ℕ) + 1 = k → 0 ≤ l i) : Antitone (pad m l) ↔ ∀ i, 0 ≤ l i := by
  rcases lt_or_eq_of_le hkm with hlt | heq
  · rw [antitone_pad hlt l]
    simp [hl]
  · subst heq
    have h' := h.resolve_left (lt_irrefl _)
    have hall : ∀ i, 0 ≤ l i := by
      intro i
      have hlast : 0 ≤ l ⟨k - 1, by omega⟩ := h' _ (by simp; omega)
      exact le_trans hlast (hl (Fin.mk_le_mk.mpr (by omega)))
    rw [pad_self]
    exact ⟨fun _ => hall, fun _ => hl⟩

variable {E : Type} [Field E] [NumberField E] {S : Finset (Pl E)}

theorem nq_pos (w : Off E S) : 0 < nq w := by
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [nq, Ideal.absNorm_eq_zero_iff] at h
  exact w.1.ne_bot h

theorem qF_eq' (w : Off E S) : qF (w.1.adicCompletion E) = nq w := PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.qF_eq w.1

theorem sqrtQ_eq (w : Off E S) :
    sqrtQ (w.1.adicCompletion E) = Complex.exp ((Real.log (nq w) / 2 : ℝ)) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [sqrtQ, qF_eq', ← Complex.ofReal_exp]
  norm_cast
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
  congr 1
  ring

theorem conj_sqrtQ_zpow (w : Off E S) (j : ℤ) :
    conj (sqrtQ (w.1.adicCompletion E) ^ j) = sqrtQ (w.1.adicCompletion E) ^ j := by
  rw [map_zpow₀]
  congr 1
  simp [sqrtQ, Complex.conj_ofReal]

theorem cast_eq_exp (w : Off E S) : (nq w : ℂ) = Complex.exp (Real.log (nq w)) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_exp, Real.exp_log hpos]

theorem cpow_eq (w : Off E S) (z : ℂ) : (nq w : ℂ) ^ z = Complex.exp (Real.log (nq w) * z) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (nq_pos w).ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hpos.le]

theorem zpow_eq (w : Off E S) (j : ℤ) : (nq w : ℂ) ^ j = Complex.exp (j * Real.log (nq w)) := by
  rw [cast_eq_exp, ← Complex.exp_int_mul]

theorem sqrt_zpow_eq (w : Off E S) (j : ℤ) :
    sqrtQ (w.1.adicCompletion E) ^ j = Complex.exp (j * (Real.log (nq w) / 2 : ℝ)) := by
  rw [sqrtQ_eq, ← Complex.exp_int_mul]

theorem rpow_cpow_eq (w : Off E S) (N : ℤ) (z : ℂ) :
    ((((nq w : ℝ) ^ N : ℝ)) : ℂ) ^ z = Complex.exp ((N * Real.log (nq w) : ℝ) * z) := by
  have hq : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  have hx : (0 : ℝ) < (nq w : ℝ) ^ N := zpow_pos hq N
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le, Real.log_zpow]

theorem local_inputs_from_literature {m k : ℕ} (q : ℕ) (α : Fin m → ℂˣ) (β : Fin k → ℂˣ) (s : ℂ) (l : Fin k → ℤ) :
    loc q α β s l = loc q α β 0 l * (q : ℂ) ^ (-s * ((∑ i, l i : ℤ) : ℂ)) := by
  unfold loc
  split_ifs <;> simp

end LocalAlgebraPowers

open LocalAlgebraPowers in
theorem localHeckeAlgebra_statement : LocalHeckeAlgebra := by
  intro E _ _ S m k α α' w χ hχ hk hkm
  have hψ := hχ.1
  have hq : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  refine ⟨?_, fun l => ⟨fun s => ?_, fun hcase => ?_, fun hneg => ?_⟩⟩
  · have hp : pad m (0 : Fin k → ℤ) = 0 := by
      funext a
      simp [pad]
    have hA : Antitone (0 : Fin k → ℤ) ∧ ∀ i, 0 ≤ (0 : Fin k → ℤ) i :=
      ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩
    simp only [aLoc, loc, if_pos hA, hp, halfModulus_zero, schur_zero, map_one, Pi.zero_apply,
      Finset.sum_const_zero, Int.cast_zero, mul_zero, neg_zero, Complex.cpow_zero, one_pow, mul_one]
    simp [hA.1]
  · have key : ∀ a b c d g : ℂ, a + 2 * b + c + d = g → ∀ L : ℂ,
        Complex.exp a * (Complex.exp b ^ 2 * Complex.exp c * L * Complex.exp d) = L * Complex.exp g := by
      intro a b c d g h L
      rw [← h, Complex.exp_add, Complex.exp_add, Complex.exp_add, two_mul, Complex.exp_add]
      ring
    rw [local_inputs_from_literature]
    simp only [aLoc, halfModulus_eq]
    rw [rpow_cpow_eq, sqrt_zpow_eq, zpow_eq, cpow_eq, cpow_eq]
    refine key _ _ _ _ _ ?_ _
    push_cast
    ring
  · rw [sphericalWhittaker_torusPow hψ, sphericalWhittaker_torusPow hψ]
    by_cases hA : Antitone l ∧ ∀ i, 0 ≤ l i
    · have hpA : Antitone (pad m l) := (antitone_pad_iff hk hkm l hA.1 hcase).mpr hA.2
      have hfac : halfModulus (w.1.adicCompletion E) (pad m l) * conj (halfModulus (w.1.adicCompletion E) l) =
          halfModulus (w.1.adicCompletion E) l ^ 2 *
            (nq w : ℂ) ^ (-(((m : ℂ) - k) / 2) * ((∑ i, l i : ℤ) : ℂ)) := by
        rw [halfModulus_eq, halfModulus_eq, rhoPair_pad hkm, conj_sqrtQ_zpow, sqrt_zpow_eq, sqrt_zpow_eq,
          cpow_eq, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [if_pos hpA, if_pos hA.1]
      simp only [aLoc, loc, if_pos hA, neg_zero, zero_mul, Complex.cpow_zero, mul_one, map_mul]
      linear_combination ((evalAt (α w)) (schur (pad m l)) * conj ((evalAt (α' w)) (schur l))) * hfac
    · have hR : aLoc α α' w l = 0 := by
        simp only [aLoc, loc, if_neg hA, mul_zero]
      rw [hR]
      by_cases hl : Antitone l
      · have hpA : ¬ Antitone (pad m l) := fun h => hA ⟨hl, (antitone_pad_iff hk hkm l hl hcase).mp h⟩
        rw [if_neg hpA, zero_mul]
      · rw [if_neg hl, map_zero, mul_zero]
  · have hA : ¬ (Antitone l ∧ ∀ i, 0 ≤ l i) := by
      rintro ⟨-, h⟩
      obtain ⟨i, hi⟩ := hneg
      exact absurd (h i) (not_le.mpr hi)
    simp only [aLoc, loc, if_neg hA, mul_zero]

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LogBallEstimates
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LogBallEstimates

theorem neg_log_le {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) : -Real.log t ≤ t ^ (-ε) / ε := by
  have := Real.log_le_rpow_div (inv_pos.2 ht).le hε
  rwa [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this

theorem large_power_bound {t σ c C : ℝ} {M : ℕ} (ht : 1 ≤ t) (hM : σ + 1 ≤ M) (hc : 0 ≤ c)
    (h : c ≤ C * (t ^ M)⁻¹) : c * t ^ σ ≤ |C| * min t t⁻¹ ^ (1 : ℝ) := by
  have t0 : 0 < t := by linarith
  rw [min_eq_right ((inv_le_one_of_one_le₀ ht).trans ht), Real.rpow_one]
  have h1 : t ^ σ * t ≤ t ^ M := by
    rw [← Real.rpow_add_one t0.ne', ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht hM
  have hp : 0 < t ^ M := by positivity
  have h2 : c ≤ |C| * (t ^ M)⁻¹ := h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h3 : t ^ σ ≤ t ^ M * t⁻¹ := by
    rw [le_mul_inv_iff₀ t0]; exact h1
  calc c * t ^ σ ≤ |C| * (t ^ M)⁻¹ * t ^ σ := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = |C| * ((t ^ M)⁻¹ * t ^ σ) := by ring
    _ ≤ |C| * ((t ^ M)⁻¹ * (t ^ M * t⁻¹)) := by gcongr
    _ = |C| * t⁻¹ := by field_simp

theorem big_log {t σ c C : ℝ} {M : ℕ} (ht : 1 ≤ t) (hM : σ + 2 ≤ M) (hc : 0 ≤ c)
    (h : c ≤ C * (t ^ M)⁻¹) : c * t ^ σ * |Real.log t| ≤ |C| * min t t⁻¹ ^ (1 : ℝ) := by
  have t0 : 0 < t := by linarith
  have hl : |Real.log t| ≤ t := by
    rw [abs_of_nonneg (Real.log_nonneg ht)]; linarith [Real.log_le_sub_one_of_pos t0]
  calc c * t ^ σ * |Real.log t| ≤ c * t ^ σ * t := by gcongr
    _ = c * t ^ (σ + 1) := by rw [Real.rpow_add_one t0.ne']; ring
    _ ≤ _ := large_power_bound ht (by linarith) hc h

theorem small_power_bound {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b ≤ |C| * t ^ (2 * ε) := by
  have h2 : c ≤ |C| * t := h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) t0.le)
  calc c * t ^ b ≤ |C| * t * t ^ b := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = |C| * t ^ (b + 1) := by rw [Real.rpow_add_one t0.ne']; ring
    _ ≤ |C| * t ^ (2 * ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge t0 t1.le hb) (abs_nonneg _)

theorem small0 {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b ≤ |C| * (1 + ε⁻¹) * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  have h1 := small_power_bound t0 t1 hε hb hc h
  have h2 : t ^ (2 * ε) ≤ t ^ ε := Real.rpow_le_rpow_of_exponent_ge t0 t1.le (by linarith)
  have h3 : 0 ≤ |C| * t ^ ε * ε⁻¹ := by positivity
  calc c * t ^ b ≤ |C| * t ^ ε := h1.trans (by gcongr)
    _ ≤ |C| * t ^ ε + |C| * t ^ ε * ε⁻¹ := by linarith
    _ = |C| * (1 + ε⁻¹) * t ^ ε := by ring

theorem small_log {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b * |Real.log t| ≤ |C| * (1 + ε⁻¹) * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  have h1 := small_power_bound t0 t1 hε hb hc h
  have hl : |Real.log t| ≤ t ^ (-ε) / ε := by
    rw [abs_of_neg (Real.log_neg t0 t1)]; exact neg_log_le t0 hε
  have e : t ^ (2 * ε) * (t ^ (-ε) / ε) = t ^ ε * ε⁻¹ := by
    rw [mul_div_assoc', ← Real.rpow_add t0, div_eq_mul_inv]; ring_nf
  have h3 : 0 ≤ |C| * t ^ ε := by positivity
  calc c * t ^ b * |Real.log t| ≤ |C| * t ^ (2 * ε) * (t ^ (-ε) / ε) := by
        gcongr
    _ = |C| * t ^ ε * ε⁻¹ := by rw [mul_assoc, e]; ring
    _ ≤ |C| * t ^ ε + |C| * t ^ ε * ε⁻¹ := by linarith
    _ = |C| * (1 + ε⁻¹) * t ^ ε := by ring

theorem bddBelow_support_primePowerComponent_coeff {t ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hc : 0 ≤ c) (h : c ≤ C) :
    c * t ^ ε ≤ |C| * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  exact mul_le_mul_of_nonneg_right (h.trans (le_abs_self C)) (by positivity)

theorem re_lt_of_ball {s s₀ : ℂ} {r : ℝ} (hs : s ∈ Metric.ball s₀ r) : |s.re - s₀.re| < r := by
  rw [Metric.mem_ball, dist_eq_norm] at hs
  rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans_lt hs

variable {X : Type*} [MeasurableSpace X]

theorem intg (ν : Measure X) (D : X → ℝ) (hD : ∀ x, 0 < D x) (hDm : Measurable D) (F : X → ℂ)
    (hF : AEStronglyMeasurable F ν) (s : ℂ) (g : X → ℝ) (hg : Integrable g ν)
    (h0 : ∀ᵐ x ∂ν, ‖F x‖ * D x ^ s.re ≤ g x) : Integrable (fun x => F x * (D x : ℂ) ^ s) ν :=
  hg.mono' (hF.mul ((Complex.measurable_ofReal.comp hDm).pow_const s).aestronglyMeasurable)
    (h0.mono fun x hx => by rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hD x)]; exact hx)

theorem diffAt (ν : Measure X) (D : X → ℝ) (hD : ∀ x, 0 < D x) (hDm : Measurable D) (F : X → ℂ)
    (hF : AEStronglyMeasurable F ν) (s₀ : ℂ) (r : ℝ) (hr : 0 < r) (g : X → ℝ) (hg : Integrable g ν)
    (h0 : ∀ᵐ x ∂ν, ‖F x‖ * D x ^ s₀.re ≤ g x)
    (hb : ∀ᵐ x ∂ν, ∀ s ∈ Metric.ball s₀ r, ‖F x‖ * D x ^ s.re * |Real.log (D x)| ≤ g x) :
    DifferentiableAt ℂ (fun s => ∫ x, F x * (D x : ℂ) ^ s ∂ν) s₀ := by
  have hDc : Measurable fun x => (D x : ℂ) := Complex.measurable_ofReal.comp hDm
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => F x * (D x : ℂ) ^ s) ν := fun s =>
    hF.mul (hDc.pow_const s).aestronglyMeasurable
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := ν)
    (F := fun s x => F x * (D x : ℂ) ^ s) (F' := fun s x => F x * ((D x : ℂ) ^ s * Complex.log (D x)))
    (x₀ := s₀) (bound := g) (Metric.ball_mem_nhds s₀ hr) (Filter.Eventually.of_forall fun s => hmeas s)
    (intg ν D hD hDm F hF s₀ g hg h0)
    (hF.mul ((hDc.pow_const s₀).mul (Complex.measurable_log.comp hDc)).aestronglyMeasurable)
    (hb.mono fun x hx s hs => by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hD x), ← Complex.ofReal_log (hD x).le,
        Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
      exact hx s hs)
    hg
    (Filter.Eventually.of_forall fun x s _ =>
      ((Complex.hasStrictDerivAt_const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (hD x).ne'))).hasDerivAt.const_mul (F x)))
  exact this.2.differentiableAt

end LogBallEstimates

open LogBallEstimates in
theorem duality_diagonalClass_of_affineProperBaseChange : D0 → V1 → E1 → E2 := by
  intro hD0 hV1 hE1 E _ _ _ k μ _ hk β hβ H H₀ hG
  obtain ⟨hpos, -, hcont, -⟩ := hD0 E k
  have hmin := (hV1 E k μ hk β hβ).2.2
  have hE := hE1 E k μ hk β hβ H₀ hG.meas₀ hG.inv₀ hG.cen hG.bdd
  have hDm : Measurable (Dt : GA E k → ℝ) := hcont.measurable
  have hS : MeasurableSet {g : GA E k | Dt g < 1} := measurableSet_lt hDm measurable_const
  obtain ⟨C₀, hC₀⟩ := hG.bdd
  obtain ⟨C₁, hC₁⟩ := hG.small
  have hFm : Measurable fun g => (Dt g : ℂ) * H g - H₀ g :=
    ((Complex.measurable_ofReal.comp hDm).mul hG.meas).sub hG.meas₀

  have hAb : ∀ (σ : ℝ), ∃ g : GA E k → ℝ, IntegrableOn g {g | Dt g < 1}ᶜ (μ.withDensity β) ∧
      ∀ x, x ∈ {g : GA E k | Dt g < 1}ᶜ → ∀ τ, τ ≤ σ →
        ‖H x‖ * Dt x ^ τ ≤ g x ∧ ‖H x‖ * Dt x ^ τ * |Real.log (Dt x)| ≤ g x := by
    intro σ
    obtain ⟨C, hC⟩ := hG.big (⌈σ⌉₊ + 2)
    refine ⟨fun x => |C| * min (Dt x) (Dt x)⁻¹ ^ (1 : ℝ), ((hmin 1 one_pos).const_mul |C|).integrableOn,
      fun x hx τ hτ => ?_⟩
    have h1 : 1 ≤ Dt x := not_lt.1 hx
    have hM : τ + 2 ≤ ((⌈σ⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith [Nat.le_ceil σ]
    exact ⟨large_power_bound h1 (by linarith) (norm_nonneg _) (hC x h1), big_log h1 hM (norm_nonneg _) (hC x h1)⟩
  have hBb : ∀ ε : ℝ, 0 < ε → ∃ g : GA E k → ℝ, IntegrableOn g {g | Dt g < 1} (μ.withDensity β) ∧
      ∀ x, x ∈ {g : GA E k | Dt g < 1} → ∀ b, 2 * ε ≤ b + 1 →
        ‖(Dt x : ℂ) * H x - H₀ x‖ * Dt x ^ b ≤ g x ∧
          ‖(Dt x : ℂ) * H x - H₀ x‖ * Dt x ^ b * |Real.log (Dt x)| ≤ g x := by
    intro ε hε
    refine ⟨fun x => |C₁| * (1 + ε⁻¹) * min (Dt x) (Dt x)⁻¹ ^ ε,
      ((hmin ε hε).const_mul (|C₁| * (1 + ε⁻¹))).integrableOn, fun x hx b hb => ?_⟩
    have h1 : Dt x < 1 := hx
    exact ⟨small0 (hpos x) h1 hε hb (norm_nonneg _) (hC₁ x h1),
      small_log (hpos x) h1 hε hb (norm_nonneg _) (hC₁ x h1)⟩
  let κ : ℂ := ((k : ℂ) * Module.finrank ℚ E)⁻¹ * ∫ g in band E k, H₀ g ∂μ.withDensity β
  let A : ℂ → ℂ := fun s => ∫ g in {g | Dt g < 1}ᶜ, H g * (Dt g : ℂ) ^ s ∂μ.withDensity β
  let B : ℂ → ℂ := fun s => ∫ g in {g | Dt g < 1}, ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1)
    ∂μ.withDensity β
  have hA : ∀ s₀ : ℂ, DifferentiableAt ℂ A s₀ := by
    intro s₀
    obtain ⟨g, hg, hgb⟩ := hAb (s₀.re + 1)
    refine diffAt _ Dt hpos hDm H hG.meas.aestronglyMeasurable s₀ 1 one_pos g hg ?_ ?_
    · exact (ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx => (hgb x hx _ (by linarith)).1)
    · exact (ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx s hs =>
        (hgb x hx _ (by linarith [(abs_lt.1 (re_lt_of_ball hs)).2])).2)
  have hB : ∀ s₀ : ℂ, 0 < s₀.re → DifferentiableAt ℂ B s₀ := by
    intro s₀ h0
    obtain ⟨g, hg, hgb⟩ := hBb (s₀.re / 4) (by linarith)
    have := diffAt _ Dt hpos hDm _ hFm.aestronglyMeasurable (s₀ - 1) (s₀.re / 2) (by linarith) g hg
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
        (hgb x hx _ (by rw [Complex.sub_re, Complex.one_re]; linarith)).1))
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx s hs =>
        (hgb x hx _ (by
          have := (abs_lt.1 (re_lt_of_ball hs)).1
          rw [Complex.sub_re, Complex.one_re] at this; linarith)).2))
    have h2 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s₀ := differentiableAt_id.sub_const 1
    have h3 := DifferentiableAt.comp s₀ this h2
    exact h3
  refine ⟨fun s => (s - 1) * (A s + B s) + κ, fun s hs => ?_, fun s hs => ?_, fun hb => ?_⟩
  · have h2 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s := differentiableAt_id.sub_const 1
    exact (h2.mul ((hA s).add (hB s hs))).add_const κ |>.differentiableWithinAt
  · obtain ⟨gA, hgA, hgAb⟩ := hAb s.re
    obtain ⟨gB, hgB, hgBb⟩ := hBb (1 / 2) (by norm_num)
    have i1 : IntegrableOn (fun g => H g * (Dt g : ℂ) ^ s) {g | Dt g < 1}ᶜ (μ.withDensity β) :=
      intg _ Dt hpos hDm H hG.meas.aestronglyMeasurable s gA hgA
        ((ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx => (hgAb x hx _ le_rfl).1))
    have i2 : IntegrableOn (fun g => ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1)) {g | Dt g < 1}
        (μ.withDensity β) :=
      intg _ Dt hpos hDm _ hFm.aestronglyMeasurable (s - 1) gB hgB
        ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
          (hgBb x hx _ (by rw [Complex.sub_re, Complex.one_re]; linarith)).1))
    have hs1 : 0 < (s - 1).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have i3 : IntegrableOn (fun g => H₀ g * (Dt g : ℂ) ^ (s - 1)) {g | Dt g < 1} (μ.withDensity β) :=
      intg _ Dt hpos hDm _ hG.meas₀.aestronglyMeasurable (s - 1) _
        ((hmin _ hs1).const_mul |C₀|).integrableOn
        ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
          bddBelow_support_primePowerComponent_coeff (hpos x) hx (norm_nonneg _) (hC₀ x)))
    have hid : ∀ g, H g * (Dt g : ℂ) ^ s =
        ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1) + H₀ g * (Dt g : ℂ) ^ (s - 1) := by
      intro g
      have h0 : (Dt g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos g).ne'
      rw [Complex.cpow_sub _ _ h0, Complex.cpow_one]
      field_simp
      ring
    have i4 : IntegrableOn (fun g => H g * (Dt g : ℂ) ^ s) {g | Dt g < 1} (μ.withDensity β) := by
      simp_rw [hid]; exact i2.add i3
    have hint : Integrable (fun g => H g * (Dt g : ℂ) ^ s) (μ.withDensity β) := by
      have := i4.union i1
      rwa [Set.union_compl_self, integrableOn_univ] at this
    have hE' := hE (s - 1) hs1
    rw [← integral_add_compl hS hint]
    have hsplit : ∫ g in {g | Dt g < 1}, H g * (Dt g : ℂ) ^ s ∂μ.withDensity β =
        B s + ∫ g in {g | Dt g < 1}, H₀ g * (Dt g : ℂ) ^ (s - 1) ∂μ.withDensity β := by
      simp_rw [hid]; exact integral_add i2 i3
    rw [hsplit]
    show (s - 1) * (A s + B s) + κ = _
    linear_combination -hE'
  · show (1 - 1) * (A 1 + B 1) + κ = 0
    simp only [sub_self, zero_mul, zero_add, κ, hb, mul_zero]

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.RhoSigmaFinite
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace RhoSigmaFinite

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem uu_eq_one {u : GA E k} {j : ℕ} (hj : k ≤ j) (hu : UU j u) : u = 1 :=
  Units.ext <| Matrix.ext fun i c => by rw [hu.2.2 i c (by omega), Units.val_one]


variable (E k) in
def rho : Measure (GA E k) := Measure.sum fun ξ : RowT E k k => Measure.dirac (ratGL E k (gam ξ))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem rho_sFinite [Countable (RowT E k k)] : SFinite (rho E k) := by
  rw [rho]; infer_instance

omit [_root_.NumberField.IsTotallyComplex E] in
theorem lint_rho (F : GA E k → ℝ≥0∞) : ∫⁻ r, F r ∂rho E k = ∑' ξ : RowT E k k, F (ratGL E k (gam ξ)) := by
  rw [rho, lintegral_sum_measure]
  simp only [lintegral_dirac]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem int_rho (Φ : GA E k → ℂ) (hΦ : Measurable Φ) (g : GA E k) :
    ∫ r, Φ (r * g) ∂rho E k = sumF Φ g := by
  by_cases hi : Integrable (fun r => Φ (r * g)) (rho E k)
  · rw [rho, integral_sum_measure hi, sumF]
    simp only [integral_dirac]
  · rw [integral_undef hi, sumF, tsum_eq_zero_of_not_summable]
    intro hs
    apply hi
    refine ⟨(hΦ.comp (measurable_mul_const g)).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lint_rho]
    have h1 : Summable fun ξ : RowT E k k => ‖Φ (ratGL E k (gam ξ) * g)‖₊ :=
      NNReal.summable_coe.mp (by simpa using hs.norm)
    have h2 := ENNReal.tsum_coe_ne_top_iff_summable.mpr h1
    simpa [enorm_eq_nnnorm] using h2.lt_top

end RhoSigmaFinite

open RhoSigmaFinite in
set_option synthInstance.maxHeartbeats 400000 in
theorem unipotent_integral_of : Q1 → Q2 → N0 → N3 → CosetIntegralParabolic → U0 := by
  intro hQ1 hQ2 hN0 hN3 hN4a E _ _ _ k μ _ hk β hβ
  have : Countable (RowT E k k) := (hN0 E k k hk le_rfl).2.2.2.2.2.2.1
  have : SFinite (rho E k) := rho_sFinite
  obtain ⟨hsf, hinv, hae⟩ := (hN3 E k).1 (k - 1) (by omega)
  have key : ∀ g, ∑' ξ : RowT E k k, ∫⁻ h, β ((ratGL E k (gam ξ))⁻¹ * h * g) ∂nuP E k (k - 1) = 1 := by
    intro g
    rw [← hN4a E k k hk le_rfl (fun h => β (h * g)) (hβ.1.comp (measurable_mul_const g))]
    exact hβ.2 g
  set β' : GA E k → ℝ≥0∞ := fun g => ∑' ξ : RowT E k k, β ((ratGL E k (gam ξ))⁻¹ * g) with hβ'
  have hwt : IsWt (nuP E k (k - 1)) β' := by
    refine ⟨Measurable.tsum fun ξ => hβ.1.comp (measurable_const_mul _), fun g => ?_⟩
    simp only [hβ']
    rw [lintegral_tsum (f := fun ξ h => β ((ratGL E k (gam ξ))⁻¹ * (h * g)))
      fun ξ => (hβ.1.comp ((measurable_const_mul _).comp (measurable_mul_const g))).aemeasurable]
    simpa only [mul_assoc] using key g
  have hH : ∀ᵐ h ∂nuP E k (k - 1), h ∈ {x : GA E k | ∃ γ, IsMir (k - 1) γ ∧ ratGL E k γ = x} := by
    filter_upwards [hae] with h ⟨γ, u, hγ, hu, hh⟩
    rw [hh, uu_eq_one (by omega) hu, mul_one]
    exact ⟨γ, hγ, rfl⟩
  have hone : ∀ g, ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k (k - 1) ∂rho E k = 1 := fun g => by
    rw [lint_rho]; exact key g
  refine ⟨β', hwt, fun Φ hΦ hΦi => ?_, fun Φ hΦ hΦi hint => ?_⟩
  · have := hQ1 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ
      (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g)
    rw [this]
    simp only [lint_rho]
  · have := (hQ2 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ
      (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g) hint).2
    rw [this]
    simp only [int_rho Φ hΦ]

end PositivityTheory.AdelicQuotientData

end
end

