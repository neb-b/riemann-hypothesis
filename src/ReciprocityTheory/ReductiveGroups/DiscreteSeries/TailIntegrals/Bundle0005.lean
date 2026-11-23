module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.VolumeUnivFinZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.CriticalExponentSucc
section
noncomputable section
open MeasureTheory Module
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace J2

abbrev TDom (p m : ℕ) := (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ

def chF (p m : ℕ) (ν : Fin (p + 1) → ℝ) (x : Xp p m) : ℝ≥0∞ :=
  ∏ l, ENNReal.ofReal (de x l ^ (-(s0N p m l + ν l)))

def tailF (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) (x : TDom p m) : ℝ≥0∞ :=
  ENNReal.ofReal (Lsq (tailPt x) 1 ^ ((-2 + α) / 2)) * ENNReal.ofReal (de (tailPt x) 1 ^ (-α)) *
    ∏ i : Fin (p + 1), ENNReal.ofReal (de (tailPt x) i.succ ^ (-(s0N (p + 1) m i.succ + ν i)))

lemma chF_meas (p m : ℕ) (ν : Fin (p + 1) → ℝ) : Measurable (chF p m ν) := by
  unfold chF
  exact Finset.measurable_prod _ fun l _ =>
    ENNReal.measurable_ofReal.comp ((cont_de l).measurable.pow_const _)

lemma tailF_meas (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) : Measurable (tailF p m α ν) := by
  unfold tailF
  have h := cont_tailPt (p := p) (m := m)
  exact ((ENNReal.measurable_ofReal.comp (((cont_lsq 1).comp h).measurable.pow_const _)).mul
    (ENNReal.measurable_ofReal.comp (((cont_de 1).comp h).measurable.pow_const _))).mul
    (Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp (((cont_de i.succ).comp h).measurable.pow_const _))

lemma criticalExponent_succ (p m : ℕ) (i : Fin (p + 1)) : s0N (p + 1) m i.succ = s0N p m i := by
  simp [s0N, Fin.val_succ]

lemma sum_s0N (p m : ℕ) : ∑ i, s0N p m i = 2 * p + m + 1 := by
  rw [Fin.sum_univ_castSucc]
  simp [s0N]
  ring

lemma prod_update {p : ℕ} (d s ν : Fin (p + 1) → ℝ) (hd : ∀ l, 0 < d l) (α : ℝ) :
    ∏ l, d l ^ (-(s l + Function.update ν 0 (α + ν 0) l)) = d 0 ^ (-α) * ∏ l, d l ^ (-(s l + ν l)) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _)]
  rw [show -(s 0 + (α + ν 0)) = -α + -(s 0 + ν 0) by ring, Real.rpow_add (hd 0)]
  ring

lemma tail_pt (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) (a0 : ℂ) (t : ℝ) (hr : 1 + ‖a0‖ ^ 2 = t ^ 2)
    (q : Xp p m) :
    tailF p m α ν (sclPt a0 t q) =
      ENNReal.ofReal ((1 + ‖a0‖ ^ 2) ^ ((-2 + α) / 2 - α - ∑ i, (s0N p m i + ν i))) *
        chF p m (Function.update ν 0 (α + ν 0)) q := by
  have hL : 0 < 1 + ‖a0‖ ^ 2 := by positivity
  unfold tailF chF
  rw [lsq_scl_one, ← Fin.succ_zero_eq_one, de_scl a0 t hr q 0]
  simp only [de_scl a0 t hr q, criticalExponent_succ]
  rw [← hr, ← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.rpow_nonneg (mul_nonneg hL.le (de_pos q i).le) _),
    ← ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (de_pos q l).le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hL.le _)
      (Real.rpow_nonneg (mul_nonneg hL.le (de_pos q 0).le) _)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
  congr 1
  rw [prod_update (de q) (s0N p m) ν (de_pos q) α,
    Finset.prod_congr rfl fun i _ => Real.mul_rpow hL.le (de_pos q i).le, Finset.prod_mul_distrib,
    ← Real.rpow_sum_of_pos hL, Real.mul_rpow hL.le (de_pos q 0).le]
  rw [show (-2 + α) / 2 - α - ∑ i, (s0N p m i + ν i) = (-2 + α) / 2 + -α + ∑ i, -(s0N p m i + ν i) by
    rw [Finset.sum_neg_distrib]; ring, Real.rpow_add hL, Real.rpow_add hL]
  ring

lemma tail_inner (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) (a0 : ℂ) :
    ∫⁻ q : Xp p m, tailF p m α ν (Fin.cons a0 q.1, q.2) =
      ENNReal.ofReal ((1 + ‖a0‖ ^ 2) ^ (-(2 + α + 2 * ∑ i, ν i) / 2)) *
        CHInt p m (Function.update ν 0 (α + ν 0)) := by
  have hL : 0 < 1 + ‖a0‖ ^ 2 := by positivity
  set t := Real.sqrt (1 + ‖a0‖ ^ 2) with ht_def
  have ht : 0 < t := Real.sqrt_pos.2 hL
  have htt : 1 + ‖a0‖ ^ 2 = t ^ 2 := (Real.sq_sqrt hL.le).symm
  have hc : Continuous fun q : Xp p m => ((Fin.cons a0 q.1, q.2) : TDom p m) :=
    (cont_cons.comp (continuous_const.prodMk continuous_fst)).prodMk continuous_snd
  have hG : Measurable fun q : Xp p m => tailF p m α ν (Fin.cons a0 q.1, q.2) :=
    (tailF_meas p m α ν).comp hc.measurable
  have hpt : ∀ x : Xp p m, tailF p m α ν (Fin.cons a0 (sclL p m t x).1, (sclL p m t x).2) =
      tailF p m α ν (sclPt a0 t x) := fun x => by rw [sclL_apply]; rfl
  rw [lint_scl hG ht]
  simp only [hpt, tail_pt p m α ν a0 t htt]
  rw [lintegral_const_mul _ (chF_meas _ _ _), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hreal : t ^ (4 * p + 2 * m + 2) * (1 + ‖a0‖ ^ 2) ^ ((-2 + α) / 2 - α - ∑ i, (s0N p m i + ν i)) =
      (1 + ‖a0‖ ^ 2) ^ (-(2 + α + 2 * ∑ i, ν i) / 2) := by
    rw [show 4 * p + 2 * m + 2 = 2 * (2 * p + m + 1) by ring, pow_mul, ← htt, ← Real.rpow_natCast,
      ← Real.rpow_add hL, Finset.sum_add_distrib, sum_s0N]
    congr 1
    push_cast
    ring
  rw [hreal]
  rfl

lemma tail_eq (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) :
    TailInt p m α ν = kc (2 + α + 2 * ∑ i, ν i) * CHInt p m (Function.update ν 0 (α + ν 0)) := by
  show ∫⁻ x : TDom p m, tailF p m α ν x = _
  rw [split_cons _ (tailF_meas p m α ν), lintegral_congr fun w => tail_inner p m α ν w,
    lintegral_mul_const _ (by fun_prop)]
  rfl

private lemma norm_sq_add_norm_sq_sub_eq_complete_square (w B a : ℂ) :
    ‖w‖ ^ 2 + ‖B - w * star a‖ ^ 2 =
      (1 + ‖a‖ ^ 2) * ‖w - B * a / ((1 + ‖a‖ ^ 2 : ℝ) : ℂ)‖ ^ 2 + ‖B‖ ^ 2 / (1 + ‖a‖ ^ 2) := by
  have key : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hL : (1 + (a.re ^ 2 + a.im ^ 2)) ≠ 0 := by positivity
  simp only [key, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

lemma ch_pt (p m : ℕ) (ν : Fin (p + 2) → ℝ) (y : TDom p m) :
    ∫⁻ w : ℂ, chF (p + 1) m ν (y.1, Fin.cons w y.2.1, y.2.2) =
      kc (2 + ν 0) * tailF p m (ν 0) (Fin.tail ν) y := by
  rcases y with ⟨a, b, r⟩
  dsimp only
  have hlsq0 : ∀ w : ℂ, Lsq ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 = 1 := by
    intro w; simp [Lsq]
  have hrho : ∀ w : ℂ, rhoSq ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 =
      rhoSq (tailPt ((a, b, r) : TDom p m)) 1 + ‖w‖ ^ 2 := by
    intro w
    simp [rhoSq, Lsq, tailPt, Fin.sum_univ_succ]
    ring
  have hbco : ∀ w : ℂ, bco ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 =
      bco (tailPt ((a, b, r) : TDom p m)) 1 - w * star (a 0) := by
    intro w
    simp [bco, tailPt, Fin.sum_univ_succ]
    ring
  have hL1 : Lsq (tailPt ((a, b, r) : TDom p m)) 1 = 1 + ‖a 0‖ ^ 2 := by
    simp [Lsq, tailPt, Fin.sum_univ_succ]
  have hd1 : de (tailPt ((a, b, r) : TDom p m)) 1 ^ 2 =
      (1 + ‖a 0‖ ^ 2) * rhoSq (tailPt ((a, b, r) : TDom p m)) 1 + ‖bco (tailPt ((a, b, r) : TDom p m)) 1‖ ^ 2 := by
    rw [de, Real.sq_sqrt (add_nonneg (mul_nonneg (by linarith [one_le_lsq (tailPt ((a, b, r) : TDom p m)) 1])
      (rhoSq_nonneg _ _)) (sq_nonneg _)), hL1]
  have hM := one_le_rhoSq (tailPt ((a, b, r) : TDom p m)) 1
  have hd1p := de_pos (tailPt ((a, b, r) : TDom p m)) 1
  set M := rhoSq (tailPt ((a, b, r) : TDom p m)) 1
  set B := bco (tailPt ((a, b, r) : TDom p m)) 1
  set d1 := de (tailPt ((a, b, r) : TDom p m)) 1
  set L := 1 + ‖a 0‖ ^ 2 with hL_def
  have hL : 0 < L := by positivity
  set D := M + ‖B‖ ^ 2 / L with hD_def
  have hD : 0 < D := add_pos_of_pos_of_nonneg (by linarith) (by positivity)
  set c : ℂ := B * a 0 / ((L : ℝ) : ℂ) with hc_def
  have hquad : ∀ w : ℂ, de ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 ^ 2 = L * ‖w - c‖ ^ 2 + D := by
    intro w
    rw [de, Real.sq_sqrt (add_nonneg (mul_nonneg (by linarith [one_le_lsq ((a, Fin.cons w b, r) : Xp (p + 1) m) 0])
      (rhoSq_nonneg _ _)) (sq_nonneg _)), hlsq0, hrho, hbco, one_mul, add_assoc, norm_sq_add_norm_sq_sub_eq_complete_square, hD_def, hc_def, hL_def]
    ring
  have hzero : ∀ w : ℂ, de ((a, Fin.cons w b, r) : Xp (p + 1) m) 0 ^ (-(s0N (p + 1) m 0 + ν 0)) =
      (L * ‖w - c‖ ^ 2 + D) ^ (-(2 + ν 0) / 2) := by
    intro w
    have hs : s0N (p + 1) m 0 = 2 := by simp [s0N]
    rw [hs, ← hquad w, ← Real.rpow_natCast, ← Real.rpow_mul (de_pos _ _).le]
    congr 1
    push_cast
    ring
  have htp : tailPt ((a, b, r) : TDom p m) = (a, Fin.cons 0 b, r) := rfl
  unfold chF tailF
  simp only [Fin.prod_univ_succ, de_cons, hzero]
  rw [lintegral_mul_const _ (by fun_prop), kernel L D hL hD c (2 + ν 0), hL1]
  have hkey : ENNReal.ofReal (L⁻¹ * D ^ (1 - (2 + ν 0) / 2)) =
      ENNReal.ofReal (L ^ ((-2 + ν 0) / 2)) * ENNReal.ofReal (d1 ^ (-ν 0)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e1 : D = d1 ^ 2 / L := by
      rw [hd1, hD_def]
      field_simp
    rw [e1, Real.div_rpow (sq_nonneg _) hL.le, ← Real.rpow_natCast d1 2, ← Real.rpow_mul hd1p.le,
      show (1 - (2 + ν 0) / 2) = -ν 0 / 2 by ring,
      show ((2 : ℕ) : ℝ) * (-ν 0 / 2) = -ν 0 by push_cast; ring,
      show (-2 + ν 0) / 2 = -1 - (-ν 0 / 2) by ring, Real.rpow_sub hL, Real.rpow_neg_one]
    field_simp
  rw [hkey, htp, show de ((a, Fin.cons 0 b, r) : Xp (p + 1) m) 1 = d1 from rfl]
  simp only [Fin.tail]
  ring

lemma ch_step (p m : ℕ) (ν : Fin (p + 2) → ℝ) :
    CHInt (p + 1) m ν = kc (2 + ν 0) * TailInt p m (ν 0) (Fin.tail ν) := by
  have hF := chF_meas (p + 1) m ν
  have hT := tailF_meas p m (ν 0) (Fin.tail ν)
  have step : ∀ a : Fin (p + 1) → ℂ,
      ∫⁻ z : (Fin (p + 1) → ℂ) × ((Fin m → ℂ) × ℝ), chF (p + 1) m ν (a, z) =
        ∫⁻ q : (Fin p → ℂ) × ((Fin m → ℂ) × ℝ), kc (2 + ν 0) * tailF p m (ν 0) (Fin.tail ν) (a, q) := by
    intro a
    rw [split_cons' (fun z => chF (p + 1) m ν (a, z)) (hF.comp measurable_prodMk_left)]
    exact lintegral_congr fun q => ch_pt p m ν (a, q)
  show ∫⁻ x : Xp (p + 1) m, chF (p + 1) m ν x =
    kc (2 + ν 0) * ∫⁻ y : TDom p m, tailF p m (ν 0) (Fin.tail ν) y
  rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable,
    lintegral_congr fun a => (step a).trans (lintegral_const_mul _ (hT.comp measurable_prodMk_left)),
    lintegral_const_mul _ hT.lintegral_prod_right']
  congr 1
  rw [Measure.volume_eq_prod (Fin (p + 1) → ℂ), lintegral_prod _ hT.aemeasurable]

end J2
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LintegralInsertFiberLe
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

private lemma rpow_sq_half {a : ℝ} (ha : 0 ≤ a) (r : ℝ) : a ^ r = (a ^ 2) ^ (r / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  congr 1
  push_cast
  ring

private lemma nnorm_ae (γ : ℝ) (f : ℂ → ℝ≥0∞) :
    ∫⁻ z : ℂ, f z * (‖z‖₊ : ℝ≥0∞) ^ (-γ) = ∫⁻ z : ℂ, f z * ENNReal.ofReal (‖z‖ ^ (-γ)) := by
  apply lintegral_congr_ae
  have h0 : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))
  filter_upwards [h0] with z hz
  congr 1
  rw [← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hz)]
  congr 1
  rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

private lemma core {e0 γ C : ℝ}
    (hC : ∀ (c : ℂ) (D : ℝ), 0 < D →
      (∫⁻ x : ℂ, ENNReal.ofReal ((‖x - c‖ ^ 2 + D ^ 2) ^ (-1 + e0 / 2)) *
        ENNReal.ofReal (‖x‖ ^ (-γ))) ≤ ENNReal.ofReal (C * (‖c‖ ^ 2 + D ^ 2) ^ (-(γ - e0) / 2)))
    {L d1 d0 : ℝ} (c : ℂ) (f : ℂ → ℝ) (hL : 0 < L) (hd1 : 0 < d1) (hd0 : 0 ≤ d0)
    (h0 : d0 ^ 2 = L * ‖c‖ ^ 2 + d1 ^ 2 / L) (hf0 : ∀ z, 0 ≤ f z)
    (hf : ∀ z, f z ^ 2 = L * ‖z - c‖ ^ 2 + d1 ^ 2 / L) :
    ∫⁻ z : ℂ, ENNReal.ofReal (f z ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ)) ≤
      ENNReal.ofReal (max C 1 * L ^ (-1 + γ / 2) * d0 ^ (-(γ - e0))) := by
  have hD : 0 < d1 / L := div_pos hd1 hL
  have hsq : ∀ t : ℝ, L * t + d1 ^ 2 / L = L * (t + (d1 / L) ^ 2) := by
    intro t
    have := hL.ne'
    field_simp
  have he : -(2 - e0) / 2 = -1 + e0 / 2 := by ring
  have hpt : ∀ z, f z ^ (-(2 - e0)) =
      L ^ (-1 + e0 / 2) * (‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2) := by
    intro z
    rw [rpow_sq_half (hf0 z), hf z, hsq, he, Real.mul_rpow hL.le (by positivity)]
  have hX : ‖c‖ ^ 2 + (d1 / L) ^ 2 = d0 ^ 2 / L := by
    rw [h0, hsq]; field_simp
  have hLp : L ^ (-1 + γ / 2) = L ^ (-1 + e0 / 2) / L ^ (-(γ - e0) / 2) := by
    rw [← Real.rpow_sub hL]; congr 1; ring
  have hd0p : (d0 ^ 2) ^ (-(γ - e0) / 2) = d0 ^ (-(γ - e0)) := (rpow_sq_half hd0 _).symm
  calc ∫⁻ z : ℂ, ENNReal.ofReal (f z ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ))
      = ∫⁻ z : ℂ, ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          (ENNReal.ofReal ((‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2)) *
            ENNReal.ofReal (‖z‖ ^ (-γ))) := by
        refine lintegral_congr (fun z => ?_)
        rw [hpt z, ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _), mul_assoc]
    _ = ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ∫⁻ z : ℂ, ENNReal.ofReal ((‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2)) *
            ENNReal.ofReal (‖z‖ ^ (-γ)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ENNReal.ofReal (C * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2)) := by
        gcongr
        exact hC c _ hD
    _ ≤ ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ENNReal.ofReal (max C 1 * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2)) := by
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (L ^ (-1 + e0 / 2) *
          (max C 1 * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2))) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)).symm
    _ = ENNReal.ofReal (max C 1 * L ^ (-1 + γ / 2) * d0 ^ (-(γ - e0))) := by
        congr 1
        rw [hX, Real.div_rpow (sq_nonneg _) hL.le, hd0p, hLp]
        ring

theorem lintegral_insertFiber_le (hC1 : C1) (hK : KER) {e0 γ : ℝ} (he0 : 0 < e0) (hγ : e0 < γ) (hγ2 : γ < 2) :
    ∃ CK : ℝ, 0 < CK ∧ ∀ {p m : ℕ} (y : Yp p m),
      ∫⁻ z : ℂ, ENNReal.ofReal (de (ins y z) 0 ^ (-(2 - e0))) * (‖z‖₊ : ℝ≥0∞) ^ (-γ) ≤
        ENNReal.ofReal (CK * Lsq (tailPt y) 1 ^ (-1 + γ / 2) * de (tailPt y) 0 ^ (-(γ - e0))) := by
  obtain ⟨C, hC⟩ := hK e0 γ he0 hγ hγ2
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro p m y
  have hf : ∀ z : ℂ, de (ins y z) 0 ^ 2 =
      Lsq (tailPt y) 1 * ‖z - y.1 0 * bco (tailPt y) 1 / (Lsq (tailPt y) 1 : ℂ)‖ ^ 2 +
        de (tailPt y) 1 ^ 2 / Lsq (tailPt y) 1 := by
    intro z
    have hb : bco (ins y z) 1 = bco (tailPt y) 1 := by simpa using bco_ins_succ y z 0
    have hd : de (ins y z) 1 = de (tailPt y) 1 := by simpa using de_ins_succ y z 0
    have h := hC1 p m (ins y z)
    rw [hb, hd, Lsq_ins] at h
    simp only [ins, Fin.cons_zero] at h
    exact h
  have h0 : de (tailPt y) 0 ^ 2 =
      Lsq (tailPt y) 1 * ‖y.1 0 * bco (tailPt y) 1 / (Lsq (tailPt y) 1 : ℂ)‖ ^ 2 +
        de (tailPt y) 1 ^ 2 / Lsq (tailPt y) 1 := by
    have := hf 0
    rw [zero_sub, norm_neg] at this
    exact this
  calc _ = ∫⁻ z : ℂ, ENNReal.ofReal (de (ins y z) 0 ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ)) :=
        nnorm_ae γ _
    _ ≤ _ := core hC _ (fun z => de (ins y z) 0) (lt_of_lt_of_le one_pos (Lsq_ge_one _ _))
        (lt_of_lt_of_le one_pos (de_ge_one _ _)) (le_trans zero_le_one (de_ge_one _ _)) h0
        (fun z => le_trans zero_le_one (de_ge_one _ _)) hf

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

