module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.IntegrableUnitIndicator

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.GaugeSplittingAlgebra
section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace J2

lemma lsq_zero {p m : ℕ} (x : Xp p m) : Lsq x 0 = 1 := by simp [Lsq]

lemma lsq_one {p m : ℕ} (x : Xp (p + 1) m) : Lsq x 1 = 1 + ‖x.1 0‖ ^ 2 := by
  simp [Lsq]

lemma rhoSq_zero {p m : ℕ} (x : Xp (p + 1) m) : rhoSq x 0 = rhoSq x 1 + ‖x.2.1 0‖ ^ 2 := by
  simp only [rhoSq, Fin.sum_univ_succ]
  simp
  ring_nf

lemma bco_zero {p m : ℕ} (x : Xp (p + 1) m) : bco x 0 = bco x 1 - x.2.1 0 * star (x.1 0) := by
  simp only [bco, Fin.sum_univ_succ]
  simp
  ring_nf

lemma one_le_lsq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ Lsq x l := by
  unfold Lsq
  have : 0 ≤ ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith

lemma rhoSq_nonneg {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 ≤ rhoSq x l := by
  unfold rhoSq
  have h1 := one_le_lsq x (Fin.last p)
  have : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  have : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  linarith

lemma de_sq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    de x l ^ 2 = Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2 := by
  unfold de
  rw [Real.sq_sqrt]
  have := one_le_lsq x l; have := rhoSq_nonneg x l
  positivity

lemma de_nonneg {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 ≤ de x l := Real.sqrt_nonneg _

lemma one_le_rhoSq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ rhoSq x l := by
  unfold rhoSq
  have h1 := one_le_lsq x (Fin.last p)
  have : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  have : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  linarith

lemma de_pos {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 < de x l := by
  unfold de
  apply Real.sqrt_pos.2
  have h1 := one_le_lsq x l; have h2 := one_le_rhoSq x l
  have : 0 ≤ ‖bco x l‖ ^ 2 := by positivity
  nlinarith

lemma rhoSq_cons {p m : ℕ} (a : Fin (p + 1) → ℂ) (w : ℂ) (b : Fin p → ℂ) (r : (Fin m → ℂ) × ℝ)
    (i : Fin (p + 1)) :
    rhoSq ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = rhoSq ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by
  simp [rhoSq, Lsq, Fin.sum_univ_succ]

lemma bco_cons {p m : ℕ} (a : Fin (p + 1) → ℂ) (w : ℂ) (b : Fin p → ℂ) (r : (Fin m → ℂ) × ℝ)
    (i : Fin (p + 1)) :
    bco ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = bco ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by
  simp [bco, Fin.sum_univ_succ]

lemma de_cons {p m : ℕ} (a : Fin (p + 1) → ℂ) (w : ℂ) (b : Fin p → ℂ) (r : (Fin m → ℂ) × ℝ)
    (i : Fin (p + 1)) :
    de ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = de ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by
  simp only [de, rhoSq_cons, bco_cons]
  rfl

def sclPt {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) :
    (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ :=
  (Fin.cons a0 (r • x.1), r • x.2.1, r • x.2.2.1, r ^ 2 * x.2.2.2)

lemma lsq_scl_one {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) :
    Lsq (tailPt (sclPt a0 r x)) 1 = 1 + ‖a0‖ ^ 2 := by
  simp [Lsq, tailPt, sclPt]

lemma lsq_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    Lsq (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * Lsq x i := by
  simp only [Lsq, tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [Nat.zero_lt_succ, if_true, add_lt_add_iff_right, mul_add, Finset.mul_sum, mul_ite, mul_zero]
  linarith

lemma rhoSq_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    rhoSq (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * rhoSq x i := by
  have hl := lsq_scl a0 r hr x (Fin.last p)
  rw [Fin.succ_last] at hl
  unfold rhoSq
  rw [hl]
  simp only [tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [add_le_add_iff_right, mul_add, Finset.mul_sum, mul_ite, mul_zero]
  simp

lemma bco_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) (i : Fin (p + 1)) :
    bco (tailPt (sclPt a0 r x)) i.succ = ((r ^ 2 : ℝ) : ℂ) * bco x i := by
  simp only [bco, tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [add_le_add_iff_right, Complex.real_smul, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  simp
  have s1 : ∑ j, (r : ℂ) ^ 2 * ((‖x.2.2.1 j‖ : ℂ)) ^ 2 = (r : ℂ) ^ 2 * ∑ j, ((‖x.2.2.1 j‖ : ℂ)) ^ 2 := by
    rw [Finset.mul_sum]
  have s2 : (∑ j : Fin p, if (i : ℕ) ≤ (j : ℕ) then (r : ℂ) * x.2.1 j * ((r : ℂ) * (starRingEnd ℂ) (x.1 j)) else 0)
      = (r : ℂ) ^ 2 * ∑ j : Fin p, if (i : ℕ) ≤ (j : ℕ) then x.2.1 j * (starRingEnd ℂ) (x.1 j) else 0 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; split_ifs <;> ring
  rw [s1, s2]; ring

lemma de_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    de (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * de x i := by
  have h := de_sq (tailPt (sclPt a0 r x)) i.succ
  rw [lsq_scl a0 r hr, rhoSq_scl a0 r hr, bco_scl, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg r)] at h
  have h2 := de_sq x i
  have : de (tailPt (sclPt a0 r x)) i.succ ^ 2 = (r ^ 2 * de x i) ^ 2 := by rw [h, mul_pow (r ^ 2) (de x i), h2]; ring
  have p1 := de_nonneg (tailPt (sclPt a0 r x)) i.succ
  have p2 := de_nonneg x i
  exact (pow_left_inj₀ p1 (by positivity) two_ne_zero).1 this

lemma cont_lsq {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => Lsq x l := by
  unfold Lsq
  exact continuous_const.add (continuous_finsetSum (Finset.univ : Finset (Fin _)) fun j _ => by split_ifs <;> fun_prop)

lemma cont_rhoSq {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => rhoSq x l := by
  unfold rhoSq
  refine ((cont_lsq _).add (continuous_finsetSum _ fun j _ => by fun_prop)).add
    (continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop)

lemma cont_bco {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => bco x l := by
  unfold bco
  refine Continuous.sub ?_ (continuous_finsetSum _ fun j _ => by split_ifs <;> fun_prop)
  fun_prop

lemma cont_de {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => de x l :=
  Real.continuous_sqrt.comp (((cont_lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

lemma cont_cons {p : ℕ} : Continuous fun q : ℂ × (Fin p → ℂ) => (Fin.cons q.1 q.2 : Fin (p + 1) → ℂ) := by
  refine continuous_pi fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply i).comp continuous_snd

lemma cont_tailPt {p m : ℕ} :
    Continuous (tailPt : (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ → Xp (p + 1) m) := by
  unfold tailPt
  exact continuous_fst.prodMk ((cont_cons.comp (continuous_const.prodMk
    (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd))

end J2
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HalfLeNormOneSub
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dot_star_self (y : ι → ℂ) : star y ⬝ᵥ y = ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

lemma tW_sq (q : ι) (x : ι → ℂ) :
    tW q x ^ 2 = ∑ i, Complex.normSq (x i) - Complex.normSq (x q) := by
  unfold tW
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg])]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_ne',
    Finset.sum_erase_eq_sub (Finset.mem_univ q)]

lemma tW_mulVec {h : Matrix ι ι ℂ} (hu : hᴴ * h = 1) {q : ι}
    (hrow : ∀ j, h q j = if j = q then 1 else 0) (x : ι → ℂ) :
    tW q (h *ᵥ x) = tW q x ∧ (h *ᵥ x) q = x q := by
  have hq : (h *ᵥ x) q = x q := by
    simp [mulVec, dotProduct, hrow]
  refine ⟨?_, hq⟩
  have hn : ∑ i, Complex.normSq ((h *ᵥ x) i) = ∑ i, Complex.normSq (x i) := by
    have e : star (h *ᵥ x) ⬝ᵥ (h *ᵥ x) = star x ⬝ᵥ x := by
      rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hu, vecMul_one]
    rw [dot_star_self, dot_star_self] at e
    exact_mod_cast e
  have h1 := tW_sq q (h *ᵥ x)
  have h2 := tW_sq q x
  rw [hn, hq, ← h2] at h1
  have n1 : 0 ≤ tW q (h *ᵥ x) := Real.sqrt_nonneg _
  have n2 : 0 ≤ tW q x := Real.sqrt_nonneg _
  exact (pow_left_inj₀ n1 n2 two_ne_zero).mp h1

lemma volume_Bset_ne_zero {p q : ι} (hpq : p ≠ q) {k : ℕ} (hk : Fintype.card ι = k + 1) :
    volume (Bset q) ≠ 0 := by
  have hc : Continuous (tW q) := by
    unfold tW
    refine Continuous.sqrt (continuous_finsetSum _ fun i _ => ?_)
    by_cases hi : i = q
    · simp only [hi, ↓reduceIte]; exact continuous_const
    · simp only [hi, ↓reduceIte]; exact Complex.continuous_normSq.comp (continuous_apply i)
  have hU : IsOpen {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} :=
    (isOpen_lt continuous_const hc).inter
      ((isOpen_lt hc continuous_const).inter
        (isOpen_lt (continuous_norm.comp (continuous_apply q)) continuous_const))
  let x0 : ι → ℂ := fun i => if i = p then ((3 / 4 : ℝ) : ℂ) else 0
  have hs : (∑ i, if i = q then (0 : ℝ) else Complex.normSq (x0 i)) = 9 / 16 := by
    rw [Finset.sum_eq_single p]
    · simp only [hpq, ↓reduceIte, x0, Complex.normSq_ofReal]; norm_num
    · intro b _ hb; simp [x0, hb]
    · intro hp; exact absurd (Finset.mem_univ p) hp
  have ht : tW q x0 = 3 / 4 := by
    unfold tW
    rw [hs, show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hx0 : x0 ∈ {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} := by
    refine ⟨by rw [ht]; norm_num, by rw [ht]; norm_num, ?_⟩
    simp [x0, Ne.symm hpq]
  have hsub : {x : ι → ℂ | 1 / 2 < tW q x ∧ tW q x < 1 ∧ ‖x q‖ < 1} ⊆ Bset q :=
    fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
  intro h0
  exact (hU.measure_pos volume ⟨x0, hx0⟩).ne' (measure_mono_null hsub h0)

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Imports
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

def fS {p m : ℕ} (s : Fin (p + 2) → ℝ) (x : Xp (p + 1) m) : ℝ≥0∞ :=
  ∏ l, ENNReal.ofReal (de x l ^ (-s l))

def rho (t : ℝ) : ℂ := (1 + t * Complex.I) ^ 2 / ((1 + t ^ 2 : ℝ) : ℂ)

def rot {p m : ℕ} (t : ℝ) (x : Xp p m) : Xp p m :=
  (fun j => rho t * x.1 j, fun j => rho t * x.2.1 j, fun i => rho t * x.2.2.1 i, x.2.2.2)

def scl {p m : ℕ} (τ : ℝ) (x : Xp (p + 1) m) : Xp (p + 1) m :=
  (Function.update x.1 0 (τ * x.1 0), Function.update x.2.1 0 (x.2.1 0 / τ), x.2.2.1, x.2.2.2)

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.PlanarKernelBound
section
open MeasureTheory Set
open scoped ENNReal Real

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals

theorem lintegral_radial (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, g ‖x‖ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g r := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      ENNReal.ofReal p.1 • g ‖Complex.polarCoord.symm p‖ =
        (fun r : ℝ => ENNReal.ofReal r * g r) p.1 * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2 := by
    intro p hp
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, smul_eq_mul, mul_one]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) h1,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal r * g r) (g := fun _ : ℝ => (1 : ℝ≥0∞))
      ((ENNReal.measurable_ofReal.mul hg).aemeasurable) aemeasurable_const]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, one_mul]
  rw [show π - -π = 2 * π by ring, mul_comm]

theorem lintegral_Ioc_rpow (a ρ : ℝ) (ha : a < 2) (hρ : 0 < ρ) :
    ∫⁻ r in Ioc (0 : ℝ) ρ, ENNReal.ofReal (r ^ (1 - a)) = ENNReal.ofReal (ρ ^ (2 - a) / (2 - a)) := by
  have hr : -1 < 1 - a := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal ((intervalIntegral.intervalIntegrable_rpow' hr).1)
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => Real.rpow_nonneg hr.1.le _)),
    ← intervalIntegral.integral_of_le hρ.le, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith)]
  congr 1
  rw [show 1 - a + 1 = 2 - a by ring, sub_zero]

theorem lintegral_Ioi_rpow (b ρ : ℝ) (hb : 2 < b) (hρ : 0 < ρ) :
    ∫⁻ r in Ioi ρ, ENNReal.ofReal (r ^ (1 - b)) = ENNReal.ofReal (ρ ^ (2 - b) / (b - 2)) := by
  have hr : 1 - b < -1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hr hρ)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => Real.rpow_nonneg (hρ.trans hr).le _)),
    integral_Ioi_rpow_of_lt hr hρ]
  congr 1
  rw [show 1 - b + 1 = 2 - b by ring, show b - 2 = -(2 - b) by ring, div_neg, neg_div]

theorem lintegral_disc (a ρ : ℝ) (ha : a < 2) (hρ : 0 < ρ) :
    ∫⁻ x : ℂ, (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-a))) ‖x‖ =
      ENNReal.ofReal (2 * π * (ρ ^ (2 - a) / (2 - a))) := by
  have hm : Measurable ((Iic ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-a)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Iic
  rw [lintegral_radial _ hm]
  have h1 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * (Iic ρ).indicator
      (fun r => ENNReal.ofReal (r ^ (-a))) r = (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (1 - a))) r := by
    intro r hr
    by_cases h : r ∈ Iic ρ
    · rw [indicator_of_mem h, indicator_of_mem h, ← ENNReal.ofReal_mul (le_of_lt hr),
        sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi, lintegral_Ioc_rpow a ρ ha hρ,
    ← ENNReal.ofReal_mul (by positivity)]

theorem lintegral_outside (b ρ : ℝ) (hb : 2 < b) (hρ : 0 < ρ) :
    ∫⁻ x : ℂ, (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-b))) ‖x‖ =
      ENNReal.ofReal (2 * π * (ρ ^ (2 - b) / (b - 2))) := by
  have hm : Measurable ((Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-b)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Ioi
  rw [lintegral_radial _ hm]
  have h1 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * (Ioi ρ).indicator
      (fun r => ENNReal.ofReal (r ^ (-b))) r = (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (1 - b))) r := by
    intro r hr
    by_cases h : r ∈ Ioi ρ
    · rw [indicator_of_mem h, indicator_of_mem h, ← ENNReal.ofReal_mul (le_of_lt hr),
        sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left hρ.le,
    lintegral_Ioi_rpow b ρ hb hρ, ← ENNReal.ofReal_mul (by positivity)]

theorem ker_pointwise (e γ : ℝ) (he : 0 < e) (heγ : e < γ) (hγ : γ < 2) (c : ℂ) (D ρ : ℝ) (hρ : 0 < ρ)
    (hρc : ‖c‖ ≤ 2 * ρ) (hDρ : D ^ 2 = 4 * ρ ^ 2 - ‖c‖ ^ 2) (x : ℂ) (hx0 : x ≠ 0) (hxc : x ≠ c) :
    ENNReal.ofReal ((‖x - c‖ ^ 2 + D ^ 2) ^ (-1 + e / 2)) * ENNReal.ofReal (‖x‖ ^ (-γ)) ≤
      ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
          (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ +
        ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
          (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ +
        ENNReal.ofReal (ρ ^ (-γ)) *
          (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x - c‖ := by
  have hE : -1 + e / 2 ≤ 0 := by linarith
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hm : 0 < ‖x - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hxc)
  have t1 : ‖c‖ - ‖x‖ ≤ ‖x - c‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le c x
  have t2 : ‖x‖ - ‖c‖ ≤ ‖x - c‖ := norm_sub_norm_le x c
  have t3 : ‖x - c‖ ≤ ‖x‖ + ‖c‖ := norm_sub_le x c
  rcases le_or_gt ‖x‖ ρ with hA | hA
  · have hle : ρ ^ 2 ≤ ‖x - c‖ ^ 2 + D ^ 2 := by
      rcases le_or_gt ‖c‖ ρ with h | h
      · nlinarith [norm_nonneg c, sq_nonneg ‖x - c‖, mul_le_mul h h (norm_nonneg c) hρ.le]
      · have h' : ‖c‖ - ρ ≤ ‖x - c‖ := by linarith
        nlinarith [mul_le_mul h' h' (by linarith) (norm_nonneg _), mul_le_mul_of_nonneg_left hρc hρ.le]
    refine le_add_right (le_add_right ?_)
    rw [indicator_of_mem (show ‖x‖ ∈ Iic ρ from hA)]
    exact mul_le_mul'
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) hle hE)) le_rfl
  rcases le_or_gt (2 * ‖c‖) ‖x‖ with hB | hB
  · refine le_add_right (le_add_left ?_)
    rw [indicator_of_mem (show ‖x‖ ∈ Ioi ρ from hA)]
    have h' : ‖x‖ / 2 ≤ ‖x - c‖ := by linarith
    have hle : ‖x‖ ^ 2 / 4 ≤ ‖x - c‖ ^ 2 + D ^ 2 := by
      nlinarith [mul_le_mul h' h' (by positivity) (norm_nonneg _), sq_nonneg D]
    have hid : (‖x‖ ^ 2 / 4) ^ (-1 + e / 2) * ‖x‖ ^ (-γ) =
        (4 : ℝ) ^ (-(-1 + e / 2)) * ‖x‖ ^ (-(2 + γ - e)) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_two, ← Real.rpow_mul hn.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
      have h2 : ‖x‖ ^ (2 * (-1 + e / 2)) * ‖x‖ ^ (-γ) = ‖x‖ ^ (-(2 + γ - e)) := by
        rw [← Real.rpow_add hn]; congr 1; ring
      rw [← h2, div_eq_mul_inv]; ring
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← hid]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (by positivity) hle hE) (by positivity))
  · refine le_add_left ?_
    have h6 : ‖x - c‖ ≤ 6 * ρ := by linarith
    rw [indicator_of_mem (show ‖x - c‖ ∈ Iic (6 * ρ) from h6)]
    have hid : (‖x - c‖ ^ 2) ^ (-1 + e / 2) = ‖x - c‖ ^ (-(2 - e)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hm.le]; congr 1; ring
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← hid,
      mul_comm (ρ ^ (-γ))]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul
      (Real.rpow_le_rpow_of_nonpos (pow_pos hm 2) (le_add_of_nonneg_right (sq_nonneg D)) hE)
      (Real.rpow_le_rpow_of_nonpos hρ hA.le (by linarith)) (by positivity) (by positivity)

end ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open RadialKernelIntegrals

theorem planarKernelBound' : KER := by
  intro e γ he heγ hγ
  set A : ℝ := 2 * π / (2 - γ) + (4 : ℝ) ^ (-(-1 + e / 2)) * (2 * π / (γ - e)) +
    (6 : ℝ) ^ e * (2 * π / e) with hA
  refine ⟨A / (4 : ℝ) ^ (-(γ - e) / 2), fun c D hD => ?_⟩
  have hS : 0 < ‖c‖ ^ 2 + D ^ 2 := by positivity
  set ρ : ℝ := Real.sqrt (‖c‖ ^ 2 + D ^ 2) / 2 with hρdef
  have hρ : 0 < ρ := div_pos (Real.sqrt_pos.2 hS) two_pos
  have hρ2 : ρ ^ 2 = (‖c‖ ^ 2 + D ^ 2) / 4 := by
    rw [hρdef, div_pow, Real.sq_sqrt hS.le]; norm_num
  have hρc : ‖c‖ ≤ 2 * ρ := by
    have : ‖c‖ ≤ Real.sqrt (‖c‖ ^ 2 + D ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg D])
    rw [hρdef]; linarith
  have hDρ : D ^ 2 = 4 * ρ ^ 2 - ‖c‖ ^ 2 := by rw [hρ2]; ring
  have hS4 : ‖c‖ ^ 2 + D ^ 2 = 4 * ρ ^ 2 := by rw [hρ2]; ring
  have hae : ∀ᵐ x : ℂ, x ≠ 0 ∧ x ≠ c := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ)),
      compl_mem_ae_iff.2 (measure_singleton c)] with x h0 hc
    exact ⟨h0, hc⟩
  refine (lintegral_mono_ae (hae.mono fun x hx =>
    ker_pointwise e γ he heγ hγ c D ρ hρ hρc hDρ x hx.1 hx.2)).trans ?_
  have hm1 : Measurable ((Iic ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-γ)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Iic
  have hm2 : Measurable ((Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-(2 + γ - e))))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Ioi
  have hF1 : Measurable fun x : ℂ => ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
      (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ :=
    (hm1.comp measurable_norm).const_mul _
  have hF2 : Measurable fun x : ℂ => ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
      (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ :=
    (hm2.comp measurable_norm).const_mul _
  have hF12 : Measurable fun x : ℂ => ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
      (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ +
      ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
      (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ := hF1.add hF2
  have h3 : ∫⁻ x : ℂ, (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x - c‖ =
      ∫⁻ x : ℂ, (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x‖ :=
    lintegral_sub_right_eq_self
      (fun y : ℂ => (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖y‖) c
  have hI1 : 0 ≤ 2 * π * (ρ ^ (2 - γ) / (2 - γ)) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  have hI2 : 0 ≤ 2 * π * (ρ ^ (2 - (2 + γ - e)) / (2 + γ - e - 2)) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  have hI3 : 0 ≤ 2 * π * ((6 * ρ) ^ (2 - (2 - e)) / (2 - (2 - e))) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  rw [lintegral_add_left hF12, lintegral_add_left hF1,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h3,
    lintegral_disc γ ρ hγ hρ, lintegral_outside (2 + γ - e) ρ (by linarith) hρ,
    lintegral_disc (2 - e) (6 * ρ) (by linarith) (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) hI1) (mul_nonneg (by positivity) hI2),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (by positivity) hI1)
      (mul_nonneg (by positivity) hI2)) (mul_nonneg (by positivity) hI3)]
  apply ENNReal.ofReal_le_ofReal
  have hP1 : (ρ ^ 2) ^ (-1 + e / 2) * ρ ^ (2 - γ) = ρ ^ (e - γ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hρ.le, ← Real.rpow_add hρ]; congr 1; ring
  have hP2 : ρ ^ (2 - (2 + γ - e)) = ρ ^ (e - γ) := by congr 1; ring
  have hP3 : ρ ^ (-γ) * (6 * ρ) ^ e = (6 : ℝ) ^ e * ρ ^ (e - γ) := by
    have h : ρ ^ (-γ) * ρ ^ e = ρ ^ (e - γ) := by rw [← Real.rpow_add hρ]; congr 1; ring
    rw [Real.mul_rpow (by norm_num) hρ.le, ← h]; ring
  have hS' : (‖c‖ ^ 2 + D ^ 2) ^ (-(γ - e) / 2) = (4 : ℝ) ^ (-(γ - e) / 2) * ρ ^ (e - γ) := by
    rw [hS4, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_two,
      ← Real.rpow_mul hρ.le]
    congr 2; ring
  have hne : (4 : ℝ) ^ (-(γ - e) / 2) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  rw [hS', hP2, show (2 : ℝ) + γ - e - 2 = γ - e by ring, show (2 : ℝ) - (2 - e) = e by ring]
  refine le_of_eq ?_
  calc _ = A * ρ ^ (e - γ) := by
        rw [hA]; linear_combination (2 * π / (2 - γ)) * hP1 + (2 * π / e) * hP3
    _ = _ := by field_simp

end ReciprocityTheory.ChartRestriction.DS.Xi
end

