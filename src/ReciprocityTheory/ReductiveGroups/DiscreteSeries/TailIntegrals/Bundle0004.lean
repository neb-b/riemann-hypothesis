module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RhoMulStar
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

private lemma rho_den (t : ℝ) : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (by positivity)

private theorem norm_rho (t : ℝ) : ‖rho t‖ = 1 := by
  have h2 : ‖(1 + (t : ℂ) * Complex.I)‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hd : ‖((1 + t ^ 2 : ℝ) : ℂ)‖ = 1 + t ^ 2 := by
    exact Complex.norm_of_nonneg (by positivity)
  unfold rho
  rw [norm_div, norm_pow, h2, hd, div_self (by positivity)]

private theorem rho_mul_star (t : ℝ) : rho t * star (rho t) = 1 := by
  have h := norm_rho t
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  simp

private theorem rho_mp (t : ℝ) : MeasurePreserving (fun z : ℂ => rho t * z) volume volume := by
  have h1 := rho_mul_star t
  have h1' : star (rho t) * rho t = 1 := by rw [mul_comm]; exact h1
  have hn := norm_rho t
  let e : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { toFun := fun z => rho t * z
      invFun := fun z => star (rho t) * z
      map_add' := fun x y => mul_add _ x y
      map_smul' := fun r x => by
        exact mul_smul_comm r (rho t) x
      left_inv := fun z => by
        show star (rho t) * (rho t * z) = z
        rw [← mul_assoc, h1', one_mul]
      right_inv := fun z => by
        show rho t * (star (rho t) * z) = z
        rw [← mul_assoc, h1, one_mul]
      norm_map' := fun z => by
        show ‖rho t * z‖ = ‖z‖
        rw [norm_mul, hn, one_mul] }
  exact e.measurePreserving

theorem rot_mp {p m : ℕ} (t : ℝ) : MeasurePreserving (rot (p := p) (m := m) t) volume volume := by
  have h0 := rho_mp t
  have hp : ∀ n : ℕ, MeasurePreserving (fun (v : Fin n → ℂ) (j : Fin n) => rho t * v j) volume volume := by
    intro n
    exact measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun _ => h0)
  have h := (hp p).prod ((hp p).prod ((hp m).prod (MeasurePreserving.id (volume : Measure ℝ))))
  exact h

private theorem continuous_rho_tail_integrals : Continuous rho := by
  unfold rho
  exact ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).pow 2).div
    (Complex.continuous_ofReal.comp (continuous_const.add (continuous_id.pow 2))) rho_den

theorem rot_meas {p m : ℕ} : Measurable (fun q : ℝ × Xp p m => rot q.1 q.2) := by
  have hu : Continuous rho := continuous_rho_tail_integrals
  have hc : Continuous (fun q : ℝ × ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => rot q.1 q.2) := by
    unfold rot
    fun_prop
  exact hc.measurable

theorem de_rot {p m : ℕ} (t : ℝ) (x : Xp p m) (l : Fin (p + 1)) : de (rot t x) l = de x l := by
  have hn : ∀ z : ℂ, ‖rho t * z‖ = ‖z‖ := fun z => by rw [norm_mul, norm_rho, one_mul]
  have hc : ∀ a b : ℂ, rho t * a * star (rho t * b) = a * star b := by
    intro a b
    rw [star_mul']
    linear_combination (a * star b) * rho_mul_star t
  simp only [ReciprocityTheory.ChartRestriction.DS.Xi.de, ReciprocityTheory.ChartRestriction.DS.Xi.Lsq, ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq, ReciprocityTheory.ChartRestriction.DS.Xi.bco, rot, hn, hc]

theorem linF_rot {p m : ℕ} (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (t : ℝ) (x : Xp p m) :
    linF η η' ζ (rot t x) = rho t * linF η η' ζ x := by
  simp only [ReciprocityTheory.ChartRestriction.DS.Xi.linF, rot]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> ring

private lemma key (t c₀ : ℝ) (X : ℂ) : 2 * (rho t * X).im + c₀ =
    ((2 * X.im + c₀) + 4 * X.re * t + (c₀ - 2 * X.im) * t ^ 2) / (1 + t ^ 2) := by
  have hd : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have key : rho t * ((1 + t ^ 2 : ℝ) : ℂ) = (1 + t * Complex.I) ^ 2 := by
    unfold rho
    exact div_mul_cancel₀ _ (rho_den t)
  have hre : (rho t).re = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [eq_div_iff hd]
    have := congrArg Complex.re key
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im] at this
    linear_combination this
  have him : (rho t).im = (2 * t) / (1 + t ^ 2) := by
    rw [eq_div_iff hd]
    have := congrArg Complex.im key
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im] at this
    linear_combination this
  rw [Complex.mul_im, hre, him]
  field_simp
  ring

private theorem rpow_neg_le_rpow_neg_of_pos_of_le {x y δ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hδ : 0 ≤ δ) : y ^ (-δ) ≤ x ^ (-δ) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
  have ha : 0 < x ^ δ := Real.rpow_pos_of_pos hx δ
  have hb : x ^ δ ≤ y ^ δ := Real.rpow_le_rpow hx.le hxy hδ
  exact inv_anti₀ ha hb

private theorem complex_norm_le_abs_re_add_abs_im (X : ℂ) : ‖X‖ ≤ |X.re| + |X.im| := by
  calc ‖X‖ = ‖(X.re : ℂ) + X.im * Complex.I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(X.re : ℂ)‖ + ‖(X.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |X.re| + |X.im| := by simp

private theorem complex_norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  simp

theorem rot_weight (hS : SUB) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℂ) (c₀ : ℝ),
      ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
        ENNReal.ofReal (C * (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
  obtain ⟨C₁, hC₁⟩ := hS δ hδ0 hδ1
  set K : ℝ := (5 : ℝ)⁻¹ ^ (-δ) with hKdef
  have hK : 0 < K := by positivity
  have hM : 0 < max C₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨K * max C₁ 1, mul_pos hK hM, fun X c₀ => ?_⟩
  set A : ℝ := 2 * X.im + c₀ with hA
  set B : ℝ := 4 * X.re with hB
  set D : ℝ := c₀ - 2 * X.im with hD
  set c : Fin 3 → ℂ := ![(A : ℂ), (B : ℂ), (D : ℂ)] with hc
  have c0 : c 0 = (A : ℂ) := rfl
  have c1 : c 1 = (B : ℂ) := rfl
  have c2 : c 2 = (D : ℂ) := rfl
  set N : ℝ := ‖c‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hAN : |A| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c0]; exact norm_le_pi_norm c 0
  have hBN : |B| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c1]; exact norm_le_pi_norm c 1
  have hDN : |D| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c2]; exact norm_le_pi_norm c 2
  have hc₀ : |c₀| ≤ N := by
    rw [abs_le] at hAN hDN ⊢
    constructor <;> linarith [hAN.1, hAN.2, hDN.1, hDN.2]
  have hX : ‖X‖ ≤ N := by
    have h1 := complex_norm_le_abs_re_add_abs_im X
    have hre : |X.re| ≤ N / 4 := by
      rw [abs_le] at hBN ⊢; constructor <;> linarith [hBN.1, hBN.2]
    have him : |X.im| ≤ N / 2 := by
      rw [abs_le] at hAN hDN ⊢; constructor <;> linarith [hAN.1, hAN.2, hDN.1, hDN.2]
    linarith
  have hpt : ∀ t ∈ Icc (1 : ℝ) 2,
      ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
        ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := by
    intro t ht
    rw [← ENNReal.ofReal_mul hK.le]
    apply ENNReal.ofReal_le_ofReal
    have hq : c 0 + c 1 * t + c 2 * t ^ 2 = ((A + B * t + D * t ^ 2 : ℝ) : ℂ) := by
      rw [c0, c1, c2]; push_cast; ring
    rw [hq, complex_norm_ofReal_eq_abs, key]
    set q : ℝ := A + B * t + D * t ^ 2 with hqdef
    have hdpos : 0 < 1 + t ^ 2 := by positivity
    have hd5 : 1 + t ^ 2 ≤ 5 := by nlinarith [ht.1, ht.2]
    rw [hKdef, ← Real.mul_rpow (by norm_num) (by positivity)]
    apply rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) _ hδ0.le
    rw [abs_div, abs_of_pos hdpos]
    have hw0 : 0 ≤ |q| / (1 + t ^ 2) := div_nonneg (abs_nonneg _) hdpos.le
    have hwd : |q| / (1 + t ^ 2) * (1 + t ^ 2) = |q| := by
      exact div_mul_cancel₀ _ hdpos.ne'
    have := mul_le_mul_of_nonneg_left hd5 hw0
    linarith
  have hfin : C₁ * (1 + N) ^ (-δ / 2) ≤ max C₁ 1 * ((1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
    have hpos : 0 < 1 + N := by linarith
    have e : (1 + N) ^ (-δ / 2) = (1 + N) ^ (-δ / 4) * (1 + N) ^ (-δ / 4) := by
      rw [← Real.rpow_add hpos]; congr 1; ring
    have hδ4 : 0 ≤ δ / 4 := by positivity
    have ha : (1 + N) ^ (-δ / 4) ≤ (1 + |c₀|) ^ (-δ / 4) := by
      rw [neg_div]; exact rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) (by linarith) hδ4
    have hb : (1 + N) ^ (-δ / 4) ≤ (1 + ‖X‖) ^ (-δ / 4) := by
      rw [neg_div]; exact rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) (by linarith) hδ4
    have hab : (1 + N) ^ (-δ / 2) ≤ (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4) := by
      rw [e]; exact mul_le_mul ha hb (by positivity) (by positivity)
    exact mul_le_mul (le_max_left _ _) hab (by positivity) hM.le
  have hmono : ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
      ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := by
    exact setLIntegral_mono' measurableSet_Icc hpt
  calc ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ))
      ≤ ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := hmono
    _ = ENNReal.ofReal K * ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (C₁ * (1 + ‖c‖) ^ (-δ / 2)) := by
        gcongr
        exact hC₁ c
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (max C₁ 1 * ((1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4))) := by
        gcongr
    _ = ENNReal.ofReal (K * max C₁ 1 * (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
        rw [← ENNReal.ofReal_mul hK.le]; congr 1; ring

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RhoSqInsSucc
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

abbrev Yp (p m : ℕ) := (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ

def ins {p m : ℕ} (y : Yp p m) (z : ℂ) : Xp (p + 1) m := (y.1, Fin.cons z y.2.1, y.2.2)

def bS {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : ℂ :=
  ∑ j : Fin p, if l.val ≤ j.val then x.2.1 j * star (x.1 j) else 0

lemma Lsq_ins {p m : ℕ} (y : Yp p m) (z : ℂ) (l : Fin (p + 2)) :
    Lsq (ins y z) l = Lsq (tailPt y) l := rfl

private theorem ins_snd_fst_eq_tailPt_snd_fst_of_ne_zero {p m : ℕ} (y : Yp p m) (z : ℂ) {j : Fin (p + 1)} (hj : j ≠ 0) :
    (ins y z).2.1 j = (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).2.1 j := by
  induction j using Fin.cases with
  | zero => exact absurd rfl hj
  | succ k => simp [ins, ReciprocityTheory.ChartRestriction.DS.Xi.tailPt]

lemma sum_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) (g : ℂ → ℂ → ℂ) :
    (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then g ((ins y z).2.1 j) ((ins y z).1 j) else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then g ((tailPt y).2.1 j) ((tailPt y).1 j) else 0 := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i.succ.val ≤ j.val
  · have hj : j ≠ 0 := by
      rintro rfl
      simp at h
    rw [if_pos h, if_pos h, ins_snd_fst_eq_tailPt_snd_fst_of_ne_zero y z hj]
    all_goals rfl
  · rw [if_neg h, if_neg h]

lemma sumR_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then ‖(ins y z).2.1 j‖ ^ 2 else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then ‖(tailPt y).2.1 j‖ ^ 2 else 0 := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i.succ.val ≤ j.val
  · have hj : j ≠ 0 := by
      rintro rfl
      simp at h
    rw [if_pos h, if_pos h, ins_snd_fst_eq_tailPt_snd_fst_of_ne_zero y z hj]
  · rw [if_neg h, if_neg h]

lemma rhoSq_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    rhoSq (ins y z) i.succ = rhoSq (tailPt y) i.succ := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  rw [Lsq_ins, sumR_ins_succ]
  all_goals rfl

lemma bco_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    bco (ins y z) i.succ = bco (tailPt y) i.succ := by
  have h : (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then (ins y z).2.1 j * star ((ins y z).1 j) else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).2.1 j * star ((ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).1 j) else 0 :=
    sum_ins_succ y z i (fun a b => a * star b)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.bco
  rw [h]
  all_goals rfl

lemma de_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    de (ins y z) i.succ = de (tailPt y) i.succ := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  rw [Lsq_ins, rhoSq_ins_succ, bco_ins_succ]

lemma Lsq_ge_one {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ Lsq x l := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.Lsq
  have : 0 ≤ ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  linarith

lemma Lsq_mono {p m : ℕ} (x : Xp p m) {l l' : Fin (p + 1)} (h : l ≤ l') : Lsq x l ≤ Lsq x l' := by
  have h' : l.val ≤ l'.val := Fin.le_iff_val_le_val.mp h
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.Lsq
  have : ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) ≤
      ∑ j : Fin p, (if j.val < l'.val then ‖x.1 j‖ ^ 2 else 0) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases h1 : j.val < l.val
    · have h2 : j.val < l'.val := lt_of_lt_of_le h1 h'
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1]
      split_ifs <;> positivity
  linarith

lemma rhoSq_ge {p m : ℕ} (x : Xp p m) (l l' : Fin (p + 1)) : Lsq x l' ≤ rhoSq x l := by
  have h1 := Lsq_mono x (Fin.le_last l')
  have h2 : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  have h3 : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  linarith

lemma de_ge_one {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ de x l := by
  have hL := Lsq_ge_one x l
  have hR : 1 ≤ ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq x l := le_trans hL (rhoSq_ge x l l)
  have hc : 0 ≤ ‖ReciprocityTheory.ChartRestriction.DS.Xi.bco x l‖ ^ 2 := by positivity
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)

def splitE (p m : ℕ) : Xp (p + 1) m ≃ᵐ Yp p m × ℂ :=
  ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prodCongr
        (MeasurableEquiv.refl ((Fin m → ℂ) × ℝ)))).trans
    (((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr MeasurableEquiv.prodAssoc).trans
      (MeasurableEquiv.prodAssoc.symm.trans
        ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans
          (MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm))))

lemma splitE_mp (p m : ℕ) : MeasurePreserving (splitE p m) volume volume := by
  have e1 : MeasurePreserving ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prodCongr
        (MeasurableEquiv.refl ((Fin m → ℂ) × ℝ)))) volume volume :=
    (MeasurePreserving.id volume).prod
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prod (MeasurePreserving.id volume))
  have e2 : MeasurePreserving ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      (MeasurableEquiv.prodAssoc :
        (ℂ × (Fin p → ℂ)) × ((Fin m → ℂ) × ℝ) ≃ᵐ ℂ × (Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) volume volume :=
    (MeasurePreserving.id volume).prod volume_preserving_prodAssoc
  have e3 : MeasurePreserving (MeasurableEquiv.prodAssoc :
      ((Fin (p + 1) → ℂ) × ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)) ≃ᵐ
        (Fin (p + 1) → ℂ) × ℂ × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))).symm volume volume :=
    MeasurePreserving.symm _ volume_preserving_prodAssoc
  have e4 : MeasurePreserving ((MeasurableEquiv.prodComm :
      (Fin (p + 1) → ℂ) × ℂ ≃ᵐ ℂ × (Fin (p + 1) → ℂ)).prodCongr
      (MeasurableEquiv.refl ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)))) volume volume :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id volume)
  have e5 : MeasurePreserving (MeasurableEquiv.prodAssoc :
      (ℂ × (Fin (p + 1) → ℂ)) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)) ≃ᵐ
        ℂ × (Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) volume volume :=
    volume_preserving_prodAssoc
  have e6 : MeasurePreserving (MeasurableEquiv.prodComm :
      ℂ × ((Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) ≃ᵐ
        ((Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) × ℂ) volume volume :=
    Measure.measurePreserving_swap
  exact e6.comp (e5.comp (e4.comp (e3.comp (e2.comp e1))))

lemma ins_splitE {p m : ℕ} (x : Xp (p + 1) m) : ins (splitE p m x).1 (splitE p m x).2 = x := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ k =>
    show x.2.1 (Fin.succAbove 0 k) = x.2.1 k.succ
    simp

lemma split_le {p m : ℕ} (G : Xp (p + 1) m → ℝ≥0∞) :
    ∫⁻ x, G x ≤ ∫⁻ y : Yp p m, ∫⁻ z : ℂ, G (ins y z) := by
  have h := (splitE_mp p m).lintegral_comp_emb (splitE p m).measurableEmbedding
    (fun w => G (ins w.1 w.2))
  simp only [ins_splitE] at h
  exact h.trans_le (lintegral_prod_le _)

lemma cont_Lsq {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => Lsq x l) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.Lsq
  exact continuous_const.fun_add (continuous_finsetSum _ (fun j _ => by
    by_cases h : j.val < l.val <;> simp only [h, ↓reduceIte] <;> fun_prop))

lemma cont_rhoSq {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => rhoSq x l) := by
  have h1 := cont_Lsq (p := p) (m := m) (Fin.last p)
  have h2 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ i, ‖x.2.2.1 i‖ ^ 2 :=
    continuous_finsetSum _ (fun i _ => by fun_prop)
  have h3 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ j : Fin p, if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0 :=
    continuous_finsetSum _ (fun j _ => by
      by_cases h : l.val ≤ j.val <;> simp only [h, ↓reduceIte] <;> fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  exact (h1.add h2).add h3

lemma cont_bco {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => bco x l) := by
  have h00 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ i, ‖x.2.2.1 i‖ ^ 2 :=
    continuous_finsetSum _ (fun i _ => by fun_prop)
  have h0 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m =>
      (((-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 : ℝ)) : ℂ) + (x.2.2.2 : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp (h00.neg.div_const 2)).add
      ((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => x.2.2.2)).mul continuous_const)
  have hs : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ j : Fin p, if l.val ≤ j.val then x.2.1 j * star (x.1 j) else 0 :=
    continuous_finsetSum _ (fun j _ => by
      by_cases h : l.val ≤ j.val <;> simp only [h, ↓reduceIte] <;> fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.bco
  exact h0.sub hs

lemma cont_de {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => de x l) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  exact Real.continuous_sqrt.comp
    (((cont_Lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

lemma cont_linF {p m : ℕ} (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) : Continuous (linF η η' ζ) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.linF
  exact (continuous_finsetSum _ fun j _ => by fun_prop).add (continuous_finsetSum _ fun i _ => by fun_prop)

lemma cont_tailPt {p m : ℕ} : Continuous (fun y : Yp p m => tailPt y) := by
  have hmid : Continuous fun y : Yp p m => (Fin.cons (0 : ℂ) y.2.1 : Fin (p + 1) → ℂ) :=
    continuous_pi (fun j => by
      induction j using Fin.cases with
      | zero => simp only [Fin.cons_zero]; exact continuous_const
      | succ k => simp only [Fin.cons_succ]; fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.tailPt
  fun_prop

lemma meas_fS {p m : ℕ} (s : Fin (p + 2) → ℝ) : Measurable (fS (p := p) (m := m) s) := by
  unfold fS
  exact Finset.measurable_prod _ (fun l _ =>
    ENNReal.measurable_ofReal.comp ((cont_de (p := p + 1) (m := m) l).measurable.pow_const _))

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

