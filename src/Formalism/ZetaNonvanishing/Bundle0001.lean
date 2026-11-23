module

public import Formalism.Bundle0001

@[expose] public section

-- bundled from Formalism.ZetaNonvanishing.Assembly
section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

section SlopeTestRemainingChoices

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

lemma Pfun_eq_of_ne {s : ℂ} (hs : s ≠ 1) :
    Pfun χ s = (s - 1) * riemannZeta s * DirichletCharacter.LFunction χ s := by
  simp [Pfun, hs]

lemma Pfun_one : Pfun χ 1 = DirichletCharacter.LFunction χ 1 := by simp [Pfun]

lemma Pfun_ne_zero_of_one_le_re (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : Pfun χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1
    rw [Pfun_one]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp)
  · rw [Pfun_eq_of_ne χ h1]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs))
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs)

lemma deriv_Pfun_of_ne {s : ℂ} (hs : s ≠ 1) :
    deriv (Pfun χ) s = riemannZeta s * DirichletCharacter.LFunction χ s
      + (s - 1) * deriv riemannZeta s * DirichletCharacter.LFunction χ s
      + (s - 1) * riemannZeta s * deriv (DirichletCharacter.LFunction χ) s := by
  have heq : Pfun χ =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z * DirichletCharacter.LFunction χ z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact Pfun_eq_of_ne χ hz
  rw [heq.deriv_eq]
  have h : HasDerivAt (fun z => (z - 1) * riemannZeta z * DirichletCharacter.LFunction χ z)
      ((1 * riemannZeta s + (s - 1) * deriv riemannZeta s) * DirichletCharacter.LFunction χ s +
        (s - 1) * riemannZeta s * deriv (DirichletCharacter.LFunction χ) s) s :=
    (((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt).mul
      (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).hasDerivAt
  rw [h.deriv]
  ring

lemma LSeries_LamF_eq (hχ : χ ≠ 1) (h4 : LSeriesLamF) (hreal : ∀ n : ℕ, (χ n).im = 0)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (LamF χ n : ℂ)) s = -deriv (Pfun χ) s / Pfun χ s + 1 / (s - 1) := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hre : 1 ≤ s.re := hs.le
  have hz := riemannZeta_ne_zero_of_one_le_re hre
  have hL := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [h4 N χ hreal s hs, deriv_Pfun_of_ne χ hs1, Pfun_eq_of_ne χ hs1]
  field_simp
  ring

end SlopeTestRemainingChoices

section Mellin

lemma cint_of_abs (f : ℝ → ℝ) (hf : Measurable f) (s : ℂ)
    (hI : IntegrableOn (fun x : ℝ => |f x| * x ^ (-s.re - 1)) (Ioi 1)) :
    IntegrableOn (fun x : ℝ => (f x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  refine Integrable.mono' hI ?_ ?_
  · exact ((Complex.measurable_ofReal.comp hf).mul
      (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp

lemma int_abs_rpow (h5 : MellinElem) {a σ : ℝ} (h : a < σ) :
    IntegrableOn (fun x : ℝ => |x ^ a| * x ^ (-σ - 1)) (Ioi 1) := by
  refine (h5.1 a σ h).congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
  simp only [abs_of_nonneg (Real.rpow_nonneg hx0.le a)]

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

lemma mellin_H (h3 : MellinS) (h5 : MellinElem) (σ₀ C : ℝ) {s : ℂ} (hs : 1 < s.re)
    (hσ₀ : σ₀ < 1) :
    ∫ x in Ioi (1:ℝ), ((G χ x + C * x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      LSeries (fun n => (LamF χ n : ℂ)) s / (s * (s - 1)) - 1 / (s - 1) ^ 2
        + (1 + gammaF χ) * (1 / (s - 1)) + C * (1 / (s - σ₀)) := by
  have hS := h3 N χ
  have i1 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ hS.1 s (hS.2.1 _ hs)
  have i2 : IntegrableOn (fun x : ℝ => ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (h5.2.1 _ hs)
  have i3 : IntegrableOn (fun x : ℝ => ((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have i4 : IntegrableOn (fun x : ℝ => ((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have hfun : (fun x : ℝ => ((G χ x + C * x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) =
      fun x => ((S χ x : ℂ) * (x : ℂ) ^ (-s - 1) - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
        + ((1 + gammaF χ : ℝ) : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)))
        + (C : ℂ) * (((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [G, Real.rpow_one]
    push_cast
    ring
  have j12 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)
      - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := Integrable.sub i1 i2
  have j3 : IntegrableOn (fun x : ℝ => ((1 + gammaF χ : ℝ) : ℂ) *
      (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) := Integrable.const_mul i3 _
  have j4 : IntegrableOn (fun x : ℝ => (C : ℂ) *
      (((x ^ σ₀ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) := Integrable.const_mul i4 _
  have j123 : IntegrableOn (fun x : ℝ => (S χ x : ℂ) * (x : ℂ) ^ (-s - 1)
      - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      + ((1 + gammaF χ : ℝ) : ℂ) * (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) :=
    Integrable.add j12 j3
  rw [hfun, integral_add j123 j4, integral_add j12 j3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
    hS.2.2 s hs, h5.2.2.2 s hs, h5.2.2.1 1 s (by simpa using hs), h5.2.2.1 σ₀ s (by linarith)]
  push_cast
  ring

end Mellin

section Main

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

def Hf (σ₀ C : ℝ) (x : ℝ) : ℝ := G χ x + C * x ^ σ₀

def Imel (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), ((Hf χ σ₀ C x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

def q0 (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  -1 + s * (1 + (gammaF χ : ℂ)) + C * s * (s - 1) / (s - σ₀)

def Afun (σ₀ C : ℝ) (s : ℂ) : ℂ :=
  -deriv (Pfun χ) s - Pfun χ s + s * (1 + (gammaF χ : ℂ)) * Pfun χ s
    + C * s * (s - 1) * Pfun χ s / (s - σ₀)

def Phi (σ₀ C : ℝ) (s : ℂ) : ℂ := dslope (Afun χ σ₀ C) 1 s / (s * Pfun χ s)

lemma ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  rintro rfl
  simp at hs

lemma sub_ne_zero_of_lt_re {s : ℂ} {a : ℝ} (hs : a < s.re) : s - a ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma ne_zero_of_lt_re {s : ℂ} {a : ℝ} (ha : 0 ≤ a) (hs : a < s.re) : s ≠ 0 := by
  rintro rfl
  simp at hs
  linarith

lemma key_identity (hχ : χ ≠ 1) (h3 : MellinS) (h4 : LSeriesLamF) (h5 : MellinElem)
    (hreal : ∀ n : ℕ, (χ n).im = 0) {σ₀ C : ℝ} (hσ₀1 : σ₀ < 1) {s : ℂ}
    (hs : 1 < s.re) :
    s * (s - 1) * Imel χ σ₀ C s = -deriv (Pfun χ) s / Pfun χ s + q0 χ σ₀ C s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hs)
  have hs0 : s ≠ 0 := ne_zero_of_lt_re zero_le_one hs
  have hsσ : s - σ₀ ≠ 0 := sub_ne_zero_of_lt_re (a := σ₀) (by linarith)
  have hP : Pfun χ s ≠ 0 := Pfun_ne_zero_of_one_le_re χ hχ hs.le
  have hm := mellin_H χ h3 h5 σ₀ C hs hσ₀1
  unfold Imel Hf
  rw [hm, LSeries_LamF_eq χ hχ h4 hreal hs]
  unfold q0
  field_simp
  ring

end Main

end Formalism
end
end

-- bundled from Formalism.ZetaNonvanishing.MellinSAux
section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def mxS (n : ℕ) (x : ℝ) : ℝ := max (x / n - 1) 0

lemma mxS_nonneg (n : ℕ) (x : ℝ) : 0 ≤ mxS n x := by
  show 0 ≤ max (x / n - 1) 0
  exact le_max_right _ _

lemma mxS_eq_indicator {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    mxS n x = (Ioi (n : ℝ)).indicator (fun x => x / n - 1) x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  show max (x / n - 1) 0 = _
  by_cases hx : x ∈ Ioi (n : ℝ)
  · rw [Set.indicator_of_mem hx]
    have h1 : 1 ≤ x / n := by
      rw [le_div_iff₀ hn0]
      have := Set.mem_Ioi.mp hx
      linarith
    exact max_eq_left (sub_nonneg.mpr h1)
  · rw [Set.indicator_of_notMem hx]
    have h1 : x / n ≤ 1 := (div_le_one hn0).mpr (le_of_not_gt (fun h => hx (Set.mem_Ioi.mpr h)))
    exact max_eq_right (sub_nonpos.mpr h1)

lemma mxS_mellin {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1) = (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsub : Ioi (n : ℝ) ⊆ Ioi 1 := Ioi_subset_Ioi hn1
  have ha : (-s).re < -1 := by
    simp only [Complex.neg_re]
    linarith
  have hb : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h'
    linarith
  have hs2 : -s + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at h'
    linarith

  have hfun : (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) =
      (Ioi (n : ℝ)).indicator (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    rw [mxS_eq_indicator hn x]
    by_cases hx : x ∈ Ioi (n : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Complex.ofReal_zero, zero_mul]
  have heq : EqOn (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)) (Ioi (n : ℝ)) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans hn0 (Set.mem_Ioi.mp hx)).ne'
    have hpow : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * x := by
      calc (x : ℂ) ^ (-s) = (x : ℂ) ^ ((-s - 1) + 1) := by rw [sub_add_cancel]
        _ = (x : ℂ) ^ (-s - 1) * x := by rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
    show ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)
    rw [hpow]
    push_cast
    ring
  have hA : Integrable (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s)) (volume.restrict (Ioi (n : ℝ))) :=
    Integrable.const_mul (integrableOn_Ioi_cpow_of_lt ha hn0) (1 / (n : ℂ))
  have hB : Integrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (volume.restrict (Ioi (n : ℝ))) :=
    integrableOn_Ioi_cpow_of_lt hb hn0
  have hint : IntegrableOn (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1))
      (Ioi (n : ℝ)) := hA.sub hB
  have hg := hint.congr_fun heq.symm measurableSet_Ioi
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul,
    integral_Ioi_cpow_of_lt ha hn0, integral_Ioi_cpow_of_lt hb hn0, sub_add_cancel,
    Complex.ofReal_natCast, Complex.cpow_add _ _ hnC, Complex.cpow_one]
  field_simp
  ring

lemma mxS_mellin_real {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => mxS n x * x ^ (-σ - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), mxS n x * x ^ (-σ - 1) = (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsub : Ioi (n : ℝ) ⊆ Ioi 1 := Ioi_subset_Ioi hn1
  have ha : -σ < -1 := by linarith
  have hb : -σ - 1 < -1 := by linarith
  have hσ0 : σ ≠ 0 := (by linarith : (0 : ℝ) < σ).ne'
  have hσ1 : σ - 1 ≠ 0 := (by linarith : (0 : ℝ) < σ - 1).ne'
  have hσ2 : -σ + 1 ≠ 0 := (by linarith : -σ + 1 < 0).ne
  have hnR : (n : ℝ) ≠ 0 := hn0.ne'

  have hfun : (fun x : ℝ => mxS n x * x ^ (-σ - 1)) =
      (Ioi (n : ℝ)).indicator (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1)) := by
    funext x
    rw [mxS_eq_indicator hn x]
    by_cases hx : x ∈ Ioi (n : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have heq : EqOn (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1))
      (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)) (Ioi (n : ℝ)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hn0 (Set.mem_Ioi.mp hx)
    have hpow : x ^ (-σ) = x ^ (-σ - 1) * x := by
      calc x ^ (-σ) = x ^ ((-σ - 1) + 1) := by rw [sub_add_cancel]
        _ = x ^ (-σ - 1) * x := by rw [Real.rpow_add hx0, Real.rpow_one]
    show (x / n - 1) * x ^ (-σ - 1) = 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)
    rw [hpow]
    ring
  have hA : Integrable (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ)) (volume.restrict (Ioi (n : ℝ))) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt ha hn0) (1 / (n : ℝ))
  have hB : Integrable (fun x : ℝ => x ^ (-σ - 1)) (volume.restrict (Ioi (n : ℝ))) :=
    integrableOn_Ioi_rpow_of_lt hb hn0
  have hint : IntegrableOn (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1))
      (Ioi (n : ℝ)) := hA.sub hB
  have hg := hint.congr_fun heq.symm measurableSet_Ioi
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul,
    integral_Ioi_rpow_of_lt ha hn0, integral_Ioi_rpow_of_lt hb hn0, sub_add_cancel,
    Real.rpow_add hn0, Real.rpow_one]
  field_simp
  ring

lemma integrable_tsum_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : ℕ → α → ℝ} (hφ : ∀ n, Integrable (φ n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ φ n x)
    (hsx : ∀ x, Summable (fun n => φ n x)) (hs : Summable fun n => ∫ x, φ n x ∂μ) :
    Integrable (fun x => ∑' n, φ n x) μ := by
  have hall : ∀ᵐ x ∂μ, ∀ n, 0 ≤ φ n x := ae_all_iff.mpr h0
  have hm : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (φ n x)) μ :=
    fun n => (hφ n).aemeasurable.ennreal_ofReal
  have hmeas : AEMeasurable (fun x => ∑' n, ENNReal.ofReal (φ n x)) μ :=
    AEMeasurable.tsum hm
  have hlin : ∫⁻ x, ∑' n, ENNReal.ofReal (φ n x) ∂μ = ENNReal.ofReal (∑' n, ∫ x, φ n x ∂μ) := by
    rw [lintegral_tsum hm,
      ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg_of_ae (h0 n)) hs]
    exact tsum_congr fun n => (ofReal_integral_eq_lintegral_ofReal (hφ n) (h0 n)).symm
  have hint := integrable_toReal_of_lintegral_ne_top hmeas (by rw [hlin]; exact ENNReal.ofReal_ne_top)
  refine hint.congr ?_
  filter_upwards [hall] with x hx
  rw [← ENNReal.ofReal_tsum_of_nonneg hx (hsx x), ENNReal.toReal_ofReal (tsum_nonneg hx)]

end Formalism
end
end

