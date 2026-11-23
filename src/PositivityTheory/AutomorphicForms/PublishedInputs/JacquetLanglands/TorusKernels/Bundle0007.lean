module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Bundle0002

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ActionsPreserveMeasuresProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ActionsPreserveMeasuresLemmas

open UpperTheory.Esk

theorem count_pres {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] (f : α → α)
    (hf : Function.Bijective f) : MeasurePreserving f Measure.count Measure.count := by
  refine ⟨measurable_of_countable f, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_of_countable f) hs, Measure.count_apply hs,
    Measure.count_apply ((Set.to_countable _).measurableSet)]
  congr 1
  exact Set.encard_preimage_of_injective_subset_range hf.1 (hf.2.range_eq ▸ Set.subset_univ s)

theorem countable_PG (F : Type) [Field F] [Countable F] : Countable (PG F) := by
  have : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  have : Countable (GL (Fin 2) F) :=
    Function.Injective.countable (f := fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) fun a b h => Units.ext h
  exact QuotientGroup.mk_surjective.countable

theorem smulX {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (g : GL (Fin 2) F) (z : D.Xs) :
    ((g : PG F) • z) = (fun v => D.r v g • z v : I → P) := rfl

end UpperTheory.Esk.ActionsPreserveMeasuresLemmas

open UpperTheory.Esk.ActionsPreserveMeasuresLemmas in
theorem UpperTheory.Esk.actions_preserve_measures_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a := by
  intro h1 h2 h3 F I Gf _ _ _ D ax
  have : SigmaFinite (volume : Measure P) := h1.1
  have : (volume : Measure P).IsOpenPosMeasure := h1.2.1
  have : Countable F := ax.cF
  have hPG : Countable (PG F) := countable_PG F
  have : Countable D.Om := ax.cO
  have : Countable D.Cj := hPG
  have hXs : SigmaFinite (volume : Measure D.Xs) :=
    show SigmaFinite (Measure.pi fun _ : I => (volume : Measure P)) from inferInstance
  have presX : ∀ γ : PG F, MeasurePreserving (fun z : D.Xs => γ • z) volume volume := by
    intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    simp only [smulX]
    exact measurePreserving_pi (fun _ : I => (volume : Measure P)) (fun _ : I => (volume : Measure P))
      (fun v => (h1.2.2 (D.r v g)).2)
  have contX : ∀ γ : PG F, Continuous fun z : D.Xs => γ • z := by
    intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    simp only [smulX]
    exact continuous_pi fun v => (h1.2.2 (D.r v g)).1.comp (continuous_apply v)
  refine ⟨hPG, hXs, presX, ?_, ?_, contX, inferInstanceAs (BorelSpace (I → P)), ?_⟩
  · intro γ
    exact (count_pres (fun ω : D.Om => γ • ω) (MulAction.bijective γ)).prod (presX γ)
  · intro γ
    exact (count_pres (fun ω : D.Cj × D.Om => γ • ω) (MulAction.bijective γ)).prod (presX γ)
  · intro δ hδ
    have hk : Continuous fun p : P × P => kap p.1 p.2 := h3.2.2.2.2.1
    have hk1 : ∀ z : P, Continuous fun w => kap z w := fun z => hk.comp (continuous_const.prodMk continuous_id)
    set U : Set P := {w | δ < kap iP w} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const (hk1 iP)
    have hUp : 0 < volume U := hUo.measure_pos volume ⟨iP, by
      show δ < kap iP iP
      rw [h3.2.1 iP]; exact hδ⟩
    obtain ⟨c0, hc0, hc0U⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hUp
    have hS : ∀ z : P, MeasurableSet {w | δ ≤ kap z w} := fun z =>
      measurableSet_le measurable_const (hk1 z).measurable
    have hball : ∀ z : P, (c0 : ℝ≥0∞) ≤ volume {w | δ ≤ kap z w} := by
      intro z
      obtain ⟨g, -, -, hg⟩ := h3.2.2.2.2.2 z
      have hf := (h1.2.2 g).2
      have hpre : (fun w : P => g • w) ⁻¹' {w | δ ≤ kap z w} = {w | δ ≤ kap iP w} := by
        ext w
        show δ ≤ kap z (g • w) ↔ δ ≤ kap iP w
        rw [← hg, h2.2.2.2.1 g iP w]
      rw [← hf.measure_preimage (hS z).nullMeasurableSet, hpre]
      refine hc0U.le.trans (measure_mono fun w hw => ?_)
      exact le_of_lt (show δ < kap iP w from hw)
    refine ⟨c0 ^ Fintype.card I, pow_pos (by exact_mod_cast hc0) _, fun z => ?_⟩
    have hset : {w : X I | Near δ z w} = Set.univ.pi fun v => {w | δ ≤ kap (z v) w} := by
      ext w
      simp [Near, Set.mem_pi]
    rw [hset]
    refine ⟨MeasurableSet.univ_pi fun v => hS (z v), ?_⟩
    rw [volume_pi, Measure.pi_pi, ENNReal.coe_pow, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun v _ => hball (z v)
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AutomorphyFactorKernelAlgebraProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

theorem den_mul (g h : GL (Fin 2) ℝ) (z : P) : den (g * h) z.1 = den g (h • z).1 * den h z.1 := by
  have h0 := den_ne h z.2
  rw [coe_smul]
  conv_rhs => rw [den, add_mul, mul_assoc, div_mul_cancel₀ _ h0]
  simp [num, den, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem p1 (k : ℕ) (g h : GL (Fin 2) ℝ) (z : P) : j1 k (g * h) z = j1 k g (h • z) * j1 k h z := by
  simp only [j1, den_mul, mul_pow, Units.val_mul, Matrix.det_mul, abs_mul,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _), Complex.ofReal_mul]
  ring

theorem p2 (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : j1 k g z ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (den_ne g z.2))
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (abs_pos.2 g.det_ne_zero) _).ne')

theorem im_smul (g : GL (Fin 2) ℝ) (z : P) :
    (g • z).1.im = g.val.det * z.1.im / Complex.normSq (den g z.1) := by
  rw [coe_smul, im_div]

theorem sub_conj (g : GL (Fin 2) ℝ) (z w : P) :
    (g • z).1 - conj (g • w).1 = (g.val.det : ℂ) * (z.1 - conj w.1) / (den g z.1 * conj (den g w.1)) := by
  rw [coe_smul, coe_smul, map_div₀, div_sub_div _ _ (den_ne g z.2) ((map_ne_zero _).2 (den_ne g w.2))]
  congr 1
  simp only [num, den, map_add (f := _), map_mul, Complex.conj_ofReal, det_eq]
  push_cast
  ring

theorem sign (g : GL (Fin 2) ℝ) (z w : P) : 0 < (g • z).1.im * (g • w).1.im ↔ 0 < z.1.im * w.1.im := by
  rw [im_smul, im_smul]
  have hd : g.val.det ≠ 0 := g.det_ne_zero
  have nz : 0 < Complex.normSq (den g z.1) := Complex.normSq_pos.2 (den_ne g z.2)
  have nw : 0 < Complex.normSq (den g w.1) := Complex.normSq_pos.2 (den_ne g w.2)
  have hc : 0 < g.val.det ^ 2 / (Complex.normSq (den g z.1) * Complex.normSq (den g w.1)) :=
    div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hd))) (mul_pos nz nw)
  rw [show g.val.det * z.1.im / Complex.normSq (den g z.1) * (g.val.det * w.1.im / Complex.normSq (den g w.1))
      = g.val.det ^ 2 / (Complex.normSq (den g z.1) * Complex.normSq (den g w.1)) * (z.1.im * w.1.im) by
    field_simp]
  exact ⟨fun h => pos_of_mul_pos_right h hc.le, fun h => mul_pos hc h⟩

theorem ratio (g : GL (Fin 2) ℝ) (z w : P) (h : 0 < z.1.im * w.1.im) :
    ((g • w).1 - conj (g • w).1) / ((g • z).1 - conj (g • w).1)
      = (w.1 - conj w.1) / (z.1 - conj w.1) * (den g z.1 / den g w.1) := by
  have hd : (g.val.det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 g.det_ne_zero
  have h1 := den_ne g z.2
  have h2 := den_ne g w.2
  have h3 : conj (den g w.1) ≠ 0 := (map_ne_zero _).2 h2
  have h4 : z.1 - conj w.1 ≠ 0 := b_ne _ _ h
  have h5 : w.1 - conj w.1 ≠ 0 := b_ne _ _ (mul_self_pos.2 w.2)
  rw [sub_conj, sub_conj]
  field_simp

theorem p3 (k : ℕ) (g : GL (Fin 2) ℝ) (z w : P) :
    q1 k (g • z) (g • w) * j1 k g w = j1 k g z * q1 k z w := by
  unfold q1
  rw [if_congr (sign g z w) rfl rfl]
  split_ifs with h
  · rw [ratio g z w h, mul_pow, div_pow (den g z.1)]
    have h2 := pow_ne_zero k (den_ne g w.2)
    simp only [j1]
    field_simp
  · simp

theorem p4 (g : GL (Fin 2) ℝ) (z w : P) : kap (g • z) (g • w) = kap z w := by
  unfold kap
  rw [if_congr (sign g z w) rfl rfl]
  split_ifs with h
  · have hd : g.val.det ≠ 0 := g.det_ne_zero
    have nz : 0 < Complex.normSq (den g z.1) := Complex.normSq_pos.2 (den_ne g z.2)
    have nw : 0 < Complex.normSq (den g w.1) := Complex.normSq_pos.2 (den_ne g w.2)
    have h4 : ‖z.1 - conj w.1‖ ≠ 0 := norm_ne_zero_iff.2 (b_ne _ _ h)
    rw [im_smul, im_smul, sub_conj, norm_div, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, div_pow, mul_pow, mul_pow, sq_abs]
    simp only [Complex.sq_norm]
    field_simp
  · rfl

end UpperTheory.Esk.AutomorphyFactorLemmas

namespace UpperTheory.Esk

open AutomorphyFactorLemmas in
theorem automorphy_factor_kernel_algebra_proof : B1b :=
  ⟨p1, p2, p3, p4, p5, fun k z w hk => p6 k z w hk, p7, p8, p9⟩

end UpperTheory.Esk
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ConjNeOne
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

theorem key_id (α β u ub : ℂ) (hα : α ≠ 0) (hu : 1 - u ≠ 0) (h1 : β - α * u ≠ 0) (h2 : α - β * ub ≠ 0)
    (hA : α - β * u * ub ≠ 0) :
    (Complex.I * (β + α * u) / (β - α * u) - -Complex.I * (α + β * ub) / (α - β * ub)) /
      (Complex.I * (1 + u) / (1 - u) - -Complex.I * (α + β * ub) / (α - β * ub)) * ((β - α * u) / (1 - u)) =
      β * (1 - u * ub) / (1 - β / α * (u * ub)) := by
  have hI := Complex.I_ne_zero
  have e1 : Complex.I * (1 + u) / (1 - u) - -Complex.I * (α + β * ub) / (α - β * ub) =
      2 * Complex.I * (α - β * u * ub) / ((1 - u) * (α - β * ub)) := by
    field_simp; ring
  have e2 : Complex.I * (β + α * u) / (β - α * u) - -Complex.I * (α + β * ub) / (α - β * ub) =
      2 * Complex.I * α * β * (1 - u * ub) / ((β - α * u) * (α - β * ub)) := by
    field_simp; ring
  have e3 : 1 - β / α * (u * ub) = (α - β * u * ub) / α := by field_simp
  rw [e1, e2, e3]
  field_simp

theorem pow_combine (c X Y S T : ℂ) (k : ℕ) (h : X * Y / S = T) :
    c * X ^ k * (Y ^ k * (S ^ k)⁻¹) = c * T ^ k := by
  rw [← h, div_pow, mul_pow]; ring

theorem cayley_val (k : ℕ) (m : GL (Fin 2) ℝ) (a b : ℝ) (h00 : m 0 0 = a) (h01 : m 0 1 = b)
    (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ext1 (U k m) (Complex.I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ)) =
      ((k : ℂ) - 1) / (4 * Real.pi) * (eta a b * (1 - (r : ℂ) ^ 2) / (1 - eta a b ^ 2 * (r : ℂ) ^ 2)) ^ k := by
  set u := circleMap 0 r θ with hu_def
  have hnu : ‖u‖ = r := by simp [u, abs_of_pos hr0]
  have hu1 : (1 : ℂ) - u ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hnu; linarith
  have huu : u * conj u = (r : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnu]; push_cast; ring
  have hn : u.re ^ 2 + u.im ^ 2 = r ^ 2 := by
    rw [← hnu, Complex.sq_norm, Complex.normSq_apply]; ring
  set z := Complex.I * (1 + u) / (1 - u) with hz_def
  have hz_im : z.im = (1 - r ^ 2) / Complex.normSq (1 - u) := by
    rw [hz_def, Complex.div_im, ← sub_div]
    congr 1
    simp
    nlinarith [hn]
  have hzpos : 0 < z.im := by
    rw [hz_im]
    apply div_pos
    · nlinarith
    · exact Complex.normSq_pos.2 hu1
  have hz : z.im ≠ 0 := hzpos.ne'
  set zP : P := ⟨z, hz⟩ with hzP
  have hzP1 : zP.1 = z := rfl
  have hzpos' : 0 < zP.1.im := hzpos
  have hext : ext1 (U k m) z = F k m zP := by
    unfold ext1; rw [dite_eq_left hz]; exact if_pos hzpos'
  have hab : 0 < a ^ 2 + b ^ 2 := by
    have := lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 hb)); nlinarith [sq_nonneg a]
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (a ^ 2 + b ^ 2) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.2 hab
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := by rw [hs_def]; exact Real.sq_sqrt hab.le
  have hS0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hα0 : (a : ℂ) + b * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hb this
  have hβ0 : (a : ℂ) - b * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hb this
  have hden : den m z = (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u) / (1 - u) := by
    rw [eq_div_iff hu1]; unfold den; rw [h10, h11, hz_def]; push_cast; field_simp; ring
  have hnum : num m z = Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) / (1 - u) := by
    rw [eq_div_iff hu1]; unfold num; rw [h00, h01, hz_def]; field_simp
    linear_combination (b * (1 - u)) * Complex.I_sq
  have h1 : ((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u ≠ 0 := by
    have := den_ne m hz; rw [hden] at this; exact (div_ne_zero_iff.1 this).1
  have h2 : ((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * conj u ≠ 0 := by
    have h := (map_ne_zero (starRingEnd ℂ)).2 h1
    convert h using 1
    simp only [map_sub, map_mul, map_add (f := _), Complex.conj_ofReal, Complex.conj_I]; ring
  have hA : ((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * u * conj u ≠ 0 := by
    intro h
    rw [mul_assoc, huu, ← Complex.ofReal_pow] at h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.zero_im] at this
    have h3 : b * (1 + r ^ 2) = 0 := by
      linear_combination this
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hb h4
    · nlinarith [sq_nonneg r]
  have hw : (m • zP).1 = Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) /
      (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u) := by
    rw [coe_smul, hzP1, hnum, hden, div_div_div_cancel_right₀ hu1]
  have hwb : conj (Complex.I * (((a : ℂ) - b * Complex.I) + ((a : ℂ) + b * Complex.I) * u) /
      (((a : ℂ) - b * Complex.I) - ((a : ℂ) + b * Complex.I) * u)) =
      -Complex.I * (((a : ℂ) + b * Complex.I) + ((a : ℂ) - b * Complex.I) * conj u) /
      (((a : ℂ) + b * Complex.I) - ((a : ℂ) - b * Complex.I) * conj u) := by
    simp only [map_div₀, map_sub, map_mul, map_add (f := _), Complex.conj_ofReal, Complex.conj_I]; ring
  have hwim : 0 < (m • zP).1.im := by
    rw [coe_smul, im_div, det_eq, h00, h01, h10, h11]
    apply div_pos (mul_pos (by nlinarith) hzpos') (Complex.normSq_pos.2 (den_ne m hz))
  have hdet : |m.val.det| = s ^ 2 := by
    rw [det_eq, h00, h01, h10, h11, hs2, abs_of_pos (by nlinarith)]; ring
  have hrp : (|m.val.det| ^ (-(k : ℝ) / 2) : ℝ) = (s ^ k)⁻¹ := by
    rw [hdet, ← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le,
      show ((2 : ℕ) : ℝ) * (-(k : ℝ) / 2) = -(k : ℝ) by push_cast; ring, Real.rpow_neg hs.le, Real.rpow_natCast]
  have hηsq : (((a : ℂ) - b * Complex.I) / (s : ℂ)) ^ 2 = ((a : ℂ) - b * Complex.I) / ((a : ℂ) + b * Complex.I) := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hS0) hα0, ← Complex.ofReal_pow, hs2]
    push_cast
    linear_combination (-((a : ℂ) - b * Complex.I) * (b : ℂ) ^ 2) * Complex.I_sq
  rw [hext]
  unfold F q1 j1
  rw [if_pos (mul_pos hzpos' hwim), hrp]
  push_cast
  refine pow_combine _ _ _ _ _ k ?_
  rw [hw, hwb, hzP1, hden, key_id _ _ _ _ hα0 hu1 h1 h2 hA, ← huu, eta, ← hs_def, hηsq]
  field_simp

end UpperTheory.Esk.RadialIntegralLemmas
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.CuspRegionVolumeFiniteProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.CuspRegionVolume

open UpperTheory.Esk

def B1 (C c : ℝ) : Set {z : ℂ // z.im ≠ 0} := {w | |w.1.re| ≤ C ∧ c ≤ |w.1.im|}

theorem measurableSet_cusp_region (C c : ℝ) : MeasurableSet (B1 C c) := by
  have h1 : Measurable fun w : {z : ℂ // z.im ≠ 0} => |w.1.re| :=
    (continuous_abs.comp (Complex.continuous_re.comp continuous_subtype_val)).measurable
  have h2 : Measurable fun w : {z : ℂ // z.im ≠ 0} => |w.1.im| :=
    (continuous_abs.comp (Complex.continuous_im.comp continuous_subtype_val)).measurable
  exact (measurableSet_le h1 measurable_const).inter (measurableSet_le measurable_const h2)

theorem pt_bound (C c : ℝ) (hc : 0 < c) (t : ℂ) (h1 : |t.re| ≤ C) (h2 : c ≤ |t.im|) :
    1 / t.im ^ 2 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hb : c ^ 2 ≤ t.im ^ 2 := by
    nlinarith [sq_abs t.im, mul_nonneg (sub_nonneg.2 h2) (add_nonneg (abs_nonneg t.im) hc.le)]
  have ha : t.re ^ 2 ≤ C ^ 2 := by
    nlinarith [sq_abs t.re, mul_nonneg (sub_nonneg.2 h1) (by linarith [abs_nonneg t.re] : 0 ≤ C + |t.re|)]
  have hbpos : 0 < t.im ^ 2 := lt_of_lt_of_le hc2 hb
  have e1 : 1 ≤ (1 + C ^ 2) * (1 + t.re ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  have e2 : 1 / t.im ^ 2 ≤ (1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹ := by
    have h3 : 1 ≤ t.im ^ 2 / c ^ 2 := by
      rw [le_div_iff₀ hc2]
      linarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ hbpos (by positivity), add_mul, one_mul, one_div, inv_mul_eq_div]
    linarith
  calc 1 / t.im ^ 2 = 1 * (1 / t.im ^ 2) := (one_mul _).symm
    _ ≤ ((1 + C ^ 2) * (1 + t.re ^ 2)⁻¹) * ((1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by ring

theorem integ_G : ∫⁻ t : ℂ, ENNReal.ofReal ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) < ⊤ := by
  have h1 : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
  have h2 : Integrable (fun p : ℝ × ℝ => (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹) :=
    h1.mul_prod h1
  have h3 : Integrable (fun t : ℂ => (1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) :=
    (Complex.volume_preserving_equiv_real_prod.integrable_comp h2.aestronglyMeasurable).2 h2
  exact h3.lintegral_lt_top

private theorem volume_eq_lintegral_inv_im_sq_comap (s : Set {z : ℂ // z.im ≠ 0}) (hs : MeasurableSet s) :
    (volume : Measure P) (show Set P from s) = ∫⁻ z in s, ENNReal.ofReal (1 / z.1.im ^ 2)
      ∂(Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume) :=
  withDensity_apply _ hs

private theorem lintegral_comap_im_ne_zero_le_lintegral (f : ℂ → ℝ≥0∞) :
    ∫⁻ z : {z : ℂ // z.im ≠ 0}, f z.1 ∂(Measure.comap Subtype.val volume) ≤ ∫⁻ t, f t := by
  have hs : MeasurableSet {z : ℂ | z.im ≠ 0} :=
    (isOpen_ne_fun Complex.continuous_im continuous_const).measurableSet
  calc ∫⁻ z : {z : ℂ // z.im ≠ 0}, f z.1 ∂(Measure.comap Subtype.val volume)
      = ∫⁻ t in {z : ℂ | z.im ≠ 0}, f t := lintegral_subtype_comap hs f
    _ ≤ ∫⁻ t, f t := setLIntegral_le_lintegral _ _

private theorem lintegral_mul_inv_one_add_sq_lt_top (K : ℝ) (hK : 0 ≤ K) :
    ∫⁻ t : ℂ, ENNReal.ofReal (K * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹)) < ⊤ := by
  simp_rw [ENNReal.ofReal_mul hK]
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top integ_G

private theorem lintegral_B1_inv_im_sq_le_lintegral (C c : ℝ) (hc : 0 < c) :
    ∫⁻ z in B1 C c, ENNReal.ofReal (1 / z.1.im ^ 2) ∂(Measure.comap Subtype.val volume) ≤
      ∫⁻ z : {z : ℂ // z.im ≠ 0}, ENNReal.ofReal ((1 + C ^ 2) * (1 + 1 / c ^ 2) *
          ((1 + z.1.re ^ 2)⁻¹ * (1 + z.1.im ^ 2)⁻¹)) ∂(Measure.comap Subtype.val volume) := by
  refine le_trans (setLIntegral_mono' (measurableSet_cusp_region C c) fun z hz => ?_) (setLIntegral_le_lintegral _ _)
  exact ENNReal.ofReal_le_ofReal (pt_bound C c hc z.1 hz.1 hz.2)

theorem volume_cusp_region_lt_top (C c : ℝ) (hc : 0 < c) : (volume : Measure P) (show Set P from B1 C c) < ⊤ := by
  have hK0 : 0 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) := by positivity
  rw [volume_eq_lintegral_inv_im_sq_comap _ (measurableSet_cusp_region C c)]
  exact lt_of_le_of_lt ((lintegral_B1_inv_im_sq_le_lintegral C c hc).trans (lintegral_comap_im_ne_zero_le_lintegral
    (fun t : ℂ => ENNReal.ofReal ((1 + C ^ 2) * (1 + 1 / c ^ 2) *
      ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹))))) (lintegral_mul_inv_one_add_sq_lt_top _ hK0)

end UpperTheory.Esk.CuspRegionVolume

open UpperTheory.Esk.CuspRegionVolume in
theorem UpperTheory.Esk.cusp_region_volume_finite_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.C2 → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.E3 := by
  intro hB1a _ hC2 hE0a hE0d
  intro F I Gf _ _ _ D hD b hb
  obtain ⟨hcnt, hsf, -, hPY, -, -, -, -⟩ := hE0a F I Gf D hD
  obtain ⟨-, hsm, -, -, -, -, -, -, -, hsurj, -⟩ := hE0d F I Gf D hD
  haveI : Countable (PG F) := hcnt
  haveI : SigmaFinite (volume : Measure D.Xs) := hsf
  haveI : SigmaFinite (volume : Measure P) := hB1a.1
  haveI : Countable D.Om := hD.cO
  obtain ⟨c₀, hc₀, hmink⟩ := hD.mink
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  have h01 : (![0, 1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1
  let T : Set D.Om := (fun x : Gf => (show D.Om from ((x : Gf) : Gf ⧸ D.H))) '' (S : Set Gf)
  let U : Set D.Xs := Set.univ.pi fun _ : I => (show Set P from B1 C c)
  have hT : T.Finite := S.finite_toSet.image _
  have hU : MeasurableSet U := MeasurableSet.univ_pi fun _ => measurableSet_cusp_region C c
  have hS : MeasurableSet (T ×ˢ U) := (MeasurableSet.of_discrete).prod hU
  have hcover : ∀ y : D.Y, ∃ g : PG F, g • y ∈ T ×ˢ U := by
    intro y
    obtain ⟨s, hs0, hs⟩ := hmink y.2 (D.rep y.1)
    obtain ⟨γ, hγ⟩ := hsurj s hs0
    set y' : D.Y := (γ : PG F) • y with hy'
    have h1 : c₀ ≤ D.Ht ![0, 1] y'.2 (D.rep y'.1) := by
      change c₀ ≤ D.HtY ![0, 1] ((γ : PG F) • y)
      rw [hsm ![0, 1] h01 γ y, hγ]
      exact hs
    obtain ⟨bb, -, ⟨x', hx'S, h, hhH, hjx⟩, hSg⟩ := hnorm y'.2 (D.rep y'.1) h1
    refine ⟨(bb : PG F) * (γ : PG F), ?_⟩
    rw [mul_smul, ← hy']
    refine ⟨?_, ?_⟩
    · have hy1 : ((D.rep y'.1 : Gf) : Gf ⧸ D.H) = y'.1 := Quotient.out_eq _
      have hm := D.mk_smulO bb (D.rep y'.1)
      rw [hy1] at hm
      refine ⟨x', hx'S, ?_⟩
      show (show D.Om from ((x' : Gf) : Gf ⧸ D.H)) = (bb : PG F) • y'.1
      rw [hm, hjx]
      refine (QuotientGroup.eq.2 ?_).symm
      rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_mem hhH
    · show (bb : PG F) • y'.2 ∈ U
      rw [D.mk_smulX]
      intro v _
      exact ⟨(hSg v).1, (hSg v).2.1⟩
  have hfin : D.μY (T ×ˢ U) < ⊤ := by
    unfold Dat.μY
    rw [Measure.prod_prod]
    refine ENNReal.mul_lt_top (Measure.count_apply_lt_top.2 hT) ?_
    change (Measure.pi fun _ : I => (volume : Measure P)) (Set.univ.pi fun _ : I => (show Set P from B1 C c)) < ⊤
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top fun _ _ => volume_cusp_region_lt_top C c hc
  exact lt_of_le_of_lt ((hC2 (PG F) D.Y).2 D.μY hPY b hb _ hS hcover) hfin
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelTraceBoundProof
section
open scoped ENNReal NNReal

open UpperTheory.Esk in
theorem UpperTheory.Esk.kernel_trace_bound_proof : UpperTheory.Esk.E0d → UpperTheory.Esk.E1 → UpperTheory.Esk.F5 := by
  intro _ hE1 F I Gf ι _ _ _ _ D k a hH
  obtain ⟨C, hC⟩ := hE1 F I Gf ι D k a hH 1 one_pos
  refine ⟨C, fun T hT y => ⟨fun hy γ s hs _ => hy s hs, fun hy => ?_⟩⟩
  simp only [Dat.abelian₂, Set.mem_ofPred_eq, not_forall, not_le] at hy
  obtain ⟨s, hs, hsT⟩ := hy
  calc ∑' γ : PG F, ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ
      ≤ ∑' γ, {γ : PG F | ¬ Fix s γ}.indicator (fun γ => ‖D.kk k a γ y‖ₑ) γ := by
        refine ENNReal.tsum_le_tsum fun γ => ?_
        by_cases hγ : y ∈ D.LamF T γ
        · have hnf : γ ∈ {γ : PG F | ¬ Fix s γ} := fun hf => absurd (hγ s hs hf) (not_le.2 hsT)
          rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hnf]
        · rw [Set.indicator_of_notMem hγ]; simp
    _ = ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ := (tsum_subtype _ _).symm
    _ ≤ C := hC y s hs (le_of_lt (hT.trans hsT))
end

