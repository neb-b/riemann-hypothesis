module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.Development

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.PositiveDefiniteSecond
section
noncomputable section

namespace PI.DefPosDefWork

open Matrix ComplexOrder

theorem re_nonneg_of_rat {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (z : ℂ) (hz : z.im ≠ 0)
    (h : ∀ α β : Fin k → ℚ, 0 ≤ (star (fun i => (α i : ℂ) + (β i : ℂ) * z) ⬝ᵥ
      (M *ᵥ (fun i => (α i : ℂ) + (β i : ℂ) * z))).re)
    (v : Fin k → ℂ) : 0 ≤ (star v ⬝ᵥ (M *ᵥ v)).re := by
  have hQc : Continuous fun w : Fin k → ℂ => (star w ⬝ᵥ (M *ᵥ w)).re := by
    show Continuous fun w : Fin k → ℂ => (∑ i, star (w i) * ∑ j, M i j * w j).re
    exact Complex.continuous_re.comp (continuous_finsetSum _ fun i _ =>
      (continuous_star.comp (continuous_apply i)).mul
        (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)))
  let ψ : (Fin k → ℝ) × (Fin k → ℝ) → (Fin k → ℂ) := fun p i => (p.1 i : ℂ) + (p.2 i : ℂ) * z
  have hψ : Continuous ψ := by fun_prop
  let d : (Fin k → ℚ) × (Fin k → ℚ) → (Fin k → ℝ) × (Fin k → ℝ) :=
    Prod.map (fun α i => (α i : ℝ)) (fun β i => (β i : ℝ))
  have hd : DenseRange d :=
    (DenseRange.piMap fun _ => Rat.denseRange_cast).prodMap (DenseRange.piMap fun _ => Rat.denseRange_cast)
  have key : ∀ p : (Fin k → ℝ) × (Fin k → ℝ), 0 ≤ (star (ψ p) ⬝ᵥ (M *ᵥ ψ p)).re := fun p =>
    hd.induction_on p (isClosed_le continuous_const (hQc.comp hψ)) (fun q => by simpa [ψ, d] using h q.1 q.2)
  let p : (Fin k → ℝ) × (Fin k → ℝ) := (fun i => (v i).re - (v i).im / z.im * z.re, fun i => (v i).im / z.im)
  have hp : ψ p = v := by
    funext i
    apply Complex.ext <;> simp [ψ, p] <;> (try field_simp) <;> (try ring)
  have h1 := key p
  rwa [hp] at h1

theorem re_quad {k : ℕ} (N : Matrix (Fin k) (Fin k) ℂ) (hN : ∀ i j, (N i j).im = 0) (a b : Fin k → ℝ) :
    (star (fun i => (a i : ℂ) + (b i : ℂ) * Complex.I) ⬝ᵥ (N *ᵥ (fun i => (a i : ℂ) + (b i : ℂ) * Complex.I))).re
      = (star (fun i => (a i : ℂ)) ⬝ᵥ (N *ᵥ (fun i => (a i : ℂ)))).re
        + (star (fun i => (b i : ℂ)) ⬝ᵥ (N *ᵥ (fun i => (b i : ℂ)))).re := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im, hN]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem posDef_of_points {E : Type} [Field E] (φ : E →+* ℂ) {k : ℕ} (N : Matrix (Fin k) (Fin k) ℂ)
    (hN : N.IsHermitian) (hu : IsUnit N) (hNr : (∀ t : E, (φ t).im = 0) → ∀ i j, (N i j).im = 0)
    (hpt : ∀ x : Fin k → E, 0 ≤ (star (fun i => φ (x i)) ⬝ᵥ (N *ᵥ (fun i => φ (x i)))).re) : N.PosDef := by
  haveI : CharZero E := RingHom.charZero φ
  have hPSD : ∀ v : Fin k → ℂ, 0 ≤ (star v ⬝ᵥ (N *ᵥ v)).re := by
    by_cases hreal : ∀ t : E, (φ t).im = 0
    · have hNr' := hNr hreal
      have hQc : Continuous fun a : Fin k → ℝ =>
          (star (fun i => (a i : ℂ)) ⬝ᵥ (N *ᵥ fun i => (a i : ℂ))).re := by
        show Continuous fun a : Fin k → ℝ => (∑ i, star ((a i : ℂ)) * ∑ j, N i j * (a j : ℂ)).re
        exact Complex.continuous_re.comp (continuous_finsetSum _ fun i _ =>
          (continuous_star.comp (Complex.continuous_ofReal.comp (continuous_apply i))).mul
            (continuous_finsetSum _ fun j _ =>
              continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j))))
      have hd : DenseRange (fun α : Fin k → ℚ => fun i => (α i : ℝ)) :=
        DenseRange.piMap fun _ => Rat.denseRange_cast
      have hreal' : ∀ a : Fin k → ℝ, 0 ≤ (star (fun i => (a i : ℂ)) ⬝ᵥ (N *ᵥ fun i => (a i : ℂ))).re :=
        fun a => hd.induction_on a (isClosed_le continuous_const hQc) (fun α => by
          have h1 := hpt (fun i => (α i : E))
          simpa [map_ratCast] using h1)
      intro v
      have e := re_quad N hNr' (fun i => (v i).re) (fun i => (v i).im)
      have hv : (fun i => ((v i).re : ℂ) + ((v i).im : ℂ) * Complex.I) = v :=
        funext fun i => Complex.re_add_im (v i)
      rw [hv] at e
      rw [e]
      exact add_nonneg (hreal' _) (hreal' _)
    · push_neg at hreal
      obtain ⟨t, ht⟩ := hreal
      refine re_nonneg_of_rat N (φ t) ht (fun α β => ?_)
      have h1 := hpt (fun i => (α i : E) + (β i : E) * t)
      simpa [map_add (f := _), map_mul, map_ratCast] using h1
  have hpsd : N.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hN, fun v => ?_⟩
    rw [Complex.nonneg_iff]
    exact ⟨hPSD v, (hN.im_star_dotProduct_mulVec_self v).symm⟩
  exact hpsd.posDef_iff_isUnit.2 hu

theorem positive_definite_second : Step2 := by
  intro F E _ _ _ _ _ hF σ k J _ hH hD h1 φ
  obtain ⟨r, hr⟩ := hF (φ.comp (algebraMap F E))
  have hr' : ∀ a, φ (algebraMap F E a) = (r a : ℂ) := fun a => hr a
  have hJ : ∀ i j, σ (J j i) = J i j := fun i j => congrFun (congrFun hH i) j
  have hst : ∀ y, star (φ y) = φ (σ y) := fun y => (h1 φ y).symm
  have hMh : (J.map φ).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, hst, hJ]
  have hQ : ∀ x : Fin k → E, star (fun i => φ (x i)) ⬝ᵥ (J.map φ *ᵥ (fun i => φ (x i)))
      = φ (hform (σ : E →+* E) J x x) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, mulVec, hform, Pi.star_apply, hst, Matrix.map_apply, map_sum, map_mul,
      Finset.mul_sum, mul_assoc]
    rfl
  have hdet : J.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hJv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr h0
    have h0' : hform (σ : E →+* E) J v v = 0 := by
      have e : hform (σ : E →+* E) J v v = ∑ i, (σ : E →+* E) (v i) * (J *ᵥ v) i := by
        simp only [hform, mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rw [e, hJv]
      simp
    rcases hD r with h | h
    · obtain ⟨a, ha, ha'⟩ := h v hv
      rw [h0'] at ha
      have ha0 : a = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).mp ha
      rw [ha0, map_zero] at ha'
      exact lt_irrefl _ ha'
    · obtain ⟨a, ha, ha'⟩ := h v hv
      rw [h0'] at ha
      have ha0 : a = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).mp ha
      rw [ha0, map_zero] at ha'
      exact lt_irrefl _ ha'
  have hMu : IsUnit (J.map φ) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).mpr hdet
  have hMr : (∀ t : E, (φ t).im = 0) → ∀ i j, ((J.map φ) i j).im = 0 := fun ht i j => ht (J i j)
  have hQ0 : ∀ x : Fin k → E, x = 0 → hform (σ : E →+* E) J x x = 0 := by
    intro x hx
    subst hx
    simp [hform]
  rcases hD r with h | h
  · left
    refine posDef_of_points φ _ hMh hMu hMr fun x => ?_
    rw [hQ]
    by_cases hx : x = 0
    · rw [hQ0 x hx]
      simp
    · obtain ⟨a, ha, ha'⟩ := h x hx
      rw [← ha, hr']
      simpa using ha'.le
  · right
    refine posDef_of_points φ _ hMh.neg hMu.neg (fun ht i j => by simpa using hMr ht i j) fun x => ?_
    rw [Matrix.neg_mulVec, dotProduct_neg, hQ]
    by_cases hx : x = 0
    · rw [hQ0 x hx]
      simp
    · obtain ⟨a, ha, ha'⟩ := h x hx
      rw [← ha, hr']
      simp
      linarith

end PI.DefPosDefWork
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.SplittingOfExtension
section
noncomputable section

namespace PI.DefPosDefWork

open Matrix ComplexOrder

theorem conj_of_pos (w z : ℂ)
    (h : ∀ q : ℚ, z + (q : ℂ) ≠ 0 → ∃ c : ℝ, 0 < c ∧ (w + (q : ℂ)) * (z + (q : ℂ)) = (c : ℂ)) :
    w = (starRingEnd ℂ) z := by
  have key : ∀ q : ℚ, z + (q : ℂ) ≠ 0 →
      (w.re + q) * z.im + w.im * (z.re + q) = 0 ∧ 0 < (w.re + q) * (z.re + q) - w.im * z.im := by
    intro q hq
    obtain ⟨c, hc, he⟩ := h q hq
    have him := congrArg Complex.im he
    have hre := congrArg Complex.re he
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ratCast_re, Complex.ratCast_im, add_zero] at him hre
    constructor
    · linear_combination him
    · have hc' : (w.re + q) * (z.re + q) - w.im * z.im = c := by linear_combination hre
      rw [hc']
      exact hc
  rw [Complex.ext_iff, Complex.conj_re, Complex.conj_im]
  by_cases hd : z.im = 0
  · have hne : ∀ q : ℚ, z.re + q ≠ 0 → z + (q : ℂ) ≠ 0 := fun q hq h0 =>
      hq (by simpa using congrArg Complex.re h0)
    obtain ⟨q0, hq0⟩ : ∃ q : ℚ, z.re + q ≠ 0 := by
      by_cases h0 : z.re = 0
      · exact ⟨1, by rw [h0]; norm_num⟩
      · exact ⟨0, by simpa using h0⟩
    have k := key q0 (hne q0 hq0)
    have e4 : w.im * (z.re + q0) = 0 := by linear_combination k.1 - (w.re + (q0 : ℝ)) * hd
    have him : w.im = 0 := (mul_eq_zero.mp e4).resolve_right hq0
    have ere : w.re = z.re := by
      by_contra hne'
      rcases lt_or_gt_of_ne hne' with hlt | hlt
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (neg_lt_neg hlt)
        have hA : w.re + q < 0 := by linarith
        have hB : 0 < z.re + q := by linarith
        have k2 := (key q (hne q hB.ne')).2
        rw [him, zero_mul, sub_zero] at k2
        linarith [mul_neg_of_neg_of_pos hA hB]
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (neg_lt_neg hlt)
        have hA : 0 < w.re + q := by linarith
        have hB : z.re + q < 0 := by linarith
        have k2 := (key q (hne q hB.ne)).2
        rw [him, zero_mul, sub_zero] at k2
        linarith [mul_neg_of_pos_of_neg hA hB]
    exact ⟨ere, by rw [him, hd, neg_zero]⟩
  · have hne : ∀ q : ℚ, z + (q : ℂ) ≠ 0 := fun q h0 => hd (by simpa using congrArg Complex.im h0)
    have k0 := key 0 (hne 0)
    have k1 := key 1 (hne 1)
    push_cast at k0 k1
    have e1 : w.im = -z.im := by linear_combination k1.1 - k0.1
    have e2 : z.im * (w.re - z.re) = 0 := by linear_combination k0.1 - z.re * e1
    have e3 : w.re = z.re := by
      rcases mul_eq_zero.mp e2 with h0 | h0
      · exact absurd h0 hd
      · linarith
    exact ⟨e3, e1⟩

theorem hform_single {E : Type} [CommRing E] (σ : E →+* E) {k : ℕ} (J : Matrix (Fin k) (Fin k) E)
    (i0 : Fin k) (s : E) :
    hform σ J (Pi.single i0 s) (Pi.single i0 s) = σ s * J i0 i0 * s := by
  unfold PI.hform
  simp [Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_eq_single i0]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i0) h

theorem pos_pair {F E : Type} [Field F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (hk : 0 < k) (hD : IsDef σ J)
    (φ : E →+* ℂ) (r : F →+* ℝ) (hr : ∀ a, φ (algebraMap F E a) = (r a : ℂ))
    (s : E) (hs : s ≠ 0) : ∃ c : ℝ, 0 < c ∧ φ (σ s) * φ s = (c : ℂ) := by
  obtain ⟨i0⟩ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hx1 : (Pi.single i0 s : Fin k → E) ≠ 0 := fun h0 => hs (by simpa using congrFun h0 i0)
  have hx2 : (Pi.single i0 (1 : E) : Fin k → E) ≠ 0 := fun h0 => by
    simpa using congrFun h0 i0
  have hv1 : hform (σ : E →+* E) J (Pi.single i0 s) (Pi.single i0 s) = σ s * J i0 i0 * s :=
    hform_single (σ : E →+* E) J i0 s
  have hv2 : hform (σ : E →+* E) J (Pi.single i0 1) (Pi.single i0 1) = J i0 i0 := by
    rw [hform_single]
    simp
  have key : ∀ a b : F, algebraMap F E a = σ s * J i0 i0 * s → algebraMap F E b = J i0 i0 →
      0 < r a * r b → ∃ c : ℝ, 0 < c ∧ φ (σ s) * φ s = c := by
    intro a b ha hb hab
    have hb0 : r b ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hab
      exact lt_irrefl _ hab
    refine ⟨r a / r b, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hb0 with h | h
      · exact div_pos_of_neg_of_neg (by nlinarith) h
      · exact div_pos (by nlinarith) h
    · have e1 : (r a : ℂ) = φ (σ s) * (r b : ℂ) * φ s := by
        rw [← hr a, ← hr b, ha, hb, map_mul, map_mul]
      have hb0' : (r b : ℂ) ≠ 0 := by exact_mod_cast hb0
      rw [Complex.ofReal_div, e1, eq_div_iff hb0']
      ring
  rcases hD r with hpos | hneg
  · obtain ⟨a, ha, ha0⟩ := hpos _ hx1
    obtain ⟨b, hb, hb0⟩ := hpos _ hx2
    exact key a b (ha.trans hv1) (hb.trans hv2) (mul_pos ha0 hb0)
  · obtain ⟨a, ha, ha0⟩ := hneg _ hx1
    obtain ⟨b, hb, hb0⟩ := hneg _ hx2
    exact key a b (ha.trans hv1) (hb.trans hv2) (mul_pos_of_neg_of_neg ha0 hb0)

theorem splitting_of_extension : Step1 := by
  intro F E _ _ _ _ _ hreal σ k J hk _ hD φ x
  obtain ⟨r, hr⟩ := hreal (φ.comp (algebraMap F E))
  apply conj_of_pos
  intro q hq
  have hs : x + (q : E) ≠ 0 := by
    intro h0
    apply hq
    rw [← map_ratCast φ q, ← map_add (f := _), h0, map_zero]
  obtain ⟨c, hc, he⟩ := pos_pair σ J hk hD φ r (fun a => hr a) (x + q) hs
  refine ⟨c, hc, ?_⟩
  rw [← he]
  simp only [map_add (f := _), map_ratCast]

end PI.DefPosDefWork
end
end

