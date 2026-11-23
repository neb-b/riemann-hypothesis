module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentOnHyperbolicComplement

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticOffDiagonalBounds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace QuadraticOffDiagonalBounds

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem quad_nonneg {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef) (v : Fin 2 → ℂ) :
    0 ≤ (∑ i, ∑ k, M i k * v i * conj (v k)).re := by
  have h := hM.dotProduct_mulVec_nonneg (star v)
  have e : dotProduct (star (star v)) ((Matrix.of M).mulVec (star v)) = ∑ i, ∑ k, M i k * v i * conj (v k) := by
    simp only [star_star, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.star_apply, ← starRingEnd_apply]
    ring
  rw [e] at h
  simpa using (Complex.le_def.mp h).1

theorem quad_comb {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef) (α β : ℂ)
    (v w : Fin 2 → ℂ) :
    (∑ i, ∑ k, M i k * (α • v + β • w) i * conj ((α • v + β • w) k)).re ≤
      (‖α‖ ^ 2 + ‖β‖ ^ 2) * ((∑ i, ∑ k, M i k * v i * conj (v k)).re +
        (∑ i, ∑ k, M i k * w i * conj (w k)).re) := by
  have hid : (∑ i, ∑ k, M i k * (α • v + β • w) i * conj ((α • v + β • w) k)) +
      (∑ i, ∑ k, M i k * (conj β • v - conj α • w) i * conj ((conj β • v - conj α • w) k)) =
      (α * conj α + β * conj β) * ((∑ i, ∑ k, M i k * v i * conj (v k)) +
        (∑ i, ∑ k, M i k * w i * conj (w k))) := by
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _),
      map_sub, map_mul, Complex.conj_conj]
    ring
  have h0 := quad_nonneg hM (conj β • v - conj α • w)
  have hαβ : α * conj α + β * conj β = ((‖α‖ ^ 2 + ‖β‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hre := congrArg Complex.re hid
  rw [Complex.add_re, hαβ, Complex.re_ofReal_mul, Complex.add_re] at hre
  linarith

theorem offdiag_le {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef)
    (h10 : M 1 0 = conj (M 0 1)) : 2 * ‖M 0 1‖ ≤ (M 0 0).re + (M 1 1).re := by
  have d0 := quad_nonneg hM ![1, 0]
  have d1 := quad_nonneg hM ![0, 1]
  simp [Fin.sum_univ_two] at d0 d1
  rcases eq_or_ne (M 0 1) 0 with h0 | h0
  · rw [h0, norm_zero, mul_zero]
    linarith
  · have hn : 0 < ‖M 0 1‖ := norm_pos_iff.mpr h0
    have hs : M 0 1 * conj (M 0 1) = ((‖M 0 1‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    have h := quad_nonneg hM ![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)]
    have e : (∑ i, ∑ k, M i k * ![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)] i *
        conj (![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)] k)) =
        ((‖M 0 1‖ ^ 2 : ℝ) : ℂ) * (M 0 0 + M 1 1) - ((2 * ‖M 0 1‖ ^ 3 : ℝ) : ℂ) := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        map_neg, Complex.conj_conj, Complex.conj_ofReal, h10]
      push_cast
      linear_combination (M 0 0 - 2 * ((‖M 0 1‖ : ℝ) : ℂ)) * hs
    rw [e] at h
    have h' := h
    simp only [Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.add_re,
      Complex.ofReal_re] at h'
    by_contra hlt
    push_neg at hlt
    have hm := mul_lt_mul_of_pos_left hlt (pow_pos hn 2)
    nlinarith

variable {r : ℕ} {X : Data E r}

private theorem Hf_smul_add_smul_right (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) (a b : ℂ) :
    X.Hf z τ u (a • v + b • w) = conj a * X.Hf z τ u v + conj b * X.Hf z τ u w := by
  simp only [Data.Hf, hermC, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
  ring

theorem coord {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (f1 f2 e : Fin r → ℂ) (a0 a1 : ℂ)
    (c : ℝ) (he : e = a0 • f1 + a1 • f2) (h1 : c * (X.Hf z τ f1 f1).re = 1)
    (h2 : X.Hf z τ e f1 = 0) (h3 : c * (X.Hf z τ e e).re = 1) :
    ∃ p q : ℂ, q * a0 + p = 0 ∧ q * a1 = 1 ∧ ‖p‖ ^ 2 + ‖q‖ ^ 2 = c * (X.Hf z τ f2 f2).re := by
  have hc : ∀ u w, conj (X.Hf z τ u w) = X.Hf z τ w u := fun u w => UnipotentCoefficientShift.Hf_conj hz τ u w
  have hL : ∀ w, X.Hf z τ e w = a0 * X.Hf z τ f1 w + a1 * X.Hf z τ f2 w := by
    intro w
    rw [← hc w e, he, Hf_smul_add_smul_right, map_add (f := _), map_mul, map_mul, Complex.conj_conj, Complex.conj_conj,
      hc, hc]
  have h2' : a0 * X.Hf z τ f1 f1 + a1 * X.Hf z τ f2 f1 = 0 := by rw [← hL, h2]
  have hee : X.Hf z τ e e = conj a0 * X.Hf z τ e f1 + conj a1 * X.Hf z τ e f2 := by
    have := Hf_smul_add_smul_right z τ e f1 f2 a0 a1
    rwa [← he] at this
  rw [h2, mul_zero, zero_add, hL f2, ← hc f2 f1] at hee
  have hA : conj (X.Hf z τ f1 f1) = X.Hf z τ f1 f1 := hc f1 f1
  have hD : conj (X.Hf z τ f2 f2) = X.Hf z τ f2 f2 := hc f2 f2
  have hB : conj a1 * conj (X.Hf z τ f2 f1) = -(conj a0 * X.Hf z τ f1 f1) := by
    rw [← map_mul, show a1 * X.Hf z τ f2 f1 = -(a0 * X.Hf z τ f1 f1) by linear_combination h2',
      map_neg, map_mul, hA]
  have hee2 : X.Hf z τ e e = -(a0 * conj a0) * X.Hf z τ f1 f1 + (a1 * conj a1) * X.Hf z τ f2 f2 := by
    rw [hee]
    linear_combination a0 * hB
  have hAr : ((X.Hf z τ f1 f1).re : ℂ) = X.Hf z τ f1 f1 := Complex.conj_eq_iff_re.mp hA
  have hDr : ((X.Hf z τ f2 f2).re : ℂ) = X.Hf z τ f2 f2 := Complex.conj_eq_iff_re.mp hD
  have hre : (X.Hf z τ e e).re =
      -(‖a0‖ ^ 2) * (X.Hf z τ f1 f1).re + ‖a1‖ ^ 2 * (X.Hf z τ f2 f2).re := by
    rw [hee2, ← hAr, ← hDr, Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [hre] at h3
  have key : ‖a1‖ ^ 2 * (c * (X.Hf z τ f2 f2).re) = 1 + ‖a0‖ ^ 2 := by
    linear_combination h3 + ‖a0‖ ^ 2 * h1
  have ha1 : a1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at key
    nlinarith [sq_nonneg ‖a0‖]
  have hn : 0 < ‖a1‖ := norm_pos_iff.mpr ha1
  have hcd : c * (X.Hf z τ f2 f2).re = (1 + ‖a0‖ ^ 2) / ‖a1‖ ^ 2 := by
    rw [eq_div_iff (by positivity)]
    linear_combination key
  refine ⟨-a0 * a1⁻¹, a1⁻¹, by ring, inv_mul_cancel₀ ha1, ?_⟩
  rw [hcd, norm_mul, norm_neg, norm_inv]
  field_simp
  ring

end QuadraticOffDiagonalBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentSubOneMajorantBound
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma normSq_sub_le_two (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]

namespace Data

variable {r : ℕ} (X : Data E r)

lemma Jp_sub (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Jp x τ (u - v) = X.Jp x τ u - X.Jp x τ v := by
  unfold Jp
  rw [X.ppos_sub, smul_sub]
  abel

section perTau

variable {x : Frame X.Ψ r} {τ : X.Ψ}

lemma maj_smul (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ)) (c : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (c • v) = Complex.normSq c * X.maj x τ v := by
  have hJ : X.Jp x τ (c • v) = c • X.Jp x τ v := by
    unfold Jp; rw [X.ppos_smul, smul_comm (2 : ℂ) c, ← smul_sub]
  have hH : ∀ u w, hermC τ.1 X.Gm (c • u) (c • w) = (Complex.normSq c : ℂ) * hermC τ.1 X.Gm u w := by
    intro u w
    unfold hermC
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have h1 := hself (c • v)
  rw [show X.Hf x τ (c • v) (c • v) = hermC τ.1 X.Gm (X.Jp x τ (c • v)) (c • v) from rfl, hJ, hH,
    show hermC τ.1 X.Gm (X.Jp x τ v) v = X.Hf x τ v v from rfl, hself v] at h1
  exact_mod_cast h1.symm

lemma maj_zero' (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ)) : X.maj x τ 0 = 0 := by
  have h1 := X.maj_smul hself (0 : ℂ) 0
  simpa using h1

lemma maj_nonneg' (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
    (hpos : ∀ v, v ≠ 0 → 0 < X.maj x τ v) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, X.maj_zero' hself]
  · exact (hpos v hv).le

variable {e : Fin r → ℂ} (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ) (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0)
  (hq : X.d2q x τ e ≠ 0) (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
include hx he hq hself

lemma maj_Ce_bz (C b : ℂ) :
    X.maj x τ (C • e - b • X.d2z x τ e δ) =
      Complex.normSq C * X.maj x τ e + Complex.normSq b * X.maj x τ (X.d2z x τ e δ) := by
  have hfz : hermC τ.1 X.Gm (X.Jp x τ e) (X.d2z x τ e δ) = 0 := by
    rw [hsym, unipotent_shift_orthogonal_Je X δ hx he hq, map_zero]
  have hze : hermC τ.1 X.Gm (X.Jp x τ (X.d2z x τ e δ)) e = 0 := by
    rw [Jp_adj X hx, unipotent_shift_orthogonal_Je X δ hx he hq]
  have h3 : X.Hf x τ (C • e - b • X.d2z x τ e δ) (C • e - b • X.d2z x τ e δ) =
      C * conj C * X.Hf x τ e e + b * conj b * X.Hf x τ (X.d2z x τ e δ) (X.d2z x τ e δ) := by
    show hermC τ.1 X.Gm (X.Jp x τ (C • e - b • X.d2z x τ e δ)) (C • e - b • X.d2z x τ e δ) =
      C * conj C * hermC τ.1 X.Gm (X.Jp x τ e) e +
        b * conj b * hermC τ.1 X.Gm (X.Jp x τ (X.d2z x τ e δ)) (X.d2z x τ e δ)
    rw [Jp_sub, Jp_smul, Jp_smul]
    simp only [hC_sub_left, hC_smul_left, hC_sub_right, hC_smul_right, hfz, hze]
    ring
  rw [hself, hself, hself, Complex.mul_conj, Complex.mul_conj] at h3
  exact_mod_cast h3

lemma maj_decomp (w : Fin r → ℂ) (hw1 : hermC τ.1 X.Gm w e = 0)
    (hw2 : hermC τ.1 X.Gm w (X.Jp x τ e) = 0) (a b : ℂ) :
    X.maj x τ (w + a • e + b • X.Jp x τ e) =
      Complex.normSq a * X.maj x τ e + Complex.normSq b * X.maj x τ e + X.maj x τ w := by
  have k1 : hermC τ.1 X.Gm (X.Jp x τ w) e = 0 := by rw [Jp_adj X hx, hw2]
  have k2 : hermC τ.1 X.Gm (X.Jp x τ w) (X.Jp x τ e) = 0 := by
    rw [Jp_adj X hx, Jp_Jp X hx, hw1]
  have k3 : hermC τ.1 X.Gm (X.Jp x τ e) w = 0 := by rw [hsym, hw2, map_zero]
  have k4 : hermC τ.1 X.Gm e w = 0 := by rw [hsym, hw1, map_zero]
  have k5 := hermitian_pairing_Je_Je_zero X hx he
  have k6 : hermC τ.1 X.Gm (X.Jp x τ e) e = X.Hf x τ e e := rfl
  have k7 : hermC τ.1 X.Gm e (X.Jp x τ e) = X.Hf x τ e e := hermitian_pairing_e_Je X hx
  have h3 : X.Hf x τ (w + a • e + b • X.Jp x τ e) (w + a • e + b • X.Jp x τ e) =
      a * conj a * X.Hf x τ e e + b * conj b * X.Hf x τ e e + X.Hf x τ w w := by
    show hermC τ.1 X.Gm (X.Jp x τ (w + a • e + b • X.Jp x τ e)) (w + a • e + b • X.Jp x τ e) =
      a * conj a * X.Hf x τ e e + b * conj b * X.Hf x τ e e + hermC τ.1 X.Gm (X.Jp x τ w) w
    rw [Jp_add, Jp_add, Jp_smul, Jp_smul, Jp_Jp X hx]
    simp only [hC_add_left, hC_smul_left, hC_add_right, hC_smul_right, k1, k2, k3, k4, k5, k6, k7,
      he]
    ring
  rw [hself, hself, hself, Complex.mul_conj, Complex.mul_conj] at h3
  exact_mod_cast h3

lemma unipotent_sub_one_majorant_bound (hpos : ∀ v, v ≠ 0 → 0 < X.maj x τ v) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hδ : ∀ u, hermC τ.1 X.Gm u e = 0 → hermC τ.1 X.Gm u (X.Jp x τ e) = 0 →
      X.maj x τ (δ u • e) ≤ κ ^ 2 * X.maj x τ u) (v : Fin r → ℂ) :
    X.maj x τ (Matrix.mulVec (X.d2n x τ e δ - 1) v) ≤ (3 * κ) ^ 2 * X.maj x τ v := by
  have hnn := maj_nonneg' X hself hpos
  have hqQ : X.d2q x τ e = (X.maj x τ e : ℂ) := hself e
  have hQ : 0 < X.maj x τ e := by
    rcases (hnn e).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hqQ, ← h]; simp) hq
  set Q := X.maj x τ e with hQdef
  set z := X.d2z x τ e δ with hzdef

  have hA : Matrix.mulVec (X.d2n x τ e δ - 1) v =
      (δ (X.d2pi x τ e v) - δ z / 2 * X.d2b x τ e v) • e - X.d2b x τ e v • z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, unipotent_mulVec_formula]
    abel
  rw [hA, maj_Ce_bz X δ hx he hq hself]

  have hv : v = X.d2pi x τ e v + X.d2a x τ e v • e + X.d2b x τ e v • X.Jp x τ e := by
    rw [hyperbolic_projection_apply]; abel
  have hw1 := hyperbolic_projection_perp_e X hx he hq v
  have hw2 := hyperbolic_projection_perp_Je X hx he hq v
  conv_rhs => rw [hv, maj_decomp X hx he hq hself _ hw1 hw2]

  have hz1 : hermC τ.1 X.Gm (X.Jp x τ z) e = 0 := by rw [Jp_adj X hx, unipotent_shift_orthogonal_Je X δ hx he hq]
  have hz2 : hermC τ.1 X.Gm (X.Jp x τ z) (X.Jp x τ e) = 0 := by
    rw [Jp_adj X hx, Jp_Jp X hx, unipotent_shift_orthogonal_e X δ hx he hq]
  have hmJz : X.maj x τ (X.Jp x τ z) = X.maj x τ z := by
    have h1 := hself (X.Jp x τ z)
    have h2 := hself z
    have h3 : X.Hf x τ (X.Jp x τ z) (X.Jp x τ z) = X.Hf x τ z z := by
      show hermC τ.1 X.Gm (X.Jp x τ (X.Jp x τ z)) (X.Jp x τ z) = X.Hf x τ z z
      rw [Jp_Jp X hx, Hf_eq X x hx]
      rfl
    rw [h1, h2] at h3
    exact_mod_cast h3
  have hZc : (X.maj x τ z : ℂ) = (Q : ℂ) * δ (X.Jp x τ z) := by
    rw [← hself z, ← hqQ]
    show hermC τ.1 X.Gm (X.Jp x τ z) z = _
    rw [unipotent_shift_spec X δ hx he hq, hyperbolic_projection_of_perp X hx he hq hz1 hz2]
  have hdJ : δ (X.Jp x τ z) = ((X.maj x τ z / Q : ℝ) : ℂ) := by
    have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
    push_cast
    rw [hZc]
    field_simp
  have hZ0 := hnn z
  have hZ : X.maj x τ z ≤ κ ^ 2 * Q := by
    have h := hδ _ hz1 hz2
    rw [maj_smul X hself, hdJ, Complex.normSq_ofReal, hmJz] at h

    have h' : X.maj x τ z * X.maj x τ z ≤ κ ^ 2 * Q * X.maj x τ z := by
      have e1 : X.maj x τ z / Q * (X.maj x τ z / Q) * Q = X.maj x τ z * X.maj x τ z / Q := by
        field_simp
      rw [e1, div_le_iff₀ hQ] at h
      nlinarith
    rcases hZ0.lt_or_eq with h0 | h0
    · exact le_of_mul_le_mul_right h' h0
    · rw [← h0]; positivity
  have hDz : Complex.normSq (δ z) ≤ κ ^ 4 := by
    have h := hδ z (unipotent_shift_orthogonal_e X δ hx he hq) (unipotent_shift_orthogonal_Je X δ hx he hq)
    rw [maj_smul X hself] at h
    have h2 : Complex.normSq (δ z) * Q ≤ κ ^ 4 * Q := by nlinarith
    exact le_of_mul_le_mul_right h2 hQ
  have hw := hyperbolic_projection_perp_e X hx he hq v
  have hD := hδ (X.d2pi x τ e v) hw1 hw2
  rw [maj_smul X hself] at hD
  have hC : Complex.normSq (δ (X.d2pi x τ e v) - δ z / 2 * X.d2b x τ e v) ≤
      2 * Complex.normSq (δ (X.d2pi x τ e v)) +
        Complex.normSq (δ z) * Complex.normSq (X.d2b x τ e v) / 2 := by
    have h1 := normSq_sub_le_two (δ (X.d2pi x τ e v)) (δ z / 2 * X.d2b x τ e v)
    have h2 : Complex.normSq (δ z / 2 * X.d2b x τ e v) =
        Complex.normSq (δ z) * Complex.normSq (X.d2b x τ e v) / 4 := by
      rw [Complex.normSq_mul, Complex.normSq_div]
      norm_num
      ring
    linarith
  have hWn := hnn (X.d2pi x τ e v)
  have hAn := Complex.normSq_nonneg (X.d2a x τ e v)
  have hBn := Complex.normSq_nonneg (X.d2b x τ e v)
  have hDn := Complex.normSq_nonneg (δ (X.d2pi x τ e v))
  have hDzn := Complex.normSq_nonneg (δ z)
  have hk4 : κ ^ 4 ≤ κ ^ 2 := pow_le_pow_of_le_one hκ0 hκ1 (by norm_num)
  have t1 := mul_le_mul_of_nonneg_right hC hQ.le
  have t2 := mul_le_mul_of_nonneg_left hZ hBn
  have t3 := mul_le_mul_of_nonneg_right hDz (mul_nonneg hBn hQ.le)
  have t4 := mul_le_mul_of_nonneg_right hk4 (mul_nonneg hBn hQ.le)
  have t5 := mul_nonneg (sq_nonneg κ) (mul_nonneg hAn hQ.le)
  have t6 := mul_nonneg (sq_nonneg κ) hWn
  have t7 := mul_nonneg (sq_nonneg κ) (mul_nonneg hBn hQ.le)
  nlinarith

end perTau

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

