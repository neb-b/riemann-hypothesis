module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCurvatureDualMetricPointwiseBound
section
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.HodgeCurvPoint

variable {g : ℕ}

theorem re_form_map (M : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℂ) :
    (form (M.map ofReal) v v).re = (fun j => (v j).re) ⬝ᵥ M *ᵥ (fun j => (v j).re) +
      (fun j => (v j).im) ⬝ᵥ M *ᵥ (fun j => (v j).im) := by
  simp only [form_eq_sum, dotProduct, mulVec, Finset.mul_sum, re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [Matrix.map_apply, mul_re, mul_im, conj_re, conj_im]; ring

theorem isHermitian_map {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm) :
    (M.map ofReal).IsHermitian := by
  ext i j; simp [conjTranspose_apply, hM.apply]

theorem form_map_self {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm) (v : Fin g → ℂ) :
    form (M.map ofReal) v v = (((fun j => (v j).re) ⬝ᵥ M *ᵥ (fun j => (v j).re) +
      (fun j => (v j).im) ⬝ᵥ M *ᵥ (fun j => (v j).im) : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [re_form_map, ofReal_re]
  · rw [ofReal_im]
    exact Complex.conj_eq_iff_im.mp (conj_form (isHermitian_map hM) v v)

theorem posSemidef_map {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm)
    (h : ∀ x, 0 ≤ x ⬝ᵥ M *ᵥ x) : (M.map ofReal).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_map hM, fun x => ?_⟩
  have e : star x ⬝ᵥ (M.map ofReal) *ᵥ x = form (M.map ofReal) (star x) (star x) := by
    simp [form]
  rw [e, form_map_self hM]
  exact_mod_cast add_nonneg (h _) (h _)

theorem sum_norm_sq (v : Fin g → ℂ) : ∑ j, ‖v j‖ ^ 2 =
    (fun j => (v j).re) ⬝ᵥ (fun j => (v j).re) + (fun j => (v j).im) ⬝ᵥ (fun j => (v j).im) := by
  simp only [dotProduct, ← Finset.sum_add_distrib, Complex.sq_norm, Complex.normSq_apply]

theorem gnorm_map_star (M : Matrix (Fin g) (Fin g) ℝ) (u : Fin g → ℂ) :
    gnorm (M.map ofReal) (star u) = gnorm (M.map ofReal) u := by
  have e1 : (fun j => (star u j).re) = fun j => (u j).re := by ext j; simp
  have e2 : (fun j => (star u j).im) = -fun j => (u j).im := by ext j; simp
  rw [gnorm, gnorm, re_form_map, re_form_map, e1, e2, mulVec_neg, neg_dotProduct, dotProduct_neg,
    neg_neg]

theorem dotProduct_mulVec_eq_form {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsSymm)
    (u v : Fin g → ℂ) : u ⬝ᵥ M *ᵥ v = form M v (star u) := by
  rw [form, star_star, dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]

theorem dotProduct_finsetSum {a : ℕ} (u : Fin g → ℂ) (w : Fin a → Fin g → ℂ) :
    u ⬝ᵥ ∑ i, w i = ∑ i, u ⬝ᵥ w i := by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem dual_bound : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K : ℝ), 0 < c → 0 ≤ K →
    Y.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, (Bs i).PosSemidef) → (∀ i, 0 < t i) →
    (∀ i x, t i * (x ⬝ᵥ Bs i *ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ j k, ‖Dm j k‖ ≤ K) →
    (Y.map Complex.ofReal).PosDef ∧ ∀ v, ‖form (Y.map Complex.ofReal)⁻¹
      ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)
      ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)‖ ≤
      (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map Complex.ofReal) v ^ 2 := by
  intro g a Y Bs Dm s t c K hc hK hY hcY hB ht hBt hD
  have hBs : ∀ i, (Bs i).IsSymm := fun i =>
    IsSymm.ext fun j k => by simpa using (hB i).isHermitian.apply j k
  have hYpos : ∀ v : Fin g → ℂ, c * ∑ j, ‖v j‖ ^ 2 ≤ (form (Y.map ofReal) v v).re := fun v => by
    rw [re_form_map, sum_norm_sq, mul_add]; exact add_le_add (hcY _) (hcY _)
  have hPD : (Y.map ofReal).PosDef := by
    refine posDef_iff.2 ⟨isHermitian_map hY, fun v hv => ?_⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    have hS : 0 < ∑ j, ‖v j‖ ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hj) 2⟩
    have h1 := hYpos v
    rw [form_map_self hY] at h1 ⊢
    rw [ofReal_re] at h1
    rw [Complex.zero_lt_real]
    linarith [mul_pos hc hS]
  have hYpsd := hPD.posSemidef
  have hBpsd : ∀ i, ((Bs i).map ofReal).PosSemidef := fun i =>
    posSemidef_map (hBs i) fun x => by simpa using (hB i).dotProduct_mulVec_nonneg x
  have hgB : ∀ i w, t i * gnorm ((Bs i).map ofReal) w ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 :=
    fun i w => by
      rw [gnorm_sq (hBpsd i), gnorm_sq hYpsd, re_form_map, re_form_map, mul_add]
      exact add_le_add (hBt i _) (hBt i _)
  have hgY : ∀ w : Fin g → ℂ, c * ∑ j, ‖w j‖ ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 := fun w => by
    rw [gnorm_sq hYpsd]; exact hYpos w
  have hgc : 0 ≤ (g : ℝ) / c := div_nonneg (Nat.cast_nonneg _) hc.le

  have hDb : ∀ u v : Fin g → ℂ, ‖u ⬝ᵥ Dm *ᵥ v‖ ≤
      g * K / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
    intro u v
    have h1 : ‖u ⬝ᵥ Dm *ᵥ v‖ ≤ K * ((∑ j, ‖u j‖) * ∑ k, ‖v k‖) := by
      simp only [dotProduct, mulVec]
      calc _ ≤ ∑ j, ‖u j * ∑ k, Dm j k * v k‖ := norm_sum_le _ _
        _ ≤ ∑ j, ‖u j‖ * ∑ k, K * ‖v k‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun k _ => ?_)) (norm_nonneg _)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hD j k) (norm_nonneg _)
        _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
    have hs : ∀ w : Fin g → ℂ, (∑ j, ‖w j‖) ^ 2 ≤ g / c * gnorm (Y.map ofReal) w ^ 2 :=
      fun w => by
        refine sq_sum_le_card_mul_sum_sq.trans ?_
        rw [Finset.card_univ, Fintype.card_fin, div_mul_eq_mul_div, le_div_iff₀ hc]
        nlinarith [hgY w, (Nat.cast_nonneg g : (0 : ℝ) ≤ g)]
    have hab : (∑ j, ‖u j‖) * (∑ k, ‖v k‖) ≤
        g / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
      rw [← pow_le_pow_iff_left₀ (by positivity)
        (mul_nonneg (mul_nonneg hgc (gnorm_nonneg _ _)) (gnorm_nonneg _ _)) two_ne_zero]
      calc ((∑ j, ‖u j‖) * (∑ k, ‖v k‖)) ^ 2 = (∑ j, ‖u j‖) ^ 2 * (∑ k, ‖v k‖) ^ 2 := mul_pow _ _ _
        _ ≤ (g / c * gnorm (Y.map ofReal) u ^ 2) * (g / c * gnorm (Y.map ofReal) v ^ 2) :=
          mul_le_mul (hs u) (hs v) (sq_nonneg _) (mul_nonneg hgc (sq_nonneg _))
        _ = _ := by ring
    calc _ ≤ K * ((∑ j, ‖u j‖) * ∑ k, ‖v k‖) := h1
      _ ≤ K * (g / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v) :=
        mul_le_mul_of_nonneg_left hab hK
      _ = _ := by ring

  have hBb : ∀ i (u v : Fin g → ℂ), ‖u ⬝ᵥ (Bs i).map ofReal *ᵥ v‖ ≤
      gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v / t i := by
    intro i u v
    rw [dotProduct_mulVec_eq_form ((hBs i).map _)]
    refine (norm_form_le (hBpsd i) _ _).trans ?_
    rw [gnorm_map_star]
    rw [← pow_le_pow_iff_left₀ (mul_nonneg (gnorm_nonneg _ _) (gnorm_nonneg _ _))
      (div_nonneg (mul_nonneg (gnorm_nonneg _ _) (gnorm_nonneg _ _)) (ht i).le) two_ne_zero]
    have a1 : ∀ w, gnorm ((Bs i).map ofReal) w ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 / t i := fun w => by
      rw [le_div_iff₀ (ht i), mul_comm]; exact hgB i w
    calc (gnorm ((Bs i).map ofReal) v * gnorm ((Bs i).map ofReal) u) ^ 2 =
          gnorm ((Bs i).map ofReal) v ^ 2 * gnorm ((Bs i).map ofReal) u ^ 2 := mul_pow _ _ _
      _ ≤ (gnorm (Y.map ofReal) v ^ 2 / t i) * (gnorm (Y.map ofReal) u ^ 2 / t i) :=
          mul_le_mul (a1 v) (a1 u) (sq_nonneg _) (div_nonneg (sq_nonneg _) (ht i).le)
      _ = _ := by ring

  have hPb : ∀ u v : Fin g → ℂ, ‖u ⬝ᵥ (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v‖ ≤
      (g * K / c + ∑ i, ‖s i‖ / t i) * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
    intro u v
    rw [add_mulVec, sum_mulVec, dotProduct_add, dotProduct_finsetSum]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖∑ i, u ⬝ᵥ (s i • (Bs i).map ofReal) *ᵥ v‖ ≤
        ∑ i, ‖s i‖ / t i * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul, norm_mul]
      calc _ ≤ ‖s i‖ * (gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v / t i) :=
            mul_le_mul_of_nonneg_left (hBb i u v) (norm_nonneg _)
        _ = _ := by ring
    calc _ ≤ g * K / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v +
          ∑ i, ‖s i‖ / t i * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v :=
          add_le_add (hDb u v) h2
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

  refine ⟨hPD, fun v => ?_⟩
  have hdet : IsUnit (Y.map ofReal).det := (isUnit_iff_isUnit_det _).1 hPD.isUnit
  set x := (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v with hx
  set q := (Y.map ofReal)⁻¹ *ᵥ star x with hq
  have hF : form (Y.map ofReal)⁻¹ x x = q ⬝ᵥ (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v := by
    rw [form]; exact dotProduct_comm _ _
  have hsq : star q = (Y.map ofReal)⁻¹ *ᵥ x := by
    rw [hq, star_mulVec, star_star, (isHermitian_map hY).inv.eq, ← mulVec_transpose,
      transpose_nonsing_inv, (hY.map _).eq]
  have hq2 : gnorm (Y.map ofReal) q ^ 2 = (form (Y.map ofReal)⁻¹ x x).re := by
    rw [gnorm_sq hYpsd]
    simp only [form]
    rw [hsq, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec, dotProduct_comm]
  have hb := hPb q v
  rw [← hF] at hb
  have hre : gnorm (Y.map ofReal) q ^ 2 ≤ ‖form (Y.map ofReal)⁻¹ x x‖ := hq2 ▸ re_le_norm _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rcases (norm_nonneg (form (Y.map ofReal)⁻¹ x x)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · refine le_of_mul_le_mul_right ?_ h0
    calc ‖form (Y.map ofReal)⁻¹ x x‖ * ‖form (Y.map ofReal)⁻¹ x x‖ =
          ‖form (Y.map ofReal)⁻¹ x x‖ ^ 2 := by ring
      _ ≤ _ := h2
      _ = (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map ofReal) v ^ 2 *
          gnorm (Y.map ofReal) q ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hre (by positivity)

end GlobalTheory.HodgeCurvPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapEqSpanPowUniformizerDvr
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem ideal_map_eq_span_pow_uniformizer
    : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W), Function.Injective f → ∀ (ϖ : V) (w : W) (e a : ℕ) (I : Ideal V), Irreducible ϖ → Irreducible w → Associated (f ϖ) (w ^ e) → I.map f = Ideal.span {w ^ a} → ∃ b : ℕ, e * b = a ∧ I = Ideal.span {ϖ ^ b} := by
  intro V W _ _ _ _ _ _ f _ ϖ w e a I hϖ hw hfe hI
  by_cases h0 : I = ⊥
  · exfalso
    subst h0
    rw [Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at hI
    exact hw.ne_zero (pow_eq_zero_iff'.mp hI).1
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h0 hϖ
  refine ⟨b, ?_, hb⟩
  rw [hb, Ideal.map_span, Set.image_singleton, map_pow,
    Ideal.span_singleton_eq_span_singleton] at hI
  have h1 : Associated (w ^ (e * b)) (w ^ a) := by
    rw [pow_mul]
    exact (hfe.pow_pow (n := b)).symm.trans hI
  have hw0 : w ≠ 0 := hw.ne_zero
  have hwu : ¬ IsUnit w := hw.not_isUnit
  apply le_antisymm
  · exact (pow_dvd_pow_iff hw0 hwu).mp h1.dvd
  · exact (pow_dvd_pow_iff hw0 hwu).mp h1.symm.dvd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImEmbHermSelf
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

namespace GlobalTheory.OrthoFrame

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (u : Fin r → Fin r → E) : Frame Ψ r :=
  fun τ k a => τ.1 (u a k)

theorem col_frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (u : Fin r → Fin r → E) (τ : Ψ) (a : Fin r) :
    col (mat (frm Ψ u) τ) a = Data.emb τ.1 (u a) := rfl

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem hermC_emb {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]

theorem im_emb_herm_self {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (x : Fin r → E) : (τ (herm G x x)).im = 0 := by
  have h2 : conj (τ (herm G x x)) = τ (herm G x x) := by
    rw [← emb_cc, HermitianTraceFormVanishing.herm_conj G hG x x]
  exact Complex.conj_eq_iff_im.1 h2

theorem dmin_frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (u : Fin r → Fin r → E) (ho : ∀ j k, j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G (frm Ψ u) τ i = ∏ k : Fin i, τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
      (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))) := by
  unfold dmin lminor
  have : (gram τ.1 G (mat (frm Ψ u) τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = Matrix.diagonal (fun k => τ.1 (herm G
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))) := by
    ext a b
    simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, col_frm, hermC_emb, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · rw [ho _ _ (fun e => h (Fin.castLE_injective _ e)), map_zero]
  rw [this, Matrix.det_diagonal]

theorem psgn_mul_dmin {r : ℕ} (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (p0 : ℕ)
    (u : Fin r → Fin r → E) (ho : ∀ j k, j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) (i : Fin (r + 1)) :
    psgn p0 i * (dmin G (frm Ψ u) τ i).re = ∏ k : Fin i, (sgn p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) k : Fin r) *
      (τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))).re) := by
  have hr : ∀ w : Fin r → E, τ.1 (herm G w w) = ((τ.1 (herm G w w)).re : ℂ) := fun w =>
    Complex.ext (by simp) (by simp [im_emb_herm_self τ.1 G hG w])
  rw [dmin_frm Ψ G u ho τ i, Finset.prod_mul_distrib, psgn, ← Fin.prod_univ_eq_prod_range]
  congr 1
  rw [Finset.prod_congr rfl (fun k _ => hr _), ← Complex.ofReal_prod, Complex.ofReal_re]

theorem prod_succ {r : ℕ} (f : Fin r → ℝ) (j : Fin r) :
    ∏ k : Fin (j.succ : ℕ), f (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) k) =
      (∏ k : Fin (j.castSucc : ℕ), f (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) k)) * f j := by
  change ∏ k : Fin ((j : ℕ) + 1), f (Fin.castLE _ k) = (∏ k : Fin (j : ℕ), f (Fin.castLE _ k)) * f j
  rw [Fin.prod_univ_castSucc]
  rfl

theorem sign_of_mem {r : ℕ} (X : Data E r) (u : Fin r → Fin r → E)
    (ho : ∀ j k, j ≠ k → herm X.Gm (u j) (u k) = 0) (hu : frm X.Ψ u ∈ X.dom) (τ : X.Ψ) (j : Fin r) :
    0 < sgn X.p0 j * (τ.1 (herm X.Gm (u j) (u j))).re := by
  have h1 := (hu τ).2 j.succ
  have h0 := (hu τ).2 j.castSucc
  rw [psgn_mul_dmin X.Ψ X.Gm X.Gm_herm X.p0 u ho τ] at h1 h0
  rw [prod_succ (fun k => sgn X.p0 k * (τ.1 (herm X.Gm (u k) (u k))).re)] at h1
  exact (pos_iff_pos_of_mul_pos h1).1 h0

theorem mem_of_sign {r : ℕ} (X : Data E r) (u : Fin r → Fin r → E)
    (ho : ∀ j k, j ≠ k → herm X.Gm (u j) (u k) = 0) (hd : (Matrix.of u).det ≠ 0)
    (hs : ∀ τ : X.Ψ, ∀ j : Fin r, 0 < sgn X.p0 j * (τ.1 (herm X.Gm (u j) (u j))).re) : frm X.Ψ u ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have : mat (frm X.Ψ u) τ = τ.1.mapMatrix (Matrix.of u).transpose := by
      ext k a; rfl
    rw [this, ← RingHom.map_det, Matrix.det_transpose]
    exact (map_ne_zero τ.1).2 hd
  · rw [psgn_mul_dmin X.Ψ X.Gm X.Gm_herm X.p0 u ho τ]
    exact Finset.prod_pos fun k _ => hs τ _

end

end GlobalTheory.OrthoFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePlaceCompletionNhdsNEZeroNeBot
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory.QSA

theorem infinitePlace_completion_nhdsNE_neBot : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by
  intro F _ _ w
  have hiso := InfinitePlace.Completion.isometry_extensionEmbedding w
  have h2 : ‖(2 : w.Completion)‖ = 2 := by
    have := (AddMonoidHomClass.isometry_iff_norm _).1 hiso (2 : w.Completion)
    rw [← this, map_ofNat]; simp
  letI : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by rw [h2]; norm_num⟩ }
  exact NormedField.nhdsNE_neBot (0 : w.Completion)
end GlobalTheory.QSA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveTraceGaloisData
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.TorsorTrace

theorem injective_trace_galoisData : ∀ (F D : Type) [CommRing F] [CommRing D] [Algebra F D] (q : ℕ) [NeZero q]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[F] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor F D q act →
    Function.Injective (algebraMap F D) ∧
    (∃ τ : D →ₗ[F] F, ∀ d : D, algebraMap F D (τ d) = ∑ g, act g d) ∧
    ∃ (n : ℕ) (x y : Fin n → D), ∀ g, ∑ i, x i * act g (y i) = if g = 1 then 1 else 0 := by
  intro F D _ _ _ q _ act h
  obtain ⟨_, _, hff, hbij⟩ := h
  have hinj : Function.Injective (algebraMap F D) := FaithfulSMul.algebraMap_injective F D
  refine ⟨hinj, ?_, ?_⟩
  · have hex : ∀ d : D, ∃ c : F, algebraMap F D c = ∑ g, act g d := by
      intro d
      have hfix : ∀ k, act k (∑ g, act g d) = ∑ g, act g d := by
        intro k
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ ?_
        intro g
        simp [map_mul]
      have h1 : (∑ g, act g d) ⊗ₜ[F] (1 : D) = (1 : D) ⊗ₜ[F] (∑ g, act g d) := by
        apply hbij.1
        rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
          map_one, map_one, mul_one, one_mul]
        funext k
        exact (hfix k).symm
      have := (Algebra.IsEffective.of_faithfullyFlat F D (∑ g, act g d)).1 (by
        rw [Algebra.TensorProduct.includeLeftSubRight_apply, h1, sub_self])
      obtain ⟨c, hc⟩ := this
      exact ⟨c, hc⟩
    choose t ht using hex
    refine ⟨{ toFun := t, map_add' := ?_, map_smul' := ?_ }, ht⟩
    · intro a b
      apply hinj
      simp [ht, Finset.sum_add_distrib]
    · intro a b
      apply hinj
      rw [RingHom.id_apply, smul_eq_mul, map_mul, ht, ht, ← Algebra.smul_def, Finset.smul_sum]
      simp
  · obtain ⟨z, hz⟩ := hbij.2 (fun g => if g = 1 then 1 else 0)
    obtain ⟨n, x, y, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
    refine ⟨n, x, y, fun g => ?_⟩
    have := congrFun hz g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply] at this
    exact this

end GlobalTheory.TorsorTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB
section
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def intInd (n d : ℕ) : Matrix (Fin n) (Fin d) k → ℂ := Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[k]} 1

def diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : GL (Fin n) k := SplitFlip.diagGL fun i => if i = i0 then x else 1

def cosetRep {n d : ℕ} (ϖ : kˣ) (i0 : Fin n) (T : Fin d → SplitFlip.Res (k := k) 1) : Matrix (Fin n) (Fin d) k :=
  Matrix.of fun i j => if i = i0 then -((ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k)) else 0

theorem intInd_mem_SB (n d : ℕ) : intInd k n d ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isCompact_intMatrix
  have ho : IsOpen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isOpen_intMatrix
  have hW : IsClopen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := ⟨hc.isClosed, ho⟩
  refine ⟨?_, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp only [Set.mem_setOf_eq] at hx
    simp [intInd, Set.indicator_apply, hy, hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx hy
    simp [intInd, Set.indicator_apply, hy, hx]

theorem intInd_zero (n d : ℕ) : intInd k n d 0 = 1 :=
  Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) k) ∈ {Y | ∀ i j, Y i j ∈ 𝒪[k]} from
    fun _ _ => zero_mem _) _

theorem det_diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : Matrix.GeneralLinearGroup.det (diagAt x i0) = x := by
  rw [diagAt, SplitFlip.det_diagGL, Fintype.prod_eq_single i0 (fun i hi => if_neg hi), if_pos rfl]

theorem diagAt_val {n : ℕ} (x : kˣ) (i0 : Fin n) :
    (diagAt x i0).val = Matrix.diagonal fun i => if i = i0 then (x : k) else 1 := by
  rw [diagAt, SplitFlip.diagGL_val]
  congr 1; funext i; split_ifs <;> simp

end GlobalTheory.HeisUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitLeftFuncAndCechConerveLevels
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isColimit_leftFunc_and_cechConerve_levels :
    ∀ (J : Type) [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{0}) (c : Cocone D), IsColimit c →
      Nonempty (IsColimit (Arrow.leftFunc.mapCocone c)) ∧
      ∀ k : SimplexCategory, Nonempty (IsColimit ((CosimplicialObject.cechConerve ⋙
        (evaluation SimplexCategory CommRingCat.{0}).obj k).mapCocone c)) := by
  intro J _ D c hc
  refine ⟨⟨isColimitOfPreserves Arrow.leftFunc hc⟩, fun k => ⟨?_⟩⟩
  have e : (CosimplicialObject.cechConerve ⋙ (evaluation SimplexCategory CommRingCat.{0}).obj k) =
      CosimplicialObject.augmentedCechConerve ⋙ CosimplicialObject.Augmented.drop ⋙
        (evaluation SimplexCategory CommRingCat.{0}).obj k := rfl
  rw [e]
  have h1 : PreservesColimitsOfSize.{0, 0} (CosimplicialObject.augmentedCechConerve (C := CommRingCat.{0})) :=
    CosimplicialObject.cechConerveAdjunction.leftAdjoint_preservesColimits
  have h0 : PreservesColimitsOfShape J (CosimplicialObject.const CommRingCat.{0}) :=
    preservesColimitsOfShape_of_evaluation _ J fun m => by
      have : PreservesColimitsOfShape J (𝟭 CommRingCat.{0}) := inferInstance
      exact this
  have h2 : PreservesColimitsOfShape J (CosimplicialObject.Augmented.drop (C := CommRingCat.{0})) :=
    Comma.preservesColimitsOfShape_snd
  have h3 : PreservesColimitsOfShape J ((evaluation SimplexCategory CommRingCat.{0}).obj k) := inferInstance
  exact @isColimitOfPreserves _ _ _ _ _ _ _ ((evaluation SimplexCategory CommRingCat.{0}).obj k) _
    (isColimitOfPreserves CosimplicialObject.Augmented.drop
      (isColimitOfPreserves CosimplicialObject.augmentedCechConerve hc)) h3.preservesColimit

end GlobalTheory.EtC
end

