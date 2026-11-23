module

public import ReciprocityTheory.SemistableReduction.Bundle0026

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegR
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def IsAt {K : Type} [Field K] {r : ℕ} (i : Fin r) (x : Fin r → K) : Prop :=
  ∀ a, a ≠ i → x a = 0

theorem gramC_single {K : Type} [Field K] [NumberField K] {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ)
    (σ : K →+* ℂ) (i : Fin r) (x : Fin r → K) (hx : IsAt i x) :
    (gramC (diagMet δ σ) σ ![x]).det.re = ‖σ (x i)‖ ^ 2 * δ σ i := by
  rw [Matrix.det_unique]
  simp only [gramC, Matrix.of_apply, embVec, diagMet, Matrix.mulVec_diagonal, dotProduct,
    Pi.star_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Fin.default_eq_zero, Matrix.cons_val_zero]
    rw [show star (σ (x i)) * (((δ σ i : ℝ) : ℂ) * σ (x i)) =
        ((δ σ i : ℝ) : ℂ) * (starRingEnd ℂ (σ (x i)) * σ (x i)) by
      rw [Complex.star_def]; ring]
    rw [Complex.conj_mul']
    simp only [Complex.re_ofReal_mul]
    norm_cast
    ring
  · intro a _ ha
    simp [Fin.default_eq_zero, hx a ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem latDeg_single {K : Type} [Field K] [NumberField K] {r : ℕ}
    (δ : (K →+* ℂ) → Fin r → ℝ) (C : Submodule (𝓞 K) (Fin r → K)) (i : Fin r) (x : Fin r → K)
    (hx : IsAt i x) :
    latDeg (diagMet δ) C ![x] = Real.log (spanIdx C ![x] : ℝ) -
      (1 / 2) * ∑ σ : K →+* ℂ, Real.log (‖σ (x i)‖ ^ 2 * δ σ i) := by
  unfold latDeg spanIdx
  congr 2
  exact Finset.sum_congr rfl fun σ _ => by rw [gramC_single δ σ i x hx]

theorem sum_log_single {K : Type} [Field K] [NumberField K] (z : K) (hz : z ≠ 0) (d : ℝ)
    (hd : 0 < d) :
    ∑ σ : K →+* ℂ, Real.log (‖σ z‖ ^ 2 * d) =
      2 * Real.log |((Algebra.norm ℚ z : ℚ) : ℝ)| + (Fintype.card (K →+* ℂ) : ℝ) * Real.log d := by
  have h1 : ∀ σ : K →+* ℂ, Real.log (‖σ z‖ ^ 2 * d) = 2 * Real.log ‖σ z‖ + Real.log d := by
    intro σ
    have : ‖σ z‖ ≠ 0 := by simpa using hz
    rw [Real.log_mul (pow_ne_zero 2 this) hd.ne', Real.log_pow]
    push_cast
    ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, sum_log_norm_emb, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

theorem kBasisIn_single {K : Type} [Field K] [NumberField K] {r : ℕ} (i : Fin r)
    (Gr : Submodule (𝓞 K) (Fin r → K)) (hat : ∀ x ∈ Gr, IsAt i x) (v : Fin r → K)
    (hv : v ∈ Gr) (hvi : v i ≠ 0) : IsKBasisIn Gr ![v] := by
  have hv0 : v ≠ 0 := fun h => hvi (by rw [h]; rfl)
  refine ⟨fun j => by fin_cases j; simpa using hv, ?_, ?_⟩
  · exact linearIndependent_unique_iff.2 (by simpa using hv0)
  · intro x hx
    rw [Set.range_unique, Submodule.mem_span_singleton]
    refine ⟨x i / v i, ?_⟩
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, Fin.default_eq_zero, Matrix.cons_val_zero]
    by_cases ha : a = i
    · subst ha
      field_simp
    · rw [hat x hx a ha, hat v hv a ha, mul_zero]

theorem rankOne_le_zero (hB : LatDegBasisStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ i, 0 < δ σ i) (i : Fin r)
    (Gr : Submodule (𝓞 K) (Fin r → K)) (hGr : Gr.FG) (hat : ∀ x ∈ Gr, IsAt i x)
    (x0 : Fin r → K) (hx0 : x0 ∈ Gr) (hx0i : x0 i ≠ 0)
    (hdeg : latDeg (diagMet δ) Gr ![x0] ≤ 0) (C : Submodule (𝓞 K) (Fin r → K)) (hC : C ≤ Gr)
    (k : ℕ) (c : Fin k → Fin r → K) (hc : IsKBasisIn C c) : latDeg (diagMet δ) C c ≤ 0 := by
  have hpd : ∀ σ, (diagMet δ σ).PosDef := fun σ =>
    Matrix.posDef_diagonal_iff.2 fun a => by exact_mod_cast hδ σ a
  have hci : ∀ j, c j i ≠ 0 := by
    intro j h0
    apply hc.2.1.ne_zero j
    funext a
    by_cases ha : a = i
    · subst ha; exact h0
    · exact hat _ (hC (hc.1 j)) a ha
  match k, c, hc, hci with
  | 0, c, hc, _ => exact (latDeg_zero_fam _ _ c hc).le
  | 1, c, hc, hci =>
    have hc1 : c = ![c 0] := by funext j; fin_cases j; rfl
    have hGc : IsKBasisIn Gr c := by
      rw [hc1]
      exact kBasisIn_single i Gr hat (c 0) (hC (hc.1 0)) (hci 0)
    calc latDeg (diagMet δ) C c ≤ latDeg (diagMet δ) Gr c :=
          latDeg_le_of_le _ C Gr c hC hGr hc hGc
      _ = latDeg (diagMet δ) Gr ![x0] :=
          hB K r 1 (diagMet δ) Gr c ![x0] hpd hGr hGc (kBasisIn_single i Gr hat x0 hx0 hx0i)
      _ ≤ 0 := hdeg
  | k + 2, c, hc, hci =>
    exfalso
    have hli := hc.2.1
    let t : Fin (k + 2) → K := fun j => if j = 0 then c 1 i else if j = 1 then -(c 0 i) else 0
    have ht : ∑ j, t j • c j = 0 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have h0 : ∀ j : Fin k, t j.succ.succ = 0 := fun j => by
        simp only [t]
        rw [if_neg (Fin.succ_ne_zero _), if_neg]
        intro h
        exact Fin.succ_ne_zero j (Fin.succ_injective _ h)
      simp only [h0, zero_smul, Finset.sum_const_zero, add_zero]
      have t0 : t 0 = c 1 i := by simp [t]
      have t1 : t (Fin.succ 0) = -(c 0 i) := by
        simp only [t]
        rw [if_neg (Fin.succ_ne_zero _)]
        rfl
      rw [t0, t1]
      funext a
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases ha : a = i
      · subst ha
        simp only [Fin.succ_zero_eq_one]
        ring
      · rw [hat _ (hC (hc.1 0)) a ha, hat _ (hC (hc.1 _)) a ha]
        ring
    have := Fintype.linearIndependent_iff.1 hli t ht 1
    simp [t] at this
    exact hci 0 this

theorem relIndex_sup_proj {G : Type} [AddCommGroup G] (π : G →+ G) (A X C : AddSubgroup G)
    (hXC : X ≤ C) (hA : ∀ a ∈ A, π a = 0) (hC : ∀ x ∈ C, π x = x) :
    (A ⊔ X).relIndex (A ⊔ C) = X.relIndex C := by
  have heq : A ⊔ X = X.comap π ⊓ (A ⊔ C) := by
    apply le_antisymm
    · refine le_inf (sup_le ?_ ?_) (sup_le_sup_left hXC A)
      · intro a ha
        show π a ∈ X
        rw [hA a ha]
        exact X.zero_mem
      · intro x hx
        show π x ∈ X
        rw [hC x (hXC hx)]
        exact hx
    · rintro z ⟨hzX, hz⟩
      obtain ⟨a, ha, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hz
      have hπ : π (a + w) = w := by rw [map_add (f := _), hA a ha, hC w hw, zero_add]
      have hwX : w ∈ X := by
        have : π (a + w) ∈ X := hzX
        rwa [hπ] at this
      exact AddSubgroup.add_mem_sup ha hwX
  have hmap : (A ⊔ C).map π = C := by
    rw [AddSubgroup.map_sup]
    have h1 : A.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨a, ha, rfl⟩
      rw [hA a ha]
      exact AddSubgroup.zero_mem _
    have h2 : C.map π = C := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        rw [hC x hx]
        exact hx
      · intro x hx
        exact ⟨x, hx, hC x hx⟩
    rw [h1, h2, bot_sup_eq]
  rw [heq, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, hmap]

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

-- bundled from ReciprocityTheory.SemistableReduction.ShareBallB
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix

def sbDp (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => if (k : ℕ) < p then 1 else 0

def sbDn (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => if (k : ℕ) < p then 0 else 1

theorem sb_signMat_eq (p r : ℕ) : signMat p r = sbDp p r - sbDn p r := by
  simp only [signMat, sgn, sbDp, sbDn, diagonal_sub]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_add_Dn (p r : ℕ) : sbDp p r + sbDn p r = 1 := by
  simp only [sbDp, sbDn, diagonal_add]
  rw [← diagonal_one]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_mul_Dp (p r : ℕ) : sbDp p r * sbDp p r = sbDp p r := by
  simp only [sbDp, diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dn_mul_Dn (p r : ℕ) : sbDn p r * sbDn p r = sbDn p r := by
  simp only [sbDn, diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_mul_Dn (p r : ℕ) : sbDp p r * sbDn p r = 0 := by
  simp only [sbDp, sbDn, diagonal_mul_diagonal]
  rw [← diagonal_zero]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dn_mul_Dp (p r : ℕ) : sbDn p r * sbDp p r = 0 := by
  simp only [sbDp, sbDn, diagonal_mul_diagonal]
  rw [← diagonal_zero]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_herm (p r : ℕ) : (sbDp p r)ᴴ = sbDp p r := by
  simp only [sbDp, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_Dn_herm (p r : ℕ) : (sbDn p r)ᴴ = sbDn p r := by
  simp only [sbDn, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_J_herm (p r : ℕ) : (signMat p r)ᴴ = signMat p r := by
  simp only [signMat, sgn, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_J_mul_J (p r : ℕ) : signMat p r * signMat p r = 1 := by
  simp only [signMat, sgn, diagonal_mul_diagonal]
  rw [← diagonal_one]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_posSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posSq p u = normSq (sbDp p r *ᵥ u) := by
  simp only [posSq, normSq, sbDp, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem sb_negSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negSq p u = normSq (sbDn p r *ᵥ u) := by
  simp only [negSq, normSq, sbDn, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem sb_herm_swap {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ} (hM : Mᴴ = M) (v w : Fin r → ℂ) :
    star v ⬝ᵥ (M *ᵥ w) = star (M *ᵥ v) ⬝ᵥ w := by
  rw [star_mulVec, hM, dotProduct_mulVec]

theorem sb_dot_Dp (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (sbDp p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) := by
  have h := sb_herm_swap (sb_Dp_herm p r) v (sbDp p r *ᵥ w)
  rw [mulVec_mulVec, sb_Dp_mul_Dp] at h
  exact h

theorem sb_dot_Dn (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (sbDn p r *ᵥ w) = star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  have h := sb_herm_swap (sb_Dn_herm p r) v (sbDn p r *ᵥ w)
  rw [mulVec_mulVec, sb_Dn_mul_Dn] at h
  exact h

theorem sb_dot_split (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ w = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) +
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  rw [← sb_dot_Dp p v w, ← sb_dot_Dn p v w, ← dotProduct_add, ← add_mulVec, sb_Dp_add_Dn,
    one_mulVec]

theorem sb_dot_J (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (signMat p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) -
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  rw [sb_signMat_eq, sub_mulVec, dotProduct_sub, sb_dot_Dp p v w, sb_dot_Dn p v w]

private theorem re_star_dotProduct_self_eq_normSq {r : ℕ} (x : Fin r → ℂ) : (star x ⬝ᵥ x).re = normSq x := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, normSq]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (star (x k) * x k).re = (x k).re * (x k).re + (x k).im * (x k).im := by
    simp [Complex.mul_re] <;> ring
  rw [h1, ← Complex.normSq_apply]
  first
    | exact (Complex.sq_norm _).symm
    | exact Complex.normSq_eq_norm_sq _
    | simp [Complex.sq_abs]

theorem sb_re_dot_J (p : ℕ) {r : ℕ} (v : Fin r → ℂ) :
    (star v ⬝ᵥ (signMat p r *ᵥ v)).re = posSq p v - negSq p v := by
  rw [sb_dot_J, Complex.sub_re, re_star_dotProduct_self_eq_normSq, re_star_dotProduct_self_eq_normSq, sb_posSq_eq, sb_negSq_eq]

theorem sb_cs {r : ℕ} (v w : Fin r → ℂ) : (star v ⬝ᵥ w).re ^ 2 ≤ normSq v * normSq w := by
  have h1 : |(star v ⬝ᵥ w).re| ≤ ∑ k, ‖v k‖ * ‖w k‖ := by
    have e1 : |(star v ⬝ᵥ w).re| ≤ ‖star v ⬝ᵥ w‖ := by
      first
        | exact Complex.abs_re_le_norm _
        | exact RCLike.abs_re_le_norm _
        | exact Complex.abs_re_le_abs _
    have e2 : ‖star v ⬝ᵥ w‖ ≤ ∑ k, ‖star (v k) * w k‖ := by
      unfold dotProduct
      exact norm_sum_le _ _
    have e3 : ∑ k, ‖star (v k) * w k‖ = ∑ k, ‖v k‖ * ‖w k‖ := by
      simp [norm_mul, norm_star]
    linarith
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖v k‖) (fun k => ‖w k‖)
  have h3 : (star v ⬝ᵥ w).re ^ 2 ≤ (∑ k, ‖v k‖ * ‖w k‖) ^ 2 :=
    sq_le_sq.mpr (h1.trans (le_abs_self _))
  unfold normSq
  exact h3.trans h2

private theorem two_mul_one_add_mul_le_of_le_mul (a b c d s : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hcd : c ≤ s * d) (hs1 : s < 1) (hle : a * c ≤ b * d) :
    2 * (1 + s) * (a * c) ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 := by
  rcases eq_or_lt_of_le hd with h0 | hdpos
  · subst h0
    have hc0 : c = 0 := le_antisymm (by simpa using hcd) hc
    subst hc0
    nlinarith [mul_nonneg hs (sq_nonneg a), sq_nonneg b]
  · have hsq : (a * c) * (a * c) ≤ (b * d) * (b * d) :=
      mul_self_le_mul_self (mul_nonneg ha hc) hle
    have hdc : 0 ≤ d - c := by nlinarith
    have hsdc : 0 ≤ s * d - c := by linarith
    have e1 : 0 ≤ (s * d ^ 2 + c ^ 2) * (a - d) ^ 2 :=
      mul_nonneg (add_nonneg (mul_nonneg hs (sq_nonneg d)) (sq_nonneg c)) (sq_nonneg _)
    have e2 : 0 ≤ 2 * a * d * ((d - c) * (s * d - c)) :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two ha) hd) (mul_nonneg hdc hsdc)
    have hd2 : 0 < d ^ 2 := pow_pos hdpos 2
    by_contra hneg
    push_neg at hneg
    have e3 := mul_lt_mul_of_pos_left hneg hd2
    nlinarith

theorem sb_real_bounds (a b c d s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hs1 : s < 1) (hba : b ≤ s * a) (hcd : c ≤ s * d) (h1 : |t| ≤ a * c)
    (h2 : |t| ≤ b * d) :
    0 ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 + 2 * (1 + s) * t ∧
      0 ≤ s * (a ^ 2 + d ^ 2) - (b ^ 2 + c ^ 2) - 2 * (1 - s) * t := by
  have hTc : |t| ≤ a * c := h1
  have hTad : |t| ≤ s * a * d := by
    have := mul_le_mul_of_nonneg_left hcd ha
    nlinarith
  have hs0 : 0 ≤ 1 - s := by linarith
  have key : 2 * (1 + s) * |t| ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 := by
    rcases le_total (a * c) (b * d) with hle | hle
    · have e := two_mul_one_add_mul_le_of_le_mul a b c d s ha hc hd hs hcd hs1 hle
      have e' := mul_le_mul_of_nonneg_left hTc (by linarith : (0 : ℝ) ≤ 2 * (1 + s))
      nlinarith
    · have e := two_mul_one_add_mul_le_of_le_mul d c b a s hd hb ha hs hba hs1
        (by rw [mul_comm d b, mul_comm c a]; exact hle)
      have e' := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * (1 + s))
      nlinarith
  have htl : 0 ≤ t + |t| := by linarith [neg_abs_le t]
  have htu : t ≤ |t| := le_abs_self t
  have hb2 : b * b ≤ (s * a) * (s * a) := mul_self_le_mul_self hb hba
  have hc2 : c * c ≤ (s * d) * (s * d) := mul_self_le_mul_self hc hcd
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 + s)) htl]
  · nlinarith [mul_nonneg (mul_nonneg hs hs0) (sq_nonneg (a - d)),
      mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ s * a * d - t)]

end ReciprocityTheory.MultiplicativeHeights
end
end

