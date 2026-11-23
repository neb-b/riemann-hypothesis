module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.SiegelSum

theorem summable_pi_prod {J A : Type} [Fintype J] (f : J → A → ℝ) (h0 : ∀ j a, 0 ≤ f j a)
    (hs : ∀ j, Summable (f j)) : Summable fun n : J → A => ∏ j, f j (n j) := by
  first
  | exact @_root_.GlobalTheory.SummableProdPi.summable_prod_pi
  | exact _root_.GlobalTheory.SummableProdPi.summable_prod_pi
  | (apply _root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> assumption)
  | (intros; apply _root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SummableProdPi.summable_prod_pi ..)

theorem exists_mul_dotProduct_le {ι : Type} [Fintype ι] {Y : Matrix ι ι ℝ} (hY : Y.PosDef) :
    ∃ c > 0, ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Y *ᵥ x) := by
  have hc : Continuous fun x : ι → ℝ => x ⬝ᵥ (Y *ᵥ x) := by
    simp only [dotProduct, mulVec]
    fun_prop
  obtain ⟨c, hc0, hcl⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_forall_le'
    hc.continuousOn (a := 0) (fun q hq => by
      have hx0 : q ≠ 0 := by
        intro h0
        simp [h0] at hq
      simpa using hY.dotProduct_mulVec_pos hx0)
  refine ⟨c / (Fintype.card ι + 1), by positivity, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 := hcl (‖x‖⁻¹ • x) (by simp [norm_smul, hn.ne'])
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
  have h2 : c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Y *ᵥ x) := by
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)
    refine this.trans_eq ?_
    field_simp
  have h3 : x ⬝ᵥ x ≤ (Fintype.card ι + 1) * ‖x‖ ^ 2 := by
    have : x ⬝ᵥ x ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
      have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at this
      rw [← sq, ← sq_abs]
      gcongr
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    nlinarith [sq_nonneg ‖x‖]
  calc c / (Fintype.card ι + 1) * (x ⬝ᵥ x) ≤ c / (Fintype.card ι + 1) *
        ((Fintype.card ι + 1) * ‖x‖ ^ 2) := by gcongr
    _ = c * ‖x‖ ^ 2 := by field_simp
    _ ≤ _ := h2

theorem exists_int_of_intM {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (hR : 0 < R)
    {x : Matrix κ ι ℚ} (hx : IntM ((R : ℚ) • x)) :
    ∃ n : κ → ι → ℤ, x = Matrix.of fun k i => (n k i : ℚ) / R := by
  have : ∀ k i, ∃ n : ℤ, (n : ℚ) = R * x k i := fun k i => by
    have := IsIntegrallyClosed.isIntegral_iff.1 (hx k i)
    simpa using this
  choose n hn using this
  refine ⟨n, ?_⟩
  ext k i
  have : (R : ℚ) ≠ 0 := by positivity
  simp only [of_apply, hn]
  field_simp

theorem exists_bound {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (hR : 0 < R)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) : ∃ M, ∀ x, ‖φ x‖ ≤ M := by
  classical
  let g : (κ → ι → Fin (R * R)) → ℝ := fun r => ‖φ (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R)‖
  refine ⟨∑ r, g r, fun x => ?_⟩
  by_cases hx : φ x = 0
  · rw [hx, norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨n, rfl⟩ := exists_int_of_intM hR (h.1 x hx)
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  let r : κ → ι → Fin (R * R) := fun k i => ⟨(n k i % (R * R)).toNat, by
    have := Int.emod_lt_of_pos (n k i) hRR
    have := Int.emod_nonneg (n k i) hRR.ne'
    zify; rw [Int.toNat_of_nonneg this]; assumption⟩
  have key := h.2 (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R)
    (Matrix.of fun k i => ((n k i / (R * R) : ℤ) : ℚ)) (fun k i => isIntegral_algebraMap (x := n k i / (R * R)))
  have he : (Matrix.of fun k i => (n k i : ℚ) / R) =
      (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R) +
        (R : ℚ) • (Matrix.of fun k i => ((n k i / (R * R) : ℤ) : ℚ)) := by
    ext k i
    have h1 : (((r k i : ℕ) : ℤ)) = n k i % (R * R) :=
      Int.toNat_of_nonneg (Int.emod_nonneg (n k i) hRR.ne')
    have h2 := Int.emod_add_mul_ediv (n k i) (R * R)
    rw [← h1] at h2
    have h3 : ((r k i : ℕ) : ℚ) + R * R * ((n k i / (R * R) : ℤ) : ℚ) = n k i := by
      exact_mod_cast h2
    have : (R : ℚ) ≠ 0 := by positivity
    simp only [of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← h3]
    field_simp
  rw [he, key]
  exact Finset.single_le_sum (f := g) (fun _ _ => norm_nonneg _) (Finset.mem_univ r)

theorem sum_le_im {ι : Type} [Fintype ι] {τ : Matrix ι ι ℂ} {c S : ℝ}
    (hc : ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (τ.map Complex.im *ᵥ x)) (ζ : ι → ℂ)
    (hS : ∀ i, |(ζ i).im| ≤ S) (v : ι → ℚ) :
    ∑ i, (c * (v i : ℝ) ^ 2 - 2 * S * |(v i : ℝ)|) ≤
      (qv v ⬝ᵥ τ *ᵥ qv v + 2 * (qv v ⬝ᵥ ζ)).im := by
  have h1 : (qv v ⬝ᵥ τ *ᵥ qv v).im =
      (fun i => (v i : ℝ)) ⬝ᵥ (τ.map Complex.im *ᵥ fun i => (v i : ℝ)) := by
    simp [dotProduct, mulVec, qv, Complex.im_sum, Complex.re_sum]
  have h2 : (2 * (qv v ⬝ᵥ ζ)).im = ∑ i, 2 * ((v i : ℝ) * (ζ i).im) := by
    simp [dotProduct, qv, Complex.im_sum, Finset.mul_sum]
  rw [Complex.add_im, h1, h2, Finset.sum_sub_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  refine add_le_add (le_trans (le_of_eq ?_) (hc _)) (Finset.sum_le_sum fun i _ => ?_)
  · simp [dotProduct, Finset.mul_sum, sq]
  · have h3 := neg_abs_le ((v i : ℝ) * (ζ i).im)
    rw [abs_mul] at h3
    nlinarith [hS i, abs_nonneg (v i : ℝ)]

theorem summable_norm_thetaTerm : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ : Matrix κ ι ℚ → ℂ), IsSB φ → ∀ τ ∈ Siegel ι, ∀ ζ : κ → ι → ℂ, Summable fun x : Matrix κ ι ℚ => ‖φ x * cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))‖ := by
  intro κ ι _ _ _ φ ⟨R, hR, h⟩ τ hτ ζ
  obtain ⟨M, hM⟩ := exists_bound hR h
  obtain ⟨c, hc0, hc⟩ := exists_mul_dotProduct_le hτ.2
  have hR0 : (R : ℝ) ≠ 0 := by positivity
  have hS : ∀ k i, |(ζ k i).im| ≤ ‖ζ‖ := fun k i =>
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (ζ k) i).trans (norm_le_pi_norm ζ k))
  let e : (κ → ι → ℤ) → Matrix κ ι ℚ := fun n => Matrix.of fun k i => (n k i : ℚ) / R
  have he : Function.Injective e := by
    intro m n hmn
    funext k i
    have h1 : (m k i : ℚ) / R = (n k i : ℚ) / R := congrFun (congrFun hmn k) i
    have : (R : ℚ) ≠ 0 := by positivity
    exact_mod_cast (div_left_inj' this).1 h1
  refine (he.summable_iff fun x hx => ?_).1 ?_
  · have : φ x = 0 := by
      by_contra h0
      obtain ⟨n, hn⟩ := exists_int_of_intM hR (h.1 x h0)
      exact hx ⟨n, hn.symm⟩
    simp [this]
  let f : ℤ → ℝ := fun n => Real.exp (-π * (c / R ^ 2 * n ^ 2 - 2 * (‖ζ‖ / R) * |n|))
  have hf : Summable f := by
    simpa [f] using summable_pow_mul_jacobiTheta₂_term_bound (‖ζ‖ / R)
      (T := c / R ^ 2) (by positivity) 0
  have hs : Summable fun n : κ → ι → ℤ => ∏ k, ∏ i, f (n k i) :=
    summable_pi_prod (fun (_ : κ) (m : ι → ℤ) => ∏ i, f (m i))
      (fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
      fun _ => summable_pi_prod (fun _ => f) (fun _ _ => (Real.exp_pos _).le) fun _ => hf
  refine (hs.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  simp only [Function.comp_apply, norm_mul]
  refine mul_le_mul (hM _) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hM 0))
  simp only [f, ← Real.exp_sum, Complex.norm_exp, Real.exp_le_exp, ← Finset.mul_sum]
  have h1 : ∀ z : ℂ, (π * I * z).re = -π * z.im := fun z => by simp
  rw [h1, Complex.im_sum]
  refine mul_le_mul_of_nonpos_left (Finset.sum_le_sum fun k _ => ?_) (by linarith [Real.pi_pos])
  refine le_trans (le_of_eq ?_) (sum_le_im hc (ζ k) (hS k) (e n k))
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [e, of_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, abs_div, Nat.abs_cast,
    Int.cast_abs]
  field_simp

end GlobalTheory.SW.SiegelSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SiegelAction

open scoped ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem posDef_ofReal {Y : Matrix ι ι ℝ} (h : Y.PosDef) :
    (Y.map (fun t => (t : ℂ))).PosDef := by
  have hs : ∀ i j, Y i j = Y j i := fun i j => by
    have := congrFun (congrFun h.isHermitian j) i
    simpa using this
  have hH : (Y.map (fun t => (t : ℂ))).IsHermitian := by
    ext i j
    simp [hs i j]
  refine PosDef.of_dotProduct_mulVec_pos hH fun v hv => ?_
  have hre : (star v ⬝ᵥ (Y.map (fun t => (t : ℂ))) *ᵥ v).re =
      star (fun i => (v i).re) ⬝ᵥ Y *ᵥ (fun i => (v i).re) +
      star (fun i => (v i).im) ⬝ᵥ Y *ᵥ (fun i => (v i).im) := by
    simp [dotProduct, mulVec, Finset.mul_sum, Finset.sum_add_distrib]
  have him : (star v ⬝ᵥ (Y.map (fun t => (t : ℂ))) *ᵥ v).im = 0 := by
    have := hH.im_star_dotProduct_mulVec_self v
    simpa using this
  rw [Complex.pos_iff, hre, him]
  refine ⟨?_, rfl⟩
  by_cases h1 : (fun i => (v i).re) = 0
  · have h2 : (fun i => (v i).im) ≠ 0 := fun h2 => hv (by
      ext i
      exact Complex.ext (congrFun h1 i) (congrFun h2 i))
    exact add_pos_of_nonneg_of_pos (h.posSemidef.dotProduct_mulVec_nonneg _)
      (h.dotProduct_mulVec_pos h2)
  · exact add_pos_of_pos_of_nonneg (h.dotProduct_mulVec_pos h1)
      (h.posSemidef.dotProduct_mulVec_nonneg _)


omit [DecidableEq ι] in
theorem posDef_of_ofReal {Y : Matrix ι ι ℝ} (h : (Y.map (fun t => (t : ℂ))).PosDef) :
    Y.PosDef := by
  have hH : Y.IsHermitian := by
    ext i j
    have := congrFun (congrFun h.isHermitian i) j
    simpa using this
  refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hv : (fun i => (x i : ℂ)) ≠ 0 := fun h0 => hx (by
    ext i
    simpa using congrFun h0 i)
  have := (Complex.pos_iff.1 (h.dotProduct_mulVec_pos hv)).1
  simpa [dotProduct, mulVec, Finset.mul_sum] using this

omit [Fintype ι] [DecidableEq ι] in
theorem sub_conj_eq (τ : Matrix ι ι ℂ) :
    τ - τ.map conj = (2 * I) • τ.map (fun z => (z.im : ℂ)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Complex.sub_conj]
  push_cast
  ring

theorem block_identity {A B C D τ τ' : Matrix ι ι ℂ}
    (h : fromBlocks A B C D ∈ symplecticGroup ι ℂ) (hτ : τ.IsSymm) :
    (A * τ + B)ᵀ * (C * τ' + D) - (C * τ + D)ᵀ * (A * τ' + B) = τ - τ' := by
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 h
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by simpa using congrArg transpose h3
  have : (A * τ + B)ᵀ * (C * τ' + D) - (C * τ + D)ᵀ * (A * τ' + B) =
      τ * (Aᵀ * C - Cᵀ * A) * τ' + τ * (Aᵀ * D - Cᵀ * B) - (Dᵀ * A - Bᵀ * C) * τ' +
        (Bᵀ * D - Dᵀ * B) := by
    simp only [transpose_add, transpose_mul, hτ.eq]
    noncomm_ring
  rw [this, h1, h2, h3, h4]
  simp

theorem act_complex {A B C D τ : Matrix ι ι ℂ}
    (h : fromBlocks A B C D ∈ symplecticGroup ι ℂ) (hA : A.map conj = A) (hB : B.map conj = B)
    (hC : C.map conj = C) (hD : D.map conj = D) (hτ : τ ∈ Siegel ι) :
    (C * τ + D).det ≠ 0 ∧ (A * τ + B) * (C * τ + D)⁻¹ ∈ Siegel ι ∧ ((C * τ + D)⁻¹ * C).IsSymm ∧
      (C * τ + D)ᵀ * ((A * τ + B) * (C * τ + D)⁻¹).map (fun z => (z.im : ℂ)) *
        (C * τ + D).map conj = τ.map (fun z => (z.im : ℂ)) := by
  obtain ⟨hs, hp⟩ := hτ
  have hY : (τ.map (fun z => (z.im : ℂ))).PosDef := posDef_ofReal hp
  have e1 := block_identity (τ' := τ) h hs
  have e2 := block_identity (τ' := τ.map conj) h hs
  have cP : (A * τ + B).map conj = A * τ.map conj + B := by
    rw [Matrix.map_add _ (map_add conj), Matrix.map_mul, hA, hB]
  have cQ : (C * τ + D).map conj = C * τ.map conj + D := by
    rw [Matrix.map_add _ (map_add conj), Matrix.map_mul, hC, hD]
  have e3 : C * (C * τ + D)ᵀ = (C * τ + D) * Cᵀ := by
    have ht := SymplecticGroup.transpose_mem h
    rw [fromBlocks_transpose] at ht
    obtain ⟨-, h2, -⟩ := SymplecticGroup.fromBlocks_mem_iff.1 ht
    simp only [transpose_transpose] at h2
    simp only [transpose_add, transpose_mul, hs.eq, Matrix.mul_add, Matrix.add_mul, h2,
      Matrix.mul_assoc]
  rw [← cP, ← cQ, sub_conj_eq] at e2
  rw [sub_self, sub_eq_zero] at e1
  generalize A * τ + B = P at *
  generalize C * τ + D = Q at *
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  have hQt : (Q.map conj)ᴴ = Qᵀ := by
    ext i j; simp
  have hdet : Q.det ≠ 0 := by
    intro h0
    have h0' : (Q.map conj).det = 0 := by
      have := RingHom.map_det (starRingEnd ℂ) Q
      rw [h0, map_zero] at this
      exact this.symm
    obtain ⟨v, hv, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    have hQv' : star v ᵥ* Qᵀ = 0 := by
      rw [← hQt, ← star_mulVec, hQv, star_zero]
    have hpos := hY.dotProduct_mulVec_pos hv
    have := congrArg (fun M => star v ⬝ᵥ M *ᵥ v) e2
    simp only [sub_mulVec, ← mulVec_mulVec, hQv, mulVec_zero, dotProduct_sub, dotProduct_zero,
      smul_mulVec, dotProduct_smul, smul_eq_mul] at this
    rw [dotProduct_mulVec (star v) Qᵀ, hQv', zero_dotProduct, sub_zero] at this
    exact hpos.ne' ((mul_eq_zero.1 this.symm).resolve_left h2I)
  have hu : IsUnit Q.det := hdet.isUnit
  have hut : IsUnit Qᵀ.det := by rwa [det_transpose]
  have hWQ : P * Q⁻¹ * Q = P := nonsing_inv_mul_cancel_right _ _ hu
  have hQW : Qᵀ * (P * Q⁻¹) = Pᵀ := by
    rw [← Matrix.mul_assoc, ← e1, mul_nonsing_inv_cancel_right _ _ hu]
  have hWs : (P * Q⁻¹).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_nonsing_inv, ← hQW, nonsing_inv_mul_cancel_left _ _ hut]
  have hcW : (P * Q⁻¹).map conj * Q.map conj = P.map conj := by
    rw [← Matrix.map_mul, hWQ]
  have key : Qᵀ * (P * Q⁻¹).map (fun z => (z.im : ℂ)) * Q.map conj =
      τ.map (fun z => (z.im : ℂ)) := by
    apply smul_right_injective _ h2I
    simp only
    rw [← e2, ← Matrix.smul_mul, ← Matrix.mul_smul, ← sub_conj_eq, Matrix.mul_sub, Matrix.sub_mul,
      hQW, Matrix.mul_assoc Qᵀ, hcW]
  refine ⟨hdet, ⟨hWs, posDef_of_ofReal ?_⟩, ?_, key⟩
  · have huc : IsUnit (Q.map conj) := by
      rw [isUnit_iff_isUnit_det]
      have := RingHom.map_det (starRingEnd ℂ) Q
      exact this ▸ hu.map (starRingEnd ℂ)
    refine (Matrix.IsUnit.posDef_star_left_conjugate_iff huc).1 ?_
    rw [star_eq_conjTranspose, hQt]
    rw [← key] at hY
    exact hY
  · rw [IsSymm, transpose_mul, transpose_nonsing_inv]
    calc Cᵀ * Qᵀ⁻¹ = Q⁻¹ * (Q * Cᵀ) * Qᵀ⁻¹ := by rw [nonsing_inv_mul_cancel_left _ _ hu]
      _ = Q⁻¹ * C := by
        rw [← e3, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hut]

theorem qm_conj {α β : Type} (A : Matrix α β ℚ) : (qm A).map conj = qm A := by
  ext i j; simp [qm]

theorem qm_add {α β : Type} (A B : Matrix α β ℚ) : qm (A + B) = qm A + qm B := by
  ext i j; simp [qm]

theorem qm_mul {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    qm (A * B) = qm A * qm B := by
  ext i j; simp [qm, Matrix.mul_apply]

theorem qm_blocks_mem {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ symplecticGroup ι ℚ) :
    fromBlocks (qm σ.toBlocks₁₁) (qm σ.toBlocks₁₂) (qm σ.toBlocks₂₁) (qm σ.toBlocks₂₂) ∈
      symplecticGroup ι ℂ := by
  have := SymplecticGroup.map_mem h (Rat.castHom ℂ)
  rw [← fromBlocks_toBlocks σ, fromBlocks_map] at this
  exact this

omit [DecidableEq ι] in
theorem toBlocks_mul (σ' σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) :
    (σ' * σ).toBlocks₁₁ = σ'.toBlocks₁₁ * σ.toBlocks₁₁ + σ'.toBlocks₁₂ * σ.toBlocks₂₁ ∧
    (σ' * σ).toBlocks₁₂ = σ'.toBlocks₁₁ * σ.toBlocks₁₂ + σ'.toBlocks₁₂ * σ.toBlocks₂₂ ∧
    (σ' * σ).toBlocks₂₁ = σ'.toBlocks₂₁ * σ.toBlocks₁₁ + σ'.toBlocks₂₂ * σ.toBlocks₂₁ ∧
    (σ' * σ).toBlocks₂₂ = σ'.toBlocks₂₁ * σ.toBlocks₁₂ + σ'.toBlocks₂₂ * σ.toBlocks₂₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply]

theorem symplectic_action : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι,
    (spDen σ τ).det ≠ 0 ∧ spAct σ τ ∈ Siegel ι ∧ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁).IsSymm ∧
    (spDen σ τ)ᵀ * (spAct σ τ).map (fun z => (z.im : ℂ)) * (spDen σ τ).map conj =
      τ.map (fun z => (z.im : ℂ)) ∧
    ∀ σ' ∈ Matrix.symplecticGroup ι ℚ, spDen (σ' * σ) τ = spDen σ' (spAct σ τ) * spDen σ τ ∧
      spAct (σ' * σ) τ = spAct σ' (spAct σ τ) := by
  intro ι _ _ σ hσ τ hτ
  obtain ⟨h1, h2, h3, h4⟩ := act_complex (qm_blocks_mem hσ) (qm_conj _) (qm_conj _) (qm_conj _)
    (qm_conj _) hτ
  refine ⟨h1, h2, h3, h4, fun σ' _ => ?_⟩
  have hu : IsUnit (spDen σ τ).det := h1.isUnit
  have hWQ : spAct σ τ * spDen σ τ = qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂ :=
    nonsing_inv_mul_cancel_right _ _ hu
  obtain ⟨m1, m2, m3, m4⟩ := toBlocks_mul σ' σ
  have gen : ∀ X Y : Matrix ι ι ℚ,
      qm (X * σ.toBlocks₁₁ + Y * σ.toBlocks₂₁) * τ + qm (X * σ.toBlocks₁₂ + Y * σ.toBlocks₂₂) =
        (qm X * spAct σ τ + qm Y) * spDen σ τ := by
    intro X Y
    rw [Matrix.add_mul (qm X * spAct σ τ), Matrix.mul_assoc, hWQ]
    simp only [qm_add, qm_mul, spDen]
    noncomm_ring
  have hden : spDen (σ' * σ) τ = spDen σ' (spAct σ τ) * spDen σ τ := by
    rw [spDen, m3, m4, gen]; rfl
  refine ⟨hden, ?_⟩
  rw [spAct, hden, m1, m2, gen, Matrix.mul_inv_rev, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ hu]
  rfl

end GlobalTheory.SiegelAction
end

