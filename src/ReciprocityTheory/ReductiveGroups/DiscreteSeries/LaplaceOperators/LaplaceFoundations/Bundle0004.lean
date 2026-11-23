module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.UnitaryHaarColumns

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.EqZeroOfInPOfNoncompactRankZero
section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.LieExponentialMajorant

variable {n : ℕ}

theorem hs_eq_re_trace (A : Matrix (Fin n) (Fin n) ℂ) :
    S7.hs A = (trace (Aᴴ * A)).re := by
  simp only [S7.hs, trace, diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem sqrt_hs_mul (A B : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (S7.hs (A * B)) ≤ Real.sqrt (S7.hs A) * Real.sqrt (S7.hs B) := by
  let _ : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, Real.sqrt (S7.hs M) = ‖M‖ := by
    intro M
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, S7.hs]
    norm_num
  rw [key, key, key]
  exact Matrix.frobenius_norm_mul A B

theorem trace_conj {V W A : Matrix (Fin n) (Fin n) ℂ} (h : W * V = 1) :
    trace (V * A * W) = trace A := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem phi_le (x : ℝ) :
    Real.exp (2 * x) + Real.exp (-(2 * x)) - 2 ≤ 4 * x ^ 2 * Real.exp (2 * |x|) := by
  have key : ∀ y : ℝ, 0 ≤ y →
      Real.exp (2 * y) + Real.exp (-(2 * y)) - 2 ≤ 4 * y ^ 2 * Real.exp (2 * y) := by
    intro y hy
    have e1 : Real.exp (2 * y) = Real.exp y * Real.exp y := by rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(2 * y)) = Real.exp (-y) * Real.exp (-y) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    have h1 := Real.add_one_le_exp (-(2 * y))
    have hpos := Real.exp_pos y
    have hu0 : 0 ≤ Real.exp y - Real.exp (-y) := by
      have := Real.exp_le_exp.mpr (show -y ≤ y by linarith); linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    rw [e2] at h2
    have h3 : Real.exp y * (Real.exp (-y) * Real.exp (-y)) = Real.exp (-y) := by
      rw [← mul_assoc, e3, one_mul]
    have hu : Real.exp y - Real.exp (-y) ≤ 2 * y * Real.exp y := by nlinarith
    calc Real.exp (2 * y) + Real.exp (-(2 * y)) - 2 = (Real.exp y - Real.exp (-y)) ^ 2 := by
          rw [e1, e2]; nlinarith [e3]
      _ ≤ (2 * y * Real.exp y) ^ 2 := pow_le_pow_left₀ hu0 hu 2
      _ = 4 * y ^ 2 * Real.exp (2 * y) := by rw [e1]; ring
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact key x hx
  · have := key (-x) (by linarith)
    rw [abs_of_nonpos hx]
    have e : -(2 * -x) = 2 * x := by ring
    rw [e] at this
    have e' : (-x) ^ 2 = x ^ 2 := by ring
    rw [e'] at this
    rw [show 2 * -x = -(2 * x) by ring] at this ⊢
    linarith

theorem exp_two_lt : Real.exp 2 < 7.5 := by
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_pos 1
  rw [h]; nlinarith

theorem log_bound (D : ℝ) (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ s a y : ℝ, 0 ≤ s → 0 ≤ a → 0 ≤ y →
    a ≤ 4 * s * Real.exp (2 * Real.sqrt s) → y ≤ D ^ 2 * a * (1 + Real.sqrt a) ^ (2 * m) →
    Real.log (1 + y) ≤ A * min s (Real.sqrt s) := by
  set A1 : ℝ := D ^ 2 * 49 ^ m * 30 with hA1d
  set B : ℝ := D ^ 2 * 9 ^ (m + 1) with hBd
  have hB : 0 ≤ B := by positivity
  set A2 : ℝ := Real.log (1 + B) + 4 * ((m : ℝ) + 1) with hA2d
  have hA1 : 0 ≤ A1 := by positivity
  have hlB : 0 ≤ Real.log (1 + B) := Real.log_nonneg (by linarith)
  have hA2 : 0 ≤ A2 := by positivity
  refine ⟨max A1 A2, le_max_of_le_left hA1, fun s a y hs ha hy haS hyA => ?_⟩
  have hσ0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hσs : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  have hsa0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hlog : Real.log (1 + y) ≤ y := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + y by linarith); linarith
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  rcases le_total s 1 with h1 | h1
  · have hσ1 : Real.sqrt s ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt h1
    have hmin : min s (Real.sqrt s) = s := min_eq_left (by nlinarith)
    have he : Real.exp (2 * Real.sqrt s) ≤ 7.5 :=
      (Real.exp_le_exp.mpr (by linarith)).trans exp_two_lt.le
    have ha30 : a ≤ 30 * s := by nlinarith
    have ha36 : a ≤ 36 := by linarith
    have hsq6 : Real.sqrt a ≤ 6 := by
      have := Real.sqrt_le_sqrt ha36
      rwa [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    have hp : (1 + Real.sqrt a) ^ (2 * m) ≤ 49 ^ m := by
      calc (1 + Real.sqrt a) ^ (2 * m) ≤ 7 ^ (2 * m) :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = 49 ^ m := by rw [pow_mul]; norm_num
    have hy2 : y ≤ A1 * s := by
      calc y ≤ D ^ 2 * a * (1 + Real.sqrt a) ^ (2 * m) := hyA
        _ ≤ D ^ 2 * (30 * s) * 49 ^ m := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left ha30 hD2) hp (by positivity) (by positivity)
        _ = A1 * s := by rw [hA1d]; ring
    rw [hmin]
    calc Real.log (1 + y) ≤ A1 * s := hlog.trans hy2
      _ ≤ max A1 A2 * s := mul_le_mul_of_nonneg_right (le_max_left _ _) hs
  · have hσ1 : 1 ≤ Real.sqrt s := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt h1
    have hmin : min s (Real.sqrt s) = Real.sqrt s := min_eq_right (by nlinarith)
    set σ := Real.sqrt s with hσ
    set E := Real.exp σ with hE
    have hE1 : 1 ≤ E := Real.one_le_exp hσ0
    have hσE : σ ≤ E := by have := Real.add_one_le_exp σ; linarith
    have he2 : Real.exp (2 * σ) = E * E := by rw [hE, ← Real.exp_add]; ring_nf
    have hsa1 : Real.sqrt a ≤ 2 * σ * E := by
      have h2 : a ≤ (2 * σ * E) ^ 2 := by rw [← hσs] at haS; rw [he2] at haS; nlinarith
      have := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq (by positivity)] at this
    have hsa2 : 1 + Real.sqrt a ≤ 3 * E ^ 2 := by nlinarith
    have hy2 : y ≤ B * Real.exp (4 * ((m : ℝ) + 1) * σ) := by
      have hexp : Real.exp (4 * ((m : ℝ) + 1) * σ) = E ^ (4 * (m + 1)) := by
        rw [hE, ← Real.exp_nat_mul]; push_cast; ring_nf
      calc y ≤ D ^ 2 * a * (1 + Real.sqrt a) ^ (2 * m) := hyA
        _ ≤ D ^ 2 * (1 + Real.sqrt a) ^ 2 * (1 + Real.sqrt a) ^ (2 * m) := by
            gcongr; nlinarith
        _ = D ^ 2 * (1 + Real.sqrt a) ^ (2 * (m + 1)) := by ring
        _ ≤ D ^ 2 * (3 * E ^ 2) ^ (2 * (m + 1)) := by gcongr
        _ = B * Real.exp (4 * ((m : ℝ) + 1) * σ) := by
            rw [hexp, hBd, mul_pow, ← pow_mul, pow_mul 3 2 (m + 1)]; ring_nf
    have hX1 : 1 ≤ Real.exp (4 * ((m : ℝ) + 1) * σ) := Real.one_le_exp (by positivity)
    have h3 : 1 + y ≤ (1 + B) * Real.exp (4 * ((m : ℝ) + 1) * σ) := by nlinarith
    have h4 : Real.log (1 + y) ≤ Real.log (1 + B) + 4 * ((m : ℝ) + 1) * σ := by
      calc Real.log (1 + y) ≤ Real.log ((1 + B) * Real.exp (4 * ((m : ℝ) + 1) * σ)) :=
            Real.log_le_log (by linarith) h3
        _ = _ := by rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
    rw [hmin]
    calc Real.log (1 + y) ≤ Real.log (1 + B) + 4 * ((m : ℝ) + 1) * σ := h4
      _ ≤ A2 * σ := by rw [hA2d]; nlinarith
      _ ≤ max A1 A2 * σ := mul_le_mul_of_nonneg_right (le_max_right _ _) hσ0

theorem herm_decomp {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) :
    ∃ (V : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ), star V * V = 1 ∧ V * star V = 1 ∧
      X = V * diagonal (fun i => (l i : ℂ)) * star V ∧
      NormedSpace.exp X = V * diagonal (fun i => (Real.exp (l i) : ℂ)) * star V := by
  have h1 := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  have h2 := Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  refine ⟨hX.eigenvectorUnitary, hX.eigenvalues, h1, h2, ?_, ?_⟩
  · conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  · conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
    have hinv : star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
        (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)⁻¹ :=
      (Matrix.inv_eq_left_inv h1).symm
    have hu : IsUnit (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) :=
      ⟨⟨_, _, h2, h1⟩, rfl⟩
    rw [hinv, Matrix.exp_conj _ _ hu, Matrix.exp_diagonal]
    congr 3
    funext i
    rw [Pi.coe_exp]
    simp [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

theorem hs_sub_one (g : Matrix (Fin n) (Fin n) ℂ) (ht : trace g = (n : ℂ)) :
    S7.hs (g - 1) = (trace (gᴴ * g)).re - n := by
  rw [hs_eq_re_trace]
  simp only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, Matrix.mul_one,
    Matrix.one_mul, trace_sub, trace_one, trace_conjTranspose, ht, Complex.sub_re]
  simp

open ReciprocityTheory.ChartRestriction.DS.Lap.Base.N in
open scoped Matrix.Norms.Operator in
theorem trace_exp_lie {k r : ℕ} {Y : Mat k r} (hY : Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r)) :
    trace (NormedSpace.exp Y) = ((2 * r + k + 1 : ℕ) : ℂ) := by
  rw [lieOf_Nset_eq] at hY
  have h0 := (mem_lieN.mp hY).1
  have h1 : NormedSpace.exp Y - 1 ∈ levF (levB k r) 0 := (isFilB (k := k) (r := r)).exp_shear.1 Y h0
  have hnil : IsNilpotent (NormedSpace.exp Y - 1) := by
    refine ⟨2 * r + 1, ?_⟩
    have := (isFilB (k := k) (r := r)).pow_mem h1 (2 * r)
    rw [(isFilB (k := k) (r := r)).bot] at this
    exact (Submodule.mem_bot ℝ).mp this
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have e : NormedSpace.exp Y = 1 + (NormedSpace.exp Y - 1) := by abel
  rw [e, trace_add, ht, trace_one]
  simp

theorem herm_of_inP {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : ReciprocityTheory.ChartRestriction.DS.inP ε X) : X.IsHermitian := by
  obtain ⟨hG, hP⟩ := h
  have h1 : Xᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε = X * ReciprocityTheory.ChartRestriction.DS.Jm ε := by
    rw [hP]; exact eq_neg_of_add_eq_zero_left hG
  have hJ := S7.Jm_mul_self ε
  show Xᴴ = X
  calc Xᴴ = Xᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * ReciprocityTheory.ChartRestriction.DS.Jm ε := by
        rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = X * ReciprocityTheory.ChartRestriction.DS.Jm ε * ReciprocityTheory.ChartRestriction.DS.Jm ε := by rw [h1]
    _ = X := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]

theorem eq_zero_of_noncompactPart_of_noncompactRank_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : ReciprocityTheory.ChartRestriction.DS.inP ε X) (hq : S7.q0 ε = 0) : X = 0 := by
  have hP := h.2
  have hc : ∃ b : Bool, ∀ a, ε a = b := by
    rcases Nat.min_eq_zero_iff.mp hq with hp | hp
    · refine ⟨false, fun a => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.DS.pOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hp
      simpa using hp (Finset.mem_univ a)
    · refine ⟨true, fun a => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.DS.qOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hp
      simpa using hp (Finset.mem_univ a)
  obtain ⟨b, hb⟩ := hc
  ext i j
  have := congrFun (congrFun hP i) j
  simp only [ReciprocityTheory.ChartRestriction.DS.Jm, mul_diagonal, diagonal_mul, Matrix.neg_apply, hb] at this
  cases b <;> simp at this
  · show X i j = 0
    linear_combination -this / 2
  · show X i j = 0
    linear_combination this / 2

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.LieExponentialMajorant
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.IsCompactUnitaryMat
section
noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding

open Formalism.QuantumDeterminants

variable {k r : ℕ}

theorem col_of_fix {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {c : Fin (2 * r + k + 1)}
    (h : s *ᵥ bvec c = bvec c) (i : Fin (2 * r + k + 1)) : s i c = if i = c then 1 else 0 := by
  have := congrFun h i
  simpa [bvec, Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem col_std {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ UWset k r (z0 k r))
    {c : Fin (2 * r + k + 1)} (hc : ¬ bl k r c) (i : Fin (2 * r + k + 1)) :
    s i c = if i = c then 1 else 0 := by
  obtain ⟨-, hf, hz⟩ := hs
  unfold bl at hc
  rcases lt_trichotomy c.val (r + k) with h1 | h1 | h1
  · have hcr : c.val < r := by omega
    have : c = eI k r ⟨c.val, hcr⟩ := by ext; simp [eI]
    rw [this]; exact col_of_fix (hf _).1 i
  · have : c = wI k r (Fin.last k) := by ext; simp [wI, h1]
    rw [this]; exact col_of_fix hz i
  · have hc2 := c.isLt
    have : c = esI k r ⟨2 * r + k - c.val, by omega⟩ := by ext; simp [esI]; omega
    rw [this]; exact col_of_fix (hf _).2 i

theorem key {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ UWset k r (z0 k r))
    {c : Fin (2 * r + k + 1)} (hc : ¬ bl k r c) (j : Fin (2 * r + k + 1)) :
    Hpk k r c j = ∑ b, Hpk k r c b * s b j := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs.1
  have e := congrFun (congrFun hU c) j
  rw [← e, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [Matrix.mul_apply]
  have hst : ∀ x : Fin (2 * r + k + 1), star (if x = c then (1 : ℂ) else 0) = if x = c then 1 else 0 :=
    fun x => by split_ifs <;> simp
  simp only [Matrix.conjTranspose_apply, col_std hs hc, hst, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem row_zero {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ UWset k r (z0 k r))
    {i j : Fin (2 * r + k + 1)} (hi : ¬ bl k r i) (hj : bl k r j) : s i j = 0 := by
  have hi' := hi
  unfold bl at hi'
  have hi2 := i.isLt

  rcases lt_trichotomy i.val (r + k) with h1 | h1 | h1
  · have hir : i.val < r := by omega
    set c : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩ with hcdef
    have hc : ¬ bl k r c := by simp only [bl, hcdef]; omega
    have e := key hs hc j
    rw [H_blcol hj, if_neg (by rintro rfl; exact hc hj)] at e
    rw [Finset.sum_eq_single i] at e
    · rw [H_hi (by simp only [hcdef]; omega), if_pos (by simp only [hcdef]; omega), one_mul] at e
      exact e.symm
    · intro b _ hb
      rw [H_hi (by simp only [hcdef]; omega), if_neg, zero_mul]
      intro h; apply hb; ext; simp only [hcdef] at h; omega
    · simp
  · have hc : ¬ bl k r i := hi
    have e := key hs hc j
    rw [H_blcol hj, if_neg (by rintro rfl; exact hc hj)] at e
    rw [Finset.sum_eq_single i] at e
    · rw [H_mid h1, if_pos rfl] at e
      have : s i j = -(-1 * s i j) := by ring
      rw [this, ← e, neg_zero]
    · intro b _ hb
      rw [H_mid h1, if_neg (Ne.symm hb), zero_mul]
    · simp
  · set c : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩ with hcdef
    have hc : ¬ bl k r c := by simp only [bl, hcdef]; omega
    have e := key hs hc j
    rw [H_blcol hj, if_neg (by rintro rfl; exact hc hj)] at e
    rw [Finset.sum_eq_single i] at e
    · rw [H_lo (by simp only [hcdef]; omega), if_pos (by simp only [hcdef]; omega), one_mul] at e
      exact e.symm
    · intro b _ hb
      rw [H_lo (by simp only [hcdef]; omega), if_neg, zero_mul]
      intro h; apply hb; ext; simp only [hcdef] at h; omega
    · simp

def blk (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun q q' => s (eB k r q) (eB k r q')

theorem blk_unitary {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UWset k r (z0 k r)) : blk s ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext q q'
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs.1
  have e := congrFun (congrFun hU (eB k r q)) (eB k r q')
  rw [H_blrow (bl_eB q), Matrix.mul_apply] at e
  rw [sumB _ (fun p hp => by rw [row_zero hs hp (bl_eB q'), mul_zero])] at e
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, H_blcol (bl_eB _), mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply, blk]
  rw [e]
  simp [eB_inj.eq_iff]

theorem eq_blockW {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UWset k r (z0 k r)) : s = Formalism.MainNotions.S.blockW k r (blk s) := by
  ext i j
  by_cases hj : bl k r j
  · by_cases hi : bl k r i
    · obtain ⟨qi, rfl⟩ := ex_eB hi
      obtain ⟨qj, rfl⟩ := ex_eB hj
      rw [bw_ee]; rfl
    · rw [bw_off _ hi hj, row_zero hs hi hj]
  · rw [bw_col _ _ hj, col_std hs hj]

theorem isCompact_unitary_mat :
    IsCompact (unitary (Matrix (Fin k) (Fin k) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin k => Set.pi Set.univ
      (fun _ : Fin k => Metric.closedBall (0 : ℂ) 1)) : Set (Matrix (Fin k) (Fin k) ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 1))
  have hC : IsClosed (unitary (Matrix (Fin k) (Fin k) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ)) := by
    have e : (unitary (Matrix (Fin k) (Fin k) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ)) =
        {U : Matrix (Fin k) (Fin k) ℂ | Uᴴ * U = 1} ∩ {U | U * Uᴴ = 1} := by
      ext U; simp [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
    rw [e]
    exact (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const)
  refine hK.of_isClosed_subset hC ?_
  intro U hU i _ j _
  simpa using entry_norm_bound_of_unitary (n := Fin k) (𝕜 := ℂ) hU i j

@[instance_reducible] def measUG (k : ℕ) : MeasurableSpace (unitary (Matrix (Fin k) (Fin k) ℂ)) := borel _

attribute [local instance] measUG

theorem borelUG : BorelSpace (unitary (Matrix (Fin k) (Fin k) ℂ)) := ⟨rfl⟩

attribute [local instance] borelUG

theorem compactUG : CompactSpace (unitary (Matrix (Fin k) (Fin k) ℂ)) :=
  isCompact_iff_compactSpace.mp isCompact_unitary_mat

attribute [local instance] compactUG

def FW (k r : ℕ) (u : unitary (Matrix (Fin k) (Fin k) ℂ)) : Mt k r :=
  fun i j => Formalism.MainNotions.S.blockW k r u.1 i j

theorem contFW : Continuous (FW k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [FW, Formalism.MainNotions.S.blockW]
  split_ifs
  all_goals first | exact continuous_subtype_val.matrix_elem _ _ | exact continuous_const

theorem measurable_lmulM' (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (lmulM (k := k) (r := r) s) := by
  have hc : Continuous (lmulM (k := k) (r := r) s) := by
    unfold lmulM
    exact continuous_const.matrix_mul continuous_id
  exact hc.measurable

theorem main (k r : ℕ) : ∃ μW : Measure (Mt k r),
    Formalism.MainNotions.S.IsHaarOn (UWset k r (z0 k r)) μW ∧ μW Set.univ = 1 := by
  haveI : Nonempty (unitary (Matrix (Fin k) (Fin k) ℂ)) := ⟨1⟩
  let ν : Measure (unitary (Matrix (Fin k) (Fin k) ℂ)) := Measure.haarMeasure ⊤
  have hν : ν Set.univ = 1 := by
    have := Measure.haarMeasure_self (G := unitary (Matrix (Fin k) (Fin k) ℂ)) (K₀ := ⊤)
    simpa [TopologicalSpace.PositiveCompacts.coe_top] using this
  have hFm : Measurable (FW k r) := contFW.measurable
  have huniv : ν.map (FW k r) Set.univ = 1 := by
    rw [Measure.map_apply hFm MeasurableSet.univ]; simpa using hν
  haveI : IsProbabilityMeasure (ν.map (FW k r)) := ⟨huniv⟩
  refine ⟨ν.map (FW k r), ⟨inferInstance, ?_, ?_, ?_⟩, huniv⟩
  · intro h; rw [h] at huniv; simp at huniv
  · have hsub : {x : Mt k r | Matrix.of x ∉ UWset k r (z0 k r)} ⊆ (Set.range (FW k r))ᶜ := by
      rintro x hx ⟨u, rfl⟩
      exact hx (mem_UW u.2)
    have hmeas : MeasurableSet (Set.range (FW k r))ᶜ :=
      (isCompact_range contFW).isClosed.measurableSet.compl
    refine le_antisymm ?_ bot_le
    calc _ ≤ ν.map (FW k r) (Set.range (FW k r))ᶜ := measure_mono hsub
      _ = 0 := by rw [Measure.map_apply hFm hmeas]; simp
  · intro s hs
    let u0 : unitary (Matrix (Fin k) (Fin k) ℂ) := ⟨blk s, blk_unitary hs⟩
    have hcomp : lmulM s ∘ FW k r = FW k r ∘ (fun u => u0 * u) := by
      funext u
      change (s * Formalism.MainNotions.S.blockW k r u.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
        (Formalism.MainNotions.S.blockW k r (blk s * u.1) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      rw [blockW_mul, ← eq_blockW hs]
    rw [Measure.map_map (measurable_lmulM' s) hFm, hcomp,
      ← Measure.map_map hFm (continuous_const_mul u0).measurable, map_mul_left_eq_self]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding
end
end

