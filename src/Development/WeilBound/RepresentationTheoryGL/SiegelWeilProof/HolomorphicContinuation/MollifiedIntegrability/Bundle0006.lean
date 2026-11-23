module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBFinal
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, herm, star_add, star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem cls_zero (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    cls s 0 p q R = fun y => Fr s p q R (herm y) := by
  funext y
  simp [cls, Fr, evUV, uM, vM]

theorem herm_spectral (y : E n) : ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ lam : Fin n → ℝ,
    herm y = k * Matrix.diagonal (fun i => (lam i : ℂ)) * kᴴ := by
  have hH := herm_isHermitian y
  refine ⟨hH.eigenvectorUnitary, hH.eigenvectorUnitary.2, hH.eigenvalues, ?_⟩
  conv_lhs => rw [hH.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

theorem conj_det (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (A : Mc n) : (k * A * kᴴ).det = A.det := by
  have h1 : k * kᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (k.det), mul_assoc, ← Matrix.det_mul, h1, Matrix.det_one, mul_one]

theorem one_sub_conj (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (c : ℂ) (A : Mc n) :
    (1 : Mc n) + c • (k * A * kᴴ) = k * (1 + c • A) * kᴴ := by
  have h1 : k * kᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, Matrix.mul_smul, Matrix.smul_mul]

theorem det_one_add_herm (y : E n) : ∃ lam : Fin n → ℝ, ∀ c : ℂ,
    ((1 : Mc n) + c • herm y).det = ∏ i, (1 + c * lam i) ∧ ((1 : Mc n) + herm y * herm y).det = ∏ i, (1 + (lam i : ℂ) ^ 2) := by
  obtain ⟨k, hk, lam, hy⟩ := herm_spectral y
  have h1 : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff'.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨lam, fun c => ⟨?_, ?_⟩⟩
  · rw [hy, one_sub_conj k hk, conj_det k hk]
    rw [show (1 : Mc n) + c • Matrix.diagonal (fun i => (lam i : ℂ)) = Matrix.diagonal (fun i => 1 + c * lam i) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h]]
    simp
  · have : herm y * herm y = k * (Matrix.diagonal (fun i => (lam i : ℂ)) * Matrix.diagonal (fun i => (lam i : ℂ))) * kᴴ := by
      rw [hy]
      calc k * diagonal (fun i => (lam i : ℂ)) * kᴴ * (k * diagonal (fun i => (lam i : ℂ)) * kᴴ)
          = k * diagonal (fun i => (lam i : ℂ)) * (kᴴ * k) * diagonal (fun i => (lam i : ℂ)) * kᴴ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, show (1 : Mc n) + k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ =
        (1 : Mc n) + (1 : ℂ) • (k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ) by simp,
      one_sub_conj k hk, conj_det k hk, Matrix.diagonal_mul_diagonal]
    rw [show (1 : Mc n) + (1 : ℂ) • diagonal (fun i => (lam i : ℂ) * lam i) = diagonal (fun i => 1 + (lam i : ℂ) ^ 2) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, sq]]
    simp

theorem dP_eq (y : E n) : ∃ lam : Fin n → ℝ, dP y = ∏ i, (1 + lam i ^ 2) ∧
    (((dP y : ℝ) : ℂ) = ((1 : Mc n) + herm y * herm y).det) ∧
    ∀ c : ℂ, ((1 : Mc n) + c • herm y).det = ∏ i, (1 + c * lam i) := by
  obtain ⟨lam, h⟩ := det_one_add_herm y
  have h2 := (h 0).2
  have hre : dP y = ∏ i, (1 + lam i ^ 2) := by
    simp only [dP, h2]
    rw [show (∏ i, (1 + (lam i : ℂ) ^ 2)) = ((∏ i, (1 + lam i ^ 2) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  refine ⟨lam, hre, ?_, fun c => (h c).1⟩
  rw [hre, h2]; push_cast; rfl

theorem dP_pos (y : E n) : 0 < dP y := by
  obtain ⟨lam, h, -⟩ := dP_eq y
  rw [h]; exact Finset.prod_pos fun i _ => by positivity

theorem herm_mem_Ugood (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : herm y ∈ Ugood s := by
  obtain ⟨lam, -, -, h⟩ := dP_eq y
  have key : ∀ c : ℂ, (c = 1 ∨ c = -1) → ((1 : Mc n) + (c * (Complex.I * s)) • herm y).det ≠ 0 := by
    intro c hc
    rw [h, Finset.prod_ne_zero_iff]
    intro i _ h0
    have h1 := congrArg Complex.re h0
    rcases hc with rfl | rfl <;> rcases hs with rfl | rfl <;> simp at h1
  refine ⟨isUnit_iff_ne_zero.2 ?_, isUnit_iff_ne_zero.2 ?_⟩
  · have := key (-1) (Or.inr rfl); rwa [neg_one_mul, neg_smul, ← sub_eq_add_neg] at this
  · have := key 1 (Or.inl rfl); rwa [one_mul] at this

theorem dP_of_spectral (y : E n) (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (lam : Fin n → ℝ)
    (hy : herm y = k * Matrix.diagonal (fun i => (lam i : ℂ)) * kᴴ) : dP y = ∏ i, (1 + lam i ^ 2) := by
  have h1 : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff'.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  have : herm y * herm y = k * (Matrix.diagonal (fun i => (lam i : ℂ)) * Matrix.diagonal (fun i => (lam i : ℂ))) * kᴴ := by
    rw [hy]
    calc k * diagonal (fun i => (lam i : ℂ)) * kᴴ * (k * diagonal (fun i => (lam i : ℂ)) * kᴴ)
        = k * diagonal (fun i => (lam i : ℂ)) * (kᴴ * k) * diagonal (fun i => (lam i : ℂ)) * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h2 : ((1 : Mc n) + herm y * herm y).det = ((∏ i, (1 + lam i ^ 2) : ℝ) : ℂ) := by
    rw [this, show (1 : Mc n) + k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ =
        (1 : Mc n) + (1 : ℂ) • (k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ) by simp,
      one_sub_conj k hk, conj_det k hk, Matrix.diagonal_mul_diagonal]
    rw [show (1 : Mc n) + (1 : ℂ) • diagonal (fun i => (lam i : ℂ) * lam i) = diagonal (fun i => 1 + (lam i : ℂ) ^ 2) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, sq]]
    simp
  simp only [dP, h2, Complex.ofReal_re]

theorem det_u_mul_det_v (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) :
    (uM s y).det * (vM s y).det = (((dP y : ℝ) : ℂ))⁻¹ := by
  obtain ⟨lam, -, hdP, -⟩ := dP_eq y
  have hg := herm_mem_Ugood s hs y
  have hprod : ((1 : Mc n) - (Complex.I * s) • herm y) * (1 + (Complex.I * s) • herm y) = 1 + herm y * herm y := by
    have hs2 : (Complex.I * s) * (Complex.I * s) = -1 := by
      rcases hs with rfl | rfl <;> simp [← sq, Complex.I_sq] <;> ring_nf <;> simp [Complex.I_sq]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs2]
    simp [neg_smul]; abel
  have h1 := Matrix.det_nonsing_inv_mul_det (A := (1 : Mc n) - (Complex.I * s) • herm y) hg.1
  have h2 := Matrix.det_nonsing_inv_mul_det (A := (1 : Mc n) + (Complex.I * s) • herm y) hg.2
  rw [hdP, ← hprod, Matrix.det_mul]
  simp only [uM, vM]
  apply eq_inv_of_mul_eq_one_left
  calc ((1 - (Complex.I * s) • herm y)⁻¹).det * ((1 + (Complex.I * s) • herm y)⁻¹).det *
        ((1 - (Complex.I * s) • herm y).det * (1 + (Complex.I * s) • herm y).det)
      = (((1 - (Complex.I * s) • herm y)⁻¹).det * (1 - (Complex.I * s) • herm y).det) *
        (((1 + (Complex.I * s) • herm y)⁻¹).det * (1 + (Complex.I * s) • herm y).det) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

theorem cls_nat (s : ℂ) (hs : s = 1 ∨ s = -1) (i p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    cls s (i : ℂ) p q R = cls s 0 (p + i) (q + i) R := by
  funext y
  have h := det_u_mul_det_v s hs y
  simp only [cls, neg_zero, Complex.cpow_zero, one_mul, Complex.cpow_neg, Complex.cpow_natCast, pow_add]
  rw [show ((((dP y : ℝ) : ℂ)) ^ i)⁻¹ = ((uM s y).det * (vM s y).det) ^ i by rw [h, inv_pow]]
  ring

theorem prod_flatMap_real {α : Type} (l : List α) (f : α → List ℝ) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

theorem prod_blocks (N : ℕ) (g : Fin N → Fin n → ℝ) :
    ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => g j k).prod = ∏ j, ∏ k, g j k := by
  rw [prod_flatMap_real, Fin.prod_univ_def]
  congr 1

theorem length_blocks {α : Type} (N : ℕ) (g : Fin N → Fin n → α) :
    ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => g j k).length = N * n := by
  simp

theorem prod_sqrt_perm (σ : Equiv.Perm (Fin n)) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∏ k, Real.sqrt (w (σ k) * w k) = ∏ k, w k := by
  have h1 : ∀ k, Real.sqrt (w (σ k) * w k) = Real.sqrt (w (σ k)) * Real.sqrt (w k) := fun k =>
    Real.sqrt_mul (hw _).le _
  simp_rw [h1, Finset.prod_mul_distrib, Equiv.prod_comp σ (fun k => Real.sqrt (w k)), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => Real.mul_self_sqrt (hw k).le

theorem conj_mem_Ugood (s : ℂ) (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (b : Mc n) (hb : b ∈ Ugood s) :
    k * b * kᴴ ∈ Ugood s := by
  refine ⟨?_, ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul, one_sub_conj k hk, conj_det k hk, neg_smul, ← sub_eq_add_neg]; exact hb.1
  · rw [one_sub_conj k hk, conj_det k hk]; exact hb.2

def conjL (k : Mc n) : Mc n →ₗ[ℂ] Mc n := (LinearMap.mulLeft ℂ k).comp (LinearMap.mulRight ℂ kᴴ)

theorem conjL_apply (k c : Mc n) : conjL k c = k * c * kᴴ := by
  simp [conjL, Matrix.mul_assoc]

theorem contDiff_conj (k : Mc n) : ContDiff ℂ (⊤ : ℕ∞) (fun c : Mc n => k * c * kᴴ) := by
  have : (fun c : Mc n => k * c * kᴴ) = (LinearMap.toContinuousLinearMap (conjL k) : Mc n → Mc n) := by
    funext c; simp [conjL_apply]
  rw [this]; exact ContinuousLinearMap.contDiff _

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GWickB
section
noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, sgn ε a * star (x a i) * x a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, map_sub, map_sum, map_mul, evX, eval_X, if_true, Bool.false_eq_true, if_false]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : ε a <;> simp [sgn, h]

theorem gramX_herm (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : (gramX ε x)ᴴ = gramX ε x := by
  ext i j
  simp only [conjTranspose_apply, gramX_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : star (sgn ε a) = sgn ε a := by unfold sgn; split_ifs <;> simp
  rw [this]; ring

theorem trace_im_zero (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : (b * gramX ε x).trace.im = 0 := by
  have h : star (b * gramX ε x).trace = (b * gramX ε x).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, gramX_herm, hb.eq, trace_mul_comm]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem norm_exp_tr (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : ‖Complex.exp (Complex.I * t * (b * gramX ε x).trace)‖ = 1 := by
  rw [Complex.norm_exp]
  have h := trace_im_zero ε b hb x
  simp [Complex.mul_re, h]

def phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) : PX m n :=
  -∑ a, ∑ k, ∑ j, C ((Amat ε c t b a) k j) * X (a, k, true) * X (a, j, false)

theorem evX_phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (phiP ε c t b) x = -∑ a, ∑ k, ∑ j, (Amat ε c t b a) k j * star (x a k) * x a j := by
  simp [phiP, evX]

theorem exp_phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) = Complex.exp (evX (phiP ε c t b) x) := by
  rw [gs, ← Complex.exp_add, evX_phiP]
  congr 1
  have h1 : (((c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ)) : ℂ) = ∑ a, ∑ k, (c : ℂ) * (star (x a k) * x a k) := by
    push_cast
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    have hz : (starRingEnd ℂ) (x a k) * x a k = ((‖x a k‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.star_def, hz]; push_cast; ring
  have h2 : (b * gramX ε x).trace = ∑ a, ∑ k, ∑ j, sgn ε a * b j k * star (x a k) * x a j := by
    simp only [trace, diag, Matrix.mul_apply, gramX_apply, Finset.mul_sum]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : ∀ a k, ∑ j, (Amat ε c t b a) k j * star (x a k) * x a j =
      (c : ℂ) * (star (x a k) * x a k) - ∑ j, Complex.I * t * (sgn ε a * b j k * star (x a k) * x a j) := by
    intro a k
    simp only [Amat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, smul_eq_mul,
      sub_mul, Finset.sum_sub_distrib]
    congr 1
    · simp [Finset.sum_ite_eq, mul_assoc]
    · refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [h1, h2]
  simp only [h3, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

end PositivityTheory.Rg.Sw.WR.G
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.MollId
section
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ}

theorem norm_cexp_It (t r : ℝ) : ‖Complex.exp (Complex.I * t * r)‖ = 1 := by
  have : Complex.I * (t : ℂ) * (r : ℂ) = ((t * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_cexp_neg_It (t r : ℝ) : ‖Complex.exp (-(Complex.I * t * r))‖ = 1 := by
  have : -(Complex.I * (t : ℂ) * (r : ℂ)) = ((-(t * r) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem ip_sub_right (y u w : E n) : ip y (u - w) = ip y u - ip y w := by
  simp only [ip, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem ip_comm (y y' : E n) : ip y y' = ip y' y := by
  simp only [ip, mul_comm]

theorem continuous_ip : Continuous (fun p : E n × E n => ip p.1 p.2) := by
  unfold ip
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => by fun_prop

theorem continuous_gK : Continuous (gK (n := n)) := by
  unfold gK
  exact continuous_finsetProd _ fun a _ => continuous_finsetProd _ fun b _ => by fun_prop

def gam (ε : ℝ) (y : E n) : ℂ := Complex.exp (-((ε * ip y y : ℝ) : ℂ))

theorem continuous_gam (ε : ℝ) : Continuous (gam (n := n) ε) := by
  unfold gam
  have h : Continuous (fun y : E n => ip y y) := continuous_ip.comp (continuous_id.prodMk continuous_id)
  fun_prop

def kr (ε t : ℝ) (u : E n) : ℂ := ∫ y, gam ε y * Complex.exp (Complex.I * t * ip y u)

theorem norm_kr_le (ε t : ℝ) (hε : 0 < ε) (u : E n) : ‖kr ε t u‖ ≤ ∫ y, ‖gam (n := n) ε y‖ := by
  unfold kr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext y
  rw [norm_mul, norm_cexp_It, mul_one]

theorem continuous_kr (ε t : ℝ) (hε : 0 < ε) : Continuous (kr (n := n) ε t) := by
  unfold kr
  refine continuous_of_dominated (bound := fun y => ‖gam (n := n) ε y‖) ?_ ?_
    (integrable_gauss ε hε).norm ?_
  · intro u
    exact ((continuous_gam ε).mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ip.comp (continuous_id.prodMk continuous_const)))))).aestronglyMeasurable
  · intro u; refine Eventually.of_forall fun y => ?_
    rw [norm_mul, norm_cexp_It, mul_one]
  · refine Eventually.of_forall fun y => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ip.comp (continuous_const.prodMk continuous_id)))))

theorem finrank_E : Module.finrank ℝ (E n) = n ^ 2 := by
  simp [E, Module.finrank_pi_fintype, sq]

def mM (ψ : E n → ℂ) (l : ℝ) (w : E n) : ℂ := ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)

theorem norm_mM_le (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℝ) (w : E n) :
    ‖mM ψ l w‖ ≤ B := by
  unfold mM
  calc ‖∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)‖ ≤ ∫ v, B * gK (n := n) v := by
        refine norm_integral_le_of_norm_le (integrable_gK.const_mul B) (Eventually.of_forall fun v => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
        exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
    _ = B := by rw [integral_const_mul, integral_gK, mul_one]

theorem continuous_mM (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℝ) :
    Continuous (mM ψ l) := by
  unfold mM
  refine continuous_of_dominated (bound := fun v => B * gK (n := n) v) ?_ ?_ (integrable_gK.const_mul B) ?_
  · intro w
    exact ((by fun_prop : Continuous fun v : E n => ψ (w - l⁻¹ • v)).mul
      (Complex.continuous_ofReal.comp continuous_gK)).aestronglyMeasurable
  · intro w; refine Eventually.of_forall fun v => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
    exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
  · exact Eventually.of_forall fun v => (by fun_prop : Continuous fun w : E n => ψ (w - l⁻¹ • v) * (gK v : ℂ))

theorem tendsto_mM (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℕ → ℝ)
    (hl : Tendsto (fun k => (l k)⁻¹) atTop (𝓝 0)) (w : E n) :
    Tendsto (fun k => mM ψ (l k) w) atTop (𝓝 (ψ w)) := by
  have hlim : ψ w = ∫ v, ψ (w - (0 : ℝ) • v) * (gK (n := n) v : ℂ) := by
    simp only [zero_smul, sub_zero]
    rw [integral_const_mul, integral_complex_ofReal, integral_gK, Complex.ofReal_one, mul_one]
  rw [hlim]
  unfold mM
  refine tendsto_integral_of_dominated_convergence (fun v => B * gK (n := n) v) ?_ (integrable_gK.const_mul B) ?_ ?_
  · intro k
    exact ((by fun_prop : Continuous fun v : E n => ψ (w - (l k)⁻¹ • v)).mul
      (Complex.continuous_ofReal.comp continuous_gK)).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun v => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
    exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
  · refine Eventually.of_forall fun v => ?_
    refine Tendsto.mul ?_ tendsto_const_nhds
    exact (hψ.tendsto _).comp (tendsto_const_nhds.sub (hl.smul_const v))

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end

