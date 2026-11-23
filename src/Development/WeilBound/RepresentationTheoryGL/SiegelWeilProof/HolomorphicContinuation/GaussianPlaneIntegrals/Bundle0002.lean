module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.IntegralHkDiag
section
noncomputable section

open MeasureTheory Complex Module
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof

def e1 (z : ℂ) : ℂ := Complex.exp (((-(‖z‖ ^ 2)) : ℝ) : ℂ)

def hk (k l : ℕ) (z : ℂ) : ℂ := z ^ k * star z ^ l * e1 z

theorem continuous_hk (k l : ℕ) : Continuous (hk k l) := by
  unfold hk e1
  fun_prop

theorem norm_hk (k l : ℕ) (z : ℂ) : ‖hk k l z‖ = ‖z‖ ^ (k + l) * Real.exp (-(‖z‖ ^ 2)) := by
  simp only [hk, e1, norm_mul, norm_pow, norm_star, Complex.norm_exp_ofReal, pow_add]

theorem pow_exp_le (n : ℕ) : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    t ^ n * Real.exp (-(t ^ 2)) ≤ C * (1 + t) ^ (-(3 : ℝ)) := by
  refine ⟨((n + 3).factorial : ℝ) * Real.exp 2, fun t ht => ?_⟩
  have h1 : 0 < 1 + t := by linarith
  have hr : (1 + t) ^ (-(3 : ℝ)) = ((1 + t) ^ 3)⁻¹ := by
    rw [Real.rpow_neg h1.le]
    norm_cast
  rw [hr, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hA : t ^ n ≤ (1 + t) ^ n := pow_le_pow_left₀ ht (by linarith) n
  have hB : (1 + t) ^ (n + 3) ≤ ((n + 3).factorial : ℝ) * Real.exp (1 + t) := by
    have h := Real.pow_div_factorial_le_exp (1 + t) h1.le (n + 3)
    rwa [div_le_iff₀ (by positivity), mul_comm] at h
  have hC : Real.exp (1 + t) * Real.exp (-(t ^ 2)) ≤ Real.exp 2 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (t - 1 / 2)])
  calc t ^ n * Real.exp (-(t ^ 2)) * (1 + t) ^ 3
      ≤ (1 + t) ^ n * Real.exp (-(t ^ 2)) * (1 + t) ^ 3 := by gcongr
    _ = (1 + t) ^ (n + 3) * Real.exp (-(t ^ 2)) := by ring
    _ ≤ ((n + 3).factorial : ℝ) * Real.exp (1 + t) * Real.exp (-(t ^ 2)) := by gcongr
    _ ≤ ((n + 3).factorial : ℝ) * Real.exp 2 := by
      rw [mul_assoc]
      gcongr

theorem integrable_hk (k l : ℕ) : Integrable (hk k l) := by
  obtain ⟨C, hC⟩ := pow_exp_le (k + l)
  have hi : Integrable (fun z : ℂ => (1 + ‖z‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by norm_num [finrank_real_complex])
  refine (hi.const_mul C).mono' (continuous_hk k l).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [norm_hk]
  exact hC _ (norm_nonneg _)

theorem integral_hk_ne (k l : ℕ) (h : k ≠ l) : ∫ z, hk k l z = 0 := by
  have hkl : ((k : ℂ) - l) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
  set θ : ℝ := Real.pi / ((k : ℝ) - l) with hθ
  have hfac : Complex.exp (θ * I) ^ k * star (Complex.exp (θ * I)) ^ l = -1 := by
    have hs : star (Complex.exp (θ * I)) = Complex.exp (-(θ * I)) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      simp
    rw [hs, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have h2 : (θ : ℂ) * ((k : ℂ) - l) = Real.pi := by
      rw [hθ]
      push_cast
      field_simp
    have h3 : (k : ℂ) * (θ * I) + l * (-(θ * I)) = Real.pi * I := by
      linear_combination I * h2
    rw [h3, Complex.exp_pi_mul_I]
  have hrot : ∀ z : ℂ, hk k l (Complex.exp (θ * I) * z) = -hk k l z := by
    intro z
    have he : e1 (Complex.exp (θ * I) * z) = e1 z := by
      simp only [e1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    simp only [hk]
    rw [he, star_mul', mul_pow, mul_pow]
    calc Complex.exp (θ * I) ^ k * z ^ k * (star (Complex.exp (θ * I)) ^ l * star z ^ l) * e1 z
        = (Complex.exp (θ * I) ^ k * star (Complex.exp (θ * I)) ^ l) * (z ^ k * star z ^ l * e1 z) := by ring
      _ = -(z ^ k * star z ^ l * e1 z) := by rw [hfac]; ring
  have key := (rotation (Circle.exp θ)).measurePreserving.integral_comp
    (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding (hk k l)
  simp only [LinearIsometryEquiv.coe_toHomeomorph, rotation_apply, Circle.coe_exp, hrot, integral_neg] at key
  linear_combination (-1 / 2 : ℂ) * key

def jr (k : ℕ) : ℝ := ∫ z : ℂ, (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2))

theorem hk_diag (k : ℕ) (z : ℂ) : hk k k z = (((‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) : ℝ) : ℂ) := by
  simp only [hk, e1]
  rw [← mul_pow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem integral_hk_diag (k : ℕ) : ∫ z, hk k k z = (jr k : ℂ) := by
  simp_rw [hk_diag]
  exact integral_ofReal

theorem jr_pos (k : ℕ) : 0 < jr k := by
  have hint : Integrable (fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2))) := by
    refine (integrable_hk k k).norm.congr (ae_of_all _ fun z => ?_)
    simp only [norm_hk]
    ring
  have hnn : 0 ≤ fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) := fun z => by positivity
  unfold jr
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hc : Continuous fun z : ℂ => (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2)) := by fun_prop
  exact hc.isOpen_support.measure_pos volume ⟨1, by simp⟩

end PositivityTheory.Rg.Sw.FFTSteps.PosProof
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.PowSpan
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps

namespace PowSpanB

variable {m n : ℕ} (ε : Fin m → Bool)

def lf (b : Matrix (Fin n) (Fin n) ℂ) : PX m n := ∑ i, ∑ j, b i j • (Qp ε j i : PX m n)

theorem lf_eq (b : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) = lf ε b := by
  simp only [lf, C_mul']

theorem lf_add (b c : Matrix (Fin n) (Fin n) ℂ) : lf ε (b + c) = lf ε b + lf ε c := by
  simp only [lf, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem lf_smul (z : ℂ) (b : Matrix (Fin n) (Fin n) ℂ) : lf ε (z • b) = z • lf ε b := by
  simp only [lf, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem lf_single (a b : Fin n) : lf ε (Matrix.single b a (1 : ℂ)) = (Qp ε a b : PX m n) := by
  simp [lf, Matrix.single_apply, ite_smul, ite_and]

def W : Set (PX m n) := {w | ∃ h : Matrix (Fin n) (Fin n) ℂ, h.IsHermitian ∧ w = lf ε h}

def S : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {R | ∃ (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ), b.IsHermitian ∧
    R = (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k}

theorem pow_mem {w : PX m n} (hw : w ∈ W ε) (k : ℕ) : w ^ k ∈ S ε := by
  obtain ⟨h, hh, rfl⟩ := hw
  exact Submodule.subset_span ⟨h, k, hh, by rw [lf_eq]⟩

theorem zero_mem_W : (0 : PX m n) ∈ W ε :=
  ⟨0, Matrix.isHermitian_zero, by simp [lf]⟩

theorem natCast_smul_add_mem_W {w v : PX m n} (hw : w ∈ W ε) (hv : v ∈ W ε) (t : ℕ) : (t : ℂ) • v + w ∈ W ε := by
  obtain ⟨h1, hh1, rfl⟩ := hw
  obtain ⟨h2, hh2, rfl⟩ := hv
  refine ⟨(t : ℂ) • h2 + h1, ?_, by rw [lf_add, lf_smul]⟩
  show Matrix.conjTranspose ((t : ℂ) • h2 + h1) = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hh2.eq, hh1.eq]
  simp

theorem herm_decomp (b : Matrix (Fin n) (Fin n) ℂ) : ∃ H1 H2 : Matrix (Fin n) (Fin n) ℂ,
    H1.IsHermitian ∧ H2.IsHermitian ∧ b = H1 + Complex.I • H2 := by
  refine ⟨(1 / 2 : ℂ) • (b + Matrix.conjTranspose b), (-Complex.I / 2) • (b - Matrix.conjTranspose b), ?_, ?_, ?_⟩
  · show Matrix.conjTranspose ((1 / 2 : ℂ) • (b + Matrix.conjTranspose b)) = _
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  · show Matrix.conjTranspose ((-Complex.I / 2) • (b - Matrix.conjTranspose b)) = _
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring
  · ext i j
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring_nf
    rw [Complex.I_sq]
    ring

private theorem coeff_mem_of_forall_natCast_poly_sum_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Submodule ℂ M) (N : ℕ)
    (c : ℕ → M) (h : ∀ t : ℕ, ∑ j ∈ Finset.range (N + 1), ((t : ℂ) ^ j) • c j ∈ T)
    (k : ℕ) (hk : k < N + 1) : c k ∈ T := by
  let V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Matrix.vandermonde (fun t : Fin (N + 1) => ((t : ℕ) : ℂ))
  have hV : IsUnit V.det := by
    refine isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ?_)
    intro a b hab
    exact Fin.ext (Nat.cast_injective hab)
  have key : ∑ t : Fin (N + 1), (V⁻¹ ⟨k, hk⟩ t) • (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j) = c k := by
    have e : ∀ t : Fin (N + 1), (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j)
        = ∑ j : Fin (N + 1), V t j • c j := by
      intro t
      rw [← Fin.sum_univ_eq_sum_range (fun j => (((t : ℕ) : ℂ) ^ j) • c j)]
      simp [V, Matrix.vandermonde_apply]
    simp_rw [e, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have hm : ∀ j : Fin (N + 1), ∑ t : Fin (N + 1), V⁻¹ ⟨k, hk⟩ t * V t j = (V⁻¹ * V) ⟨k, hk⟩ j := by
      intro j
      rw [Matrix.mul_apply]
    simp_rw [hm, Matrix.nonsing_inv_mul _ hV, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    simp
  rw [← key]
  exact Submodule.sum_mem _ (fun t _ => T.smul_mem _ (h t))

theorem core : ∀ l : List (PX m n), (∀ v ∈ l, v ∈ W ε) → ∀ w ∈ W ε, ∀ r : ℕ, l.prod * w ^ r ∈ S ε := by
  intro l
  induction l with
  | nil =>
    intro _ w hw r
    simpa using pow_mem ε hw r
  | cons v l ih =>
    intro hl w hw r
    have hv : v ∈ W ε := hl v (by simp)
    have ih' := ih (fun u hu => hl u (by simp [hu]))
    have h1 : ∀ t : ℕ, ∑ j ∈ Finset.range (r + 1 + 1), ((t : ℂ) ^ j) •
        (l.prod * (v ^ j * w ^ (r + 1 - j) * (((r + 1).choose j : ℕ) : PX m n))) ∈ S ε := by
      intro t
      have := ih' _ (natCast_smul_add_mem_W ε hw hv t) (r + 1)
      convert this using 1
      rw [add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_pow, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
    have h2 := coeff_mem_of_forall_natCast_poly_sum_mem (S ε) (r + 1) _ h1 1 (by omega)
    have e : (v :: l).prod * w ^ r = ((r + 1 : ℕ) : ℂ)⁻¹ •
        (l.prod * (v ^ 1 * w ^ (r + 1 - 1) * (((r + 1).choose 1 : ℕ) : PX m n))) := by
      rw [Nat.choose_one_right, pow_one, Nat.add_sub_cancel, List.prod_cons]
      rw [show (((r + 1 : ℕ)) : PX m n) = ((r + 1 : ℕ) : ℂ) • (1 : PX m n) by
        rw [Nat.cast_smul_eq_nsmul, nsmul_one]]
      rw [mul_smul_comm, mul_smul_comm, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)), one_smul]
      ring
    rw [e]
    exact (S ε).smul_mem _ h2

private theorem list_prod_mul_span_prod_mem_S : ∀ l : List (PX m n), (∀ x ∈ l, x ∈ Submodule.span ℂ (W ε)) →
    ∀ q : List (PX m n), (∀ v ∈ q, v ∈ W ε) → q.prod * l.prod ∈ S ε := by
  intro l
  induction l with
  | nil =>
    intro _ q hq
    simpa using core ε q hq 0 (zero_mem_W ε) 0
  | cons x l ih =>
    intro hl q hq
    have hx : x ∈ Submodule.span ℂ (W ε) := hl x (by simp)
    have hl' : ∀ y ∈ l, y ∈ Submodule.span ℂ (W ε) := fun y hy => hl y (by simp [hy])
    clear hl
    rw [List.prod_cons]
    induction hx using Submodule.span_induction with
    | mem y hy =>
      have := ih hl' (y :: q) (by
        intro v hv
        rcases List.mem_cons.mp hv with h | h
        · exact h ▸ hy
        · exact hq v h)
      rw [List.prod_cons] at this
      rw [← mul_assoc, mul_comm q.prod y]
      exact this
    | zero => simp
    | add a b _ _ ha hb =>
      rw [add_mul, mul_add]
      exact add_mem ha hb
    | smul z a _ ha =>
      rw [smul_mul_assoc, mul_smul_comm]
      exact (S ε).smul_mem z ha

theorem span_eq :
    (Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))).toSubmodule = S ε := by
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.mpr ?_
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    have := list_prod_mul_span_prod_mem_S ε l (by
      intro y hy
      obtain ⟨⟨a, b⟩, rfl⟩ := hl y hy
      obtain ⟨H1, H2, h1, h2, hb⟩ := herm_decomp (Matrix.single b a (1 : ℂ))
      have e : (Qp ε a b : PX m n) = lf ε H1 + Complex.I • lf ε H2 := by
        rw [← lf_single, hb, lf_add, lf_smul]
      show (Qp ε a b : PX m n) ∈ _
      rw [e]
      exact add_mem (Submodule.subset_span ⟨H1, h1, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨H2, h2, rfl⟩))) [] (by simp)
    simpa using this
  · refine Submodule.span_le.mpr ?_
    rintro R ⟨b, k, _, rfl⟩
    show _ ∈ Algebra.adjoin ℂ _
    refine Subalgebra.pow_mem _ (Subalgebra.sum_mem _ (fun i _ => Subalgebra.sum_mem _ (fun j _ => ?_))) k
    refine Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin ⟨(j, i), rfl⟩)
    rw [← MvPolynomial.algebraMap_eq]
    exact Subalgebra.algebraMap_mem _ _

end PowSpanB

theorem powSpan : PowSpan := fun _ _ ε => PowSpanB.span_eq ε

end PositivityTheory.Rg.Sw.FFTSteps
end
end

