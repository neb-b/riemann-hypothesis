module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0455
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivZeroEqLaguerreDerivativePolynomialV
section
set_option autoImplicit false

noncomputable section

open Filter Topology

namespace GlobalTheory.HilbFam.LagDeriv

set_option autoImplicit false in
open Filter Topology in
private lemma hasDerivAt_inv_pow_mul_exp_div_one_add_mul (c y : ℂ) (j : ℕ) {z : ℂ} (hz : 1 + z * c ≠ 0) :
    HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ j * Complex.exp (y * w / (1 + w * c)))
      (-(j * c) * ((1 + z * c)⁻¹ ^ (j + 1) * Complex.exp (y * z / (1 + z * c))) +
        y * ((1 + z * c)⁻¹ ^ (j + 2) * Complex.exp (y * z / (1 + z * c)))) z := by
  have hu : HasDerivAt (fun w : ℂ ↦ 1 + w * c) c z := by
    simpa using ((hasDerivAt_id z).mul_const c).const_add 1
  have hinv : HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹) (-c / (1 + z * c) ^ 2) z := hu.inv hz
  have hpow : HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ j)
      (j * (1 + z * c)⁻¹ ^ (j - 1) * (-c / (1 + z * c) ^ 2)) z := hinv.pow j
  have hq : HasDerivAt (fun w : ℂ ↦ y * w / (1 + w * c)) (y / (1 + z * c) ^ 2) z := by
    refine (((hasDerivAt_id z).const_mul y).div hu hz).congr_deriv ?_
    simp only [id, mul_one]
    field_simp
    ring
  refine (hpow.mul hq.cexp).congr_deriv ?_
  rcases j with _ | j
  · simp [div_eq_mul_inv]
    ring
  · simp only [Nat.cast_succ, Nat.add_sub_cancel, inv_pow]
    field_simp
    ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_eq_zero_of_lt (k n m : ℕ) (hm : n < m) :
    _root_.GlobalTheory.HilbFam.rco k n m = 0 := by
  unfold _root_.GlobalTheory.HilbFam.rco
  simp [Nat.choose_eq_zero_of_lt hm]

set_option autoImplicit false in
open Filter Topology in
private lemma ascFactorial_succ_eq_mul_succ_ascFactorial (a e : ℕ) :
    a.ascFactorial (e + 1) = a * (a + 1).ascFactorial e := by
  induction e with
  | zero => simp [Nat.ascFactorial_succ]
  | succ e ih =>
    rw [Nat.ascFactorial_succ, ih, Nat.ascFactorial_succ]
    ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_succ_succ (k n m : ℕ) (hm : m ≤ n) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) (m + 1) : ℤ) =
      -((k + n + m + 1 : ℕ) : ℤ) * _root_.GlobalTheory.HilbFam.rco k n (m + 1) +
        _root_.GlobalTheory.HilbFam.rco k n m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  unfold _root_.GlobalTheory.HilbFam.rco
  rcases d with _ | e
  · simp
  · have h1 : m + (e + 1) + 1 - (m + 1) = e + 1 := by omega
    have h2 : m + (e + 1) - (m + 1) = e := by omega
    have h3 : m + (e + 1) - m = e + 1 := by omega
    rw [h1, h2, h3]
    have hc := Nat.choose_succ_right_eq (m + (e + 1)) m
    have hc' : m + (e + 1) - m = e + 1 := by omega
    rw [hc'] at hc
    have hs : (m + (e + 1) + 1).choose (m + 1) = (m + (e + 1)).choose m + (m + (e + 1)).choose (m + 1) :=
      Nat.choose_succ_succ' _ _
    have ha1 : (k + (m + 1)).ascFactorial (e + 1) = (k + (m + 1) + e) * (k + (m + 1)).ascFactorial e :=
      Nat.ascFactorial_succ
    have ha2 := ascFactorial_succ_eq_mul_succ_ascFactorial (k + m) e
    rw [hs, ha1, ha2]
    have hkm : k + m + 1 = k + (m + 1) := by omega
    rw [hkm]
    push_cast
    have hcz : ((m + (e + 1)).choose (m + 1) : ℤ) * (m + 1) = ((m + (e + 1)).choose m : ℤ) * (e + 1) := by
      exact_mod_cast hc
    rw [pow_succ]
    linear_combination ((-1 : ℤ) ^ e * ((k + (m + 1)).ascFactorial e : ℤ)) * hcz

set_option autoImplicit false in
open Filter Topology in
private lemma rco_mul_pow_mul_pow_succ_succ (k n m : ℕ) (hm : m ≤ n) (c y : ℂ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) (m + 1) : ℂ) * c ^ (n + 1 - (m + 1)) * y ^ (m + 1) =
      -(((k + n + (m + 1) : ℕ) : ℂ) * c) *
          ((_root_.GlobalTheory.HilbFam.rco k n (m + 1) : ℂ) * c ^ (n - (m + 1)) * y ^ (m + 1)) +
        y * ((_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m) := by
  have hZ := congrArg (Int.cast : ℤ → ℂ) (rco_succ_succ k n m hm)
  push_cast at hZ
  rw [hZ]
  rcases hm.lt_or_eq with hlt | rfl
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have e1 : m + t + 1 + 1 - (m + 1) = t + 1 := by omega
    have e2 : m + t + 1 - (m + 1) = t := by omega
    have e3 : m + t + 1 - m = t + 1 := by omega
    rw [e1, e2, e3]
    push_cast
    ring
  · rw [rco_eq_zero_of_lt k m (m + 1) (Nat.lt_succ_self m)]
    simp only [Nat.sub_self, pow_zero]
    push_cast
    ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_succ_zero (k n : ℕ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) 0 : ℤ) =
      -((k + n : ℕ) : ℤ) * _root_.GlobalTheory.HilbFam.rco k n 0 := by
  unfold _root_.GlobalTheory.HilbFam.rco
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, add_zero, Nat.ascFactorial_succ]
  push_cast
  ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_mul_pow_mul_pow_succ_zero (k n : ℕ) (c y : ℂ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) 0 : ℂ) * c ^ (n + 1 - 0) * y ^ 0 =
      -(((k + n + 0 : ℕ) : ℂ) * c) *
        ((_root_.GlobalTheory.HilbFam.rco k n 0 : ℂ) * c ^ (n - 0) * y ^ 0) := by
  have hZ := congrArg (Int.cast : ℤ → ℂ) (rco_succ_zero k n)
  push_cast at hZ
  rw [hZ]
  simp only [Nat.sub_zero, pow_zero, add_zero]
  push_cast
  ring

set_option autoImplicit false in
open Filter Topology in
private lemma iteratedDeriv_inv_pow_mul_exp_eq_sum_rco (c y : ℂ) (n : ℕ) :
    ∀ k : ℕ, ∀ z : ℂ, 1 + z * c ≠ 0 →
      iteratedDeriv n (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) z =
        ∑ m ∈ Finset.range (n + 1), (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) *
          y ^ m * ((1 + z * c)⁻¹ ^ (k + n + m) * Complex.exp (y * z / (1 + z * c))) := by
  induction n with
  | zero =>
    intro k z _
    simp [_root_.GlobalTheory.HilbFam.rco]
  | succ n ih =>
    intro k z hz
    have hopen : IsOpen {w : ℂ | 1 + w * c ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    have hev : iteratedDeriv n (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) =ᶠ[𝓝 z]
        fun w ↦ ∑ m ∈ Finset.range (n + 1), (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) *
          y ^ m * ((1 + w * c)⁻¹ ^ (k + n + m) * Complex.exp (y * w / (1 + w * c))) :=
      Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw ↦ ih k w hw
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hd := HasDerivAt.fun_sum (u := Finset.range (n + 1)) (fun m _ ↦
      (hasDerivAt_inv_pow_mul_exp_div_one_add_mul c y (k + n + m) hz).const_mul
        ((_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m))
    rw [hd.deriv]
    set H : ℕ → ℂ := fun j ↦ (1 + z * c)⁻¹ ^ j * Complex.exp (y * z / (1 + z * c)) with hH
    set C : ℕ → ℕ → ℂ := fun n m ↦
      (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m with hC
    change ∑ m ∈ Finset.range (n + 1), C n m * (-(((k + n + m : ℕ) : ℂ) * c) * H (k + n + m + 1) +
        y * H (k + n + m + 2)) = ∑ m ∈ Finset.range (n + 1 + 1), C (n + 1) m * H (k + (n + 1) + m)
    have hA : ∑ m ∈ Finset.range (n + 1 + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) := by
      rw [Finset.sum_range_succ]
      simp [hC, rco_eq_zero_of_lt k n (n + 1) (Nat.lt_succ_self n)]
    have hT : ∀ m ∈ Finset.range (n + 1), C (n + 1) (m + 1) * H (k + (n + 1) + (m + 1)) =
        -(((k + n + (m + 1) : ℕ) : ℂ) * c) * C n (m + 1) * H (k + n + (m + 1) + 1) +
          C n m * (y * H (k + n + m + 2)) := by
      intro m hm
      have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      simp only [hC]
      rw [rco_mul_pow_mul_pow_succ_succ k n m hmn c y]
      have e1 : k + (n + 1) + (m + 1) = k + n + (m + 1) + 1 := by omega
      have e2 : k + n + m + 2 = k + n + (m + 1) + 1 := by omega
      rw [e1, e2]
      ring
    have h0 : C (n + 1) 0 * H (k + (n + 1) + 0) = -(((k + n + 0 : ℕ) : ℂ) * c) * C n 0 * H (k + n + 0 + 1) := by
      simp only [hC]
      rw [rco_mul_pow_mul_pow_succ_zero k n c y]
      have e1 : k + (n + 1) + 0 = k + n + 0 + 1 := by omega
      rw [e1]
    have hS : ∑ m ∈ Finset.range (n + 1), -(((k + n + (m + 1) : ℕ) : ℂ) * c) * C n (m + 1) *
          H (k + n + (m + 1) + 1) + -(((k + n + 0 : ℕ) : ℂ) * c) * C n 0 * H (k + n + 0 + 1) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) := by
      rw [← Finset.sum_range_succ' (fun m ↦ -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1))]
      exact hA
    have hB : ∑ m ∈ Finset.range (n + 1), C n m * (-(((k + n + m : ℕ) : ℂ) * c) * H (k + n + m + 1)) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) :=
      Finset.sum_congr rfl fun m _ ↦ by ring
    conv_rhs => rw [Finset.sum_range_succ', Finset.sum_congr rfl hT, Finset.sum_add_distrib, h0]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hB, ← hS]
    ring


set_option autoImplicit false in
open Filter Topology in
theorem _root_.GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag : ∀ (k n : ℕ) (c y : ℂ),
    iteratedDeriv n (fun z : ℂ ↦ (1 + z * c)⁻¹ ^ k * Complex.exp (y * z / (1 + z * c))) 0 =
      _root_.GlobalTheory.HilbFam.lag k n c y := by
  intro k n c y
  rw [iteratedDeriv_inv_pow_mul_exp_eq_sum_rco c y n k 0 (by simp)]
  unfold _root_.GlobalTheory.HilbFam.lag
  simp

end GlobalTheory.HilbFam.LagDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedPartialDerivProdOneVarAtZero
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.IterDProd

theorem diffOn_iteratedDeriv {r : ℝ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n f) (Metric.ball 0 r) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv Metric.isOpen_ball

theorem hasLineDerivAt_prod {I : Type} [Fintype I] [DecidableEq I] (φ : I → ℂ → ℂ) (A : ℂ)
    (z : I → ℂ) (j : I) (hj : DifferentiableAt ℂ (φ j) (z j)) :
    HasLineDerivAt ℂ (fun z : I → ℂ ↦ A * ∏ i, φ i (z i))
      (A * (deriv (φ j) (z j) * ∏ i ∈ Finset.univ.erase j, φ i (z i))) z (Pi.single j 1) := by
  unfold HasLineDerivAt
  have h1 : (fun t : ℂ ↦ A * ∏ i, φ i ((z + t • (Pi.single j (1 : ℂ) : I → ℂ)) i))
      = fun t ↦ A * (φ j (z j + t) * ∏ i ∈ Finset.univ.erase j, φ i (z i)) := by
    funext t
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 2
    · simp
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi)]
  have h2 : HasDerivAt (fun t : ℂ ↦ φ j (z j + t)) (deriv (φ j) (z j)) 0 := by
    have h : HasDerivAt (φ j) (deriv (φ j) (z j)) (z j + 0) := by simpa using hj.hasDerivAt
    exact h.comp_const_add (z j) 0
  show HasDerivAt (fun t : ℂ ↦ A * ∏ i, φ i ((z + t • (Pi.single j (1 : ℂ) : I → ℂ)) i)) _ 0
  rw [h1]
  exact (h2.mul_const _).const_mul A

theorem iterD_prod_ball {I : Type} [Fintype I] [DecidableEq I] (u : List I) (r : ℝ)
    (ψ : I → ℂ → ℂ) (A : ℂ) (hr : 0 < r) (hψ : ∀ i, DifferentiableOn ℂ (ψ i) (Metric.ball 0 r)) :
    ∀ z ∈ Metric.ball (0 : I → ℂ) r, iterD u (fun z ↦ A * ∏ i, ψ i (z i)) z
      = A * ∏ i, iteratedDeriv (u.count i) (ψ i) (z i) := by
  induction u with
  | nil => intro z _; simp [iterD]
  | cons j u ih =>
    intro z hz
    have hzj : z j ∈ Metric.ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff] at hz ⊢
      exact (norm_le_pi_norm z j).trans_lt hz
    have hev : iterD u (fun z ↦ A * ∏ i, ψ i (z i)) =ᶠ[nhds z]
        fun z ↦ A * ∏ i, iteratedDeriv (u.count i) (ψ i) (z i) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) ih
    have hd := hasLineDerivAt_prod (fun i ↦ iteratedDeriv (u.count i) (ψ i)) A z j
      ((diffOn_iteratedDeriv (hψ j) _).differentiableAt (Metric.isOpen_ball.mem_nhds hzj))
    show lineDeriv ℂ (iterD u (fun z ↦ A * ∏ i, ψ i (z i))) z (Pi.single j 1) = _
    rw [hev.lineDeriv_eq, hd.lineDeriv,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 2
    · rw [List.count_cons_self, iteratedDeriv_succ]
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      rw [List.count_cons_of_ne (Finset.ne_of_mem_erase hi).symm]

theorem iterD_prod : ∀ (I : Type) [Fintype I] [DecidableEq I] (u : List I) (r : ℝ) (ψ : I → ℂ → ℂ) (A : ℂ), 0 < r → (∀ i, DifferentiableOn ℂ (ψ i) (Metric.ball 0 r)) → iterD u (fun z ↦ A * ∏ i, ψ i (z i)) 0 = A * ∏ i, iteratedDeriv (u.count i) (ψ i) 0 := by
  intro I _ _ u r ψ A hr hψ
  exact iterD_prod_ball u r ψ A hr hψ 0 (Metric.mem_ball_self hr)

end GlobalTheory.IterDProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreSignedBinomCoeffMul
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem rco_mul_rco : ∀ k n m j : ℕ, j ≤ m → m ≤ n →
    rco k n m * rco k m j = rco k n j * ((n - j).choose (m - j) : ℤ) := by
  intro k n m j hjm hmn
  have h1 : n.choose m * m.choose j = n.choose j * (n - j).choose (m - j) := by
    first
      | exact Nat.choose_mul hjm
      | exact Nat.choose_mul hmn hjm
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hjm
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have e1 : j + p + q - (j + p) = q := by omega
  have e2 : j + p - j = p := by omega
  have e3 : j + p + q - j = p + q := by omega
  have h2 : ∀ a p q : ℕ, a.ascFactorial p * (a + p).ascFactorial q = a.ascFactorial (p + q) := by
    intro a p q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [← add_assoc, Nat.ascFactorial_succ, Nat.ascFactorial_succ, ← ih, add_assoc a p q]
      ring
  have h3 := h2 (k + j) p q
  rw [e2, e3] at h1
  have h1' : ((j + p + q).choose (j + p) : ℤ) * ((j + p).choose j : ℤ)
      = ((j + p + q).choose j : ℤ) * ((p + q).choose p : ℤ) := by exact_mod_cast h1
  have h3' : ((k + j).ascFactorial p : ℤ) * ((k + (j + p)).ascFactorial q : ℤ)
      = ((k + j).ascFactorial (p + q) : ℤ) := by
    rw [← add_assoc]; exact_mod_cast h3
  unfold rco
  rw [e1, e2, e3, pow_add, ← h3']
  linear_combination ((-1 : ℤ) ^ p * (-1) ^ q * ((k + j).ascFactorial p : ℤ)
    * ((k + (j + p)).ascFactorial q : ℤ)) * h1'

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeraySimplicialCocycleCoboundaryOfAcyclicLevelsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leray_simplicialCocycle_coboundary_of_acyclicLevels : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ), (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op (SimplexCategory.mk (k))))) F m, y = 0) → (∀ s : (free R).obj (E.obj (op (SimplexCategory.mk (0)))) ⟶ F, IsCls s 0 → s = 0) ∧ ∀ s : (free R).obj (E.obj (op (SimplexCategory.mk (n + 1)))) ⟶ F, IsCls s 0 → ∃ t : (free R).obj (E.obj (op (SimplexCategory.mk (n)))) ⟶ F, cobd t = s := by
  first | (exact @GlobalTheory.EtC.leray_inj) | (exact GlobalTheory.EtC.leray_inj) | (intros; apply GlobalTheory.EtC.leray_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisSpansUnitaryLie
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.SkewSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_eq_dot (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = (x ᵥ* G) ⬝ᵥ (fun b => cc (y b)) := by
  unfold herm
  rw [Finset.sum_comm]
  simp [dotProduct, vecMul, Finset.sum_mul]

theorem herm_sum_left {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E) (c : ι → E)
    (v : ι → Matrix (Fin r) (Fin r) E) (u w : Fin r → E) :
    herm G ((∑ i, c i • v i) *ᵥ u) w = ∑ i, c i * herm G (v i *ᵥ u) w := by
  simp only [herm_eq_dot, Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.sum_vecMul,
    Matrix.smul_vecMul, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem herm_sum_right {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E) (c : ι → E)
    (v : ι → Matrix (Fin r) (Fin r) E) (u w : Fin r → E) :
    herm G u ((∑ i, c i • v i) *ᵥ w) = ∑ i, cc (c i) * herm G u (v i *ᵥ w) := by
  have : (fun b => cc (((∑ i, c i • v i) *ᵥ w) b))
      = ∑ i, cc (c i) • (fun b => cc ((v i *ᵥ w) b)) := by
    funext b
    simp [cc, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply]
  simp only [herm_eq_dot, this, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem eq_zero_of_herm (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (Y : Matrix (Fin r) (Fin r) E) (h : ∀ u w, herm G (Y *ᵥ u) w = 0) : Y = 0 := by
  have key : ∀ u, Y *ᵥ u = 0 := by
    intro u
    apply Matrix.eq_zero_of_vecMul_eq_zero hG
    funext b
    have := h u (Pi.single b 1)
    rw [herm_eq_dot] at this
    have h2 : (fun b' => cc ((Pi.single b (1 : E) : Fin r → E) b')) = Pi.single b 1 := by
      funext b'
      by_cases hb : b' = b
      · subst hb; simp [cc]
      · simp [cc, hb]
    rw [h2] at this
    simpa using this
  ext a b
  have := congrFun (key (Pi.single b 1)) a
  simpa using this

theorem linearIndependent_of_skew {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E)
    (hG : G.det ≠ 0) (v : ι → Matrix (Fin r) (Fin r) E)
    (hv : ∀ i u w, herm G (v i *ᵥ u) w + herm G u (v i *ᵥ w) = 0)
    (hli : LinearIndependent (maximalRealSubfield E) v) : LinearIndependent E v := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  have step : ∀ c : ι → E, ∑ i, c i • v i = 0 → ∀ i, c i + cc (c i) = 0 := by
    intro c hc
    have h1 : ∑ i, cc (c i) • v i = 0 := by
      apply eq_zero_of_herm G hG
      intro u w
      have h := herm_sum_right G c v u w
      rw [hc] at h
      have h0 : herm G u ((0 : Matrix (Fin r) (Fin r) E) *ᵥ w) = 0 := by simp [herm, cc]
      rw [h0] at h
      rw [herm_sum_left, ← neg_eq_zero, ← Finset.sum_neg_distrib, h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [eq_neg_of_add_eq_zero_right (hv i u w)]; ring
    have hm : ∀ i, c i + cc (c i) ∈ maximalRealSubfield E := by
      intro i
      rw [← IsCMField.complexConj_eq_self_iff]
      simp [cc, add_comm]
    intro i
    have := hli (fun i => ⟨c i + cc (c i), hm i⟩) (by
      have : ∑ i, (c i + cc (c i)) • v i = 0 := by
        simp only [add_smul, Finset.sum_add_distrib, hc, h1, add_zero]
      exact this) i
    exact congrArg Subtype.val this
  intro c hc j
  have h := step (fun i => cc (c j) * c i) (by
    simp only [mul_smul, ← Finset.smul_sum, hc, smul_zero]) j
  have h2 : 2 * (cc (c j) * c j) = 0 := by
    rw [← h]; simp [cc]; ring
  simp [cc] at h2
  exact h2

theorem finrank_ker_trace (K : Type) [Field K] (r : ℕ) :
    Module.finrank K (LinearMap.ker (Matrix.traceLinearMap (Fin (r + 1)) K K)) = (r + 1) ^ 2 - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin (r + 1)) K K)
  have hs : LinearMap.range (Matrix.traceLinearMap (Fin (r + 1)) K K) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro a
    exact ⟨Matrix.single 0 0 a, by simp⟩
  rw [hs, finrank_top, Module.finrank_self, Module.finrank_matrix] at h
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
  rw [sq]; omega

theorem mem_span_of_skew : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ i, (e i).trace = 0 ∧ ∀ u w, herm G (e i *ᵥ u) w + herm G u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → X ∈ Submodule.span (maximalRealSubfield E) (Set.range e) := by
  intro E _ _ _ r G e _ hG he hli X hX hXs
  rcases r with _ | r
  · have : X = 0 := Subsingleton.elim _ _
    rw [this]; exact Submodule.zero_mem _
  by_contra hn
  have h1 : LinearIndependent (maximalRealSubfield E) (fun o : Option _ => Option.casesOn' o X e) :=
    hli.option hn
  have h2 := linearIndependent_of_skew G hG _ (by
    rintro (_ | i)
    · exact hXs
    · exact (he i).2) h1
  let f : Option (Fin ((r + 1) ^ 2 - 1)) →
      LinearMap.ker (Matrix.traceLinearMap (Fin (r + 1)) E E) := fun o =>
    ⟨Option.casesOn' o X e, by
      rcases o with _ | i
      · exact hX
      · exact (he i).1⟩
  have h3 : LinearIndependent E f := LinearIndependent.of_comp (Submodule.subtype _) h2
  have h4 := h3.fintype_card_le_finrank
  rw [finrank_ker_trace] at h4
  simp at h4

end GlobalTheory.SkewSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeResolutionLocalChaseOnSupportStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_resolution_localChase_on_support : ∀ (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G), (∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) → ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b₁ : Sec ((res R F).X (n + 1)) U) (b₂ : Sec ((res R G).X n) U), Sec.map ((res R F).d (n + 1) (n + 2)) b₁ = 0 → Sec.map ((resMap R φ).f (n + 1)) b₁ + Sec.map ((res R G).d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec ((res R F).X n) V) (a₂ : Sec ((res R G).X (n - 1)) V), Sec.map ((res R F).d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map ((resMap R φ).f n) a₁ + Sec.map ((res R G).d (n - 1) n) a₂ = Sec.res g b₂ := by
  first | (exact @GlobalTheory.EtC.ConeChase.chase) | (exact GlobalTheory.EtC.ConeChase.chase) | (intros; apply GlobalTheory.EtC.ConeChase.chase  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualLocalizationIffForallRegularFormStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) := by
  first | (exact @GlobalTheory.mem_traceDual_localization_iff_forall_regularForm) | (exact GlobalTheory.mem_traceDual_localization_iff_forall_regularForm) | (intros; apply GlobalTheory.mem_traceDual_localization_iff_forall_regularForm  <;> assumption)
end

