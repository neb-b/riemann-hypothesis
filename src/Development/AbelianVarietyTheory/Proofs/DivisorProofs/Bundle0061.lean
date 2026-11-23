module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSimilitudeEntrySqBound
section
open Matrix

namespace GlobalTheory

theorem herm_scale_entry_bound : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ), P.IsHermitian → (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) → ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * P * Y = (s : ℂ) • P → ∀ i j, ‖Y i j‖ ^ 2 ≤ K * s := by
  intro n P _hP hpos
  cases n with
  | zero => exact ⟨0, fun _ _ _ _ i => i.elim0⟩
  | succ k =>
  set q : (Fin (k+1) → ℂ) → ℝ := fun x => (star x ⬝ᵥ P *ᵥ x).re with hq
  have hcont : Continuous q := by
    simp only [hq, dotProduct, mulVec, Pi.star_apply]
    fun_prop
  have hsmul : ∀ (t : ℝ) (x : Fin (k+1) → ℂ), q ((t : ℂ) • x) = t ^ 2 * q x := by
    intro t x
    simp only [hq, star_smul, Complex.star_def, Complex.conj_ofReal, mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    ring
  obtain ⟨x0, hx0S, hmin⟩ := (isCompact_sphere (0 : Fin (k+1) → ℂ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
  set m := q x0 with hm_def
  have hx0 : x0 ≠ 0 := by
    intro h; rw [h] at hx0S; simp at hx0S
  have hm : 0 < m := hpos x0 hx0
  have hlow : ∀ x, m * ‖x‖ ^ 2 ≤ q x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [hq]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set u : Fin (k+1) → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu
    have huS : u ∈ Metric.sphere (0 : Fin (k+1) → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hxu : x = ((‖x‖ : ℝ) : ℂ) • u := by
      rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
    have h1 : m ≤ q u := hmin huS
    have hqx : q x = ‖x‖ ^ 2 * q u := by
      conv_lhs => rw [hxu]
      exact hsmul _ _
    rw [hqx]
    nlinarith [sq_nonneg ‖x‖]
  have hY : ∀ (Y : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) (s : ℝ), Yᴴ * P * Y = (s : ℂ) • P →
      ∀ x, q (Y *ᵥ x) = s * q x := by
    intro Y s h x
    simp only [hq]
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  set C : ℝ := ∑ j, ‖P j j‖ with hC
  refine ⟨C / m, fun Y s hs h i j => ?_⟩
  set e : Fin (k+1) → ℂ := Pi.single j 1 with he
  have hYe : Y *ᵥ e = fun i => Y i j := by
    rw [he, mulVec_single_one]; rfl
  have hqe : q e = (P j j).re := by
    simp [hq, he, mulVec_single_one]
  have hle : ‖Y i j‖ ≤ ‖Y *ᵥ e‖ := by
    rw [hYe]; exact norm_le_pi_norm (fun i => Y i j) i
  have hPjj : (P j j).re ≤ C :=
    (Complex.re_le_norm _).trans (Finset.single_le_sum (f := fun j => ‖P j j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j))
  have key : m * ‖Y *ᵥ e‖ ^ 2 ≤ s * (P j j).re := by
    rw [← hqe, ← hY Y s h e]; exact hlow _
  have h2 : ‖Y i j‖ ^ 2 ≤ ‖Y *ᵥ e‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith [mul_le_mul_of_nonneg_left hPjj hs.le]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpectralPartsAnticommute
section
open Matrix

namespace GlobalTheory

theorem spectral_parts_of_diag {n : Type} [Fintype n] [DecidableEq n] (Y J U : Matrix n n ℂ)
    (μ : n → ℝ) (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1)
    (hY : Y = U * diagonal (fun j => (μ j : ℂ)) * Uᴴ) (hJ : J * Y = -(Y * J)) :
    ∃ (s : Finset ℝ) (N E : ℝ → Matrix n n ℂ), Y = ∑ ν ∈ s, (ν : ℂ) • N ν ∧
      (∀ ν, (N ν).IsHermitian ∧ (E ν).IsHermitian ∧ Y * N ν = (ν : ℂ) • E ν ∧
        N ν * Y = (ν : ℂ) • E ν ∧ Y * E ν = (ν : ℂ) • N ν ∧ E ν * Y = (ν : ℂ) • N ν ∧
        J * N ν = -(N ν * J) ∧ J * E ν = E ν * J) ∧ ∀ ν ν', E ν * E ν' = E ν' * E ν := by
  classical
  set φ : (ℝ → ℝ) → Matrix n n ℂ := fun f => U * diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * Uᴴ
    with hφ
  have hcongr : ∀ f g : ℝ → ℝ, (∀ x, f x = g x) → φ f = φ g := by
    intro f g h
    rw [show f = g from funext h]
  have hmul : ∀ f g : ℝ → ℝ, φ f * φ g = φ (fun x => f x * g x) := by
    intro f g
    simp only [hφ]
    calc U * diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * Uᴴ *
          (U * diagonal (fun j => ((g (μ j) : ℝ) : ℂ)) * Uᴴ)
        = U * (diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * (Uᴴ * U) *
          diagonal (fun j => ((g (μ j) : ℝ) : ℂ))) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [h1, Matrix.mul_one, diagonal_mul_diagonal]
        simp only [Complex.ofReal_mul]
  have hsmul : ∀ (c : ℝ) (f : ℝ → ℝ), (c : ℂ) • φ f = φ (fun x => c * f x) := by
    intro c f
    simp only [hφ]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    ext j
    simp [Pi.smul_apply, smul_eq_mul]
  have hherm : ∀ f : ℝ → ℝ, (φ f).IsHermitian := by
    intro f
    simp only [hφ]
    apply isHermitian_mul_mul_conjTranspose
    rw [isHermitian_diagonal_iff]
    intro j
    exact Complex.conj_ofReal _
  have hid : Y = φ (fun x => x) := hY
  set K := Uᴴ * J * U with hK
  have hJK : J = U * K * Uᴴ := by
    rw [hK]
    calc J = (U * Uᴴ) * J * (U * Uᴴ) := by rw [h2]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hKD : K * diagonal (fun j => (μ j : ℂ)) = -(diagonal (fun j => (μ j : ℂ)) * K) := by
    have e := congrArg (fun M => Uᴴ * M * U) hJ
    simp only [hY] at e
    have a1 : Uᴴ * (J * (U * diagonal (fun j => (μ j : ℂ)) * Uᴴ)) * U
        = K * diagonal (fun j => (μ j : ℂ)) * (Uᴴ * U) := by
      simp only [hK, Matrix.mul_assoc]
    have a2 : Uᴴ * (-(U * diagonal (fun j => (μ j : ℂ)) * Uᴴ * J)) * U
        = -((Uᴴ * U) * diagonal (fun j => (μ j : ℂ)) * K) := by
      simp only [hK, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
    rw [a1, a2, h1, Matrix.mul_one, Matrix.one_mul] at e
    exact e
  have hkey : ∀ f : ℝ → ℝ, J * φ f = φ (fun x => f (-x)) * J := by
    intro f
    have hK2 : K * diagonal (fun j => ((f (μ j) : ℝ) : ℂ))
        = diagonal (fun j => ((f (-μ j) : ℝ) : ℂ)) * K := by
      ext i j
      have e := congrFun (congrFun hKD i) j
      simp only [mul_diagonal, diagonal_mul, Matrix.neg_apply] at e ⊢
      by_cases h0 : K i j = 0
      · simp [h0]
      · have : (μ j : ℂ) = -(μ i : ℂ) := by
          apply mul_left_cancel₀ h0
          rw [e]; ring
        have h3 : μ j = -μ i := by exact_mod_cast this
        rw [h3, mul_comm]
    simp only [hφ]
    rw [hJK]
    calc U * K * Uᴴ * (U * diagonal (fun j => ((f (μ j) : ℝ) : ℂ)) * Uᴴ)
        = U * (K * (Uᴴ * U) * diagonal (fun j => ((f (μ j) : ℝ) : ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * (diagonal (fun j => ((f (-μ j) : ℝ) : ℂ)) * (Uᴴ * U) * K) * Uᴴ := by
          rw [h1, Matrix.mul_one, Matrix.mul_one, hK2]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hs1 : ∀ x : ℝ, x * Real.sign x = |x| := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · simp [h]
    · rw [Real.sign_of_pos h, abs_of_pos h]; ring
  have hs2 : ∀ x : ℝ, |x| * Real.sign x = x := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · simp [h]
    · rw [Real.sign_of_pos h, abs_of_pos h]; ring
  refine ⟨Finset.univ.image (fun j => |μ j|),
    fun ν => φ (fun x => if |x| = ν then Real.sign x else 0),
    fun ν => φ (fun x => if |x| = ν then 1 else 0), ?_, ?_, ?_⟩
  · simp only [hsmul]
    simp only [hφ]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hY]
    congr 2
    ext i j
    rw [Matrix.sum_apply]
    by_cases hij : i = j
    · subst hij
      simp only [diagonal_apply_eq]
      rw [Finset.sum_eq_single |μ i|]
      · simp only [if_true, hs2]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_image_of_mem (fun j => |μ j|) (Finset.mem_univ i)) h
    · simp [diagonal_apply_ne _ hij]
  · intro ν
    clear hY hK hKD hJK hφ
    clear_value φ
    beta_reduce
    refine ⟨hherm _, hherm _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [hs1, h, mul_one]
      · simp
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [mul_comm, hs1, h, mul_one]
      · simp
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [← h, hs2, mul_one]
      · simp
    · rw [hsmul, hid, hmul]
      apply hcongr; intro x
      split_ifs with h
      · rw [← h, hs2, one_mul]
      · simp
    · have : ∀ f : ℝ → ℝ, -φ f = φ (fun x => -f x) := by
        intro f
        have := hsmul (-1) f
        simpa using this
      rw [hkey, ← Matrix.neg_mul, this]
      congr 1
      apply hcongr; intro x
      rw [abs_neg]
      split_ifs with h
      · exact Real.sign_neg
      · simp
    · rw [hkey]
      congr 1
      apply hcongr; intro x
      rw [abs_neg]
  · intro ν ν'
    clear hY hK hKD hJK hφ hkey hs1 hs2 hherm hsmul hid
    clear_value φ
    beta_reduce
    exact (hmul _ _).trans ((hcongr _ _ fun x => mul_comm _ _).trans (hmul _ _).symm)

theorem hermitian_spectral_parts_anticommute :
    ∀ (n : Type) [Fintype n] [DecidableEq n] (Y J : Matrix n n ℂ), Y.IsHermitian →
      J * Y = -(Y * J) →
      ∃ (s : Finset ℝ) (N E : ℝ → Matrix n n ℂ), Y = ∑ ν ∈ s, (ν : ℂ) • N ν ∧
      (∀ ν, (N ν).IsHermitian ∧ (E ν).IsHermitian ∧ Y * N ν = (ν : ℂ) • E ν ∧
        N ν * Y = (ν : ℂ) • E ν ∧ Y * E ν = (ν : ℂ) • N ν ∧ E ν * Y = (ν : ℂ) • N ν ∧
        J * N ν = -(N ν * J) ∧ J * E ν = E ν * J) ∧ ∀ ν ν', E ν * E ν' = E ν' * E ν := by
  intro n _ _ Y J hY hJ
  refine spectral_parts_of_diag Y J (hY.eigenvectorUnitary : Matrix n n ℂ) hY.eigenvalues
    ?_ ?_ ?_ hJ
  · exact hY.eigenvectorUnitary.2.1
  · exact hY.eigenvectorUnitary.2.2
  · exact hY.spectral_theorem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelALogALe
section
namespace GlobalTheory

theorem hilbertSamuel_ALogA_le (T D : ℕ) (PP b z : ℝ) (hD1 : 1 ≤ D) (hDT : D ≤ T) (hPP : 1 ≤ PP)
    (hb : 1 ≤ b) (hlogb : Real.log b ≤ PP) (hTP : (T : ℝ) * PP ≤ Real.sqrt b) (hz0 : 0 ≤ z)
    (hz : z ≤ 1 / 2) :
    26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) * Real.log (max (26 * (26 * (D : ℝ) ^ 2 + 2 * z * T)) 1)
      ≤ 6000 * b := by
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDT' : (D : ℝ) ≤ T := by exact_mod_cast hDT
  have hT1 : (1 : ℝ) ≤ T := le_trans hD1' hDT'
  set A : ℝ := 26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) with hAdef
  have hA1 : 1 ≤ A := by
    have : (0 : ℝ) ≤ 2 * z * T := by positivity
    nlinarith
  have hmax : max A 1 = A := max_eq_left hA1
  rw [hmax]
  have hApos : 0 < A := by linarith
  have hAle : A ≤ 702 * (T : ℝ) ^ 2 := by
    have h1 : (D : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by nlinarith
    have h2 : 2 * z * (T : ℝ) ≤ T := by nlinarith
    have h3 : (T : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hTsq : (T : ℝ) ≤ Real.sqrt b := by nlinarith
  have hlogT : 2 * Real.log T ≤ PP := by
    have h1 : Real.log T ≤ Real.log (Real.sqrt b) := Real.log_le_log hT0 hTsq
    rw [Real.log_sqrt (by linarith)] at h1
    linarith
  have hlog702 : Real.log 702 < 7 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : Real.exp 7 = Real.exp 1 ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h27 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by
      apply pow_le_pow_left₀ (by norm_num); linarith
    nlinarith
  have hlogA : Real.log A ≤ 8 * PP := by
    have h1 : Real.log A ≤ Real.log (702 * (T : ℝ) ^ 2) := Real.log_le_log hApos hAle
    have h2 : Real.log (702 * (T : ℝ) ^ 2) = Real.log 702 + 2 * Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    linarith
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hmain : A * Real.log A ≤ 702 * (T : ℝ) ^ 2 * (8 * PP) :=
    mul_le_mul hAle hlogA hlogA0 (by positivity)
  have hsq : ((T : ℝ) * PP) ^ 2 ≤ b := by
    have h0 : 0 ≤ (T : ℝ) * PP := by positivity
    calc ((T : ℝ) * PP) ^ 2 ≤ Real.sqrt b ^ 2 := pow_le_pow_left₀ h0 hTP 2
      _ = b := Real.sq_sqrt (by linarith)
  have hTPP : (T : ℝ) ^ 2 * PP ≤ (T : ℝ) ^ 2 * PP ^ 2 := by
    have : PP ≤ PP ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentsOfConeIntegralEquation
section
open MvPolynomial

namespace GlobalTheory

theorem coeff_eval₂_C_mul_X {F K : Type} [Field F] [Field K] (φ : F →+* K) {r : ℕ} (w : Fin r → K)
    (p : MvPolynomial (Fin r) F) (d : ℕ) :
    (MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) p).coeff d
      = MvPolynomial.eval₂ φ w (homogeneousComponent d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    have hprod : (u.prod fun i k => (Polynomial.C (w i) * Polynomial.X : Polynomial K) ^ k)
        = Polynomial.C (u.prod fun i k => w i ^ k) * Polynomial.X ^ (Finsupp.degree u) := by
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
        Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
    have hcomp : homogeneousComponent d (monomial u a)
        = if Finsupp.degree u = d then monomial u a else 0 := by
      ext v
      rw [coeff_homogeneousComponent]
      by_cases hd : Finsupp.degree u = d
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
    rw [eval₂_monomial, hprod, hcomp, ← mul_assoc, RingHom.comp_apply, ← map_mul,
      Polynomial.coeff_C_mul_X_pow]
    by_cases h : Finsupp.degree u = d
    · subst h
      simp [eval₂_monomial]
    · have h' : d ≠ Finsupp.degree u := fun e => h e.symm
      simp [h, h']
  | add p q hp hq =>
    simp only [eval₂_add, Polynomial.coeff_add, map_add (f := _), hp, hq]

theorem homogeneous_components_of_integral_equation (F K : Type) [Field F] [Field K] (φ : F →+* K)
    (r e m : ℕ) (w : Fin r → K) (τ : K) (b : Fin m → MvPolynomial (Fin r) F)
    (h : (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ)
      (fun i => Polynomial.C (w i) * Polynomial.X) (b k) *
        (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0) :
    ∃ a : Fin m → MvPolynomial (Fin r) F, (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧
      τ ^ m + ∑ k, MvPolynomial.eval₂ φ w (a k) * τ ^ (k : ℕ) = 0 := by
  refine ⟨fun k => homogeneousComponent (e * (m - k)) (b k),
    fun k => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hc := congrArg (fun P : Polynomial K => P.coeff (e * m)) h
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc
  have hpow : ∀ n : ℕ, (Polynomial.C τ * Polynomial.X ^ e) ^ n
      = Polynomial.C (τ ^ n) * Polynomial.X ^ (e * n) := by
    intro n
    rw [mul_pow, ← pow_mul, map_pow]
  have hterm : ∀ k : Fin m, (MvPolynomial.eval₂ (Polynomial.C.comp φ)
      (fun i => Polynomial.C (w i) * Polynomial.X) (b k) *
        (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ)).coeff (e * m)
      = MvPolynomial.eval₂ φ w (homogeneousComponent (e * (m - k)) (b k)) * τ ^ (k : ℕ) := by
    intro k
    have hle : e * (k : ℕ) ≤ e * m := Nat.mul_le_mul_left e k.is_lt.le
    rw [hpow, ← mul_assoc, Polynomial.coeff_mul_X_pow', if_pos hle, Polynomial.coeff_mul_C,
      ← Nat.mul_sub, coeff_eval₂_C_mul_X]
  rw [hpow, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
  simpa only [hterm] using hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfaceDiffIsPreirreducibleOfNoSplitting
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_prime_factor_mem_prime_ideal_ufd {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (I : Ideal R) [hI : I.IsPrime] (a : R) (ha : a ≠ 0)
    (haI : a ∈ I) : ∃ u : R, Prime u ∧ u ∣ a ∧ u ∈ I := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl ha
  | h₂ x hx => exact absurd (I.eq_top_of_isUnit_mem haI hx) hI.ne_top
  | h₃ a p ha' hp ih =>
    rcases hI.mem_or_mem haI with h | h
    · exact ⟨p, hp, dvd_mul_right _ _, h⟩
    · obtain ⟨u, hu, hua, huI⟩ := ih (right_ne_zero_of_mul ha) h
      exact ⟨u, hu, dvd_mul_of_dvd_right hua _, huI⟩

theorem hypersurface_diff_isPreirreducible (Ω : Type) [Field Ω] [IsAlgClosed Ω] (σ : Type) [Finite σ]
    (f g : MvPolynomial σ Ω) (D : ℕ) (hf0 : f ≠ 0) (hfD : f.totalDegree ≤ D)
    (hno : ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧
      ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧
        MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0)) :
    IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) := by
  intro U V hU hV ⟨p, hpS, hpU⟩ ⟨q, hqS, hqV⟩
  have hfp : f ∈ p.asIdeal := by simpa using hpS.1
  have hgp : g ∉ p.asIdeal := by simpa using hpS.2
  obtain ⟨u, hu, huf, hup⟩ := exists_prime_factor_mem_prime_ideal_ufd p.asIdeal f hf0 hfp
  obtain ⟨v, rfl⟩ := huf
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := right_ne_zero_of_mul hf0
  have hdeg := MvPolynomial.totalDegree_mul_of_isDomain hu0 hv0

  have hgrad : g ∉ (Ideal.span {u}).radical := by
    intro hg
    apply hgp
    have : (Ideal.span {u}).radical ≤ p.asIdeal :=
      (Ideal.radical_mono ((Ideal.span_singleton_le_iff_mem _).mpr hup)).trans
        p.isPrime.radical.le
    exact this hg
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω)] at hgrad
  simp only [MvPolynomial.mem_vanishingIdeal_iff, not_forall] at hgrad
  obtain ⟨P, hP, hPg⟩ := hgrad
  have hPu : MvPolynomial.eval P u = 0 := by
    have := hP u (Ideal.mem_span_singleton_self u)
    simpa [MvPolynomial.aeval_eq_eval] using this
  have hPg' : MvPolynomial.eval P g ≠ 0 := by simpa [MvPolynomial.aeval_eq_eval] using hPg

  have hvg : g ∈ (Ideal.span {v}).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω)]
    intro Q hQ
    have hQv : MvPolynomial.eval Q v = 0 := by
      have := hQ v (Ideal.mem_span_singleton_self v)
      simpa [MvPolynomial.aeval_eq_eval] using this
    by_contra hQg
    apply hno
    refine ⟨u, v, by omega, by omega, rfl, P, Q, hPu, hPg', hQv, ?_⟩
    simpa [MvPolynomial.aeval_eq_eval] using hQg

  have hprime : (Ideal.span {u}).IsPrime := (Ideal.span_singleton_prime hu0).mpr hu
  let x : PrimeSpectrum (MvPolynomial σ Ω) := ⟨Ideal.span {u}, hprime⟩
  have key : ∀ y ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g},
      y ∈ closure ({x} : Set _) := by
    intro y hy
    have hfy : u * v ∈ y.asIdeal := by simpa using hy.1
    have hgy : g ∉ y.asIdeal := by simpa using hy.2
    rw [← PrimeSpectrum.le_iff_mem_closure]
    show Ideal.span {u} ≤ y.asIdeal
    rw [Ideal.span_singleton_le_iff_mem]
    rcases y.isPrime.mem_or_mem hfy with h | h
    · exact h
    · exfalso; apply hgy
      have : (Ideal.span {v}).radical ≤ y.asIdeal :=
        (Ideal.radical_mono ((Ideal.span_singleton_le_iff_mem _).mpr h)).trans
          y.isPrime.radical.le
      exact this hvg
  have hxS : x ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g} := by
    constructor
    · simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
      exact Ideal.mem_span_singleton.mpr (dvd_mul_right u v)
    · simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
      intro hg
      exact hgp (((Ideal.span_singleton_le_iff_mem _).mpr hup) hg)
  have hxU : x ∈ U := by
    have := key p hpS
    rw [mem_closure_iff] at this
    obtain ⟨z, hzU, hz⟩ := this U hU hpU
    rw [Set.mem_singleton_iff.mp hz] at hzU; exact hzU
  have hxV : x ∈ V := by
    have := key q hqS
    rw [mem_closure_iff] at this
    obtain ⟨z, hzV, hz⟩ := this V hV hqV
    rw [Set.mem_singleton_iff.mp hz] at hzV; exact hzV
  exact ⟨x, hxS, hxU, hxV⟩

end GlobalTheory
end

