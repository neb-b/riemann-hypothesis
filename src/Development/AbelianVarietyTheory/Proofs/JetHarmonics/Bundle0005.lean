module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormAddSqLeOfBounds
section
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem sum_norm_add_sq_le_of_bounds :
    ∀ (V ι : Type) [NormedAddCommGroup V] [Fintype ι] (u v : ι → V) (c s N : ℝ), 0 ≤ c → 0 ≤ s → 0 ≤ N → ∑ i, ‖u i‖ ^ 2 ≤ c ^ 2 * N → ∑ i, ‖v i‖ ^ 2 ≤ s ^ 2 * N → ∑ i, ‖u i + v i‖ ^ 2 ≤ (c + s) ^ 2 * N := by
  intro V ι _ _ u v c s N hc hs hN hu hv
  have hcs : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hv0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h1 : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤ (c * s * N) ^ 2 := by
    calc _ ≤ _ := hcs
      _ ≤ (c ^ 2 * N) * (s ^ 2 * N) := mul_le_mul hu hv hv0 (by positivity)
      _ = _ := by ring
  have h2 : ∑ i, ‖u i‖ * ‖v i‖ ≤ c * s * N :=
    (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun i _ => by positivity) (by positivity)
      two_ne_zero).1 h1
  have h3 : ∑ i, ‖u i + v i‖ ^ 2 ≤ ∑ i, (‖u i‖ ^ 2 + 2 * (‖u i‖ * ‖v i‖) + ‖v i‖ ^ 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    calc ‖u i + v i‖ ^ 2 ≤ (‖u i‖ + ‖v i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ = _ := by ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h3
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPosOfTensorPos
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointStepCompare

open NumberField Matrix
open scoped MatrixOrder

section Evaluations

variable {Y : Type} [AddCommGroup Y] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Y)

def evalOn (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) : (ι × ι → ℤ) →ₗ[ℤ] ℝ where
  toFun n := ∑ p, (n p : ℝ) * B (b p.1) (b p.2)
  map_add' n n' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k n := by simp [Finset.mul_sum, mul_assoc]

def tensorCoord : Y →ₗ[ℤ] Y →ₗ[ℤ] (ι × ι → ℤ) :=
  LinearMap.mk₂ ℤ (fun x y p => b.repr x p.1 * b.repr y p.2)
    (fun _ _ _ => by funext p; simp [add_mul]) (fun _ _ _ => by funext p; simp [mul_assoc])
    (fun _ _ _ => by funext p; simp [mul_add]) (fun _ _ _ => by funext p; simp [mul_left_comm])

theorem evalOn_tensorCoord (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x y : Y) :
    evalOn b B (tensorCoord b x y) = B x y := by
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  change ∑ p : ι × ι, ((b.repr x p.1 * b.repr y p.2 : ℤ) : ℝ) * B (b p.1) (b p.2) = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    Fintype.sum_prod_type, Int.cast_mul, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Evaluations

theorem posSemidef_of_int {ι : Type} [Fintype ι] {N : Matrix ι ι ℝ} (hH : N.IsHermitian)
    (hp : ∀ x : ι → ℤ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ))) : N.PosSemidef := by
  have hq : ∀ x : ι → ℚ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ)) := by
    intro x
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
    choose y hy using hd
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    have hxy : (fun i => (y i : ℝ)) = ((d : ℤ) : ℝ) • (fun i => (x i : ℝ)) := by
      funext i
      have := congrArg (fun q : ℚ => (q : ℝ)) (hy i)
      simpa [Submonoid.smul_def] using this
    have h1 := hp y
    rw [hxy, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
    exact nonneg_of_mul_nonneg_right h1 (mul_self_pos.2 hd0)
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun x => ?_⟩
  have hd : DenseRange (Pi.map fun (_ : ι) => (Rat.cast : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on (p := fun x => 0 ≤ star x ⬝ᵥ N *ᵥ x) x ?_ (fun q => ?_)
  · exact isClosed_le continuous_const (by fun_prop)
  · exact hq q

theorem posDef_of_int {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (hs : ∀ i j, M i j = M j i)
    (hp : ∀ x : ι → ℤ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x) :
    M.det ≠ 0 ∧ (M.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hd : M.det ≠ 0 := fun h => by
    obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [h0] using hp v hv
  have h1 : (M.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    refine posSemidef_of_int (by ext i j; simp [hs i j]) fun x => ?_
    have : (fun i => (x i : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (x i : ℝ)) =
        ((x ⬝ᵥ M *ᵥ x : ℤ) : ℝ) := by simp [dotProduct, mulVec]
    rw [this]
    by_cases hx : x = 0
    · simp [hx]
    · exact_mod_cast (hp x hx).le
  refine ⟨hd, h1.posDef_iff_det_ne_zero.2 ?_⟩
  rw [← Int.cast_det]
  exact_mod_cast hd

theorem sum_pos_of_tensor_pos : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (ι : Type) [Fintype ι] (a c : ι → Y), (∀ f g : Y →ₗ[ℤ] ℤ, ∑ i, f (a i) * g (c i) = ∑ i, g (a i) * f (c i)) → (∀ f : Y →ₗ[ℤ] ℤ, f ≠ 0 → 0 < ∑ i, f (a i) * f (c i)) → ∀ γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ, (∀ x y, γ x y = γ y x) → (∀ x, 0 ≤ γ x x) → γ ≠ 0 → 0 < ∑ i, γ (a i) (c i) := by
  intro Y _ _ _ ι _ a c hs hp γ hγ h0 hne
  classical
  let b := Module.finBasis ℤ Y
  let M : Matrix _ _ ℤ := Matrix.of fun p q => ∑ i, b.coord p (a i) * b.coord q (c i)
  have hM := (posDef_of_int M (fun p q => hs _ _) fun x hx => by
    have := hp (∑ p, x p • b.coord p) fun h => hx (funext fun q => by
      simpa [Finsupp.single_apply] using LinearMap.congr_fun h (b q))
    convert this using 1
    simp only [dotProduct, mulVec, M, Matrix.of_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    ring).2
  let G : Matrix _ _ ℝ := Matrix.of fun p q => γ (b p) (b q)
  have hG : G.PosSemidef := posSemidef_of_int (by ext p q; simp [G, hγ (b p) (b q)]) fun x => by
    convert h0 (∑ p, x p • b p) using 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, mulVec, G, Matrix.of_apply, map_sum, map_zsmul, LinearMap.sum_apply,
      LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]; ring
  have htr : ∑ i, γ (a i) (c i) = (M.map (Int.cast : ℤ → ℝ) * G).trace := by
    simp only [← evalOn_tensorCoord b γ]
    change ∑ i, ∑ p : _ × _, ((b.repr (a i) p.1 * b.repr (c i) p.2 : ℤ) : ℝ) * γ (b p.1) (b p.2) = _
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, M, G, Matrix.of_apply,
      Int.cast_sum, Finset.sum_mul, Module.Basis.coord_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  have hCd : IsUnit C.det := by
    refine Ne.isUnit fun h => hM.det_pos.ne' ?_
    rw [hC, det_mul, h, mul_zero]
  have h1 := hG.mul_mul_conjTranspose_same C
  have h2 : (C * G * Cᴴ).trace = ∑ i, γ (a i) (c i) := by
    rw [htr, hC, trace_mul_cycle, star_eq_conjTranspose]
  rw [← h2]
  refine lt_of_le_of_ne h1.trace_nonneg fun h => hne ?_
  have h3 := h1.trace_eq_zero_iff.1 h.symm
  have hu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 hCd
  have h4 : G = 0 := by
    rwa [← star_eq_conjTranspose, hu.star.mul_left_eq_zero, hu.mul_right_eq_zero] at h3
  exact b.ext fun p => b.ext fun q => congrFun (congrFun h4 p) q

theorem eq_zero_of_trace_mul (E : Type) [Field E] [NumberField E] {u : 𝓞 E}
    (h : ∀ α : 𝓞 E, Algebra.trace ℤ (𝓞 E) (α * u) = 0) : u = 0 := by
  by_contra hu
  obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) u).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hu)
  have h1 := h α
  rw [mul_comm, ← hα, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
  have hd : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
  exact mul_ne_zero (by exact_mod_cast hd.ne') hr h1

theorem exists_traceDual : ∀ (E : Type) [Field E] [NumberField E], ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (ω θ : ι → 𝓞 E), 0 < N ∧ ∑ s, θ s * ω s = (N : 𝓞 E) ∧ ∀ g : 𝓞 E →ₗ[ℤ] ℤ, ∀ α : 𝓞 E, Algebra.trace ℤ (𝓞 E) (α * ∑ s, g (ω s) • θ s) = N * g α := by
  intro E _ _
  classical
  let ω := RingOfIntegers.basis E
  let d := (integralBasis E).traceDual
  have : Algebra.IsAlgebraic ℤ E := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨k, hk, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image d)
  let θ : _ → 𝓞 E := fun s => k • (⟨k • d s, hint _ (by simp)⟩ : 𝓞 E)
  have hN : (((k * k).toNat : ℕ) : ℤ) = k * k := Int.toNat_of_nonneg (mul_self_nonneg k)
  have hθ : ∀ s t, Algebra.trace ℤ (𝓞 E) (ω t * θ s) = if t = s then k * k else 0 := by
    intro s t
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_trace_int]
    have : ((ω t * θ s : 𝓞 E) : E) = k • k • (d s * integralBasis E t) := by
      change (ω t : E) * (k • k • d s) = _
      rw [integralBasis_apply, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]
      ring
    rw [this, map_zsmul, map_zsmul, Module.Basis.trace_traceDual_mul]
    split_ifs <;> simp
  have h3 : ∀ (g : 𝓞 E →ₗ[ℤ] ℤ) (α : 𝓞 E),
      Algebra.trace ℤ (𝓞 E) (α * ∑ s, g (ω s) • θ s) = k * k * g α := by
    intro g α
    have : (Algebra.trace ℤ (𝓞 E)) ∘ₗ LinearMap.mulRight ℤ (∑ s, g (ω s) • θ s) = (k * k) • g :=
      ω.ext fun t => by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Finset.mul_sum, mul_smul_comm,
          map_sum, map_smul, hθ, LinearMap.smul_apply, smul_eq_mul]
        simp [mul_comm]
    exact LinearMap.congr_fun this α
  refine ⟨(k * k).toNat, _, inferInstance, ω, θ, ?_, ?_, fun g α => by rw [hN, h3]⟩
  · have := mul_self_pos.2 hk
    omega
  · rw [← sub_eq_zero]
    refine eq_zero_of_trace_mul E fun α => ?_
    have h4 : ∀ s, Algebra.trace ℤ (𝓞 E) (α * (θ s * ω s)) = k * k * ω.repr (α * ω s) s := by
      intro s
      have := h3 (ω.coord s) (α * ω s)
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      rw [← this, mul_comm (θ s), mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_sub, map_sub, Finset.mul_sum, map_sum, mul_comm α (_ : 𝓞 E), ← nsmul_eq_mul, map_nsmul,
      nsmul_eq_mul, hN, Algebra.trace_eq_matrix_trace ω α]
    simp only [h4, Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Finset.mul_sum, sub_self]

end GlobalTheory.PointStepCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAdd
section
namespace GlobalTheory.PrimeLogSum
open Finset

open Finset in
private lemma log_three_lt_one_point_one_one : Real.log 3 < 1.11 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp 0.11
  have h3 : Real.exp 1.11 = Real.exp 1 * Real.exp 0.11 := by
    rw [← Real.exp_add]; norm_num
  rw [h3]
  nlinarith

open Finset in
private lemma log_succ_div_le_telescoping_sub (n : ℕ) (hn : 3 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1))
      ≤ (Real.log n + 4 / 3) / n - (Real.log ((n + 1 : ℕ) : ℝ) + 4 / 3) / ((n + 1 : ℕ) : ℝ) := by
  push_cast
  set x : ℝ := (n : ℝ) with hx
  have hx3 : (3 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hd : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div (by positivity) hx0.ne'] at h
    have : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have h1 : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ (x + 1) * (1 / x) :=
    mul_le_mul_of_nonneg_left hd (by linarith)
  have h2 : (x + 1) * (1 / x) ≤ 4 / 3 := by
    rw [mul_one_div, div_le_iff₀ hx0]; linarith
  have key : Real.log (x + 1)
      ≤ (x + 1) * (Real.log x + 4 / 3) - x * (Real.log (x + 1) + 4 / 3) := by
    nlinarith
  have hpos : 0 < (x + 1) * x := by positivity
  calc Real.log (x + 1) / ((x + 1) * (x + 1 - 1))
      = Real.log (x + 1) / ((x + 1) * x) := by ring_nf
    _ ≤ ((x + 1) * (Real.log x + 4 / 3) - x * (Real.log (x + 1) + 4 / 3)) / ((x + 1) * x) :=
        div_le_div_of_nonneg_right key hpos.le
    _ = (Real.log x + 4 / 3) / x - (Real.log (x + 1) + 4 / 3) / (x + 1) := by
        field_simp

open Finset in
private lemma sum_log_div_mul_pred_add_le_const (N : ℕ) (hN : 3 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) + (Real.log N + 4 / 3) / N
      ≤ Real.log 2 / 2 + Real.log 3 / 6 + (Real.log 3 + 4 / 3) / 3 := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp [Finset.sum_range_succ]
    norm_num
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have := log_succ_div_le_telescoping_sub n hn
    linarith

open Finset in
private lemma div_le_factorization_factorial' (N p : ℕ) (hp : p.Prime) :
    N / p ≤ (N.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (lt_add_one (Nat.log p N))]
  rcases Nat.lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  · have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
      simp [Nat.log_pos hp.one_lt h]
    simpa using single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1

open Finset in
private lemma mul_sum_prime_log_div_le_log_factorial_add (N : ℕ) :
    (N : ℝ) * ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log (N.factorial : ℝ) + N * Real.log 4 := by
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hfac : Real.log (N.factorial : ℝ)
      = ∑ p ∈ P, ((N.factorial).factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization]
    apply Finsupp.sum_of_support_subset
    · intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      simp only [hP, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le ((hp.1.dvd_factorial).1 hp.2.1), hp.1⟩
    · intro i _
      simp
  have htheta : ∑ p ∈ P, Real.log p ≤ N * Real.log 4 := by
    rw [← Real.log_prod (fun p hp => by
      have := (Finset.mem_filter.1 hp).2.pos
      positivity), ← Real.log_pow]
    apply Real.log_le_log
    · exact Finset.prod_pos fun p hp => by
        have := (Finset.mem_filter.1 hp).2.pos
        positivity
    · have h := primorial_le_four_pow N
      have h' : ((primorial N : ℕ) : ℝ) ≤ ((4 ^ N : ℕ) : ℝ) := by exact_mod_cast h
      simpa [primorial, hP, Nat.cast_prod] using h'
  rw [Finset.mul_sum, hfac]
  calc ∑ p ∈ P, (N : ℝ) * (Real.log p / p)
      ≤ ∑ p ∈ P, (((N.factorial).factorization p : ℝ) * Real.log p + Real.log p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := (Finset.mem_filter.1 hp).2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        have hv : ((N / p : ℕ) : ℝ) ≤ ((N.factorial).factorization p : ℝ) := by
          exact_mod_cast div_le_factorization_factorial' N p hp'
        have hlt : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by
          exact_mod_cast Nat.lt_div_mul_add hp'.pos
        have hq : (N : ℝ) / p ≤ ((N.factorial).factorization p : ℝ) + 1 := by
          rw [div_le_iff₀ hp0]
          nlinarith
        calc (N : ℝ) * (Real.log p / p) = (N : ℝ) / p * Real.log p := by ring
          _ ≤ (((N.factorial).factorization p : ℝ) + 1) * Real.log p :=
            mul_le_mul_of_nonneg_right hq hlog
          _ = _ := by ring
    _ = ∑ p ∈ P, ((N.factorial).factorization p : ℝ) * Real.log p + ∑ p ∈ P, Real.log p :=
        Finset.sum_add_distrib
    _ ≤ _ := by linarith

open Finset in
private lemma log_factorial_le_stirling_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + 1 + Real.log n / 2 := by
  have h1 : Real.log (Stirling.stirlingSeq n) ≤ Real.log (Stirling.stirlingSeq 1) := by
    have := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (n - 1))
    simpa [Function.comp, Nat.sub_add_cancel hn] using this
  rw [Stirling.log_stirlingSeq_formula, Stirling.log_stirlingSeq_formula] at h1
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul (by norm_num) hn0, Real.log_div hn0 (Real.exp_pos 1).ne', Real.log_exp] at h1
  simp only [Nat.factorial_one, Nat.cast_one, mul_one, Real.log_one, one_div, Real.log_inv,
    Real.log_exp] at h1
  linarith [h1]


open Finset in
theorem _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le : ∀ N : ℕ,
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
      ≤ Real.log N + 2.2 := by
  intro N
  have hl2 := Real.log_two_lt_d9
  have hl3 := log_three_lt_one_point_one_one
  have hl3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rcases Nat.lt_or_ge N 4 with hN | hN
  · interval_cases N <;>
      simp [Finset.sum_filter, Finset.sum_range_succ, Nat.prime_two, Nat.prime_three] <;>
      norm_num <;> linarith
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hsplit : ∑ p ∈ P, Real.log p / ((p : ℝ) - 1)
      = ∑ p ∈ P, Real.log p / p + ∑ p ∈ P, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
    have h3 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h4 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hB : ∑ p ∈ P, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ n ∈ Finset.range (N + 1), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n _ _
    apply div_nonneg (Real.log_natCast_nonneg n)
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  have hC := sum_log_div_mul_pred_add_le_const N (by omega)
  have hg : 0 ≤ (Real.log N + 4 / 3) / N :=
    div_nonneg (by linarith [Real.log_natCast_nonneg N]) (Nat.cast_nonneg N)
  have hA := mul_sum_prime_log_div_le_log_factorial_add N
  have hF := log_factorial_le_stirling_bound N (by omega)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : Real.log N ≤ 0.4 * N := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / Real.exp 1 by positivity)
    rw [Real.log_div hNpos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    have he := Real.exp_one_gt_d9
    have h5 : (N : ℝ) / Real.exp 1 ≤ 0.4 * N := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      nlinarith
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hA' : ∑ p ∈ P, Real.log p / p ≤ Real.log N - 1 + 0.25 + 0.2 + Real.log 4 := by
    have h : (N : ℝ) * ∑ p ∈ P, Real.log p / p
        ≤ N * (Real.log N - 1 + 0.25 + 0.2 + Real.log 4) := by
      linarith
    exact le_of_mul_le_mul_left h hNpos
  rw [hsplit]
  linarith

end GlobalTheory.PrimeLogSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi
section
namespace GlobalTheory

open Module


open Module in
theorem _root_.GlobalTheory.ev_starProjection_eigenspace_eq_residue :
    ∀ (Y : Type) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (t : ℕ) (m : Fin t → ℂ) (s : ℂ) (Om : Module.End ℂ Y) (ev : Y →ₗ[ℂ] V) (K : ℂ → (Y →ₗ[ℂ] V)) (q : ℂ → ℂ) (y : Y) (v : V) (l : Fin t), Function.Injective m → Om.IsSymmetric → (∀ (lam : ℂ) (x : Y), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + s) → (∀ (u : ℂ) (x : Y), K u ((u - s) • x + Om x) = (∏ j, (u + m j)) • ev x) → Continuous q → (∀ u, K u y = q u • v) → ev ((Module.End.eigenspace Om (m l + s)).starProjection y) = (q (-m l) / ∏ j ∈ Finset.univ.erase l, (m j - m l)) • v := by
  intro Y _ _ _ V _ _ t m s Om ev K q y v l hm hOm hspec hK hq hKy
  set P : Fin t → Y → Y := fun j x => (Module.End.eigenspace Om (m j + s)).starProjection x with hP
  set c : Fin t → ℂ → ℂ := fun j u => ∏ k ∈ Finset.univ.erase j, (u + m k) with hc
  have key : ∀ x : Y, ∀ u : ℂ, (∏ k, (u + m k)) • K u x = (∏ k, (u + m k)) • ∑ j, c j u • ev (P j x) := by
    intro x u
    have hx : x ∈ ⨆ μ, Module.End.eigenspace Om μ := by
      rw [Submodule.orthogonal_eq_bot_iff.mp hOm.orthogonalComplement_iSup_eigenspaces_eq_bot]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (fun μ => Module.End.eigenspace Om μ) (motive := fun x => (∏ k, (u + m k)) • K u x = (∏ k, (u + m k)) • ∑ j, c j u • ev (P j x)) hx ?_ ?_ ?_
    · intro μ x hxμ
      by_cases hx0 : x = 0
      · subst hx0; simp [hP]
      have hOmx : Om x = μ • x := Module.End.mem_eigenspace_iff.mp hxμ
      obtain ⟨i, rfl⟩ := hspec μ x hx0 hOmx
      have hPx : ∀ j, P j x = if j = i then x else 0 := by
        intro j
        split_ifs with hji
        · subst hji; exact Submodule.starProjection_eq_self_iff.mpr hxμ
        · have hne : m j + s ≠ m i + s := fun h => hji (hm (add_right_cancel h))
          have hortho := hOm.orthogonalFamily_eigenspaces.isOrtho hne
          exact (Submodule.starProjection_apply_eq_zero_iff _).mpr (hortho.symm hxμ)
      have hsum : ∑ j, c j u • ev (P j x) = c i u • ev x := by
        rw [Finset.sum_eq_single i (fun j _ hji => by rw [hPx, if_neg hji, map_zero, smul_zero]) (by simp), hPx, if_pos rfl]
      have hKx : (u + m i) • K u x = (∏ k, (u + m k)) • ev x := by
        rw [← hK u x, hOmx, ← map_smul]
        congr 1
        rw [← add_smul]; congr 1; ring
      have hprod : ∏ k, (u + m k) = c i u * (u + m i) := by
        simp only [hc]; exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
      rw [hsum, smul_comm (∏ k, (u + m k)) (c i u), ← hKx, hprod, mul_smul]
    · simp [hP]
    · intro x₁ x₂ h₁ h₂
      simp only [hP] at h₁ h₂ ⊢
      simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, h₁, h₂]
  have hgen : ∀ u, ∏ k, (u + m k) ≠ 0 → q u • v = ∑ j, c j u • ev (P j y) := by
    intro u hu
    rw [← hKy]
    exact smul_right_injective V hu (key y u)
  have hdense : Dense {u : ℂ | ∏ k, (u + m k) ≠ 0} := by
    have hfin : {u : ℂ | ∏ k, (u + m k) = 0}.Countable := by
      apply Set.Finite.countable
      apply (Set.finite_range (fun k => -m k)).subset
      intro u hu
      simp only [Set.mem_setOf_eq, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hu
      obtain ⟨k, hk⟩ := hu
      exact ⟨k, by linear_combination -hk⟩
    simpa [Set.compl_setOf] using hfin.dense_compl ℝ
  have hcont : Continuous fun u => ∑ j, c j u • ev (P j y) := by
    simp only [hc]; fun_prop
  have hf : Continuous fun u => q u • v := hq.smul continuous_const
  have hl := congrFun (Continuous.ext_on hdense hf hcont hgen) (-m l)
  rw [Finset.sum_eq_single l (fun j _ hjl => by
    simp only [hc]
    rw [Finset.prod_eq_zero (i := l) (Finset.mem_erase.mpr ⟨Ne.symm hjl, Finset.mem_univ l⟩) (by ring), zero_smul]) (by simp)] at hl
  have hcl : c l (-m l) = ∏ j ∈ Finset.univ.erase l, (m j - m l) :=
    Finset.prod_congr rfl (fun k _ => by ring)
  have hD : ∏ j ∈ Finset.univ.erase l, (m j - m l) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => sub_ne_zero.mpr (hm.ne (Finset.ne_of_mem_erase hj)))
  rw [hcl] at hl
  change ev (P l y) = _
  rw [div_eq_inv_mul, mul_smul, hl, smul_smul, inv_mul_cancel₀ hD, one_smul]

end GlobalTheory
end

