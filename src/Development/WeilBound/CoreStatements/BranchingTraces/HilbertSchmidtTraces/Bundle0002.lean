module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HeBranching
public import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.IntegralGermIndependentOfSystem
section
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

def IntegralGermIndependentOfSystem : Prop := ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → ∀ {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)) (σ : Matrix (Fin r) (Fin r) ℂ → (B →L[ℂ] B)) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (ν : Measure (UJ ε')) [ν.IsHaarMeasure] (dπ dσ : ℝ), IsU (onU ε π) → IsU (onU ε' σ) → IsFd μ (onU ε π) dπ → IsFd ν (onU ε' σ) dσ → ∀ i : B →L[ℂ] A, IsIsoMap (onU ε' σ) (res ι π) i → ∀ (v₀ : A) (w : B), ‖v₀‖ = 1 → ‖w‖ = 1 → ∀ Y₁ K D : ℝ, 1 ≤ Y₁ → 0 < K → ∫⁻ g, ENNReal.ofReal (nsq (umat g⁻¹ *ᵥ z) * ‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ ≤ ENNReal.ofReal (Y₁ / 2) * ∫⁻ g, ENNReal.ofReal (‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ → ENNReal.ofReal dπ * μ {g | hs (umat g) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2} ≤ ENNReal.ofReal K → 1 / dσ ≤ D * ν.real (ball ε' 1) → ∃ g₀ : UJ ε, hs (umat g₀) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2 ∧ 1 ≤ 4 * D * K * ‖ContinuousLinearMap.adjoint i (π (umat g₀) v₀)‖ ^ 2

def EmbSt : Prop := (∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), Fits ε ε' e → ∃ ι : UJ ε' →* UJ ε, (∀ h, umat (ι h) = emb e (um h)) ∧ IsStdStab ε ε' ι (Pi.single (zi e) 1) ∧ ∀ h : Matrix (Fin n) (Fin n) ℂ, incl e * h * (incl e)ᴴ + vecMulVec (Pi.single (zi e) (1 : ℂ)) (star (Pi.single (zi e) (1 : ℂ) : Fin (n + 1) → ℂ)) = emb e h) ∧ (∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m), nsq (g *ᵥ Pi.single j 1) = colSq g j) ∧ (∀ {m : ℕ} (ε : Fin m → Bool) {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)), IsURepOn (UJset ε) π → IsU (onU ε π)) ∧ ∀ {m : ℕ} (ε : Fin m → Bool) (lam : Fin m → ℝ) {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] (π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)) (μ : Measure (UJ ε)), μ.IsHaarMeasure → IsHCParam lam → IsDS ε lam π → μ.IsMulRightInvariant ∧ (∃ d, IsFdeg μ π d ∧ IsFd μ (onU ε π) d) ∧ ∃ v ∈ lowKSub ε lam π, ‖v‖ = 1

theorem num_C {n : ℕ} {x : ℝ} (hn : 1 ≤ n) (hx : 3 ≤ x) (hnx : (n : ℝ) ≤ x) :
    Real.exp (6 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log n + 12 * ((n + 1 : ℕ) : ℝ) ^ 2) * (n : ℝ) ^ (12 * (n + 1) ^ 2) ≤
      x ^ (30 * (n + 1) ^ 2) := by
  have h0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ x := (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hx
  have e1 : Real.exp (6 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log n + 12 * ((n + 1 : ℕ) : ℝ) ^ 2) =
      (n : ℝ) ^ (6 * (n + 1) ^ 2) * Real.exp 1 ^ (12 * (n + 1) ^ 2) := by
    rw [Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_log (pow_pos h0 (6 * (n + 1) ^ 2)), Real.log_pow]
    push_cast
    rw [mul_one]
  rw [e1, show 30 * (n + 1) ^ 2 = 6 * (n + 1) ^ 2 + 12 * (n + 1) ^ 2 + 12 * (n + 1) ^ 2 by ring, pow_add x, pow_add x]
  gcongr

theorem num_D {n : ℕ} {x : ℝ} (hx : 16 ≤ x) (hnx : (n : ℝ) ≤ x) :
    (x ^ (30 * (n + 1) ^ 2)) ^ 2 * (2 * (16 * (n : ℝ) ^ 2) ^ (2 * n ^ 2)) ≤ x ^ (67 * (n + 1) ^ 2) := by
  have h1 : (1 : ℝ) ≤ x := by linarith
  have h2 : 16 * (n : ℝ) ^ 2 ≤ x ^ 3 := by
    rw [pow_succ' x 2]; gcongr
  calc _ ≤ (x ^ (30 * (n + 1) ^ 2)) ^ 2 * (x * (x ^ 3) ^ (2 * n ^ 2)) := by gcongr; linarith
    _ = x ^ (60 * (n + 1) ^ 2 + 1 + 6 * n ^ 2) := by rw [← pow_mul, ← pow_mul, ← pow_succ', ← pow_add]; congr 1; ring
    _ ≤ _ := pow_le_pow_right₀ h1 (by
      have a1 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have a2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)

theorem num_Y {N : ℕ} {x : ℝ} (hN : 1 ≤ N) (hx : 9 ≤ x) (hnx : (N : ℝ) ≤ x) :
    64 * (N : ℝ) * ((N : ℝ) + 2 * x ^ (8 * N)) ^ 2 ≤ x ^ (20 * N) := by
  have h1 : (1 : ℝ) ≤ x := by linarith
  have h2 : (N : ℝ) ≤ x ^ (8 * N) := hnx.trans (le_self_pow₀ h1 (by omega))
  calc _ ≤ x ^ 2 * x * (3 * x ^ (8 * N)) ^ 2 := by gcongr <;> nlinarith
    _ = 9 * x ^ (16 * N + 3) := by ring
    _ ≤ x * x ^ (16 * N + 3) := by gcongr
    _ = x ^ (16 * N + 4) := by ring
    _ ≤ _ := pow_le_pow_right₀ h1 (by omega)

theorem num_V {N : ℕ} {B x : ℝ} (hN : 3 ≤ N) (hB : 2 ≤ B) (hx : x = 8 * N * B) :
    (4 * N * (Real.sqrt N + 1) * x ^ (10 * N) / ((100 * N * (B + 1)) ^ 2)⁻¹) ^ (2 * N ^ 2) ≤ x ^ (24 * N ^ 3) := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 25 ≤ x := by rw [hx]; nlinarith
  have a1 : 4 * (N : ℝ) ≤ x := by rw [hx]; nlinarith
  have a2 : Real.sqrt N + 1 ≤ x := by
    have : Real.sqrt N ≤ N := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    linarith
  have a3 : 100 * N * (B + 1) ≤ x ^ 2 := by
    have : 100 * N * (B + 1) ≤ 25 * x := by rw [hx]; nlinarith
    nlinarith
  rw [div_inv_eq_mul]
  calc _ ≤ (x * x * x ^ (10 * N) * (x ^ 2) ^ 2) ^ (2 * N ^ 2) := by gcongr
    _ = x ^ ((10 * N + 6) * (2 * N ^ 2)) := by rw [pow_mul x (10 * N + 6)]; congr 1; ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by nlinarith [Nat.mul_le_mul_right (N ^ 2) hN])


end PositivityTheory.UnitaryDecomposition.X4
end
end

-- bundled from Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.IsFdAbs
section
open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

theorem hs_nonneg' {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hs a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem hs_mul_le' {m : ℕ} (a b : Matrix (Fin m) (Fin m) ℂ) : hs (a * b) ≤ hs a * hs b := by
  unfold hs
  rw [Finset.sum_comm (f := fun i j => ‖b i j‖ ^ 2), Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.mul_apply]
  refine (pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq ?_)) 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖a i k‖) fun k => ‖b k j‖)
  simp only [norm_mul]

theorem umat_inv' {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : umat g⁻¹ = Jm ε * (umat g)ᴴ * Jm ε := by
  have hg : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h1 : umat g * umat g⁻¹ = 1 := g.1.mul_inv
  calc umat g⁻¹ = Jm ε * ((umat g)ᴴ * Jm ε * umat g) * umat g⁻¹ := by rw [hg, Jm_mul_self, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem hs_inv' {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hs (umat g⁻¹) = hs (umat g) := by
  rw [umat_inv']
  unfold hs
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_star]
  split_ifs <;> simp

theorem hs_le_of_sub {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) : hs a ≤ 2 * hs (a - 1) + 2 * m := by
  have h1 : hs (1 : Matrix (Fin m) (Fin m) ℂ) = m := by
    unfold hs
    simp [Matrix.one_apply, apply_ite, Finset.sum_ite_eq]
  rw [← h1]
  unfold hs
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h : ‖a i j‖ ≤ ‖(a - 1) i j‖ + ‖(1 : Matrix (Fin m) (Fin m) ℂ) i j‖ := by
    refine le_trans (le_of_eq ?_) (norm_add_le _ _)
    simp
  nlinarith [norm_nonneg (a i j), norm_nonneg ((a - 1) i j), norm_nonneg ((1 : Matrix (Fin m) (Fin m) ℂ) i j),
    sq_nonneg (‖(a - 1) i j‖ - ‖(1 : Matrix (Fin m) (Fin m) ℂ) i j‖)]

theorem continuous_hs {X : Type} [TopologicalSpace X] {m : ℕ} {f : X → Matrix (Fin m) (Fin m) ℂ} (hf : Continuous f) :
    Continuous fun x => hs (f x) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hf.matrix_elem i j).norm.pow 2

theorem isU_adj {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {ρ : Γ → (A →L[ℂ] A)} (h : IsU ρ) (g : Γ) (x y : A) : ⟪x, ρ g y⟫_ℂ = ⟪ρ g⁻¹ x, y⟫_ℂ := by
  have hx : x = ρ g (ρ g⁻¹ x) := by
    rw [← ContinuousLinearMap.mul_apply, ← h.mul, mul_inv_cancel, h.one]; rfl
  conv_lhs => rw [hx]
  exact (LinearIsometry.mk (ρ g : A →ₗ[ℂ] A) (h.norm g)).inner_map_map _ y

theorem isFd_abs {Γ : Type} [MeasurableSpace Γ] {ν : Measure Γ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {ρ : Γ → (A →L[ℂ] A)} {d : ℝ} (h : IsFd ν ρ d) (x y : A) :
    ∫⁻ g, ENNReal.ofReal (‖⟪y, ρ g x⟫_ℂ‖ ^ 2) ∂ν = ENNReal.ofReal (‖x‖ ^ 2 * ‖y‖ ^ 2 / d) := by
  obtain ⟨hi, he⟩ := h.2 x y x y
  have hf : (fun g => ⟪y, ρ g x⟫_ℂ * star ⟪y, ρ g x⟫_ℂ) = fun g => ((‖⟪y, ρ g x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hf] at hi he
  have hi' : Integrable (fun g => ‖⟪y, ρ g x⟫_ℂ‖ ^ 2) ν := by simpa using hi.norm
  rw [← ofReal_integral_eq_lintegral_ofReal hi' (.of_forall fun _ => by positivity)]
  congr 1
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at he
  simp only [Complex.coe_algebraMap] at he
  exact_mod_cast he

theorem standard_stabiliser_bound (hst : ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → IsNormEmb ι ∧ (∀ h, hs (umat (ι h)) = hs (umat h) + 1) ∧ ∀ g : UJ ε, umat g *ᵥ z = z → ∃ h, ι h = g) (hbo : ∀ {n : ℕ} (ε : Fin n → Bool) (z y : Fin n → ℂ), star z ⬝ᵥ (Jm ε *ᵥ z) = 1 → nsq z = 1 → star y ⬝ᵥ (Jm ε *ᵥ y) = 1 → ∃ g : UJ ε, umat g *ᵥ z = y ∧ hs (umat g) ≤ 16 * ((n : ℝ) + nsq y) ^ 2) : ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → ∀ {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)) (σ : Matrix (Fin r) (Fin r) ℂ → (B →L[ℂ] B)) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (ν : Measure (UJ ε')) [ν.IsHaarMeasure] (dπ dσ : ℝ), IsU (onU ε π) → IsU (onU ε' σ) → IsFd μ (onU ε π) dπ → IsFd ν (onU ε' σ) dσ → ∀ i : B →L[ℂ] A, IsIsoMap (onU ε' σ) (res ι π) i → ∀ (v₀ : A) (w : B), ‖v₀‖ = 1 → ‖w‖ = 1 → ∀ Y₁ K D : ℝ, 1 ≤ Y₁ → 0 < K → ∫⁻ g, ENNReal.ofReal (nsq (umat g⁻¹ *ᵥ z) * ‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ ≤ ENNReal.ofReal (Y₁ / 2) * ∫⁻ g, ENNReal.ofReal (‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) ∂μ → ENNReal.ofReal dπ * μ {g | hs (umat g) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2} ≤ ENNReal.ofReal K → 1 / dσ ≤ D * ν.real (ball ε' 1) → ∃ g₀ : UJ ε, hs (umat g₀) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2 ∧ 1 ≤ 4 * D * K * ‖ContinuousLinearMap.adjoint i (π (umat g₀) v₀)‖ ^ 2 := by
  intro n r ε ε' ι z hz A B _ _ _ _ _ _ π σ μ _ ν _ dπ dσ hπ hσ fπ fσ i hi v₀ w hv hw Y₁ K D hY hK hM hV hD
  obtain ⟨⟨hc, hne⟩, -, hsur⟩ := hst ι z hz
  obtain ⟨Fr, hFr, -, -, hz1⟩ := hz
  have hn : (1 : ℝ) ≤ n := by have := hFr.codim; exact_mod_cast (by omega : 1 ≤ n)
  have cu : Continuous fun g : UJ ε => umat g := Formalism.MainNotions.BridgeCSchur.continuous_umat
  have cu' : Continuous fun g : UJ ε' => umat g := Formalism.MainNotions.BridgeCSchur.continuous_umat
  by_contra hcon
  push Not at hcon
  set P := ContinuousLinearMap.adjoint i with hP
  set F : UJ ε → ENNReal := fun g => ENNReal.ofReal (‖⟪i w, π (umat g) v₀⟫_ℂ‖ ^ 2) with hF
  have hFm : Measurable F := ((continuous_const.inner (hπ.cont v₀)).norm.pow 2).measurable.ennreal_ofReal
  set S : Set (UJ ε) := {g | nsq (umat g⁻¹ *ᵥ z) ≤ Y₁} with hS
  have cn : Continuous fun g : UJ ε => nsq (umat g⁻¹ *ᵥ z) :=
    continuous_finsetSum _ fun a _ => ((continuous_apply a).comp ((cu.comp continuous_inv).matrix_mulVec continuous_const)).norm.pow 2
  have hSm : MeasurableSet S := (isClosed_le cn continuous_const).measurableSet
  have hCm : MeasurableSet {g : UJ ε | hs (umat g) ≤ 64 * n * ((n : ℝ) + Y₁) ^ 2} :=
    (isClosed_le (continuous_hs cu) continuous_const).measurableSet
  have hUm : MeasurableSet (ball ε' 1) := (isClosed_le (continuous_hs (cu'.sub continuous_const)) continuous_const).measurableSet
  have hσ0 : 0 < 1 / dσ := one_div_pos.2 fσ.1
  have hU0 : 0 ≤ ν.real (ball ε' 1) := measureReal_nonneg
  have hDU : 0 < D * ν.real (ball ε' 1) := hσ0.trans_le hD
  have hUp : 0 < ν.real (ball ε' 1) := lt_of_le_of_ne hU0 fun e => by rw [← e, mul_zero] at hDU; exact lt_irrefl _ hDU
  have hD0 : 0 < D := (mul_pos_iff_of_pos_right hUp).1 hDU
  have hI : ∫⁻ g, F g ∂μ = ENNReal.ofReal (1 / dπ) := by
    have := isFd_abs fπ v₀ (i w)
    rwa [hv, hi.2, hw, one_pow, mul_one] at this
  have key := unfold μ ν ι hc F hFm S _ (ball ε' 1) hSm hCm hUm (fun g hg => ?_)
    (ENNReal.ofReal (1 / (4 * D * K) / dσ)) fun c hcC => ?_
  · have hsplit := lintegral_add_compl F (μ := μ) hSm
    have hb : ENNReal.ofReal Y₁ * ∫⁻ g in Sᶜ, F g ∂μ ≤ ENNReal.ofReal (Y₁ / 2) * ENNReal.ofReal (1 / dπ) := by
      rw [← hI]
      refine le_trans ?_ hM
      rw [← lintegral_const_mul _ hFm]
      refine le_trans (setLIntegral_mono' hSm.compl fun g hg => ?_) (setLIntegral_le_lintegral _ _)
      rw [hF, ← ENNReal.ofReal_mul (by linarith)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_of_lt (not_le.1 hg)) (by positivity))
    rw [hI] at hsplit
    have ta : ∫⁻ g in S, F g ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsplit ▸ le_self_add)
    have tb : ∫⁻ g in Sᶜ, F g ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsplit ▸ le_add_self)
    have hπ0 : 0 < 1 / dπ := one_div_pos.2 fπ.1
    have r1 := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add ta tb, ENNReal.toReal_ofReal hπ0.le] at r1
    have r2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hb
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal hπ0.le] at r2
    have r3 : 1 / dπ / 2 ≤ (∫⁻ g in S, F g ∂μ).toReal := by
      have : (∫⁻ g in Sᶜ, F g ∂μ).toReal ≤ 1 / dπ / 2 := le_of_mul_le_mul_left (by linarith) (by linarith : 0 < Y₁)
      linarith
    have k2 : ENNReal.ofReal dπ * (ν (ball ε' 1) * ∫⁻ g in S, F g ∂μ) ≤
        ENNReal.ofReal K * ENNReal.ofReal (1 / (4 * D * K) / dσ) :=
      (mul_le_mul_right key _).trans (by rw [← mul_assoc]; exact mul_le_mul_left hV _)
    have r4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) k2
    have hp : 0 ≤ 1 / (4 * D * K) / dσ := div_nonneg (by positivity) fσ.1.le
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal fπ.1.le,
      ENNReal.toReal_ofReal hK.le, ENNReal.toReal_ofReal hp] at r4
    have r5 : K * (1 / (4 * D * K) / dσ) = 1 / dσ / (4 * D) := by have := fσ.1; field_simp
    have r6 : 1 / dσ / (4 * D) ≤ ν.real (ball ε' 1) / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have r7 : ν.real (ball ε' 1) / 2 ≤ dπ * (ν.real (ball ε' 1) * (∫⁻ g in S, F g ∂μ).toReal) := by
      calc ν.real (ball ε' 1) / 2 = dπ * (ν.real (ball ε' 1) * (1 / dπ / 2)) := by have := fπ.1; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left r3 hU0) fπ.1.le
    have r8 : (ν (ball ε' 1)).toReal = ν.real (ball ε' 1) := rfl
    rw [r8, r5] at r4
    linarith
  · have hy : star (umat g⁻¹ *ᵥ z) ⬝ᵥ (Jm ε *ᵥ (umat g⁻¹ *ᵥ z)) = 1 := by
      have hg' : (umat g⁻¹)ᴴ * Jm ε * umat g⁻¹ = Jm ε := (g⁻¹).2
      rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, hg', hFr.one]
    obtain ⟨gy, hgy, hgn⟩ := hbo ε z _ hFr.one hz1 hy
    obtain ⟨h₀, hh⟩ := hsur (g * gy) (by
      have e1 : umat (g * gy) = umat g * umat gy := rfl
      have e2 : umat g * umat g⁻¹ = 1 := g.1.mul_inv
      rw [e1, ← mulVec_mulVec, hgy, mulVec_mulVec, e2, one_mulVec])
    refine ⟨h₀, fun u hu => ?_⟩
    have e : (ι (h₀ * u))⁻¹ * g = (ι u)⁻¹ * gy⁻¹ := by rw [map_mul, hh]; group
    show hs (umat _) ≤ _
    rw [e, show umat ((ι u)⁻¹ * gy⁻¹) = umat (ι u)⁻¹ * umat gy⁻¹ from rfl]
    refine (hs_mul_le' _ _).trans ?_
    rw [hs_inv', hs_inv']
    have b1 : hs (umat (ι u)) ≤ 4 * n := by
      have := hs_le_of_sub (umat (ι u))
      have h2 : hs (umat u - 1) ≤ 1 ^ 2 := hu
      rw [hne] at this
      linarith
    have n0 : 0 ≤ nsq (umat g⁻¹ *ᵥ z) := Finset.sum_nonneg fun _ _ => by positivity
    have b2 : hs (umat gy) ≤ 16 * ((n : ℝ) + Y₁) ^ 2 :=
      hgn.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by have : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (umat g⁻¹ *ᵥ z) ≤ Y₁ := hg; linarith) 2) (by norm_num))
    calc _ ≤ 4 * n * (16 * ((n : ℝ) + Y₁) ^ 2) := mul_le_mul b1 b2 (hs_nonneg' _) (by linarith)
      _ = _ := by ring
  · have e : ∀ h : UJ ε', F (ι h * c) = ENNReal.ofReal (‖⟪w, onU ε' σ h (P (π (umat c) v₀))⟫_ℂ‖ ^ 2) := fun h => by
      have a1 : π (umat (ι h * c)) v₀ = onU ε π (ι h) (π (umat c) v₀) := DFunLike.congr_fun (hπ.mul (ι h) c) v₀
      have a2 : onU ε π (ι h)⁻¹ (i w) = i (onU ε' σ h⁻¹ w) := by rw [← map_inv]; exact (hi.1 h⁻¹ w).symm
      simp only [hF]
      rw [a1, isU_adj hπ, a2, isU_adj hσ, hP, ContinuousLinearMap.adjoint_inner_right]
    simp only [e]
    rw [isFd_abs fσ, hw, one_pow, mul_one]
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ fσ.1.le)
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact (hcon c hcC).le

end PositivityTheory.UnitaryDecomposition.X4
end

-- bundled from Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.ReflEx
section
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

private theorem star_dotProduct_Jm_mulVec_comm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n → ℂ) :
    star (star a ⬝ᵥ (Jm ε *ᵥ b)) = star b ⬝ᵥ (Jm ε *ᵥ a) := by
  simp only [Jm, dotProduct, mulVec_diagonal, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

theorem refl_ex {n : ℕ} (ε : Fin n → Bool) (z y : Fin n → ℂ) (hz : star z ⬝ᵥ (Jm ε *ᵥ z) = 1) (hy : star y ⬝ᵥ (Jm ε *ᵥ y) = 1)
    (c : ℝ) (hc : c ≤ 0) (hyz : star y ⬝ᵥ (Jm ε *ᵥ z) = c) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, inUJ ε R ∧ R *ᵥ z = y ∧ hs R ≤ 2 * n + 2 * nsq (y - z) ^ 2 := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : Fin n → ℂ, w = y - z := ⟨_, rfl⟩
  rw [← hw]
  have hzy : star z ⬝ᵥ (Jm ε *ᵥ y) = c := by
    rw [← star_dotProduct_Jm_mulVec_comm, hyz, Complex.star_def, Complex.conj_ofReal]
  have hq : star w ⬝ᵥ (Jm ε *ᵥ w) = 2 - 2 * (c : ℂ) := by
    rw [hw, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hy, hz, hyz, hzy]
    ring
  have hwz : star w ⬝ᵥ (Jm ε *ᵥ z) = c - 1 := by
    rw [hw, star_sub, sub_dotProduct, hyz, hz]
  have hpos : (0 : ℝ) < 2 - 2 * c := by linarith
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = 2 / (2 - 2 * c) := ⟨_, rfl⟩
  have hk : k * (2 - 2 * c) = 2 := by rw [hkdef, div_mul_cancel₀ _ (ne_of_gt hpos)]
  have hk0 : 0 < k := by rw [hkdef]; exact div_pos (by norm_num) hpos
  have hk1 : k ≤ 1 := by nlinarith
  have hkC : (k : ℂ) * (2 - 2 * (c : ℂ)) = 2 := by exact_mod_cast hk
  have hq' : (star w ᵥ* Jm ε) ⬝ᵥ w = 2 - 2 * (c : ℂ) := by rw [← dotProduct_mulVec, hq]
  have hbj : ∀ j, ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖ ^ 2 = k ^ 2 * ‖w j‖ ^ 2 := by
    intro j
    simp only [Pi.smul_apply, smul_eq_mul, Jm, vecMul_diagonal, norm_mul, Pi.star_apply, norm_star,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0]
    split_ifs <;> simp <;> ring
  have h1 : ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = n := by
    simp [Matrix.one_apply, apply_ite]
  have h2 : ∑ i : Fin n, ∑ j : Fin n, ‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2) = k ^ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2 := by
    simp only [GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  refine ⟨1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)), ?_, ?_, ?_⟩
  · show (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)))ᴴ * Jm ε * (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε))) = Jm ε
    have hsb : star ((k : ℂ) • (star w ᵥ* Jm ε)) = (k : ℂ) • (Jm ε *ᵥ w) := by
      rw [star_smul, Matrix.star_vecMul, star_star, Jm_conjTranspose, Complex.star_def, Complex.conj_ofReal]
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_vecMulVec, hsb]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.vecMulVec_mul,
      Matrix.mul_vecMulVec, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, hq']
    ext i j
    simp only [Matrix.sub_apply, vecMulVec_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination ((k : ℂ) * ((Jm ε *ᵥ w) i * (star w ᵥ* Jm ε) j)) * hkC
  · have hkc : (k : ℂ) * ((c : ℂ) - 1) = -1 := by linear_combination (-1 / 2 : ℂ) * hkC
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_dotProduct,
      ← dotProduct_mulVec, hwz, smul_eq_mul, hkc, hw]
    ext i
    simp
  · calc hs (1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε)))
        = ∑ i, ∑ j, ‖(1 - vecMulVec w ((k : ℂ) • (star w ᵥ* Jm ε))) i j‖ ^ 2 := rfl
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (2 * ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
            + 2 * (‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2))) := by
        gcongr with i _ j _
        rw [Matrix.sub_apply, vecMulVec_apply]
        have h3 := norm_sub_le ((1 : Matrix (Fin n) (Fin n) ℂ) i j) (w i * ((k : ℂ) • (star w ᵥ* Jm ε)) j)
        rw [norm_mul] at h3
        have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        have hp : (‖w i‖ * ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖) ^ 2 = ‖w i‖ ^ 2 * (k ^ 2 * ‖w j‖ ^ 2) := by
          rw [mul_pow, hbj]
        nlinarith [sq_nonneg (‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ - ‖w i‖ * ‖((k : ℂ) • (star w ᵥ* Jm ε)) j‖)]
      _ = 2 * n + 2 * (k ^ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2) := by
        rw [← h1, ← h2]
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * n + 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w ^ 2 := by
        have hk2 : k ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hk2 (sq_nonneg (GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq w))]

private theorem nsq_sub_le_two_mul_add {n : ℕ} (a b : Fin n → ℂ) :
    GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (a - b) ≤ 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq a + 2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq b := by
  unfold GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  gcongr with i _
  simp only [Pi.sub_apply]
  have h := norm_sub_le (a i) (b i)
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]

private theorem nsq_nonneg_hilbert_schmidt_traces {n : ℕ} (a : Fin n → ℂ) : 0 ≤ GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq a :=
  Finset.sum_nonneg fun i _ => by positivity

theorem boost : ∀ {n : ℕ} (ε : Fin n → Bool) (z y : Fin n → ℂ), star z ⬝ᵥ (Jm ε *ᵥ z) = 1 → nsq z = 1 → star y ⬝ᵥ (Jm ε *ᵥ y) = 1 → ∃ g : UJ ε, umat g *ᵥ z = y ∧ hs (umat g) ≤ 16 * ((n : ℝ) + nsq y) ^ 2 := by
  classical
  intro n ε z y hz hnz hy
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hz
    · exact h
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = star y ⬝ᵥ (Jm ε *ᵥ z) := ⟨_, rfl⟩
  obtain ⟨u, hu1, hua⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ star u * a = -(‖a‖ : ℂ) := by
    by_cases h0 : a = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · have hn0 : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      have hsq : star a * a = (‖a‖ : ℂ) ^ 2 := by rw [Complex.star_def, Complex.conj_mul']
      refine ⟨-(a / (‖a‖ : ℂ)), ?_, ?_⟩
      · rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          div_self (norm_ne_zero_iff.mpr h0)]
      · rw [star_neg, star_div₀, Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, neg_mul,
          div_mul_eq_mul_div, hsq, sq, mul_div_assoc, div_self hn0, mul_one]
  have hu2 : star u * u = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hu1]
    simp
  have hy' : star (u • y) ⬝ᵥ (Jm ε *ᵥ (u • y)) = 1 := by
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hy, smul_eq_mul,
      smul_eq_mul, mul_one, hu2]
  have hyz' : star (u • y) ⬝ᵥ (Jm ε *ᵥ z) = ((-‖a‖ : ℝ) : ℂ) := by
    rw [star_smul, smul_dotProduct, ← ha, smul_eq_mul, hua]
    push_cast
    ring
  obtain ⟨R, hR, hRz, hRs⟩ := refl_ex ε z (u • y) hz hy' (-‖a‖) (by simp) hyz'
  have hR' : Rᴴ * Jm ε * R = Jm ε := hR
  have hg : (star u • R)ᴴ * Jm ε * (star u • R) = Jm ε := by
    rw [conjTranspose_smul, star_star]
    simp only [Matrix.smul_mul, Matrix.mul_smul, hR', smul_smul]
    rw [hu2, one_smul]
  have hinv : (Jm ε * (star u • R)ᴴ * Jm ε) * (star u • R) = 1 := by
    rw [show Jm ε * (star u • R)ᴴ * Jm ε * (star u • R)
        = Jm ε * ((star u • R)ᴴ * Jm ε * (star u • R)) by simp only [Matrix.mul_assoc], hg, Jm_mul_self]
  refine ⟨⟨⟨star u • R, Jm ε * (star u • R)ᴴ * Jm ε, mul_eq_one_comm.mp hinv, hinv⟩, hg⟩, ?_, ?_⟩
  · show (star u • R) *ᵥ z = y
    rw [Matrix.smul_mulVec, hRz, smul_smul, hu2, one_smul]
  · show hs (star u • R) ≤ 16 * ((n : ℝ) + GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y) ^ 2
    have hsu : hs (star u • R) = hs R := by
      simp [hs, Matrix.smul_apply, norm_mul, norm_star, hu1]
    have hnu : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (u • y) = GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y := by
      simp [GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq, norm_mul, hu1]
    have hD := nsq_sub_le_two_mul_add (u • y) z
    rw [hnu, hnz] at hD
    have hD0 := nsq_nonneg_hilbert_schmidt_traces (u • y - z)
    have hs0 := nsq_nonneg_hilbert_schmidt_traces y
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (u • y - z) ^ 2 ≤ (2 * GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq y + 2 * 1) ^ 2 :=
      pow_le_pow_left₀ hD0 hD 2
    rw [hsu]
    nlinarith

end PositivityTheory.UnitaryDecomposition.X4
end
end

