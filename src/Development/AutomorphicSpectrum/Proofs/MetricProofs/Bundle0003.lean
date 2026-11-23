module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalNormOutsideFiniteSet
section
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.LogLin

theorem exists_log_affine_le : ∀ C n K : ℝ, 0 ≤ C → 0 ≤ n → 0 ≤ K → ∃ C₁ : ℝ, 1 ≤ C₁ ∧ K ≤ C₁ ∧ ∀ x y : ℝ, -K ≤ x → y ≤ n * x + C → C * Real.log (2 + C + max y 0) + C ≤ C₁ * Real.log (2 + C₁ + x) := by
  intro C n K hC hn hK
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 + 2 * C + n := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; linarith
  have hCA : 0 ≤ C * A := mul_nonneg hC hA0.le
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 1 + K + C + 2 * (C * A + C) := ⟨_, rfl⟩
  refine ⟨D, by rw [hD]; linarith, by rw [hD]; linarith, ?_⟩
  intro x y hx hy
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 + D + x := ⟨_, rfl⟩
  rw [← hu]
  have ht : 0 ≤ x + K := by linarith
  have hut : 2 + (x + K) ≤ u := by rw [hu, hD]; linarith
  have hu2 : 2 ≤ u := by linarith
  have hnK : 0 ≤ n * K := mul_nonneg hn hK
  have hnt : 0 ≤ n * (x + K) := mul_nonneg hn ht
  have hmax : max y 0 ≤ n * (x + K) + C := max_le (by nlinarith) (by linarith)
  have hm0 : 0 ≤ max y 0 := le_max_right _ _
  have h1 : n * (x + K) ≤ n * u := mul_le_mul_of_nonneg_left (by linarith) hn
  have h2 : C * 1 ≤ C * u := mul_le_mul_of_nonneg_left (by linarith) hC
  have hle : 2 + C + max y 0 ≤ A * u := by rw [hA]; nlinarith
  have hlog : Real.log (2 + C + max y 0) ≤ Real.log A + Real.log u := by
    rw [← Real.log_mul hA0.ne' (by linarith)]
    exact Real.log_le_log (by linarith) hle
  have hlA : Real.log A ≤ A := (Real.log_le_sub_one_of_pos hA0).trans (by linarith)
  have hlu : 1 / 2 ≤ Real.log u := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 2) hu2
    have h' := Real.log_two_gt_d9
    linarith
  have h3 : C * Real.log (2 + C + max y 0) ≤ C * (A + Real.log u) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have h4 : 2 * (C * A + C) * (1 / 2) ≤ 2 * (C * A + C) * Real.log u :=
    mul_le_mul_of_nonneg_left hlu (by linarith)
  have h5 : 0 ≤ (1 + K) * Real.log u := mul_nonneg (by linarith) (by linarith)
  rw [hD]
  nlinarith

end GlobalTheory.CompanionTheory.LogLin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MulVecEqZeroOfPair
section
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.PeriodLimit

theorem sq_mul_sum_sq_le {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) {c : ℝ} (hc : 0 < c)
    (h : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) (v : Fin g → ℝ) :
    c ^ 2 * ∑ k, v k ^ 2 ≤ ∑ k, (Y *ᵥ v) k ^ 2 := by
  have h1 := h.dotProduct_mulVec_nonneg v
  rw [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul] at h1
  have h2 : 0 ≤ ∑ k, (c * v k - (Y *ᵥ v) k) ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h3 : ∑ k, (c * v k - (Y *ᵥ v) k) ^ 2
      = c ^ 2 * ∑ k, v k ^ 2 - 2 * c * (v ⬝ᵥ (Y *ᵥ v)) + ∑ k, (Y *ᵥ v) k ^ 2 := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h4 : v ⬝ᵥ v = ∑ k, v k ^ 2 := by simp [dotProduct, sq]
  rw [h4, smul_eq_mul] at h1
  nlinarith [mul_nonneg hc.le h1]

theorem coord_eq {a g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (l : Fin a → ℂ) (v : Fin g → ℤ) (k : Fin g) :
    2 * Real.pi * Complex.I * (((T + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k)
      = 2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v k : ℂ))) k
        + ∑ j, (((B j *ᵥ v) k : ℤ) : ℂ) * l j := by
  have h : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  rw [add_mulVec, sum_mulVec, Pi.add_apply, mul_add, Finset.sum_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mulVec, Pi.smul_apply, smul_eq_mul]
  have : (((B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k
      = (((B j *ᵥ v) k : ℤ) : ℂ) := by
    simp [mulVec, dotProduct]
  rw [this]
  field_simp

theorem exp_coord_eq {a g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (l : Fin a → ℂ) (u v : Fin g → ℤ) (k : Fin g) :
    Complex.exp (2 * Real.pi * Complex.I * (((fun k => (u k : ℂ)) +
        (T + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k))
      = Complex.exp (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v k : ℂ))) k)
        * ∏ j, Complex.exp (l j) ^ ((B j *ᵥ v) k) := by
  rw [Pi.add_apply, mul_add, coord_eq, Complex.exp_add, Complex.exp_add, mul_comm _ (u k : ℂ),
    Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_sum]
  simp only [Complex.exp_int_mul]

theorem exp_pair_eq {a g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (l : Fin a → ℂ) (u v : Fin g → ℤ) :
    Complex.exp (∑ k, (v k : ℂ) * (2 * Real.pi * Complex.I * (((fun k => (u k : ℂ)) +
        (T + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k)))
      = Complex.exp (∑ k, (v k : ℂ) *
          (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v k : ℂ))) k))
        * ∏ j, Complex.exp (l j) ^ (v ⬝ᵥ (B j *ᵥ v)) := by
  simp only [Complex.exp_sum, Complex.exp_int_mul, exp_coord_eq, mul_zpow,
    Finset.prod_mul_distrib]
  congr 1
  simp only [← Finset.prod_zpow, ← _root_.zpow_mul, ← Complex.exp_int_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Complex.exp_sum]
  congr 1
  simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem cast_pair {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    star (fun k => (v k : ℝ)) ⬝ᵥ ((B.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun k => (v k : ℝ)))
      = ((v ⬝ᵥ (B *ᵥ v) : ℤ) : ℝ) := by
  simp [mulVec, dotProduct]

theorem pair_nonneg {g : ℕ} {B : Matrix (Fin g) (Fin g) ℤ}
    (h : (B.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) : 0 ≤ v ⬝ᵥ (B *ᵥ v) := by
  have := h.dotProduct_mulVec_nonneg (fun k => (v k : ℝ))
  rw [cast_pair] at this
  exact_mod_cast this

theorem mulVec_eq_zero_of_pair {g : ℕ} {B : Matrix (Fin g) (Fin g) ℤ}
    (h : (B.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) (h0 : v ⬝ᵥ (B *ᵥ v) = 0) :
    B *ᵥ v = 0 := by
  have := (h.dotProduct_mulVec_zero_iff (x := fun k => (v k : ℝ))).1
    (by rw [cast_pair, h0]; simp)
  ext k
  have h1 := congrFun this k
  have h2 : ((B.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun k => (v k : ℝ))) k
      = (((B *ᵥ v) k : ℤ) : ℝ) := by
    simp [mulVec, dotProduct]
  rw [h2, Pi.zero_apply] at h1
  exact_mod_cast h1

theorem finite_sum_sq_le {g : ℕ} (M : ℝ) :
    {v : Fin g → ℤ | ∑ k, (v k : ℝ) ^ 2 ≤ M}.Finite := by
  refine (Set.Finite.pi' (fun _ : Fin g => Set.finite_Icc (-⌈M⌉) ⌈M⌉)).subset ?_
  intro v hv k
  have h1 : (v k : ℝ) ^ 2 ≤ M :=
    (Finset.single_le_sum (f := fun k => (v k : ℝ) ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ k)).trans hv
  have h2 : v k ^ 2 ≤ ⌈M⌉ := by
    have := h1.trans (Int.le_ceil M)
    exact_mod_cast this
  constructor <;> nlinarith [sq_nonneg (v k), sq_nonneg (2 * v k - 1), sq_nonneg (2 * v k + 1), Int.le_self_sq (v k), Int.le_self_sq (-v k)]

theorem im_period {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℤ) (k : Fin g) :
    ((A.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k
      = ((((fun k => (u k : ℂ)) + A *ᵥ (fun k => (v k : ℂ)) : Fin g → ℂ)) k).im := by
  simp [mulVec, dotProduct]

theorem limit_period : ∀ (n a g : ℕ) (ha : a ≤ n) (U : Set (Fin n → ℂ)) (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c : ℝ), IsOpen U → ContinuousOn τ0 U → (∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) → 0 < c → (∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, Complex.exp (l j) = z (Fin.castLE ha j)) → ((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → ∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, z (Fin.castLE ha j) ≠ 0 → Complex.exp (l j) = z (Fin.castLE ha j)) → (∀ j, z (Fin.castLE ha j) = 0 → l j = 0) → ∀ w : Fin g → ℂ, (z, w) ∈ closure {p : (Fin n → ℂ) × (Fin g → ℂ) | p.1 ∈ U ∧ ∃ (l' : Fin a → ℂ) (u v : Fin g → ℤ), (∀ j, Complex.exp (l' j) = p.1 (Fin.castLE ha j)) ∧ p.2 = (fun k => (u k : ℂ)) + (τ0 p.1 + ∑ j, (l' j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))} → ∃ u v : Fin g → ℤ, (∀ j, z (Fin.castLE ha j) = 0 → B j *ᵥ v = 0) ∧ w = (fun k => (u k : ℂ)) + (τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ)) := by
  intro n a g ha U τ0 B c hU hτ hB hc hY z hz l hl hl0 w hw
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.1 hw
  choose hpU l' u v hl' hpw using hp
  have hz' : Tendsto (fun m => (p m).1) atTop (𝓝 z) := (continuous_fst.tendsto _).comp hlim
  have hw' : Tendsto (fun m => (p m).2) atTop (𝓝 w) := (continuous_snd.tendsto _).comp hlim
  have hτ' : Tendsto (fun m => τ0 (p m).1) atTop (𝓝 (τ0 z)) :=
    ((hτ.continuousAt (hU.mem_nhds hz)).tendsto).comp hz'

  have hbd : ∀ m, c ^ 2 * ∑ k, (v m k : ℝ) ^ 2 ≤ ∑ k, ((p m).2 k).im ^ 2 := by
    intro m
    have := sq_mul_sum_sq_le _ hc (hY _ (hpU m) (l' m) (hl' m)) (fun k => (v m k : ℝ))
    simp only [im_period _ (u m)] at this
    rw [← hpw m] at this
    exact this
  have hcont : Continuous fun x : Fin g → ℂ => ∑ k, (x k).im ^ 2 := by fun_prop
  obtain ⟨M, hM⟩ := ((hcont.tendsto w).comp hw').bddAbove_range
  have hfin : ∀ m, v m ∈ {v : Fin g → ℤ | ∑ k, (v k : ℝ) ^ 2 ≤ M / c ^ 2} := by
    intro m
    rw [Set.mem_setOf_eq, le_div_iff₀ (by positivity), mul_comm]
    exact (hbd m).trans (hM ⟨m, rfl⟩)
  obtain ⟨v0, hv0⟩ : ∃ v0, ∃ᶠ m in atTop, v m = v0 := by
    have h1 : ∃ᶠ m in atTop, ∃ v0 ∈ {v : Fin g → ℤ | ∑ k, (v k : ℝ) ^ 2 ≤ M / c ^ 2}, v m = v0 :=
      Frequently.of_forall fun m => ⟨v m, hfin m, rfl⟩
    obtain ⟨v0, -, h⟩ := (frequently_exists_finite (finite_sum_sq_le _)).1 h1
    exact ⟨v0, h⟩
  obtain ⟨φ, hφ, hφv⟩ := extraction_of_frequently_atTop hv0
  have hz2 := hz'.comp hφ.tendsto_atTop
  have hw2 := hw'.comp hφ.tendsto_atTop
  have hτ2 := hτ'.comp hφ.tendsto_atTop
  have hzj : ∀ j : Fin a, Tendsto (fun m => (p (φ m)).1 (Fin.castLE ha j)) atTop
      (𝓝 (z (Fin.castLE ha j))) := fun j => ((continuous_apply _).tendsto _).comp hz2

  have hpair : Complex.exp (∑ k, (v0 k : ℂ) * (2 * Real.pi * Complex.I * w k))
      = Complex.exp (∑ k, (v0 k : ℂ) *
          (2 * Real.pi * Complex.I * (τ0 z *ᵥ (fun k => (v0 k : ℂ))) k))
        * ∏ j, z (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0)) := by
    have c1 : Continuous fun x : Fin g → ℂ =>
        Complex.exp (∑ k, (v0 k : ℂ) * (2 * Real.pi * Complex.I * x k)) := by fun_prop
    have c2 : Continuous fun T : Matrix (Fin g) (Fin g) ℂ => Complex.exp (∑ k, (v0 k : ℂ) *
          (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v0 k : ℂ))) k)) := by
      simp only [mulVec, dotProduct]; fun_prop
    have t3 : Tendsto (fun m => ∏ j, (p (φ m)).1 (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0))) atTop
        (𝓝 (∏ j, z (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0)))) := by
      refine tendsto_finsetProd _ fun j _ => ?_
      obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (pair_nonneg (hB j) v0)
      simp only [hb, zpow_natCast]
      exact (hzj j).pow b
    refine tendsto_nhds_unique ((c1.tendsto w).comp hw2)
      ((((c2.tendsto _).comp hτ2).mul t3).congr fun m => ?_)
    simp only [Function.comp]
    rw [hpw (φ m), hφv m, exp_pair_eq]
    simp only [hl']
  have hker : ∀ j, z (Fin.castLE ha j) = 0 → B j *ᵥ v0 = 0 := by
    intro j hj
    refine mulVec_eq_zero_of_pair (hB j) v0 ?_
    by_contra hne
    have : ∏ j, z (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, _root_.zero_zpow _ hne])
    rw [this, mul_zero] at hpair
    exact Complex.exp_ne_zero _ hpair

  have hcoord : ∀ k, Complex.exp (2 * Real.pi * Complex.I * w k)
      = Complex.exp (2 * Real.pi * Complex.I * (τ0 z *ᵥ (fun k => (v0 k : ℂ))) k)
        * ∏ j, Complex.exp (l j) ^ ((B j *ᵥ v0) k) := by
    intro k
    have c1 : Continuous fun x : Fin g → ℂ =>
        Complex.exp (2 * Real.pi * Complex.I * x k) := by fun_prop
    have c2 : Continuous fun T : Matrix (Fin g) (Fin g) ℂ =>
        Complex.exp (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v0 k : ℂ))) k) := by
      simp only [mulVec, dotProduct]; fun_prop
    have t3 : Tendsto (fun m => ∏ j, (p (φ m)).1 (Fin.castLE ha j) ^ ((B j *ᵥ v0) k)) atTop
        (𝓝 (∏ j, Complex.exp (l j) ^ ((B j *ᵥ v0) k))) := by
      refine tendsto_finsetProd _ fun j _ => ?_
      by_cases hj : z (Fin.castLE ha j) = 0
      · simp [hker j hj]
      · rw [hl j hj]
        exact (hzj j).zpow₀ _ (Or.inl hj)
    refine tendsto_nhds_unique ((c1.tendsto w).comp hw2)
      ((((c2.tendsto _).comp hτ2).mul t3).congr fun m => ?_)
    simp only [Function.comp]
    rw [hpw (φ m), hφv m, exp_coord_eq]
    simp only [hl']
  have hint : ∀ k, ∃ N : ℤ, w k = N + ((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
      (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v0 k : ℂ))) k := by
    intro k
    have h1 := hcoord k
    rw [← exp_coord_eq _ _ _ 0, Complex.exp_eq_exp_iff_exists_int] at h1
    obtain ⟨N, hN⟩ := h1
    refine ⟨N, mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
    rw [hN]
    simp only [Pi.add_apply, Pi.zero_apply, Int.cast_zero, zero_add]
    ring
  choose u0 hu0 using hint
  exact ⟨u0, v0, hker, funext hu0⟩

end GlobalTheory.CompanionTheory.PeriodLimit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProdIicBlockDiagDetFactors
section
open Matrix

namespace GlobalTheory.CompanionTheory.Metric.GradedLines

theorem prod_Iic_eq_prod_castLE {Φ : Type} [CommMonoid Φ] {N : ℕ} (G : Fin N → Φ)
    (i : Fin N) (n : ℕ) (hn : n ≤ N) (hin : n = (i : ℕ) + 1) :
    ∏ k ∈ Finset.Iic i, G k = ∏ l : Fin n, G (Fin.castLE hn l) := by
  symm
  refine Finset.prod_bij (fun l _ => Fin.castLE hn l) ?_ ?_ ?_ ?_
  · intro l _
    have := l.2
    simp only [Finset.mem_Iic, Fin.le_def, Fin.val_castLE]
    omega
  · intro a _ b _ hab
    exact Fin.castLE_injective hn hab
  · intro b hb
    have hb' : (b : ℕ) ≤ (i : ℕ) := Fin.le_def.mp (Finset.mem_Iic.mp hb)
    refine ⟨⟨(b : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩
    ext
    simp
  · intro _ _
    rfl

theorem prod_first_graded_lines :
    ∀ (Φ : Type) [CommMonoid Φ] (p q : ℕ) (tW : Fin p → Φ) (tO : Fin q → Φ) (G : Fin (p + q) → Φ), (∀ (i : Fin (p + q)) (h : (i : ℕ) < p), G i = tW ⟨i, h⟩) → (∀ (i : Fin (p + q)) (h : p ≤ (i : ℕ)), G i = tO ⟨(i : ℕ) - p, by have := i.2; omega⟩) → ∀ i : Fin (p + q), (∀ h : (i : ℕ) < p, ∏ k ∈ Finset.Iic i, G k = ∏ l : Fin ((i : ℕ) + 1), tW (Fin.castLE h l)) ∧ (∀ h : p ≤ (i : ℕ), ∏ k ∈ Finset.Iic i, G k = (∏ l, tW l) * ∏ l : Fin ((i : ℕ) - p + 1), tO (Fin.castLE (by have := i.2; omega) l)) := by
  intro Φ _ p q tW tO G h1 h2 i
  constructor
  · intro h
    rw [prod_Iic_eq_prod_castLE G i ((i : ℕ) + 1) (by have := i.2; omega) rfl]
    refine Finset.prod_congr rfl fun l _ => ?_
    have hl : ((Fin.castLE (by have := i.2; omega) l : Fin (p + q)) : ℕ) < p := by
      have := l.2
      simp only [Fin.val_castLE]
      omega
    rw [h1 _ hl]
    rfl
  · intro h
    have hi := i.2
    rw [prod_Iic_eq_prod_castLE G i (p + ((i : ℕ) - p + 1)) (by omega) (by omega),
      Fin.prod_univ_add]
    congr 1
    · refine Finset.prod_congr rfl fun l _ => ?_
      have hl : ((Fin.castLE (by omega) (Fin.castAdd ((i : ℕ) - p + 1) l) : Fin (p + q)) : ℕ) < p := by
        have := l.2
        simp only [Fin.val_castLE, Fin.val_castAdd]
        omega
      rw [h1 _ hl]
      rfl
    · refine Finset.prod_congr rfl fun l _ => ?_
      have hl : p ≤ ((Fin.castLE (by omega) (Fin.natAdd p l) : Fin (p + q)) : ℕ) := by
        simp only [Fin.val_castLE, Fin.val_natAdd]
        omega
      rw [h2 _ hl]
      congr 1
      ext
      simp

end GlobalTheory.CompanionTheory.Metric.GradedLines
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RatioSuccessiveNonzeroRegular
section
open Matrix

namespace GlobalTheory.CompanionTheory.Metric.UnitQuotients

theorem consecutive_quotients_units :
    ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (N : ℕ) (G E : Fin N → Φ), (∀ i, E i ≠ 0) → (∀ i, (∏ k ∈ Finset.Iic i, G k) / E i ≠ 0 ∧ (∏ k ∈ Finset.Iic i, G k) / E i ∈ R ∧ ((∏ k ∈ Finset.Iic i, G k) / E i)⁻¹ ∈ R) → ∀ i : Fin N, G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩) ≠ 0 ∧ G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩) ∈ R ∧ (G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩))⁻¹ ∈ R := by
  intro Φ _ R N G E hE hU i
  by_cases h : (i : ℕ) = 0
  · have hI : Finset.Iic i = {i} := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_singleton]
      constructor
      · intro hk
        apply Fin.ext
        have : (k : ℕ) ≤ i := hk
        omega
      · rintro rfl
        exact le_rfl
    have hi := hU i
    rw [hI, Finset.prod_singleton] at hi
    simpa only [dif_pos h] using hi
  · simp only [dif_neg h]
    have hlt : (i : ℕ) - 1 < N := by have := i.2; omega
    generalize hj : (⟨(i : ℕ) - 1, hlt⟩ : Fin N) = j
    have hjv : (j : ℕ) = (i : ℕ) - 1 := by rw [← hj]
    have hI : Finset.Iic i = insert i (Finset.Iic j) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_insert]
      constructor
      · intro hk
        have hk' : (k : ℕ) ≤ i := hk
        by_cases hki : k = i
        · exact Or.inl hki
        · right
          have : (k : ℕ) ≠ i := fun e => hki (Fin.ext e)
          show (k : ℕ) ≤ j
          omega
      · rintro (rfl | hk)
        · exact le_rfl
        · have hk' : (k : ℕ) ≤ j := hk
          show (k : ℕ) ≤ i
          omega
    have hnot : i ∉ Finset.Iic j := by
      simp only [Finset.mem_Iic]
      intro hij
      have : (i : ℕ) ≤ j := hij
      omega
    obtain ⟨a0, a1, a2⟩ := hU i
    obtain ⟨b0, b1, b2⟩ := hU j
    rw [hI, Finset.prod_insert hnot] at a0 a1 a2
    generalize (∏ k ∈ Finset.Iic j, G k) = D at a0 a1 a2 b0 b1 b2
    have hD : D ≠ 0 := fun e => b0 (by rw [e, zero_div])
    have hEi := hE i
    have hEj := hE j
    have key : G i / (E i / E j) = (G i * D / E i) * (D / E j)⁻¹ := by
      field_simp
    rw [key]
    refine ⟨mul_ne_zero a0 (inv_ne_zero b0), R.mul_mem a1 b2, ?_⟩
    rw [mul_inv, inv_inv]
    exact R.mul_mem a2 b1

end GlobalTheory.CompanionTheory.Metric.UnitQuotients
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TendstoLimUnderOfCauchyRate
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tendsto_limUnder_of_cauchy_rate :
    ∀ (f δ : ℝ → ℝ) (t₁ : ℝ), 0 < t₁ → Filter.Tendsto δ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      (∀ t t', 0 < t' → t' ≤ t → t ≤ t₁ → |f t - f t'| ≤ δ t) →
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) f)) ∧
        ∀ t, 0 < t → t ≤ t₁ → |f t - Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) f| ≤ δ t := by
  intro f δ t₁ ht₁ hδ hrate
  set F : Filter ℝ := nhdsWithin 0 (Set.Ioi 0) with hF

  have hS : ∀ ε > 0, {t | δ t < ε ∧ 0 < t ∧ t ≤ t₁} ∈ F := by
    intro ε hε
    filter_upwards [hδ (Iio_mem_nhds hε),
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ F),
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht₁) : Set.Iic t₁ ∈ F)] with t hδt ht ht₁t
    exact ⟨hδt, ht, ht₁t⟩
  have hC : Cauchy (Filter.map f F) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ⟨f '' {t | δ t < ε ∧ 0 < t ∧ t ≤ t₁}, Filter.image_mem_map (hS ε hε), ?_⟩⟩
    rintro _ ⟨t, ⟨h1, h2, h3⟩, rfl⟩ _ ⟨t', ⟨h1', h2', h3'⟩, rfl⟩
    rw [Real.dist_eq]
    rcases le_total t' t with h | h
    · exact (hrate t t' h2' h h3).trans_lt h1
    · rw [abs_sub_comm]; exact (hrate t' t h2 h h3').trans_lt h1'
  obtain ⟨L, hL⟩ := CompleteSpace.complete hC
  have hlim : Filter.Tendsto f F (nhds (Filter.limUnder F f)) := tendsto_nhds_limUnder ⟨L, hL⟩
  refine ⟨hlim, fun t ht htt => ?_⟩

  have hev : ∀ᶠ t' in F, |f t - f t'| ≤ δ t := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht)] with t' h0 h1
    exact hrate t t' h0 h1 htt
  exact le_of_tendsto (tendsto_const_nhds.sub hlim).abs hev

end GlobalTheory.CompanionTheory.Ar.PB
end

