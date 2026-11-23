module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbA
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem dpb_sylv (f : W →ₗ[ℝ] V) (g : V →ₗ[ℝ] W) :
    LinearMap.det (1 + f ∘ₗ g : V →ₗ[ℝ] V) = LinearMap.det (1 + g ∘ₗ f : W →ₗ[ℝ] W) := by
  classical
  let bV := Module.finBasis ℝ V
  let bW := Module.finBasis ℝ W
  rw [← LinearMap.det_toMatrix bV, ← LinearMap.det_toMatrix bW, map_add (f := _), map_add (f := _),
    LinearMap.toMatrix_comp bV bW bV, LinearMap.toMatrix_comp bW bV bW, LinearMap.toMatrix_one,
    LinearMap.toMatrix_one]
  exact Matrix.det_one_add_mul_comm _ _

theorem dpb_ring {R : Type*} [Ring R] (a p q : R) (h0 : p * q = 0) (hc : p * a = a * p) :
    (1 + a * p) * (1 + a * q) = 1 + a * (p + q) := by
  have h : a * p * (a * q) = 0 := by
    rw [mul_assoc, ← mul_assoc p a q, hc, mul_assoc, h0, mul_zero, mul_zero]
  calc (1 + a * p) * (1 + a * q) = 1 + a * p + a * q + a * p * (a * q) := by noncomm_ring
    _ = 1 + a * (p + q) := by rw [h, add_zero, mul_add, add_assoc]

theorem det_one_add_compression (a p q r s ι κ N C : Module.End ℝ V) (E : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W)
    (hpq : p + q = 1) (hpq0 : p * q = 0) (hpa : p * a = a * p)
    (hNC : N * C = a) (hCN : C * N = a) (hpN : p * N = N * q)
    (hrs : r + s = q) (hrs0 : r * s = 0) (hra : r * a = a * r)
    (hι : ι * κ = 1) (hιa : ι * a = a * ι) (hιr : ι * r = s * ι)
    (hEP : E ∘ₗ P = r) :
    LinearMap.det (1 + a) = LinearMap.det (1 + P ∘ₗ a ∘ₗ E : W →ₗ[ℝ] W) ^ 4 := by
  have hsy : ∀ X Y : Module.End ℝ V, LinearMap.det (1 + X * Y) = LinearMap.det (1 + Y * X) :=
    fun X Y => dpb_sylv X Y
  have hA : 1 + a = (1 + a * p) * (1 + a * q) := by rw [dpb_ring a p q hpq0 hpa, hpq, mul_one]
  have hq : q = 1 - p := eq_sub_of_add_eq' hpq
  have hqa : q * a = a * q := by rw [hq, sub_mul, mul_sub, one_mul, mul_one, hpa]
  have hB1 : a * p = N * (q * C) := by rw [← hpa, ← hNC, ← mul_assoc, hpN, mul_assoc]
  have hB2 : q * C * N = a * q := by rw [mul_assoc, hCN, hqa]
  have hB : LinearMap.det (1 + a * p) = LinearMap.det (1 + a * q) := by
    rw [hB1, hsy N (q * C), hB2]
  have hC : 1 + a * q = (1 + a * r) * (1 + a * s) := by rw [dpb_ring a r s hrs0 hra, hrs]
  have hs : s = ι * r * κ := by rw [hιr, mul_assoc, hι, mul_one]
  have hD1 : 1 + a * s = ι * (1 + a * r) * κ := by
    rw [hs, mul_add, add_mul, mul_one, hι, ← mul_assoc ι a r, hιa]
    simp only [mul_assoc]
  have hdet : LinearMap.det ι * LinearMap.det κ = 1 := by rw [← map_mul, hι, map_one]
  have hD : LinearMap.det (1 + a * s) = LinearMap.det (1 + a * r) := by
    rw [hD1, map_mul, map_mul]
    calc LinearMap.det ι * LinearMap.det (1 + a * r) * LinearMap.det κ
        = LinearMap.det (1 + a * r) * (LinearMap.det ι * LinearMap.det κ) := by ring
      _ = LinearMap.det (1 + a * r) := by rw [hdet, mul_one]
  have hE : LinearMap.det (1 + P ∘ₗ a ∘ₗ E : W →ₗ[ℝ] W) = LinearMap.det (1 + a * r) := by
    have h := dpb_sylv E (P ∘ₗ a)
    have h2 : E ∘ₗ (P ∘ₗ a) = a * r := by
      show (E ∘ₗ P) ∘ₗ a = a * r
      rw [hEP, ← hra]
      rfl
    rw [h2] at h
    exact h.symm
  rw [hA, map_mul, hB, hC, map_mul, hD, hE]
  ring

theorem dpb_abs (t θ α ι N C : Module.End ℝ V) (E : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W)
    (hθ : ∀ v, θ (θ v) = v) (hα : ∀ v, α (α v) = v) (hθα : ∀ v, θ (α v) = α (θ v))
    (htθ : ∀ v, θ (t v) = t (θ v)) (htα : ∀ v, α (t v) = t (α v))
    (hNC : ∀ v, N (C v) = t v - v) (hCN : ∀ v, C (N v) = t v - v) (hθN : ∀ v, θ (N v) = -N (θ v))
    (hι : ∀ v, ι (ι v) = -v) (hιt : ∀ v, ι (t v) = t (ι v)) (hιθ : ∀ v, θ (ι v) = ι (θ v))
    (hια : ∀ v, α (ι v) = -ι (α v))
    (hEP : ∀ v, E (P v) = (1 / 4 : ℝ) • (v + α v - θ v - α (θ v))) (hPE : ∀ w, P (E w) = w) :
    LinearMap.det t = LinearMap.det (P ∘ₗ t ∘ₗ E : W →ₗ[ℝ] W) ^ 4 := by
  have key := det_one_add_compression (t - 1) ((1 / 2 : ℝ) • (1 + θ)) ((1 / 2 : ℝ) • (1 - θ))
    ((1 / 4 : ℝ) • (1 + α - θ - α * θ)) ((1 / 4 : ℝ) • (1 - α - θ + α * θ)) ι (-ι) N C E P
    (by ext v; simp; module)
    (by ext v; simp [hθ]; try module)
    (by ext v; simp [htθ]; try module)
    (by ext v; simp [hNC]) (by ext v; simp [hCN])
    (by ext v; simp [hθN]; try module)
    (by ext v; simp; module)
    (by ext v; simp [hθ, hα, hθα]; try module)
    (by ext v; simp [htθ, htα]; try module)
    (by ext v; simp [hι])
    (by ext v; simp [hιt])
    (by ext v; simp [hιθ, hια]; try module)
    (by ext v; simp [hEP])
  have e1 : (1 : Module.End ℝ V) + (t - 1) = t := by abel
  have e2 : (1 + P ∘ₗ (t - 1) ∘ₗ E : W →ₗ[ℝ] W) = P ∘ₗ t ∘ₗ E := by
    ext w; simp [hPE]
  rwa [e1, e2] at key

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbB
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dpbH (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (W : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  U * Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) * Uᴴ

def dpbD (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (x i : ℂ)

theorem dpbH_add (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (W W' : Matrix (Fin n) (Fin n) ℂ) :
    dpbH U x h (W + W') = dpbH U x h W + dpbH U x h W' := by
  have key : Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * (W + W') * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) +
        Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W' * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, mul_add, add_mul]
  simp only [dpbH]
  rw [key, mul_add, add_mul]

theorem dpbH_smul (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (c : ℂ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x h (c • W) = c • dpbH U x h W := by
  have key : Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * (c • W) * U) i j) =
      c • Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]
    ring
  simp only [dpbH]
  rw [key, Matrix.mul_smul, Matrix.smul_mul]

def dpbL (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := dpbH U x h
  map_add' := dpbH_add U x h
  map_smul' c W := by
    have := dpbH_smul U x h (c : ℂ) W
    simpa only [Complex.coe_smul, RingHom.id_apply] using this

theorem dpbH_conjTranspose (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (he : ∀ u, h (-u) = h u)
    (W : Matrix (Fin n) (Fin n) ℂ) : (dpbH U x h W)ᴴ = dpbH U x h Wᴴ := by
  have key : (Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j))ᴴ =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * Wᴴ * U) i j) := by
    ext i j
    have h1 : (Uᴴ * Wᴴ * U) i j = star ((Uᴴ * W * U) j i) := by
      rw [← Matrix.conjTranspose_apply]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have h2 : h (x j - x i) = h (x i - x j) := by rw [← neg_sub, he]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [h1, h2, star_mul']
    simp [Complex.conj_ofReal]
  rw [dpbH, dpbH, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, key]
  exact (Matrix.mul_assoc _ _ _).symm

theorem dpb_had_conj (Q M : Matrix (Fin n) (Fin n) ℂ) (F G : Fin n → Fin n → ℂ)
    (hFG : ∀ i j k l, Q i j ≠ 0 → Q l k ≠ 0 → F i l = G j k) :
    Matrix.of (fun i l => F i l * (Q * M * Qᴴ) i l) = Q * Matrix.of (fun j k => G j k * M j k) * Qᴴ := by
  ext i l
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h1 : Q i j = 0
  · simp [h1]
  by_cases h2 : Q l k = 0
  · simp [h2]
  rw [hFG i j k l h1 h2]
  ring

theorem dpbH_indep {U V : Matrix (Fin n) (Fin n) ℂ} {x x' : Fin n → ℝ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1) (hY : U * dpbD x * Uᴴ = V * dpbD x' * Vᴴ) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x h W = dpbH V x' h W := by
  have hQ : dpbD x * (Uᴴ * V) = (Uᴴ * V) * dpbD x' := by
    calc dpbD x * (Uᴴ * V) = Uᴴ * (U * dpbD x * Uᴴ) * V := by
          simp only [Matrix.mul_assoc]
          rw [← mul_assoc Uᴴ U, hU, one_mul]
      _ = Uᴴ * (V * dpbD x' * Vᴴ) * V := by rw [hY]
      _ = (Uᴴ * V) * dpbD x' := by
          simp only [Matrix.mul_assoc]
          rw [hV, mul_one]
  have hx : ∀ i j, (Uᴴ * V) i j ≠ 0 → x i = x' j := by
    intro i j hne
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hQ
    simp only [dpbD, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    have h2 : ((x i : ℂ) - x' j) * (Uᴴ * V) i j = 0 := by
      rw [sub_mul, h1]
      ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact_mod_cast sub_eq_zero.mp h3
    · exact absurd h3 hne
  have hQM : (Uᴴ * V) * (Vᴴ * W * V) * (Uᴴ * V)ᴴ = Uᴴ * W * U := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Uᴴ * V * (Vᴴ * W * V) * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * W * (V * Vᴴ) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * W * U := by rw [hV', mul_one, mul_one]
  have key := dpb_had_conj (Uᴴ * V) (Vᴴ * W * V) (fun i l => ((h (x i - x l) : ℝ) : ℂ))
    (fun j k => ((h (x' j - x' k) : ℝ) : ℂ)) (by
      intro i j k l h1 h2
      show ((h (x i - x l) : ℝ) : ℂ) = ((h (x' j - x' k) : ℝ) : ℂ)
      rw [hx i j h1, hx l k h2])
  try simp only at key
  rw [hQM] at key
  simp only [dpbH]
  rw [key, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [hU', mul_one, ← mul_assoc U Uᴴ, hU', one_mul]

theorem dpbH_theta {U J : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℝ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hJ : J * J = 1) (hJ' : Jᴴ = J) (hY : J * (U * dpbD x * Uᴴ) * J = -(U * dpbD x * Uᴴ)) (h : ℝ → ℝ)
    (he : ∀ u, h (-u) = h u) (W : Matrix (Fin n) (Fin n) ℂ) :
    J * dpbH U x h W * J = dpbH U x h (J * W * J) := by
  have hV : (J * U)ᴴ * (J * U) = 1 := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc Uᴴ * J * (J * U) = Uᴴ * (J * J) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, mul_one, hU]
  have hV' : (J * U) * (J * U)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc J * U * (Uᴴ * J) = J * (U * Uᴴ) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU', mul_one, hJ]
  have hD : dpbD (-x) = -dpbD x := by
    ext i j
    simp only [dpbD, Matrix.neg_apply, Matrix.diagonal_apply, Pi.neg_apply, Complex.ofReal_neg]
    split_ifs <;> simp
  have hY' : U * dpbD x * Uᴴ = (J * U) * dpbD (-x) * (J * U)ᴴ := by
    rw [hD, Matrix.conjTranspose_mul, hJ']
    calc U * dpbD x * Uᴴ = -(J * (U * dpbD x * Uᴴ) * J) := by rw [hY, neg_neg]
      _ = J * U * -dpbD x * (Uᴴ * J) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hM : (J * U)ᴴ * (J * W * J) * (J * U) = Uᴴ * W * U := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc Uᴴ * J * (J * W * J) * (J * U) = Uᴴ * (J * J) * W * (J * J) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * W * U := by rw [hJ, mul_one, mul_one]
  have hA : Matrix.of (fun i j => ((h ((-x) i - (-x) j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Pi.neg_apply]
    rw [neg_sub_neg, ← neg_sub, he]
  rw [dpbH_indep hU hU' hV hV' hY' h (J * W * J)]
  simp only [dpbH]
  rw [hM, hA, Matrix.conjTranspose_mul, hJ']
  simp only [Matrix.mul_assoc]

theorem dpb_comm_D (x : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (dpbD x * X - X * dpbD x) i j = ((x i - x j : ℝ) : ℂ) * X i j := by
  simp only [dpbD, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_sub]
  ring

theorem dpbH_sub_one {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU' : U * Uᴴ = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x (fun u => h u - 1) W = dpbH U x h W - W := by
  have key : Matrix.of (fun i j => ((h (x i - x j) - 1 : ℝ) : ℂ) * (Uᴴ * W * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) - Uᴴ * W * U := by
    ext i j
    simp only [Matrix.of_apply, Matrix.sub_apply, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  simp only [dpbH]
  rw [key, mul_sub, sub_mul]
  congr 1
  calc U * (Uᴴ * W * U) * Uᴴ = (U * Uᴴ) * W * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = W := by rw [hU', one_mul, mul_one]

private theorem unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1)
    (A B : Matrix (Fin n) (Fin n) ℂ) : U * A * Uᴴ * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  calc U * A * Uᴴ * (U * B * Uᴴ) = U * A * (Uᴴ * U) * B * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * (A * B) * Uᴴ := by
        rw [hU, mul_one]
        simp only [Matrix.mul_assoc]

theorem dpbH_ad_left {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU : Uᴴ * U = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) :
    (U * dpbD x * Uᴴ) * dpbH U x h W - dpbH U x h W * (U * dpbD x * Uᴴ) = dpbH U x (fun u => u * h u) W := by
  simp only [dpbH]
  rw [unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self hU, unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self hU, ← sub_mul, ← mul_sub]
  congr 2
  ext i j
  rw [dpb_comm_D]
  simp only [Matrix.of_apply, Complex.ofReal_mul]
  ring

theorem dpbH_ad_right {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU : Uᴴ * U = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) :
    dpbH U x h ((U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)) = dpbH U x (fun u => u * h u) W := by
  have e1 : Uᴴ * (U * dpbD x * Uᴴ * W) * U = dpbD x * (Uᴴ * W * U) := by
    calc Uᴴ * (U * dpbD x * Uᴴ * W) * U = (Uᴴ * U) * dpbD x * (Uᴴ * W * U) := by
          simp only [Matrix.mul_assoc]
      _ = dpbD x * (Uᴴ * W * U) := by rw [hU, one_mul]
  have e2 : Uᴴ * (W * (U * dpbD x * Uᴴ)) * U = (Uᴴ * W * U) * dpbD x * (Uᴴ * U) := by
    simp only [Matrix.mul_assoc]
  have key : Uᴴ * ((U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)) * U =
      dpbD x * (Uᴴ * W * U) - (Uᴴ * W * U) * dpbD x := by
    rw [mul_sub, sub_mul, e1, e2, hU, mul_one]
  simp only [dpbH]
  rw [key]
  congr 2
  ext i j
  simp only [Matrix.of_apply]
  rw [dpb_comm_D, Complex.ofReal_mul]
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdDefs
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def Dvec (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) - ((a : ℕ) : ℝ)

def lamT (lam : Fin n → ℝ) (t : ℕ) : Fin n → ℝ := lam + (t : ℝ) • Dvec n

def Vand (lam : Fin n → ℝ) : ℝ := ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b)

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def volU (M : ℕ) : ℝ := ∏ i ∈ range M, 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)

theorem volU_eq_pow_div (M : ℕ) : volU M = 2 ^ M * Real.pi ^ (∑ i ∈ range M, (i + 1)) /
    ∏ i ∈ range M, (i.factorial : ℝ) := by
  rw [volU, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Finset.prod_pow_eq_pow_sum]

theorem volU_sum_succ_add (p q : ℕ) : ∑ i ∈ range (p + q), (i + 1) =
    ∑ i ∈ range p, (i + 1) + ∑ i ∈ range q, (i + 1) + p * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← Nat.add_assoc, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

theorem volU_factProd_pos (M : ℕ) : (0 : ℝ) < ∏ i ∈ range M, (i.factorial : ℝ) := Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos i)

theorem volU_ratio (p q m : ℕ) (h : p + q = m) :
    volU p * volU q / volU m = (∏ i ∈ range m, (i.factorial : ℝ)) /
      (Real.pi ^ (p * q) * (∏ i ∈ range p, (i.factorial : ℝ)) *
        ∏ i ∈ range q, (i.factorial : ℝ)) := by
  subst h
  have hp := volU_factProd_pos p
  have hq := volU_factProd_pos q
  have hn := volU_factProd_pos (p + q)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [volU_eq_pow_div, volU_eq_pow_div, volU_eq_pow_div, volU_sum_succ_add]
  simp only [pow_add]
  field_simp

theorem volU_factProd_mul_le (p q : ℕ) :
    (∏ i ∈ range p, i.factorial) * (∏ i ∈ range q, i.factorial) ≤
      ∏ i ∈ range (p + q), i.factorial := by
  rw [Finset.prod_range_add]
  exact Nat.mul_le_mul le_rfl
    (Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i _ => Nat.factorial_le (by omega)))

theorem volU_pOf_add_qOf (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  unfold pOf qOf
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have hone : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem cPQ_eq_volU (ε : Fin n → Bool) : cPQ ε = volU (pOf ε) * volU (qOf ε) / volU n := by
  rw [volU_ratio _ _ _ (volU_pOf_add_qOf ε)]
  rfl

theorem inv_pi_pow_le_cPQ (ε : Fin n → Bool) : (Real.pi ^ (pOf ε * qOf ε))⁻¹ ≤ cPQ ε := by
  have hle := volU_factProd_mul_le (pOf ε) (qOf ε)
  rw [volU_pOf_add_qOf ε] at hle
  have hle' : (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) ≤
      ∏ i ∈ range n, (i.factorial : ℝ) := by
    exact_mod_cast hle
  have hp := volU_factProd_pos (pOf ε)
  have hq := volU_factProd_pos (qOf ε)
  have hpi : 0 < Real.pi ^ (pOf ε * qOf ε) := pow_pos Real.pi_pos _
  have hD : 0 < Real.pi ^ (pOf ε * qOf ε) * (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) *
      ∏ i ∈ range (qOf ε), (i.factorial : ℝ) := mul_pos (mul_pos hpi hp) hq
  unfold cPQ
  rw [le_div_iff₀ hD]
  have he : (Real.pi ^ (pOf ε * qOf ε))⁻¹ * (Real.pi ^ (pOf ε * qOf ε) *
      (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ)) =
      (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) := by
    rw [mul_assoc, inv_mul_cancel_left₀ hpi.ne']
  linarith

end ReciprocityTheory.ChartRestriction.DS
end
end

