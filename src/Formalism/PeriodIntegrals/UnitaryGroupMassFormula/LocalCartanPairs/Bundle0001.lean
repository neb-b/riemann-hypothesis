module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PlaneIsUnitOfSubOneMem
section
noncomputable section

namespace PI.SqPair.LCP

open Polynomial IsLocalRing Matrix

theorem plane_isUnit_of_sub_one_mem {A : Type*} [CommRing A] [IsLocalRing A] {x : A}
    (h : x - 1 ∈ maximalIdeal A) : IsUnit x := by
  by_contra hx
  have hxm : x ∈ maximalIdeal A := (mem_maximalIdeal x).2 hx
  have h1 : (1 : A) ∈ maximalIdeal A := by
    have h2 := sub_mem hxm h
    rwa [sub_sub_cancel] at h2
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem plane_core {R : Type*} [CommRing R] (σ : R ≃+* R) (α β t s c : R)
    (hα : σ α = α) (h1 : β + t + σ t + t * σ t * α = 0)
    (h2 : s * (1 + t * α) + σ s * (1 + σ t * α) = -α) (h3 : c * (1 + t * α) = 1) :
    ((!![1 + s * t, c * t; s, c] : Matrix (Fin 2) (Fin 2) R).map σ)ᵀ * !![α, 1; 1, β]
        * !![1 + s * t, c * t; s, c] = !![0, 1; 1, 0] ∧
      (!![1 + s * t, c * t; s, c] : Matrix (Fin 2) (Fin 2) R).det = c := by
  have h3σ : σ c * (1 + σ t * α) = 1 := by
    have h4 := congrArg σ h3
    simpa only [map_mul, map_add (f := _), map_one, hα] using h4
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), map_mul, map_one]
    · linear_combination h2 + σ s * s * h1
    · linear_combination h3 + σ s * c * h1
    · linear_combination h3σ + σ c * s * h1
    · linear_combination σ c * c * h1
  · simp [Matrix.det_fin_two]
    ring

theorem plane_exists {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x)
    (R₀ : Subring R) (hR₀ : ∀ x, x ∈ R₀ ↔ σ x = x) [HenselianLocalRing R₀]
    (τ : R) (hτ : τ + σ τ = 1) (α β : R₀) (hα : α ∈ maximalIdeal R₀) :
    ∃ t s c : R, β + t + σ t + t * σ t * α = 0 ∧
      s * (1 + t * α) + σ s * (1 + σ t * α) = -α ∧ c * (1 + t * α) = 1 ∧ ∃ s', s = α * s' := by
  have hfix : ∀ x : R₀, σ (x : R) = x := fun x => (hR₀ x).1 x.2
  have hNfix : σ (τ * σ τ) = τ * σ τ := by rw [map_mul, hσ, mul_comm]
  let N : R₀ := ⟨τ * σ τ, (hR₀ _).2 hNfix⟩
  have hN : (N : R) = τ * σ τ := rfl
  obtain ⟨w, hwroot, hw1⟩ := HenselianLocalRing.is_henselian (X ^ 2 - X + C (α * N * β))
    (by monicity!) 1
    (by
      simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C, one_pow, sub_self, zero_add]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hα))
    (by
      simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_X, derivative_C,
        eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one, eval_zero]
      norm_num)
  have hr : w ^ 2 - w + α * N * β = 0 := by
    have h0 := hwroot.eq_zero
    simpa only [eval_add, eval_sub, eval_pow, eval_X, eval_C] using h0
  obtain ⟨wu, rfl⟩ := plane_isUnit_of_sub_one_mem hw1
  have hwv : (wu : R₀) * ↑wu⁻¹ = 1 := wu.mul_inv
  let x : R₀ := -β * ↑wu⁻¹
  have hx : β + x + α * N * x ^ 2 = 0 := by
    linear_combination (β * (↑wu⁻¹ : R₀) ^ 2) * hr -
      (β + β * ↑wu⁻¹ * ↑wu - β * ↑wu⁻¹) * hwv
  have hxR : (β : R) + x + α * (τ * σ τ) * (x : R) ^ 2 = 0 := by
    have h0 := congrArg (fun y : R₀ => (y : R)) hx
    simpa only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow, hN, ZeroMemClass.coe_zero]
      using h0
  let nR : R₀ := 1 + x * α + N * x ^ 2 * α ^ 2
  have hnm : nR - 1 ∈ maximalIdeal R₀ := by
    have e : nR - 1 = α * (x + N * x ^ 2 * α) := by ring
    rw [e]
    exact Ideal.mul_mem_right _ _ hα
  obtain ⟨nu, hnu⟩ := plane_isUnit_of_sub_one_mem hnm
  have hninv : ((nR : R₀) : R) * ((↑nu⁻¹ : R₀) : R) = 1 := by
    have h0 := congrArg (fun y : R₀ => (y : R)) nu.mul_inv
    simpa only [hnu, Subring.coe_mul, OneMemClass.coe_one] using h0
  set t : R := τ * x with ht
  have hσt : σ t = σ τ * x := by rw [ht, map_mul, hfix]
  have hnR : (1 + t * α) * (1 + σ t * α) = ((nR : R₀) : R) := by
    rw [hσt, ht]
    simp only [nR]
    push_cast
    linear_combination ((x : R) * α) * hτ - ((x : R) ^ 2 * (α : R) ^ 2) * hN
  set c : R := (1 + σ t * α) * ((↑nu⁻¹ : R₀) : R) with hc
  have h3 : c * (1 + t * α) = 1 := by
    rw [hc]
    linear_combination ((↑nu⁻¹ : R₀) : R) * hnR + hninv
  have hσc : σ c = (1 + t * α) * ((↑nu⁻¹ : R₀) : R) := by
    rw [hc, map_mul, map_add (f := _), map_one, map_mul, hσ, hfix, hfix]
  refine ⟨t, -((α : R) * τ * c), c, ?_, ?_, h3, -(τ * c), by ring⟩
  · rw [hσt, ht]
    linear_combination hxR + (x : R) * hτ
  · rw [map_neg, map_mul, map_mul, hfix, hσc]
    linear_combination (-((α : R) * τ)) * h3 + (-((α : R) * σ τ * ((↑nu⁻¹ : R₀) : R))) * hnR +
      (-((α : R) * σ τ)) * hninv + (-(α : R)) * hτ

theorem plane_w {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x)
    (R₀ : Subring R) (hR₀ : ∀ x, x ∈ R₀ ↔ σ x = x) [HenselianLocalRing R₀]
    (τ : R) (hτ : τ + σ τ = 1) (α β : R₀) (hα : α ∈ maximalIdeal R₀) :
    ∃ w : Matrix (Fin 2) (Fin 2) R, IsUnit w.det ∧
      (w.map σ)ᵀ * !![(α : R), 1; 1, (β : R)] * w = !![0, 1; 1, 0] ∧ ∃ s', w 1 0 = (α : R) * s' := by
  obtain ⟨t, s, c, h1, h2, h3, s', hs'⟩ := plane_exists σ hσ R₀ hR₀ τ hτ α β hα
  obtain ⟨hform, hdet⟩ := plane_core σ (α : R) (β : R) t s c ((hR₀ _).1 α.2) h1 h2 h3
  refine ⟨!![1 + s * t, c * t; s, c], ?_, hform, s', ?_⟩
  · rw [hdet]
    exact IsUnit.of_mul_eq_one _ h3
  · simp [hs']

theorem tau_of_theta {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x) (θ : R)
    (hθ : IsUnit (θ - σ θ)) : ∃ τ : R, τ + σ τ = 1 := by
  obtain ⟨u, hu⟩ := hθ
  refine ⟨θ * ↑u⁻¹, ?_⟩
  have hσu : σ (↑u : R) = -↑u := by rw [hu, map_sub, hσ]; ring
  have h2 : (↑u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
  have hσinv : σ (↑u⁻¹ : R) = -↑u⁻¹ := by
    have h1 : σ (↑u : R) * σ (↑u⁻¹ : R) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    rw [hσu] at h1
    linear_combination (-σ (↑u⁻¹ : R)) * h2 + (-(↑u⁻¹ : R)) * h1
  rw [map_mul, hσinv]
  rw [hu] at h2
  linear_combination h2

end PI.SqPair.LCP
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.SelCore
section
noncomputable section
open Matrix

namespace PI.SqPair.LCP

variable {R : Type} [CommRing R] [IsDomain R]

theorem sel_factor (ϖ : R) (hϖ0 : ϖ ≠ 0)
    (hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u)
    {ι κ : Type} (h : Matrix ι κ R) (hh : h ≠ 0) :
    ∃ (m : ℕ) (h₁ : Matrix ι κ R) (i : ι) (j : κ), h = ϖ ^ m • h₁ ∧ IsUnit (h₁ i j) := by
  classical
  have hex : ∃ n : ℕ, ∃ i j, h i j ≠ 0 ∧ ∃ u : R, IsUnit u ∧ h i j = ϖ ^ n * u := by
    by_contra hne
    apply hh
    ext i j
    rw [Matrix.zero_apply]
    by_contra hij
    obtain ⟨n, u, hu, he⟩ := hval _ hij
    exact hne ⟨n, i, j, hij, u, hu, he⟩
  obtain ⟨i₀, j₀, _, u₀, hu₀, he₀⟩ := Nat.find_spec hex
  have hdiv : ∀ i j, ∃ z : R, h i j = ϖ ^ Nat.find hex * z := by
    intro i j
    by_cases hij : h i j = 0
    · exact ⟨0, by rw [hij, mul_zero]⟩
    · obtain ⟨n, u, hu, he⟩ := hval _ hij
      have hmn : Nat.find hex ≤ n := Nat.find_min' hex ⟨i, j, hij, u, hu, he⟩
      refine ⟨ϖ ^ (n - Nat.find hex) * u, ?_⟩
      rw [he, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]
  choose h₁ hh₁ using hdiv
  refine ⟨Nat.find hex, Matrix.of h₁, i₀, j₀, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact hh₁ i j
  · have e : h₁ i₀ j₀ = u₀ :=
      mul_left_cancel₀ (pow_ne_zero _ hϖ0) ((hh₁ i₀ j₀).symm.trans he₀)
    simp only [Matrix.of_apply, e]
    exact hu₀

theorem sel_star_smul (σ : R ≃+* R) (ϖ : R) (hσϖ : σ ϖ = ϖ) (m : ℕ) {ι κ : Type}
    (h : Matrix ι κ R) : ((ϖ ^ m • h).map σ)ᵀ = ϖ ^ m • (h.map σ)ᵀ := by
  ext i j
  simp [Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hσϖ]

theorem sel_smul_cancel {ι κ : Type} {c : R} (hc : c ≠ 0) {X Y : Matrix ι κ R}
    (h : c • X = c • Y) : X = Y := by
  ext i j
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h'
  exact mul_left_cancel₀ hc h'

theorem sel_le (σ : R ≃+* R) (ϖ : R) (hϖ0 : ϖ ≠ 0) (hϖ : ¬ IsUnit ϖ) (hσϖ : σ ϖ = ϖ)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det) (m k : ℕ)
    (hrel : ((ϖ ^ m • h₁).map σ)ᵀ * A * (ϖ ^ m • h₁) = ϖ ^ (2 * k) • A') :
    m ≤ k ∧ (h₁.map σ)ᵀ * A * h₁ = ϖ ^ (2 * (k - m)) • A' := by
  have hB : ϖ ^ (2 * m) • ((h₁.map σ)ᵀ * A * h₁) = ϖ ^ (2 * k) • A' := by
    rw [← hrel, sel_star_smul σ ϖ hσϖ]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, two_mul]
  have hp0 : ∀ t : ℕ, ϖ ^ t ≠ 0 := fun t => pow_ne_zero _ hϖ0
  by_cases hmk : m ≤ k
  · refine ⟨hmk, sel_smul_cancel (hp0 (2 * m)) ?_⟩
    rw [hB, smul_smul, ← pow_add]
    congr 2
    omega
  · exfalso
    push_neg at hmk
    have h2 : ϖ ^ (2 * k) • (ϖ ^ (2 * (m - k)) • ((h₁.map σ)ᵀ * A * h₁)) = ϖ ^ (2 * k) • A' := by
      rw [smul_smul, ← pow_add, ← hB]
      congr 2
      omega
    have h3 := sel_smul_cancel (hp0 (2 * k)) h2
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_smul] at h4
    rw [← h4] at hA'
    have h5 : IsUnit ((ϖ ^ (2 * (m - k))) ^ Fintype.card ι) := isUnit_of_mul_isUnit_left hA'
    rw [← pow_mul] at h5
    have hpos : 2 * (m - k) * Fintype.card ι ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Nat.mul_pos (by omega) Fintype.card_pos)
    exact hϖ ((isUnit_pow_iff hpos).mp h5)

theorem sel_unit_of_rel (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det)
    (hrel : (h₁.map σ)ᵀ * A * h₁ = A') : IsUnit h₁.det := by
  have e := congrArg Matrix.det hrel
  rw [Matrix.det_mul, Matrix.det_mul] at e
  rw [← e] at hA'
  exact isUnit_of_mul_isUnit_right hA'

theorem sel_comm {ι : Type} [Fintype ι] [DecidableEq ι] {c : R} (hc : c ≠ 0)
    (g h : Matrix ι ι R) (hgh : g * h = c • 1) : h * g = c • 1 := by
  have hdet : g.det * h.det = c ^ Fintype.card ι := by
    rw [← Matrix.det_mul, hgh, Matrix.det_smul, Matrix.det_one, mul_one]
  have hh0 : h.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero _ hc hdet.symm
  have key : (h * g - c • 1) * h = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hgh, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self]
  have key2 : h.det • (h * g - c • 1) = 0 := by
    have e := congrArg (· * h.adjugate) key
    simp only [Matrix.zero_mul] at e
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at e
    exact e
  have e0 : h * g - c • 1 = 0 := by
    ext i j
    have e := congrFun (congrFun key2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at e ⊢
    exact (mul_eq_zero.mp e).resolve_left hh0
  exact sub_eq_zero.mp e0

theorem sel_inv (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det) {c : R} (hc : c ≠ 0)
    (hrel : (h₁.map σ)ᵀ * A * h₁ = c • A') :
    (A'⁻¹ * (h₁.map σ)ᵀ * A) * h₁ = c • 1 ∧ h₁ * (A'⁻¹ * (h₁.map σ)ᵀ * A) = c • 1 := by
  have h1 : (A'⁻¹ * (h₁.map σ)ᵀ * A) * h₁ = c • 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ A h₁, hrel, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ hA']
  exact ⟨h1, sel_comm hc _ _ h1⟩

theorem sel_dual (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (hA : IsUnit A.det) (x : ι → R) (i : ι) (hx : IsUnit (x i)) :
    ∃ y : ι → R, (fun l => σ (x l)) ⬝ᵥ (A *ᵥ y) = 1 := by
  obtain ⟨u, hu⟩ := hx.map σ
  refine ⟨A⁻¹ *ᵥ Pi.single i (↑u⁻¹ : R), ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec, dotProduct_single]
  simp [← hu]

theorem sel_form (σ : R ≃+* R) {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι R) (M : Matrix ι κ R) (v w : κ → R) :
    (fun l => σ ((M *ᵥ v) l)) ⬝ᵥ (A *ᵥ (M *ᵥ w)) =
      (fun l => σ (v l)) ⬝ᵥ (((M.map σ)ᵀ * A * M) *ᵥ w) := by
  have e : (fun l => σ ((M *ᵥ v) l)) = (M.map σ) *ᵥ (fun l => σ (v l)) := by
    funext l
    exact RingHom.map_mulVec (σ : R →+* R) M v l
  rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end PI.SqPair.LCP
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.SplPlane
section
noncomputable section

open Matrix

namespace PI.LocCartanPair

variable {R : Type} [CommRing R] [StarRing R]

theorem splPlane_entry {ι m n : Type} [Fintype ι] (A : Matrix ι ι R) (M : Matrix ι m R)
    (N : Matrix ι n R) (r : m) (s : n) :
    (Mᴴ * A * N) r s = star (fun i => M i r) ⬝ᵥ (A *ᵥ fun i => N i s) := by
  rw [Matrix.mul_assoc]; rfl

theorem splPlane_herm {ι : Type} [Fintype ι] (A : Matrix ι ι R) (hA : Aᴴ = A) (a b : ι → R) :
    star (star a ⬝ᵥ (A *ᵥ b)) = star b ⬝ᵥ (A *ᵥ a) := by
  rw [star_dotProduct, star_star, star_mulVec, ← dotProduct_mulVec, hA]

theorem splPlane_unitEntry [IsLocalRing R] {ι : Type} [Fintype ι] (w z : ι → R)
    (h : w ⬝ᵥ z = 1) : ∃ i, IsUnit (z i) := by
  by_contra hn
  push Not at hn
  have hm : w ⬝ᵥ z ∈ IsLocalRing.maximalIdeal R :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hn i))
  rw [h] at hm
  exact (IsLocalRing.mem_maximalIdeal _).1 hm isUnit_one

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def splBasis (E : Fin 2 ⊕ κ ≃ ι) (x y : ι → R) : Matrix ι (Fin 2 ⊕ κ) R :=
  fun i c => Sum.elim (fun a => ![x, y] a i) (fun j => (1 : Matrix ι ι R) i (E (.inr j))) c

def splCorr (E : Fin 2 ⊕ κ ≃ ι) (A : Matrix ι ι R) (x y : ι → R) : Matrix (Fin 2) κ R :=
  fun a j => ![-(star y ⬝ᵥ (A *ᵥ fun i => (1 : Matrix ι ι R) i (E (.inr j)))),
    -(star x ⬝ᵥ (A *ᵥ fun i => (1 : Matrix ι ι R) i (E (.inr j))))] a

theorem splPlane_core (E : Fin 2 ⊕ κ ≃ ι) (A : Matrix ι ι R) (hA : Aᴴ = A) (x y : ι → R)
    (hxx : star x ⬝ᵥ (A *ᵥ x) = 0) (hyy : star y ⬝ᵥ (A *ᵥ y) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1)
    (hdet : IsUnit (x (E (.inl 0)) * y (E (.inl 1)) - y (E (.inl 0)) * x (E (.inl 1)))) :
    ∃ (u : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ : Matrix κ κ R),
      u * v = 1 ∧ v * u = 1 ∧ (∀ i, u i (.inl 0) = x i) ∧ (∀ i, u i (.inl 1) = y i) ∧
      uᴴ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁ ∧ A₁ᴴ = A₁ ∧
      (IsUnit A.det → IsUnit A₁.det) := by
  have hyx : star y ⬝ᵥ (A *ᵥ x) = 1 := by rw [← splPlane_herm A hA x y, hxy, star_one]
  set u₀ := splBasis E x y with hu₀def
  set B := splCorr E A x y with hBdef
  set T : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks 1 B 0 1 with hTdef
  set T' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks 1 (-B) 0 1 with hT'def
  have hTT' : T * T' = 1 := by simp [hTdef, hT'def, fromBlocks_multiply, fromBlocks_one]
  have hT'T : T' * T = 1 := by simp [hTdef, hT'def, fromBlocks_multiply, fromBlocks_one]
  set S : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := u₀.submatrix E id with hSdef
  have hS : S = fromBlocks S.toBlocks₁₁ 0 S.toBlocks₂₁ 1 := by
    conv_lhs => rw [← fromBlocks_toBlocks S]
    congr 1
    · ext a j; simp [hSdef, hu₀def, splBasis, toBlocks₁₂]
    · ext k j; simp [hSdef, hu₀def, splBasis, toBlocks₂₂, Matrix.one_apply]
  have hSdet : IsUnit S.det := by
    rw [hS, det_fromBlocks_zero₁₂, det_one, mul_one, det_fin_two]
    simpa [hSdef, hu₀def, splBasis, toBlocks₁₁] using hdet
  set v₀ : Matrix (Fin 2 ⊕ κ) ι R := S⁻¹.submatrix id E.symm with hv₀def
  have hu₀S : u₀ = S.submatrix E.symm id := by ext i c; simp [hSdef]
  have huv₀ : u₀ * v₀ = 1 := by
    rw [hu₀S, hv₀def, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      mul_nonsing_inv _ hSdet, submatrix_one_equiv]
  have hvu₀ : v₀ * u₀ = 1 := by
    rw [hu₀S, hv₀def, submatrix_mul_equiv, nonsing_inv_mul _ hSdet, submatrix_id_id]
  set u := u₀ * T with hudef
  set v := T' * v₀ with hvdef
  have huv : u * v = 1 := by
    rw [hudef, hvdef, Matrix.mul_assoc, ← Matrix.mul_assoc T, hTT', Matrix.one_mul, huv₀]
  have hvu : v * u = 1 := by
    rw [hudef, hvdef, Matrix.mul_assoc, ← Matrix.mul_assoc v₀, hvu₀, Matrix.one_mul, hT'T]
  have hc0 : (fun i => u i (.inl 0)) = x := by
    funext i; simp [hudef, hTdef, hu₀def, splBasis, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two]
  have hc1 : (fun i => u i (.inl 1)) = y := by
    funext i; simp [hudef, hTdef, hu₀def, splBasis, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two]
  have hcj : ∀ j, (fun i => u i (.inr j)) = (fun i => (1 : Matrix ι ι R) i (E (.inr j)))
      + B 0 j • x + B 1 j • y := by
    intro j; funext i
    simp [hudef, hTdef, hu₀def, splBasis, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.one_apply, mul_ite]
    ring
  set G := uᴴ * A * u with hGdef
  have hG : ∀ r s, G r s = star (fun i => u i r) ⬝ᵥ (A *ᵥ fun i => u i s) :=
    fun r s => splPlane_entry A u u r s
  have h12 : G.toBlocks₁₂ = 0 := by
    ext a j
    simp only [toBlocks₁₂, of_apply, hG, hcj, Matrix.zero_apply]
    fin_cases a
    · simp only [Fin.zero_eta, Fin.isValue, hc0, mulVec_add, mulVec_smul, dotProduct_add,
        dotProduct_smul, smul_eq_mul, hxx, hxy, hBdef, splCorr]
      simp
    · simp only [Fin.mk_one, Fin.isValue, hc1, mulVec_add, mulVec_smul, dotProduct_add,
        dotProduct_smul, smul_eq_mul, hyx, hyy, hBdef, splCorr]
      simp
  have h21 : G.toBlocks₂₁ = 0 := by
    ext j a
    have := congrFun (congrFun h12 a) j
    simp only [toBlocks₁₂, toBlocks₂₁, of_apply, Matrix.zero_apply] at this ⊢
    rw [hG, ← splPlane_herm A hA, ← hG, this, star_zero]
  have h11 : G.toBlocks₁₁ = !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [toBlocks₁₁, hG, hc0, hc1, hxx, hyy, hxy, hyx]
  have hGe : G = fromBlocks !![0, 1; 1, 0] 0 0 G.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks G]
    rw [h11, h12, h21]
  refine ⟨u, v, G.toBlocks₂₂, huv, hvu, fun i => congrFun hc0 i, fun i => congrFun hc1 i,
    hGe, ?_, ?_⟩
  · ext i j
    simp only [conjTranspose_apply, toBlocks₂₂, of_apply]
    rw [hG, hG, splPlane_herm A hA]
  · intro hAdet
    set U : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := u.submatrix E id with hUdef
    have hUv : U * v.submatrix id E = 1 := by
      rw [hUdef, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, huv,
        submatrix_one_equiv]
    have hU : IsUnit U.det := isUnit_det_of_right_inverse hUv
    have hGU : G = Uᴴ * A.submatrix E E * U := by
      rw [hUdef, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv,
        submatrix_id_id]
    have hGdet : IsUnit G.det := by
      rw [hGU, det_mul, det_mul, det_conjTranspose, det_submatrix_equiv_self]
      exact (hU.star.mul hAdet).mul hU
    rw [hGe, det_fromBlocks_zero₁₂] at hGdet
    exact isUnit_of_mul_isUnit_right hGdet

section Local

variable {R : Type} [CommRing R] [StarRing R]

theorem splPlane_pair [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R)
    (hA : Aᴴ = A) (x y : ι → R) (hxx : star x ⬝ᵥ (A *ᵥ x) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1) :
    ∃ i₀ j₀, i₀ ≠ j₀ ∧ IsUnit (x i₀ * y j₀ - y i₀ * x j₀) := by
  have hyx : star y ⬝ᵥ (A *ᵥ x) = 1 := by rw [← splPlane_herm A hA x y, hxy, star_one]
  rw [dotProduct_mulVec] at hyx
  obtain ⟨i₀, hi₀⟩ := splPlane_unitEntry _ _ hyx
  obtain ⟨xi, hxi⟩ := hi₀.exists_right_inv
  set y' := y - (y i₀ * xi) • x with hy'
  have hy'i : y' i₀ = 0 := by
    simp only [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(y i₀)) * hxi
  have hxy' : (star x ᵥ* A) ⬝ᵥ y' = 1 := by
    rw [← dotProduct_mulVec, hy', mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hxx,
      hxy, smul_eq_mul, mul_zero, sub_zero]
  obtain ⟨j₀, hj₀⟩ := splPlane_unitEntry _ _ hxy'
  have hne : i₀ ≠ j₀ := by
    rintro rfl; rw [hy'i] at hj₀; exact not_isUnit_zero hj₀
  refine ⟨i₀, j₀, hne, ?_⟩
  have e : x i₀ * y j₀ - y i₀ * x j₀ = x i₀ * y' j₀ := by
    simp only [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (y i₀ * x j₀) * hxi
  rw [e]; exact hi₀.mul hj₀

def splEquiv {ι : Type} [DecidableEq ι] (i₀ j₀ : ι) (hne : i₀ ≠ j₀) :
    Fin 2 ⊕ {j // j ≠ i₀ ∧ j ≠ j₀} ≃ ι where
  toFun := Sum.elim ![i₀, j₀] Subtype.val
  invFun j := if h0 : j = i₀ then .inl 0 else if h1 : j = j₀ then .inl 1 else .inr ⟨j, h0, h1⟩
  left_inv := by
    rintro (a | ⟨j, h0, h1⟩)
    · fin_cases a
      · simp
      · simp [hne.symm]
    · simp [h0, h1]
  right_inv := by
    intro j
    by_cases h0 : j = i₀
    · subst h0; simp
    · by_cases h1 : j = j₀
      · subst h1; simp [h0]
      · simp [h0, h1]

theorem splPlane [IsLocalRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (hc : Fintype.card κ + 2 = Fintype.card ι) (A : Matrix ι ι R) (hA : Aᴴ = A)
    (x y : ι → R) (hxx : star x ⬝ᵥ (A *ᵥ x) = 0) (hyy : star y ⬝ᵥ (A *ᵥ y) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1) :
    ∃ (u : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ : Matrix κ κ R),
      u * v = 1 ∧ v * u = 1 ∧ (∀ i, u i (.inl 0) = x i) ∧ (∀ i, u i (.inl 1) = y i) ∧
      uᴴ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁ ∧ A₁ᴴ = A₁ ∧
      (IsUnit A.det → IsUnit A₁.det) := by
  obtain ⟨i₀, j₀, hne, hu⟩ := splPlane_pair A hA x y hxx hxy
  have hc₀ : Fintype.card {j // j ≠ i₀ ∧ j ≠ j₀} = Fintype.card κ := by
    have := Fintype.card_congr (splEquiv i₀ j₀ hne)
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  let E : Fin 2 ⊕ κ ≃ ι :=
    (Equiv.sumCongr (Equiv.refl _) (Fintype.equivOfCardEq hc₀).symm).trans (splEquiv i₀ j₀ hne)
  have h0 : E (.inl 0) = i₀ := by simp [E, splEquiv]
  have h1 : E (.inl 1) = j₀ := by simp [E, splEquiv]
  exact splPlane_core E A hA x y hxx hyy hxy (by rw [h0, h1]; exact hu)

end Local

end PI.LocCartanPair
end
end

