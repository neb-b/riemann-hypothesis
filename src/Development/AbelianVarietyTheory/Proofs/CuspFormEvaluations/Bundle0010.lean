module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SubConjTransposeOfSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.BetaEqZeroOfCharacter
section
noncomputable section

open Complex Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.LagSplit

section Defs

variable {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V]

def IsLagSection (ω : LinearMap.BilinForm R M) (π : M →ₗ[R] V) (σ : V →ₗ[R] M) : Prop :=
  (∀ z, π (σ z) = z) ∧ ∀ z w, ω (σ z) (σ w) = 0

def beta (ω : LinearMap.BilinForm R M) (σ σ' : V →ₗ[R] M) : LinearMap.BilinForm R V :=
  LinearMap.compl₁₂ ω σ σ'

end Defs

section Concrete

variable {g : ℕ}

def omegaCx (g : ℕ) : LinearMap.BilinForm ℂ (Fin g ⊕ Fin g → ℂ) :=
  LinearMap.mk₂ ℂ (fun a b => ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i)))
    (fun a a' b => by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (fun c a b => by
      rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (fun a b b' => by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (fun c a b => by
      rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring)

theorem omegaCx_apply (a b : Fin g ⊕ Fin g → ℂ) :
    omegaCx g a b = ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i)) := rfl

theorem omegaCx_eq_dot (a b : Fin g ⊕ Fin g → ℂ) :
    omegaCx g a b = (a ∘ Sum.inl) ⬝ᵥ (b ∘ Sum.inr) - (a ∘ Sum.inr) ⬝ᵥ (b ∘ Sum.inl) := by
  simp [omegaCx_apply, dotProduct, Finset.sum_sub_distrib]

theorem omegaCx_elim (m n m' n' : Fin g → ℂ) :
    omegaCx g (Sum.elim m n) (Sum.elim m' n') = m ⬝ᵥ n' - n ⬝ᵥ m' := by
  simp [omegaCx_eq_dot]

theorem omegaCx_intCast (a b : Fin g ⊕ Fin g → ℤ) :
    omegaCx g (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) = (omegaStd a b : ℂ) := by
  simp [omegaCx_apply, omegaStd]

theorem eq_omegaCx_of_intCast (B : LinearMap.BilinForm ℂ (Fin g ⊕ Fin g → ℂ))
    (hB : ∀ a b : Fin g ⊕ Fin g → ℤ,
      B (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) = (omegaStd a b : ℂ)) : B = omegaCx g := by
  classical
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℂ _) fun i j => ?_
  have e : ∀ i : Fin g ⊕ Fin g, Pi.basisFun ℂ (Fin g ⊕ Fin g) i =
      fun k => (((Pi.single i 1 : Fin g ⊕ Fin g → ℤ) k : ℤ) : ℂ) := by
    intro i; ext k; simp [Pi.single_apply]
  rw [e, e, hB, omegaCx_intCast]

def perProj (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun u := u ∘ Sum.inl + τ *ᵥ (u ∘ Sum.inr)
  map_add' u v := by
    have h1 : (u + v) ∘ Sum.inl = u ∘ Sum.inl + v ∘ Sum.inl := rfl
    have h2 : (u + v) ∘ Sum.inr = u ∘ Sum.inr + v ∘ Sum.inr := rfl
    rw [h1, h2, Matrix.mulVec_add]; abel
  map_smul' c u := by
    have h1 : (c • u) ∘ Sum.inl = c • (u ∘ Sum.inl) := rfl
    have h2 : (c • u) ∘ Sum.inr = c • (u ∘ Sum.inr) := rfl
    rw [h1, h2, Matrix.mulVec_smul, smul_add]; rfl

theorem perProj_apply (τ : Matrix (Fin g) (Fin g) ℂ) (u : Fin g ⊕ Fin g → ℂ) :
    perProj τ u = u ∘ Sum.inl + τ *ᵥ (u ∘ Sum.inr) := rfl

theorem perProj_elim (τ : Matrix (Fin g) (Fin g) ℂ) (m n : Fin g → ℂ) :
    perProj τ (Sum.elim m n) = m + τ *ᵥ n := by
  simp [perProj_apply]

def secL (g : ℕ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ) where
  toFun z := Sum.elim z 0
  map_add' z w := by ext (i | i) <;> simp
  map_smul' c z := by ext (i | i) <;> simp

theorem secL_apply (z : Fin g → ℂ) : secL g z = Sum.elim z 0 := rfl

def secH (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ) where
  toFun z := Sum.elim (-(τ.map star *ᵥ (((2 * I) • imC τ)⁻¹ *ᵥ z))) (((2 * I) • imC τ)⁻¹ *ᵥ z)
  map_add' z w := by ext (i | i) <;> simp [Matrix.mulVec_add, add_comm]
  map_smul' c z := by ext (i | i) <;> simp [Matrix.mulVec_smul]

theorem secH_apply (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : secH τ z =
    Sum.elim (-(τ.map star *ᵥ (((2 * I) • imC τ)⁻¹ *ᵥ z))) (((2 * I) • imC τ)⁻¹ *ᵥ z) := rfl

theorem dot_mulVec_symm {A : Matrix (Fin g) (Fin g) ℂ} (hA : A.IsSymm) (x y : Fin g → ℂ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (A *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq]

theorem perProj_eq_zero_iff (τ : Matrix (Fin g) (Fin g) ℂ) (u : Fin g ⊕ Fin g → ℂ) :
    perProj τ u = 0 ↔ u ∘ Sum.inl = -(τ *ᵥ (u ∘ Sum.inr)) := by
  rw [perProj_apply, add_eq_zero_iff_eq_neg]

theorem secL_isLagSection (τ : Matrix (Fin g) (Fin g) ℂ) :
    IsLagSection (omegaCx g) (perProj τ) (secL g) :=
  ⟨fun z => by simp [secL_apply, perProj_elim], fun z w => by simp [secL_apply, omegaCx_elim]⟩

theorem sub_map_star (τ : Matrix (Fin g) (Fin g) ℂ) : τ - τ.map star = (2 * I) • imC τ := by
  ext i j
  simp only [Matrix.sub_apply, imC, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp; ring

theorem imC_mul_inv {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    imC τ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) = 1 := by
  have h := congrArg (fun A : Matrix (Fin g) (Fin g) ℝ => A.map Complex.ofRealHom)
    (Matrix.mul_nonsing_inv _ hY)
  simp only [Matrix.map_mul] at h
  rw [Matrix.map_one _ (by simp) (by simp)] at h
  exact h

theorem imC_inv {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    (imC τ)⁻¹ = ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) :=
  Matrix.inv_eq_right_inv (imC_mul_inv hY)

theorem two_I_imC_mul {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    ((2 * I) • imC τ) * ((2 * I)⁻¹ • (imC τ)⁻¹) = 1 := by
  have h2 : (2 * I : ℂ) ≠ 0 := by simp
  rw [imC_inv hY, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h2, one_smul,
    imC_mul_inv hY]

theorem two_I_imC_inv {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    ((2 * I) • imC τ)⁻¹ = (2 * I)⁻¹ • (imC τ)⁻¹ :=
  Matrix.inv_eq_right_inv (two_I_imC_mul hY)

theorem two_I_imC_mul_inv {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    ((2 * I) • imC τ) * ((2 * I) • imC τ)⁻¹ = 1 := by
  rw [two_I_imC_inv hY, two_I_imC_mul hY]

theorem two_I_imC_inv_mul {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    ((2 * I) • imC τ)⁻¹ * ((2 * I) • imC τ) = 1 :=
  mul_eq_one_comm.mp (two_I_imC_mul_inv hY)

theorem perProj_secH {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    (z : Fin g → ℂ) : perProj τ (secH τ z) = z := by
  rw [secH_apply, perProj_elim, neg_add_eq_sub, ← Matrix.sub_mulVec, sub_map_star,
    Matrix.mulVec_mulVec, two_I_imC_mul_inv hY, Matrix.one_mulVec]

theorem star_mulVec_map (τ : Matrix (Fin g) (Fin g) ℂ) (n : Fin g → ℂ) :
    star (τ *ᵥ n) = τ.map star *ᵥ star n := by
  ext i; simp [Matrix.mulVec, dotProduct]

theorem mem_range_secH_iff {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    (u : Fin g ⊕ Fin g → ℂ) : u ∈ LinearMap.range (secH τ) ↔ perProj τ (star u) = 0 := by
  have key : perProj τ (star u) = 0 ↔ u ∘ Sum.inl = -(τ.map star *ᵥ (u ∘ Sum.inr)) := by
    rw [perProj_eq_zero_iff, ← star_inj, star_neg, star_mulVec_map]
    have h1 : star ((star u) ∘ Sum.inl) = u ∘ (Sum.inl : Fin g → _) := by ext i; simp
    have h2 : star ((star u) ∘ Sum.inr) = u ∘ (Sum.inr : Fin g → _) := by ext i; simp
    rw [h1, h2]
  rw [key]
  constructor
  · rintro ⟨z, rfl⟩
    simp [secH_apply]
  · intro h
    refine ⟨((2 * I) • imC τ) *ᵥ (u ∘ Sum.inr), ?_⟩
    rw [secH_apply, Matrix.mulVec_mulVec (u ∘ Sum.inr), two_I_imC_inv_mul hY, Matrix.one_mulVec, ← h]
    ext (i | i) <;> rfl

theorem eq_secH_of_conj_mem_ker {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    {u : Fin g ⊕ Fin g → ℂ} {z : Fin g → ℂ} (hu : perProj τ u = z) (hc : perProj τ (star u) = 0) :
    u = secH τ z := by
  obtain ⟨v, rfl⟩ := (mem_range_secH_iff hY u).mpr hc
  rw [perProj_secH hY] at hu
  rw [hu]

theorem secH_equivariant {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    (A : (Fin g ⊕ Fin g → ℂ) → (Fin g ⊕ Fin g → ℂ)) (B : (Fin g → ℂ) → (Fin g → ℂ)) (hB : B 0 = 0)
    (hA : ∀ u, A (star u) = star (A u)) (hAB : ∀ u, perProj τ (A u) = B (perProj τ u))
    (z : Fin g → ℂ) : secH τ (B z) = A (secH τ z) := by
  refine (eq_secH_of_conj_mem_ker hY ?_ ?_).symm
  · rw [hAB, perProj_secH hY]
  · rw [← hA, hAB, (mem_range_secH_iff hY _).mp ⟨z, rfl⟩, hB]

theorem beta_secL (σ : (Fin g → ℂ) →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ)) (z w : Fin g → ℂ) :
    beta (omegaCx g) σ (secL g) z w = -((σ z ∘ Sum.inr) ⬝ᵥ w) := by
  simp [beta, omegaCx_eq_dot, secL_apply]

theorem beta_secH_secL' {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hY : IsUnit (τ.map Complex.im).det) (z w : Fin g → ℂ) :
    beta (omegaCx g) (secH τ) (secL g) z w = -(2 * I)⁻¹ * (z ⬝ᵥ (imC τ)⁻¹ *ᵥ w) := by
  have hs : (imC τ).IsSymm := (hτ.map _).map _
  rw [beta_secL, secH_apply, Sum.elim_comp_inr, two_I_imC_inv hY, Matrix.smul_mulVec,
    smul_dotProduct, dot_mulVec_symm hs.inv, smul_eq_mul, neg_mul]

theorem beta_secH_secL {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hY : IsUnit (τ.map Complex.im).det) (z w : Fin g → ℂ) :
    beta (omegaCx g) (secH τ) (secL g) z w =
      -(2 * I)⁻¹ * (z ⬝ᵥ ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ w) := by
  rw [beta_secH_secL' hτ hY, imC_inv hY]

end Concrete

section General

variable {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V]
  {ω : LinearMap.BilinForm R M} {π : M →ₗ[R] V} {σ σ' σ'' : V →ₗ[R] M}

variable {O : Type*} [CommRing O] [StarRing O] [Module O M] [Module O V]

end General

end GlobalTheory.LagSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjEmbRt
section
namespace GlobalTheory.ConjugateEmbeddingSquareRoot

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem conj_eq_neg_of_sq {z : ℂ} {r : ℝ} (hr : 0 < r) (h : z ^ 2 = -(r : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  have hre : z.re * z.re - z.im * z.im = -r := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have him : z.re * z.im + z.im * z.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h0 : z.re = 0 := by
    have hm : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hm with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp

theorem conjEmb_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : E →+* ℂ) :
    conjEmb τ (H.rt : E) = -τ (H.rt : E) := by
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have h1 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : (τ (H.rt : E)) ^ 2 = -(((H.d : ℝ)) : ℂ) := by
    rw [← map_pow, h1]
    simp
  exact conj_eq_neg_of_sq hd h2

end GlobalTheory.ConjugateEmbeddingSquareRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNeZeroOnCoset
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.TorsionCoset

variable {E : Type} [Field E] [NumberField E]

theorem eps_zero (X : PT E) : X.eps 0 = 1 := by
  have h := X.eps_add 0 (zero_mem _) 0 (zero_mem _)
  simp only [add_zero] at h
  rcases X.eps_pm 0 (zero_mem _) with h1 | h1
  · exact h1
  · rw [h1] at h
    norm_num [Hf] at h

theorem natCast_smul_mem (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (k : ℕ) :
    (k : ℂ) • x ∈ X.L := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx k

theorem eps_natCast_smul (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (k : ℕ) :
    (X.eps ((k : ℂ) • x) : ℝ) = (X.eps x : ℝ) ^ k := by
  induction k with
  | zero => simp [eps_zero]
  | succ k ih =>
    have h := X.eps_add _ (natCast_smul_mem X hx k) x hx
    have him : (Hf ((k : ℂ) • x) x).im = 0 := by
      unfold Hf
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [PiLp.smul_apply, mul_assoc, Complex.mul_conj]
    rw [show ((k + 1 : ℕ) : ℂ) • x = (k : ℂ) • x + x by push_cast; rw [add_smul, one_smul],
      h, ih, him]
    simp [pow_succ]

theorem isPi_natCast (X : PT E) (n : ℕ) : IsPi X (n ^ 2) ((n : ℂ) • LinearMap.id) := by
  refine ⟨fun α v => ?_, fun x hx => ?_, fun v w => ?_, fun x hx => ?_⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    ext i
    simp [act]
    ring
  · exact natCast_smul_mem X hx n
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    unfold Hf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
    ring
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    have h := eps_natCast_smul X hx n
    have h2 : (X.eps x : ℝ) ^ n = (X.eps x : ℝ) ^ (n ^ 2) := by
      rcases X.eps_pm x hx with h1 | h1
      · simp [h1]
      · rw [h1]
        push_cast
        rw [sq, pow_mul]
        rcases neg_one_pow_eq_or ℝ n with h3 | h3 <;> simp [h3]
    exact_mod_cast h.trans h2

theorem exists_isReps (X : PT E) (n : ℕ) (hn : n ≠ 0) :
    ∃ K, IsReps X (n ^ 2) 1 ((n : ℂ) • LinearMap.id) K := by
  classical
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsq : ∀ x : Vsp X.dim, ((n ^ 2 : ℕ) : ℂ) • x = (n : ℂ) • (n : ℂ) • x := fun x => by
    rw [smul_smul]; push_cast; rw [sq]
  let S : Set (Fin 1 → Vsp X.dim) :=
    {b | (n : ℂ) • (n : ℂ) • b 0 ∈ X.L ∧ (n : ℂ) • b 0 ∈ ZSpan.fundamentalDomain X.b}
  have hS : S.Finite := by
    have hb := ZSpan.setFinite_inter X.b
      ((ZSpan.fundamentalDomain_isBounded X.b).smul₀ (n : ℂ))
    refine Set.Finite.of_injOn (f := fun b => (n : ℂ) • (n : ℂ) • b 0) ?_ ?_ hb
    · intro b hb
      exact ⟨Set.smul_mem_smul_set hb.2, hb.1⟩
    · intro b _ c _ h
      funext k
      rw [Subsingleton.elim k 0]
      exact smul_right_injective _ hn' (smul_right_injective _ hn' h)
  refine ⟨hS.toFinset, fun b hb k => ?_, fun b hb => ?_⟩
  · rw [Subsingleton.elim k 0, hsq]
    exact (hS.mem_toFinset.1 hb).1
  · have hb0 := hb 0
    rw [hsq] at hb0
    have hfl : (n : ℂ) • b 0 - ZSpan.fract X.b ((n : ℂ) • b 0) ∈ X.L := by
      rw [ZSpan.fract_apply, sub_sub_cancel]
      exact (ZSpan.floor X.b _).2
    refine ⟨fun _ => (n : ℂ)⁻¹ • ZSpan.fract X.b ((n : ℂ) • b 0), ⟨hS.mem_toFinset.2 ⟨?_, ?_⟩,
      fun k => ?_⟩, ?_⟩
    · simp only [smul_inv_smul₀ hn']
      have := sub_mem hb0 (natCast_smul_mem X hfl n)
      rwa [smul_sub, sub_sub_cancel] at this
    · simp only [smul_inv_smul₀ hn']
      exact ZSpan.fract_mem_fundamentalDomain X.b _
    · rw [Subsingleton.elim k 0]
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_sub, smul_inv_smul₀ hn'] using hfl
    · rintro c ⟨hc, hc'⟩
      have h1 := (hS.mem_toFinset.1 hc).2
      have h2 := hc' 0
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_sub] at h2
      funext k
      rw [Subsingleton.elim k 0, eq_inv_smul_iff₀ hn', ← (ZSpan.fract_eq_self.2 h1),
        ZSpan.fract_eq_fract, neg_add_eq_sub]
      exact h2

theorem exists_ne_zero_on_coset (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E)
    (s : (Fin 1 → Vsp X.dim) → ℂ) (hs : s ∈ X.Sec 1 1) (h0 : s ≠ 0) (n : ℕ) (hn : 2 ≤ n)
    (a : Vsp X.dim) : ∃ y ∈ X.L, s (fun _ => a + ((n : ℂ)⁻¹) • y) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hn0 : n ≠ 0 := by omega
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hq : 2 ≤ n ^ 2 := by nlinarith
  obtain ⟨K, hK⟩ := exists_isReps X n hn0
  obtain ⟨-, -, -, hspan⟩ :=
    thetaBasis_holds E X (n ^ 2) 1 _ (by omega) (isPi_natCast X n) s hs h0 K hK
  obtain ⟨F, hF, hFv⟩ := GlobalTheory.BasePointFree.exists_sec_ne_zero E X s hs h0 (n ^ 2) hq
    (fun _ => (n : ℂ)⁻¹ • a)
  apply hFv
  have hle : Submodule.span ℂ ((fun b => X.U (n ^ 2) b (s0 X ((n : ℂ) • LinearMap.id) s)) ''
      (K : Set _)) ≤ LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ => ℂ)
        (fun _ : Fin 1 => (n : ℂ)⁻¹ • a)) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have h := hcon _ (neg_mem (hK.1 b hb 0))
    have e : a + (n : ℂ)⁻¹ • -(((n ^ 2 : ℕ) : ℂ) • b 0) = (n : ℂ) • ((n : ℂ)⁻¹ • a - b 0) := by
      rw [smul_sub, smul_inv_smul₀ hn', smul_neg, smul_smul, sub_eq_add_neg]
      congr 3
      push_cast
      field_simp
    rw [e] at h
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, PT.U, s0,
      Fin.prod_univ_one, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, h, mul_zero]
  exact hle (hspan hF)

end GlobalTheory.TorsionCoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSymplecticCoordinatesAdapted
section
open Module Function

namespace GlobalTheory


open Module Function in
theorem _root_.GlobalTheory.exists_symplectic_coordinates_adapted {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
    [Module.Finite ℤ Λ] {ω : LinearMap.BilinForm ℤ Λ} (hω : ω.IsAlt) (hp : Bijective ω)
    {I : Submodule ℤ Λ} (hsat : ∀ (k : ℤ) (x : Λ), k ≠ 0 → k • x ∈ I → x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, ω x y = 0) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ) (S : Finset (Fin g)),
      (∀ a b, ω (bas a) (bas b) = ε * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) ∧
      I = Submodule.span ℤ ((fun k => bas (Pi.single (Sum.inl k) 1)) '' (S : Set (Fin g))) ∧
      2 * g = finrank ℤ Λ := by
  obtain ⟨r, v⟩ := Submodule.basisOfPid (Module.Free.chooseBasis ℤ Λ) I
  have htf : Module.IsTorsionFree ℤ (Λ ⧸ I) := (_root_.GlobalTheory.isTorsionFree_quotient_iff I).mpr hsat
  have hle : I ≤ ω.orthogonal I := fun x hx =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun y hy => hiso y hy x hx
  obtain ⟨g, b, hb, hbv⟩ := _root_.GlobalTheory.exists_isSymplecticBasis_extend hω hp htf hle v
  set e : Fin r ⊕ Fin g ≃ Fin (r + g) := finSumFinEquiv
  set b' := b.reindex (e.sumCongr e) with hb'
  have hsymp : _root_.GlobalTheory.IsSymplecticBasis ω b' := hb.reindex e
  have hb'v : ∀ i, b' (Sum.inl (e (Sum.inl i))) = (v i : Λ) := by
    intro i
    rw [hb', Module.Basis.reindex_apply]
    simp [hbv]
  obtain ⟨u, hu⟩ : IsUnit ε := Int.isUnit_iff.mpr hε
  let D : (Fin (r + g) ⊕ Fin (r + g) → ℤ) ≃ₗ[ℤ] (Fin (r + g) ⊕ Fin (r + g) → ℤ) :=
    LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (Sum.elim (fun _ => 1) (fun _ => u) i)
  have hD : ∀ a i, D a i = Sum.elim (fun _ => (1 : ℤ)) (fun _ => ε) i * a i := by
    intro a i
    rcases i with i | i <;> change (_ : ℤˣ) • a _ = _ <;> simp [Units.smul_def, hu]
  refine ⟨r + g, D.trans b'.equivFun.symm, Finset.univ.image fun i => e (Sum.inl i), ?_, ?_, ?_⟩
  · intro a c
    rw [hsymp.apply_eq_sum hω]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearEquiv.trans_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hD,
      Sum.elim_inl, Sum.elim_inr]
    ring
  · have hspan : Submodule.span ℤ (Set.range fun i => (v i : Λ)) = I := by
      have h := congrArg (Submodule.map I.subtype) v.span_eq
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h
      exact h
    have hsingle : ∀ k, D (Pi.single (Sum.inl k) 1) = Pi.single (Sum.inl k) 1 := by
      intro k
      funext i
      rw [hD]
      rcases i with i | i <;> simp [Pi.single_apply]
    rw [← hspan]
    congr 1
    ext x
    simp only [Set.mem_image, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      LinearEquiv.trans_apply, hsingle, _root_.Basis.equivFun_symm_single]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e (Sum.inl i), ⟨i, rfl⟩, hb'v i⟩
    · rintro ⟨k, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hb'v i).symm⟩
  · rw [Module.finrank_eq_card_basis b']
    simp
    ring

end GlobalTheory
end

