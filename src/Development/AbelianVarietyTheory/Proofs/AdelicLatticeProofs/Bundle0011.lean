module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraEmbIntegralAndRational
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EmbInt

theorem res_mul' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (g h : Matrix κ κ A) :
    res b (g * h) = res b g * res b h := by
  ext p q
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

theorem res_one' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) :
    res b (1 : Matrix κ κ A) = 1 := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.one_apply]
  by_cases h : p.1 = q.1
  · rw [if_pos h, map_one, Matrix.one_apply]
    by_cases h' : p.2 = q.2
    · rw [if_pos h', if_pos (Prod.ext h h')]
    · rw [if_neg h', if_neg (fun e => h' (congrArg Prod.snd e))]
  · rw [if_neg h, map_zero, Matrix.zero_apply, if_neg (fun e => h (congrArg Prod.fst e))]

theorem repr_mem {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    (b : Module.Basis β R A) (R₀ : Subring R) (h1 : ∀ i, b.repr 1 i ∈ R₀) (x : A)
    (hx : ∀ p q, Algebra.leftMulMatrix b x p q ∈ R₀) (k : β) : b.repr x k ∈ R₀ := by

  have hsum : x = ∑ i, b.repr 1 i • (x * b i) := by
    conv_lhs => rw [← mul_one x, ← b.sum_repr 1]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
  have hk : b.repr x k = ∑ i, b.repr 1 i * Algebra.leftMulMatrix b x k i := by
    conv_lhs => rw [hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hk]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (h1 i) (hx k i)

theorem inv_mem {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (R₀ : Subring R)
    (M N : Matrix ι ι R) (hNM : N * M = 1) (hM : ∀ p q, M p q ∈ R₀) (hd : N.det ∈ R₀) (p q : ι) :
    N p q ∈ R₀ := by

  have hadj : N = N.det • M.adjugate := by
    have h1 : N * M * M.adjugate = M.adjugate := by rw [hNM, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h1
    have hd1 : N.det * M.det = 1 := by rw [← Matrix.det_mul, hNM, Matrix.det_one]
    rw [← h1, smul_smul, hd1, one_smul]

  let M' : Matrix ι ι R₀ := Matrix.of fun p q => ⟨M p q, hM p q⟩
  have hM' : R₀.subtype.mapMatrix M' = M := by ext; rfl
  have hA : M.adjugate p q = R₀.subtype (M'.adjugate p q) := by
    rw [← hM', ← RingHom.map_adjugate]; rfl
  rw [hadj, Matrix.smul_apply, smul_eq_mul, hA]
  exact Subring.mul_mem _ hd (M'.adjugate p q).2

theorem repr_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (x : F) (k : β) :
    b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k) := by

  have hq : ∀ c : ℚ, algebraMap R A (algebraMap ℚ R c) = algebraMap F A (algebraMap ℚ F c) := fun c =>
    DFunLike.congr_fun (RingHom.ext_rat ((algebraMap R A).comp (algebraMap ℚ R))
      ((algebraMap F A).comp (algebraMap ℚ F))) c
  have hx : algebraMap F A x = ∑ i, algebraMap ℚ R (ω.repr x i) • b i := by
    conv_lhs => rw [← ω.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hq, hb]
  rw [hx, Module.Basis.repr_sum_self]

theorem res_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {κ R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (g : Matrix κ κ F) :
    res b (g.map (algebraMap F A)) = (res ω g).map (algebraMap ℚ R) := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, hb,
    ← map_mul]
  exact repr_map ω b hb _ _

theorem emb_integral_and_rational : (∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (R₀ : Subring R) (u : GL κ A), (∀ i, b.repr 1 i ∈ R₀) → (∀ p q, emb b u p q ∈ R₀) → ∀ i j k, b.repr ((u : Matrix κ κ A) i j) k ∈ R₀ ∧ b.repr (((u⁻¹ : GL κ A) : Matrix κ κ A) i j) k ∈ R₀) ∧ ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (κ : Type) [Fintype κ] [DecidableEq κ] (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ γ : GL κ F, emb b (Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ) = (emb ω γ).map (algebraMap ℚ R) := by
  refine ⟨fun R A β κ _ _ _ _ _ _ _ b R₀ u h1 he i j k => ?_,
    fun F β _ _ _ _ ω κ _ _ R A _ _ _ _ _ b hb γ => ?_⟩
  ·

    have hres : ∀ p q, res b (u : Matrix κ κ A) p q ∈ R₀ := fun p q => by
      simpa [emb] using he (Sum.inl p) (Sum.inl q)
    have hdet : (res b ((u⁻¹ : GL κ A) : Matrix κ κ A)).det ∈ R₀ := by
      simpa [emb] using he (Sum.inr ()) (Sum.inr ())
    have hinv : res b ((u⁻¹ : GL κ A) : Matrix κ κ A) * res b (u : Matrix κ κ A) = 1 := by
      rw [← res_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, res_one']
    have hres' : ∀ p q, res b ((u⁻¹ : GL κ A) : Matrix κ κ A) p q ∈ R₀ :=
      fun p q => inv_mem R₀ _ _ hinv hres hdet p q
    exact ⟨repr_mem b R₀ h1 _ (fun p q => hres (i, p) (j, q)) k,
      repr_mem b R₀ h1 _ (fun p q => hres' (i, p) (j, q)) k⟩
  · have hc : ((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ : GL κ A) :
        Matrix κ κ A) = (γ : Matrix κ κ F).map (algebraMap F A) := rfl
    have hc' : (((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ)⁻¹ : GL κ A) :
        Matrix κ κ A) = ((γ⁻¹ : GL κ F) : Matrix κ κ F).map (algebraMap F A) := by
      rw [← map_inv]; rfl
    unfold emb
    rw [hc, hc', res_map ω b hb, res_map ω b hb, Matrix.fromBlocks_map]
    ext (x | x) (y | y) <;> simp [RingHom.map_det]

end GlobalTheory.ClassFin.EmbInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraToSpecialLinearEmbInjectiveHom
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EmbHom

variable {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
  [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A)

theorem res_one' : res b (1 : Matrix κ κ A) = 1 := by
  ext ⟨i, x⟩ ⟨j, y⟩
  by_cases h : i = j
  · subst h
    simp [res, Matrix.one_apply]
  · simp [res, Matrix.one_apply, h]

omit [DecidableEq κ] in
theorem res_mul' (g h : Matrix κ κ A) : res b (g * h) = res b g * res b h := by
  ext ⟨i, x⟩ ⟨j, y⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

omit [Fintype κ] [DecidableEq κ] in
theorem res_inj' (g h : Matrix κ κ A) (e : res b g = res b h) : g = h := by
  ext i j
  apply Algebra.leftMulMatrix_injective b
  ext x y
  exact congrFun (congrFun e (i, x)) (j, y)

theorem emb_one' : emb b (1 : GL κ A) = 1 := by
  unfold emb
  rw [inv_one, Units.val_one, res_one', Matrix.det_one, ← Matrix.fromBlocks_one]
  congr 1

theorem emb_mul' (g h : GL κ A) : emb b (g * h) = emb b g * emb b h := by
  unfold emb
  rw [Matrix.fromBlocks_multiply, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, res_mul', res_mul',
    Matrix.det_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  ext i j
  simp [Matrix.mul_apply, mul_comm]

theorem emb_det' (g : GL κ A) : (emb b g).det = 1 := by
  unfold emb
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (n := Unit), Matrix.of_apply, ← Matrix.det_mul, ← res_mul',
    Units.mul_inv, res_one', Matrix.det_one]

theorem emb_adjugate' (g : GL κ A) : (emb b g).adjugate = emb b g⁻¹ := by
  have h1 : emb b g * emb b g⁻¹ = 1 := by rw [← emb_mul', mul_inv_cancel, emb_one']
  calc (emb b g).adjugate = (emb b g).adjugate * (emb b g * emb b g⁻¹) := by rw [h1, Matrix.mul_one]
    _ = emb b g⁻¹ := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, emb_det', one_smul, Matrix.one_mul]

theorem emb_injective' : Function.Injective (fun g : GL κ A => emb b g) := by
  intro g h e
  apply Units.ext
  apply res_inj' b
  exact (Matrix.fromBlocks_inj.mp e).1

theorem emb_hom : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), emb b (1 : GL κ A) = 1 ∧ (∀ g h : GL κ A, emb b (g * h) = emb b g * emb b h) ∧ (∀ g : GL κ A, (emb b g).det = 1 ∧ (emb b g).adjugate = emb b g⁻¹) ∧ Function.Injective (fun g : GL κ A => emb b g) := by
  intro R A β κ _ _ _ _ _ _ _ b
  exact ⟨emb_one' b, emb_mul' b, fun g => ⟨emb_det' b g, emb_adjugate' b g⟩, emb_injective' b⟩

end GlobalTheory.ClassFin.EmbHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramLeadingMinorLowerBoundIntegral
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem gramLB_shift {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    ∃ U : Matrix n n ℝ, U * Uᴴ = 1 ∧
      A + t • (1 : Matrix n n ℝ) = U * diagonal (fun i => hA.eigenvalues i + t) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℝ), Unitary.coe_mul_star_self _, ?_⟩
  have hU : (hA.eigenvectorUnitary : Matrix n n ℝ) * star (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self _
  have hD : diagonal (fun i => hA.eigenvalues i + t) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) + t • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, ← star_eq_conjTranspose, hU]

theorem gramLB_one_le_det {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℝ}
    (hR : R.PosSemidef) : 1 ≤ (R + 1).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hR.1 1
  rw [one_smul] at hEq
  have hdet : U.det * Uᴴ.det = 1 := by rw [← det_mul, hU, det_one]
  rw [hEq, det_mul, det_mul, det_diagonal]
  have e : U.det * (∏ i, (hR.1.eigenvalues i + 1)) * Uᴴ.det = ∏ i, (hR.1.eigenvalues i + 1) := by
    linear_combination (∏ i, (hR.1.eigenvalues i + 1)) * hdet
  rw [e]
  calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
    _ ≤ ∏ i, (hR.1.eigenvalues i + 1) :=
      Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => by linarith [hR.eigenvalues_nonneg i]

theorem gramLB_exists_shift {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosDef) : ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ (A - k • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ hA.1.eigenvalues i := by
    rcases isEmpty_or_nonempty n with hn | hn
    · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_min hA.1.eigenvalues
      exact ⟨_, hA.eigenvalues_pos i0, hi0⟩
  refine ⟨min 1 m, lt_min one_pos hm0, min_le_left _ _, ?_⟩
  obtain ⟨U, -, hEq⟩ := gramLB_shift hA.1 (-(min 1 m))
  rw [sub_eq_add_neg, ← neg_smul, hEq]
  exact (posSemidef_diagonal_iff.2 fun i => by linarith [hm i, min_le_right 1 m]).mul_mul_conjTranspose_same U

open scoped MatrixOrder in
theorem gramLB_det_mono {n : Type} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℝ}
    (hP : P.PosDef) (hQ : Q.PosSemidef) : P.det ≤ (P + Q).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hP.1 0
  simp only [zero_smul, add_zero] at hEq
  have hd : ∀ i, 0 < hP.1.eigenvalues i := hP.eigenvalues_pos
  have hUU : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  let s : n → ℝ := fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹
  let B : Matrix n n ℝ := U * diagonal s
  have hBt : Bᴴ = diagonal s * Uᴴ := by
    simp [B]
  have hBPB : Bᴴ * P * B = 1 := by
    rw [hBt, hEq]
    simp only [B, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
      diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hs : Real.sqrt (hP.1.eigenvalues i) * Real.sqrt (hP.1.eigenvalues i) = hP.1.eigenvalues i :=
      Real.mul_self_sqrt (hd i).le
    have hs0 : Real.sqrt (hP.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s]
    field_simp
    try nlinarith [hs, Real.sq_sqrt (hd i).le]
  have hsum : Bᴴ * (P + Q) * B = 1 + Bᴴ * Q * B := by
    rw [Matrix.mul_add, Matrix.add_mul, hBPB]
  have h1 : Bᴴ.det * B.det * P.det = 1 := by
    have e := congrArg det hBPB
    rw [det_mul, det_mul, det_one] at e
    linear_combination e
  have h2 : Bᴴ.det * B.det * (P + Q).det = (1 + Bᴴ * Q * B).det := by
    rw [← hsum, det_mul (Bᴴ * (P + Q)) B, det_mul Bᴴ (P + Q)]
    ring
  have h3 : 1 ≤ (1 + Bᴴ * Q * B).det := by
    rw [add_comm]
    exact gramLB_one_le_det (hQ.conjTranspose_mul_mul_same B)
  have hc : 0 < Bᴴ.det * B.det := by
    have := hP.det_pos
    by_contra hneg
    nlinarith [not_lt.mp hneg]
  exact le_of_mul_le_mul_left (by linarith) hc

theorem gramLB_posDef {n : Type} [Fintype n] [DecidableEq n] {g : Matrix n n ℝ}
    (hg : g.det ≠ 0) : (gᵀ * g).PosDef := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact PosDef.conjTranspose_mul_self g
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det g).2 (Ne.isUnit hg)))

theorem gram_leading_minor_lower_bound :
    ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ γ : Matrix (Fin N) (Fin N) ℤ, γ.det ≠ 0 → ∀ (j : ℕ) (h : j ≤ N), c ≤ (((g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ))).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  intro N g hg
  obtain ⟨k, hk0, hk1, hkQ⟩ := gramLB_exists_shift (gramLB_posDef hg)
  refine ⟨k ^ N, pow_pos hk0 N, fun γ hγ j hj => ?_⟩
  set Γ : Matrix (Fin N) (Fin N) ℝ := γ.map (Int.cast : ℤ → ℝ) with hΓ
  set E : Fin j → Fin N := Fin.castLE hj with hE
  let C : Matrix (Fin N) (Fin j) ℝ := Γ.submatrix id E
  let Cz : Matrix (Fin N) (Fin j) ℤ := γ.submatrix id E
  have hGram : ((g * Γ)ᵀ * (g * Γ)).submatrix E E = Cᵀ * (gᵀ * g) * C := by
    have e1 : (g * Γ)ᵀ * (g * Γ) = Γᵀ * (gᵀ * g) * Γ := by
      rw [transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.submatrix_mul _ _ E id E Function.bijective_id,
      Matrix.submatrix_mul _ _ E id id Function.bijective_id, submatrix_id_id, transpose_submatrix]
  have hsplit : Cᵀ * (gᵀ * g) * C = k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    abel
  have hΓdet : Γ.det ≠ 0 := by
    have e := (Int.castRingHom ℝ).map_det γ
    rw [show Γ = (Int.castRingHom ℝ).mapMatrix γ from rfl, ← e]
    simpa using hγ
  have hCinj : Function.Injective C.mulVec := by
    have hC : C = Γ * (1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E := by
      rw [← Matrix.submatrix_id_id Γ, ← Matrix.submatrix_mul _ _ id id E Function.bijective_id,
        Matrix.mul_one]
    have hI : Function.Injective ((1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E).mulVec := by
      intro x y hxy
      funext a
      have hEinj : Function.Injective E := Fin.castLE_injective hj
      have e := congrFun hxy (E a)
      simpa [mulVec, dotProduct, Matrix.one_apply, hEinj.eq_iff] using e
    rw [hC]
    intro x y hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact hI (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det Γ).2 (Ne.isUnit hΓdet)) hxy)
  have hCC : (Cᵀ * C).PosDef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact PosDef.conjTranspose_mul_self C hCinj
  have hQ' : (Cᵀ * (gᵀ * g - k • 1) * C).PosSemidef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hkQ.conjTranspose_mul_mul_same C
  have hCz : Cᵀ * C = (Int.castRingHom ℝ).mapMatrix (Czᵀ * Cz) := by
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
    rfl
  have hdet1 : 1 ≤ (Cᵀ * C).det := by
    have hpos := hCC.det_pos
    rw [hCz, ← RingHom.map_det, eq_intCast] at hpos
    rw [hCz, ← RingHom.map_det, eq_intCast]
    have hz : 0 < (Czᵀ * Cz).det := by exact_mod_cast hpos
    have hz1 : (1 : ℤ) ≤ (Czᵀ * Cz).det := hz
    exact_mod_cast hz1
  calc k ^ N ≤ k ^ j := pow_le_pow_of_le_one hk0.le hk1 hj
    _ ≤ k ^ j * (Cᵀ * C).det := le_mul_of_one_le_right (pow_nonneg hk0.le _) hdet1
    _ = (k • (Cᵀ * C)).det := by rw [det_smul, Fintype.card_fin]
    _ ≤ (k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C).det := gramLB_det_mono (hCC.smul hk0) hQ'
    _ = _ := by rw [← hsplit, ← hGram]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.finite_places_over (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v}.Finite := by
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).preimage
    (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.places_over : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ SE : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), ∃ e : ℕ, 0 < e ∧ ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x ^ e := by
  intro F E _ _ _ _ _
  refine ⟨fun S => ?_, fun v => ?_, fun w => ?_⟩
  · have hfin : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S}.Finite := by
      have hU : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S} =
          ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v} := by
        ext w; simp
      rw [hU]
      exact S.finite_toSet.biUnion fun v _ => _root_.GlobalTheory.QNorm.finite_places_over F E v
    exact ⟨hfin.toFinset, fun w => by simp⟩
  · obtain ⟨P, hmax, hover⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral v.asIdeal (S := 𝓞 E)
    have hne : P ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [hover.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
    exact ⟨⟨P, hmax.isPrime, hne⟩, HeightOneSpectrum.ext hover.over.symm⟩
  · haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    refine ⟨(w.under (𝓞 F)).asIdeal.ramificationIdx' w.asIdeal, Nat.pos_of_ne_zero ?_,
      fun x => ?_⟩
    · refine Ideal.IsDedekindDomain.ramificationIdx'_ne_zero ?_ w.isPrime Ideal.map_comap_le
      rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
      exact (w.under (𝓞 F)).ne_bot
    · rw [Ideal.ramificationIdx'_eq_ramificationIdx
        (w.under (𝓞 F)).asIdeal w.asIdeal (w.under (𝓞 F)).ne_bot]
      exact (HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 F)) w x).symm

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HigherUnitsLeSquaresHigherUnits
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

namespace DeepSquares

end DeepSquares

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exp_neg_two_mul_le_mul_of_lt {e : ℕ} {a b : ℤᵐ⁰}
    (ha : WithZero.exp (-((e : ℤ) + 1)) < a) (hb : WithZero.exp (-((e : ℤ) + 1)) < b) :
    WithZero.exp (-(2 * (e : ℤ))) ≤ a * b := by
  obtain ⟨k, rfl⟩ : ∃ k, WithZero.exp k = a := ⟨_, WithZero.exp_log (ne_bot_of_gt ha)⟩
  obtain ⟨l, rfl⟩ : ∃ l, WithZero.exp l = b := ⟨_, WithZero.exp_log (ne_bot_of_gt hb)⟩
  rw [WithZero.exp_lt_exp] at ha hb
  rw [← WithZero.exp_add, WithZero.exp_le_exp]
  omega


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : ℕ),
    Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) →
    _root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (2 * e + 1) ≤
      _root_.GlobalTheory.QNorm.sqs
        (_root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (e + 1)) := by
  intro F _ _ v e h2 x hx
  unfold _root_.GlobalTheory.QNorm.hiUnits at hx
  unfold _root_.GlobalTheory.QNorm.sqs _root_.GlobalTheory.QNorm.hiUnits
  obtain ⟨-, hx1⟩ := hx
  set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  have h4 : w 4 = WithZero.exp (-(2 * e : ℤ)) := by
    have : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
    rw [this, map_mul, h2, ← WithZero.exp_add]; congr 1; ring
  have hlt : w ((x : v.adicCompletion F) - 1) < w 4 := by
    refine lt_of_le_of_lt hx1 ?_
    rw [h4, WithZero.exp_lt_exp]; push_cast; omega
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v _ hlt
  have hprod : w (r - 1) * w (r + 1) ≤ WithZero.exp (-((2 * e + 1 : ℕ) : ℤ)) := by
    rw [← map_mul, show (r - 1) * (r + 1) = r * r - 1 by ring, ← hr]; exact hx1
  obtain ⟨s, hs, hs1⟩ : ∃ s : v.adicCompletion F, s * s = x ∧
      w (s - 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ)) := by
    by_cases hm : w (r - 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ))
    · exact ⟨r, hr.symm, hm⟩
    by_cases hp : w (r + 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ))
    · refine ⟨-r, by rw [neg_mul_neg, hr], ?_⟩
      rwa [show -r - 1 = -(r + 1) by ring, Valuation.map_neg]
    exfalso
    push_cast at hm hp hprod
    have := (exp_neg_two_mul_le_mul_of_lt (not_le.mp hm) (not_le.mp hp)).trans hprod
    rw [WithZero.exp_le_exp] at this
    omega
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hs
    exact x.ne_zero hs.symm
  have hsv : w s = 1 := by
    have hlt1 : w (s - 1) < 1 :=
      hs1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using Valuation.map_one_add_of_lt w hlt1
  refine ⟨Units.mk0 s hs0, ⟨hsv, hs1⟩, ?_⟩
  ext
  simp [pow_two, hs]

end GlobalTheory.QNorm
end

