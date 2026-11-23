module

public import Formalism.PeriodIntegrals.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.ConjTMulMulApply
section
noncomputable section

open Matrix PI.FlagGramNonneg

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem tau_form {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (v w : V) :
    τ (hT v w) = star (fun n => τ (b.repr v n)) ⬝ᵥ
      (((PI.FlagGramNonneg.gram hT b).map τ) *ᵥ (fun n => τ (b.repr w n))) := by
  conv_lhs => rw [← b.sum_repr v, ← b.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul,
    map_mul, starRingEnd_apply, hτ, dotProduct, mulVec, Matrix.map_apply, PI.FlagGramNonneg.gram,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem conjT_mul_mul_apply {m n : Type} [Fintype m] (A : Matrix m n ℂ) (B : Matrix m m ℂ) (i j : n) :
    (Aᴴ * B * A) i j = star (fun k => A k i) ⬝ᵥ (B *ᵥ fun k => A k j) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, dotProduct, mulVec, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem gram_tau {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) {ι : Type} (y : ι → V) (i j : ι) :
    ((Matrix.of fun n k => τ (b.repr (y k) n))ᴴ * ((PI.FlagGramNonneg.gram hT b).map τ) *
      (Matrix.of fun n k => τ (b.repr (y k) n))) i j = τ (hT (y i) (y j)) := by
  rw [conjT_mul_mul_apply, tau_form hT b τ hτ]
  rfl

end PI.UnitaryGroupMassFormula.FlagGramNonneg
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.HasSignatureExistsNonneg
section
noncomputable section

open Matrix PI.FlagGramNonneg
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem cT_star_eq {m n : Type} (M : Matrix m n ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply]

theorem form_mulVec {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℂ) (B : Matrix m m ℂ)
    (u : n → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (B *ᵥ (A *ᵥ u)) = star u ⬝ᵥ ((Aᴴ * B * A) *ᵥ u) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem form_reindex {n m : Type} [Fintype n] [Fintype m] (e : n ≃ m) (J : Matrix n n ℂ)
    (x : n → ℂ) :
    star (fun i => x (e.symm i)) ⬝ᵥ ((J.reindex e e) *ᵥ (fun i => x (e.symm i))) =
      star x ⬝ᵥ (J *ᵥ x) := by
  have h : (J.reindex e e) *ᵥ (fun i => x (e.symm i)) = fun i => (J *ᵥ x) (e.symm i) := by
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    funext i
    simp [Function.comp_def]
  rw [h]
  simp only [dotProduct, Pi.star_apply]
  exact Equiv.sum_comp e.symm (fun i => star (x i) * (J *ᵥ x) i)

theorem Jpq_mulVec_of {p q : ℕ} (u : Fin p ⊕ Fin q → ℂ) (hu : ∀ j, u (Sum.inr j) = 0) :
    Jpq p q *ᵥ u = u := by
  have h0 : (u ∘ Sum.inr) = 0 := funext hu
  rw [Jpq, Matrix.fromBlocks_mulVec, h0]
  funext i
  cases i <;> simp [hu]

theorem hasSignature_exists_nonneg {N p q : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix (Fin N) (Fin N) ℂ) (hJ : HasSignature J p q) (hq : q < Fintype.card ι)
    (X : Matrix (Fin N) ι ℂ) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ 0 ≤ (star (X *ᵥ c) ⬝ᵥ (J *ᵥ (X *ᵥ c))).re := by
  obtain ⟨e, P, hP⟩ := hJ
  let Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix _ _ ℂ)
  let Y : Matrix (Fin p ⊕ Fin q) ι ℂ := Q * X.submatrix e.symm id
  let K : Matrix (Fin q) ι ℂ := fun j l => Y (Sum.inr j) l
  have hk : LinearMap.ker (Matrix.mulVecLin K) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa [Module.finrank_fintype_fun_eq_card] using hq)
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp hk
  refine ⟨c, hc0, ?_⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc
  have hy : ∀ j, (Y *ᵥ c) (Sum.inr j) = 0 := fun j => congrFun hc j
  have hx : (fun i => (X *ᵥ c) (e.symm i)) = (P : Matrix _ _ ℂ) *ᵥ (Y *ᵥ c) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
    have hPQ : (P : Matrix _ _ ℂ) * Q = 1 := Units.mul_inv P
    rw [hPQ, Matrix.one_mul]
    rfl
  have key : star (X *ᵥ c) ⬝ᵥ (J *ᵥ (X *ᵥ c)) = star (Y *ᵥ c) ⬝ᵥ (Y *ᵥ c) := by
    rw [cT_star_eq] at hP
    rw [← form_reindex e J (X *ᵥ c), hx, form_mulVec, hP, Jpq_mulVec_of _ hy]
  rw [key]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [mul_self_nonneg ((Y *ᵥ c) i).re, mul_self_nonneg ((Y *ᵥ c) i).im]

end PI.UnitaryGroupMassFormula.FlagGramNonneg
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.NatAddZeroFinOne
section
noncomputable section

open Matrix PI.FlagGramNonneg

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem det_succ_schur {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h : IsUnit (Z.submatrix Fin.castSucc Fin.castSucc).det) :
    Z.det = (Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z (Fin.last r) (Fin.last r) - (fun b => Z (Fin.last r) (Fin.castSucc b)) ⬝ᵥ
        ((Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ (fun a => Z (Fin.castSucc a) (Fin.last r)))) := by
  haveI : Invertible (Z.submatrix Fin.castSucc Fin.castSucc) := Matrix.invertibleOfIsUnitDet _ h
  have hZ : Z.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks
      (Z.submatrix Fin.castSucc Fin.castSucc) (Matrix.of fun a (_ : Fin 1) => Z (Fin.castSucc a) (Fin.last r))
      (Matrix.of fun (_ : Fin 1) b => Z (Fin.last r) (Fin.castSucc b))
      (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => Z (Fin.last r) (Fin.last r)) := by
    ext (i | i) (j | j)
    · rfl
    · rw [Fin.fin_one_eq_zero j]
      rfl
    · rw [Fin.fin_one_eq_zero i]
      rfl
    · rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      rfl
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv Z, hZ, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv, Matrix.det_unique (n := Fin 1)]
  congr 1
  rw [Matrix.sub_apply, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] <;> rfl

theorem leadMinorE_succ {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    leadMinorE Z (r + 1) = Z.det := by
  unfold leadMinorE
  rw [dite_eq_left le_rfl]
  rfl

theorem leadMinorE_self {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    leadMinorE Z r = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadMinorE
  rw [dite_eq_left (Nat.le_succ r)]
  rfl

end PI.UnitaryGroupMassFormula.FlagGramNonneg
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.SumMulCommMulVec
section
noncomputable section

open Matrix PI.FlagGramNonneg

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

section Vec

variable {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]

def amat (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) : Matrix (Fin r) (Fin r) E :=
  fun a b => hT (e a) (e' b)

def uvec (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e : Fin r → V) (z' : V) : Fin r → E :=
  fun a => hT (e a) z'

def vvec (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (z : V) (e' : Fin r → V) : Fin r → E :=
  fun b => hT z (e' b)

def sval (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z z' : V) : E :=
  hT z z' - vvec hT z e' ⬝ᵥ ((amat hT e e')⁻¹ *ᵥ uvec hT e z')

def zt (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z : V) : V :=
  z - ∑ a, star ((vvec hT z e' ᵥ* (amat hT e e')⁻¹) a) • e a

def zt' (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z' : V) : V :=
  z' - ∑ b, ((amat hT e e')⁻¹ *ᵥ uvec hT e z') b • e' b

def yv (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (a : Fin r) : V :=
  e a - ∑ b, (amat hT e e')⁻¹ b a • e' b

theorem sum_mul_comm_mulVec {n : Type} [Fintype n] (A : Matrix n n E) (w : n → E) (c : n) :
    ∑ b, w b * A c b = (A *ᵥ w) c := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem sum_mul_vecMul {n : Type} [Fintype n] (A : Matrix n n E) (w : n → E) (c : n) :
    ∑ a, w a * A a c = (w ᵥ* A) c := by
  simp only [Matrix.vecMul, dotProduct]

theorem herm {hT : V →ₗ⋆[E] V →ₗ[E] E} (hS : hT.IsSymm) (x y : V) : hT x y = star (hT y x) := by
  first
    | exact (hS.eq y x).symm
    | exact (hS y x).symm

theorem left_sub_sum (hT : V →ₗ⋆[E] V →ₗ[E] E) {ι : Type} [Fintype ι] (z : V) (c : ι → E)
    (f : ι → V) (x : V) :
    hT (z - ∑ a, c a • f a) x = hT z x - ∑ a, star (c a) * hT (f a) x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]

theorem right_sub_sum (hT : V →ₗ⋆[E] V →ₗ[E] E) {ι : Type} [Fintype ι] (z : V) (c : ι → E)
    (f : ι → V) (x : V) :
    hT x (z - ∑ a, c a • f a) = hT x z - ∑ a, c a * hT x (f a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_smul, smul_eq_mul]

variable (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z z' : V)

theorem e_zt' (hA : IsUnit (amat hT e e').det) (c : Fin r) : hT (e c) (zt' hT e e' z') = 0 := by
  unfold zt'
  rw [right_sub_sum]
  have h : ∑ b, ((amat hT e e')⁻¹ *ᵥ uvec hT e z') b * hT (e c) (e' b) =
      (amat hT e e' *ᵥ ((amat hT e e')⁻¹ *ᵥ uvec hT e z')) c :=
    sum_mul_comm_mulVec (amat hT e e') _ c
  rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec]
  simp [uvec]

theorem zt_e' (hA : IsUnit (amat hT e e').det) (c : Fin r) : hT (zt hT e e' z) (e' c) = 0 := by
  unfold zt
  rw [left_sub_sum]
  simp only [star_star]
  have h : ∑ a, (vvec hT z e' ᵥ* (amat hT e e')⁻¹) a * hT (e a) (e' c) =
      ((vvec hT z e' ᵥ* (amat hT e e')⁻¹) ᵥ* amat hT e e') c :=
    sum_mul_vecMul (amat hT e e') _ c
  rw [h, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  simp [vvec]

theorem e_zt (he : ∀ a b, hT (e a) (e b) = 0) (hez : ∀ a, hT (e a) z = 0) (c : Fin r) :
    hT (e c) (zt hT e e' z) = 0 := by
  unfold zt
  rw [right_sub_sum, hez]
  simp [he]

theorem e'_zt' (he' : ∀ a b, hT (e' a) (e' b) = 0) (hez' : ∀ a, hT (e' a) z' = 0) (c : Fin r) :
    hT (e' c) (zt' hT e e' z') = 0 := by
  unfold zt'
  rw [right_sub_sum, hez']
  simp [he']

theorem zt_zt (hS : hT.IsSymm) (he : ∀ a b, hT (e a) (e b) = 0) (hez : ∀ a, hT (e a) z = 0) :
    hT (zt hT e e' z) (zt hT e e' z) = hT z z := by
  nth_rw 1 [zt]
  rw [left_sub_sum]
  simp only [e_zt hT e e' z he hez, mul_zero, Finset.sum_const_zero, sub_zero]
  have hze : ∀ a, hT z (e a) = 0 := fun a => by rw [herm hS, hez, star_zero]
  unfold zt
  rw [right_sub_sum]
  simp [hze]

theorem zt'_zt' (hS : hT.IsSymm) (he' : ∀ a b, hT (e' a) (e' b) = 0)
    (hez' : ∀ a, hT (e' a) z' = 0) :
    hT (zt' hT e e' z') (zt' hT e e' z') = hT z' z' := by
  nth_rw 1 [zt']
  rw [left_sub_sum]
  simp only [e'_zt' hT e e' z' he' hez', mul_zero, Finset.sum_const_zero, sub_zero]
  have hze : ∀ a, hT z' (e' a) = 0 := fun a => by rw [herm hS, hez', star_zero]
  unfold zt'
  rw [right_sub_sum]
  simp [hze]

theorem zt_zt' (hA : IsUnit (amat hT e e').det) :
    hT (zt hT e e' z) (zt' hT e e' z') = sval hT e e' z z' := by
  rw [zt', right_sub_sum]
  simp only [zt_e' hT e e' z hA, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [zt, left_sub_sum]
  simp only [star_star]
  unfold sval
  rw [Matrix.dotProduct_mulVec]
  simp [dotProduct, uvec]

theorem yv_yv (hS : hT.IsSymm) (hA : IsUnit (amat hT e e').det) (he : ∀ a b, hT (e a) (e b) = 0)
    (he' : ∀ a b, hT (e' a) (e' b) = 0) (a c : Fin r) :
    hT (yv hT e e' a) (yv hT e e' c) = if a = c then -2 else 0 := by
  have hAA : amat hT e e' * (amat hT e e')⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA
  have key : ∀ a c, ∑ d, hT (e a) (e' d) * (amat hT e e')⁻¹ d c = if a = c then 1 else 0 := by
    intro a c
    have h := congrFun (congrFun hAA a) c
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have h1 : ∑ d, (amat hT e e')⁻¹ d c * hT (e a) (e' d) = if a = c then 1 else 0 := by
    rw [← key a c]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  have h2 : ∑ b, star ((amat hT e e')⁻¹ b a) * hT (e' b) (e c) = if a = c then 1 else 0 := by
    have h3 : ∑ b, star ((amat hT e e')⁻¹ b a) * hT (e' b) (e c) =
        star (∑ b, hT (e c) (e' b) * (amat hT e e')⁻¹ b a) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [star_mul', herm hS (e' b) (e c), mul_comm]
    rw [h3, key c a]
    rcases eq_or_ne a c with h | h
    · subst h
      simp
    · simp [h, Ne.symm h]
  unfold yv
  simp only [left_sub_sum, right_sub_sum, he, he', mul_zero, Finset.sum_const_zero, sub_zero, zero_sub]
  rw [h1, h2]
  split_ifs <;> ring

theorem yv_zt (hS : hT.IsSymm) (hA : IsUnit (amat hT e e').det) (he : ∀ a b, hT (e a) (e b) = 0)
    (hez : ∀ a, hT (e a) z = 0) (a : Fin r) : hT (yv hT e e' a) (zt hT e e' z) = 0 := by
  unfold yv
  rw [left_sub_sum, e_zt hT e e' z he hez]
  have h : ∀ b, hT (e' b) (zt hT e e' z) = 0 := fun b => by
    rw [herm hS, zt_e' hT e e' z hA, star_zero]
  simp [h]

theorem yv_zt' (hA : IsUnit (amat hT e e').det) (he' : ∀ a b, hT (e' a) (e' b) = 0)
    (hez' : ∀ a, hT (e' a) z' = 0) (a : Fin r) : hT (yv hT e e' a) (zt' hT e e' z') = 0 := by
  unfold yv
  rw [left_sub_sum, e_zt' hT e e' z' hA]
  simp [e'_zt' hT e e' z' he' hez']

end Vec

end PI.UnitaryGroupMassFormula.FlagGramNonneg
end
end

