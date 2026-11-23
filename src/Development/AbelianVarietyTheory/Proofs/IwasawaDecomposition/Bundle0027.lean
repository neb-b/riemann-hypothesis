module

public import Mathlib
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricBlockTraceInverseEqTwoMul
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.FockDetDer

theorem trace_fromBlocks_diag {m n : Type} [Fintype m] [Fintype n]
    (X : Matrix m m ℂ) (Y : Matrix n n ℂ) :
    (fromBlocks X 0 0 Y).trace = X.trace + Y.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem symmetric_block_trace_inverse_eq_two_mul {P Q : ℕ} (C : Matrix (Fin Q) (Fin P) ℂ) (B : Matrix (Fin P) (Fin Q) ℂ) (c : ℂ)
    (h : IsUnit (1 - c • (C * B)).det) :
    IsUnit (1 - c • ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))).det ∧
    ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (1 - c • ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))⁻¹).trace =
      2 * ((1 - c • (C * B))⁻¹ * (C * B)).trace := by
  have hTS : (fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      fromBlocks (B * C) 0 0 (C * B)ᵀ := by
    rw [fromBlocks_multiply]; simp
  have h1 : (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) - c • fromBlocks (B * C) 0 0 (C * B)ᵀ =
      fromBlocks (1 - c • (B * C)) 0 0 (1 - c • (C * B))ᵀ := by
    rw [← fromBlocks_one]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply, eq_comm]
  have hd : (1 - c • (B * C)).det = (1 - c • (C * B)).det := by
    rw [← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul]
  have h' : IsUnit (1 - c • (B * C)).det := hd ▸ h
  rw [hTS, h1]
  refine ⟨?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, det_transpose]
    exact h'.mul h
  · have hinv : (fromBlocks (1 - c • (B * C)) 0 0 (1 - c • (C * B))ᵀ)⁻¹ =
        fromBlocks (1 - c • (B * C))⁻¹ 0 0 ((1 - c • (C * B))⁻¹)ᵀ := by
      apply Matrix.inv_eq_left_inv
      rw [fromBlocks_multiply, ← transpose_mul, nonsing_inv_mul _ h', mul_nonsing_inv _ h]
      simp
    have hMB : (1 - c • (B * C))⁻¹ * B = B * (1 - c • (C * B))⁻¹ := by
      have e : B * (1 - c • (C * B)) = (1 - c • (B * C)) * B := by
        simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      calc (1 - c • (B * C))⁻¹ * B
          = (1 - c • (B * C))⁻¹ * B * ((1 - c • (C * B)) * (1 - c • (C * B))⁻¹) := by
            rw [mul_nonsing_inv _ h, Matrix.mul_one]
        _ = (1 - c • (B * C))⁻¹ * (B * (1 - c • (C * B))) * (1 - c • (C * B))⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = B * (1 - c • (C * B))⁻¹ := by
            rw [e, ← Matrix.mul_assoc, nonsing_inv_mul _ h', Matrix.one_mul]
    rw [hinv, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [trace_fromBlocks_diag, ← transpose_mul, trace_transpose, two_mul]
    congr 1
    rw [trace_mul_comm (B * C), ← Matrix.mul_assoc, hMB, Matrix.mul_assoc, trace_mul_comm B,
      Matrix.mul_assoc]

theorem hasDerivAt_det_one_sub_sq :
    ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ) (t : ℝ),
      IsUnit (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det →
      let S : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 (Matrix.transpose Aᴴ) Aᴴ 0
      let T : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 B Bᵀ 0
      IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det ∧
        HasDerivAt (fun s : ℝ => (1 - ((s : ℂ) ^ 2) • (Aᴴ * B)).det)
          (-((t : ℂ) * (T * S * (1 - ((t : ℂ) ^ 2) • (T * S))⁻¹).trace) *
            (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det) t := by
  intro P Q A B t h S T
  obtain ⟨h1, h2⟩ := symmetric_block_trace_inverse_eq_two_mul Aᴴ B ((t : ℂ) ^ 2) h
  refine ⟨h1, ?_⟩
  have hsq : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (t : ℂ)) t := by
    have := (hasDerivAt_pow 2 (t : ℂ)).comp_ofReal
    simpa using this
  have hd := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun s : ℝ => 1 - ((s : ℂ) ^ 2) • (Aᴴ * B))
    (-((2 * (t : ℂ)) • (Aᴴ * B))) t (fun i j => by
      have := (hsq.mul_const ((Aᴴ * B) i j)).const_sub ((1 : Matrix (Fin Q) (Fin Q) ℂ) i j)
      simpa using this)
  refine hd.congr_deriv ?_
  have hne := h.ne_zero
  have hadj : (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).adjugate =
      (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det • (1 - ((t : ℂ) ^ 2) • (Aᴴ * B))⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ hne, one_smul]
  simp only [S, T]
  rw [h2, hadj, Matrix.smul_mul, Matrix.mul_neg, Matrix.mul_smul, trace_smul, trace_neg, trace_smul]
  simp only [smul_eq_mul]
  ring

end GlobalTheory.FockDetDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

variable {ι : Type} {N n : ℕ}

def subst2 (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin N × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin n) ℂ :=
  aeval fun p => ∑ k, ∑ l, C (h k p.1 * g l p.2) * X (k, l)

def substF (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin N × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin N × Fin n) ℂ :=
  aeval fun p => ∑ k, ∑ l, C (h p.1 k p.2.1 * g p.1 l p.2.2) * X (p.1, k, l)

theorem subst2_X (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (p : Fin N × Fin n) :
    subst2 h g (X p) = ∑ k, ∑ l, C (h k p.1 * g l p.2) * X (k, l) := aeval_X _ _

theorem substF_X (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    substF h g (X p) = ∑ k, ∑ l, C (h p.1 k p.2.1 * g p.1 l p.2.2) * X (p.1, k, l) := aeval_X _ _

theorem totalDegree_aeval_le {κ : Type} (f : κ → MvPolynomial κ ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (P : MvPolynomial κ ℂ) : (aeval f P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.AevalTotalDegreeLinear.main
  | exact _root_.GlobalTheory.AevalTotalDegreeLinear.main
  | (apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalTotalDegreeLinear.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalTotalDegreeLinear.main ..)

theorem totalDegree_substF_le (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) : (substF h g P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le _ (fun _ => totalDegree_finsetSum_le fun _ _ => totalDegree_finsetSum_le fun _ _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])) P

theorem subst2_mul (h h' : Matrix (Fin N) (Fin N) ℂ) (g g' : Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 h g (subst2 h' g' P) = subst2 (h * h') (g * g') P := by
  have key : (subst2 h g).comp (subst2 h' g') = subst2 (h * h') (g * g') := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, subst2_X, subst2_X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, subst2_X, algHom_C, algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun _ => Finset.univ) (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  exact congrArg (fun f => f P) key

theorem subst2_one (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 1 1 P = P := by
  have key : subst2 (1 : Matrix (Fin N) (Fin N) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) = AlgHom.id ℂ _ := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [key]; rfl

end GlobalTheory.CompactHowe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowGrassmannBlockCurvatureSupertraceZero
section
noncomputable section

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel.SuperTrace

variable {n : ℕ}

def Sg (m : ℕ) (z : Big n) : Prop :=
  ∀ a : Fin n, ((1 : Ext n) ⊗ₜ vec n a) * z = (-1) ^ m * (z * ((1 : Ext n) ⊗ₜ vec n a))

theorem sg_zero (m : ℕ) : Sg m (0 : Big n) := by intro a; simp

theorem sg_add {m : ℕ} {z w : Big n} (hz : Sg m z) (hw : Sg m w) : Sg m (z + w) := by
  intro a; rw [mul_add, hz a, hw a, add_mul, mul_add]

theorem sg_sum {ι : Type*} (s : Finset ι) (m : ℕ) (f : ι → Big n) (h : ∀ i ∈ s, Sg m (f i)) :
    Sg m (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using sg_zero m
  | cons x s hx ih =>
    rw [Finset.sum_cons]
    exact sg_add (h x (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem sg_mul {m l : ℕ} {z w : Big n} (hz : Sg m z) (hw : Sg l w) : Sg (m + l) (z * w) := by
  intro a
  have hc : Commute ((-1 : Big n) ^ l) z := (Commute.neg_one_left z).pow_left l
  rw [← mul_assoc, hz a, mul_assoc, mul_assoc, hw a, pow_add, ← mul_assoc z, ← hc.eq]
  simp only [mul_assoc]

theorem sg_one : Sg 0 (1 : Big n) := by intro a; simp

theorem sg_left (x : Ext n) : Sg 0 (x ⊗ₜ (1 : Ext n)) := by
  intro a; simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem sg_right (b : Fin n) : Sg 1 ((1 : Ext n) ⊗ₜ vec n b) := by
  intro a
  simp [Algebra.TensorProduct.tmul_mul_tmul, vec_mul_vec_comm n a b, TensorProduct.tmul_neg]

def MSg {r s : Type*} (m : ℕ) (M : Matrix r s (Big n)) : Prop := ∀ i j, Sg m (M i j)

theorem msg_mul {r s t : Type*} [Fintype s] {m l : ℕ} {M : Matrix r s (Big n)}
    {N : Matrix s t (Big n)} (hM : MSg m M) (hN : MSg l N) : MSg (m + l) (M * N) := by
  intro i j; rw [Matrix.mul_apply]; exact sg_sum _ _ _ fun k _ => sg_mul (hM i k) (hN k j)

theorem msg_one {r : Type*} [Fintype r] [DecidableEq r] : MSg 0 (1 : Matrix r r (Big n)) := by
  intro i j; rw [Matrix.one_apply]; split_ifs
  · exact sg_one
  · exact sg_zero 0

theorem msg_pow {r : Type*} [Fintype r] [DecidableEq r] {M : Matrix r r (Big n)} (hM : MSg 1 M)
    (j : ℕ) : MSg j (M ^ j) := by
  induction j with
  | zero => simpa using (msg_one : MSg 0 (1 : Matrix r r (Big n)))
  | succ j ih => rw [pow_succ]; exact msg_mul ih hM

theorem pow_mul_left {p q : ℕ} {R : Type*} [Semiring R] (A : Matrix (Fin p) (Fin q) R)
    (B : Matrix (Fin q) (Fin p) R) (m : ℕ) : (A * B) ^ m * A = A * (B * A) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc A B A]

theorem trace_swap {p q : ℕ} (A : Matrix (Fin p) (Fin q) (Big n)) (B : Matrix (Fin q) (Fin p) (Big n))
    (hA : MSg 0 A) (hB : ∀ b i, ∃ a, B b i = (1 : Ext n) ⊗ₜ vec n a) (m : ℕ) :
    ((B * A) ^ (m + 1)).trace = (-1) ^ m * ((A * B) ^ (m + 1)).trace := by
  have hB1 : MSg 1 B := by
    intro b i; obtain ⟨a, ha⟩ := hB b i; rw [ha]; exact sg_right a
  have hY : MSg m (A * (B * A) ^ m) := by
    simpa using msg_mul hA (msg_pow (by simpa using msg_mul hB1 hA) m)
  have h1 : (B * A) ^ (m + 1) = B * (A * (B * A) ^ m) := by
    rw [pow_succ', Matrix.mul_assoc]
  have h2 : (A * B) ^ (m + 1) = (A * (B * A) ^ m) * B := by
    rw [pow_succ, ← Matrix.mul_assoc, pow_mul_left]
  generalize A * (B * A) ^ m = Y at hY h1 h2
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  obtain ⟨a, ha⟩ := hB b i
  rw [ha, hY i b a]

theorem val_trace {r : Type*} [Fintype r] (M : Matrix r r (EvenPart n)) :
    ((EvenPart n).val M.trace) = (M.map (EvenPart n).val).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, map_sum]

theorem val_pow {r : Type*} [Fintype r] [DecidableEq r] (M : Matrix r r (EvenPart n)) (k : ℕ) :
    (M ^ k).map (EvenPart n).val = (M.map (EvenPart n).val) ^ k :=
  map_pow ((EvenPart n).val.toRingHom.mapMatrix) M k

end GlobalTheory.GrassModel.SuperTrace

open GlobalTheory.GrassModel GlobalTheory.GrassModel.SuperTrace in
theorem GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar {n p q : ℕ}
    (e : Fin p × Fin q → Fin n) (k : ℕ) (hk : 1 ≤ k) :
    ((blockPoly e).map (toEven n) ^ k).trace + ((-blockPolyBar e).map (toEven n) ^ k).trace = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set A : Matrix (Fin p) (Fin q) (Big n) := Matrix.of fun i b => vec n (e (i, b)) ⊗ₜ (1 : Ext n)
  set B : Matrix (Fin q) (Fin p) (Big n) := Matrix.of fun b j => (1 : Ext n) ⊗ₜ vec n (e (j, b))
  have hA : MSg 0 A := fun i b => sg_left _
  have hB : ∀ b i, ∃ a, B b i = (1 : Ext n) ⊗ₜ vec n a := fun b i => ⟨e (i, b), rfl⟩
  have hL : ((blockPoly e).map (toEven n)).map (EvenPart n).val = A * B := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [A, B, blockPoly, toEven, gen, Matrix.mul_apply, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
  have hD : (Matrix.transpose ((blockPolyBar e).map (toEven n))).map (EvenPart n).val = B * A := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [A, B, blockPolyBar, toEven, gen, Matrix.mul_apply, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
  have hneg : (-blockPolyBar e).map (toEven n) = -((blockPolyBar e).map (toEven n)) := by
    ext i j; simp
  apply Subtype.val_injective
  show (EvenPart n).val (_ + _) = (EvenPart n).val 0
  rw [map_add (f := _), map_zero, hneg, ← Matrix.trace_transpose (( -_ ) ^ _), Matrix.transpose_pow,
    Matrix.transpose_neg, val_trace, val_trace, val_pow, val_pow, hL]
  rw [show (-Matrix.transpose ((blockPolyBar e).map (toEven n))).map (EvenPart n).val = -(B * A) by
    rw [← hD]; ext i j; simp]
  rcases Nat.even_or_odd (m + 1) with h | h
  · rw [h.neg_pow, trace_swap A B hA hB m]
    have : Odd m := by rcases h with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
    rw [this.neg_one_pow]; simp
  · rw [h.neg_pow, Matrix.trace_neg, trace_swap A B hA hB m]
    have : Even m := by rcases h with ⟨t, ht⟩; exact ⟨t, by omega⟩
    rw [this.neg_one_pow]; simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VLeOne
section
namespace GlobalTheory.CommonReading

open scoped NNReal

section
variable {l : ℕ} [Fact l.Prime] {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]

theorem exists_extend [Module.Finite A B] (hi : Function.Injective (algebraMap A B)) (κ : A →+* ℂ_[l])
    (hκ : Function.Injective κ) :
    ∃ ι : FractionRing B →+* ℂ_[l], ∀ y, ι (algebraMap B (FractionRing B) (algebraMap A B y)) = κ y := by
  let _ : Algebra A ℂ_[l] := κ.toAlgebra
  have hAF : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hi
  have : Module.IsTorsionFree A ℂ_[l] := Module.isTorsionFree_iff_algebraMap_injective.mpr hκ
  have : Module.IsTorsionFree A (FractionRing B) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hAF
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hi
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  have : Algebra.IsAlgebraic A (FractionRing B) :=
    (IsFractionRing.isAlgebraic_iff' A B (FractionRing B)).1 inferInstance
  let φ : FractionRing B →ₐ[A] ℂ_[l] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom, fun y => ?_⟩
  rw [← IsScalarTower.algebraMap_apply A B (FractionRing B) y]
  exact φ.commutes y

theorem v_le_one [Module.Finite A B] (j : B →+* ℂ_[l]) (hκ : ∀ y, Valued.v (j (algebraMap A B y)) ≤ (1 : ℝ≥0)) (b : B) :
    Valued.v (j b) ≤ (1 : ℝ≥0) := by
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := A) b
  have hroot : p.eval₂ (j.comp (algebraMap A B)) (j b) = 0 := by
    rw [← Polynomial.hom_eval₂, hp, map_zero]
  by_contra hle
  have hlt := not_le.mp hle
  rw [hpm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hroot
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hroot
  have hxn := eq_neg_of_add_eq_zero_left hroot
  have hn : p.natDegree ≠ 0 := by
    intro h0
    rw [h0] at hxn
    simp at hxn
  have h1 : Valued.v (j b ^ p.natDegree) ≤ Valued.v (j b) ^ (p.natDegree - 1) := by
    rw [hxn, Valuation.map_neg]
    apply Valuation.map_sum_le
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc Valued.v ((j.comp (algebraMap A B)) (p.coeff i)) * Valued.v (j b) ^ i
        ≤ 1 * Valued.v (j b) ^ (p.natDegree - 1) :=
          mul_le_mul' (hκ _) (pow_le_pow_right₀ hlt.le (by omega))
      _ = _ := one_mul _
  rw [map_pow] at h1
  have h2 : Valued.v (j b) ^ (p.natDegree - 1) < Valued.v (j b) ^ p.natDegree :=
    pow_lt_pow_right₀ hlt (by omega)
  exact absurd h1 (not_le.mpr h2)

theorem mem_range_iff [IsDiscreteValuationRing B] (ι : FractionRing B →+* ℂ_[l])
    (h : ∀ b, Valued.v (ι (algebraMap B (FractionRing B) b)) ≤ (1 : ℝ≥0)) (x : FractionRing B) :
    x ∈ (algebraMap B (FractionRing B)).range ↔ Valued.v (ι x) ≤ (1 : ℝ≥0) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact h b
  · intro hx
    by_contra hxn
    set φ : B →+* ℂ_[l] := ι.comp (algebraMap B (FractionRing B)) with hφ
    have hφ1 : ∀ b, Valued.v (φ b) ≤ (1 : ℝ≥0) := fun b => h b
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxn (RingHom.mem_range.mpr ⟨0, map_zero _⟩)
    obtain ⟨b, hb⟩ : ∃ b, algebraMap B (FractionRing B) b = x⁻¹ := by
      rcases ValuationRing.isInteger_or_isInteger B x with h1 | h1
      · exact absurd (RingHom.mem_range.mpr (RingHom.mem_rangeS.mp h1)) hxn
      · exact RingHom.mem_rangeS.mp h1
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      exact hx0 (inv_eq_zero.mp hb.symm)
    have hbu : ¬ IsUnit b := by
      rintro ⟨u, rfl⟩
      apply hxn
      refine RingHom.mem_range.mpr ⟨(↑u⁻¹ : B), ?_⟩
      rw [map_units_inv, hb, inv_inv]
    have hl1 : Valued.v ((l : ℕ) : ℂ_[l]) < 1 := by
      rw [PadicComplex.valuation_p, one_div]
      have : (1 : ℝ≥0) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      exact inv_lt_one_of_one_lt₀ this
    have hl0 : ((l : ℕ) : B) ≠ 0 := by
      intro h0
      have h2 : φ ((l : ℕ) : B) = 0 := by rw [h0, map_zero]
      rw [map_natCast] at h2
      exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h2
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hbu (hk.symm.isUnit (by simp))
    have hdvd : ((l : ℕ) : B) ∣ b ^ n := by
      have h2 : ϖ ^ n ∣ ϖ ^ (k * n) :=
        pow_dvd_pow ϖ (by have := Nat.pos_of_ne_zero hk0; nlinarith)
      have h3 : ϖ ^ (k * n) ∣ b ^ n := by
        rw [pow_mul]
        exact (hk.pow_pow (n := n)).symm.dvd
      exact hn.dvd.trans (h2.trans h3)
    obtain ⟨c, hc⟩ := hdvd
    have hvb : Valued.v (φ b) < 1 := by
      by_contra hlt'
      have hge := not_lt.mp hlt'
      have h1 : 1 ≤ Valued.v (φ b) ^ n := one_le_pow₀ hge
      rw [← map_pow Valued.v, ← map_pow φ, hc, map_mul, map_mul, map_natCast] at h1
      exact absurd h1 (not_le.mpr (mul_lt_one_of_nonneg_of_lt_one_left (by positivity) hl1 (hφ1 c)))
    have h1 : Valued.v (ι x) * Valued.v (φ b) = 1 := by
      rw [← map_mul]
      have h3 : ι x * φ b = 1 := by
        show ι x * ι (algebraMap B (FractionRing B) b) = 1
        rw [← map_mul, hb, mul_inv_cancel₀ hx0, map_one]
      rw [h3, map_one]
    exact absurd h1 (ne_of_lt (mul_lt_one_of_nonneg_of_lt_one_right hx (by positivity) hvb))

end

theorem exists_factor {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] (g : L →+* ℂ_[l]) :
    ∃ e : L →+* PadicAlgCl l, ∀ x, algebraMap (PadicAlgCl l) ℂ_[l] (e x) = g x := by
  have hmem : ∀ x : L, g x ∈ (algebraMap (PadicAlgCl l) ℂ_[l]).range := by
    intro x
    obtain ⟨f, hf0, hf⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x
    have hg : (f.map (algebraMap ℚ ℂ_[l])).eval (g x) = 0 := by
      have h1 : g (Polynomial.eval₂ (algebraMap ℚ L) x f) = 0 := by
        rw [← Polynomial.aeval_def, hf, map_zero]
      rw [Polynomial.hom_eval₂] at h1
      rw [Polynomial.eval_map]
      have e : g.comp (algebraMap ℚ L) = algebraMap ℚ ℂ_[l] := RingHom.ext_rat _ _
      rwa [e] at h1
    have hsplit : (f.map (algebraMap ℚ (PadicAlgCl l))).Splits := IsAlgClosed.splits _
    have hP0 : f.map (algebraMap ℚ (PadicAlgCl l)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ (PadicAlgCl l)).injective).mpr hf0
    have hmap : f.map (algebraMap ℚ ℂ_[l]) =
        (f.map (algebraMap ℚ (PadicAlgCl l))).map (algebraMap (PadicAlgCl l) ℂ_[l]) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext_rat _ _
    have hroot : g x ∈ ((f.map (algebraMap ℚ (PadicAlgCl l))).map (algebraMap (PadicAlgCl l) ℂ_[l])).roots := by
      rw [Polynomial.mem_roots ((Polynomial.map_ne_zero_iff (algebraMap (PadicAlgCl l) ℂ_[l]).injective).mpr hP0)]
      show Polynomial.eval _ _ = 0
      rw [← hmap]
      exact hg
    rw [hsplit.roots_map_of_injective (algebraMap (PadicAlgCl l) ℂ_[l]).injective, Multiset.mem_map] at hroot
    obtain ⟨β, -, hβ⟩ := hroot
    exact RingHom.mem_range.mpr ⟨β, hβ⟩
  have hr : Function.Bijective (algebraMap (PadicAlgCl l) ℂ_[l]).rangeRestrict :=
    ⟨fun a b hab => (algebraMap (PadicAlgCl l) ℂ_[l]).injective (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩
  let E := RingEquiv.ofBijective _ hr
  refine ⟨E.symm.toRingHom.comp (g.codRestrict _ hmem), fun x => ?_⟩
  exact congrArg Subtype.val (E.apply_symm_apply (g.codRestrict _ hmem x))

theorem exists_common {l : ℕ} [Fact l.Prime] {A B L : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] (hi : Function.Injective (algebraMap A B))
    (κ : A →+* ℂ_[l]) (hκ : Function.Injective κ) (hv : ∀ y, Valued.v (κ y) ≤ (1 : ℝ≥0))
    [Field L] [NumberField L] (eB : L →+* FractionRing B) (e : L →+* PadicAlgCl l)
    (he : ∀ x, eB x ∈ (algebraMap B (FractionRing B)).range ↔ ‖e x‖ ≤ 1) :
    ∃ (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (ι : FractionRing B →+* ℂ_[l]),
      (∀ y, ι (algebraMap B (FractionRing B) (algebraMap A B y)) = κ y) ∧
      ∀ x, ι (eB x) = algebraMap (PadicAlgCl l) ℂ_[l] (σ (e x)) := by
  obtain ⟨ι, hι⟩ := exists_extend hi κ hκ
  have hB : ∀ b, Valued.v (ι (algebraMap B (FractionRing B) b)) ≤ (1 : ℝ≥0) := by
    intro b
    refine v_le_one (A := A) (ι.comp (algebraMap B (FractionRing B))) (fun y => ?_) b
    rw [RingHom.comp_apply, hι]
    exact hv y
  obtain ⟨e', he'⟩ := exists_factor (ι.comp eB)
  have hcond : ∀ x, ‖e x‖ ≤ 1 ↔ ‖e' x‖ ≤ 1 := by
    intro x
    rw [← he x, mem_range_iff ι hB, ← RingHom.comp_apply ι eB, ← he' x, ← PadicComplex.coe_eq,
      PadicComplex.valuation_extends, PadicAlgCl.valuation_def, ← NNReal.coe_le_coe, coe_nnnorm,
      NNReal.coe_one]
  obtain ⟨σ, hσ⟩ := GlobalTheory.EmbUnitBallConj.exists_conj l L e e' hcond
  refine ⟨σ, ι, hι, fun x => ?_⟩
  rw [hσ, he']
  rfl

end GlobalTheory.CommonReading
end

