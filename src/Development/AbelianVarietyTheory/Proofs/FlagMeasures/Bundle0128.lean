module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClassFunctionBernsteinZelevinskyDerivative
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

noncomputable section

namespace GlobalTheory.GLm.DerClass

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

def blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g)) (D : Mt g b) :
    Mt g (a + b) :=
  (Matrix.fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem exists_blocks (M : Mt g (a + b)) : ∃ A B C D, M = blocks A B C D := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [blocks, Matrix.fromBlocks_toBlocks]
  ext i j
  simp

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {a b : ℕ} in
theorem _root_.GlobalTheory.GLm.DerClass.blocks_mul (A A' : _root_.GlobalTheory.GLq.Mt g a)
    (B B' : Matrix (Fin a) (Fin b) (ZMod g)) (C C' : Matrix (Fin b) (Fin a) (ZMod g))
    (D D' : _root_.GlobalTheory.GLq.Mt g b) :
    _root_.GlobalTheory.GLm.DerClass.blocks A B C D * _root_.GlobalTheory.GLm.DerClass.blocks A' B' C' D' =
      _root_.GlobalTheory.GLm.DerClass.blocks (A * A' + B * C') (A * B' + B * D') (C * A' + D * C')
        (C * B' + D * D') := by
  unfold _root_.GlobalTheory.GLm.DerClass.blocks
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {a b : ℕ} in
theorem _root_.GlobalTheory.GLm.DerClass.blocks_one :
    _root_.GlobalTheory.GLm.DerClass.blocks (1 : _root_.GlobalTheory.GLq.Mt g a) 0 0 (1 : _root_.GlobalTheory.GLq.Mt g b) = 1 := by
  unfold _root_.GlobalTheory.GLm.DerClass.blocks
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem tl_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : tl a (blocks A B C D) = A := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [tl, entN, dite_eq_left ⟨by omega, by omega⟩]
  change blocks A B C D (Fin.castAdd b i) (Fin.castAdd b j) = _
  simp [blocks]

theorem br_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : br a b (blocks A B C D) = D := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [br, entN, dite_eq_left ⟨by omega, by omega⟩]
  change blocks A B C D (Fin.natAdd a i) (Fin.natAdd a j) = _
  simp [blocks]

theorem inPar_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : InPar a (blocks A B C D) ↔ C = 0 := by
  constructor
  · intro h
    ext i j
    have := h (Fin.natAdd a i) (Fin.castAdd b j) (by simp) (by simp)
    simpa [blocks] using this
  · rintro rfl i j hj hi
    induction i using Fin.addCases with
    | left i => have := i.2; simp at hi; omega
    | right i =>
      induction j using Fin.addCases with
      | left j => simp [blocks]
      | right j => simp at hj

theorem inMir_blocks (hb : 0 < b) (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) {D : Mt g b} (hD : IsUniUp D) :
    InMir (blocks A B 0 D) := by
  intro i j hi
  rw [← blocks_one]
  induction i using Fin.addCases with
  | left i => have := i.2; simp at hi; omega
  | right i =>
    induction j using Fin.addCases with
    | left j => simp [blocks]
    | right j =>
      have hj := j.2
      simp only [Fin.val_natAdd] at hi
      simp only [blocks, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]
      by_cases h : i = j
      · rw [(hD i j).2 h, h, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne h]
        refine (hD i j).1 ?_
        have : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
        rw [Fin.lt_def]
        omega

theorem isUniUp_one : IsUniUp (1 : Mt g b) := fun i j =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => by rw [h, Matrix.one_apply_eq]⟩

def dg (b : ℕ) (y : Gn g a) : Gn g (a + b) where
  val := blocks y.val 0 0 1
  inv := blocks (y⁻¹).val 0 0 1
  val_inv := by rw [blocks_mul]; simpa using blocks_one
  inv_val := by rw [blocks_mul]; simpa using blocks_one

theorem conj_val (y : Gn g a) (x : Gn g (a + b)) {A : Mt g a} {B : Matrix (Fin a) (Fin b) (ZMod g)}
    {C : Matrix (Fin b) (Fin a) (ZMod g)} {D : Mt g b} (hx : x.val = blocks A B C D) :
    (dg b y * x * (dg b y)⁻¹).val = blocks (y.val * A * (y⁻¹).val) (y.val * B) (C * (y⁻¹).val) D := by
  change blocks y.val 0 0 1 * x.val * blocks (y⁻¹).val 0 0 1 = _
  rw [hx, blocks_mul, blocks_mul]
  simp

theorem res_conj (hb : 0 < b) {F : Gn g (a + b) → ℂ} (hF : IsMirClass F) (h y : Gn g a) (u : Gn g b)
    (hu : IsUniUp (u : Mt g b)) : res a b F (y * h * y⁻¹) u = res a b F h u := by
  unfold res
  congr 1
  symm
  refine Fintype.sum_equiv (MulAut.conj (dg b y)).toEquiv _ _ fun x => ?_
  obtain ⟨A, B, C, D, hx⟩ := exists_blocks x.val
  have e := conj_val y x hx
  change _ = if InPar a (dg b y * x * (dg b y)⁻¹).val ∧ tl a (dg b y * x * (dg b y)⁻¹).val = (y * h * y⁻¹).val ∧
    br a b (dg b y * x * (dg b y)⁻¹).val = u.val then F (dg b y * x * (dg b y)⁻¹) else 0
  rw [e, hx, inPar_blocks, inPar_blocks, tl_blocks, tl_blocks, br_blocks, br_blocks]
  have h1 : C * (y⁻¹).val = 0 ↔ C = 0 := by
    constructor
    · intro hc
      have := congrArg (· * y.val) hc
      simpa [Matrix.mul_assoc] using this
    · rintro rfl
      simp
  have h2 : y.val * A * (y⁻¹).val = (y * h * y⁻¹).val ↔ A = h.val := by
    rw [Units.val_mul, Units.val_mul, Units.mul_left_inj, Units.mul_right_inj]
  simp only [h1, h2]
  split_ifs with hc
  · obtain ⟨rfl, -, rfl⟩ := hc
    refine (hF _ _ ?_ ?_).symm
    · exact inMir_blocks hb _ _ isUniUp_one
    · rw [hx]
      exact inMir_blocks hb _ _ hu
  · rfl

theorem wh_congr (ψ : AddChar (ZMod g) ℂ) {α β : Gn g b → ℂ} (h : ∀ u : Gn g b, IsUniUp (u : Mt g b) → α u = β u) :
    wh ψ α = wh ψ β := by
  unfold wh tr
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : IsUniUp (u : Mt g b)
  · rw [h u hu]
  · have : (eU g b ψ).coeff u = 0 := by
      simp only [eU, eDat, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
        Finsupp.smul_apply, Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_zero, smul_zero]
      intro v hv
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hu (Finset.mem_filter.1 hv).2
    rw [this, zero_mul, zero_mul]

theorem isClass_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ), i < n →
    IsMirClass F → IsClass (der ψ i F) := by
  intro g _ ψ i n F hin hF h y
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hin.le
  unfold der
  rw [Nat.add_sub_cancel_left]
  exact wh_congr ψ fun u hu => res_conj (by omega) hF h y u hu

end GlobalTheory.GLm.DerClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsMirabolicConjInvariantTwistedTailMeanFun
section
noncomputable section

namespace GlobalTheory.GLm.TailClass

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime] {m k : ℕ}

def dM (k : ℕ) (A : Mt g m) : Mt g (m + k) :=
  (Matrix.fromBlocks A 0 0 (1 : Mt g k)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem dM_mul (A B : Mt g m) : dM k A * dM k B = dM k (A * B) := by
  simp [dM, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem dM_one : dM k (1 : Mt g m) = 1 := by
  simp [dM, Matrix.fromBlocks_one]

def dG (k : ℕ) (p : Gn g m) : Gn g (m + k) :=
  ⟨dM k p.val, dM k p.inv, by rw [dM_mul, p.val_inv, dM_one], by rw [dM_mul, p.inv_val, dM_one]⟩

theorem conj_val (p : Gn g m) (x : Gn g (m + k)) :
    ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) =
      dM k (p : Mt g m) * (x : Mt g (m + k)) * dM k ((p⁻¹ : Gn g m) : Mt g m) := rfl

theorem tl_apply (X : Mt g (m + k)) (i j : Fin m) : tl m X i j = X (Fin.castAdd k i) (Fin.castAdd k j) := by
  have h : (i : ℕ) < m + k ∧ (j : ℕ) < m + k := ⟨by omega, by omega⟩
  rw [tl, entN, dif_pos h]; rfl

theorem upperLeftBlock_blockDiagExtendByIdentity_conj (A B : Mt g m) (X : Mt g (m + k)) : tl m (dM k A * X * dM k B) = A * tl m X * B := by
  ext i j
  simp [tl_apply, dM, Matrix.mul_apply, Fin.sum_univ_add]

theorem blockDiagExtendByIdentity_conj_upperRight_apply (A B : Mt g m) (X : Mt g (m + k)) (i : Fin m) (j : Fin k) :
    (dM k A * X * dM k B) (Fin.castAdd k i) (Fin.natAdd m j) =
      ∑ l, A i l * X (Fin.castAdd k l) (Fin.natAdd m j) := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem blockDiagExtendByIdentity_conj_lowerLeft_apply (A B : Mt g m) (X : Mt g (m + k)) (i : Fin k) (j : Fin m) :
    (dM k A * X * dM k B) (Fin.natAdd m i) (Fin.castAdd k j) =
      ∑ l, X (Fin.natAdd m i) (Fin.castAdd k l) * B l j := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem blockDiagExtendByIdentity_conj_lowerRight_apply (A B : Mt g m) (X : Mt g (m + k)) (i j : Fin k) :
    (dM k A * X * dM k B) (Fin.natAdd m i) (Fin.natAdd m j) = X (Fin.natAdd m i) (Fin.natAdd m j) := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem entN_blockDiagExtendByIdentity_conj_lowerRight (A B : Mt g m) (X : Mt g (m + k)) (i j : ℕ) (hi : m ≤ i) (hj : m ≤ j) :
    entN (dM k A * X * dM k B) i j = entN X i j := by
  unfold entN
  split_ifs with h
  · have e1 : (⟨i, h.1⟩ : Fin (m + k)) = Fin.natAdd m ⟨i - m, by omega⟩ := by ext; simp; omega
    have e2 : (⟨j, h.2⟩ : Fin (m + k)) = Fin.natAdd m ⟨j - m, by omega⟩ := by ext; simp; omega
    rw [e1, e2, blockDiagExtendByIdentity_conj_lowerRight_apply]
  · rfl

theorem inR_conj (A B : Mt g m) (X : Mt g (m + k)) (h : InR m X) : InR m (dM k A * X * dM k B) := by
  refine ⟨fun i j hj hi => ?_, ?_⟩
  · have e1 : i = Fin.natAdd m ⟨i - m, by omega⟩ := by ext; simp; omega
    have e2 : j = Fin.castAdd k ⟨j, hj⟩ := by ext; simp
    rw [e1, e2, blockDiagExtendByIdentity_conj_lowerLeft_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [h.1 _ _ (by simp) (by simp), zero_mul]
  · have : br m (m + k - m) (dM k A * X * dM k B) = br m (m + k - m) X := by
      ext i j
      exact entN_blockDiagExtendByIdentity_conj_lowerRight A B X _ _ (by omega) (by omega)
    rw [this]; exact h.2

theorem supFrom_conj (hm : 1 ≤ m) (A B : Mt g m) (hA : InMir A) (X : Mt g (m + k)) :
    supFrom (m - 1) (dM k A * X * dM k B) = supFrom (m - 1) X := by
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  by_cases h : m ≤ j
  · exact entN_blockDiagExtendByIdentity_conj_lowerRight A B X _ _ h (by omega)
  · have h' : j < m + k ∧ j + 1 < m + k := ⟨by omega, by omega⟩
    have e1 : (⟨j, h'.1⟩ : Fin (m + k)) = Fin.castAdd k ⟨j, by omega⟩ := by ext; simp
    have e2 : (⟨j + 1, h'.2⟩ : Fin (m + k)) = Fin.natAdd m ⟨0, by omega⟩ := by ext; simp; omega
    rw [entN, entN, dif_pos h', dif_pos h', e1, e2, blockDiagExtendByIdentity_conj_upperRight_apply]
    have : ∀ l, A ⟨j, by omega⟩ l = (1 : Mt g m) ⟨j, by omega⟩ l := fun l => hA _ _ (by simp; omega)
    simp [this, Matrix.one_apply]

theorem inMir_of (X : Mt g (m + k)) (h : InR m X) (h0 : InMir (tl m X)) : InMir X := by
  intro i j hi
  by_cases him : (i : ℕ) < m
  · have hj : (j : ℕ) < m := by omega
    have e1 : i = Fin.castAdd k ⟨i, him⟩ := by ext; simp
    have e2 : j = Fin.castAdd k ⟨j, hj⟩ := by ext; simp
    have := h0 ⟨i, him⟩ ⟨j, hj⟩ (by simp; omega)
    rw [tl_apply, ← e1, ← e2] at this
    rw [this]
    simp [Matrix.one_apply, Fin.ext_iff]
  · by_cases hj : (j : ℕ) < m
    · rw [h.1 i j hj (by omega), Matrix.one_apply_ne]
      intro e; subst e; omega
    · have h2 := h.2 ⟨i - m, by omega⟩ ⟨j - m, by omega⟩
      have h' : m + (i - m) < m + k ∧ m + (j - m) < m + k := ⟨by omega, by omega⟩
      have e1 : (⟨m + (i - m), h'.1⟩ : Fin (m + k)) = i := by ext; simp; omega
      have e2 : (⟨m + (j - m), h'.2⟩ : Fin (m + k)) = j := by ext; simp; omega
      simp only [br, entN, dif_pos h', e1, e2] at h2
      by_cases e : i = j
      · subst e
        rw [h2.2 rfl, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne e]
        refine h2.1 ?_
        have : (i : ℕ) ≠ j := fun h => e (Fin.ext h)
        rw [Fin.lt_def]
        simp only
        omega

theorem inMir_dM (A : Mt g m) (hA : InMir A) : InMir (dM k A) := by
  have e : dM k A = dM k A * 1 * dM k 1 := by rw [dM_one, mul_one, mul_one]
  have h1 : InR m (1 : Mt g (m + k)) := by
    refine ⟨fun i j hj hi => Matrix.one_apply_ne (by intro e; subst e; omega), fun a b => ?_⟩
    have h' : m + a < m + k ∧ m + b < m + k := ⟨by omega, by omega⟩
    simp only [br, entN, dif_pos h', Matrix.one_apply, Fin.ext_iff, Fin.lt_def]
    constructor
    · intro h; rw [if_neg (by omega)]
    · intro h; rw [if_pos (by omega)]
  have h2 : tl m (1 : Mt g (m + k)) = 1 := by
    ext i j
    simp [tl_apply, Matrix.one_apply, Fin.ext_iff]
  refine inMir_of _ (e ▸ inR_conj _ _ _ h1) ?_
  rw [e, upperLeftBlock_blockDiagExtendByIdentity_conj, h2, mul_one, mul_one]
  exact hA

theorem isMirClass_tail (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (m n : ℕ) (F : Gn g n → ℂ)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hF : IsMirClass F) : IsMirClass (tail ψ m F) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  intro p x₀ hp hx₀
  unfold tail
  congr 1
  symm
  refine Fintype.sum_equiv (MulAut.conj (dG k p)).toEquiv _ _ fun x => ?_
  have e : (MulAut.conj (dG k p)).toEquiv x = dG k p * x * (dG k p)⁻¹ := rfl
  rw [e]
  have hiff : (InR m (x : Mt g (m + k)) ∧ tl m (x : Mt g (m + k)) = (x₀ : Mt g m)) ↔
      (InR m ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) ∧
        tl m ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) = ((p * x₀ * p⁻¹ : Gn g m) : Mt g m)) := by
    rw [conj_val, upperLeftBlock_blockDiagExtendByIdentity_conj, Units.val_mul, Units.val_mul, Units.mul_left_inj, Units.mul_right_inj]
    refine and_congr_left fun _ => ⟨inR_conj _ _ _, fun h => ?_⟩
    have := inR_conj ((p⁻¹ : Gn g m) : Mt g m) (p : Mt g m) _ h
    rwa [← mul_assoc, ← mul_assoc, mul_assoc _ (dM k _) (dM k _), dM_mul, Units.inv_mul, dM_one,
      one_mul, mul_one] at this
  by_cases h : InR m (x : Mt g (m + k)) ∧ tl m (x : Mt g (m + k)) = (x₀ : Mt g m)
  · rw [if_pos h, if_pos (hiff.1 h), hF _ _ (inMir_dM _ hp) (inMir_of _ h.1 (h.2 ▸ hx₀)), conj_val,
      supFrom_conj hm _ _ hp]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

end GlobalTheory.GLm.TailClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotypicTraceEqOfOneDoubleCoset
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.OneDoubleCoset

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem isClass_mul_comm {φ : G → ℂ} (hφ : IsClass φ) (x y : G) : φ (x * y) = φ (y * x) := by
  have := hφ (y * x) x
  rw [← this]; congr 1; group

theorem coset_sum_mem (K : Subgroup G) (l : K →* ℂˣ) (φ : G → ℂ) (b : K) :
    ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ (a * b) =
      (l b : ℂ) * ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ a := by
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulRight b⁻¹)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Equiv.coe_mulRight, map_mul, map_inv, mul_inv_rev, inv_inv, Units.val_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel, mul_one]

theorem coset_sum_eq_zero (K : Subgroup G) (l : K →* ℂˣ) {φ : G → ℂ} (hφ : IsClass φ) (h : G)
    (a₀ a₁ : K) (e : (a₁ : G) = h⁻¹ * a₀ * h) (ne : l a₁ ≠ l a₀) :
    ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ (a * h) = 0 := by
  set F := ∑ a : K, (((l a)⁻¹ : ℂˣ) : ℂ) * φ (a * h) with hF
  have key : F = ((l a₁ * (l a₀)⁻¹ : ℂˣ) : ℂ) * F := by
    conv_lhs => rw [hF, ← Equiv.sum_comp ((Equiv.mulRight a₀).trans (Equiv.mulLeft a₁⁻¹))]
    rw [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : φ (((a₁⁻¹ * (c * a₀) : K) : G) * h) = φ (c * h) := by
      rw [← hφ (c * h) (a₁ : G)⁻¹]
      congr 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
      congr 2
      rw [e]; group
    simp only [Equiv.trans_apply, Equiv.coe_mulRight, Equiv.coe_mulLeft]
    rw [h1]
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv, Units.val_mul]
    ring
  by_contra hne
  apply ne
  have : ((l a₁ * (l a₀)⁻¹ : ℂˣ) : ℂ) = 1 := by
    have h2 : (((l a₁ * (l a₀)⁻¹ : ℂˣ) : ℂ) - 1) * F = 0 := by rw [sub_mul, ← key]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hne)
  exact mul_inv_eq_one.1 (Units.val_eq_one.1 this)

theorem sum_indicator (H₁ H₂ : Subgroup G) :
    ∑ b : H₂, (if (b : G) ∈ H₁ then (1 : ℂ) else 0) =
      ((Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂).card : ℂ) := by
  rw [Finset.sum_boole]
  congr 1
  refine Finset.card_bij (fun b _ => (b : G)) ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact ⟨hb, b.2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact ⟨⟨g, hg.2⟩, by simpa using hg.1, rfl⟩

theorem double_sum (H₁ H₂ : Subgroup G) (l₁ : H₁ →* ℂˣ) (l₂ : H₂ →* ℂˣ)
    (hag : ∀ (a : H₁) (b : H₂), (a : G) = b → l₁ a = l₂ b)
    (hM : ∀ h ∈ H₂, h ∉ H₁ → ∃ a a' : H₁, (a' : G) = h⁻¹ * a * h ∧ l₁ a' ≠ l₁ a)
    {φ : G → ℂ} (hφ : IsClass φ) :
    ∑ b : H₂, ∑ a : H₁, (((l₂ b)⁻¹ : ℂˣ) : ℂ) * ((((l₁ a)⁻¹ : ℂˣ) : ℂ) * φ (a * b)) =
      ((Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂).card : ℂ) *
        ∑ a : H₁, (((l₁ a)⁻¹ : ℂˣ) : ℂ) * φ a := by
  rw [← sum_indicator, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum]
  split_ifs with hb
  · have := coset_sum_mem H₁ l₁ φ ⟨b, hb⟩
    simp only at this
    rw [this, hag ⟨b, hb⟩ b rfl, ← mul_assoc, Units.inv_mul]
  · obtain ⟨a₀, a₁, e, ne⟩ := hM b b.2 hb
    rw [coset_sum_eq_zero H₁ l₁ hφ b a₀ a₁ e ne]; simp

theorem isotypic_trace_eq : ∀ (G : Type) [Group G] [Fintype G] (H H₁ H₂ : Subgroup G) (l₁ : H₁ →* ℂˣ) (l₂ : H₂ →* ℂˣ), H₁ ≤ H → H₂ ≤ H → Nat.card H₁ = Nat.card H₂ → (∀ (a : H₁) (b : H₂), (a : G) = b → l₁ a = l₂ b) → (∀ h ∈ H, h ∉ H₁ → ∃ a a' : H₁, (a' : G) = h⁻¹ * a * h ∧ l₁ a' ≠ l₁ a) → (∀ h ∈ H, h ∉ H₂ → ∃ b b' : H₂, (b' : G) = h⁻¹ * b * h ∧ l₂ b' ≠ l₂ b) → ∀ φ : G → ℂ, IsClass φ → (Nat.card H₁ : ℂ)⁻¹ * ∑ a : H₁, ((l₁ a)⁻¹ : ℂˣ) * φ a = (Nat.card H₂ : ℂ)⁻¹ * ∑ b : H₂, ((l₂ b)⁻¹ : ℂˣ) * φ b := by
  intro G _ _ H H₁ H₂ l₁ l₂ h1 h2 hc hag hM1 hM2 φ hφ
  have e1 := double_sum H₁ H₂ l₁ l₂ hag (fun h hh => hM1 h (h2 hh)) hφ
  have e2 := double_sum H₂ H₁ l₂ l₁ (fun b a e => (hag a b e.symm).symm)
    (fun h hh => hM2 h (h1 hh)) hφ
  have hf : (Finset.univ.filter fun g : G => g ∈ H₂ ∧ g ∈ H₁) =
      (Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂) :=
    Finset.filter_congr fun g _ => and_comm
  rw [hf, Finset.sum_comm] at e2
  have hN : ((Finset.univ.filter fun g : G => g ∈ H₁ ∧ g ∈ H₂).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨1, by simp⟩
  rw [hc]
  congr 1
  apply mul_left_cancel₀ hN
  rw [← e1, ← e2]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [isClass_mul_comm hφ (a : G) b]; ring

end GlobalTheory.GLm.OneDoubleCoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepLevelTLat
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.St.G.stepLevel_tLat : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : _root_.Formalism.L2.Forms.StepLevel F E σ J T f bad),
    _root_.GlobalTheory.St.G.TLat σ J T f S.Lb := by
  intro F E _ _ _ _ _ n σ J T f bad S
  refine ⟨⟨S.Lb_fin, S.Lb_span⟩, S.Lb_int, S.Lb_dual, S.Lb_index, fun v hv => ?_⟩
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (S.fT_ne v hv)
  exact ⟨x, x.2, fun hmem => hx (S.fT_L v hv x hmem)⟩

end GlobalTheory.St.G
end

