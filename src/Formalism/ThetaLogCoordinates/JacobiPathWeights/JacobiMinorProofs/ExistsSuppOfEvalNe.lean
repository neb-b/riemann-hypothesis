module

public import Mathlib
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.Bundle0002

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

section Laurent

variable {A : Type*} [CommRing A] [IsDomain A]





omit [IsDomain A] in
theorem lp_coeff_TC (p : A) (m j : ℤ) :
    (LaurentPolynomial.T m * LaurentPolynomial.C p).coeff j = if m = j then p else 0 := by
  rw [LaurentPolynomial.T_mul, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]

omit [IsDomain A] in
theorem lp_coeff_sum {κ : Type*} (s : Finset κ) (f : κ → LaurentPolynomial A) (j : ℤ) :
    (∑ i ∈ s, f i).coeff j = ∑ i ∈ s, (f i).coeff j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, ih]

omit [IsDomain A] in
theorem prod_laurent_T {κ : Type*} (s : Finset κ) (f : κ → ℤ) :
    ∏ i ∈ s, (LaurentPolynomial.T (f i) : LaurentPolynomial A) = LaurentPolynomial.T (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, LaurentPolynomial.T_add]

end Laurent

section Sharp

variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L]

def wtX (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool) : LVar ι ζ n → ℤ
  | Sum.inl (i, a) =>
    if i ∈ S then
      (if (if last then a.val + 1 = n else a.val = 0) then (if isVec i then 1 else -1) else 0)
    else 0
  | Sum.inr _ => 0

def wExp (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool) (e : LVar ι ζ n →₀ ℕ) : ℤ :=
  ∑ x ∈ e.support, (e x : ℤ) * wtX isVec S last x

abbrev cc (τ : Type*) (L : Type*) [CommRing L] : L →+* LaurentPolynomial (MvPolynomial τ L) :=
  (LaurentPolynomial.C).comp C

theorem conjS_eq (τ : Type*) (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (e : ℤ) :
    conjS τ g gi last e = g.map (cc τ L) * diagS (MvPolynomial τ L) n last e * gi.map (cc τ L) := rfl

theorem conjS_mul (τ : Type*) {g gi : Matrix (Fin n) (Fin n) L} (h : gi * g = 1) (last : Bool) (e : ℤ) :
    conjS τ g gi last e * g.map (cc τ L) = g.map (cc τ L) * diagS (MvPolynomial τ L) n last e := by
  rw [conjS_eq, Matrix.mul_assoc, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.mul_one]

theorem mul_conjS (τ : Type*) {g gi : Matrix (Fin n) (Fin n) L} (h : gi * g = 1) (last : Bool) (e : ℤ) :
    gi.map (cc τ L) * conjS τ g gi last e = diagS (MvPolynomial τ L) n last e * gi.map (cc τ L) := by
  rw [conjS_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, h,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

variable (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

def tw (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) :
    MvPolynomial (LVar ι ζ n) L →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L) :=
  eval₂Hom (cc _ L) fun x =>
    LaurentPolynomial.T (wtX isVec S last x) * LaurentPolynomial.C (sharpHom isVec S g gi (X x))

theorem conjAct_C {k : Type*} [CommRing k] (φ : k →+* L) (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (c : k) :
    conjAct (ζ := ζ) φ isVec S g gi last (C c) = cc _ L (φ c) := by
  simp [conjAct]

theorem conjAct_sharp {g gi : Matrix (Fin n) (Fin n) L} (h : gi * g = 1) (last : Bool)
    (H : MvPolynomial (LVar ι ζ n) L) :
    conjAct (RingHom.id L) isVec S g gi last (sharpHom isVec S g gi H) = tw isVec S g gi last H := by
  suffices hh : (conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last).comp
      (sharpHom isVec S g gi).toRingHom = tw isVec S g gi last from by
    rw [← hh]; rfl
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [tw, conjAct_C, sharpHom]
  · intro x
    rcases x with ⟨i, a⟩ | z
    · by_cases h1 : i ∈ S
      · by_cases h3 : isVec i
        · have e1 : sharpHom isVec S g gi (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
              Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) a := by
            simp [sharpHom, h1, h3]
          have e2 : (⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) ∘
              fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
              Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b)))) (conjS _ g gi last 1) := by
            funext b
            simp [conjAct, h1, h3]
          have e3 : (g.map C).map ⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) = g.map (cc _ L) := by
            ext p q
            simp [conjAct_C]
          have e4 : (g.map (C : L →+* MvPolynomial (LVar ι ζ n) L)).map
              ⇑(LaurentPolynomial.C : _ →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L)) =
              g.map (cc _ L) := by
            ext p q
            simp
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, tw, coe_eval₂Hom, eval₂_X]
          rw [e1, RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, conjS_mul _ h, ← Matrix.vecMul_vecMul,
            diagS, Matrix.vecMul_diagonal, RingHom.map_vecMul, e4, mul_comm]
          congr 1
          by_cases h2 : (if last then a.val + 1 = n else a.val = 0) <;> simp [wtX, h1, h2, h3]
        · have e1 : sharpHom isVec S g gi (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
              Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose a := by
            simp [sharpHom, h1, h3]
          have e2 : (⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) ∘
              fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
              Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b))))
                (conjS _ g gi last (-1)).transpose := by
            funext b
            simp [conjAct, h1, h3]
          have e3 : ((gi.map C).transpose).map ⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) =
              (gi.map (cc _ L)).transpose := by
            ext p q
            simp [conjAct_C]
          have e4 : ((gi.map (C : L →+* MvPolynomial (LVar ι ζ n) L)).transpose).map
              ⇑(LaurentPolynomial.C : _ →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L)) =
              (gi.map (cc _ L)).transpose := by
            ext p q
            simp
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, tw, coe_eval₂Hom, eval₂_X]
          rw [e1, RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.transpose_mul, mul_conjS _ h,
            Matrix.transpose_mul, ← Matrix.vecMul_vecMul,
            diagS, Matrix.diagonal_transpose, Matrix.vecMul_diagonal, RingHom.map_vecMul, e4, mul_comm]
          congr 1
          by_cases h2 : (if last then a.val + 1 = n else a.val = 0) <;> simp [wtX, h1, h2, h3]
      · simp [tw, conjAct, sharpHom, wtX, h1]
    · simp [tw, conjAct, sharpHom, wtX]

theorem tw_monomial (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (e : LVar ι ζ n →₀ ℕ) (c : L) :
    tw isVec S g gi last (monomial e c) =
      LaurentPolynomial.T (wExp isVec S last e) * LaurentPolynomial.C (sharpHom isVec S g gi (monomial e c)) := by
  have e1 : sharpHom isVec S g gi (monomial e c) =
      C c * ∏ x ∈ e.support, (sharpHom isVec S g gi (X x)) ^ (e x) := by
    rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
    simp [sharpHom]
  rw [e1, tw, coe_eval₂Hom, eval₂_monomial, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, LaurentPolynomial.T_pow, prod_laurent_T, map_mul, map_prod, map_pow,
    wExp, RingHom.comp_apply]
  ring

theorem tw_coeff (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (H : MvPolynomial (LVar ι ζ n) L) (j : ℤ) :
    (tw isVec S g gi last H).coeff j =
      sharpHom isVec S g gi
        (∑ e ∈ H.support.filter (fun e => wExp isVec S last e = j), monomial e (AddMonoidAlgebra.coeff H e)) := by
  conv_lhs => rw [H.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, lp_coeff_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [tw_monomial, lp_coeff_TC]

theorem sharp_sharp {g gi : Matrix (Fin n) (Fin n) L} (h : g * gi = 1) (H : MvPolynomial (LVar ι ζ n) L) :
    sharpHom isVec S g gi (sharpHom isVec S gi g H) = H := by
  suffices hh : (sharpHom (ζ := ζ) isVec S g gi).comp (sharpHom isVec S gi g) = AlgHom.id L _ from by
    have := congrArg (fun f => f H) hh
    simpa using this
  apply MvPolynomial.algHom_ext
  intro x
  rcases x with ⟨i, a⟩ | z
  · by_cases h1 : i ∈ S
    · by_cases h3 : isVec i
      · have e1 : sharpHom isVec S gi g (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C) a := by
          simp [sharpHom, h1, h3]
        have e2 : (⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom ∘
            fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) := by
          funext b
          simp [sharpHom, h1, h3]
        have e3 : (gi.map C).map ⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom = gi.map C := by
          ext p q
          simp [sharpHom]
        rw [AlgHom.comp_apply, e1]
        change (sharpHom (ζ := ζ) isVec S g gi).toRingHom _ = _
        rw [RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.map_mul, h,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one]
        rfl
      · have e1 : sharpHom isVec S gi g (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C).transpose a := by
          simp [sharpHom, h1, h3]
        have e2 : (⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom ∘
            fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose := by
          funext b
          simp [sharpHom, h1, h3]
        have e3 : ((g.map C).transpose).map ⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom =
            (g.map C).transpose := by
          ext p q
          simp [sharpHom]
        rw [AlgHom.comp_apply, e1]
        change (sharpHom (ζ := ζ) isVec S g gi).toRingHom _ = _
        rw [RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.transpose_mul, ← Matrix.map_mul, h,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.vecMul_one]
        rfl
    · simp [sharpHom, h1]
  · simp [sharpHom]

theorem sharp_bij {g gi : Matrix (Fin n) (Fin n) L} (h : g * gi = 1) (h' : gi * g = 1) :
    Function.Bijective (sharpHom (ζ := ζ) isVec S g gi) :=
  ⟨Function.LeftInverse.injective (g := sharpHom (ζ := ζ) isVec S gi g) (sharp_sharp isVec S h'),
   Function.RightInverse.surjective (g := sharpHom (ζ := ζ) isVec S gi g) (sharp_sharp isVec S h)⟩

end Sharp

section Gen

variable {ι ζ : Type*} {n : ℕ}

theorem conjAct_map {k L : Type*} [CommRing k] [CommRing L] (φ : k →+* L) (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (G : MvPolynomial (LVar ι ζ n) k) :
    conjAct φ isVec S g gi last G = conjAct (RingHom.id L) isVec S g gi last (map φ G) := by
  suffices hh : conjAct (ζ := ζ) φ isVec S g gi last =
      (conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last).comp (map φ) from by
    rw [hh]; rfl
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [conjAct_C]
  · intro x
    simp [conjAct]

theorem part_ne_zero {σ L : Type*} [CommRing L] (H : MvPolynomial σ L) (p : (σ →₀ ℕ) → Prop) [DecidablePred p] :
    (∑ e ∈ H.support.filter p, monomial e (AddMonoidAlgebra.coeff H e)) ≠ 0 ↔ ∃ e ∈ H.support, p e := by
  classical
  constructor
  · intro h
    by_contra hc
    apply h
    have : H.support.filter p = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he hp
      exact hc ⟨e, he, hp⟩
    rw [this, Finset.sum_empty]
  · rintro ⟨e, he, hp⟩ h
    have := congrArg (AddMonoidAlgebra.coeff · e) h
    rw [coeff_sum] at this
    simp only [coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    simp only [he, hp, and_self, ite_true] at this
    exact (mem_support_iff.mp he) this

theorem conj_mem_supp {L : Type*} [CommRing L] (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] {g gi : Matrix (Fin n) (Fin n) L} (h : g * gi = 1) (h' : gi * g = 1) (last : Bool)
    (G : MvPolynomial (LVar ι ζ n) L) (j : ℤ) :
    j ∈ (conjAct (RingHom.id L) isVec S g gi last G).coeff.support ↔
      ∃ e ∈ (sharpHom isVec S gi g G).support, wExp isVec S last e = j := by
  conv_lhs => rw [← sharp_sharp isVec S h G]
  rw [conjAct_sharp isVec S h', Finsupp.mem_support_iff, tw_coeff, ← part_ne_zero]
  exact (map_ne_zero_iff _ (sharp_bij isVec S h h').1)

variable (k : Type*) [Field k]

abbrev genφ (n : ℕ) : k →+* GenField k n := (algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C

theorem genMat_eq (n : ℕ) : genMat k n =
    (algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) k) := by
  ext a b
  simp [genMat, Matrix.mvPolynomialX]

theorem genMat_det_ne (n : ℕ) : (genMat k n).det ≠ 0 := by
  rw [genMat_eq, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (Matrix.det_mvPolynomialX_ne_zero (Fin n) k)

theorem genMat_mul_inv (n : ℕ) : genMat k n * (genMat k n)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (genMat_det_ne k n))

theorem genMat_inv_mul (n : ℕ) : (genMat k n)⁻¹ * genMat k n = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (genMat_det_ne k n))

variable {k}

def genH (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (G : MvPolynomial (LVar ι ζ n) k) :
    MvPolynomial (LVar ι ζ n) (GenField k n) :=
  sharpHom isVec S (genMat k n)⁻¹ (genMat k n) (map (genφ k n) G)

theorem gen_mem_supp (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool)
    (G : MvPolynomial (LVar ι ζ n) k) (j : ℤ) :
    j ∈ (genAct k isVec S last G).coeff.support ↔ ∃ e ∈ (genH isVec S G).support, wExp isVec S last e = j := by
  rw [genAct, conjAct_map]
  exact conj_mem_supp isVec S (genMat_mul_inv k n) (genMat_inv_mul k n) last _ j

end Gen

section Consts

variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

end Consts

section Coord

variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

end Coord

section DetPart

variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

end DetPart

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
