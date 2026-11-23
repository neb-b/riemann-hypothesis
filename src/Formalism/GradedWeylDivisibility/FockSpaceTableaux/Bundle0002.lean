module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0005

@[expose] public section

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
section
open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

section general

variable {σ : Type*}

lemma LFocks_C_mul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (C c * f) g = c * fockF f g := by
  rw [C_mul', fischerInner_eq_sum_of_subset (c • f) g f.support support_smul, fockF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

lemma LFocks_C_mul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (C c * g) = star c * fockF f g := by
  simp only [fockF, coeff_C_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

lemma LFocks_C_left (a : ℂ) (g : MvPolynomial σ ℂ) :
    fockF (C a) g = a * star (constantCoeff g) := by
  rw [C_apply, fischerInner_monomial_left, Finsupp.support_zero, Finset.prod_empty, Nat.cast_one, mul_one,
    constantCoeff_eq]

end general

variable {σ : Type*} [Fintype σ]

lemma LFocks_sub_X (U : Matrix σ σ ℂ) (i : σ) :
    sub U (X i) = ∑ j, C (U i j) * X j := by
  unfold sub
  exact aeval_X _ _

lemma LFocks_sub_C (U : Matrix σ σ ℂ) (a : ℂ) :
    sub U (C a) = C a := by
  unfold sub
  rw [aeval_C, algebraMap_eq]

lemma LFocks_constantCoeff_sub (U : Matrix σ σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (sub U g) = constantCoeff g := by
  induction g using MvPolynomial.induction_on
  next a => rw [LFocks_sub_C]
  next p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  next p i hp =>
    rw [map_mul, map_mul, map_mul, LFocks_sub_X]
    simp

lemma LFocks_sub_comp (A B : Matrix σ σ ℂ) :
    (sub A).comp (sub B) = sub (B * A) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AlgHom.comp_apply, LFocks_sub_X, LFocks_sub_X, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, LFocks_sub_C, LFocks_sub_X, Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

variable [DecidableEq σ]

lemma LFocks_sub_one : sub (1 : Matrix σ σ ℂ) = AlgHom.id ℂ (MvPolynomial σ ℂ) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [LFocks_sub_X, Matrix.one_apply]

lemma LFocks_pderiv_sub (V : Matrix σ σ ℂ) (i : σ) (g : MvPolynomial σ ℂ) :
    pderiv i (sub V g) = ∑ j, C (V j i) * sub V (pderiv j g) := by
  induction g using MvPolynomial.induction_on
  next a => simp
  next p q hp hq => simp only [map_add (f := _), mul_add, Finset.sum_add_distrib, hp, hq]
  next p k hp =>
    have hS : pderiv i (sub V (X k)) = C (V k i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LFocks_sub_X, map_sum]
      simp [pderiv_X, Pi.single_apply]
    have hT : ∀ j, sub V (pderiv j (X k : MvPolynomial σ ℂ)) = if j = k then 1 else 0 := by
      intro j
      rw [pderiv_X]
      by_cases h : j = k
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [map_mul, pderiv_mul, hp, hS]
    simp only [pderiv_mul, map_add (f := _), map_mul, hT, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp [mul_comm]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas
section
namespace Formalism.GradedWeylDivisibility

open MvPolynomial

def idPoint (R : Type*) [CommRing R] (r n : ℕ) : Fin r × Fin n → R :=
  fun v => if v.1.val = v.2.val then 1 else 0

theorem eval_idPoint_lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r)
    (hn : s ≤ n) : eval (idPoint R r n) (lpMinor R s hr hn) = 1 := by
  unfold lpMinor
  rw [RingHom.map_det]
  convert Matrix.det_one (R := R) (n := Fin s)
  ext p q
  simp [RingHom.mapMatrix_apply, idPoint, Matrix.one_apply]
  exact if_congr Fin.val_inj rfl rfl

theorem hwrow_sum_single_castLE {r s : ℕ} (hr : s ≤ r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      fun a => if a.val < s then 1 else 0 := by
  have h1 : (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      ∑ q : Fin s, (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ) :=
    Equiv.sum_comp σ (fun q => (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ))
  rw [h1]
  funext a
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · exact if_pos (Fin.ext rfl)
    · intro b _ hb
      rw [if_neg]
      intro hab
      subst hab
      exact hb (Fin.ext rfl)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hab
    subst hab
    exact h b.isLt

theorem lpMinor_rowHom (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (lpMinor R s hr hn)
      (fun a => if a.val < s then 1 else 0) := by
  unfold lpMinor
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hk : IsWeightedHomogeneous (rowW r n)
      (∏ i, (Matrix.of fun p q : Fin s =>
        (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) (σ i) i)
      (fun a : Fin r => if a.val < s then 1 else 0) := by
    rw [← hwrow_sum_single_castLE hr σ]
    apply IsWeightedHomogeneous.prod
    intro i _
    simp only [Matrix.of_apply]
    exact isWeightedHomogeneous_X R (rowW r n) _
  rw [← mem_weightedHomogeneousSubmodule] at hk ⊢
  rw [Units.smul_def]
  exact zsmul_mem hk _

end Formalism.GradedWeylDivisibility
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LNondomLemmas
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

set_option linter.unusedSimpArgs false

section NonDom

variable {R : Type*} [CommRing R] {r n : ℕ}

def ndEul (R : Type*) [CommRing R] (r n : ℕ) (s : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => (colW r n v s) • X v

def ndE (R : Type*) [CommRing R] (r n : ℕ) (l j : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.2 = j then X (v.1, l) else 0

def ndF (R : Type*) [CommRing R] (r n : ℕ) (l j : Fin n) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.2 = l then X (v.1, j) else 0

lemma nd_weight_apply (s : Fin n) (m : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (fun v => colW r n v s) m = Finsupp.weight (colW r n) m s := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]

lemma ndEul_coeff (s : Fin n) (g : MvPolynomial (Fin r × Fin n) R) (m : Fin r × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (ndEul R r n s g) m =
      (Finsupp.weight (fun v => colW r n v s) m : R) * AddMonoidAlgebra.coeff g m := by
  classical
  induction g using MvPolynomial.induction_on generalizing m with
  | C a =>
    rw [derivation_C, AddMonoidAlgebra.coeff_zero, coeff_C]
    split_ifs with h
    · subst h; simp
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]
  | mul_X p v hp =>
    have hX : ndEul R r n s (X v) = colW r n v s • X v := mkDerivation_X _ _ _
    rw [Derivation.leibniz, hX, MvPolynomial.coeff_add, smul_eq_mul, smul_eq_mul,
      mul_smul_comm, coeff_smul, coeff_mul_X', coeff_X_mul']
    split_ifs with h
    · rw [hp]
      have hle : Finsupp.single v 1 ≤ m := by
        rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
      have hm : m = (m - Finsupp.single v 1) + Finsupp.single v 1 := (tsub_add_cancel_of_le hle).symm
      have hw : Finsupp.weight (fun v => colW r n v s) m =
          Finsupp.weight (fun v => colW r n v s) (m - Finsupp.single v 1) + colW r n v s := by
        conv_lhs => rw [hm]
        rw [map_add (f := _), Finsupp.weight_single, one_smul]
      rw [hw, nsmul_eq_mul]; push_cast; ring
    · simp

lemma ndEul_homog {g : MvPolynomial (Fin r × Fin n) R} {μ : Fin n → ℕ}
    (hg : IsWeightedHomogeneous (colW r n) g μ) (s : Fin n) :
    ndEul R r n s g = (μ s : R) • g := by
  ext m
  rw [ndEul_coeff, coeff_smul, smul_eq_mul]
  by_cases h : AddMonoidAlgebra.coeff g m = 0
  · simp [h]
  · rw [nd_weight_apply, hg h]

lemma ndEul_neg_eq_zero [IsDomain R] [CharZero R] {g : MvPolynomial (Fin r × Fin n) R}
    (s : Fin n) (h : ndEul R r n s g = -g) : g = 0 := by
  ext m
  have h1 := congrArg (AddMonoidAlgebra.coeff · m) h
  rw [ndEul_coeff, coeff_neg] at h1
  have h2 : ((Finsupp.weight (fun v => colW r n v s) m : R) + 1) * AddMonoidAlgebra.coeff g m = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (Nat.cast_add_one_ne_zero _)
  · simpa using h3

lemma nd_comm_EF {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndE R r n l j (ndF R r n l j g) =
      ndF R r n l j (ndE R r n l j g) + (ndEul R r n l g - ndEul R r n j g) := by
  have key : ⁅ndE R r n l j, ndF R r n l j⁆ = ndEul R r n l - ndEul R r n j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply, Derivation.sub_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply, Derivation.sub_apply] at this
  rw [← this]; abel

lemma nd_comm_EulF_l {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEul R r n l (ndF R r n l j g) = ndF R r n l j (ndEul R r n l g) - ndF R r n l j g := by
  have key : ⁅ndEul R r n l, ndF R r n l j⁆ = -ndF R r n l j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply, Derivation.neg_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply, Derivation.neg_apply] at this
  rw [sub_eq_iff_eq_add.1 this]; abel

lemma nd_comm_EulF_j {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEul R r n j (ndF R r n l j g) = ndF R r n l j (ndEul R r n j g) + ndF R r n l j g := by
  have key : ⁅ndEul R r n j, ndF R r n l j⁆ = ndF R r n l j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a, s⟩
    rw [Derivation.commutator_apply]
    by_cases h1 : s = l
    · subst h1
      simp [ndE, ndF, ndEul, colW, hlj, hlj.symm, Pi.single_apply]
    · by_cases h2 : s = j
      · subst h2
        simp [ndE, ndF, ndEul, colW, h1, hlj, Pi.single_apply]
      · simp [ndE, ndF, ndEul, colW, h1, h2, Ne.symm h1, Ne.symm h2, Pi.single_apply]
  have := congrArg (fun D => D g) key
  simp only [Derivation.commutator_apply] at this
  rw [sub_eq_iff_eq_add.1 this]; abel

end NonDom

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowstLemmas
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

section General

variable {R : Type*} [CommRing R] {σ τ M : Type*} [AddCommMonoid M]

theorem isWH_algHom_monomial (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (w : σ → M) (w' : τ → M)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (m : σ →₀ ℕ) (c : R) :
    IsWeightedHomogeneous w' (φ (monomial m c)) (Finsupp.weight w m) := by
  have hC : φ (C c) = C c := by
    rw [← MvPolynomial.algebraMap_eq]
    exact φ.commutes c
  rw [monomial_eq, map_mul, hC, Finsupp.prod, map_prod]
  simp only [map_pow]
  have h := (isWeightedHomogeneous_C w' c).mul
    (IsWeightedHomogeneous.prod m.support (fun v => φ (X v) ^ m v) (fun v => m v • w v)
      (fun v _ => (hφ v).pow (m v)))
  rw [zero_add] at h
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact h

theorem isWH_algHom (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (w : σ → M) (w' : τ → M)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) {f : MvPolynomial σ R} {d : M}
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w' (φ f) d := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  have h := isWH_algHom_monomial φ w w' hφ s (AddMonoidAlgebra.coeff f s)
  rwa [hf (mem_support_iff.mp hs)] at h

private theorem weightedHomogeneousComponent_self_of_isWH {w : σ → M} {p : MvPolynomial σ R} {m : M}
    (hp : IsWeightedHomogeneous w p m) : weightedHomogeneousComponent w m p = p := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with h
  · rfl
  · by_contra hd
    exact h (hp (Ne.symm hd))

private theorem weightedHomogeneousComponent_eq_zero_of_isWH_ne {w : σ → M} {p : MvPolynomial σ R} {m μ : M}
    (hne : m ≠ μ) (hp : IsWeightedHomogeneous w p m) : weightedHomogeneousComponent w μ p = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  split_ifs with h
  · by_contra hd
    exact hne ((hp hd).symm.trans h)
  · rfl

theorem algHom_weightedHomogeneousComponent (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (w : σ → M) (w' : τ → M) (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (μ : M)
    (f : MvPolynomial σ R) :
    φ (weightedHomogeneousComponent w μ f) = weightedHomogeneousComponent w' μ (φ f) := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs := isWH_algHom_monomial φ w w' hφ s (AddMonoidAlgebra.coeff f s)
  have hm : IsWeightedHomogeneous w (monomial s (AddMonoidAlgebra.coeff f s)) (Finsupp.weight w s) :=
    isWeightedHomogeneous_monomial w s (AddMonoidAlgebra.coeff f s) rfl
  by_cases h : Finsupp.weight w s = μ
  · subst h
    rw [weightedHomogeneousComponent_self_of_isWH hm, weightedHomogeneousComponent_self_of_isWH hs]
  · rw [weightedHomogeneousComponent_eq_zero_of_isWH_ne h hm, weightedHomogeneousComponent_eq_zero_of_isWH_ne h hs,
      map_zero]

end General

theorem rowst_mem_dualWeyl_iff {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule, AlgHom.toLinearMap_apply]

def rowActO (R : Type*) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun o => Option.elim o (X none) (fun v => ∑ b : Fin r, C (g v.1 b) * X (some (b, v.2)))

theorem colAddGen_rowAct {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l j (rowAct R g f) = rowActO R g (colAddGen R l j f) := by
  have key : (colAddGen R l j).comp (rowAct R g) =
      (rowActO R g).comp (colAddGen R (r := r) l j) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, colAddGen, rowAct, rowActO, aeval_X, map_sum,
      map_mul, aeval_C, MvPolynomial.algebraMap_eq]
    by_cases h : t = j
    · simp only [h, if_true, aeval_X, map_add (f := _), map_mul, Option.elim]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    · simp [h]
  exact DFunLike.congr_fun key f

theorem rename_rowAct {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rename (some : Fin r × Fin n → Option (Fin r × Fin n)) (rowAct R g f) =
      rowActO R g (rename some f) := by
  have key : (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).comp (rowAct R g) =
      (rowActO R g).comp (rename some) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    simp [rowAct, rowActO, MvPolynomial.algebraMap_eq]
  exact DFunLike.congr_fun key f

theorem rowAct_X_isWH {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (v : Fin r × Fin n) : IsWeightedHomogeneous (colW r n) (rowAct R g (X v)) (colW r n v) := by
  simp only [rowAct, aeval_X]
  refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
  convert (isWeightedHomogeneous_C (colW r n) (g v.1 b)).mul
    (isWeightedHomogeneous_X (R := R) (colW r n) (b, v.2)) using 1
  simp [colW]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lsat_mem_dualWeyl {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule]

theorem lsat_map_colAddGen {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (colAddGen R l j f) = colAddGen S l j (map φ f) := by
  induction f using MvPolynomial.induction_on
  next a =>
    simp [colAddGen]
  next p q hp hq =>
    simp only [map_add (f := _), hp, hq]
  next p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [colAddGen, aeval_X]
    split_ifs <;> simp

theorem lsat_isWH_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {σ M : Type*}
    [AddCommMonoid M] (w : σ → M) (m : M) (f : MvPolynomial σ R)
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w (map φ f) m := by
  intro d hd
  apply hf
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]

end Formalism.GradedWeylDivisibility
end
end

