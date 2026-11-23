module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0002
public import Mathlib
public import Lemmata.GeneralBFactMore.Imports
public import Lemmata.FirstBlockLemmaA.Imports

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodB
section
namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {σ : Type}

abbrev qmap : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)

def qIdeal (P : Ideal (MvPolynomial σ ℤ)) : Ideal (MvPolynomial σ ℚ) := P.map qmap

theorem qmap_injective : Function.Injective (qmap : MvPolynomial σ ℤ → MvPolynomial σ ℚ) := MvPolynomial.map_injective _ Int.cast_injective

theorem exists_int_mul_eq_qmap (q : MvPolynomial σ ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ q' : MvPolynomial σ ℤ, (D : MvPolynomial σ ℚ) * q = qmap q' := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨a.den, by exact_mod_cast a.den_nz, MvPolynomial.monomial u a.num, ?_⟩
    rw [show ((a.den : ℤ) : MvPolynomial σ ℚ) = C ((a.den : ℤ) : ℚ) from (map_intCast (C : ℚ →+* MvPolynomial σ ℚ) _).symm,
      C_mul_monomial, MvPolynomial.map_monomial]
    congr 1
    push_cast
    exact Rat.den_mul_eq_num a
  | add p q hp hq =>
    obtain ⟨D₁, hD₁, p', hp'⟩ := hp
    obtain ⟨D₂, hD₂, q', hq'⟩ := hq
    refine ⟨D₁ * D₂, mul_ne_zero hD₁ hD₂, (D₂ : MvPolynomial σ ℤ) * p' + (D₁ : MvPolynomial σ ℤ) * q', ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_intCast, map_intCast, ← hp', ← hq']
    push_cast
    ring

theorem exists_int_mul_mem_of_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) {g : MvPolynomial σ ℚ}
    (hg : g ∈ qIdeal P) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ h ∈ P, (N : MvPolynomial σ ℚ) * g = qmap h := by
  have hg' : g ∈ Submodule.span (MvPolynomial σ ℚ) (qmap '' (P : Set (MvPolynomial σ ℤ))) := hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    exact ⟨1, one_ne_zero, h, hh, by simp⟩
  | zero => exact ⟨1, one_ne_zero, 0, P.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, hN₁, h₁, hh₁, e₁⟩ := hx
    obtain ⟨N₂, hN₂, h₂, hh₂, e₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, (N₂ : MvPolynomial σ ℤ) * h₁ + (N₁ : MvPolynomial σ ℤ) * h₂,
      P.add_mem (P.mul_mem_left _ hh₁) (P.mul_mem_left _ hh₂), ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_intCast, map_intCast, ← e₁, ← e₂]
    push_cast
    ring
  | smul a x _ hx =>
    obtain ⟨N, hN, h, hh, e⟩ := hx
    obtain ⟨D, hD, a', ha'⟩ := exists_int_mul_eq_qmap a
    refine ⟨D * N, mul_ne_zero hD hN, a' * h, P.mul_mem_left _ hh, ?_⟩
    rw [map_mul, ← ha', ← e, smul_eq_mul]
    push_cast
    ring

theorem mem_of_qmap_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) {f : MvPolynomial σ ℤ}
    (hf : qmap f ∈ qIdeal P) : f ∈ P := by
  obtain ⟨N, hN, h, hh, e⟩ := exists_int_mul_mem_of_mem_qIdeal P hf
  have hNf : (N : MvPolynomial σ ℤ) * f = h := by
    apply qmap_injective
    rw [map_mul, map_intCast, e]
  rw [← hNf, show (N : MvPolynomial σ ℤ) = C N from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) N).symm] at hh
  rcases hP.mem_or_mem hh with hC | hf'
  · have : N ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hC
    rw [hH] at this
    exact absurd ((Submodule.mem_bot ℤ).mp this) hN
  · exact hf'

def ratHom (P : Ideal (MvPolynomial σ ℤ)) :
    MvPolynomial σ ℤ ⧸ P →+* MvPolynomial σ ℚ ⧸ qIdeal P :=
  Ideal.quotientMap (qIdeal P) qmap Ideal.le_comap_map

theorem ratHom_mk (P : Ideal (MvPolynomial σ ℤ)) (f : MvPolynomial σ ℤ) :
    ratHom P (Ideal.Quotient.mk P f) = Ideal.Quotient.mk (qIdeal P) (qmap f) := rfl

theorem ratHom_isLocalization (P : Ideal (MvPolynomial σ ℤ)) :
    (letI := (ratHom P).toAlgebra
     IsLocalization (Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
       (MvPolynomial σ ℚ ⧸ qIdeal P)) := by
  let _ := (ratHom P).toAlgebra
  have hcast : ∀ n : ℤ, algebraMap (MvPolynomial σ ℤ ⧸ P) (MvPolynomial σ ℚ ⧸ qIdeal P)
      (algebraMap ℤ (MvPolynomial σ ℤ ⧸ P) n) = algebraMap ℚ (MvPolynomial σ ℚ ⧸ qIdeal P) n := by
    intro n
    rw [eq_intCast, map_intCast, map_intCast]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.mp hy
    rw [hcast]
    exact (IsUnit.mk0 (n : ℚ) (by exact_mod_cast nonZeroDivisors.ne_zero hn)).map _
  · intro z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨D, hD, q', hq'⟩ := exists_int_mul_eq_qmap q
    refine ⟨⟨Ideal.Quotient.mk P q', ⟨algebraMap ℤ _ D,
      Submonoid.mem_map.mpr ⟨D, mem_nonZeroDivisors_of_ne_zero hD, rfl⟩⟩⟩, ?_⟩
    change _ * algebraMap (MvPolynomial σ ℤ ⧸ P) _ (algebraMap ℤ _ D) = ratHom P (Ideal.Quotient.mk P q')
    rw [hcast, ratHom_mk, ← hq', mul_comm, map_mul]
    congr 1
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change ratHom P _ = ratHom P _ at hxy
    rw [ratHom_mk, ratHom_mk, Ideal.Quotient.eq, ← map_sub] at hxy
    obtain ⟨N, hN, h, hh, e⟩ := exists_int_mul_mem_of_mem_qIdeal P hxy
    have hNab : (N : MvPolynomial σ ℤ) * (a - b) = h := by
      apply qmap_injective
      rw [map_mul, map_intCast, e]
    refine ⟨⟨algebraMap ℤ _ N, Submonoid.mem_map.mpr ⟨N, mem_nonZeroDivisors_of_ne_zero hN, rfl⟩⟩, ?_⟩
    change algebraMap ℤ _ N * Ideal.Quotient.mk P a = algebraMap ℤ _ N * Ideal.Quotient.mk P b
    rw [← sub_eq_zero, ← mul_sub, ← map_sub, eq_intCast, ← map_intCast (Ideal.Quotient.mk P), ← map_mul,
      hNab, Ideal.Quotient.eq_zero_iff_mem]
    exact hh

theorem isDomain_qQuot (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) :
    IsDomain (MvPolynomial σ ℚ ⧸ qIdeal P) := by
  let _ := (ratHom P).toAlgebra
  have := ratHom_isLocalization P
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := MvPolynomial σ ℤ ⧸ P)
    (M := Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
    (S := MvPolynomial σ ℚ ⧸ qIdeal P) ?_
  rintro _ ⟨n, hn, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h0
  rw [eq_intCast, ← map_intCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem,
    show (n : MvPolynomial σ ℤ) = C n from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) n).symm] at h0
  have : n ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := h0
  rw [hH] at this
  exact nonZeroDivisors.ne_zero hn ((Submodule.mem_bot ℤ).mp this)

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
section
namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

def substFun {r : ℕ} (lam : Fin r → k) : Fin (r + 1) → Polynomial (MvPolynomial (Fin r) k) :=
  Fin.cons Polynomial.X (fun i => Polynomial.C (C (lam i)) * Polynomial.X + Polynomial.C (X i))

def subst {r : ℕ} (lam : Fin r → k) :
    MvPolynomial (Fin (r + 1)) k →ₐ[k] Polynomial (MvPolynomial (Fin r) k) :=
  aeval (substFun lam)

theorem substFun_natDegree {r : ℕ} (lam : Fin r → k) (j : Fin (r + 1)) :
    (substFun lam j).natDegree ≤ 1 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [substFun]
  · simp only [substFun, Fin.cons_succ]
    exact Polynomial.natDegree_linear_le

theorem substFun_coeff_one {r : ℕ} (lam : Fin r → k) (j : Fin (r + 1)) :
    (substFun lam j).coeff 1 = C ((Fin.cons (1 : k) lam : Fin (r + 1) → k) j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [substFun]
  · simp [substFun, Polynomial.coeff_C]

theorem prod_pow_natDegree_coeff {R ι : Type*} [CommRing R] (s : Finset ι) (p : ι → Polynomial R)
    (e : ι → ℕ) (hp : ∀ i, (p i).natDegree ≤ 1) :
    (∏ i ∈ s, p i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧
      (∏ i ∈ s, p i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (p i).coeff 1 ^ e i := by
  classical
  have hpow (i : ι) : (p i ^ e i).natDegree ≤ e i ∧
      (p i ^ e i).coeff (e i) = (p i).coeff 1 ^ e i := by
    constructor
    · calc
        (p i ^ e i).natDegree ≤ e i * (p i).natDegree := Polynomial.natDegree_pow_le
        _ ≤ e i * 1 := Nat.mul_le_mul_left _ (hp i)
        _ = e i := Nat.mul_one _
    · simpa only [Nat.mul_one] using
        (Polynomial.coeff_pow_of_natDegree_le (m := e i) (hp i))
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hpow a).1 ih.1),
      (Polynomial.coeff_mul_add_eq_of_natDegree_le (hpow a).1 ih.1).trans
        (congrArg₂ (· * ·) (hpow a).2 ih.2)⟩

theorem subst_monomial {r : ℕ} (lam : Fin r → k) (m : Fin (r + 1) →₀ ℕ) (a : k) :
    (subst lam (monomial m a)).natDegree ≤ Finsupp.degree m ∧
      (subst lam (monomial m a)).coeff (Finsupp.degree m) =
        C (eval (Fin.cons (1 : k) lam) (monomial m a)) := by
  have h := prod_pow_natDegree_coeff m.support (substFun lam) m (substFun_natDegree lam)
  have hdeg : Finsupp.degree m = ∑ i ∈ m.support, m i := rfl
  simp only [subst, aeval_monomial, Finsupp.prod, eval_monomial]
  rw [hdeg, Polynomial.algebraMap_apply, algebraMap_eq]
  refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans h.1, ?_⟩
  rw [Polynomial.coeff_C_mul, h.2]
  simp only [substFun_coeff_one, ← map_pow, ← map_prod, ← C_mul]

theorem subst_natDegree_le {r : ℕ} (lam : Fin r → k) (F : MvPolynomial (Fin (r + 1)) k) :
    (subst lam F).natDegree ≤ F.totalDegree := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [F.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  exact (subst_monomial lam m _).1.trans (le_totalDegree hm)

theorem subst_coeff_totalDegree {r : ℕ} (lam : Fin r → k) (F : MvPolynomial (Fin (r + 1)) k) :
    (subst lam F).coeff F.totalDegree =
      C (eval (Fin.cons (1 : k) lam) (homogeneousComponent F.totalDegree F)) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show subst lam F = ∑ v ∈ F.support, subst lam (monomial v (AddMonoidAlgebra.coeff F v)) by
    rw [← map_sum, ← F.as_sum]]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [homogeneousComponent_apply, map_sum, map_sum, Polynomial.finsetSum_coeff,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : Finsupp.degree m ≤ F.totalDegree := le_totalDegree hm
  split_ifs with hd
  · rw [← hd]; exact (subst_monomial lam m _).2
  · have hlt : Finsupp.degree m < F.totalDegree := lt_of_le_of_ne hle hd
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((subst_monomial lam m _).1.trans_lt hlt)

theorem homogeneousComponent_totalDegree_ne_zero {σ : Type*} {F : MvPolynomial σ k} (hF : F ≠ 0) :
    homogeneousComponent F.totalDegree F ≠ 0 := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF)
    (fun s => s.sum fun _ e => e)
  intro h0
  have hcoeff := congrArg (AddMonoidAlgebra.coeff · m) h0
  rw [coeff_homogeneousComponent, if_pos (by rw [totalDegree, hmax]; rfl)] at hcoeff
  exact (mem_support_iff.mp hm) (hcoeff.trans rfl)

theorem eval_smul_of_degree {σ : Type*} [Fintype σ] (H : MvPolynomial σ k) (d : ℕ)
    (hH : ∀ m ∈ H.support, Finsupp.degree m = d) (c : k) (v : σ → k) :
    eval (c • v) H = c ^ d * eval v H := by
  first | exact Bl.FirstBlockLemmaA.goal1 .. | (apply Bl.FirstBlockLemmaA.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaA.goal1 <;> assumption)

theorem exists_eval_cons_one_ne_zero [Infinite k] {r : ℕ} (H : MvPolynomial (Fin (r + 1)) k)
    (d : ℕ) (hH : ∀ m ∈ H.support, Finsupp.degree m = d) (h0 : H ≠ 0) :
    ∃ lam : Fin r → k, eval (Fin.cons (1 : k) lam) H ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h0
  have hX : H * X 0 = 0 := by
    apply MvPolynomial.funext
    intro y
    rw [map_mul, eval_X, map_zero]
    by_cases hy : y 0 = 0
    · rw [hy, mul_zero]
    · have hyeq : y = y 0 • (Fin.cons (1 : k) (fun i => (y 0)⁻¹ * y i.succ) : Fin (r + 1) → k) := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp [hy]
      rw [hyeq, eval_smul_of_degree H d hH, hall, mul_zero, zero_mul]
  rcases mul_eq_zero.mp hX with h | h
  · exact h
  · exact absurd h (X_ne_zero 0)

theorem eval₂_subst {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (lam : Fin r → k)
    (ℓ : Fin (r + 1) → R) (F : MvPolynomial (Fin (r + 1)) k) :
    Polynomial.eval₂ ((aeval (fun i => ℓ i.succ - lam i • ℓ 0) : MvPolynomial (Fin r) k →ₐ[k] R) :
      MvPolynomial (Fin r) k →+* R) (ℓ 0) (subst lam F) =
      aeval ℓ F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp [subst, Polynomial.eval₂_C, Polynomial.algebraMap_apply]
  | add p q hp hq => rw [map_add (f := _), Polynomial.eval₂_add, hp, hq, map_add (f := _)]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.eval₂_mul, hp, map_mul]
    congr 1
    simp only [subst, aeval_X]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [substFun]
    · simp [substFun, Algebra.smul_def]

def IntOver (k : Type*) [Field k] {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (ℓ : Fin r → R)
    (x : R) : Prop :=
  ((aeval ℓ : MvPolynomial (Fin r) k →ₐ[k] R) : MvPolynomial (Fin r) k →+* R).IsIntegralElem x

theorem exists_isIntegralElem_linear [Infinite k] {R : Type*} [CommRing R] [Algebra k R] {r : ℕ}
    (ℓ : Fin (r + 1) → R) (F : MvPolynomial (Fin (r + 1)) k) (hF : F ≠ 0) (h : aeval ℓ F = 0) :
    ∃ lam : Fin r → k, IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) (ℓ 0) := by
  classical
  set d := F.totalDegree
  have hsupp : ∀ m ∈ (homogeneousComponent d F).support, Finsupp.degree m = d := by
    intro m hm
    rw [mem_support_iff, coeff_homogeneousComponent] at hm
    by_contra hne
    exact hm (if_neg hne)
  obtain ⟨lam, hlam⟩ := exists_eval_cons_one_ne_zero _ d hsupp
    (homogeneousComponent_totalDegree_ne_zero hF)
  set c := eval (Fin.cons (1 : k) lam) (homogeneousComponent d F)
  refine ⟨lam, Polynomial.C (C c⁻¹) * subst lam F, ?_, ?_⟩
  · refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one d ?_ ?_
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (subst_natDegree_le lam F)
    · rw [Polynomial.coeff_C_mul, subst_coeff_totalDegree, ← C_mul, inv_mul_cancel₀ hlam, C_1]
  · rw [Polynomial.eval₂_mul, eval₂_subst, h, mul_zero]

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

