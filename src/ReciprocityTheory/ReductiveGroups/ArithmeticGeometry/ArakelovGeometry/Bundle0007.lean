module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ComplexHessianTransposeIsHermitian
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Complex Filter Topology Finset Matrix
open scoped ComplexOrder

section

variable {D : ℕ}

theorem mixedDiscriminant_constant (A : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun _ => A) = A.det := by
  show (1 / (D.factorial : ℂ)) * ∑ S : Finset (Fin D), (-1) ^ (D - S.card) * (∑ _k ∈ S, A).det = A.det
  have h1 : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ _k ∈ S, A).det =
      ((-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D) * A.det := by
    intro S
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, Matrix.det_smul, Fintype.card_fin]
    ring
  simp_rw [h1]
  rw [← Finset.sum_mul]
  have h2 : ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D = D.factorial := by
    have h3 := congrFun (fwdDiff_iter_eq_factorial (R := ℂ) (n := D)) 0
    rw [fwdDiff_iter_eq_sum_shift] at h3
    rw [← Finset.powerset_univ,
      Finset.sum_powerset_apply_card (fun k => (-1 : ℂ) ^ (D - k) * (k : ℂ) ^ D),
      Finset.card_univ, Fintype.card_fin]
    simp only [Pi.natCast_apply, zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [h2]
  have : (D.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero D)
  field_simp

theorem complexHessian_transpose_isHermitian {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : IsSymmSndFDerivAt ℝ φ y) (c : ℝ) :
    ((c : ℂ) • (cxHessian φ y).transpose).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.smul_apply, cxHessian,
    smul_eq_mul]
  rw [h (Pi.single j 1) (Pi.single i 1), h (I • Pi.single j 1) (I • Pi.single i 1),
    h (Pi.single j 1) (I • Pi.single i 1), h (I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp

theorem im_hermitian_quadraticForm {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (w : n → ℂ) : (star w ⬝ᵥ M *ᵥ w).im = 0 := by
  have h := hM.im_star_dotProduct_mulVec_self w
  simpa using h

theorem complexHessian_posSemidef {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : IsSymmSndFDerivAt ℝ φ y)
    {c : ℝ} (hc : 0 ≤ c) (hL : ∀ w, 0 ≤ leviForm φ y w) :
    ((c : ℂ) • (cxHessian φ y).transpose).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (complexHessian_transpose_isHermitian h c) fun w => ?_
  rw [Complex.nonneg_iff]
  refine ⟨?_, (im_hermitian_quadraticForm (complexHessian_transpose_isHermitian h c) w).symm⟩
  have e : (star w ⬝ᵥ ((c : ℂ) • (cxHessian φ y).transpose) *ᵥ w) =
      (c : ℂ) * ∑ i, ∑ j, starRingEnd ℂ (w i) * cxHessian φ y j i * w j := by
    simp only [dotProduct, mulVec, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
      Pi.star_apply, Finset.mul_sum, Complex.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, Complex.re_ofReal_mul, ← leviForm_eq_complexHessian]
  exact mul_nonneg hc (hL w)

end

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsPrimeFiltrationOfIsMultiHomogIdeal
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable abbrev lexDecEq (n : ℕ) : DecidableEq (Lex (Fin n → ℕ)) := LinearOrder.toDecidableEq

attribute [local instance 2000] lexDecEq

section Lex

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}

def lexW (e : K ≃ Fin n) : (Σ k, ι k) → Lex (Fin n → ℕ) :=
  fun p => toLex (Pi.single (e p.1) 1)

theorem weight_lexW (e : K ≃ Fin n) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexW (ι := ι) e) m = toLex (fun j => ∑ i, m ⟨e.symm j, i⟩) := by
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype m (fun i c => c • lexW (ι := ι) e i) (fun i => zero_nsmul _)]
  show (∑ p, m p • (Pi.single (e p.1) 1 : Fin n → ℕ)) = fun j => ∑ i, m ⟨e.symm j, i⟩
  funext j
  rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single (e.symm j)]
  · simp [Pi.single_apply]
  · intro k _ hk
    refine Finset.sum_eq_zero fun i _ => ?_
    have hjk : j ≠ e k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [Pi.single_apply, hjk]
  · simp

theorem isMultiHomog_iff_lex (e : K ≃ Fin n) (f : MRing ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (lexW e) f (toLex (a ∘ e.symm)) := by
  constructor
  · intro h d hd
    rw [weight_lexW]
    congr 1
    funext j
    exact h d (MvPolynomial.mem_support_iff.mpr hd) (e.symm j)
  · intro h d hd k
    have h1 := h (MvPolynomial.mem_support_iff.mp hd)
    rw [weight_lexW] at h1
    obtain ⟨j, rfl⟩ := e.symm.surjective k
    exact congrFun (toLex.injective h1) j

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomog_of_mem_lex (e : K ≃ Fin n) {f : MRing ι} {m : Lex (Fin n → ℕ)}
    (h : f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) m) :
    IsMultiHomog f (fun k => ofLex m (e k)) := by
  rw [mem_weightedHomogeneousSubmodule] at h
  rw [isMultiHomog_iff_lex e]
  have hm : (fun k => ofLex m (e k)) ∘ e.symm = ofLex m := by
    funext j
    simp
  rw [hm, toLex_ofLex]
  exact h

theorem mem_lex_of_isMultiHomog (e : K ≃ Fin n) {f : MRing ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) (toLex (a ∘ e.symm)) := by
  rw [mem_weightedHomogeneousSubmodule]
  exact (isMultiHomog_iff_lex e f a).1 h

theorem isHomogeneous_lex_iff (e : K ≃ Fin n) (J : Ideal (MRing ι)) :
    J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) ↔ IsMultiHomogIdeal J := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ J).1 h
    refine ⟨Subtype.val '' S, ?_, hS⟩
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨i, hi⟩ := x.2
    exact ⟨_, isMultiHomog_of_mem_lex e hi⟩
  · rintro ⟨S, hS, rfl⟩
    apply Ideal.homogeneous_span
    intro x hx
    obtain ⟨a, ha⟩ := hS x hx
    exact ⟨_, mem_lex_of_isMultiHomog e ha⟩

end Lex

section Filtration

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    by_contra h
    exact hm (if_neg (Ne.symm h))
  simp [hm0]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem exists_colon_prime (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) (hJt : J ≠ ⊤) :
    ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∉ J ∧
      (J.colon {f}).IsPrime ∧ IsMultiHomogIdeal (J.colon {f}) := by
  let e := Fintype.equivFin K
  have hJh : J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) :=
    (isHomogeneous_lex_iff e J).2 hJ

  have hcolh : ∀ (f : MRing ι) (d : Lex (Fin (Fintype.card K) → ℕ)),
      f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) d →
      (J.colon {f}).IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) := by
    intro f d hf i g hg
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
    rw [← DirectSum.coe_decompose_mul_add_of_right_mem _ hf]
    exact hJh (i + d) hg

  let S : Set (Ideal (MRing ι)) := {P | ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∉ J ∧ P = J.colon {f}}
  have hne : S.Nonempty := by
    refine ⟨J.colon {1}, ?_⟩
    simp only [S, Set.mem_setOf_eq]
    exact ⟨1, 0, isMultiHomog_one, fun h => hJt ((Ideal.eq_top_iff_one J).2 h), rfl⟩
  obtain ⟨P, hP, hmax⟩ :=
    set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian (MRing ι) (MRing ι)) S hne
  obtain ⟨f, c, hf, hfJ, rfl⟩ := hP
  have hfm := mem_lex_of_isMultiHomog e hf
  have hPh := hcolh f _ hfm
  refine ⟨f, c, hf, hfJ, ?_, (isHomogeneous_lex_iff e _).1 hPh⟩
  apply Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem hPh
  · intro h
    apply hfJ
    have h1 : (1 : MRing ι) ∈ J.colon {f} := by rw [h]; exact Submodule.mem_top
    rwa [Submodule.mem_colon_singleton, one_smul] at h1
  · rintro x y ⟨i, hx⟩ ⟨j, hy⟩ hxy
    by_cases hxP : x ∈ J.colon {f}
    · exact Or.inl hxP
    right
    have hxf := SetLike.GradedMul.mul_mem hx hfm
    have hxfJ : x * f ∉ J := by rwa [Submodule.mem_colon_singleton, smul_eq_mul] at hxP
    have hmem : J.colon {x * f} ∈ S := by
      simp only [S, Set.mem_setOf_eq]
      exact ⟨x * f, _, isMultiHomog_of_mem_lex e hxf, hxfJ, rfl⟩
    have hle : J.colon {f} ≤ J.colon {x * f} := by
      intro g hg
      rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
      rw [← mul_assoc, mul_comm g x, mul_assoc]
      exact J.mul_mem_left x hg
    have heq : J.colon {f} = J.colon {x * f} := by
      by_contra hne'
      exact hmax _ hmem (lt_of_le_of_ne hle hne')
    rw [heq, Submodule.mem_colon_singleton, smul_eq_mul]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hxy
    rw [← mul_assoc, mul_comm y x]
    exact hxy

theorem isMultiHomogIdeal_sup_span_via_span_union {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι}
    {c : K → ℕ} (hf : IsMultiHomog f c) : IsMultiHomogIdeal (J ⊔ Ideal.span {f}) := by
  obtain ⟨S, hS, rfl⟩ := hJ
  refine ⟨S ∪ {f}, ?_, (Ideal.span_union _ _).symm⟩
  rintro g (hg | hg)
  · exact hS g hg
  · rw [Set.mem_singleton_iff.mp hg]
    exact ⟨c, hf⟩

theorem exists_primeFiltration_of_isMultiHomogIdeal (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) :
    ∃ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι) (c : Fin N → K → ℕ)
      (q : Fin N → Ideal (MRing ι)),
      F 0 = J ∧ F (Fin.last N) = ⊤ ∧ ∀ j : Fin N,
        IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc := by
  induction J using WellFoundedGT.induction
  rename_i J ih
  by_cases hJt : J = ⊤
  · exact ⟨0, fun _ => J, Fin.elim0, Fin.elim0, Fin.elim0, rfl, hJt, fun j => Fin.elim0 j⟩
  obtain ⟨f, c, hf, hfJ, hprime, hqh⟩ := exists_colon_prime J hJ hJt
  have hlt : J < J ⊔ Ideal.span {f} := lt_of_le_of_ne le_sup_left fun h =>
    hfJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨N, F, g, cc, q, hF0, hFl, hstep⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ hf)
  refine ⟨N + 1, Fin.cons J F, Fin.cons f g, Fin.cons c cc, Fin.cons (J.colon {f}) q, rfl, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ]
    exact hFl
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨by simpa using hf, ?_, by simpa using hprime, by simpa using hqh, fun g' => ?_⟩
      · simp [hF0]
      · simp [Submodule.mem_colon_singleton, smul_eq_mul]
    · simp only [← Fin.succ_castSucc, Fin.cons_succ]
      exact hstep j

end Filtration

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.TwoLeKrullDimOfRelevantPrime
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Dim

variable {R : Type*} [CommRing R]

theorem krullDim_quotient_add_one_le {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : q < p) : ringKrullDim (R ⧸ p) + 1 ≤ ringKrullDim (R ⧸ q) := by
  obtain ⟨r, hrp, hrq⟩ := SetLike.exists_of_lt h
  have hr : Ideal.Quotient.mk q r ∈ nonZeroDivisors (R ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h.le)
    (Ideal.Quotient.factor_surjective h.le) hr
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hrp)

end Dim

section Kill

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

end Kill

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

