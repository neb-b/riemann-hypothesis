module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanMapOfEvalMemOfNeZero
section
open MvPolynomial

namespace GlobalTheory

theorem mem_span_map_of_eval_mem (k : Type) [Field k] [Infinite k] (σ τ : Type)
    (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k) (hD : D ≠ 0)
    (P : MvPolynomial σ (MvPolynomial τ k))
    (hP : ∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) :
    P ∈ Submodule.span (MvPolynomial τ k)
      (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by
  classical
  let Γ : Finset (τ →₀ ℕ) := P.support.biUnion (fun m => (AddMonoidAlgebra.coeff P m).support)
  let Q : (τ →₀ ℕ) → MvPolynomial σ k := fun γ =>
    ∑ m ∈ P.support, monomial m (AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff P m) γ)
  have hQ : ∀ γ m, AddMonoidAlgebra.coeff (Q γ) m = AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff P m) γ := by
    intro γ m
    simp only [Q, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp only [notMem_support_iff.mp h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have hdec : P = ∑ γ ∈ Γ, (monomial γ (1 : k) : MvPolynomial τ k) • map (algebraMap k (MvPolynomial τ k)) (Q γ) := by
    ext m : 1
    rw [coeff_sum]
    simp only [coeff_smul, coeff_map, hQ, smul_eq_mul, MvPolynomial.algebraMap_eq]
    have : ∀ γ, (monomial γ (1 : k) : MvPolynomial τ k) * C (AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff P m) γ) = monomial γ (AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff P m) γ) := by
      intro γ; rw [mul_comm, C_mul_monomial, mul_one]
    simp only [this]
    by_cases hm : m ∈ P.support
    · conv_lhs => rw [as_sum (AddMonoidAlgebra.coeff P m)]
      apply Finset.sum_subset
      · intro γ hγ; exact Finset.mem_biUnion.mpr ⟨m, hm, hγ⟩
      · intro γ _ hγ; rw [notMem_support_iff.mp hγ, monomial_zero]
    · rw [notMem_support_iff.mp hm]
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, monomial_zero,
        Finset.sum_const_zero]
  have hevid : ∀ y : τ → k, (eval y).comp (algebraMap k (MvPolynomial τ k)) = RingHom.id k := by
    intro y; ext c; simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, eval_C, RingHom.id_apply]
  have hevP : ∀ y : τ → k, map (eval y) P =
      ∑ γ ∈ Γ, (eval y (monomial γ (1 : k) : MvPolynomial τ k)) • Q γ := by
    intro y
    conv_lhs => rw [hdec]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [smul_eq_C_mul, map_mul, map_C, map_map, hevid, map_id, smul_eq_C_mul]
  have hQM : ∀ γ ∈ Γ, Q γ ∈ M := by
    intro β hβ
    by_contra hnot
    obtain ⟨L, hLβ, hLM⟩ := Submodule.exists_le_ker_of_notMem hnot
    let R : MvPolynomial τ k := ∑ γ ∈ Γ, monomial γ (L (Q γ))
    have hR : ∀ y : τ → k, eval y R = L (map (eval y) P) := by
      intro y
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hevP, map_sum, map_sum]
      refine Finset.sum_congr rfl (fun γ _ => ?_)
      rw [map_smul, smul_eq_mul, eval_monomial, eval_monomial, mul_comm, one_mul]
    have hRD : R * D = 0 := by
      apply MvPolynomial.funext
      intro y
      rw [map_mul, map_zero]
      by_cases hy : eval y D = 0
      · rw [hy, mul_zero]
      · rw [hR, LinearMap.mem_ker.mp (hLM (hP y hy)), zero_mul]
    have hR0 : R = 0 := (mul_eq_zero.mp hRD).resolve_right hD
    have hcoef : AddMonoidAlgebra.coeff R β = L (Q β) := by
      simp only [R, coeff_sum, coeff_monomial]
      rw [Finset.sum_ite_eq', ite_eq_left hβ]
    exact hLβ (by simp only [← hcoef, hR0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply])
  suffices h : (∑ γ ∈ Γ, (monomial γ (1 : k) : MvPolynomial τ k) • map (algebraMap k (MvPolynomial τ k)) (Q γ)) ∈
      Submodule.span (MvPolynomial τ k)
        (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) by
    rwa [← hdec] at h
  refine Submodule.sum_mem _ (fun γ hγ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact ⟨Q γ, hQM γ hγ, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoCharOfMulPolyDivPow
section
open Matrix Polynomial

namespace GlobalTheory

theorem mono_char_of_mul_poly_div_pow (χ : ℂ → ℂ)
    (hmul : ∀ s t : ℂ, s ≠ 0 → t ≠ 0 → χ (s * t) = χ s * χ t) (h1 : χ 1 = 1) (N : ℕ)
    (p : Polynomial ℂ) (hp : ∀ t : ℂ, t ≠ 0 → t ^ N * χ t = p.eval t) :
    ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ t = t ^ k := by
  have hne : ∀ t : ℂ, t ≠ 0 → χ t ≠ 0 := by
    intro t ht h
    have := hmul t t⁻¹ ht (inv_ne_zero ht)
    rw [mul_inv_cancel₀ ht, h1, h, zero_mul] at this
    exact one_ne_zero this
  have hp0 : p ≠ 0 := by
    intro h
    have := hp 1 one_ne_zero
    rw [h, eval_zero, one_pow, one_mul, h1] at this
    exact one_ne_zero this
  obtain ⟨q, hpq, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  have hq : ∀ t : ℂ, q.eval t ≠ 0 := by
    intro t ht
    by_cases t0 : t = 0
    · subst t0
      apply hdvd
      rw [dvd_iff_isRoot]
      exact ht
    · have := hp t t0
      rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_zero, ht, mul_zero] at this
      exact mul_ne_zero (pow_ne_zero _ t0) (hne t t0) this
  have hdeg : q.natDegree = 0 := by
    by_contra hd
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact hq 0 (eval_zero)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root q (by
      rw [degree_eq_natDegree hq0]
      exact_mod_cast hd)
    exact hq z hz
  rw [eq_C_of_natDegree_eq_zero hdeg] at hpq
  have hc : q.coeff 0 = 1 := by
    have := hp 1 one_ne_zero
    rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_C, sub_zero, one_pow, one_pow,
      one_mul, one_mul, h1] at this
    exact this.symm
  refine ⟨(rootMultiplicity 0 p : ℤ) - N, fun t ht => ?_⟩
  have := hp t ht
  rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_C, sub_zero, hc, mul_one] at this
  rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast, eq_div_iff (pow_ne_zero _ ht), mul_comm, this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulSubOneLeOfValuation
section
namespace GlobalTheory.MulSubOneValuation

theorem mul_sub_one_le_of_valuation {K Γ : Type*} [CommRing K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} {γ : Γ} (hγ : γ ≤ 1) {A B : Matrix (Fin n) (Fin n) K}
    (hA : ∀ r s, v (A r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ)
    (hB : ∀ r s, v (B r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ) (r s : Fin n) :
    v ((A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ := by

  have hM : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  have he : (A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s =
      (A - 1) r s + (B - 1) r s + ((A - 1) * (B - 1)) r s := by
    simpa [Matrix.sub_apply, Matrix.add_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) K => M r s) hM
  rw [he, Matrix.mul_apply]
  refine v.map_add_le (v.map_add_le (hA r s) (hB r s)) (v.map_sum_le fun k _ => ?_)
  calc v ((A - 1) r k * (B - 1) k s) = v ((A - 1) r k) * v ((B - 1) k s) := map_mul v _ _
    _ ≤ γ * γ := mul_le_mul' (hA r k) (hB k s)
    _ ≤ γ := mul_le_of_le_one_right' hγ

theorem mul_sub_one_le {E : Type} [Field E] [NumberField E]
    {P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)} {n N : ℕ}
    {A B : Matrix (Fin n) (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)}
    (hA : ∀ r s : Fin n, (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) (A r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (hB : ∀ r s : Fin n, (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) (B r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (r s : Fin n) :
    (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) ((A * B) r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  have hγ : WithZero.exp (-(N : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  exact mul_sub_one_le_of_valuation Valued.v hγ hA hB r s

end GlobalTheory.MulSubOneValuation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialClearDenominatorsEval
section
namespace GlobalTheory

open MvPolynomial Finset

theorem clearDenominators {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K)
    (P D : ι → MvPolynomial τ K) :
    ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) →
      MvPolynomial.eval y M ≠ 0 ∧
      MvPolynomial.eval y G = MvPolynomial.eval y M *
        MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by
  classical
  set N := F.totalDegree
  refine ⟨∑ m ∈ F.support, C (F.coeff m) * ∏ i ∈ F.vars, (P i) ^ (m i) * (D i) ^ (N - m i),
    ∏ i ∈ F.vars, (D i) ^ N, fun y hy => ⟨?_, ?_⟩⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by rw [map_pow]; exact pow_ne_zero _ (hy i)
  · have hle : ∀ m ∈ F.support, ∀ i, m i ≤ N := fun m hm i =>
      (monomial_le_degreeOf i hm).trans (degreeOf_le_totalDegree F i)
    have hsub : ∀ m ∈ F.support, m.support ⊆ F.vars := fun m hm i hi =>
      (MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨m, hm, hi⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPolynomial.eval_eq (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F,
      map_prod, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [map_mul, eval_C, map_prod]
    rw [Finset.prod_subset (hsub m hm) (fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero])]
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow]
    have hd := hy i
    have hk := hle m hm i
    rw [div_pow, ← pow_sub_mul_pow (MvPolynomial.eval y (D i)) hk]
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDetOfRealLeFactorialMulPow
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem psd_real_quad_single (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosSemidef) (i j : Fin g)
    (hij : i ≠ j) (c : ℝ) : 0 ≤ Y i i + c * Y i j + c * Y j i + c * c * Y j j := by
  have h := hY.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j c)
  simp only [star_trivial, mulVec_add, add_dotProduct, dotProduct_add, mulVec_single,
    single_dotProduct, dotProduct_single] at h
  simp [Pi.single_apply, hij, hij.symm] at h
  linarith

theorem abs_entry_le_of_psd_le (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ)
    (hY : Y.PosSemidef) (hMY : (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef) (i j : Fin g) :
    |Y i j| ≤ M := by
  have hdiag : ∀ k, Y k k ≤ M := by
    intro k
    have := hMY.diag_nonneg (i := k)
    simp at this
    linarith
  have hsym : Y j i = Y i j := by
    have := congrFun (congrFun hY.isHermitian j) i
    simpa [conjTranspose_apply] using this.symm
  by_cases hij : i = j
  · subst hij
    rw [abs_of_nonneg (hY.diag_nonneg (i := i))]
    exact hdiag i
  · have h1 := psd_real_quad_single g Y hY i j hij 1
    have h2 := psd_real_quad_single g Y hY i j hij (-1)
    have hi := hdiag i
    have hj := hdiag j
    rw [hsym] at h1 h2
    rw [abs_le]
    constructor <;> nlinarith

theorem det_map_ofReal_norm_le : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef →
    (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef →
    ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by
  intro g Y M _ hY hMY
  have hmap : (Y.map Complex.ofReal).det = ((Y.det : ℝ) : ℂ) := by
    have := RingHom.map_det Complex.ofRealHom Y
    exact this.symm
  rw [hmap, Complex.norm_real, Real.norm_eq_abs]
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := M) (A := Y)
    (fun i j => abs_entry_le_of_psd_le g Y M hY hMY i j)
  simpa [Fintype.card_fin, nsmul_eq_mul] using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubPowLe
section
namespace GlobalTheory.NormEvalSubBound

open Polynomial

section
variable {C : Type} [NormedField C] [IsUltrametricDist C]

lemma norm_pow_sub_pow_le {y a : C} (hy : ‖y‖ ≤ 1) (ha : ‖a‖ ≤ 1) (i : ℕ) :
    ‖y ^ i - a ^ i‖ ≤ ‖y - a‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : y ^ (i + 1) - a ^ (i + 1) = y * (y ^ i - a ^ i) + (y - a) * a ^ i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖y‖ * ‖y ^ i - a ^ i‖ ≤ 1 * ‖y - a‖ :=
            mul_le_mul hy ih (norm_nonneg _) zero_le_one
        _ = ‖y - a‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖y - a‖ * ‖a‖ ^ i ≤ ‖y - a‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ha) (norm_nonneg _)
        _ = ‖y - a‖ := mul_one _

lemma norm_eval_sub_le (Q : C[X]) (hc : ∀ i, ‖Q.coeff i‖ ≤ 1) {y a : C} (hy : ‖y‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) : ‖Q.eval y - Q.eval a‖ ≤ ‖y - a‖ := by
  rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖Q.coeff i‖ * ‖y ^ i - a ^ i‖ ≤ 1 * ‖y - a‖ :=
        mul_le_mul (hc i) (norm_pow_sub_pow_le hy ha i) (norm_nonneg _) zero_le_one
    _ = ‖y - a‖ := one_mul _

lemma norm_le_one_of_root (Q : C[X]) (hm : Q.Monic) (hc : ∀ i, ‖Q.coeff i‖ ≤ 1) {a : C}
    (h : Q.eval a = 0) : ‖a‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  set n := Q.natDegree
  have hpos : 0 < ‖a‖ := lt_trans zero_lt_one hlt
  have hs : ‖∑ i ∈ Finset.range n, Q.coeff i * a ^ i‖ ≤ ‖a‖ ^ n / ‖a‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    have hi' : i + 1 ≤ n := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    calc ‖Q.coeff i‖ * ‖a‖ ^ i * ‖a‖ ≤ 1 * ‖a‖ ^ i * ‖a‖ := by
          gcongr
          exact hc i
      _ = ‖a‖ ^ (i + 1) := by ring
      _ ≤ ‖a‖ ^ n := pow_le_pow_right₀ hlt.le hi'
  have hlt2 : ‖a‖ ^ n / ‖a‖ < ‖a‖ ^ n := div_lt_self (by positivity) hlt
  have he : Q.eval a = a ^ n + ∑ i ∈ Finset.range n, Q.coeff i * a ^ i := by
    conv_lhs => rw [hm.as_sum]
    simp [eval_finsetSum, n]
  rw [h] at he
  have : a ^ n = -∑ i ∈ Finset.range n, Q.coeff i * a ^ i := by linear_combination -he
  have h3 : ‖a‖ ^ n = ‖∑ i ∈ Finset.range n, Q.coeff i * a ^ i‖ := by
    rw [← norm_pow, this, norm_neg]
  linarith
end

theorem main_theorem : (let d1 : {C : Type} → [inst : NormedField C] → [IsUltrametricDist C] → Subfield C → Subring C := @(fun {C : Type} [NormedField C] [IsUltrametricDist C] (F : Subfield C) ↦ Subfield.toSubring F ⊓ Valuation.integer NormedField.valuation); ∀ {C : Type} [inst : NormedField C] [inst_1 : IsUltrametricDist C] {F : Subfield C} [IsAlgClosed C] [inst_3 : IsLocalRing ↥(d1 F)], (∀ (x : C), ‖x‖ ≤ (1 : ℝ) → ∃ y ∈ F, ‖x - y‖ < (1 : ℝ)) → IsAlgClosed (IsLocalRing.ResidueField ↥(d1 F))) := by
  intro d1 C _ _ F _ _ hdense
  have mem : ∀ x : C, x ∈ d1 F ↔ x ∈ F ∧ ‖x‖ ≤ 1 := by
    intro x
    simp only [d1, Subring.mem_inf, Subfield.mem_toSubring, Valuation.mem_integer_iff,
      NormedField.valuation_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by exact_mod_cast h2⟩
  apply IsAlgClosed.of_exists_root
  intro p hmon hirr
  have hlift : p ∈ lifts (IsLocalRing.residue (d1 F)) :=
    (mem_lifts p).mpr (Polynomial.map_surjective _ IsLocalRing.residue_surjective p)
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ := lifts_and_degree_eq_and_monic hlift hmon
  set Q : C[X] := q.map (d1 F).subtype with hQ
  have hQc : ∀ i, ‖Q.coeff i‖ ≤ 1 := fun i => by
    rw [hQ, coeff_map]; exact ((mem _).mp (q.coeff i).2).2
  have hQm : Q.Monic := hqmon.map _
  have hQdeg : Q.degree ≠ 0 := by
    rw [hQ, degree_map_eq_of_injective (Subring.subtype_injective _), hqdeg]
    exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root Q hQdeg
  have ha1 : ‖a‖ ≤ 1 := norm_le_one_of_root Q hQm hQc ha
  obtain ⟨y, hyF, hya⟩ := hdense a ha1
  have hy1 : ‖y‖ ≤ 1 := by
    have : y = a - (a - y) := by ring
    rw [this]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha1 ?_)
    rw [norm_neg]; exact hya.le
  let y' : d1 F := ⟨y, (mem y).mpr ⟨hyF, hy1⟩⟩
  refine ⟨IsLocalRing.residue _ y', ?_⟩
  rw [← hqmap, eval_map, eval₂_hom, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hval : ((q.eval y' : d1 F) : C) = Q.eval y := by
    rw [hQ, eval_map]
    exact (eval₂_hom (d1 F).subtype y').symm
  have hn : ‖((q.eval y' : d1 F) : C)‖ < 1 := by
    rw [hval]
    have : Q.eval y = Q.eval y - Q.eval a := by rw [IsRoot.def.mp ha, sub_zero]
    rw [this]
    refine lt_of_le_of_lt (norm_eval_sub_le Q hQc hy1 ha1) ?_
    rwa [norm_sub_rev]
  obtain ⟨v, huv⟩ := hu.exists_right_inv
  have h1 : ((q.eval y' : d1 F) : C) * (v : C) = 1 := by
    have := congrArg Subtype.val huv
    simpa using this
  have hv : ‖(v : C)‖ ≤ 1 := ((mem _).mp v.2).2
  have : ‖((q.eval y' : d1 F) : C) * (v : C)‖ < 1 := by
    rw [norm_mul]
    calc _ ≤ ‖((q.eval y' : d1 F) : C)‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hn
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

end GlobalTheory.NormEvalSubBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodicLeftHalfPlaneShiftNonnegOfImPos
section
open Complex MeasureTheory

namespace GlobalTheory

theorem periodic_strip_shift_nonneg (c : ℝ) (f : ℂ → ℂ) (m : ℤ)
    (hf : DifferentiableOn ℂ f {s : ℂ | s.re < c})
    (hper : ∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m)
    (hpos : ∀ s : ℂ, s.re < c → 0 < (f s).im) : 0 ≤ m := by
  have hcont : ContinuousOn f {s : ℂ | s.re < c} := hf.continuousOn
  have hvert : ∀ x : ℝ, x < c → IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume 0 (2 * Real.pi) := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    refine hcont.comp (by fun_prop) ?_
    intro y _
    simp [hx]
  have hhor : ∀ (x₁ x₂ : ℝ), x₁ ≤ x₂ → x₂ < c → IntervalIntegrable (fun x : ℝ => f (x : ℂ)) volume x₁ x₂ := by
    intro x₁ x₂ h12 h2
    apply ContinuousOn.intervalIntegrable
    refine hcont.comp (by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le h12] at hx
    simp only [Set.mem_setOf_eq, ofReal_re]
    linarith [hx.2]
  have hVim : ∀ x : ℝ, x < c → 0 ≤ (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x + y * I)).im := by
    intro x hx
    have h2pi : (0:ℝ) ≤ 2 * Real.pi := by positivity
    have hc := Complex.imCLM.intervalIntegral_comp_comm (hvert x hx)
    simp only [Complex.imCLM_apply] at hc
    rw [← hc]
    apply intervalIntegral.integral_nonneg h2pi
    intro y _
    exact (hpos _ (by simp [hx])).le
  have key : ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → x₂ < c →
      (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₁ + y * I)).im
        = (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₂ + y * I)).im + m * (x₂ - x₁) := by
    intro x₁ x₂ h12 h2c
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (x₁ : ℂ)
      ((x₂ : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * I) ?_
    · simp only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
        mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add, ofReal_zero] at hrect
      have htop : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I))
          = (∫ x : ℝ in x₁..x₂, f (x : ℂ)) + (m : ℂ) * ((x₂ - x₁ : ℝ) : ℂ) := by
        have hc : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I))
            = ∫ x : ℝ in x₁..x₂, (f (x : ℂ) + m) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le h12] at hx
          have hxc : (x : ℂ).re < c := by simp; linarith [hx.2]
          simp only
          rw [← hper _ hxc]
          congr 1
          push_cast
          ring
        rw [hc, intervalIntegral.integral_add (hhor x₁ x₂ h12 h2c) intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp [mul_comm]
      rw [htop] at hrect
      have hre := congrArg Complex.re hrect
      simp at hre
      linarith
    · apply hf.mono
      intro z hz
      rw [Complex.mem_reProdIm] at hz
      simp only [ofReal_re, add_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at hz
      rw [Set.uIcc_of_le h12] at hz
      show z.re < c
      linarith [hz.1.2]
  by_contra hm
  push_neg at hm
  have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
  set a := (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f ((c - 1 : ℝ) + y * I)).im with ha
  have ha0 : 0 ≤ a := hVim (c - 1) (by linarith)
  have h1 := key (c - 1 - (a + 1)) (c - 1) (by linarith) (by linarith)
  have h2 := hVim (c - 1 - (a + 1)) (by linarith)
  rw [h1] at h2
  nlinarith [mul_le_mul_of_nonneg_right hm1 (by linarith : (0:ℝ) ≤ a + 1)]

end GlobalTheory
end

