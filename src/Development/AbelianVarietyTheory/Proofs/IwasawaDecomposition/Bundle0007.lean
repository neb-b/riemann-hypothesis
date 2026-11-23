module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemPairingEqSingleNonradical
section
open Matrix

namespace GlobalTheory

theorem dualV_pairing_exists : ∀ (r g rk : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)) (ε : Fin g → Fin r → ℚ), Mqᵀ = -Mq → LinearIndependent ℚ ε → (∀ i : Fin g, i.val < rk → ∀ w ∈ V, ε i ⬝ᵥ Mq *ᵥ w = 0) → (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → y ∈ Submodule.span ℚ (ε '' {i | i.val < rk})) → ∀ j : Fin g, rk ≤ j.val → ∃ x ∈ V, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0 := by
  intro r g rk Mq V ε hskew hli horth hperp j hj
  have skew : ∀ x y : Fin r → ℚ, x ⬝ᵥ Mq *ᵥ y = -(y ⬝ᵥ Mq *ᵥ x) := by
    intro x y
    rw [dotProduct_mulVec x Mq y, dotProduct_comm y, ← vecMul_transpose, hskew, vecMul_neg,
      neg_dotProduct, neg_neg]
  let Φ : (Fin r → ℚ) →ₗ[ℚ] (Fin g → ℚ) :=
    { toFun := fun x i => x ⬝ᵥ Mq *ᵥ ε i
      map_add' := by intro x y; funext i; simp [add_dotProduct]
      map_smul' := by intro c x; funext i; simp [smul_dotProduct] }
  have hΦ : ∀ x i, Φ x i = x ⬝ᵥ Mq *ᵥ ε i := fun _ _ => rfl
  suffices h : Pi.single j (1 : ℚ) ∈ V.map Φ by
    obtain ⟨x, hx, hxe⟩ := h
    refine ⟨x, hx, fun i => ?_⟩
    rw [← hΦ, hxe, Pi.single_apply]
  by_contra hnot
  obtain ⟨f, hfj, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hf0 : ∀ s ∈ V.map Φ, f s = 0 := by
    intro s hs
    have : f s ∈ (V.map Φ).map f := Submodule.mem_map_of_mem hs
    rw [hfS] at this
    simpa using this
  set a : Fin g → ℚ := fun i => f (Pi.single i 1) with ha
  have hfsum : ∀ s : Fin g → ℚ, f s = ∑ i, a i * s i := by
    intro s
    conv_lhs => rw [pi_eq_sum_univ s]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    congr 1
    simp only [ha]
    congr 1
    funext k
    simp [Pi.single_apply, eq_comm]
  set a' : Fin g → ℚ := fun i => if rk ≤ i.val then a i else 0 with ha'
  have hΦlow : ∀ w ∈ V, ∀ i : Fin g, i.val < rk → Φ w i = 0 := by
    intro w hw i hi
    rw [hΦ, skew, horth i hi w hw, neg_zero]
  have hsum' : ∀ w ∈ V, ∑ i, a' i * Φ w i = 0 := by
    intro w hw
    have h1 : ∑ i, a' i * Φ w i = ∑ i, a i * Φ w i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : rk ≤ i.val
      · simp [ha', hi]
      · simp [ha', hi, hΦlow w hw i (by omega)]
    rw [h1, ← hfsum]
    exact hf0 _ (Submodule.mem_map_of_mem hw)
  set e : Fin r → ℚ := ∑ i, a' i • ε i with he
  have heV : ∀ w ∈ V, e ⬝ᵥ Mq *ᵥ w = 0 := by
    intro w hw
    rw [he, sum_dotProduct]
    have : ∑ i, (a' i • ε i) ⬝ᵥ Mq *ᵥ w = -∑ i, a' i * Φ w i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_dotProduct, smul_eq_mul, hΦ, skew w, mul_neg, neg_neg]
    rw [this, hsum' w hw, neg_zero]
  have hespan := hperp e heV
  rw [Finsupp.mem_span_image_iff_linearCombination] at hespan
  obtain ⟨l, hl, hc⟩ := hespan
  let c' : Fin g → ℚ := fun i => l i
  have hc' : ∑ i, c' i • ε i = e := by
    rw [← hc, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  have hzero : ∑ i, (a' i - c' i) • ε i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hc', he, sub_self]
  have := Fintype.linearIndependent_iff.mp hli _ hzero j
  have hcj : c' j = 0 := (Finsupp.mem_supported' ℚ l).mp hl j (by simp; omega)
  have haj : a' j = a j := by simp [ha', hj]
  rw [hcj, haj, sub_zero] at this
  exact hfj this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulEqMulDiagonal
section
open IsDedekindDomain NumberField

namespace GlobalTheory.SmithBetween

open Matrix


open IsDedekindDomain NumberField in
open Matrix in
theorem _root_.GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n R) (hM : M.det ≠ 0) :
    ∃ P Q : Matrix n n R, IsUnit P.det ∧ IsUnit Q.det ∧ ∃ c : n → R,
      M * Q = P * Matrix.diagonal c := by
  have hinj : Function.Injective M.mulVecLin := Matrix.mulVec_injective_of_det_ne_zero hM
  obtain ⟨m, snf⟩ := Submodule.smithNormalForm (Pi.basisFun R n) (LinearMap.range M.mulVecLin)
  have hm : m = Fintype.card n := by
    have h1 := Module.finrank_eq_card_basis snf.bN
    rw [LinearMap.finrank_range_of_inj hinj] at h1
    simpa using h1.symm
  have hf : Function.Bijective snf.f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨snf.f.injective, by simp [hm]⟩
  let g : Fin m ≃ n := Equiv.ofBijective snf.f hf
  let eN := LinearEquiv.ofInjective M.mulVecLin hinj
  let bQ : Module.Basis n R (n → R) := (snf.bN.map eN.symm).reindex g
  letI := (Pi.basisFun R n).invertibleToMatrix snf.bM
  letI := (Pi.basisFun R n).invertibleToMatrix bQ
  refine ⟨(Pi.basisFun R n).toMatrix snf.bM, (Pi.basisFun R n).toMatrix bQ, ?_, ?_,
    fun j => snf.a (g.symm j), ?_⟩
  · exact isUnit_det_of_invertible _
  · exact isUnit_det_of_invertible _
  · ext i j
    have key : M *ᵥ bQ j = snf.a (g.symm j) • snf.bM j := by
      have h2 := snf.snf (g.symm j)
      have h3 : snf.f (g.symm j) = j := g.apply_symm_apply j
      rw [h3] at h2
      rw [← h2]
      simp only [bQ, Module.Basis.reindex_apply, Module.Basis.map_apply]
      have h4 : ((eN (eN.symm (snf.bN (g.symm j)))) : n → R) =
          M.mulVecLin (eN.symm (snf.bN (g.symm j))) := rfl
      rw [LinearEquiv.apply_symm_apply] at h4
      rw [← Matrix.mulVecLin_apply, ← h4]
    have := congrFun key i
    simp only [Matrix.mul_diagonal, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [Matrix.mul_apply]
    simp [Matrix.mulVec, dotProduct] at this
    simpa [mul_comm, Module.Basis.toMatrix_apply] using this

open IsDedekindDomain NumberField in
open Matrix in
theorem _root_.GlobalTheory.SmithBetween.smith_between (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (M M' : Matrix (Fin n) (Fin n) R)
    (hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R)) (hdet : Associated M.det (ϖ ^ k)) :
    ∃ P Q : Matrix (Fin n) (Fin n) R, IsUnit P.det ∧ IsUnit Q.det ∧
      M * Q = P * Matrix.diagonal (fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ) := by
  classical
  have hM0 : M.det ≠ 0 := by
    rw [hdet.ne_zero_iff]; exact pow_ne_zero _ hϖ.ne_zero
  obtain ⟨P, Q, hP, hQ, c, hMQ⟩ := _root_.GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal M hM0
  have hdvd : ∀ j, c j ∣ ϖ := by
    intro j
    have hD : Matrix.diagonal c = P⁻¹ * M * Q := by
      rw [Matrix.mul_assoc, hMQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
    have hX : Matrix.diagonal c * (Q⁻¹ * M' * P) = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
      rw [hD]
      calc P⁻¹ * M * Q * (Q⁻¹ * M' * P) = P⁻¹ * (M * (Q * Q⁻¹) * M') * P := by
            simp only [Matrix.mul_assoc]
        _ = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
            rw [Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, hMM, Matrix.mul_smul, Matrix.mul_one,
              Matrix.smul_mul, Matrix.nonsing_inv_mul _ hP]
    have := congrFun (congrFun hX j) j
    simp only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one] at this
    exact ⟨_, this.symm⟩
  let d : Fin n → R := fun j => if IsUnit (c j) then 1 else ϖ
  have hu : ∀ j, ∃ u : Rˣ, c j = d j * u := by
    intro j
    by_cases h : IsUnit (c j)
    · exact ⟨h.unit, by simp [d, h]⟩
    · obtain ⟨b, hb⟩ := hdvd j
      rcases hϖ.isUnit_or_isUnit hb with h' | h'
      · exact absurd h' h
      · refine ⟨h'.unit⁻¹, ?_⟩
        simp only [d, h, if_false, hb]
        rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
  choose u hu using hu

  set s := (Finset.univ.filter fun j => ¬IsUnit (c j)).card with hs
  have hprod : ∏ j, d j = ϖ ^ s := by
    simp only [d]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have hsk : s = k := by
    have h1 : M.det * Q.det = P.det * ∏ j, c j := by
      rw [← Matrix.det_mul, hMQ, Matrix.det_mul, Matrix.det_diagonal]
    have h2 : ∏ j, c j = ϖ ^ s * ∏ j, (u j : R) := by
      rw [← hprod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => hu j
    have h3 : Associated (ϖ ^ s) M.det := by
      have hA : Associated (M.det * Q.det) M.det := (associated_mul_isUnit_left_iff hQ).2 (Associated.refl _)
      have hv : IsUnit (P.det * ∏ j, (u j : R)) :=
        hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)
      have hB : Associated (ϖ ^ s) (P.det * ∏ j, c j) := by
        rw [h2, mul_left_comm]
        exact associated_mul_unit_right _ _ hv
      rw [← h1] at hB
      exact hB.trans hA
    have h4 : Associated (ϖ ^ s) (ϖ ^ k) := h3.trans hdet
    exact le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.dvd)
      ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.symm.dvd)
  let P' := P * Matrix.diagonal fun j => (u j : R)
  have hP' : IsUnit P'.det := by
    simp only [P', Matrix.det_mul, Matrix.det_diagonal]
    exact hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)
  have hMQ' : M * Q = P' * Matrix.diagonal d := by
    rw [hMQ, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext j
    rw [hu j, mul_comm]

  have hcard1 : Fintype.card {j // ¬IsUnit (c j)} = Fintype.card {i : Fin n // ¬i.1 < n - k} := by
    rw [Fintype.card_subtype, ← hs, hsk, Fintype.card_subtype_compl, Fintype.card_subtype,
      Fin.card_filter_val_lt, Fintype.card_fin]
    omega
  have hcard0 : Fintype.card {j // IsUnit (c j)} = Fintype.card {i : Fin n // i.1 < n - k} := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun j => IsUnit (c j))
    rw [Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt]
    rw [← hs, hsk, Finset.card_univ, Fintype.card_fin] at h
    omega
  let τ : Equiv.Perm (Fin n) :=
    Equiv.subtypeCongr (Fintype.equivOfCardEq hcard0) (Fintype.equivOfCardEq hcard1)
  have hτ : ∀ j, (τ j).1 < n - k ↔ IsUnit (c j) := by
    intro j
    by_cases h : IsUnit (c j)
    · have e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inl ⟨j, h⟩ :=
        Equiv.sumCompl_symm_apply_of_pos (p := fun x => IsUnit (c x)) (a := j) h
      simp only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inl,
        Equiv.sumCompl_apply_inl, h, iff_true]
      exact (Fintype.equivOfCardEq hcard0 ⟨j, h⟩).2
    · have e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inr ⟨j, h⟩ :=
        Equiv.sumCompl_symm_apply_of_neg (p := fun x => IsUnit (c x)) (a := j) h
      simp only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inr,
        Equiv.sumCompl_apply_inr, h, iff_false]
      exact (Fintype.equivOfCardEq hcard1 ⟨j, h⟩).2
  have hsign : ∀ A : Matrix (Fin n) (Fin n) R, IsUnit A.det → IsUnit (A.submatrix id τ.symm).det := by
    intro A hA
    rw [Matrix.det_permute']
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ.symm) with h | h <;> simp [h, hA]
  refine ⟨P'.submatrix id τ.symm, Q.submatrix id τ.symm, hsign P' hP', hsign Q hQ, ?_⟩
  have h1 : M * Q.submatrix id τ.symm = (M * Q).submatrix id τ.symm := by
    ext i j; simp [Matrix.mul_apply]
  rw [h1, hMQ', ← Matrix.submatrix_mul_equiv P' (Matrix.diagonal d) id τ.symm τ.symm,
    Matrix.submatrix_diagonal_equiv]
  congr 2
  funext i
  have := hτ (τ.symm i)
  rw [Equiv.apply_symm_apply] at this
  simp only [Function.comp_apply, d]
  by_cases hi : i.1 < n - k
  · simp [hi, this.1 hi]
  · simp [hi, mt this.2 hi]

end GlobalTheory.SmithBetween
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulEqInteger
section
universe u_1 u_2

namespace GlobalTheory.NatMulIntegerMultiple

open NumberField

theorem exists_nat_mul_eq_integer {K : Type*} [Field K] [NumberField K] (k : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, (n : K) * k = algebraMap (𝓞 K) K a := by
  have halg : IsAlgebraic ℤ k :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, by rintro rfl; exact hy rfl, ⟨(n : K) * k, ?_⟩, rfl⟩
    have : (n : K) * k = (n : ℤ) • k := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [this]; exact hint
  · refine ⟨n, by rintro rfl; exact hy rfl, ⟨(n : K) * k, ?_⟩, rfl⟩
    have : (n : K) * k = -((-(n : ℤ)) • k) := by rw [zsmul_eq_mul]; push_cast; ring
    rw [this]; exact hint.neg

theorem exists_nsmul_mem {K : Type*} {V : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) :
    ∀ x ∈ Submodule.span K (L : Set V), ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, one_ne_zero, by simpa using h⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    have e1 : (m * n) • x = n • (m • x) := by rw [mul_nsmul]
    have e2 : (m * n) • y = m • (n • y) := by rw [mul_comm, mul_nsmul]
    rw [e1, e2]
    exact L.add_mem (L.nsmul_mem hmx n) (L.nsmul_mem hny m)
  | smul c x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, a, ha⟩ := exists_nat_mul_eq_integer c
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have : (m * n) • (c • x) = a • (n • x) := by
      calc (m * n) • (c • x) = ((m : K) * c) • (n • x) := by
            rw [← Nat.cast_smul_eq_nsmul K (m * n), ← Nat.cast_smul_eq_nsmul K n, smul_smul, smul_smul]
            push_cast; ring_nf
        _ = algebraMap (𝓞 K) K a • (n • x) := by rw [ha]
        _ = a • (n • x) := algebraMap_smul K a (n • x)
    rw [this]; exact L.smul_mem a hnx

theorem main : ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    ∀ x ∈ Submodule.span K (↑L : Set V), ∃ (n : ℕ), n ≠ (0 : ℕ) ∧ n • x ∈ L :=
  fun L => exists_nsmul_mem L

end GlobalTheory.NatMulIntegerMultiple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulIntegral
section
namespace GlobalTheory.NatMulIntegralExists

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
  have hz : IsAlgebraic ℤ a := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ a)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact hint.neg

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)),
    Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤ →
    ∀ (w : Fin r → E), ∃ (k : ℕ), (0 : ℕ) < k ∧ (↑k : E) • w ∈ Λ := by
  intro E _ _ r Λ hspan w
  have hw : w ∈ Submodule.span E (↑Λ : Set (Fin r → E)) := by rw [hspan]; trivial

  have hnat : ∀ (n : ℕ) (v : Fin r → E), v ∈ Λ → (n : E) • v ∈ Λ := by
    intro n v hv
    rw [Nat.cast_smul_eq_nsmul]
    exact Λ.nsmul_mem hv n
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k₁, hk₁, h₁⟩ := hx
    obtain ⟨k₂, hk₂, h₂⟩ := hy
    refine ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_⟩
    have e : ((k₁ * k₂ : ℕ) : E) • (x + y) = (k₂ : E) • ((k₁ : E) • x) + (k₁ : E) • ((k₂ : E) • y) := by
      rw [smul_add, smul_smul, smul_smul]; push_cast; ring_nf
    rw [e]
    exact Λ.add_mem (hnat _ _ h₁) (hnat _ _ h₂)
  | smul a x _ hx =>
    obtain ⟨k, hk, h⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_nat_mul_integral a
    refine ⟨d * k, Nat.mul_pos hd hk, ?_⟩
    let c : NumberField.RingOfIntegers E := ⟨(d : E) * a, hint⟩
    have e : ((d * k : ℕ) : E) • (a • x) = c • ((k : E) • x) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Algebra.smul_def]
      change _ = ((d : E) * a) * _
      push_cast; ring
    rw [e]
    exact Λ.smul_mem c h

end GlobalTheory.NatMulIntegralExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulIntegralAlt
section
namespace GlobalTheory.NatSmulMemIntegral

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ k : ℕ, k ≠ 0 ∧ ∃ b : RingOfIntegers E, (b : E) = (k : E) * a := by

  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have hi : IsIntegral ℤ (y • a) := hy a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with hpos | hneg
  · refine ⟨⟨y • a, hi⟩, ?_⟩
    change y • a = _
    rw [zsmul_eq_mul]
    congr 1
    rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]
  · refine ⟨-⟨y • a, hi⟩, ?_⟩
    change -(y • a) = _
    rw [zsmul_eq_mul, ← neg_mul]
    congr 1
    rw [Nat.cast_natAbs, abs_of_nonpos (by omega), Int.cast_neg]

theorem exists_nat_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E))
    (h : Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ (m : ℕ), m ≠ (0 : ℕ) ∧ (↑m : E) • y ∈ Λ := by
  have hy : y ∈ Submodule.span E (↑Λ : Set (Fin n → E)) := by rw [h]; exact Submodule.mem_top
  simp only [Nat.cast_smul_eq_nsmul]
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hz
    refine ⟨m₂ * m₁, mul_ne_zero hm₂ hm₁, ?_⟩
    have ex : (m₂ * m₁) • x = m₂ • (m₁ • x) := by rw [mul_smul]
    have ez : (m₂ * m₁) • z = m₁ • (m₂ • z) := by rw [mul_comm, mul_smul]
    rw [smul_add, ex, ez]
    exact Λ.add_mem (Λ.nsmul_mem h₁ m₂) (Λ.nsmul_mem h₂ m₁)
  | smul c x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨k, hk, b, hb⟩ := exists_nat_mul_integral c
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    have hbx : b • (m • x) ∈ Λ := Λ.smul_mem b hmx
    convert hbx using 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
    rw [Algebra.smul_def, show (algebraMap (RingOfIntegers E) E b) = (b : E) from rfl, hb]
    simp only [Pi.mul_apply, Pi.natCast_apply, Nat.cast_mul]
    ring

end GlobalTheory.NatSmulMemIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroSmulMem
section
namespace GlobalTheory.NonzeroSmulMem

open NumberField

theorem exists_ne_zero_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {M : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hay
    · rw [mul_smul]
      exact M.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨p, q, hq, hc⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap (𝓞 K) K q ≠ 0 := by
      intro h
      exact hq0 ((IsFractionRing.injective (𝓞 K) K) (by rw [h, map_zero]))
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h1 : q • (c • y) = p • y := by
      rw [← algebraMap_smul K q, ← algebraMap_smul K p, smul_smul, ← hc,
        mul_div_cancel₀ _ hqK]
    rw [mul_smul, h1, smul_smul, mul_comm, mul_smul]
    exact M.smul_mem p hay

end GlobalTheory.NonzeroSmulMem
end

