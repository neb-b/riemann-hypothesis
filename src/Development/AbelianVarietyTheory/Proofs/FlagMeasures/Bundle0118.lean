module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0107

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetNotGG
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.WUnfold

variable {k r : ℕ}

theorem mul_mem_GG_iff {s x : Mat k r} (hs : s ∈ GG k r) : s * x ∈ GG k r ↔ x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * Hpk k r * x := by
    rw [Matrix.conjTranspose_mul]
    calc xᴴ * sᴴ * Hpk k r * (s * x) = xᴴ * (sᴴ * Hpk k r * s) * x := by
          simp only [Matrix.mul_assoc]
      _ = xᴴ * Hpk k r * x := by rw [hs']
  show (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r ↔ xᴴ * Hpk k r * x = Hpk k r
  rw [this]

theorem Sset_subset (z : Fin (2 * r + k + 1) → ℂ) : Sset k r z ⊆ GG k r := by
  rintro s ⟨h, hh, m, hm, rfl⟩
  exact (mul_mem_GG_iff hh.1).2 hm.1

theorem measurableSet_not_GG : MeasurableSet {x : Mt k r | Matrix.of x ∉ GG k r} := by
  have hc : IsClosed {x : Mat k r | xᴴ * Hpk k r * x = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hc' : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := hc
  exact hc'.measurableSet.compl

theorem ae_mem_GG {z : Fin (2 * r + k + 1) → ℂ} {μG μS ν : Measure (Mt k r)}
    (hG : IsHaarOn (GG k r) μG) (hS : IsHaarOn (Sset k r z) μS) (hq : IsQuotMeas μG μS ν) :
    ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := by
  set U : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hU
  have hUm : MeasurableSet U := measurableSet_not_GG
  have haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := hS.2.2.1
  have h1 := hq (U.indicator 1) (measurable_const.indicator hUm)
  rw [lintegral_indicator_one hUm, hG.2.2.1] at h1
  have h2 : ∫⁻ x, U.indicator (fun _ => μS Set.univ) x ∂ν ≤ 0 := by
    rw [h1]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine lintegral_mono_ae (haeS.mono fun s hs => ?_)
      have : (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∈ U := fun h =>
        hx ((mul_mem_GG_iff (Sset_subset z hs)).1 h)
      rw [Set.indicator_of_mem this]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  rw [lintegral_indicator_const hUm, nonpos_iff_eq_zero, mul_eq_zero] at h2
  rcases h2 with h | h
  · exact absurd (Measure.measure_univ_eq_zero.1 h) hS.2.1
  · exact h

end GlobalTheory.SgInf.WUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
section
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped Classical

namespace GlobalTheory.LoopVol

theorem measurePreserving_affine {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (hM : M.det = 1) (b : ι → ℂ) :
    MeasurePreserving (fun c : ι → ℂ => M *ᵥ c + b) volume volume := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' M).restrictScalars ℝ
  have hdet : LinearMap.det f = 1 := by
    simp only [f, LinearMap.det_restrictScalars, LinearMap.det_toLin', hM, map_one]
  have hfun : (f : (ι → ℂ) → ι → ℂ) = fun c => M *ᵥ c := by
    funext c
    simp [f, Matrix.toLin'_apply]
  have hlin : MeasurePreserving (fun c : ι → ℂ => M *ᵥ c) volume volume := by
    rw [← hfun]
    refine ⟨(LinearMap.continuous_of_finiteDimensional f).measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  exact (measurePreserving_add_right volume b).comp hlin

variable {N : ℕ}

theorem ofRoots_eq (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2) (c : R → ℂ) (i j : Fin N) :
    ofRoots R c i j = (1 : Matrix (Fin N) (Fin N) ℂ) i j + ∑ q : R, if q.1 = (i, j) then c q else 0 := by
  simp only [ofRoots]
  by_cases h : (i, j) ∈ R
  · rw [dite_eq_left h, Matrix.one_apply_ne (hR _ h).ne, zero_add, Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro h'
      exact hq (Subtype.ext h')
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [dite_eq_right h, Finset.sum_eq_zero, add_zero, Matrix.one_apply]
    intro q _
    rw [if_neg]
    intro h'
    apply h
    rw [← h']
    exact q.2

theorem det_two_sided (R : Finset (Fin N × Fin N)) (a b : Matrix (Fin N) (Fin N) ℂ) (ha : IsUpUni a)
    (hb : IsUpUni b) : (Matrix.of fun q q' : R => a q.1.1 q'.1.1 * b q'.1.2 q.1.2).det = 1 := by
  let key : R → Fin N ×ₗ (Fin N)ᵒᵈ := fun q => toLex (q.1.1, OrderDual.toDual q.1.2)
  have hinj : Function.Injective key := by
    intro x y h
    simp only [key, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  let e := Equiv.ofInjective key hinj
  rw [← Matrix.det_reindex_self e, Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, (ha _ _).2 rfl,
      (hb _ _).2 rfl, mul_one]
  · intro i j hlt
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
    have hk : key (e.symm j) < key (e.symm i) := by
      simp only [e, Equiv.apply_ofInjective_symm]
      exact hlt
    simp only [key, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual] at hk
    rcases hk with h1 | ⟨-, h2⟩
    · rw [(ha _ _).1 h1, zero_mul]
    · rw [(hb _ _).1 h2, mul_zero]

theorem measurePreserving_mul (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2)
    (a b : Matrix (Fin N) (Fin N) ℂ) (ha : IsUpUni a) (hb : IsUpUni b) :
    MeasurePreserving (fun (c : R → ℂ) (q : R) => (a * ofRoots R c * b) q.1.1 q.1.2) volume volume := by
  have hent : ∀ (c : R → ℂ) (x y : Fin N),
      (a * ofRoots R c * b) x y = ∑ q : R, a x q.1.1 * b q.1.2 y * c q + (a * b) x y := by
    intro c x y
    have hO : ofRoots R c = 1 + ∑ q : R, c q • Matrix.of (fun i j => if q.1 = (i, j) then (1 : ℂ) else 0) := by
      ext i j
      rw [ofRoots_eq R hR c i j, Matrix.add_apply, Matrix.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [hO, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.add_apply, add_comm, Finset.mul_sum,
      Finset.sum_mul, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_comm (c q)]
    congr 1
    simp [Matrix.mul_apply, Prod.ext_iff, ite_and]
  have h := measurePreserving_affine (Matrix.of fun q q' : R => a q.1.1 q'.1.1 * b q'.1.2 q.1.2)
    (det_two_sided R a b ha hb) (fun q : R => (a * b) q.1.1 q.1.2)
  convert h using 1
  funext c q
  simp only [hent, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]

theorem measurePreserving_mul_pi {ι : Type*} [Fintype ι] (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2)
    (a b : ι → Matrix (Fin N) (Fin N) ℂ) (ha : ∀ v, IsUpUni (a v)) (hb : ∀ v, IsUpUni (b v)) :
    MeasurePreserving (fun (c : ι → R → ℂ) (v : ι) (q : R) => (a v * ofRoots R (c v) * b v) q.1.1 q.1.2)
      volume volume :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume) fun v =>
    measurePreserving_mul R hR (a v) (b v) (ha v) (hb v)

end GlobalTheory.LoopVol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormLowerLe
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.LduBound

theorem norm_det_le {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (B : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ B) : ‖A.det‖ ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι := by
  have := Matrix.det_le (A := A) (abv := NormedField.toAbsoluteValue ℂ) (x := B) h
  rw [nsmul_eq_mul] at this
  exact this

theorem det_minor {n : ℕ} (L R : Matrix (Fin n) (Fin n) ℂ) (hL : IsLoUni L)
    (hR : ∀ a b, b < a → R a b = 0) (i j : Fin n) :
    ((L * R).submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1)).det = L i j * ∏ k ∈ Finset.Iic j, R k k := by
  have hf : (L * R).submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) =
      L.submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) * R.submatrix (fun a : {k : Fin n // k ≤ j} => a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k : Fin n => k ≤ j)]
    have : ∑ k : {k : Fin n // ¬ k ≤ j}, L (if a.1 = j then i else a.1) k.1 * R k.1 b.1 = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hR k.1 b.1 (lt_of_le_of_lt b.2 (not_le.1 k.2)), mul_zero]
    rw [this, add_zero]
  rw [hf, Matrix.det_mul]
  congr 1
  · rw [Matrix.det_of_lowerTriangular]
    · rw [Finset.prod_eq_single (⟨j, le_rfl⟩ : {k : Fin n // k ≤ j})]
      · simp
      · intro b _ hb
        have : b.1 ≠ j := fun h => hb (Subtype.ext h)
        simp only [Matrix.submatrix_apply, if_neg this]
        exact (hL _ _).2 rfl
      · simp
    · intro a b hab
      have hab' : a.1 < b.1 := hab
      have : a.1 ≠ j := ne_of_lt (lt_of_lt_of_le hab' b.2)
      simp only [Matrix.submatrix_apply, if_neg this]
      exact (hL _ _).1 hab'
  · rw [Matrix.det_of_upperTriangular]
    · simp only [Matrix.submatrix_apply]
      exact (Finset.prod_subtype (Finset.Iic j) (fun k => Finset.mem_Iic) (fun k => R k k)).symm
    · intro a b hab
      exact hR _ _ hab

theorem norm_lower_le {n : ℕ} (L U : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ) (B δ : ℝ)
    (hL : IsLoUni L) (hU : IsUpUni U) (hB : 1 ≤ B) (hδ : 0 < δ)
    (ht : ∀ l : Fin n, δ ≤ ‖∏ i ∈ Finset.Iic l, t i‖)
    (hZ : ∀ i j, ‖(L * Matrix.diagonal t * U) i j‖ ≤ B) (i j : Fin n) :
    ‖L i j‖ ≤ n.factorial * B ^ n / δ := by
  have h1 := det_minor L (Matrix.diagonal t * U) hL
    (fun a b hab => by rw [Matrix.diagonal_mul, (hU a b).1 hab, mul_zero]) i j
  have h2 : ∏ k ∈ Finset.Iic j, (Matrix.diagonal t * U) k k = ∏ k ∈ Finset.Iic j, t k :=
    Finset.prod_congr rfl fun k _ => by rw [Matrix.diagonal_mul, (hU k k).2 rfl, mul_one]
  rw [h2, ← Matrix.mul_assoc] at h1
  have h3 := norm_det_le ((L * Matrix.diagonal t * U).submatrix
    (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1)) B (fun a b => hZ _ _)
  rw [h1, norm_mul] at h3
  have hc : Fintype.card {k : Fin n // k ≤ j} ≤ n := by
    simpa using Fintype.card_subtype_le (fun k : Fin n => k ≤ j)
  have h4 : ((Fintype.card {k : Fin n // k ≤ j}).factorial : ℝ) * B ^ Fintype.card {k : Fin n // k ≤ j}
      ≤ n.factorial * B ^ n :=
    mul_le_mul (by exact_mod_cast Nat.factorial_le hc) (pow_le_pow_right₀ hB hc) (by positivity)
      (by positivity)
  rw [le_div_iff₀ hδ]
  exact (mul_le_mul_of_nonneg_left (ht j) (norm_nonneg _)).trans (h3.trans h4)

theorem norm_inv_le {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hA : A.det = 1) (x : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ x) (i j : Fin (m + 1)) : ‖A⁻¹ i j‖ ≤ m.factorial * x ^ m := by
  rw [Matrix.inv_def, hA, Ring.inverse_one, one_smul, Matrix.adjugate_fin_succ_eq_det_submatrix,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  simpa using norm_det_le (A.submatrix j.succAbove i.succAbove) x (fun a b => h _ _)

theorem ldu_bound (m : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ (L U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (t : Fin (m + 1) → ℂ) (B δ : ℝ), IsLoUni L → IsUpUni U → 1 ≤ B → 0 < δ → δ ≤ 1 →
    (∀ l : Fin (m + 1), δ ≤ ‖∏ i ∈ Finset.Iic l, t i‖) →
    (∀ i j, ‖(L * Matrix.diagonal t * U) i j‖ ≤ B) →
    ∀ i j, ‖L i j‖ ≤ c * B ^ (m + 1) / δ ∧ ‖U i j‖ ≤ c * B ^ (m + 1) / δ ∧
      ‖L⁻¹ i j‖ ≤ c * (B ^ (m + 1) / δ) ^ m ∧ ‖U⁻¹ i j‖ ≤ c * (B ^ (m + 1) / δ) ^ m := by
  refine ⟨(m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m, by positivity, ?_⟩
  intro L U t B δ hL hU hB hδ _ ht hZ
  have hB0 : 0 < B := by linarith
  have h1 := norm_lower_le L U t B δ hL hU hB hδ ht hZ
  have h2 : ∀ i j, ‖U i j‖ ≤ (m + 1).factorial * B ^ (m + 1) / δ := fun i j =>
    norm_lower_le Uᵀ Lᵀ t B δ (fun a b => ⟨(hU b a).1, fun h => (hU b a).2 h.symm⟩)
      (fun a b => ⟨(hL b a).1, fun h => (hL b a).2 h.symm⟩) hB hδ ht
      (fun a b => by
        have : Uᵀ * Matrix.diagonal t * Lᵀ = (L * Matrix.diagonal t * U)ᵀ := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
        rw [this]; exact hZ b a) j i
  have dL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L (fun a b hab => (hL a b).1 hab)]
    exact Finset.prod_eq_one fun k _ => (hL k k).2 rfl
  have dU : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := U) (fun a b hab => (hU a b).1 hab)]
    exact Finset.prod_eq_one fun k _ => (hU k k).2 rfl
  have e1 : ((m + 1).factorial : ℝ) * B ^ (m + 1) / δ ≤
      ((m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m) * B ^ (m + 1) / δ := by
    gcongr
    exact le_add_of_nonneg_right (by positivity)
  have e2 : (m.factorial : ℝ) * (((m + 1).factorial : ℝ) * B ^ (m + 1) / δ) ^ m ≤
      ((m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m) * (B ^ (m + 1) / δ) ^ m := by
    rw [mul_div_assoc, mul_pow, ← mul_assoc]
    gcongr
    exact le_add_of_nonneg_left (by positivity)
  exact fun i j => ⟨(h1 i j).trans e1, (h2 i j).trans e1, (norm_inv_le L dL _ h1 i j).trans e2,
    (norm_inv_le U dU _ h2 i j).trans e2⟩

end GlobalTheory.SgInf.LduBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLeadMinorDecay
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.MinorDecay

lemma Jm_sq {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

lemma herm_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X) :
    X.IsHermitian := by
  obtain ⟨h1, h2⟩ := h
  unfold inG at h1
  have h3 : Xᴴ * Jm ε = X * Jm ε := by
    rw [h2]; exact eq_neg_of_add_eq_zero_left h1
  have h4 := congrArg (· * Jm ε) h3
  simp only [Matrix.mul_assoc, Jm_sq, Matrix.mul_one] at h4
  exact h4

lemma diag_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X)
    (a : Fin n) : X a a = 0 := by
  have h2 := congrFun (congrFun h.2 a) a
  unfold Jm at h2
  simp only [mul_diagonal, Matrix.neg_apply, diagonal_mul] at h2
  split_ifs at h2
  · linear_combination h2 / 2
  · linear_combination -h2 / 2

lemma hs_eq_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    ((hs X : ℝ) : ℂ) = (X * Xᴴ).trace := by
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.mul_conj']
  rfl

lemma conj_facts {n : ℕ} {ε : Fin n → Bool} {X k : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X)
    (hk : k ∈ Kset ε) :
    inP ε (k⁻¹ * X * k) ∧ hs (k⁻¹ * X * k) = hs X ∧
      k⁻¹ * NormedSpace.exp X * k = NormedSpace.exp (k⁻¹ * X * k) := by
  obtain ⟨hu, hJ⟩ := hk
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  have h2 : k * kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hu
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv h1
  have hunit : IsUnit k := ⟨⟨k, kᴴ, h2, h1⟩, rfl⟩
  have hH := herm_of_inP h
  have hJ' : kᴴ * Jm ε = Jm ε * kᴴ := by
    calc kᴴ * Jm ε = kᴴ * Jm ε * (k * kᴴ) := by rw [h2, Matrix.mul_one]
      _ = kᴴ * (Jm ε * k) * kᴴ := by simp only [Matrix.mul_assoc]
      _ = (kᴴ * k) * Jm ε * kᴴ := by rw [← hJ]; simp only [Matrix.mul_assoc]
      _ = Jm ε * kᴴ := by rw [h1, Matrix.one_mul]
  have hanti : kᴴ * X * k * Jm ε = -(Jm ε * (kᴴ * X * k)) := by
    calc kᴴ * X * k * Jm ε = kᴴ * (X * Jm ε) * k := by
          simp only [Matrix.mul_assoc]; rw [hJ]
      _ = -(kᴴ * Jm ε * X * k) := by rw [h.2]; simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
      _ = _ := by rw [hJ']; simp only [Matrix.mul_assoc]
  have hYH : (kᴴ * X * k)ᴴ = kᴴ * X * k := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]
  refine ⟨?_, ?_, (Matrix.exp_conj' k X hunit).symm⟩
  · rw [hinv]
    refine ⟨?_, hanti⟩
    unfold inG
    rw [hYH, hanti, neg_add_cancel]
  · rw [hinv]
    apply Complex.ofReal_injective
    rw [hs_eq_trace, hs_eq_trace, hYH, hH.eq]
    have : kᴴ * X * k * (kᴴ * X * k) = kᴴ * (X * (k * kᴴ) * X * k) := by
      simp only [Matrix.mul_assoc]
    rw [this, h2, Matrix.mul_one, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one]

lemma deriv_sum_exp {ι : Type} [Fintype ι] (w y : ι → ℝ) :
    deriv (fun t : ℝ => ∑ J, w J * Real.exp (t * y J)) =
      fun t : ℝ => ∑ J, (w J * y J) * Real.exp (t * y J) := by
  funext t
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum
  intro J _
  have := (((hasDerivAt_id t).mul_const (y J)).exp).const_mul (w J)
  exact this.congr_deriv (by simp only [id]; ring)

lemma hs_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs X := by
  unfold hs; positivity

lemma minor_bound {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inP ε Y)
    (R : ℝ) (hR : R = Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) * Real.sqrt (hs Y))
    (l : ℕ) (hl : l ≤ n) :
    0 < (leadMinor (NormedSpace.exp Y) l hl).re ∧ (leadMinor (NormedSpace.exp Y) l hl).im = 0 ∧
      min 1 (1 / R) * (∑ a : Fin n, ∑ b : Fin n,
        if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0) / 4
        ≤ Real.log (leadMinor (NormedSpace.exp Y) l hl).re := by
  have hH := herm_of_inP h
  obtain ⟨w, hw0, -, hw1, hw⟩ := _root_.GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum n Y hH l hl
  obtain ⟨hd1, hd2⟩ := _root_.GlobalTheory.MinorJet.deriv_leadMinor_exp n Y hH (diag_of_inP h) l hl
  have hrange := _root_.GlobalTheory.EigenPartialSum.abs_sum_eigenvalues_le n ε Y hH h
  rw [← hR] at hrange
  set y : Finset (Fin n) → ℝ := fun J => ∑ j ∈ J, hH.eigenvalues j with hy
  have hfun : (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)
      = fun t : ℝ => ∑ J, w J * Real.exp (t * y J) := by
    funext t; rw [hw t, Complex.ofReal_re]
  rw [hfun, deriv_sum_exp] at hd1 hd2
  rw [deriv_sum_exp] at hd2
  simp only [zero_mul, Real.exp_zero, mul_one] at hd1 hd2
  have hone := hw 1
  simp only [Complex.ofReal_one, one_smul, one_mul] at hone
  rw [hone, Complex.ofReal_re, Complex.ofReal_im]
  have hpos : 0 < ∑ J, w J * Real.exp (y J) := by
    have : ∃ J, w J ≠ 0 := by
      by_contra hc
      push Not at hc
      simp [hc] at hw1
    obtain ⟨J, hJ⟩ := this
    exact Finset.sum_pos' (fun J _ => mul_nonneg (hw0 J) (Real.exp_pos _).le)
      ⟨J, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw0 J) hJ.symm) (Real.exp_pos _)⟩
  refine ⟨hpos, rfl, ?_⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hvar : ∑ J, w J * y J ^ 2 = ∑ a : Fin n, ∑ b : Fin n,
        if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
    rw [← hd2]; refine Finset.sum_congr rfl fun J _ => by ring
  rw [← hvar]
  rcases hR0.eq_or_lt with h0 | h0
  · have hy0 : ∀ J, y J = 0 := fun J => abs_nonpos_iff.1 (by rw [h0]; exact hrange J)
    change _ ≤ Real.log (∑ J, w J * Real.exp (y J))
    simp [hy0, hw1]
  · exact _root_.GlobalTheory.cumulant_lower_bound_of_bounded_centred _ w y R h0 hw0 hw1 hd1 (fun J _ => hrange J)

lemma min_mul_eq (H c : ℝ) (hH : 0 ≤ H) :
    min 1 (1 / (c * Real.sqrt H)) * H = min H (Real.sqrt H / c) := by
  rw [min_mul_of_nonneg _ _ hH, one_mul]
  congr 1
  rcases hH.eq_or_lt with h0 | h0
  · simp [← h0]
  · have hs : 0 < Real.sqrt H := Real.sqrt_pos.2 h0
    have : H = Real.sqrt H * Real.sqrt H := (Real.mul_self_sqrt hH).symm
    rcases eq_or_ne c 0 with hc | hc
    · simp [hc]
    · rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (by positivity) hc]
      linear_combination c * this

theorem prod_leadMinor_decay : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (X km : Matrix (Fin n) (Fin n) ℂ), IsHCParam lam → GapAtLeast ε lam h → inP ε X → km ∈ Kset ε → (∀ (l : ℕ) (hl : l ≤ n), 0 < (leadMinor (km⁻¹ * NormedSpace.exp X * km) l hl).re ∧ (leadMinor (km⁻¹ * NormedSpace.exp X * km) l hl).im = 0) ∧ ∏ i : Fin (n - 1), (leadMinor (km⁻¹ * NormedSpace.exp X * km) (i.val + 1) (by omega)).re ^ (-(lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1)) ≤ Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card : ℕ) : ℝ)))) := by
  intro n ε lam h X km hlam hgap hX hk
  obtain ⟨hY, hhs, hexp⟩ := conj_facts hX hk
  rw [hexp, ← hhs]
  set Y := km⁻¹ * X * km with hYdef
  have key := minor_bound hY _ rfl
  refine ⟨fun l hl => ⟨(key l hl).1, (key l hl).2.1⟩, ?_⟩
  have hgs := _root_.GlobalTheory.GapSum.gap_mul_hs_le n ε lam h Y hlam.1 hgap hY
  rw [← min_mul_eq _ _ (hs_nonneg Y)]
  set c := Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) with hc
  set t := min 1 (1 / (c * Real.sqrt (hs Y))) with ht
  have ht0 : 0 ≤ t := le_min zero_le_one (by positivity)
  rw [Finset.prod_congr rfl fun i _ => Real.rpow_def_of_pos (key _ _).1 _, ← Real.exp_sum,
    Real.exp_le_exp]
  have h2 := mul_le_mul_of_nonneg_left hgs (by positivity : 0 ≤ t / 4)
  rw [Finset.mul_sum] at h2
  have h3 : -(h / 8) * (t * hs Y) = -(t / 4 * (h * hs Y / 2)) := by ring
  rw [h3, le_neg]
  refine h2.trans ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hlt : lam ⟨i.val + 1, by omega⟩ < lam ⟨i.val, by omega⟩ :=
    hlam.1 (by simp [Fin.lt_def])
  have hk := (key (i.val + 1) (by omega)).2.2
  have hs0 : 0 ≤ lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1 := by linarith
  have := mul_le_mul_of_nonneg_left hk hs0
  linarith

end GlobalTheory.MinorDecay
end

