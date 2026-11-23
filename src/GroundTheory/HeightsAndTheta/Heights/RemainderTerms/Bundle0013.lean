module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchCompleteAtRootsOfUnity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem prod_one_sub_rootOfUnityPoint (h1 : SchProdOneSubRootsOfUnity.Statement) {N k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∏ i : Fin N, (1 - Polynomial.C (rootOfUnityPoint N k i) * Polynomial.X) =
      (1 - Polynomial.X ^ k : Polynomial ℂ) := by
  let f : ℕ → Polynomial ℂ := fun i =>
    1 - Polynomial.C (if i < k then rootOfUnity k ^ i else 0) * Polynomial.X
  calc ∏ i : Fin N, (1 - Polynomial.C (rootOfUnityPoint N k i) * Polynomial.X)
      = ∏ i ∈ range N, f i := Fin.prod_univ_eq_prod_range f N
    _ = ∏ i ∈ range k, f i := by
        refine (prod_subset (range_subset_range.2 hkN) fun i _ hik => ?_).symm
        have : ¬ i < k := fun h => hik (mem_range.2 h)
        simp [f, this]
    _ = ∏ i ∈ range k, (1 - Polynomial.C (rootOfUnity k ^ i) * Polynomial.X) :=
        prod_congr rfl fun i hi => by simp [f, mem_range.1 hi]
    _ = 1 - Polynomial.X ^ k := h1 k hk

theorem SchCompleteAtRootsOfUnity.proof (h1 : SchProdOneSubRootsOfUnity.Statement)
    (h2 : SchCompleteGenerating.Statement) : SchCompleteAtRootsOfUnity.Statement := by
  intro N k d hk hkN
  let H : ℕ → ℂ := fun n => aeval (rootOfUnityPoint N k) (hsymm (Fin N) ℚ n)
  have hrec : ∀ n, H n - (if k ≤ n then H (n - k) else 0) = if n = 0 then 1 else 0 := by
    intro n
    have e := h2 N (rootOfUnityPoint N k) n
    rw [prod_one_sub_rootOfUnityPoint h1 hk hkN] at e
    rw [← e]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow, sub_mul,
      sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
    simp [H]
  show H d = _
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have e := hrec d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [if_neg (by omega), sub_zero, if_pos rfl] at e
      rw [e, if_pos (dvd_zero k)]
    · by_cases hkd : k ≤ d
      · rw [if_pos hkd, if_neg (show d ≠ 0 by omega), sub_eq_zero, ih (d - k) (by omega)] at e
        have hdvd : k ∣ d - k ↔ k ∣ d := by
          conv_rhs => rw [show d = d - k + k by omega]
          exact (Nat.dvd_add_self_right).symm
        rw [e]
        exact if_congr hdvd rfl rfl
      · rw [if_neg hkd, if_neg (show d ≠ 0 by omega), sub_zero] at e
        rw [e, if_neg]
        exact fun h => hkd (Nat.le_of_dvd hd h)

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchCompleteGenerating
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace SchCompleteGenerating

theorem coeff_prod_geomSeries_eval {N : ℕ} (y : Fin N → ℂ) (n : ℕ) :
    PowerSeries.coeff n (∏ i : Fin N, Schur.geomSeries (y i)) =
      aeval y (hsymm (Fin N) ℚ n) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PowerSeries.coeff_prod, Schur.hsymm_eq_sum_finsuppAntidiag, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Schur.geomSeries, PowerSeries.coeff_mk, map_prod]

theorem coe_prod_one_sub {N : ℕ} (y : Fin N → ℂ) :
    ((∏ i : Fin N, (1 - Polynomial.C (y i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) =
      ∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp

theorem prod_one_sub_mul_prod_geomSeries {N : ℕ} (y : Fin N → ℂ) :
    (∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X)) *
      ∏ i : Fin N, Schur.geomSeries (y i) = 1 := by
  rw [← prod_mul_distrib]
  exact prod_eq_one fun i _ => by rw [mul_comm, Schur.geomSeries_mul]

theorem proof : Statement := by
  intro N y d
  have key := congrArg (PowerSeries.coeff d) (prod_one_sub_mul_prod_geomSeries y)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X)) *
      PowerSeries.coeff b (∏ i : Fin N, Schur.geomSeries (y i))), PowerSeries.coeff_one] at key
  simp only [coeff_prod_geomSeries_eval, ← coe_prod_one_sub, Polynomial.coeff_coe] at key
  exact key

end SchCompleteGenerating

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatAlternant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchConcatAlternant.alternant_comp_perm {N : ℕ} (w : Fin N → ℕ) (τ : Equiv.Perm (Fin N)) :
    alternant (w ∘ τ) = C ((Equiv.Perm.sign τ : ℤ) : ℚ) * alternant w := by
  unfold alternant
  have hM : (Matrix.of fun i i' : Fin N =>
      (X i : MvPolynomial (Fin N) ℚ) ^ (w ∘ τ) i') =
      (Matrix.of fun i i' : Fin N => (X i : MvPolynomial (Fin N) ℚ) ^ w i').submatrix id τ := rfl
  rw [hM, Matrix.det_permute', map_intCast]

theorem SchConcatAlternant.alternant_add_staircase {N : ℕ} (mu : Fin N → ℕ) :
    alternant (fun p : Fin N => mu p + (N - 1 - (p : ℕ))) =
      vandermondeOf (fun p : Fin N => (X p : MvPolynomial (Fin N) ℚ)) * schur (Fin N) mu := by
  rw [mul_comm, ← Schur.det_pow_add_staircase_eq, ← Matrix.det_transpose]
  rfl

theorem SchConcatAlternant.proof (h1 : SchAlternantRenamePlace.Statement)
    (h2 : SchConcatExponent.Statement) : SchConcatAlternant.Statement := by
  intro r a c
  obtain ⟨τ, hτ⟩ := h2 r a c
  refine ⟨((Equiv.Perm.sign τ : ℤ) : ℚ), ?_, fun lam hlam => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  · rw [h1, hτ lam hlam, SchConcatAlternant.alternant_comp_perm,
      SchConcatAlternant.alternant_add_staircase,
      Schur.schur_padPartition (Fin (r + a)) (fun i : Fin r => lam i - a) (r + a) (by omega), map_mul,
      rename_C]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatExponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

noncomputable section

def SchConcatExponent.rotateFun (r a : ℕ) (p : Fin (r + a)) : Fin (r + a) :=
  if h : (p : ℕ) < a then ⟨r + p, by omega⟩ else ⟨p - a, by have := p.isLt; omega⟩

def SchConcatExponent.rotateInv (r a : ℕ) (q : Fin (r + a)) : Fin (r + a) :=
  if h : (q : ℕ) < r then ⟨q + a, by omega⟩ else ⟨q - r, by have := q.isLt; omega⟩

theorem SchConcatExponent.rotateFun_val (r a : ℕ) (p : Fin (r + a)) :
    (SchConcatExponent.rotateFun r a p : ℕ) = if (p : ℕ) < a then r + p else p - a := by
  unfold SchConcatExponent.rotateFun; split <;> rfl

theorem SchConcatExponent.rotateInv_val (r a : ℕ) (q : Fin (r + a)) :
    (SchConcatExponent.rotateInv r a q : ℕ) = if (q : ℕ) < r then q + a else q - r := by
  unfold SchConcatExponent.rotateInv; split <;> rfl

def SchConcatExponent.rotate (r a : ℕ) : Equiv.Perm (Fin (r + a)) where
  toFun := SchConcatExponent.rotateFun r a
  invFun := SchConcatExponent.rotateInv r a
  left_inv p := by
    have hp := p.isLt
    apply Fin.ext
    rw [SchConcatExponent.rotateInv_val, SchConcatExponent.rotateFun_val]
    split_ifs <;> omega
  right_inv q := by
    have hq := q.isLt
    apply Fin.ext
    rw [SchConcatExponent.rotateFun_val, SchConcatExponent.rotateInv_val]
    split_ifs <;> omega

theorem SchConcatExponent.proof : SchConcatExponent.Statement := by
  intro r a c
  cases c with
  | first =>
    refine ⟨Equiv.refl _, fun lam hlam => ?_⟩
    funext p
    have hp := p.isLt
    by_cases h : (p : ℕ) < r
    · have := hlam ⟨p, h⟩
      simp [smallBlockOf, Schur.padPartition, h]
      omega
    · simp [smallBlockOf, Schur.padPartition, h]
      omega
  | last =>
    refine ⟨SchConcatExponent.rotate r a, fun lam hlam => ?_⟩
    funext p
    have hp := p.isLt
    simp only [Function.comp_apply]
    generalize hq : SchConcatExponent.rotate r a p = q
    have hv : (q : ℕ) = if (p : ℕ) < a then r + p else p - a := by
      rw [← hq]; exact SchConcatExponent.rotateFun_val r a p
    simp only [Schur.padPartition, smallBlockOf]
    by_cases h : (p : ℕ) < a
    · have hn : ¬ ((q : ℕ) < r) := by rw [hv, if_pos h]; omega
      rw [dite_eq_left h, dite_eq_right hn]
      simp only [Sum.elim_inr]
      rw [hv, if_pos h]
      omega
    · have h' : (p : ℕ) - a < r := by omega
      have hn : (q : ℕ) < r := by rw [hv, if_neg h]; exact h'
      rw [dite_eq_right h, dite_eq_left hn]
      simp only [Sum.elim_inl]
      have hqe : (⟨q, hn⟩ : Fin r) = ⟨(p : ℕ) - a, h'⟩ := Fin.ext (by rw [hv, if_neg h])
      rw [hqe, hv, if_neg h]
      have := hlam ⟨(p : ℕ) - a, h'⟩
      omega

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchEvalPowerSumHom
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchEvalPowerSumHom.eq_single_of_dvd {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (e : Fin N →₀ ℕ) (hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = k)
    (hd : ∀ i ∈ e.support, k ∣ (i : ℕ) + 1) :
    e = Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1 := by
  have hsum : ∑ i ∈ e.support, e i * ((i : ℕ) + 1) = k := by
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] at hw
    exact hw
  obtain ⟨j, hj⟩ : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hsum
    omega
  have hej : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have hjk : k ≤ (j : ℕ) + 1 := Nat.le_of_dvd (by omega) (hd j hj)
  rw [← Finset.add_sum_erase _ _ hj] at hsum
  have hmul : k ≤ e j * ((j : ℕ) + 1) := le_trans hjk (Nat.le_mul_of_pos_left _ hej)
  have hrest : ∑ i ∈ e.support.erase j, e i * ((i : ℕ) + 1) = 0 := by omega
  have hjm : e j * ((j : ℕ) + 1) = k := by omega
  have hej1 : e j = 1 := by nlinarith
  have hjv : j = (⟨k - 1, by omega⟩ : Fin N) := by
    rw [hej1, one_mul] at hjm
    exact Fin.ext (by simp; omega)
  have hother : ∀ i, i ≠ j → e i = 0 := by
    intro i hij
    by_contra hne
    have hi : i ∈ e.support.erase j :=
      Finset.mem_erase.mpr ⟨hij, Finsupp.mem_support_iff.mpr hne⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hrest) i hi
    rw [Nat.mul_eq_zero] at h0
    omega
  ext i
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [← h, ← hjv, hej1]
  · exact hother i (fun hij => h (hjv.symm.trans hij.symm))

theorem SchEvalPowerSumHom.proof (h1 : SchPowerSumAtRootsOfUnity.Statement) :
    SchEvalPowerSumHom.Statement := by
  intro N k hk1 hkN S hS
  have hzv : ∀ i : Fin N, aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1)) =
      if k ∣ (i : ℕ) + 1 then (k : ℂ) else 0 := fun i =>
    h1 N k ((i : ℕ) + 1) hk1 hkN (by omega)
  have hcomp : aeval (rootOfUnityPoint N k) (powerSumHom N S) =
      aeval (fun i : Fin N => aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1))) S := by
    rw [powerSumHom, ← AlgHom.comp_apply, comp_aeval]
  rw [hcomp]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [S.as_sum, map_sum]
  rw [Finset.sum_eq_single (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1)]
  · have hdvd : k ∣ ((⟨k - 1, by omega⟩ : Fin N) : ℕ) + 1 := by
      simp only [Nat.sub_add_cancel hk1, dvd_refl]
    rw [aeval_monomial, Finsupp.prod_single_index (by simp), pow_one, hzv, if_pos hdvd]
    simp [mul_comm]
  · intro e he hne
    rw [aeval_monomial]
    have hw := hS (MvPolynomial.mem_support_iff.mp he)
    obtain ⟨i, hi, hik⟩ : ∃ i ∈ e.support, ¬ k ∣ (i : ℕ) + 1 := by
      by_contra hcon
      push Not at hcon
      exact hne (SchEvalPowerSumHom.eq_single_of_dvd hk1 hkN e hw hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
    rw [hzv, if_neg hik, zero_pow (Finsupp.mem_support_iff.mp hi)]
  · intro h
    rw [MvPolynomial.notMem_support_iff.mp h, monomial_zero, map_zero]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchHookResidues
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchHookResidues.proof : SchHookResidues.Statement := by
  intro k nu hk hanti hsum hhook
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  set s := univ.filter fun i : Fin (n + 1) => (i : ℕ) ≠ 0 ∧ nu i = 1 with hs
  set t := s.card with ht
  have down : ∀ i j : Fin (n + 1), (i : ℕ) ≠ 0 → i ≤ j → j ∈ s → i ∈ s := by
    intro i j hi hij hj
    simp only [hs, mem_filter, mem_univ, true_and] at hj ⊢
    have h1 := hanti hij
    have h2 := hhook i hi
    exact ⟨hi, by omega⟩
  have hA : ∀ j ∈ s, (j : ℕ) ≤ t := by
    intro j hj
    have hsub : Finset.Icc 1 (j : ℕ) ⊆ s.map Fin.valEmbedding := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_map]
      refine ⟨⟨m, by omega⟩, down _ j (show m ≠ 0 by omega)
        (by rw [Fin.le_iff_val_le_val]; show m ≤ (j : ℕ); omega) hj, rfl⟩
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hB : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → (i : ℕ) ≤ t → i ∈ s := by
    intro i hi hit
    by_contra hni
    have hsub : s.map Fin.valEmbedding ⊆ Finset.Ico 1 (i : ℕ) := by
      intro m hm
      rw [Finset.mem_map] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      have hj' := hj
      simp only [hs, mem_filter, mem_univ, true_and] at hj'
      rw [Finset.mem_Ico]
      refine ⟨by simp only [Fin.valEmbedding_apply]; omega, ?_⟩
      by_contra hle
      exact hni (down i j hi (by rw [Fin.le_iff_val_le_val]; simp at hle; omega) hj)
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hval : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → nu i = if (i : ℕ) ≤ t then 1 else 0 := by
    intro i hi
    have h1 := hhook i hi
    split_ifs with h
    · have := hB i hi h
      simp only [hs, mem_filter, mem_univ, true_and] at this
      exact this.2
    · have : nu i ≠ 1 := by
        intro h1'
        have := hA i (by simp only [hs, mem_filter, mem_univ, true_and]; exact ⟨hi, h1'⟩)
        omega
      omega
  have htn : t ≤ n := by
    have hsub : s ⊆ univ.erase 0 := by
      intro i hi
      simp only [hs, mem_filter, mem_univ, true_and] at hi
      exact Finset.mem_erase.mpr ⟨fun h => hi.1 (by simp [h]), mem_univ _⟩
    have := card_le_card hsub
    simpa [card_erase_of_mem] using this
  have hnu0 : nu 0 + t = n + 1 := by
    have hpt : ∀ i, nu i = (if i = 0 then nu 0 else 0) +
        (if (i : ℕ) ≠ 0 ∧ nu i = 1 then 1 else 0) := by
      intro i
      by_cases h0 : i = 0
      · subst h0; simp
      · have hi : (i : ℕ) ≠ 0 := fun h => h0 (Fin.ext (by simp [h]))
        have := hhook i hi
        rw [if_neg h0, zero_add]
        split_ifs with h <;> omega
    have hsum2 : ∑ i, nu i = nu 0 + t := by
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_boole]
      simp [t, s]
    omega
  refine ⟨(Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)))⁻¹, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := (Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1))).surjective i
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rcases lt_trichotomy (j : ℕ) t with h | h | h
    · have hlt : j < (⟨t, by omega⟩ : Fin (n + 1)) := Fin.lt_def.mpr h
      have hv : ((Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)) j : Fin (n + 1)) : ℕ) = j + 1 :=
        Fin.coe_cycleRange_of_lt hlt
      rw [hval _ (by rw [hv]; omega), hv, if_pos (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Fin.cycleRange_of_eq (Fin.ext h), Fin.val_zero]
      have h2 : nu 0 + (n + 1 - 1 - 0) = (n - t) + (n + 1) := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hgt : (⟨t, by omega⟩ : Fin (n + 1)) < j := Fin.lt_def.mpr h
      rw [Fin.cycleRange_of_gt hgt, hval j (by omega), if_neg (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [Equiv.Perm.sign_inv, Fin.sign_cycleRange]
    simp [t, s]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchJTMatrixDetAtRoots
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchJTMatrixDetAtRoots.proof (h1 : SchRootOfUnityBialternant.Statement)
    (h2 : SchRootOfUnityRowsPerm.Statement) (h3 : SchRootOfUnityRowsEq.Statement)
    (h4 : SchHookResidues.Statement) (h5 : SchNonHookResidues.Statement)
    (h6 : SchRootOfUnityVandermondeNe.Statement) : SchJTMatrixDetAtRoots.Statement := by
  intro k nu hk hanti hsum
  have hV := h6 k hk
  have hB := h1 k nu hk

  have hstair : (Matrix.of fun i j : Fin k =>
      rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).det =
      vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := by
    rw [← Schur.det_pow_staircase_eq_vandermondeOf (fun j : Fin k => rootOfUnity k ^ (j : ℕ))]
    congr 1
    ext i j
    simp [Matrix.of_apply, pow_mul]
  split_ifs with hhook
  · obtain ⟨π, hres, hsign⟩ := h4 k nu hk hanti hsum hhook
    have hP := h2 k (fun i => nu i + (k - 1 - (i : ℕ))) π hk hres
    rw [hstair] at hP
    have hP' : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
          vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := hP
    rw [hB] at hP'
    have := mul_right_cancel₀ hV hP'
    rw [this, hsign]
    push_cast
    rfl
  · obtain ⟨i, i', hne, hres⟩ := h5 k nu hk hanti hsum hhook
    have hZ : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det = 0 :=
      h3 k (fun i => nu i + (k - 1 - (i : ℕ))) i i' hne hres
    rw [hB] at hZ
    exact (mul_eq_zero.mp hZ).resolve_right hV

end GroundTheory.Heights₂.Heights.RestTerms
end

