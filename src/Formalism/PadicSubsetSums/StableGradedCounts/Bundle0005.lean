module

public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0001
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0001
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002

@[expose] public section

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.LagrangeBound
section
namespace Formalism.IrreducibleCountingLemmas.WindowSums

private theorem sum_le_of_unique {ι : Type} (s : Finset ι) (g : ι → ℕ) (r : ℕ)
    (hle : ∀ i ∈ s, g i ≤ r) (huniq : ∀ i ∈ s, ∀ j ∈ s, g i ≠ 0 → g j ≠ 0 → i = j) :
    ∑ i ∈ s, g i ≤ r := by
  classical
  by_cases h : ∃ i ∈ s, g i ≠ 0
  · obtain ⟨i, hi, hgi⟩ := h
    rw [← Finset.add_sum_erase s g hi]
    have h0 : ∑ j ∈ s.erase i, g j = 0 := Finset.sum_eq_zero fun j hj => by
      by_contra hne
      exact (Finset.ne_of_mem_erase hj) (huniq j (Finset.mem_of_mem_erase hj) i hi hne hgi)
    rw [h0, add_zero]
    exact hle i hi
  · push Not at h
    rw [Finset.sum_eq_zero h]
    exact Nat.zero_le _

theorem sumPadicValDifferencesLe : LagrangeBoundT := by
  intro l a A' r' Cc hl ha hA hlt hdiv c hc n hn
  have hfact : Fact l.Prime := ⟨hl⟩
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hnotL : ¬ (l : ℤ) ∣ (l : ℤ) ^ a - 1 := by
    intro h
    have h1 : (l : ℤ) ∣ (l : ℤ) ^ a := dvd_pow_self _ (by omega)
    have h2 : (l : ℤ) ∣ 1 := by
      have h3 := dvd_sub h1 h
      rwa [sub_sub_cancel] at h3
    exact hlZ.not_isUnit (isUnit_of_dvd_one h2)
  have hsep : ∀ x m1 m2 : ℤ, |m1 - m2| < l → (l : ℤ) ∣ x + m1 * ((l : ℤ) ^ a - 1) →
      (l : ℤ) ∣ x + m2 * ((l : ℤ) ^ a - 1) → m1 = m2 := by
    intro x m1 m2 hm h1 h2
    have h3 : (l : ℤ) ∣ (m1 - m2) * ((l : ℤ) ^ a - 1) := by
      have e : (m1 - m2) * ((l : ℤ) ^ a - 1) =
          (x + m1 * ((l : ℤ) ^ a - 1)) - (x + m2 * ((l : ℤ) ^ a - 1)) := by ring
      rw [e]
      exact dvd_sub h1 h2
    rcases hlZ.dvd_or_dvd h3 with h | h
    · have := Int.eq_zero_of_abs_lt_dvd h hm
      linarith
    · exact absurd h hnotL
  have hdv : ∀ z : ℤ, padicValInt l z ≠ 0 → (l : ℤ) ∣ z := by
    intro z hz
    have h := (padicValInt_dvd_iff (p := l) 1 z).mpr (Or.inr (Nat.one_le_iff_ne_zero.mpr hz))
    simpa using h
  have hneg : ∀ z : ℤ, padicValInt l (-z) = padicValInt l z := fun z => by simp [padicValInt]
  have hpow : ∀ k : ℕ, ((l ^ k - 1 : ℕ) : ℤ) = (l : ℤ) ^ k - 1 := fun k => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hl.pos)]
    push_cast
    ring
  have hper : ∀ c' ∈ Cc, (∑ n' ∈ Finset.range (2 * A'),
      if c' = c ∧ n' = n then 0
      else padicValInt l (((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)))) ≤
      if c' = c then 0 else r' := by
    intro c' hc'
    by_cases hcc : c' = c
    · subst hcc
      rw [if_pos rfl]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro n' hn'
      rw [Finset.mem_range] at hn'
      split_ifs with h
      · rfl
      · by_contra hne
        have h1 := hdv _ hne
        have hz : ((c' : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
            0 + ((n : ℤ) - n') * ((l : ℤ) ^ a - 1) := by ring
        rw [hz] at h1
        have h2 := hsep 0 ((n : ℤ) - n') 0 (by rw [sub_zero, abs_lt]; constructor <;> omega) h1 (by simp)
        exact h ⟨rfl, by omega⟩
    · rw [if_neg hcc]
      obtain ⟨ρ, hρ1, hρr, hρd⟩ := hdiv c hc c' hc' (Ne.symm hcc)
      apply sum_le_of_unique
      · intro n' hn'
        rw [Finset.mem_range] at hn'
        rw [if_neg (fun h => hcc h.1)]
        refine le_trans ?_ hρr
        rcases lt_or_gt_of_ne hcc with hlt' | hgt
        · have hdN : (l ^ a - 1) ∣ (c - c') * (l ^ ρ - 1) := by
            rw [← Int.natCast_dvd_natCast, Nat.cast_mul, hpow, hpow, Nat.cast_sub hlt'.le]
            exact hρd
          have hD := padicValIntShiftLe l a (c - c') ρ ((n : ℤ) - n') hl ha (by omega)
            (lt_of_le_of_lt (Nat.sub_le _ _) (hlt c hc)) hρ1 hdN
            (by rw [abs_lt]; constructor <;> omega)
          have hz : ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
              ((c - c' : ℕ) : ℤ) + ((n : ℤ) - n') * ((l : ℤ) ^ a - 1) := by
            rw [Nat.cast_sub hlt'.le]
            ring
          rw [hz]
          exact hD
        · have hdN : (l ^ a - 1) ∣ (c' - c) * (l ^ ρ - 1) := by
            rw [← Int.natCast_dvd_natCast, Nat.cast_mul, hpow, hpow, Nat.cast_sub hgt.le]
            have e : ((c' : ℤ) - c) * ((l : ℤ) ^ ρ - 1) = -(((c : ℤ) - c') * ((l : ℤ) ^ ρ - 1)) := by ring
            rw [e]
            exact dvd_neg.mpr hρd
          have hD := padicValIntShiftLe l a (c' - c) ρ ((n' : ℤ) - n) hl ha (by omega)
            (lt_of_le_of_lt (Nat.sub_le _ _) (hlt c' hc')) hρ1 hdN
            (by rw [abs_lt]; constructor <;> omega)
          have hz : ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
              -(((c' - c : ℕ) : ℤ) + ((n' : ℤ) - n) * ((l : ℤ) ^ a - 1)) := by
            rw [Nat.cast_sub hgt.le]
            ring
          rw [hz, hneg]
          exact hD
      · intro i hi j hj hgi hgj
        rw [Finset.mem_range] at hi hj
        rw [if_neg (fun h => hcc h.1)] at hgi hgj
        have h1 := hdv _ hgi
        have h2 := hdv _ hgj
        have ez : ∀ k : ℕ, ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + k * ((l : ℤ) ^ a - 1)) =
            ((c : ℤ) - c') + ((n : ℤ) - k) * ((l : ℤ) ^ a - 1) := fun k => by ring
        rw [ez] at h1 h2
        have := hsep _ _ _ (by rw [abs_lt]; constructor <;> omega) h1 h2
        omega
  calc (∑ c' ∈ Cc, ∑ n' ∈ Finset.range (2 * A'),
        if c' = c ∧ n' = n then 0
        else padicValInt l (((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1))))
      ≤ ∑ c' ∈ Cc, (if c' = c then 0 else r') := Finset.sum_le_sum hper
    _ = (Cc.card - 1) * r' := by
      rw [← Finset.add_sum_erase Cc _ hc, if_pos rfl, zero_add,
        Finset.sum_congr rfl (fun x hx => if_neg (Finset.ne_of_mem_erase hx)), Finset.sum_const,
        smul_eq_mul, Finset.card_erase_of_mem hc]

end Formalism.IrreducibleCountingLemmas.WindowSums
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.TWCentralIdempotentIntegral
section
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.TW

theorem isIntegral_trace_of_isIntegral {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := by
  let L := AlgebraicClosure K
  let φ : Matrix n n K →ₐ[ℤ] Matrix n n L := ((algebraMap K L).mapMatrix).toIntAlgHom
  have hM' : IsIntegral ℤ (φ M) := hM.map φ
  have htr : algebraMap K L M.trace = (φ M).trace := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, map_sum]
    rfl
  rw [← isIntegral_algebraMap_iff (A := K) (B := L) , htr,
    Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : IsRoot (φ M).charpoly μ := (mem_roots'.1 hμ).2
  have hspec : μ ∈ spectrum L (φ M) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  obtain ⟨p, hp, hp0⟩ := hM'
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap ℤ L)) ⟨μ, hspec, rfl⟩
  have h2 : aeval (φ M) (p.map (algebraMap ℤ L)) = 0 := by
    rw [aeval_map_algebraMap]; simpa [aeval_def] using hp0
  have : Nontrivial (Matrix n n L) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hspec
    exact hspec
  rw [h2, spectrum.zero_eq, Set.mem_singleton_iff] at h1
  simpa [eval_map] using h1

theorem central_idempotent_integral_twist : CentralIdempotentIntegral := by
  intro K _ _ G _ _ e he hc g
  classical
  set x : MonoidAlgebra K G := e * MonoidAlgebra.single g⁻¹ 1 with hx
  have hpow : ∀ k : ℕ, x ^ (k + 1) = e * MonoidAlgebra.single (g⁻¹ ^ (k + 1)) 1 := by
    intro k
    induction k with
    | zero => simp [hx]
    | succ k ih =>
      rw [pow_succ, ih, hx, mul_assoc, ← mul_assoc (MonoidAlgebra.single _ _) e, ← hc,
        mul_assoc, ← mul_assoc e e, he, MonoidAlgebra.single_mul_single, ← pow_succ, one_mul]
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have hxe : x ^ Fintype.card G = e := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
    rw [hk, Nat.succ_eq_add_one, hpow, ← Nat.succ_eq_add_one, ← hk, pow_card_eq_one,
      ← MonoidAlgebra.one_def, mul_one]
  have hei : IsIntegral ℤ e := by
    refine ⟨X ^ 2 - X, monic_X_pow_sub (by simp), ?_⟩
    simp [pow_two, he]
  have hxi : IsIntegral ℤ x := IsIntegral.of_pow hcard (hxe ▸ hei)
  have hMi : IsIntegral ℤ (Algebra.leftMulMatrix (MonoidAlgebra.basis G K) x) :=
    hxi.map (A := K) (Algebra.leftMulMatrix (MonoidAlgebra.basis G K))
  have htr : (Algebra.leftMulMatrix (MonoidAlgebra.basis G K) x).trace
      = (Fintype.card G : K) * e.coeff g := by
    have : ∀ i : G, Algebra.leftMulMatrix (MonoidAlgebra.basis G K) x i i = e.coeff g := by
      intro i
      rw [Algebra.leftMulMatrix_eq_repr_mul, MonoidAlgebra.basis_apply]
      change (x * MonoidAlgebra.single i 1).coeff i = _
      simp [hx]
    simp [Matrix.trace, this]
  rw [← htr]
  exact isIntegral_trace_of_isIntegral _ hMi

end Formalism.IrreducibleCountingLemmas.TW
end

