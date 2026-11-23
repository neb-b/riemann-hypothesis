module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationComapSpanPow
section
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatPdpEq

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

def dq (i : ℕ) : ℚ := ((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i

theorem dq_ne_zero (hl : l ≠ 0) (i : ℕ) : dq l M i ≠ 0 := by
  have h1 : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  have h2 : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  unfold dq
  positivity

theorem dpE_eq_smul (i : ℕ) : Lat.dpE f ξ l M i = dq l M i • f ξ ^ i := by
  unfold Lat.dpE Lat.η dq
  rw [smul_pow, smul_smul]

theorem dpE_eq_zero {m i : ℕ} (hm : f ξ ^ m = 0) (hi : m ≤ i) : Lat.dpE f ξ l M i = 0 := by
  rw [dpE_eq_smul, ← Nat.add_sub_of_le hi, pow_add, hm, zero_mul, smul_zero]

theorem dpE_mem_span {k i : ℕ} (hi : k ≤ i) : Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ k} := by
  rw [dpE_eq_smul, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ hi))

theorem ι_mem (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M :=
  Subtype.property (p := fun y => y ∈ Lat.sub f ξ l M) x

theorem dpA_one_mem : Lat.dpA f ξ l M 1 ∈ Lat.I f ξ l M := by
  show Lat.dpE f ξ l M 1 ∈ Lat.IB f ξ
  have := dpE_mem_span f ξ l M (k := 1) le_rfl
  simpa [Lat.IB] using this

theorem dpow_dpA (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (i : ℕ) :
    (Lat.γ f ξ l M hc).dpow i (Lat.dpA f ξ l M 1) = Lat.dpA f ξ l M i := by
  apply Lat.ι_injective f ξ l M
  rw [Lat.ι_γ f ξ l M hc (dpA_one_mem f ξ l M), Lat.ι_dpA, Lat.ι_dpA]
  have hy : Lat.dpE f ξ l M 1 ∈ Lat.IB f ξ := dpA_one_mem f ξ l M
  rw [RatAlgebra.dpow_eq_inv_fact_smul _ (Lat.γB f ξ) hy, Ring.inverse_eq_inv']
  simp [Lat.dpE]

theorem dpA_mem_pdP (hl : l ≠ 0) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) {r i : ℕ} (hi : r ≤ i) :
    Lat.dpA f ξ l M i ∈ pdP (Lat.γ f ξ l M hc) r := by
  refine Ideal.subset_span ⟨[(i, Lat.dpA f ξ l M 1)], ?_, by simpa using hi, ?_⟩
  · intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact dpA_one_mem f ξ l M
  · simp [dpow_dpA f ξ l M hc i]

variable {f ξ l M}

theorem coeff_dvd {m j : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) (hj : j < m) (c : ℕ → W)
    (hy : ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)}) :
    ξ ∣ c j := by
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)] at hy
  have ht : ∑ i ∈ Finset.Ico (j + 1) (m + 1), f (c i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)} :=
    Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (dpE_mem_span f ξ l M (Finset.mem_Ico.1 hi).1)
  have hh := (Ideal.add_mem_iff_left _ ht).1 hy
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hh
  refine h.gr j hj (c j) ((dq l M j)⁻¹ • b) ?_
  rw [dpE_eq_smul, mul_smul_comm] at hb
  rw [mul_smul_comm, ← hb, smul_smul, inv_mul_cancel₀ (dq_ne_zero l M hl j), one_smul]

theorem push {m j : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) (hj : j < m) (c : ℕ → W) {y : B}
    (e : y = ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i)
    (hy : y ∈ Ideal.span {f ξ ^ (j + 1)}) :
    ∃ c' : ℕ → W, y = ∑ i ∈ Finset.Ico (j + 1) (m + 1), f (c' i) * Lat.dpE f ξ l M i := by
  obtain ⟨d, hd⟩ := coeff_dvd h hl hj c (M := M) (e ▸ hy)
  refine ⟨Function.update c (j + 1) (c (j + 1) + d * ((l : W) ^ M * ((j : W) + 1))), ?_⟩
  rw [e, Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_eq_sum_Ico_succ_bot (a := j + 1) (by omega),
    Finset.sum_eq_sum_Ico_succ_bot (a := j + 1) (by omega)]
  have hs : ∑ i ∈ Finset.Ico (j + 1 + 1) (m + 1), f (Function.update c (j + 1)
      (c (j + 1) + d * ((l : W) ^ M * ((j : W) + 1))) i) * Lat.dpE f ξ l M i =
      ∑ i ∈ Finset.Ico (j + 1 + 1) (m + 1), f (c i) * Lat.dpE f ξ l M i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (by have := (Finset.mem_Ico.1 hi).1; omega)]
  rw [hs, Function.update_self, hd, map_mul, mul_assoc, mul_left_comm (f ξ) (f d), GlobalTheory.CompanionTheory.LatDp.mul_divPow_eq f ξ l M hl j]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_one]
  ring

theorem exists_rep {m : ℕ} (hm : f ξ ^ m = 0) {y : B} (hy : y ∈ Lat.sub f ξ l M) :
    ∃ c : ℕ → W, y = ∑ i ∈ Finset.Ico 0 (m + 1), f (c i) * Lat.dpE f ξ l M i := by
  obtain ⟨n, c, rfl⟩ := (GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff f ξ l M y).1 hy
  refine ⟨fun i => if h : i < n then c ⟨i, h⟩ else 0, ?_⟩
  have h1 : ∑ i : Fin n, f (c i) * Lat.dpE f ξ l M i =
      ∑ i ∈ Finset.range n, f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [h1, Nat.Ico_zero_eq_range]
  have h2 := Finset.sum_subset (s₁ := Finset.range n) (s₂ := Finset.range (n + m + 1))
    (f := fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i _ hi => by simp only [Finset.mem_range] at hi; simp [hi])
  have h3 := Finset.sum_subset (s₁ := Finset.range (m + 1)) (s₂ := Finset.range (n + m + 1))
    (f := fun i => f (if h : i < n then c ⟨i, h⟩ else 0) * Lat.dpE f ξ l M i)
    (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    (fun i _ hi => by
      simp only [Finset.mem_range] at hi
      simp only [dpE_eq_zero f ξ l M hm (show m ≤ i by omega), mul_zero])
  exact h2.trans h3.symm

theorem exists_rep_high {m r : ℕ} (h : Lat.Hyp f ξ l m) (hl : l ≠ 0) {y : B} (hy : y ∈ Lat.sub f ξ l M)
    (hr : y ∈ Ideal.span {f ξ ^ r}) (j : ℕ) (hjr : j ≤ r) (hjm : j ≤ m) :
    ∃ c : ℕ → W, y = ∑ i ∈ Finset.Ico j (m + 1), f (c i) * Lat.dpE f ξ l M i := by
  induction j with
  | zero => exact exists_rep h.nil hy
  | succ j ih =>
    obtain ⟨c, e⟩ := ih (by omega) (by omega)
    have hle : Ideal.span {f ξ ^ r} ≤ Ideal.span {f ξ ^ (j + 1)} :=
      Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hjr)
    exact push h hl (by omega) c e (hle hr)

end

theorem dividedPowerFiltration_eq : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ r : ℕ,
    pdP (Lat.γ f ξ l M hc) r = (Ideal.span {f ξ ^ r}).comap (Lat.ι f ξ l M) := by
  intro W B _ _ _ f ξ l M m h hc r
  have hl : l ≠ 0 := fun e => h.l0 (by simp [e])
  apply le_antisymm
  · intro x hx
    have hdp : IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γB f ξ) (Lat.ι f ξ l M) :=
      ⟨Ideal.map_le_iff_le_comap.2 le_rfl, fun {n} a ha => (Lat.ι_γ f ξ l M hc ha).symm⟩
    have := dividedPowerFiltration_map hdp r hx
    rwa [GlobalTheory.CompanionTheory.DPFiltration.pdP_γB f ξ r] at this
  · intro x hx
    obtain ⟨c, e⟩ := exists_rep_high h hl (ι_mem f ξ l M x) hx (min r m) (by omega) (by omega)
    have hx' : x = ∑ i ∈ Finset.Ico (min r m) (m + 1), Lat.ofW f ξ l M (c i) * Lat.dpA f ξ l M i := by
      apply Lat.ι_injective f ξ l M
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Lat.ι_ofW, Lat.ι_dpA]
    rw [hx']
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    by_cases hir : r ≤ i
    · exact dpA_mem_pdP f ξ l M hl hc hir
    · have : Lat.dpA f ξ l M i = 0 := by
        apply Lat.ι_injective f ξ l M
        rw [Lat.ι_dpA, map_zero]
        exact dpE_eq_zero f ξ l M h.nil (by omega)
      rw [this]
      exact Ideal.zero_mem _

end GlobalTheory.CompanionTheory.LatPdpEq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeIdealIffSum
section
open DividedPowers CrystallineSemistableComparison.Pb

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatIdeal

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem dpE_succ_mem_IB (i : ℕ) : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
  have h1 : Lat.η f ξ l M ∈ Lat.IB f ξ := by
    unfold Lat.η Lat.IB
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  unfold Lat.dpE
  rw [Algebra.smul_def, pow_succ]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ h1)

theorem dpE_zero : Lat.dpE f ξ l M 0 = 1 := by
  unfold Lat.dpE
  rw [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]

private theorem dpE_mul_dpE_eq_choose_mul (a b : ℕ) :
    Lat.dpE f ξ l M a * Lat.dpE f ξ l M b =
      (((a + b).choose a : ℕ) : B) * Lat.dpE f ξ l M (a + b) := by
  have h0 : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
    rwa [Nat.add_sub_cancel_left] at h1
  have hC : (((a + b).choose a : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right a b)).ne'
  have key : ((a.factorial : ℚ))⁻¹ * ((b.factorial : ℚ))⁻¹ =
      (((a + b).choose a : ℕ) : ℚ) * (((a + b).factorial : ℕ) : ℚ)⁻¹ := by
    rw [← h0, Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ hC, one_mul]
  have key' : algebraMap ℚ B ((a.factorial : ℚ))⁻¹ * algebraMap ℚ B ((b.factorial : ℚ))⁻¹ =
      (((a + b).choose a : ℕ) : B) * algebraMap ℚ B (((a + b).factorial : ℕ) : ℚ)⁻¹ := by
    rw [← map_mul, key, map_mul, map_natCast]
  unfold Lat.dpE
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, pow_add]
  linear_combination (Lat.η f ξ l M ^ a * Lat.η f ξ l M ^ b) * key'

private theorem mul_mem_set_f_mul_dpE {y z : B}
    (hy : y ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k})
    (hz : z ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    y * z ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  obtain ⟨w, a, rfl⟩ := hy
  obtain ⟨w', b, rfl⟩ := hz
  refine ⟨w * w' * (((a + b).choose a : ℕ) : W), a + b, ?_⟩
  rw [map_mul, map_mul, map_natCast]
  linear_combination (f w * f w') * dpE_mul_dpE_eq_choose_mul f ξ l M a b

private theorem mul_mem_closure_f_mul_dpE {y z : B}
    (hy : y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k})
    (hz : z ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    y * z ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    induction hz using AddSubgroup.closure_induction with
    | mem z hz' => exact AddSubgroup.subset_closure (mul_mem_set_f_mul_dpE f ξ l M hy' hz')
    | zero => rw [mul_zero]; exact zero_mem _
    | add z1 z2 _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg z _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add y1 y2 _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg y _ h => rw [neg_mul]; exact neg_mem h

private theorem mem_closure_f_mul_dpE_of_mem_sub {y : B} (hy : y ∈ Lat.sub f ξ l M) :
    y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  unfold Lat.sub at hy
  induction hy using Subring.closure_induction with
  | mem y hy' =>
    apply AddSubgroup.subset_closure
    rcases hy' with ⟨w, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨w, 0, by rw [dpE_zero, mul_one]⟩
    · exact ⟨1, k, by rw [map_one, one_mul]⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, 0, by rw [dpE_zero, map_one, mul_one]⟩
  | add y z _ _ h1 h2 => exact add_mem h1 h2
  | neg y _ h => exact neg_mem h
  | mul y z _ _ h1 h2 => exact mul_mem_closure_f_mul_dpE f ξ l M h1 h2

private theorem exists_repr_of_mem_closure_f_mul_dpE {y : B}
    (hy : y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    ∃ (w₀ : W) (c : ℕ →₀ W), y = f w₀ + c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    obtain ⟨w, k, rfl⟩ := hy'
    cases k with
    | zero => exact ⟨w, 0, by rw [dpE_zero, mul_one, Finsupp.sum_zero_index, add_zero]⟩
    | succ j =>
      refine ⟨0, Finsupp.single j w, ?_⟩
      rw [map_zero, zero_add, Finsupp.sum_single_index]
      simp
  | zero => exact ⟨0, 0, by rw [map_zero, Finsupp.sum_zero_index, add_zero]⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, c, rfl⟩ := h1
    obtain ⟨b, d, rfl⟩ := h2
    refine ⟨a + b, c + d, ?_⟩
    rw [Finsupp.sum_add_index', map_add (f := _)]
    · ring
    · intro i
      simp
    · intro i b1 b2
      simp [add_mul]
  | neg y _ h =>
    obtain ⟨a, c, rfl⟩ := h
    refine ⟨-a, -c, ?_⟩
    rw [Finsupp.sum_neg_index, map_neg, neg_add]
    · simp only [map_neg, neg_mul, Finsupp.sum, Finset.sum_neg_distrib]
    · intro i
      simp

private theorem exists_fin_sum_eq_finsupp_sum_f_mul_dpE (c : ℕ →₀ W) :
    ∃ (n : ℕ) (c' : Fin n → W), c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) =
      ∑ i : Fin n, f (c' i) * Lat.dpE f ξ l M (i + 1) := by
  have hs : c.support ⊆ Finset.range (c.support.sup id + 1) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (f := id) hi
  refine ⟨c.support.sup id + 1, fun i => c i, ?_⟩
  rw [Finsupp.sum_of_support_subset c hs (fun i w => f w * Lat.dpE f ξ l M (i + 1))
    (fun _ _ => by simp)]
  exact (Fin.sum_univ_eq_sum_range (fun i => f (c i) * Lat.dpE f ξ l M (i + 1)) _).symm

private theorem f_xi_eq_f_pow_mul_dpE_one (hl : (l : ℚ) ≠ 0) :
    f ξ = f ((l : W) ^ M) * Lat.dpE f ξ l M 1 := by
  have h1 : Lat.dpE f ξ l M 1 = ((l : ℚ) ^ M)⁻¹ • f ξ := by
    unfold Lat.dpE Lat.η
    rw [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
  rw [h1, Algebra.smul_def, ← mul_assoc, map_pow, map_natCast,
    ← map_natCast (algebraMap ℚ B) l, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hl),
    map_one, one_mul]

private theorem finsupp_sum_add_single_zero_f_mul_dpE (c : ℕ →₀ W) (v : W) :
    (c + Finsupp.single 0 v).sum (fun i w => f w * Lat.dpE f ξ l M (i + 1))
      = c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) + f v * Lat.dpE f ξ l M 1 := by
  rw [Finsupp.sum_add_index', Finsupp.sum_single_index]
  all_goals simp [add_mul]

theorem mem_I_iff (m : ℕ) (H : Lat.Hyp f ξ l m) (x : Lat.A f ξ l M) :
    x ∈ Lat.I f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), Lat.ι f ξ l M x = ∑ i, f (c i) * Lat.dpE f ξ l M (i + 1) := by
  have hI : x ∈ Lat.I f ξ l M ↔ Lat.ι f ξ l M x ∈ Lat.IB f ξ := Iff.rfl
  rw [hI]
  constructor
  · intro hx
    have hsub : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := (x : ↥(Lat.sub f ξ l M)).2
    obtain ⟨w₀, c, hc⟩ := exists_repr_of_mem_closure_f_mul_dpE f ξ l M (mem_closure_f_mul_dpE_of_mem_sub f ξ l M hsub)
    have hS : c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) ∈ Lat.IB f ξ :=
      by
        unfold Finsupp.sum
        exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (dpE_succ_mem_IB f ξ l M i))
    have hw : f w₀ ∈ Lat.IB f ξ := by
      have h2 := sub_mem hx hS
      rwa [hc, add_sub_cancel_right] at h2
    unfold Lat.IB at hw
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hw
    obtain ⟨w', rfl⟩ := H.gr 0 H.one_le w₀ b
      (by rw [pow_zero, mul_one, zero_add, pow_one, ← hb, mul_comm])
    have hl : (l : ℚ) ≠ 0 := by
      intro h
      apply H.l0
      have h3 : l = 0 := by exact_mod_cast h
      rw [h3, Nat.cast_zero]
    obtain ⟨n, c', hc'⟩ := exists_fin_sum_eq_finsupp_sum_f_mul_dpE f ξ l M (c + Finsupp.single 0 ((l : W) ^ M * w'))
    refine ⟨n, c', ?_⟩
    rw [← hc', finsupp_sum_add_single_zero_f_mul_dpE f ξ l M, hc]
    simp only [map_mul]
    rw [f_xi_eq_f_pow_mul_dpE_one f ξ l M hl]
    ring
  · rintro ⟨n, c, hc⟩
    rw [hc]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (dpE_succ_mem_IB f ξ l M _))

end

theorem mem_I : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∈ Lat.I f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), Lat.ι f ξ l M x = ∑ i, f (c i) * Lat.dpE f ξ l M (i + 1) := by
  intro W B _ _ _ f ξ l M m H x
  exact mem_I_iff f ξ l M m H x

end GlobalTheory.CompanionTheory.LatIdeal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusJacobianDet
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

theorem dlog_ratio_det {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) :
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := by
  intro g
  set u : Fin (n + 1) → R := fun j => (((t j)⁻¹ : Rˣ) : R) with hu
  have htu : ∀ j, (t j : R) * u j = 1 := fun j => by simp [hu]
  have hDu : ∀ k j, D k (u j) = if k = j then -(u j * u j) else 0 := by
    intro k j
    have h2 := (D k).leibniz_of_mul_eq_one (a := u j) (b := (t j : R)) (by rw [mul_comm]; exact htu j)
    rw [h2, hD k j]
    split_ifs <;> simp [pow_two]
  have hg0 : g 0 = u 0 := by simp [g, hu]
  have hgs : ∀ (l : Fin (n + 1)) (h : (l : ℕ) ≠ 0), g l = (t ⟨l - 1, by omega⟩ : R) * u l := by
    intro l h
    exact dif_neg h
  have hgu : ∀ l, IsUnit (g l) := by
    intro l
    by_cases h : (l : ℕ) = 0
    · simp only [g, h, dite_true]; exact Units.isUnit _
    · simp only [g, h, dite_false]; exact (Units.isUnit _).mul (Units.isUnit _)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of fun k l => if k = l then -1 else if (k : ℕ) + 1 = l then 1 else 0
  have hM : (Matrix.of fun k l => D k (g l)) = Matrix.diagonal u * B * Matrix.diagonal g := by
    ext k l
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, B]
    by_cases h : (l : ℕ) = 0
    · have hl : l = 0 := Fin.ext h
      subst hl
      have hk : ¬ ((k : ℕ) + 1 = ((0 : Fin (n + 1)) : ℕ)) := by simp
      rw [hg0, hDu k 0]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · simp [hk0]
    · rw [hgs l h, Derivation.leibniz, hDu k l, hD k _]
      simp only [smul_eq_mul]
      by_cases hkl : k = l
      · subst hkl
        have hne : k ≠ ⟨(k : ℕ) - 1, by omega⟩ := by
          intro e
          have := congrArg Fin.val e
          simp at this
          omega
        simp only [if_true, hne, if_false]
        ring
      · by_cases hs : (k : ℕ) + 1 = l
        · have hp : k = ⟨(l : ℕ) - 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [if_neg hkl, if_pos hp, if_neg hkl, if_pos hs, ← hp]
          have := htu k
          linear_combination (-(u l)) * this
        · have hp : k ≠ ⟨(l : ℕ) - 1, by omega⟩ := by
            intro e
            have := congrArg Fin.val e
            simp at this
            omega
          rw [if_neg hkl, if_neg hp, if_neg hkl, if_neg hs]
          simp
  have hB : B.det = (-1) ^ (n + 1) := by
    rw [Matrix.det_of_upperTriangular]
    · simp [B]
    · intro i j hij
      have : (j : ℕ) < i := hij
      have h1 : i ≠ j := fun h => by simp [h] at this
      have h2 : ¬ ((i : ℕ) + 1 = j) := by omega
      simp [B, h1, h2]
  have hprod : ∏ k, u k = (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    simp only [hu, ← Units.coe_prod, Finset.prod_inv_distrib]
  have hU : IsUnit (∏ k, g k) := by
    obtain ⟨v, hv⟩ := IsUnit.prod_univ_iff.2 hgu
    exact hv ▸ v.isUnit
  have hcan : Ring.inverse (∏ k, g k) * (∏ k, g k) = 1 := Ring.inverse_mul_cancel _ hU
  have key : Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det =
      (-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hB, hprod]
    linear_combination ((-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R)) * hcan
  rcases neg_one_pow_eq_or R (n + 1) with h | h
  · left; rw [key, h, one_mul]
  · right; rw [key, h, neg_one_mul]

end GlobalTheory.CompanionTheory.Cone
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZKApply
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.BasisBase

def zK {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (Q : ObjectProperty (Thick (smFun X q))) (t u : ℤ) (ht : t ≤ 0) (j : ℕ) : HdR q j →ₗ[K] HQ Q t u j :=
  ((toSq (sFil Q t) (sFil Q u) fun T => by
    change T.obj.pdPow t.toNat = ⊤
    rw [Int.toNat_of_nonpos ht, Thick.pdPow_zero]).pull j).comp (resK q Q j)

end GlobalTheory.CompanionTheory.BasisBase
end
end

