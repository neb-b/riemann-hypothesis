module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.HasDerivAtDet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Matrix Equiv
open scoped ComplexOrder

noncomputable section

theorem LogDetDerivative.hasDerivAt_det {m : ℕ} {G : ℝ → Matrix (Fin m) (Fin m) ℂ}
    {G' : Matrix (Fin m) (Fin m) ℂ} {t : ℝ} (h : ∀ i j, HasDerivAt (fun s ↦ G s i j) (G' i j) t) :
    HasDerivAt (fun s ↦ (G s).det) (∑ i, (G t).cramer (fun k ↦ G' k i) i) t := by
  have key : ∀ σ : Perm (Fin m), HasDerivAt (fun s ↦ ((Perm.sign σ : ℤ) : ℂ) * ∏ i, G s (σ i) i)
      (((Perm.sign σ : ℤ) : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, G t (σ j) j) * G' (σ i) i) t := by
    intro σ
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s ↦ G s (σ i) i)
      (f' := fun i ↦ G' (σ i) i) (x := t) (fun i _ ↦ h (σ i) i)
    simpa [smul_eq_mul] using this.const_mul ((Perm.sign σ : ℤ) : ℂ)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ ↦ key σ)
  have hfun : (fun s ↦ (G s).det) =
      fun s ↦ ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℂ) * ∏ i, G s (σ i) i := by
    ext s
    exact det_apply' _
  rw [hfun]
  refine hsum.congr_deriv ?_
  symm
  rw [Finset.sum_congr rfl fun i _ ↦ cramer_apply (G t) (fun k ↦ G' k i) i]
  simp only [det_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i, (G t).updateCol i (fun k ↦ G' k i) (σ j) j =
      ∏ j ∈ Finset.univ.erase i, G t (σ j) j := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [updateCol_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, updateCol_self]
  ring

theorem LogDetDerivative.sum_cramer_eq {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (hA : IsUnit A.det) :
    ∑ i, A.cramer (fun k ↦ B k i) i = A.det * (A⁻¹ * B).trace := by
  simp only [← det_smul_inv_mulVec_eq_cramer A _ hA, Pi.smul_apply, smul_eq_mul, trace,
    diag_apply, Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum]

theorem LogDetDerivative.intersectionNumber_baseChange : LogDetDerivative.Statement := by
  intro m G G' hpos hG t
  have hdet := LogDetDerivative.hasDerivAt_det (hG t)
  rw [LogDetDerivative.sum_cramer_eq _ _ (hpos t).det_pos.ne'.isUnit] at hdet
  have hre : HasDerivAt (fun s ↦ (G s).det.re)
      ((G t).det * ((G t)⁻¹ * G' t).trace).re t := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hdet
  have hp := (hpos t).det_pos
  rw [Complex.lt_def] at hp
  obtain ⟨hre0, him0⟩ := hp
  simp only [Complex.zero_re, Complex.zero_im] at hre0 him0
  have hlog := (hre.log hre0.ne').const_mul (-(1 / 2) : ℝ)
  refine hlog.congr_deriv ?_
  rw [Complex.mul_re, ← him0, zero_mul, sub_zero]
  field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Finset Filter Asymptotics

theorem GridSum.choose_antidiagonal (m i j : ℕ) :
    ∑ p ∈ antidiagonal m, p.1.choose i * p.2.choose j = (m + 1).choose (i + j + 1) := by
  induction m generalizing i with
  | zero =>
    cases i <;> cases j <;> simp <;> exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ m ih =>
    rw [Finset.Nat.sum_antidiagonal_succ]
    cases i with
    | zero =>
      have h := ih 0
      simp only [Nat.choose_zero_right, one_mul, zero_add] at h ⊢
      rw [h, Nat.choose_succ_succ (m + 1) j]
    | succ i =>
      have h1 := ih i
      have h2 := ih (i + 1)
      have e : ∀ p : ℕ × ℕ, (p.1 + 1).choose (i + 1) * p.2.choose j =
          p.1.choose i * p.2.choose j + p.1.choose (i + 1) * p.2.choose j := fun p ↦ by
        rw [Nat.choose_succ_succ', add_mul]
      simp only [Nat.choose_zero_succ, zero_mul, zero_add, e, Finset.sum_add_distrib, h1, h2]
      rw [show i + 1 + j + 1 = (i + j + 1) + 1 by omega, Nat.choose_succ_succ' (m + 1) (i + j + 1)]

theorem GridSum.choose_range (n i j : ℕ) :
    ∑ a ∈ range n, a.choose i * (n - 1 - a).choose j = n.choose (i + j + 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [← GridSum.choose_antidiagonal m i j, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp

theorem GridSum.choose_le_pow_div_factorial (a i : ℕ) :
    (a.choose i : ℝ) ≤ (a : ℝ) ^ i / (i.factorial : ℝ) := by
  rw [le_div_iff₀ (by positivity)]
  have h : a.choose i * i.factorial ≤ a ^ i := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow a i
  exact_mod_cast h

theorem GridSum.pow_div_factorial_le (a i : ℕ) :
    (a : ℝ) ^ i / (i.factorial : ℝ) ≤ ((a + i).choose i : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  have h : a ^ i ≤ (a + i).choose i * i.factorial := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    calc a ^ i ≤ (a + i + 1 - i) ^ i := Nat.pow_le_pow_left (by omega) i
      _ ≤ (a + i).descFactorial i := Nat.pow_sub_le_descFactorial _ _
  exact_mod_cast h

theorem GridSum.pow_sub_pow_le (x y : ℝ) (k : ℕ) (hy : 0 ≤ y) (hxy : y ≤ x) :
    x ^ k - y ^ k ≤ k * (x - y) * x ^ (k - 1) := by
  rw [← geom_sum₂_mul]
  have hx : 0 ≤ x := hy.trans hxy
  have hs : ∑ l ∈ range k, x ^ l * y ^ (k - 1 - l) ≤ k * x ^ (k - 1) := by
    calc ∑ l ∈ range k, x ^ l * y ^ (k - 1 - l) ≤ ∑ l ∈ range k, x ^ (k - 1) := by
          apply sum_le_sum
          intro l hl
          have hl' : l + (k - 1 - l) = k - 1 := by have := mem_range.mp hl; omega
          calc x ^ l * y ^ (k - 1 - l) ≤ x ^ l * x ^ (k - 1 - l) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hxy _) (pow_nonneg hx _)
            _ = x ^ (k - 1) := by rw [← pow_add, hl']
      _ = k * x ^ (k - 1) := by simp
  have hd : 0 ≤ x - y := sub_nonneg.mpr hxy
  calc (∑ l ∈ range k, x ^ l * y ^ (k - 1 - l)) * (x - y) ≤ (k * x ^ (k - 1)) * (x - y) :=
        mul_le_mul_of_nonneg_right hs hd
    _ = k * (x - y) * x ^ (k - 1) := by ring

theorem GridSum.proof : GridSum.Statement := by
  intro D i hi
  set j := D - i with hj
  have hD : i + j + 1 = D + 1 := by omega
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF1 : (1 : ℝ) ≤ F := by
    rw [hFdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF : 0 < F := lt_of_lt_of_le one_pos hF1
  have lower : ∀ n : ℕ, ((n.choose (D + 1) : ℕ) : ℝ) ≤ ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) := by
    intro n
    have h := GridSum.choose_range n i j
    rw [hD] at h
    rw [← h, Nat.cast_sum]
    apply sum_le_sum
    intro a _
    rw [mul_div_mul_comm, Nat.cast_mul]
    exact mul_le_mul (GridSum.choose_le_pow_div_factorial _ _)
      (GridSum.choose_le_pow_div_factorial _ _) (by positivity) (by positivity)
  have upper : ∀ n : ℕ, ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) ≤
        (((n + D).choose (D + 1) : ℕ) : ℝ) := by
    intro n
    have h := GridSum.choose_range (n + D) i j
    rw [hD] at h
    rw [← h, Nat.cast_sum]
    calc ∑ a ∈ range n,
          (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ))
        ≤ ∑ a ∈ range n, (((a + i).choose i * (n + D - 1 - (a + i)).choose j : ℕ) : ℝ) := by
          apply sum_le_sum
          intro a ha
          have hb : n + D - 1 - (a + i) = (n - 1 - a) + j := by
            have := mem_range.mp ha; omega
          rw [hb, mul_div_mul_comm, Nat.cast_mul]
          exact mul_le_mul (GridSum.pow_div_factorial_le _ _)
            (GridSum.pow_div_factorial_le _ _) (by positivity) (by positivity)
      _ = ∑ a ∈ (range n).map (addRightEmbedding i),
            ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by
          rw [sum_map]; rfl
      _ ≤ ∑ a ∈ range (n + D), ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_map] at hx
            obtain ⟨a, ha, rfl⟩ := hx
            rw [mem_range] at ha ⊢
            change a + i < n + D
            omega
          · intros; positivity
  refine IsBigO.of_bound (((D + 1 : ℕ) : ℝ) * (2 * D) * 2 ^ D) ?_
  filter_upwards [eventually_ge_atTop D] with n hn
  have hL := lower n
  have hU := upper n
  set S := ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) with hS
  have hnD : (D : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n : ℝ) - D) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F := by
    have h : (n - D) ^ (D + 1) ≤ n.choose (D + 1) * (D + 1).factorial := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      have := Nat.pow_sub_le_descFactorial n (D + 1)
      rwa [show n + 1 - (D + 1) = n - D by omega] at this
    have h' : (((n - D : ℕ) : ℝ)) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F := by
      rw [hFdef]; exact_mod_cast h
    rwa [Nat.cast_sub hn] at h'
  have h2 : (((n + D).choose (D + 1) : ℕ) : ℝ) * F ≤ ((n : ℝ) + D) ^ (D + 1) := by
    have h : (n + D).choose (D + 1) * (D + 1).factorial ≤ (n + D) ^ (D + 1) := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow _ _
    rw [hFdef]; exact_mod_cast h
  have hSlo : ((n : ℝ) - D) ^ (D + 1) / F ≤ S := by
    rw [div_le_iff₀ hF]; nlinarith
  have hShi : S ≤ ((n : ℝ) + D) ^ (D + 1) / F := by
    rw [le_div_iff₀ hF]; nlinarith
  have hy : (0 : ℝ) ≤ (n : ℝ) - D := sub_nonneg.mpr hnD
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hp1 : ((n : ℝ) - D) ^ (D + 1) ≤ (n : ℝ) ^ (D + 1) :=
    pow_le_pow_left₀ hy (by linarith) _
  have hp2 : (n : ℝ) ^ (D + 1) ≤ ((n : ℝ) + D) ^ (D + 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) _
  have hgap := GridSum.pow_sub_pow_le ((n : ℝ) + D) ((n : ℝ) - D) (D + 1) hy (by linarith)
  rw [Nat.add_sub_cancel] at hgap
  have hpow : ((n : ℝ) + D) ^ D ≤ 2 ^ D * (n : ℝ) ^ D := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have habs : |S - (n : ℝ) ^ (D + 1) / F| ≤
      ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F := by
    rw [abs_le, sub_div]
    constructor
    · have : ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F := div_le_div_of_nonneg_right hp1 hF.le
      have : (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F := div_le_div_of_nonneg_right hp2 hF.le
      linarith
    · have : ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F := div_le_div_of_nonneg_right hp1 hF.le
      have : (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F := div_le_div_of_nonneg_right hp2 hF.le
      linarith
  have hnum : 0 ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := by linarith
  have hdiv : ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F ≤
      ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := div_le_self hnum hF1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ D)]
  have hk : (0 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) * (2 * D) := by positivity
  calc |S - (n : ℝ) ^ (D + 1) / F|
      ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := habs.trans hdiv
    _ ≤ ((D + 1 : ℕ) : ℝ) * ((n + D) - (n - D)) * ((n : ℝ) + D) ^ D := hgap
    _ = ((D + 1 : ℕ) : ℝ) * (2 * D) * ((n : ℝ) + D) ^ D := by ring
    _ ≤ ((D + 1 : ℕ) : ℝ) * (2 * D) * (2 ^ D * (n : ℝ) ^ D) := mul_le_mul_of_nonneg_left hpow hk
    _ = ((D + 1 : ℕ) : ℝ) * (2 * D) * 2 ^ D * (n : ℝ) ^ D := by ring

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMinkowskiCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Module Metric
open scoped ENNReal

noncomputable section

namespace MinkowskiCount

section Count

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


omit [MeasurableSpace V] [BorelSpace V] in
theorem finite_latticePoints (La : Submodule ℤ V) [DiscreteTopology La] (ρ : ℝ) :
    {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.Finite := by
  have h : {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} = closedBall 0 ρ ∩ (La : Set V) := by
    ext x; simp [and_comm]
  rw [h]
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

theorem unitBallVolume_pos (R : ℕ) : 0 < unitBallVolume R :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

theorem volume_ball_one :
    volume (ball (0 : V) 1) = ENNReal.ofReal (unitBallVolume (finrank ℝ V)) := by
  rw [unitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne,
    ← (stdOrthonormalBasis ℝ V).measurePreserving_repr.measure_preimage
      measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem volume_ball_half_le (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ) {F : Set V}
    (fund : IsAddFundamentalDomain La F volume) :
    volume (ball (0 : V) (ρ / 2)) ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ≥0∞) * volume F := by
  have : MeasurableVAdd La V := (inferInstance : MeasurableVAdd La.toAddSubgroup V)
  have : VAddInvariantMeasure La V volume :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup V volume)
  have : Countable La := inferInstance
  set S := ball (0 : V) (ρ / 2) with hSdef
  set A := {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} with hAdef
  have hS : MeasurableSet S := measurableSet_ball
  have key : ∀ y : V, ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) ≤ (A.ncard : ℝ≥0∞) := by
    intro y
    set T : Set La := {g | (g : V) + y ∈ S} with hTdef
    have h1 : ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) =
        ∑' g : La, T.indicator (1 : La → ℝ≥0∞) g := by
      congr 1
    rw [h1, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    have hA : (A.ncard : ℝ≥0∞) = ((A.encard : ℕ∞) : ℝ≥0∞) := by
      rw [← (finite_latticePoints La ρ).cast_ncard_eq]; rfl
    rw [hA]
    refine ENat.toENNReal_le.mpr ?_
    rcases T.eq_empty_or_nonempty with hT | ⟨g₀, hg₀⟩
    · simp [hT]
    refine Set.encard_le_encard_of_injOn (f := fun g : La => (g : V) - g₀) ?_ ?_
    · intro g hg
      refine ⟨La.sub_mem g.2 g₀.2, ?_⟩
      have hg' : ‖(g : V) + y‖ < ρ / 2 := by simpa [T, S] using hg
      have hg₀' : ‖(g₀ : V) + y‖ < ρ / 2 := by simpa [T, S] using hg₀
      have : (g : V) - g₀ = ((g : V) + y) - ((g₀ : V) + y) := by abel
      show ‖(g : V) - g₀‖ ≤ ρ
      rw [this]
      linarith [norm_sub_le ((g : V) + y) ((g₀ : V) + y)]
    · intro g _ g' _ h
      exact Subtype.ext (sub_left_injective h)
  calc volume S = ∫⁻ z, S.indicator 1 z := (lintegral_indicator_one hS).symm
    _ = ∑' g : La, ∫⁻ z in F, S.indicator 1 (g +ᵥ z) := fund.lintegral_eq_tsum'' _
    _ = ∫⁻ z in F, ∑' g : La, S.indicator 1 (g +ᵥ z) :=
        (lintegral_tsum fun g => ((measurable_one.indicator hS).comp
          (measurable_const_vadd g)).aemeasurable).symm
    _ ≤ ∫⁻ _ in F, (A.ncard : ℝ≥0∞) := lintegral_mono fun z => key z
    _ = A.ncard * volume F := setLIntegral_const _ _

theorem log_count (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ)
    (hρ : 0 < ρ) :
    Real.log (unitBallVolume (finrank ℝ V)) + (finrank ℝ V : ℝ) * Real.log (ρ / 2) -
        Real.log (ZLattice.covolume La) ≤
      Real.log ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
  set b := Module.Free.chooseBasis ℤ La
  have fund := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain La volume fund
  have hFtop : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hle := volume_ball_half_le La ρ fund
  rw [Measure.addHaar_ball_of_pos volume 0 (half_pos hρ), volume_ball_one] at hle
  have hle' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFtop) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (unitBallVolume_pos _).le, ENNReal.toReal_natCast, ← measureReal_def,
    ← hcov] at hle'
  have hcpos := ZLattice.covolume_pos La volume
  have hN : 0 < ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
    have : 0 < {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard :=
      (Set.ncard_pos (finite_latticePoints La ρ)).mpr ⟨0, La.zero_mem, by simp [hρ.le]⟩
    exact_mod_cast this
  have hdiv : (ρ / 2) ^ finrank ℝ V * unitBallVolume (finrank ℝ V) / ZLattice.covolume La ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := (div_le_iff₀ hcpos).mpr hle'
  have hlog := Real.log_le_log (by have := unitBallVolume_pos (finrank ℝ V); positivity) hdiv
  rw [Real.log_div (by have := unitBallVolume_pos (finrank ℝ V); positivity) hcpos.ne',
    Real.log_mul (by positivity) (unitBallVolume_pos _).ne', Real.log_pow] at hlog
  linarith

end Count

theorem cube_le_unitBallVolume (R : ℕ) : (2 / Real.sqrt R) ^ R ≤ unitBallVolume R := by
  set a := 1 / Real.sqrt R with ha_def
  have ha : 0 ≤ a := by positivity
  have hsub : (WithLp.ofLp : EuclideanSpace ℝ (Fin R) → Fin R → ℝ) ⁻¹'
      (Set.univ.pi fun _ => Set.Ioo (-a) a) ⊆ ball 0 1 := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo] at hx
    rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_lt' one_pos, one_pow]
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp
    · calc ∑ i, ‖x i‖ ^ 2 < ∑ _i : Fin R, a ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨⟨0, hR⟩, Finset.mem_univ _⟩ fun i _ => by
              rw [Real.norm_eq_abs, sq_abs]
              exact sq_lt_sq' (hx i).1 (hx i).2
        _ = 1 := by
          have hR' : (0 : ℝ) < R := by exact_mod_cast hR
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ha_def,
            div_pow, one_pow, Real.sq_sqrt hR'.le]
          field_simp
  have hvol := measure_mono (μ := volume) hsub
  rw [(PiLp.volume_preserving_ofLp (Fin R)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    at hvol
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hvol
  have h := ENNReal.toReal_mono measure_ball_lt_top.ne hvol
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at h
  have h2 : 2 / Real.sqrt R = a + a := by rw [ha_def]; ring
  rw [h2]
  exact h

theorem proof : MinkowskiCount.Statement :=
  ⟨fun _ _ _ _ _ _ La _ _ ρ hρ => log_count La ρ hρ, cube_le_unitBallVolume⟩

end MinkowskiCount

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegrePrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type) [Field F]

theorem segreMap_monomial_isMultiHomog (d : ((_ : Unit) × ((k : K) → ι k)) →₀ ℕ) (a : F) :
    IsMultiHomog (segreMap F (monomial d a))
      (fun _ => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()) := by
  unfold IsMultiHomog
  rw [segreMap, aeval_monomial, algebraMap_eq, Finsupp.prod]
  refine IsWeightedHomogeneous.C_mul ?_ a
  have hX : ∀ v : (_ : Unit) × ((k : K) → ι k),
      IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1) := by
    intro v
    have := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => Pi.single k 1)
      (fun k _ => isWeightedHomogeneous_X F _ _)
    convert this using 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have := IsWeightedHomogeneous.prod d.support
    (fun v => (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) ^ d v) (fun v => d v • (fun _ : K => (1 : ℕ)))
    (fun v _ => (hX v).pow _)
  have e : (fun _ : K => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()) =
      ∑ v ∈ d.support, d v • (fun _ : K => (1 : ℕ)) := by
    ext j
    simp [Finsupp.weight_apply, Finsupp.sum, blockWeight, Finset.sum_apply]
  rw [e]
  exact this

theorem segreMap_weightedHomogeneousComponent [Nonempty K] (b : Unit → ℕ)
    (g : MRing (fun _ : Unit => ∀ k, ι k) F) :
    segreMap F (weightedHomogeneousComponent (blockWeight (fun _ : Unit => ∀ k, ι k)) b g) =
      weightedHomogeneousComponent (blockWeight ι) (fun _ => b ()) (segreMap F g) := by
  classical
  induction g using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := isWeightedHomogeneous_monomial (blockWeight (fun _ : Unit => ∀ k, ι k)) d a rfl
    rw [weightedHomogeneousComponent_of_mem h1,
      weightedHomogeneousComponent_of_mem (segreMap_monomial_isMultiHomog F d a)]
    have key : b = Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ↔
        (fun _ : K => b ()) = fun _ => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d () := by
      constructor
      · rintro rfl; rfl
      · intro h; funext u; cases u; exact congr_fun h (Classical.arbitrary K)
    by_cases h : b = Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d
    · rw [if_pos h, if_pos (key.mp h)]
    · rw [if_neg h, if_neg (mt key.mpr h), map_zero]
  | add p p' hp hp' => simp only [map_add (f := _), hp, hp']

theorem SegrePrime.proof : SegrePrime.Statement := by
  intro F _ K _ _ _ ι _ q hq
  have := hq.isPrime
  refine ⟨segrePrime.isPrime F q, ?_, ?_⟩
  · intro g hg b
    rw [segrePrime, Ideal.mem_comap] at hg ⊢
    rw [segreMap_weightedHomogeneousComponent]
    exact hq.multiHomog _ hg _
  · intro u
    cases u
    choose i hi using hq.relevant
    refine ⟨i, ?_⟩
    rw [segrePrime, Ideal.mem_comap, segreMap_X, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, _, hk⟩
    exact hi k hk

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

