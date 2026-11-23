module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoincareSeriesMeasurability.FoldL2DoubleCoset
public import Formalism.PeriodIntegrals.Bundle0015
public import Formalism.PeriodIntegrals.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkipSuccessorIndex.SkipSucc2
public import Formalism.PeriodIntegrals.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardCharacterTrace.SumEmbeddingEqTrace
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittLogarithm.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesMemLp
section
theorem fold_l2_bound_b (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesMemLp G μ :=
  PI.PoincareSeriesMemLp.UnitaryGroupMassFormula.fold_L2_double_coset G μ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmColExp
section
private theorem bijective_cycleRange_symm_mul_decomposeFin_symm (t : ℕ) :
    Function.Bijective (fun p : Fin (t + 1) × Equiv.Perm (Fin t) =>
      (Fin.cycleRange p.1).symm * Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), p.2)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨l, τ⟩ ⟨l', τ'⟩ h
    simp only at h
    have h0 := congrArg (fun σ : Equiv.Perm (Fin (t + 1)) => σ 0) h
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_zero,
      Fin.cycleRange_symm_zero] at h0
    subst h0
    have h1 := mul_left_cancel h
    have h2 := Equiv.Perm.decomposeFin.symm.injective h1
    simp only [Prod.mk.injEq, true_and] at h2
    rw [h2]
  · simp [Fintype.card_perm, Nat.factorial_succ]

private theorem sum_perm_succ_eq_sum_cycleRange_decomposeFin {M : Type*} [AddCommMonoid M] (t : ℕ) (g : Equiv.Perm (Fin (t + 1)) → M) :
    ∑ σ, g σ = ∑ l : Fin (t + 1), ∑ τ : Equiv.Perm (Fin t),
      g ((Fin.cycleRange l).symm * Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (bijective_cycleRange_symm_mul_decomposeFin_symm t) _ _ (fun _ => rfl)).symm

private theorem sign_cycleRange_symm_mul_decomposeFin_symm (t : ℕ) (l : Fin (t + 1)) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign ((Fin.cycleRange l).symm *
        Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ)) : ℤˣ) : ℤ)
      = (-1) ^ (l : ℕ) * (Equiv.Perm.sign τ : ℤ) := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign]
  simp

private theorem sign_cycleRange_symm_mul_decomposeFin_mul_finRotate (t : ℕ) (l : Fin (t + 1)) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign ((Fin.cycleRange l).symm *
        Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ) * finRotate (t + 1)) : ℤˣ) : ℤ)
      = (-1) ^ (t + (l : ℕ)) * (Equiv.Perm.sign τ : ℤ) := by
  rw [Equiv.Perm.sign_mul, Units.val_mul, sign_cycleRange_symm_mul_decomposeFin_symm, sign_finRotate]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    add_tsub_cancel_right, add_tsub_cancel_left]
  ring

private theorem qminor_eq_sum_expand_first_column {A : Type} [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
      (Formalism.REAL.Tm E u (a l) (b 0) *
        Formalism.REAL.qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (u - 1)) := by
  unfold Formalism.REAL.qminor
  rw [sum_perm_succ_eq_sum_cycleRange_decomposeFin]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [sign_cycleRange_symm_mul_decomposeFin_symm, List.ofFn_succ, List.prod_cons]
  have hs : ∀ k : Fin t, u - ((k : ℂ) + 1) = u - 1 - (k : ℂ) := fun k => by ring
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_zero,
    Fin.cycleRange_symm_zero, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
    Equiv.refl_apply, Fin.cycleRange_symm_succ, Function.comp_apply, Fin.val_zero,
    Nat.cast_zero, sub_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one, hs]
  rw [Int.cast_mul, mul_assoc]
  congr 1
  rw [← mul_assoc, (Int.cast_commute ((Equiv.Perm.sign τ : ℤˣ) : ℤ)
    (Formalism.REAL.Tm E u (a l) (b 0))).eq, mul_assoc]

private theorem qminor_eq_sum_expand_last_column {A : Type} [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
      (Formalism.REAL.qminor E (a ∘ l.succAbove) (b ∘ Fin.castSucc) u *
        Formalism.REAL.Tm E (u - (t : ℂ)) (a l) (b (Fin.last t))) := by
  unfold Formalism.REAL.qminor
  rw [← Equiv.sum_comp (Equiv.mulRight (finRotate (t + 1))), sum_perm_succ_eq_sum_cycleRange_decomposeFin]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Equiv.coe_mulRight]
  rw [sign_cycleRange_symm_mul_decomposeFin_mul_finRotate, List.ofFn_succ', List.prod_concat]
  simp only [Equiv.Perm.mul_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.last_add_one,
    Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
    Fin.cycleRange_symm_succ, Function.comp_apply, Fin.coe_castSucc, Fin.val_last]
  rw [Int.cast_mul]
  simp only [mul_assoc]

theorem quantum_minor_column_expansion : PI.QmColExp := by
  delta PI.QmColExp PI.ExpFirstCol PI.ExpLastCol
  exact ⟨fun A _ _ n t E a b u => qminor_eq_sum_expand_first_column n t E a b u,
    fun A _ _ n t E a b u => qminor_eq_sum_expand_last_column n t E a b u⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmSkip
section
theorem quantum_minor_skip : PI.QmSkip := by
  have hsa : ∀ {n : ℕ} (p : Fin (n + 1)) (k : Fin n),
      (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
    intro n p k
    unfold Fin.succAbove
    split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]
  refine ⟨fun t i j => ?_, fun t i i' j hii' => ?_⟩
  · apply Fin.ext
    have e := hsa i j
    unfold PI.skip1
    split_ifs at e ⊢ <;> simp only at * <;> omega
  · apply Fin.ext
    have e1 := hsa i i'
    have e2 := hsa i' j
    have e3 := hsa i (i'.succAbove j)
    rw [if_neg (by omega)] at e1
    unfold PI.skip2
    split_ifs at e2 e3 ⊢ <;> simp only at * <;> omega
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StdCharTR
section
theorem stdCharTR : PI.StdCharTR.Target :=
  PI.StdCharTRWork.stdCharTR_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittLogarithm
section
private lemma inv_series_sub : PI.InvSerSub := by
  intro K _ S l ex hl hl0 hl1 hex0 hsub n
  obtain ⟨c, hc⟩ := PowerSeries.X_dvd_iff.2 hex0
  have hpow : ∀ d m, PowerSeries.coeff m (ex ^ d) =
      if d ≤ m then PowerSeries.coeff (m - d) (c ^ d) else 0 := by
    intro d m
    rw [hc, mul_pow, PowerSeries.coeff_X_pow_mul']
  have hcoef : ∀ j, PowerSeries.coeff j c = PowerSeries.coeff (j + 1) ex := by
    intro j
    rw [hc, PowerSeries.coeff_succ_X_mul]
  have hHS : PowerSeries.HasSubst ex := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hex0]; exact IsNilpotent.zero)
  have key : ∀ m, PowerSeries.coeff m (PowerSeries.X : PowerSeries K) =
      ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l * PowerSeries.coeff m (ex ^ d) := by
    intro m
    have hfin : (∑ᶠ d, PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d)) =
        ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d) := by
      apply finsum_eq_sum_of_support_subset
      intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [hpow, if_neg (by omega), smul_zero]
    rw [← hsub, PowerSeries.coeff_subst' hHS, hfin]
    simp only [smul_eq_mul]

  have hB : ∀ N, (∀ j ≤ N, PowerSeries.coeff j c ∈ S) →
      ∀ d, ∀ i ≤ N, PowerSeries.coeff i (c ^ d) ∈ S := by
    intro N hN d
    induction d with
    | zero =>
      intro i _
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    | succ d ihd =>
      intro i hi
      rw [pow_succ, PowerSeries.coeff_mul]
      apply Subring.sum_mem
      intro p hp
      have h : p.1 + p.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      exact S.mul_mem (ihd _ (by omega)) (hN _ (by omega))
  have hl0' : PowerSeries.coeff 0 l = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hl0]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hex0]
      exact S.zero_mem
    · have k := key (n + 1)
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at k
      simp only [zero_add, pow_one, hl1, one_mul, hl0', zero_mul, add_zero] at k
      have he : PowerSeries.coeff (n + 1) ex = PowerSeries.coeff (n + 1) (PowerSeries.X : PowerSeries K) -
          ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1 + 1) l *
            PowerSeries.coeff (n + 1) (ex ^ (i + 1 + 1)) := by
        rw [k]
        ring
      rw [he]
      apply S.sub_mem
      · rw [PowerSeries.coeff_X]
        split_ifs
        · exact S.one_mem
        · exact S.zero_mem
      · apply Subring.sum_mem
        intro i hi
        rw [Finset.mem_range] at hi
        apply S.mul_mem (hl _)
        rw [hpow]
        split_ifs with hle
        · apply hB (n - 1) _ (i + 1 + 1) _ (by omega)
          intro j hj
          rw [hcoef]
          exact ih _ (by omega)
        · exact S.zero_mem

theorem witt_logarithm : PI.WfLog :=
  PI.WfLogWork.wfLog_of inv_series_sub PI.WfLogWork.formal_logarithm_holds
end

