module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.AbsLeA

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.MtInvUpper
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.TwSMInt2

open PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem sum_meas_le {α β : Type*} [MeasurableSpace α] (μ : Measure α) (F : Finset β) (A : β → Set α)
    (hA : ∀ b, MeasurableSet (A b)) {Y : Set α} (hY : MeasurableSet Y) (hsub : ∀ b ∈ F, A b ⊆ Y) (R : ℕ)
    (hR : ∀ x, ∀ S : Finset β, S ⊆ F → (∀ b ∈ S, x ∈ A b) → S.card ≤ R) : ∑ b ∈ F, μ (A b) ≤ R * μ Y := by
  classical
  have e1 : ∑ b ∈ F, μ (A b) = ∫⁻ x, ∑ b ∈ F, (A b).indicator (1 : α → ℝ≥0∞) x ∂μ := by
    rw [lintegral_finsetSum _ fun b _ => measurable_one.indicator (hA b)]
    exact Finset.sum_congr rfl fun b _ => (lintegral_indicator_one (hA b)).symm
  have e2 : (R : ℝ≥0∞) * μ Y = ∫⁻ x, Y.indicator (fun _ => (R : ℝ≥0∞)) x ∂μ := (lintegral_indicator_const hY _).symm
  rw [e1, e2]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ Y
  · rw [Set.indicator_of_mem hx]
    have : ∑ b ∈ F, (A b).indicator (1 : α → ℝ≥0∞) x = ((F.filter fun b => x ∈ A b).card : ℝ≥0∞) := by
      simp [Set.indicator_apply]
    rw [this]
    exact Nat.cast_le.2 (by
      convert hR x (F.filter fun b => x ∈ A b) (Finset.filter_subset _ _) fun b hb => (Finset.mem_filter.1 hb).2)
  · rw [Set.indicator_of_notMem hx]
    refine (Finset.sum_eq_zero fun b hb => Set.indicator_of_notMem (fun h => hx (hsub b hb h)) _).le

theorem mt_mul' (a b : G ι N) (w : ι) : mt (a * b) w = mt a w * mt b w := rfl

theorem mt_nu_same (w0 : ι) (c : SpecialLinearGroup (Fin N) GaussianInt) :
    mt (nu w0 c) w0 = (c : Matrix (Fin N) (Fin N) GaussianInt).map GaussianInt.toComplex := by
  classical
  simp only [MomentRationality.Cz.Pk.mt, nu, MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
  rfl

theorem mt_nu_ne {w0 w : ι} (h : w ≠ w0) (c : SpecialLinearGroup (Fin N) GaussianInt) :
    mt (nu w0 c) w = 1 := by
  classical
  simp only [MomentRationality.Cz.Pk.mt, nu, MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]
  rfl

theorem mt_inv_upper {a : G ι N} {w : ι} (h : (mt a w).BlockTriangular id) : (mt a⁻¹ w).BlockTriangular id := by
  have h1 : mt a⁻¹ w * mt a w = 1 := by rw [← mt_mul', inv_mul_cancel]; rfl
  haveI : Invertible (mt a w) := invertibleOfLeftInverse _ _ h1
  rw [← Matrix.inv_eq_left_inv h1]
  exact blockTriangular_inv_of_blockTriangular h

theorem mt_inv_unit {a : G ι N} {w : ι} (h : mt a w ∈ unitaryGroup (Fin N) ℂ) : mt a⁻¹ w ∈ unitaryGroup (Fin N) ℂ := by
  have h1 : mt a⁻¹ w * mt a w = 1 := by rw [← mt_mul', inv_mul_cancel]; rfl
  rw [← Matrix.inv_eq_left_inv h1, Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 h)]
  exact Unitary.star_mem h

theorem pack [Fintype ι] [Nonempty ι] [MeasurableSpace (G ι N)] [BorelSpace (G ι N)] (μ : Measure (G ι N))
    [μ.IsHaarMeasure] {P : Set (G ι N)} (hPc : IsCompact P) (M T : ℝ) (hP : P ⊆ PB M) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (m : Fin N → ℤ) (s0 : Fin N → ℝ), ∑ i, s0 i = 0 → Cone T s0 →
      (∀ i, (m i : ℝ) ≤ s0 i ∧ s0 i ≤ m i + 1) →
      μ (Xb P T m) ≤ K * ENNReal.ofReal (Real.exp (-2 * Phi s0)) := by
  classical
  obtain ⟨w0⟩ := ‹Nonempty ι›
  obtain ⟨R0, hR0⟩ := tri (N := N) M
  obtain ⟨R, hR⟩ := fin_bdd (N := N) R0
  obtain ⟨R1, hR1⟩ := env (N := N) M T
  refine ⟨R * μ (Zb R1), ENNReal.mul_ne_top (ENNReal.natCast_ne_top R) (cpt_Z R1).measure_lt_top.ne, ?_⟩
  intro m s0 hs0 hc0 hm0
  obtain ⟨F, hF, hcard⟩ := count s0
  have hs0' : ∑ i, (-s0 i) = 0 := by rw [Finset.sum_neg_distrib, hs0, neg_zero]
  have hXm : MeasurableSet (Xb P T m) := (cpt_X hPc T m).measurableSet
  have hZm : MeasurableSet (Zb (ι := ι) (N := N) R1) := (cpt_Z R1).measurableSet
  have hclose : ∀ s s' : Fin N → ℝ, (∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1) →
      (∀ i, (m i : ℝ) ≤ s' i ∧ s' i ≤ m i + 1) → ∀ i, |s i - s' i| ≤ 1 := by
    intro s s' h h' i
    have := h i; have := h' i
    rw [abs_le]; constructor <;> linarith
  have key := sum_meas_le μ F (fun c => (fun x => (nu w0 c)⁻¹ * x) ⁻¹' Xb P T m)
    (fun c => measurable_const_mul _ hXm)
    (Y := (fun x => (dg (fun i => -s0 i) hs0' : G ι N) * x) ⁻¹' Zb R1) (measurable_const_mul _ hZm) ?_ R ?_
  · simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul] at key
    have h1 : ENNReal.ofReal (Real.exp (2 * Phi s0)) * μ (Xb P T m) ≤ R * μ (Zb R1) :=
      (mul_le_mul' hcard le_rfl).trans key
    have h2 : ENNReal.ofReal (Real.exp (2 * Phi s0)) * ENNReal.ofReal (Real.exp (-2 * Phi s0)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      simp
    calc μ (Xb P T m) = (ENNReal.ofReal (Real.exp (2 * Phi s0)) * μ (Xb P T m)) *
          ENNReal.ofReal (Real.exp (-2 * Phi s0)) := by rw [mul_right_comm, h2, one_mul]
      _ ≤ _ := mul_le_mul' h1 le_rfl
  · rintro c hc x ⟨p, hp, s, hs, -, hm, k, hk, hx⟩ w i j
    have hx' : x = nu w0 c * p * dg s hs * k := by
      have : x = nu w0 c * ((nu w0 c)⁻¹ * x) := by group
      rw [this]; dsimp only at hx; rw [hx]; simp only [mul_assoc]
    rw [hx']
    have hn : (mt (nu w0 c) w).BlockTriangular id ∧
        ∀ i j, i ≤ j → ‖mt (nu w0 c) w i j‖ ≤ 2 * Real.exp (s0 i - s0 j) := by
      by_cases hw : w = w0
      · subst hw; rw [mt_nu_same]; exact hF c hc
      · rw [mt_nu_ne hw]
        refine ⟨blockTriangular_one, fun i j _ => ?_⟩
        by_cases hij : i = j
        · subst hij; simp
        · rw [one_apply_ne hij, norm_zero]; positivity
    exact hR1 _ _ _ s0 s hc0 (hclose _ _ hm hm0) hn.1 hn.2 (hP hp w).1 (hP hp w).2 (hk w) i j
  · intro x S hS hx
    refine hR S fun c hc c' hc' i j => ?_
    obtain ⟨p, hp, s, hs, -, hm, k, hk, e⟩ := hx c hc
    obtain ⟨p', hp', s', hs', -, hm', k', hk', e'⟩ := hx c' hc'
    dsimp only at e e'
    have hE : nu w0 (c⁻¹ * c') * p' * dg s' hs' = p * dg s hs * (k * k'⁻¹) := by
      have a1 : p' * dg s' hs' = (nu w0 c')⁻¹ * x * k'⁻¹ := by rw [e']; group
      rw [mul_assoc, a1, ← mul_assoc (p * dg s hs), ← e, map_mul, map_inv]; group
    have hup : (mt (nu w0 (c⁻¹ * c')) w0).BlockTriangular id := by
      rw [map_mul, map_inv, mt_mul']
      refine (mt_inv_upper ?_).mul ?_
      · rw [mt_nu_same]; exact (hF c (hS hc)).1
      · rw [mt_nu_same]; exact (hF c' (hS hc')).1
    have := hR0 (mt (nu w0 (c⁻¹ * c')) w0) (mt p' w0) (mt p w0) (mt (k * k'⁻¹) w0) s' s (hclose _ _ hm' hm) hup
      (hP hp' w0).1 (hP hp w0).1 (hP hp' w0).2 (hP hp w0).2 (p' w0).2 (p w0).2
      (by rw [mt_mul']; exact mul_mem (hk w0) (mt_inv_unit (hk' w0))) (congrArg (fun y => mt y w0) hE) i j
    rw [mt_nu_same] at this
    exact this

end PositivityTheory.KB.TwSMInt2

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SetLIntegralLeOfMul
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.TwSMInt2

open PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem setLIntegral_le_of_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) {X : Set α} (hX : MeasurableSet X)
    (f : α → ℝ≥0∞) (D : ℝ≥0∞) (h : ∀ x ∈ X, f x * μ X ≤ D) : ∫⁻ x in X, f x ∂μ ≤ D := by
  rcases eq_or_ne (μ X) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.mpr h0]
  rcases eq_or_ne D ⊤ with hD | hD
  · simp [hD]
  rcases eq_or_ne (μ X) ⊤ with htop | htop
  · have hz : ∀ x ∈ X, f x = 0 := by
      intro x hx
      by_contra hne
      have := h x hx
      rw [htop, ENNReal.mul_top hne] at this
      exact hD (top_le_iff.mp this)
    calc ∫⁻ x in X, f x ∂μ = ∫⁻ _ in X, 0 ∂μ := setLIntegral_congr_fun hX hz
      _ = 0 := lintegral_zero
      _ ≤ D := bot_le
  · have hle : ∀ x ∈ X, f x ≤ D / μ X := fun x hx =>
      (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop)).mpr (h x hx)
    calc ∫⁻ x in X, f x ∂μ ≤ ∫⁻ _ in X, D / μ X ∂μ := setLIntegral_mono' hX hle
      _ = D / μ X * μ X := setLIntegral_const X _
      _ = D := ENNReal.div_mul_cancel h0 htop

theorem main_of_pack (hN : 2 ≤ N) [Fintype ι] [Nonempty ι] [MeasurableSpace (G ι N)] [BorelSpace (G ι N)]
    (μ : Measure (G ι N)) [μ.IsHaarMeasure] {P : Set (G ι N)} (hPc : IsCompact P)
    (T B : ℝ) (hpk : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (m : Fin N → ℤ) (s0 : Fin N → ℝ), ∑ i, s0 i = 0 → Cone T s0 →
      (∀ i, (m i : ℝ) ≤ s0 i ∧ s0 i ≤ m i + 1) →
      μ (Xb P T m) ≤ K * ENNReal.ofReal (Real.exp (-2 * Phi s0))) (hB : B < 2 * ((N : ℝ) - 1)) (C : ℝ≥0∞) (hC : C ≠ ⊤) (f : G ι N → ℝ≥0∞)
    (hf : ∀ p ∈ P, ∀ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), Cone T s → ∀ k ∈ KS,
      f (p * dg s hs * k) ≤ C * ENNReal.ofReal (Real.exp (B * W s))) :
    ∫⁻ x in Sg P T, f x ∂μ < ⊤ := by
  obtain ⟨K, hK, hμ⟩ := hpk
  obtain ⟨c, ε, hε, hexp⟩ := ineq hN T B hB
  set D : (Fin N → ℤ) → ℝ≥0∞ := fun m => C * K * (ENNReal.ofReal (Real.exp (c + ε * N)) *
    ENNReal.ofReal (Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|)))) with hD
  have hcov : Sg P T ⊆ ⋃ m, Xb P T m := by
    rintro x ⟨p, hp, s, hs, hcone, k, hk, rfl⟩
    refine Set.mem_iUnion.mpr ⟨fun i => ⌊s i⌋, p, hp, s, hs, hcone, fun i => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩, k, hk, rfl⟩
  have hpiece : ∀ m, ∫⁻ x in Xb P T m, f x ∂μ ≤ D m := by
    intro m
    refine setLIntegral_le_of_mul μ (cpt_X hPc T m).measurableSet f (D m) ?_
    rintro x ⟨p, hp, s, hs, hcone, hb, k, hk, rfl⟩
    have h1 := hf p hp s hs hcone k hk
    have h2 := hμ m s hs hcone hb
    have habs : ∑ i, |((m i : ℤ) : ℝ)| ≤ ∑ i, |s i| + N := by
      have : ∀ i, |((m i : ℤ) : ℝ)| ≤ |s i| + 1 := by
        intro i
        have := (hb i).1
        have := (hb i).2
        calc |((m i : ℤ) : ℝ)| = |s i - (s i - m i)| := by ring_nf
          _ ≤ |s i| + |s i - m i| := abs_sub _ _
          _ ≤ |s i| + 1 := by
            gcongr
            rw [abs_le]
            constructor <;> linarith
      calc ∑ i, |((m i : ℤ) : ℝ)| ≤ ∑ i, (|s i| + 1) := Finset.sum_le_sum fun i _ => this i
        _ = ∑ i, |s i| + N := by simp [Finset.sum_add_distrib]
    have hreal : Real.exp (B * W s) * Real.exp (-2 * Phi s) ≤
        Real.exp (c + ε * N) * Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := hexp s hs hcone
      nlinarith
    calc f (p * dg s hs * k) * μ (Xb P T m)
        ≤ (C * ENNReal.ofReal (Real.exp (B * W s))) * (K * ENNReal.ofReal (Real.exp (-2 * Phi s))) :=
          mul_le_mul' h1 h2
      _ = C * K * ENNReal.ofReal (Real.exp (B * W s) * Real.exp (-2 * Phi s)) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
      _ ≤ C * K * ENNReal.ofReal (Real.exp (c + ε * N) * Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|))) := by
          gcongr
      _ = D m := by
          rw [hD, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hsum : ∑' m, D m ≠ ⊤ := by
    simp only [hD]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hC hK)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (summ ε hε))
  calc ∫⁻ x in Sg P T, f x ∂μ ≤ ∫⁻ x in ⋃ m, Xb P T m, f x ∂μ := lintegral_mono_set hcov
    _ ≤ ∑' m, ∫⁻ x in Xb P T m, f x ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' m, D m := ENNReal.tsum_le_tsum hpiece
    _ < ⊤ := lt_top_iff_ne_top.mpr hsum

end PositivityTheory.KB.TwSMInt2

end
end

