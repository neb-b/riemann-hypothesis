module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.IntegralityGoodReduction
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CrossUp
section
open PositivityTheory.RgJS UpperTheory.V.Z.Tf.GOne
open scoped ComplexConjugate

theorem UpperTheory.V.Z.Tf.GOne.crossUp :
    ExtId → CrossUp := by
  intro hE W q X d A hS x y hxy
  obtain ⟨F, hFa, hFe⟩ := hE W q X d A hS x y
  have hc : ContinuousOn (fun t : ℝ => F t) (Set.Icc 1 2) := fun t ht =>
    ((hFa t (by linarith [ht.1])).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun σ h1 h2 => ?_⟩
  have h3 := hM σ ⟨h1.le, h2⟩
  rw [hFe σ h1, if_neg hxy, one_mul, Complex.norm_exp] at h3
  linarith [Real.add_one_le_exp (∑' p, lterm q (A x) (A y) σ p).re]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.LogTwo
section
open PositivityTheory.RgJS UpperTheory.V.Z.Tf.GOne
open scoped ComplexConjugate

theorem UpperTheory.V.Z.Tf.GOne.logTwo :
    ExtId → LogTwo := by
  intro hE W q X d A hS x
  obtain ⟨F, hFa, hFe⟩ := hE W q X d A hS x x
  simp only [if_true] at hFe
  have hq : ∀ w, (0 : ℝ) < q w := fun w => by exact_mod_cast lt_of_lt_of_le two_pos (hS.primes.two w)
  have hne : ∀ σ : ℝ, 1 < σ → (σ : ℂ) - 1 ≠ 0 := fun σ h => sub_ne_zero.2 (by exact_mod_cast h.ne')
  have h1 : F 1 ≠ 0 := by
    intro h0
    have hc : ContinuousOn (fun t : ℝ => dslope F 1 t) (Set.Icc 1 2) := fun t ht => by
      refine (ContinuousAt.comp (g := dslope F 1) ?_ Complex.continuous_ofReal.continuousAt).continuousWithinAt
      rcases eq_or_ne (t : ℂ) 1 with e | e
      · rw [e]
        exact continuousAt_dslope_same.2 (by simpa using (hFa 1 one_pos).differentiableAt)
      · exact (continuousAt_dslope_of_ne e).2 (hFa t (by linarith [ht.1])).continuousAt
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine dirichlet_series_unbounded landauL newton_identities_low_degree euler_product_log_bound removable_singularity_holds (convergence_of_landau_euler landauL euler_product_log_bound)
      W q X d A hS Unit (fun _ => x) ⟨M, fun σ a b => ?_⟩
    have e1 : ∀ p, lterm q (A x) (A x) σ p = ((DirichletSeriesUnbounded₂.cc A (fun _ : Unit => x) p * Real.exp (-(DirichletSeriesUnbounded₂.ll q p * σ)) : ℝ) : ℂ) :=
      fun p => by simpa using DirichletSeriesUnbounded₂.sum_lterm q A (fun _ : Unit => x) hq σ p
    have e2 := sub_smul_dslope F 1 (σ : ℂ)
    rw [h0, sub_zero, hFe σ a, smul_eq_mul] at e2
    have e3 := hM σ ⟨a.le, b⟩
    simp only [mul_left_cancel₀ (hne σ a) e2, Complex.norm_exp] at e3
    simp only [Finset.univ_unique, Finset.sum_singleton]
    simp only [e1, ← Complex.ofReal_tsum, Complex.ofReal_re] at e3 ⊢
    rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun p => mul_nonneg (DirichletSeriesUnbounded₂.cc_nonneg A _ p) (Real.exp_pos _).le)]
    exact le_trans (by linarith [Real.add_one_le_exp (∑' p, DirichletSeriesUnbounded₂.cc A (fun _ : Unit => x) p * Real.exp (-(DirichletSeriesUnbounded₂.ll q p * σ)))]) e3
  have h2 : ∀ t ∈ Set.Icc (1 : ℝ) 2, F t ≠ 0 := fun t ht => by
    rcases ht.1.eq_or_lt with e | e
    · rw [← e]; simpa using h1
    · rw [hFe t e]; exact mul_ne_zero (hne t e) (Complex.exp_ne_zero _)
  have hc : ContinuousOn (fun t : ℝ => Real.log ‖F t‖) (Set.Icc 1 2) := fun t ht =>
    (((hFa t (by linarith [ht.1])).continuousAt.comp Complex.continuous_ofReal.continuousAt).norm.log
      (norm_ne_zero_iff.2 (h2 t ht))).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun σ a b => ?_⟩
  have h3 := hM σ ⟨a.le, b⟩
  have hn : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hFe σ a, norm_mul, hn, Complex.norm_exp, Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, Real.norm_eq_abs, add_comm] at h3
  exact h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.NormLterm
section
open PositivityTheory.RgJS UpperTheory.V.Z.Tf.GOne
open scoped ComplexConjugate

private theorem norm_lterm {W : Type} (q : W → ℕ) (hq : ∀ w, 0 < q w) {A B : Type} [Fintype A] [Fintype B] (α : W → A → ℂ) (β : W → B → ℂ)
    (s : ℂ) (p : W × ℕ) : ‖lterm q α β s p‖ =
      ‖∑ a, α p.1 a ^ (p.2 + 1)‖ * ‖∑ b, β p.1 b ^ (p.2 + 1)‖ * ((q p.1 : ℝ) ^ (-s.re)) ^ (p.2 + 1) / ‖(p.2 : ℂ) + 1‖ := by
  rw [lterm, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_natCast_cpow_of_pos (hq _), Complex.neg_re]

theorem UpperTheory.V.Z.Tf.GOne.extId :
    ExtId := by
  intro W q X d A hS x y
  classical
  obtain ⟨F, σ0, hFa, hFe⟩ := hS.rs x y
  refine ⟨F, hFa, ?_⟩
  have hq : ∀ w, 0 < q w := fun w => lt_of_lt_of_le two_pos (hS.primes.two w)
  have hC := (convergence_of_landau_euler landauL euler_product_log_bound W q X d A hS x y).1
  have hSa : ∀ σ : ℝ, 1 < σ → AnalyticAt ℂ (fun s => ∑' p, lterm q (A x) (A y) s p) σ := by
    intro σ hσ
    have hU : IsOpen {s : ℂ | (1 + σ) / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hd : DifferentiableOn ℂ (fun s => ∑' p, lterm q (A x) (A y) s p) {s : ℂ | (1 + σ) / 2 < s.re} := by
      refine Complex.differentiableOn_tsum_of_summable_norm (hC ((1 + σ) / 2) (by linarith)) (fun p => ?_) hU (fun p s hs => ?_)
      · refine Differentiable.differentiableOn ?_
        unfold lterm
        refine Differentiable.div_const (Differentiable.const_mul (Differentiable.pow ?_ _) _) _
        exact differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast (hq p.1).ne'))
      · rw [norm_lterm q hq, norm_lterm q hq, Complex.ofReal_re]
        have hs' : (1 + σ) / 2 < s.re := hs
        have h1 : (1 : ℝ) ≤ q p.1 := by exact_mod_cast hq p.1
        have h2 : (q p.1 : ℝ) ^ (-s.re) ≤ (q p.1 : ℝ) ^ (-((1 + σ) / 2)) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
        gcongr
    exact hd.analyticAt (hU.mem_nhds (by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith))
  have ha1 : AnalyticOnNhd ℝ (fun t : ℝ => F t) (Set.Ioi 1) := fun t ht => by
    have h1 : AnalyticAt ℝ F (t : ℂ) := (hFa t (by linarith [Set.mem_Ioi.1 ht])).restrictScalars
    exact h1.comp (Complex.ofRealCLM.analyticAt t)
  have ha2 : AnalyticOnNhd ℝ (fun t : ℝ => (if x = y then (t : ℂ) - 1 else 1) * Complex.exp (∑' p, lterm q (A x) (A y) t p))
      (Set.Ioi 1) := fun t ht => by
    have h : AnalyticAt ℂ (fun s : ℂ => (if x = y then s - 1 else 1) * Complex.exp (∑' p, lterm q (A x) (A y) s p)) (t : ℂ) := by
      refine AnalyticAt.mul ?_ (hSa t (Set.mem_Ioi.1 ht)).cexp
      split_ifs
      · exact analyticAt_id.sub analyticAt_const
      · exact analyticAt_const
    exact (h.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  have hid := ha1.eqOn_of_preconnected_of_eventuallyEq ha2 isPreconnected_Ioi (z₀ := max σ0 2 + 1)
    (Set.mem_Ioi.2 (by linarith [le_max_right σ0 2])) (by
      filter_upwards [Ioi_mem_nhds (show max σ0 2 < max σ0 2 + 1 by linarith)] with t ht
      have h1 : σ0 < t := lt_of_le_of_lt (le_max_left _ _) ht
      have h2 : (2 : ℝ) < t := lt_of_le_of_lt (le_max_right _ _) ht
      rw [hFe t h1, (euler_product_log_bound W q _ _ (A x) (A y) t hS.primes (hS.bd _) (hS.bd _) (by simpa using h2)).2.1])
  exact fun σ hσ => hid (Set.mem_Ioi.2 hσ)
end

