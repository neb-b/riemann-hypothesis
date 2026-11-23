module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeRowDifferenceSummableBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0159

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDirectionIndep
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem dif_comm (L : ℕ) (v w : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (dif L w F) = dif L w (dif L v F) := by
  funext x
  simp only [dif]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h : ∑ s ∈ Finset.range L, ∑ r ∈ Finset.range L, F (x + (s : ℤ) • v + (r : ℤ) • w)
      = ∑ r ∈ Finset.range L, ∑ s ∈ Finset.range L, F (x + (r : ℤ) • w + (s : ℤ) • v) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [add_right_comm]
  rw [h]
  ring

theorem sum_dif_dif (L : ℕ) (w : ℤ × ℤ) (Φ G : ℤ × ℤ → ℂ) (hL : 0 < L) (hΦ : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C)
    (hw : Kills L w Φ) (hG : Summable fun x => ‖G x‖) :
    ∑' x, Φ x * dif L w (dif L w G) x = ∑' x, Φ x * G x := by
  obtain ⟨hs1, he1⟩ := _root_.GlobalTheory.EisM.kills_sum_dif_eq L w Φ G hL hΦ hw hG
  obtain ⟨_, he2⟩ := _root_.GlobalTheory.EisM.kills_sum_dif_eq L w Φ (dif L w G) hL hΦ hw hs1
  exact he2.trans he1

theorem lat_indep : ∀ (j L : ℕ) (v w : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 1 ≤ j → 0 < L →
    (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → Kills L w Φ → lat j 0 L v Φ τ = lat j 0 L w Φ τ := by
  intro j L v w Φ τ hj hL hΦ hv hw
  set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT
  have hsv := _root_.GlobalTheory.LatSumZ.latsum_summable j L v τ hj hL
  have hsw := _root_.GlobalTheory.LatSumZ.latsum_summable j L w τ hj hL
  simp only [lat]
  calc ∑' x, Φ x * dif L v (dif L v T) x
      = ∑' x, Φ x * dif L w (dif L w (dif L v (dif L v T))) x :=
        (sum_dif_dif L w Φ _ hL hΦ hw hsv).symm
    _ = ∑' x, Φ x * dif L v (dif L v (dif L w (dif L w T))) x := by
        have c1 : ∀ F : ℤ × ℤ → ℂ, dif L w (dif L v (dif L v F)) = dif L v (dif L v (dif L w F)) := by
          intro F; rw [dif_comm L w v (dif L v F), dif_comm L w v F]
        rw [c1 T, c1 (dif L w T)]
    _ = ∑' x, Φ x * dif L w (dif L w T) x := sum_dif_dif L v Φ _ hL hΦ hv hsw

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumModerateMeasurabl
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.LatBd

theorem continuous_eisensteinLatticeTermWeightS_exponent {j : ℕ} (hj : 1 ≤ j) (z : ℂ) : Continuous fun s : ℝ => trm j s z := by
  by_cases hz : z = 0
  · subst hz
    have : ∀ s : ℝ, trm j s 0 = 0 := fun s => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · unfold trm
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact continuous_const.rpow (continuous_const.mul continuous_id) fun _ => Or.inl (norm_ne_zero_iff.2 hz)

theorem lin_ne_zero (x : ℤ × ℤ) (hx : x ≠ 0) (τ : ℍ) : (x.1 : ℂ) * (τ : ℂ) + x.2 ≠ 0 := by
  intro h
  have him : (x.1 : ℝ) * τ.im = 0 := by
    have := congrArg Complex.im h
    simpa using this
  have h1 : x.1 = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' τ.im_pos.ne'
  have h2 : x.2 = 0 := by
    have := congrArg Complex.re h
    simp [h1] at this
    exact_mod_cast this
  exact hx (Prod.ext h1 h2)

theorem trm_cont_tau {j : ℕ} (hj : 1 ≤ j) (s : ℝ) (x : ℤ × ℤ) :
    Continuous fun τ : ℍ => trm j s ((x.1 : ℂ) * τ + x.2) := by
  by_cases hx : x = 0
  · subst hx
    have : ∀ τ : ℍ, trm j s (((0 : ℤ × ℤ).1 : ℂ) * τ + (0 : ℤ × ℤ).2) = 0 := fun τ => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · have hc : Continuous fun τ : ℍ => (x.1 : ℂ) * (τ : ℂ) + x.2 :=
      (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
    unfold trm
    refine ((hc.pow j).inv₀ fun τ => pow_ne_zero _ (lin_ne_zero x hx τ)).mul
      (Complex.continuous_ofReal.comp ((continuous_norm.comp hc).rpow_const fun τ => Or.inl ?_))
    exact norm_ne_zero_iff.2 (lin_ne_zero x hx τ)

theorem dif_cont {α : Type*} [TopologicalSpace α] (L : ℕ) (v : ℤ × ℤ) (F : α → ℤ × ℤ → ℂ)
    (h : ∀ x, Continuous fun a => F a x) (x : ℤ × ℤ) : Continuous fun a => dif L v (F a) x := by
  unfold dif
  exact (h x).sub (continuous_const.mul (continuous_finsetSum _ fun r _ => h _))

theorem difdif_le (L : ℕ) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (u : ℤ × ℤ → ℝ) (h : ∀ x, ‖dif L v F x‖ ≤ u x)
    (x : ℤ × ℤ) : ‖dif L v (dif L v F) x‖ ≤ u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v) := by
  show ‖dif L v F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, dif L v F (x + (r : ℤ) • v)‖ ≤ _
  refine (norm_sub_le _ _).trans (add_le_add (h x) ?_)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => h _))
    (inv_nonneg.2 (Nat.cast_nonneg L))

theorem hasSum_dom (L : ℕ) (hL : 0 < L) (v : ℤ × ℤ) (u : ℤ × ℤ → ℝ) {S : ℝ} (hu : HasSum u S) :
    HasSum (fun x => u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v)) (2 * S) := by
  have h1 : ∀ r : ℕ, HasSum (fun x => u (x + (r : ℤ) • v)) S := fun r =>
    (Equiv.addRight ((r : ℤ) • v)).hasSum_iff.2 hu
  have h2 := hasSum_sum (s := Finset.range L) fun r _ => h1 r
  have h3 := hu.add (h2.mul_left ((L : ℝ)⁻¹))
  convert h3 using 1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp; ring

theorem measurable_tsum_any {X I : Type} [MeasurableSpace X] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (g : X → I → ℂ) (hg : ∀ i, Measurable fun x => g x i) :
    Measurable fun x => ∑' i, g x i := by
  have e : ∀ x, ∑' i, g x i = ∫ i, g x i ∂(Measure.count : Measure I) := fun x => by
    by_cases hf : Summable (g x)
    · have hi : Integrable (g x) (Measure.count : Measure I) := by
        rw [integrable_count_iff]; exact summable_norm_iff.mpr hf
      rw [integral_countable hi]; simp [measureReal_def]
    · rw [tsum_eq_zero_of_not_summable hf, integral_undef]
      intro hi; rw [integrable_count_iff] at hi; exact hf (summable_norm_iff.mp hi)
  simp only [e]
  have hm : Measurable fun p : X × I => g p.1 p.2 := measurable_from_prod_countable_left hg
  exact (StronglyMeasurable.integral_prod_right' (ν := (Measure.count : Measure I))
    hm.stronglyMeasurable).measurable

end GlobalTheory.EisM.LatBd

namespace GlobalTheory.EisM.LatBd

theorem lat_mod_meas_tendsto : ∀ (j L : ℕ) (Φ : ℤ × ℤ → ℂ), 2 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) →
    (∃ (C : ℝ) (A : ℕ), ∀ (s : ℝ) (τ : ℍ), 0 ≤ s → s ≤ 1 → ‖lat j s L (0, 1) Φ τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)) ∧
    (∀ s : ℝ, Measurable (lat j s L (0, 1) Φ)) ∧
    ∀ τ : ℍ, Tendsto (fun s : ℝ => lat j s L (0, 1) Φ τ) (𝓝[>] 0) (𝓝 (lat j 0 L (0, 1) Φ τ)) := by
  intro j L Φ hj hL ⟨B, hB⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hj1 : 1 ≤ j := by omega
  obtain ⟨C, A, hrow⟩ := _root_.GlobalTheory.RowBd.rowbd j L hj hL

  have dom : ∀ τ : ℍ, ∃ U : ℤ × ℤ → ℝ, ∃ S : ℝ, HasSum U (2 * S) ∧ S ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x, ‖Φ x * dif L (0, 1) (dif L (0, 1)
        fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ B * U x := by
    intro τ
    obtain ⟨u, hus, hule, hu⟩ := hrow τ
    refine ⟨_, _, hasSum_dom L hL (0, 1) u hus.hasSum, hule, fun s hs0 hs1 x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hB x) (difdif_le L (0, 1) _ u (fun x => hu s x hs0 hs1) x) (norm_nonneg _) hB0
  refine ⟨⟨2 * B * C, A, fun s τ hs0 hs1 => ?_⟩, fun s => ?_, fun τ => ?_⟩
  · obtain ⟨U, S, hU, hS, hb⟩ := dom τ
    have h := tsum_of_norm_bounded (hU.mul_left B) (hb s hs0 hs1)
    have hpos : 0 ≤ B * 2 := by positivity
    calc ‖lat j s L (0, 1) Φ τ‖ ≤ B * (2 * S) := h
      _ = (B * 2) * S := by ring
      _ ≤ (B * 2) * (C * (τ.im ^ A + (τ.im ^ A)⁻¹)) := mul_le_mul_of_nonneg_left hS hpos
      _ = 2 * B * C * (τ.im ^ A + (τ.im ^ A)⁻¹) := by ring
  · unfold lat
    refine measurable_tsum_any (fun (τ : ℍ) x => Φ x * dif L (0, 1) (dif L (0, 1)
      fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x) fun x => ?_
    exact (continuous_const.mul (dif_cont L (0, 1) _
      (dif_cont L (0, 1) _ (fun y => trm_cont_tau hj1 s y)) x)).measurable
  · obtain ⟨U, S, hU, -, hb⟩ := dom τ
    unfold lat
    refine tendsto_tsum_of_dominated_convergence (bound := fun x => B * U x) (hU.mul_left B).summable
      (fun x => ?_) ?_
    · have hc : Continuous fun s : ℝ => Φ x * dif L (0, 1) (dif L (0, 1)
          fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x :=
        continuous_const.mul (dif_cont L (0, 1) _ (dif_cont L (0, 1) _ (fun y => continuous_eisensteinLatticeTermWeightS_exponent hj1 _)) x)
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
      exact hb s hs.1.le hs.2.le

end GlobalTheory.EisM.LatBd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformationStatement
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_function_transformation : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ), admitted c x → sg c x (γ • τ) = sg c (act x γ) τ := by
  first | exact @GlobalTheory.Sieg.sg_smul | exact GlobalTheory.Sieg.sg_smul | (intros; apply GlobalTheory.Sieg.sg_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralQExpansionEqLSeries
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

private theorem im_ofComplex_pt (x y : ℝ) (hy : 0 < y) :
    (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ofComplex_apply_of_im_pos h]
  simp [UpperHalfPlane.im]

theorem strip_eq_LSeries : ∀ (h b : ℕ → ℂ) (w : ℝ), 0 < w → PolyB h → PolyB b → h 0 = 0 →
    LSeriesSummable (fun n => conj (h n) * b n) w →
    IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ)) strip →
    ∫ τ in strip, conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ) =
      ((Real.Gamma w / (4 * π) ^ w : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) w := by
  intro h b w hw hh hb h0 hL hint
  set a : ℕ → ℂ := fun n => conj (h n) * b n with ha
  set P : ℝ → ℂ := fun y => ∫ x in (0 : ℝ)..1,
    conj (qs h (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I)) with hPd
  have h4 : (0 : ℝ) < 4 * π := by positivity
  have ha0 : a 0 = 0 := by simp [ha, h0]
  have h1 : (∫ τ in strip, conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ)) = mellin P (w : ℂ) := by
    rw [_root_.GlobalTheory.EisM.strip_iterated.2 _ hint]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy : 0 < y := hy
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    simp only [im_ofComplex_pt _ _ hy, hPd, smul_eq_mul]
    rw [intervalIntegral.integral_mul_const]
    have e : ((y : ℂ) ^ ((w : ℂ) - 1)) = ((y ^ (w + 1) : ℝ) : ℂ) / (y : ℂ) ^ 2 := by
      have e1 : (w : ℂ) - 1 = ((w - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e1, ← Complex.ofReal_cpow hy.le]
      have e2 : y ^ (w - 1) = y ^ (w + 1) / y ^ 2 := by
        have : w - 1 = (w + 1) - ((2 : ℕ) : ℝ) := by push_cast; ring
        rw [this, Real.rpow_sub hy, Real.rpow_natCast]
      rw [e2]; push_cast; ring
    rw [e]; ring
  have hsum : Summable fun n : ℕ => ‖a n‖ / (4 * π * n) ^ ((w : ℂ).re) := by
    have hs2 := (hL.norm).div_const ((4 * π) ^ w)
    refine hs2.congr (fun n => ?_)
    rw [LSeries.norm_term_eq, Complex.ofReal_re]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · rw [if_neg hn.ne', Real.mul_rpow h4.le (Nat.cast_nonneg n), div_div, mul_comm ((n : ℝ) ^ w)]
  have h2 := hasSum_mellin (a := a) (p := fun n : ℕ => 4 * π * n) (F := P) (s := (w : ℂ))
    (fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · left; exact ha0
      · right; positivity)
    (by simpa using hw)
    (fun y hy => by
      have := _root_.GlobalTheory.EisM.parseval_line h b y hh hb hy
      refine this.congr_fun (fun n => ?_)
      simp only [ha]
      congr 2
      ring_nf)
    hsum
  rw [h1, ← h2.tsum_eq, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  rw [LSeries.term_of_ne_zero hn.ne', ← Complex.ofReal_cpow (by positivity), Real.mul_rpow h4.le (Nat.cast_nonneg n),
    Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.Gamma_ofReal]
  push_cast
  field_simp

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZmodCocycleEqCoboundaryOfUnitTwistedCocycle
section
open GlobalTheory.NeedB Polynomial

noncomputable section

open IntermediateField

namespace GlobalTheory.Hilbert90CupCoboundary

theorem isLocallyConstant_eval {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (τ : Ω) : IsLocallyConstant (fun g : Ω ≃ₐ[K] Ω => g τ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  haveI : FiniteDimensional K K⟮τ⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral τ)
  have hopen : IsOpen ((K⟮τ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' ((K⟮τ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)),
    hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  · intro g' hg'
    have hfτ : (g⁻¹ * g') τ = τ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' τ
        (IntermediateField.mem_adjoin_simple_self K τ)
    have e : g' = g * (g⁻¹ * g') := by group
    show g' τ = g τ
    rw [e, AlgEquiv.mul_apply, hfτ]

theorem zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (c : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ZMod N) (v : (Ω ≃ₐ[K] Ω) → Ωˣ), IsLocallyConstant v →
  (∀ g h, (v g : Ω) * g (v h) = ζ ^ (c g h).val * v (g * h)) →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, c g h = η h - η (g * h) + η g := by
  intro K Ω _ _ _ _ _ N ζ hN0 hζ hfix c v hv hcoc
  classical
  haveI : NeZero N := ⟨by omega⟩
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let u : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => v g ^ N
  have hu_lc : IsLocallyConstant u := hv.comp (fun x : Ωˣ => x ^ N)
  have hu_coc : ∀ g h, ((u (g * h) : Ωˣ) : Ω) = u g * g (u h) := by
    intro g h
    simp only [u, Units.val_pow_eq_pow_val, map_pow]
    rw [← mul_pow, hcoc g h, mul_pow, ← pow_mul, mul_comm (c g h).val N, pow_mul, hζ.pow_eq_one,
      one_pow, one_mul]
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.hilbert90_locallyConstant_cocycle K Ω u hu_lc hu_coc
  obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_pow_nat_eq (t : Ω) hN0
  have ht0 : (t : Ω) ≠ 0 := t.ne_zero
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0.ne'] at hτ
    exact ht0 hτ.symm
  have hgτ0 : ∀ g : Ω ≃ₐ[K] Ω, g τ ≠ 0 := fun g => (map_ne_zero g).2 hτ0
  let w : (Ω ≃ₐ[K] Ω) → Ω := fun g => (v g : Ω) * τ / g τ
  have hw_lc : IsLocallyConstant w :=
    (hv.comp (fun x : Ωˣ => (x : Ω))).comp₂ (isLocallyConstant_eval (K := K) τ) (fun a b => a * τ / b)
  have hw_pow : ∀ g, w g ^ N = 1 := by
    intro g
    have h1 : (v g : Ω) ^ N = g t / t := by rw [← Units.val_pow_eq_pow_val]; exact ht g
    have h2 : (g τ) ^ N = g t := by rw [← map_pow, hτ]
    have h3 : g (t : Ω) ≠ 0 := (map_ne_zero g).2 ht0
    simp only [w]
    rw [div_pow, mul_pow, h1, h2, hτ]
    field_simp
  have hw_coc : ∀ g h, w g * g (w h) = ζ ^ (c g h).val * w (g * h) := by
    intro g h
    have hghτ : g (h τ) ≠ 0 := (map_ne_zero g).2 (hgτ0 h)
    have hg := hgτ0 g
    have e1 : w g * g (w h) = ((v g : Ω) * g (v h)) * τ / g (h τ) := by
      simp only [w, map_div₀, map_mul]
      field_simp
    rw [e1, hcoc g h]
    simp only [w, AlgEquiv.mul_apply]
    ring
  let E : Ω → ZMod N := fun x => if hx : ∃ i : ZMod N, ζ ^ i.val = x then hx.choose else 0
  let η : (Ω ≃ₐ[K] Ω) → ZMod N := fun g => E (w g)
  have hη : ∀ g, ζ ^ (η g).val = w g := by
    intro g
    obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one (hw_pow g)
    have hex : ∃ j : ZMod N, ζ ^ j.val = w g := ⟨(i : ZMod N), by rw [ZMod.val_cast_of_lt hi, hi']⟩
    simp only [η, E, dif_pos hex]
    exact hex.choose_spec
  refine ⟨η, hw_lc.comp E, ?_⟩
  intro g h
  have key : ζ ^ (η g + η h).val = ζ ^ (c g h + η (g * h)).val := by
    rw [KumLemma.pow_val_add hζ, KumLemma.pow_val_add hζ, hη g, hη h, hη (g * h)]
    have : g (w h) = w h := by rw [← hη h, map_pow, hfix]
    rw [← hw_coc, this]
  have hinj : η g + η h = c g h + η (g * h) :=
    ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) key)
  linear_combination -hinj

end GlobalTheory.Hilbert90CupCoboundary
end
end

