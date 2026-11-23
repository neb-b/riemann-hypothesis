module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.LineExp
section
open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

namespace UpperTheory.V.Af.Rs

private noncomputable def ex (n : ℕ) (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * n * x)

private theorem ex_norm (n : ℕ) (x : ℝ) : ‖ex n x‖ = 1 := by
  unfold ex
  have h : (2 * Real.pi * Complex.I * n * x : ℂ) = ((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem ex_cont (n : ℕ) : Continuous (ex n) := by unfold ex; fun_prop

private theorem ex_orth (m n : ℕ) : ∫ x in (0 : ℝ)..1, conj (ex m x) * ex n x = if m = n then 1 else 0 := by
  unfold ex
  have key : ∀ x : ℝ, conj (Complex.exp (2 * Real.pi * Complex.I * m * x)) *
      Complex.exp (2 * Real.pi * Complex.I * n * x) =
      Complex.exp ((2 * Real.pi * Complex.I * ((n : ℂ) - m)) * x) := by
    intro x
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
    ring
  simp_rw [key]
  split_ifs with hmn
  · subst hmn
    simp
  · have hc : (2 * Real.pi * Complex.I * ((n : ℂ) - m)) ≠ 0 := by
      have h1 : ((n : ℂ) - m) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast (Ne.symm hmn)
      have h2 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [h1, h2, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have e1 : Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) - m) * ((1 : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
      rw [← this]
      congr 1
      push_cast
      ring
    rw [e1]
    simp

private theorem pars_abs (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b) (F G : ℝ → ℂ)
    (hF : ∀ x, HasSum (fun n => a n * ex n x) (F x)) (hG : ∀ x, HasSum (fun n => b n * ex n x) (G x)) :
    HasSum (fun n => conj (b n) * a n) (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
  have han : Summable (fun n => ‖a n‖) := summable_norm_iff.mpr ha
  have hbn : Summable (fun n => ‖b n‖) := summable_norm_iff.mpr hb
  have hGc : Continuous G := by
    have e : G = fun x => ∑' n, b n * ex n x := funext fun x => (hG x).tsum_eq.symm
    rw [e]
    refine continuous_tsum (fun n => continuous_const.mul (ex_cont n)) hbn ?_
    intro n x
    rw [norm_mul, ex_norm, mul_one]
  have hGb : ∀ t, ‖G t‖ ≤ ∑' n, ‖b n‖ := by
    intro t
    rw [← (hG t).tsum_eq]
    have e : (fun n => ‖b n * ex n t‖) = fun n => ‖b n‖ := by
      funext n
      rw [norm_mul, ex_norm, mul_one]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · rw [e]; exact hbn
    · rw [e]
  have hC : ∀ n, ∫ x in (0 : ℝ)..1, conj (G x) * ex n x = conj (b n) := by
    intro n
    have hs : HasSum (fun m => ∫ x in (0 : ℝ)..1, conj (b m) * (conj (ex m x) * ex n x))
        (∫ x in (0 : ℝ)..1, conj (G x) * ex n x) := by
      refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun m _ => ‖b m‖)
        ?_ ?_ ?_ ?_ ?_
      · intro m
        exact (continuous_const.mul
          ((Complex.continuous_conj.comp (ex_cont m)).mul (ex_cont n))).aestronglyMeasurable
      · intro m
        refine Filter.Eventually.of_forall (fun t _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, ex_norm, ex_norm]
        simp
      · exact Filter.Eventually.of_forall (fun t _ => hbn)
      · exact intervalIntegrable_const
      · refine Filter.Eventually.of_forall (fun t _ => ?_)
        have e : (fun m => conj (b m) * (conj (ex m t) * ex n t)) =
            fun m => conj (b m * ex m t) * ex n t := by
          funext m
          rw [map_mul, mul_assoc]
        rw [e]
        exact (Complex.hasSum_conj'.mpr (hG t)).mul_right (ex n t)
    simp_rw [intervalIntegral.integral_const_mul, ex_orth] at hs
    have h2 : HasSum (fun m => conj (b m) * if m = n then (1 : ℂ) else 0) (conj (b n)) := by
      have e : (fun m => conj (b m) * if m = n then (1 : ℂ) else 0) =
          fun m => if m = n then conj (b n) else 0 := by
        funext m
        split_ifs with h
        · rw [h, mul_one]
        · rw [mul_zero]
      rw [e]
      exact hasSum_ite_eq n (conj (b n))
    exact hs.unique h2
  have hB : HasSum (fun n => ∫ x in (0 : ℝ)..1, a n * (conj (G x) * ex n x))
      (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => ‖a n‖ * ∑' m, ‖b m‖) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (continuous_const.mul
        ((Complex.continuous_conj.comp hGc).mul (ex_cont n))).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall (fun t _ => ?_)
      rw [norm_mul, norm_mul, ex_norm, mul_one, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hGb t) (norm_nonneg _)
    · exact Filter.Eventually.of_forall (fun t _ => han.mul_right _)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun t _ => ?_)
      have e : (fun n => a n * (conj (G t) * ex n t)) = fun n => conj (G t) * (a n * ex n t) := by
        funext n
        ring
      rw [e]
      exact (hF t).mul_left (conj (G t))
  simp_rw [intervalIntegral.integral_const_mul, hC] at hB
  have e : (fun n => conj (b n) * a n) = fun n => a n * conj (b n) := by
    funext n
    ring
  rw [e]
  exact hB

private theorem line_exp (k L : ℕ) [NeZero L] (f : CuspForm (Gamma1 L) (k : ℤ)) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ) * ex n x) (f (pt x y)) := by
  have hp : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 L)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1
  have hs := ModularForm.hasSum_qExpansion f one_pos hp (pt x y)
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
  have hc : ((pt x y : ℍ) : ℂ) = x + y * Complex.I := by
    unfold pt
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have e : (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ) * ex n x) =
      fun m => (qExpansion 1 f).coeff m * Function.Periodic.qParam 1 ↑(pt x y) ^ m := by
    funext n
    rw [hc, mul_assoc]
    unfold coef ex Function.Periodic.qParam
    congr 1
    rw [← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ) * n * y)) * Complex.I_sq
  rw [e]
  exact hs

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.pars :
    UpperTheory.V.Af.Rs.Pars := by
  intro k L _ f g y hy
  have hF := line_exp k L f y hy
  have hG := line_exp k L g y hy
  have ex0 : ∀ n, ex n 0 = 1 := by
    intro n
    simp [ex]
  have ha : Summable (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) :=
    (hF 0).summable.congr (fun n => by rw [ex0, mul_one])
  have hb : Summable (fun n : ℕ => coef g n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) :=
    (hG 0).summable.congr (fun n => by rw [ex0, mul_one])
  have h := pars_abs _ _ ha hb (fun x => f (pt x y)) (fun x => g (pt x y)) hF hG
  have e : (fun n : ℕ => conj (coef g n) * coef f n * ((Real.exp (-(4 * Real.pi * n) * y) : ℝ) : ℂ)) =
      fun n => conj (coef g n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) *
        (coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) := by
    funext n
    rw [map_mul, Complex.conj_ofReal,
      show -(4 * Real.pi * n) * y = (-(2 * Real.pi * n) * y) + (-(2 * Real.pi * n) * y) by ring,
      Real.exp_add]
    push_cast
    ring
  rw [e]
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.NicePet
section
open Filter Asymptotics CongruenceSubgroup Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Pointwise

private theorem bounded_petersson_weight (H : ℍ → ℂ) (B a : ℝ) (ha : 0 < a) (hB : ∀ z, ‖H z‖ ≤ B)
    (hd : H =O[atImInfty] fun τ => Real.exp (-a * τ.im)) : ∃ C : ℝ, ∀ z : ℍ, ‖H z‖ * z.im ^ 3 ≤ C := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hd
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp hc
  set M := max A 0 with hM
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB UpperHalfPlane.I)
  have hM0 : 0 ≤ M := le_max_right _ _
  refine ⟨B * M ^ 3 + |c| * (6 / a ^ 3), fun z => ?_⟩
  have ht := z.im_pos
  have h1 : 0 ≤ B * M ^ 3 := by positivity
  have h2 : 0 ≤ |c| * (6 / a ^ 3) := by positivity
  rcases le_total z.im M with h | h
  · have : ‖H z‖ * z.im ^ 3 ≤ B * M ^ 3 :=
      mul_le_mul (hB z) (pow_le_pow_left₀ ht.le h 3) (by positivity) hB0
    linarith
  · have hz := hA z ((le_max_left _ _).trans h)
    simp only [Set.mem_setOf_eq] at hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hz
    have hexp : (a * z.im) ^ 3 / 6 ≤ Real.exp (a * z.im) := by
      have := Real.pow_div_factorial_le_exp (a * z.im) (by positivity) 3
      simpa [Nat.factorial] using this
    have he := Real.exp_pos (a * z.im)
    have hkey : Real.exp (-a * z.im) * z.im ^ 3 ≤ 6 / a ^ 3 := by
      rw [le_div_iff₀ (by positivity), neg_mul, Real.exp_neg, inv_mul_eq_div, div_mul_eq_mul_div,
        div_le_iff₀ he]
      rw [mul_pow] at hexp
      nlinarith
    have : ‖H z‖ * z.im ^ 3 ≤ |c| * (6 / a ^ 3) :=
      calc ‖H z‖ * z.im ^ 3 ≤ c * Real.exp (-a * z.im) * z.im ^ 3 :=
            mul_le_mul_of_nonneg_right hz (by positivity)
        _ ≤ |c| * (Real.exp (-a * z.im) * z.im ^ 3) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
        _ ≤ |c| * (6 / a ^ 3) := mul_le_mul_of_nonneg_left hkey (abs_nonneg c)
    linarith

theorem UpperTheory.V.Af.Rs.nicePet :
    UpperTheory.V.Af.Rs.NicePet := by
  intro k L _ f g
  refine ⟨by fun_prop, ?_⟩
  obtain ⟨B, hB⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) (Subgroup.map (mapGL ℝ) (Gamma1 L)) g f
  have hdec : ∀ h : SL(2, ℤ), ∃ a > 0,
      (fun τ => UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • τ)) =O[atImInfty]
        fun τ => Real.exp (-a * τ.im) := by
    intro h
    have : ((ConjAct.toConjAct (h : GL (Fin 2) ℝ)⁻¹) •
        (Subgroup.map (mapGL ℝ) (Gamma1 L))).IsArithmetic := by
      simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
        using! Subgroup.IsArithmetic.conj (Subgroup.map (mapGL ℝ) (Gamma1 L)) (mapGL ℚ h)⁻¹
    simp_rw [← UpperHalfPlane.petersson_slash_SL]
    exact (CuspFormClass.zero_at_infty (CuspForm.translate g h)).petersson_exp_decay_left
      (k : ℤ) _ (ModularForm.translate f h)
  have key : ∀ h : SL(2, ℤ), ∃ C : ℝ, ∀ z : ℍ,
      ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • z)‖ * z.im ^ 3 ≤ C := by
    intro h
    obtain ⟨a, ha, hd⟩ := hdec h
    exact bounded_petersson_weight (fun τ => UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • τ)) B a ha
      (fun z => hB _) hd
  choose Cf hCf using key
  let Γ' : Subgroup SL(2, ℤ) :=
    (Subgroup.map (mapGL ℝ) (Gamma1 L)).comap (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
  have : Fintype (SL(2, ℤ) ⧸ Γ') := Subgroup.fintypeQuotientOfFiniteIndex
  have hinv : ∀ j ∈ Γ', ∀ w : ℍ,
      ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (j • w)‖ = ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f w‖ :=
    fun j hj w => SlashInvariantFormClass.norm_petersson_smul (g := mapGL ℝ j) hj
  refine ⟨∑ q : SL(2, ℤ) ⧸ Γ', |Cf (Quotient.out q)⁻¹|, fun γ z _ => ?_⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul Γ' γ⁻¹
  have hγ : γ = (j : SL(2, ℤ)) * (Quotient.out (QuotientGroup.mk γ⁻¹ : SL(2, ℤ) ⧸ Γ'))⁻¹ := by
    rw [hj]; group
  rw [hγ, mul_smul, hinv _ j.2]
  refine (hCf _ z).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun q : SL(2, ℤ) ⧸ Γ' => |Cf (Quotient.out q)⁻¹|)
    (fun q _ => abs_nonneg _) (Finset.mem_univ _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.NotSummableTwo
section
open Filter Topology Set

private lemma not_summable_two : ¬ Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * (1 : ℝ))) := by
  intro hs
  set f : (Fin 2 → ℤ) → ℝ := fun x => ‖x‖ ^ (-(2 * (1 : ℝ))) with hf
  have hnn : ∀ x, 0 ≤ f x := fun x => Real.rpow_nonneg (norm_nonneg _) _
  let g : ℕ × ℕ → (Fin 2 → ℤ) := fun p => ![(p.1 : ℤ) + 1, (p.2 : ℤ)]
  have hg : Function.Injective g := by
    intro p q h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [g] at h0 h1
    exact Prod.ext (by omega) (by omega)
  have hsg : Summable (f ∘ g) := hs.comp_injective hg
  have hprod : Summable fun a : ℕ => ∑' b : ℕ, (f ∘ g) (a, b) := hsg.prod
  have key : ∀ a : ℕ, (1 : ℝ) / ((a : ℝ) + 1) ≤ ∑' b : ℕ, (f ∘ g) (a, b) := by
    intro a
    have hrow : Summable fun b : ℕ => (f ∘ g) (a, b) := hsg.prod_factor a
    have hterm : ∀ b ∈ Finset.range (a + 1), (f ∘ g) (a, b) = 1 / ((a : ℝ) + 1) ^ 2 := by
      intro b hb
      have hb' : b ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hn : ‖g (a, b)‖ = (a : ℝ) + 1 := by
        apply le_antisymm
        · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
          intro i
          fin_cases i
          · simp [g, Int.norm_eq_abs]
            rw [abs_of_nonneg (by positivity)]
          · simp [g, Int.norm_eq_abs]
            have : (b : ℝ) ≤ a := by exact_mod_cast hb'
            linarith
        · have h := norm_le_pi_norm (g (a, b)) 0
          have h2 : ‖g (a, b) 0‖ = (a : ℝ) + 1 := by
            simp [g, Int.norm_eq_abs]
            positivity
          linarith
      simp only [Function.comp, hf, hn]
      rw [show (-(2 * (1 : ℝ))) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast, one_div]
    calc (1 : ℝ) / ((a : ℝ) + 1)
        = ∑ b ∈ Finset.range (a + 1), 1 / ((a : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          field_simp
      _ = ∑ b ∈ Finset.range (a + 1), (f ∘ g) (a, b) :=
          Finset.sum_congr rfl (fun b hb => (hterm b hb).symm)
      _ ≤ ∑' b, (f ∘ g) (a, b) := hrow.sum_le_tsum _ (fun b _ => hnn _)
  have hsum : Summable fun a : ℕ => (1 : ℝ) / ((a : ℝ) + 1) :=
    Summable.of_nonneg_of_le (fun a => by positivity) key hprod
  have hsum' : Summable fun a : ℕ => (1 : ℝ) / ((a + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hsum
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hsum')

theorem UpperTheory.V.Af.Rs.wTop :
    UpperTheory.V.Af.Rs.WTop := by
  unfold UpperTheory.V.Af.Rs.WTop
  refine ⟨fun t ht => EisensteinSeries.summable_one_div_norm_rpow ht, fun M => ?_⟩
  have hnn : ∀ (s : ℝ) (x : Fin 2 → ℤ), 0 ≤ ‖x‖ ^ (-(2 * s)) :=
    fun s x => Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin 2 → ℤ), M < ∑ x ∈ F, ‖x‖ ^ (-(2 * (1 : ℝ))) := by
    by_contra h
    push_neg at h
    exact not_summable_two (summable_of_sum_le (hnn 1) h)
  have ht : Tendsto (fun s : ℝ => ∑ x ∈ F, ‖x‖ ^ (-(2 * s))) (𝓝 1)
      (𝓝 (∑ x ∈ F, ‖x‖ ^ (-(2 * (1 : ℝ))))) := by
    apply tendsto_finsetSum
    intro x _
    have hc : ContinuousAt (fun s : ℝ => ‖x‖ ^ (-(2 * s))) 1 := by
      apply ContinuousAt.comp (f := fun s : ℝ => -(2 * s)) (g := fun y : ℝ => ‖x‖ ^ y)
      · exact Real.continuousAt_const_rpow' (by norm_num)
      · fun_prop
    exact hc
  have hev : ∀ᶠ s in 𝓝[>] (1 : ℝ), M < ∑ x ∈ F, ‖x‖ ^ (-(2 * s)) ∧ s ∈ Ioc 1 2 := by
    refine ((ht.eventually (lt_mem_nhds hF)).filter_mono nhdsWithin_le_nhds).and ?_
    have hI : Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hI] with s hs using ⟨hs.1, hs.2.le⟩
  obtain ⟨s, hsM, hs⟩ := hev.exists
  refine ⟨s, hs, ?_⟩
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) :=
    EisensteinSeries.summable_one_div_norm_rpow (by linarith [hs.1])
  exact hsM.le.trans (hsum.sum_le_tsum F (fun x _ => hnn s x))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.NsqPos
section
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace UpperTheory.V.Af.Rs

private lemma nsq_eq (x : Fin 2 → ℤ) (z : ℍ) :
    Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) =
      ((x 0 : ℝ) * z.re + x 1) ^ 2 + ((x 0 : ℝ) * z.im) ^ 2 := by
  simp [Complex.normSq_apply]; ring

private lemma nsq_pos (x : Fin 2 → ℤ) (hx : x ≠ 0) (z : ℍ) :
    0 < Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) := by
  rw [nsq_eq]
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have : (x 1 : ℝ) ≠ 0 := by exact_mod_cast h1
    simp only [h0, Int.cast_zero, zero_mul, zero_add]
    positivity
  · have : (x 0 : ℝ) ≠ 0 := by exact_mod_cast h0
    have := z.im_pos.ne'
    positivity

private lemma nsq_low (x : Fin 2 → ℤ) (z : ℍ) (hz : z ∈ ModularGroup.fd) :
    ‖x‖ ^ 2 ≤ 2 * Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) := by
  rw [nsq_eq]
  obtain ⟨hz1, hzre⟩ := hz
  have hN : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    have := hz1
    rw [Complex.normSq_apply] at this
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
    nlinarith
  set a : ℝ := (x 0 : ℝ)
  set b : ℝ := (x 1 : ℝ)
  have hnorm : ‖x‖ ≤ max |a| |b| := by
    refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg a))).mpr fun i => ?_
    fin_cases i
    · simp [Int.norm_eq_abs, a]
    · simp [Int.norm_eq_abs, b]
  have hM : (max |a| |b|) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total |a| |b| with h | h
    · rw [max_eq_right h, sq_abs]
      nlinarith [sq_nonneg a]
    · rw [max_eq_left h, sq_abs]
      nlinarith [sq_nonneg b]
  have hx2 : ‖x‖ ^ 2 ≤ (max |a| |b|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hab : -(|a| * |b|) ≤ 2 * a * b * z.re := by
    have h1 : |2 * a * b * z.re| ≤ |a| * |b| := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have := abs_nonneg a
      have := abs_nonneg b
      nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg b)]
    exact (abs_le.mp h1).1
  have hsq : a ^ 2 + b ^ 2 ≤ 2 * (a ^ 2 - |a| * |b| + b ^ 2) := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hexp : (a * z.re + b) ^ 2 + (a * z.im) ^ 2
      = a ^ 2 * (z.re ^ 2 + z.im ^ 2) + 2 * a * b * z.re + b ^ 2 := by ring
  rw [hexp]
  have : a ^ 2 ≤ a ^ 2 * (z.re ^ 2 + z.im ^ 2) := by
    nlinarith [sq_nonneg a]
  linarith

end UpperTheory.V.Af.Rs

theorem UpperTheory.V.Af.Rs.kerBd :
    UpperTheory.V.Af.Rs.KerBd := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hs0 : 0 < s := by linarith
  have hzero : ∀ z, ker s 0 z = 0 := by
    intro z
    simp [ker, Real.zero_rpow hs0.ne']
  have hnn : ∀ (x : Fin 2 → ℤ) (z : ℍ), 0 ≤ z.im / Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) :=
    fun x z => div_nonneg z.im_pos.le (Complex.normSq_nonneg _)
  refine ⟨?_, ?_, hzero, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst hx
      have : ker s 0 = fun _ => 0 := funext hzero
      rw [this]; exact continuous_const
    · unfold ker
      refine Continuous.rpow_const ?_ (fun _ => Or.inr hs0.le)
      refine Continuous.div UpperHalfPlane.continuous_im ?_ (fun z => (nsq_pos x hx z).ne')
      exact Complex.continuous_normSq.comp
        ((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const)
  · intro x z
    exact Real.rpow_nonneg (hnn x z) _
  · intro γ z
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
    rfl
  · intro n x z
    have h : Complex.normSq (((((n : ℤ) • x) 0 : ℤ) : ℂ) * z + ((((n : ℤ) • x) 1 : ℤ) : ℂ)) =
        Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) * (n : ℝ) ^ (2 : ℝ) := by
      rw [nsq_eq, nsq_eq]
      simp
      ring
    unfold ker
    rw [h, ← div_div, Real.div_rpow (hnn x z) (by positivity), ← Real.rpow_mul (Nat.cast_nonneg n)]
  · intro x z hz
    by_cases hx : x = 0
    · subst hx
      rw [hzero]
      positivity
    · have hp := nsq_pos x hx z
      have hl := nsq_low x z hz
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy := z.im_pos
      have hy1 : 1 ≤ 2 * z.im := by
        have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
        nlinarith
      have h1 : z.im / Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) ≤ 2 * z.im / ‖x‖ ^ (2 : ℝ) := by
        rw [Real.rpow_two, div_le_div_iff₀ hp (by positivity)]
        nlinarith
      calc ker s x z ≤ (2 * z.im / ‖x‖ ^ (2 : ℝ)) ^ s := Real.rpow_le_rpow (hnn x z) h1 hs0.le
        _ = (2 * z.im) ^ s * ‖x‖ ^ (-(2 * s)) := by
          rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hn.le,
            Real.rpow_neg hn.le, div_eq_mul_inv]
        _ ≤ (2 * z.im) ^ (2 : ℝ) * ‖x‖ ^ (-(2 * s)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hy1 hs2) (by positivity)
        _ = _ := by rw [Real.rpow_two]; ring
end

