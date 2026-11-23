module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.MeanVal
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma circle_mean (g : ℂ → ℂ)
    (hd : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, DifferentiableAt ℂ g u) :
    ∫ s : UnitAddCircle, g ((AddCircle.toCircle s : Circle) : ℂ) = g 0 := by
  have hc : ContinuousOn g (Metric.closedBall (0 : ℂ) |1|) := by
    intro u hu
    exact (hd u (by simpa using hu)).continuousAt.continuousWithinAt
  have hmv : Real.circleAverage g 0 1 = g 0 :=
    circleAverage_of_differentiable_on_off_countable (s := ∅) Set.countable_empty hc
      (fun u hu => hd u (by
        have := hu.1
        simp only [abs_one, Metric.mem_ball] at this
        simpa using this.le))
  have hpi : (2 * Real.pi) ≠ 0 := Real.two_pi_pos.ne'
  have e : ∀ a : ℝ, ((AddCircle.toCircle (a : UnitAddCircle) : Circle) : ℂ)
      = circleMap 0 1 (2 * Real.pi * a) := by
    intro a
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap]
    simp only [zero_add, Complex.ofReal_one, one_mul]
    congr 1
    push_cast
    ring
  rw [← UnitAddCircle.intervalIntegral_preimage 0, ← hmv, Real.circleAverage_def]
  simp_rw [e]
  rw [intervalIntegral.integral_comp_mul_left (fun θ => g (circleMap 0 1 θ)) hpi]
  simp

private lemma ratio_eq (u : ℂ) (hu : u ≠ 0) (c : ℤ) (i j : ℕ) (hij : i < j) (a b : ℂ) :
    (u ^ (c - (i : ℤ)) * a) / (u ^ (c - (j : ℤ)) * b) = u ^ (j - i) * (a / b) := by
  have h : u ^ (c - (i : ℤ)) / u ^ (c - (j : ℤ)) = u ^ (j - i) := by
    rw [← zpow_sub₀ hu, ← zpow_natCast, Nat.cast_sub hij.le]
    congr 1
    ring
  rw [mul_div_mul_comm, h]

theorem UpperTheory.Gal.Gen.meanVal_pf :
    UpperTheory.Gal.Gen.MeanVal := by
  intro n t ht0 ht1 z hz c m
  set g : ℂ → ℂ := fun u => u ^ m * ∏ p ∈ prs n,
    (1 - u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) /
      (1 - (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ)))) with hg
  have hden : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, ∀ p : Fin n × Fin n,
      1 - (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) ≠ 0 := by
    intro u hu p h0
    have hu1 : ‖u‖ ≤ 1 := by simpa using hu
    have hx : (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) = 1 :=
      (sub_eq_zero.mp h0).symm
    have hn := congrArg norm hx
    rw [norm_mul, norm_mul, norm_div, hz, hz, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0,
      norm_one, div_one, mul_one] at hn
    have : ‖u‖ ^ ((p.2 : ℕ) - (p.1 : ℕ)) ≤ 1 := pow_le_one₀ (norm_nonneg _) hu1
    nlinarith
  have hd : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, DifferentiableAt ℂ g u := by
    intro u hu
    refine (differentiableAt_id.pow m).mul ?_
    refine DifferentiableAt.fun_finsetProd fun p _ => ?_
    refine DifferentiableAt.div ?_ ?_ (hden u hu p)
    · exact (differentiableAt_const _).sub ((differentiableAt_id.pow _).mul (differentiableAt_const _))
    · exact (differentiableAt_const _).sub
        ((differentiableAt_const _).mul ((differentiableAt_id.pow _).mul (differentiableAt_const _)))
  have h0 : g 0 = if m = 0 then 1 else 0 := by
    have hp : ∏ p ∈ prs n, (1 - (0 : ℂ) ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) /
        (1 - (t : ℂ) * ((0 : ℂ) ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ)))) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have hlt : (p.1 : ℕ) < (p.2 : ℕ) := (Finset.mem_filter.mp hp).2
      have hk : (p.2 : ℕ) - (p.1 : ℕ) ≠ 0 := by omega
      simp [zero_pow hk]
    simp only [hg, hp, mul_one]
    split_ifs with hm
    · simp [hm]
    · exact zero_pow hm
  have hs : ∀ s : UnitAddCircle, ((AddCircle.toCircle s : Circle) : ℂ) ^ m *
      half (t : ℂ) (fun i => Circle.toUnits (AddCircle.toCircle s) ^ (c - (i : ℕ)) * z i)
      = g ((AddCircle.toCircle s : Circle) : ℂ) := by
    intro s
    simp only [hg, half]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hlt : (p.1 : ℕ) < (p.2 : ℕ) := (Finset.mem_filter.mp hp).2
    have hu : ((AddCircle.toCircle s : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have key := ratio_eq _ hu c p.1 p.2 hlt (z p.1 : ℂ) (z p.2 : ℂ)
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Circle.toUnits_apply, Units.val_mk0]
    rw [key]
  simp_rw [hs]
  rw [circle_mean g hd, h0]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.NullZero
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma pt_coe {n : ℕ} (θ : Fin n → UnitAddCircle) (i : Fin n) :
    ((pt θ i : ℂˣ) : ℂ) = ((AddCircle.toCircle (θ i) : Circle) : ℂ) := rfl

private lemma eval_cons_pt {n : ℕ} (s : UnitAddCircle) (θ : Fin n → UnitAddCircle)
    (p : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.eval (fun i => (pt (Fin.cons s θ : Fin (n + 1) → UnitAddCircle) i : ℂ)) p =
      Polynomial.eval ((AddCircle.toCircle s : Circle) : ℂ)
        (Polynomial.map (MvPolynomial.eval (fun i => (pt θ i : ℂ))) (MvPolynomial.finSuccEquiv ℂ n p)) := by
  rw [← MvPolynomial.eval_eq_eval_mv_eval']
  have h : (fun i => (pt (Fin.cons s θ : Fin (n + 1) → UnitAddCircle) i : ℂ)) =
      (Fin.cons ((AddCircle.toCircle s : Circle) : ℂ) (fun i => (pt θ i : ℂ)) : Fin (n + 1) → ℂ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [pt_coe]
  rw [h]

private lemma continuous_eval_pt {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    Continuous fun θ : Fin n → UnitAddCircle => MvPolynomial.eval (fun i => (pt θ i : ℂ)) p := by
  have h1 : Continuous fun x : Fin n → ℂ => MvPolynomial.eval x p := MvPolynomial.continuous_eval p
  have h2 : Continuous fun θ : Fin n → UnitAddCircle => (fun i => (pt θ i : ℂ)) := by
    refine continuous_pi fun i => ?_
    simp only [pt_coe]
    exact continuous_subtype_val.comp ((AddCircle.continuous_toCircle).comp (continuous_apply i))
  exact h1.comp h2

private lemma circle_zero_null (r : Polynomial ℂ) (hr : r ≠ 0) :
    volume {s : UnitAddCircle | r.eval ((AddCircle.toCircle s : Circle) : ℂ) = 0} = 0 := by
  haveI : NullSingletonClass (volume : Measure UnitAddCircle) := ⟨fun x => by
    have h := AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) 0
    simpa using h⟩
  have hinj : Function.Injective fun s : UnitAddCircle => ((AddCircle.toCircle s : Circle) : ℂ) :=
    Circle.coe_injective.comp (AddCircle.injective_toCircle one_ne_zero)
  have hfin : ({s : UnitAddCircle | r.eval ((AddCircle.toCircle s : Circle) : ℂ) = 0}).Finite := by
    refine Set.Finite.of_finite_image (f := fun s : UnitAddCircle => ((AddCircle.toCircle s : Circle) : ℂ)) ?_ hinj.injOn
    refine (Polynomial.finite_setOf_isRoot hr).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  exact hfin.measure_zero _

theorem UpperTheory.Gal.Gen.nullZero_pf :
    UpperTheory.Gal.Gen.NullZero := by
  intro n
  induction n with
  | zero =>
    intro p hp
    obtain ⟨a, rfl⟩ : ∃ a, p = MvPolynomial.C a := ⟨_, MvPolynomial.eq_C_of_isEmpty p⟩
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hp
    refine Filter.Eventually.of_forall fun θ => ?_
    simpa using ha
  | succ n ih =>
    intro p hp
    have hq : MvPolynomial.finSuccEquiv ℂ n p ≠ 0 := by
      simpa using hp
    have hc := ih (MvPolynomial.finSuccEquiv ℂ n p).leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hq)
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) 0
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) 0 with he
    have hclosed : IsClosed {θ : Fin (n + 1) → UnitAddCircle |
        MvPolynomial.eval (fun i => (pt θ i : ℂ)) p = 0} :=
      isClosed_eq (continuous_eval_pt p) continuous_const
    have hm : MeasurableSet {z : UnitAddCircle × (Fin n → UnitAddCircle) |
        MvPolynomial.eval (fun i => (pt (e.symm z) i : ℂ)) p ≠ 0} :=
      e.symm.measurable hclosed.measurableSet.compl
    have hsymm : ∀ (s : UnitAddCircle) (θ : Fin n → UnitAddCircle),
        e.symm (s, θ) = (Fin.cons s θ : Fin (n + 1) → UnitAddCircle) := by
      intro s θ
      simp [he, MeasurableEquiv.piFinSuccAbove, Fin.insertNth_zero']
    have hprod : ∀ᵐ z ∂(volume.prod volume : Measure (UnitAddCircle × (Fin n → UnitAddCircle))),
        MvPolynomial.eval (fun i => (pt (e.symm z) i : ℂ)) p ≠ 0 := by
      refine (Measure.ae_prod_iff_ae_ae hm).2 ?_
      refine (Measure.ae_ae_comm hm).2 ?_
      filter_upwards [hc] with θ' hθ'
      have hr : Polynomial.map (MvPolynomial.eval (fun i => (pt θ' i : ℂ)))
          (MvPolynomial.finSuccEquiv ℂ n p) ≠ 0 := by
        intro h
        apply hθ'
        rw [Polynomial.leadingCoeff, ← Polynomial.coeff_map, h, Polynomial.coeff_zero]
      refine ae_iff.2 (measure_mono_null ?_ (circle_zero_null _ hr))
      intro s hs
      have hs' : MvPolynomial.eval (fun i => (pt (e.symm (s, θ')) i : ℂ)) p = 0 := by
        by_contra h
        exact hs h
      rw [hsymm, eval_cons_pt] at hs'
      exact hs'
    have := hmp.quasiMeasurePreserving.ae hprod
    filter_upwards [this] with θ hθ
    rw [e.symm_apply_apply] at hθ
    exact hθ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Planch
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

end

private theorem sum_norm_sq_le_integral_of_plancherel {G : Type} [Group G] {n : ℕ} (K : Subgroup G)
    (φ : (Fin n → UnitAddCircle) → G → ℂ) (D S : (Fin n → UnitAddCircle) → ℂ) (f : G → ℂ)
    (T : Finset G) (mr B : ℝ) (N : ℕ) (c : ℂ) (hm : 0 < mr) (hN : 0 < N)
    (hφc : ∀ y, Continuous fun θ => φ θ y) (hDc : Continuous D) (hSc : Continuous S)
    (hB : ∀ θ, ‖D θ‖ ≤ B)
    (hintK : ∀ y ∈ K, c * ∫ θ, φ θ y * D θ = (N : ℂ))
    (hint0 : ∀ y ∉ K, c * ∫ θ, φ θ y * D θ = 0)
    (hA : ∀ θ y, (mr : ℂ) * ∑ g ∈ T, f g * φ θ (y * g) = S θ * φ θ y)
    (hT1 : ∀ g ∈ T, ∀ g' ∈ T, g⁻¹ * g' ∈ K → g = g')
    (hconj : ∀ᵐ θ, ∀ y, φ θ y⁻¹ = starRingEnd ℂ (φ θ y))
    (hone : ∀ θ, φ θ 1 = 1) :
    ∑ g ∈ T, ‖f g‖ ^ 2 ≤ (‖c‖ * B / (mr ^ 2 * N)) * ∫ θ, ‖S θ‖ ^ 2 := by
  classical
  have hI : ∀ u : (Fin n → UnitAddCircle) → ℂ, Continuous u → Integrable u := fun u hu =>
    hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace u)
  have h1 : ∀ g ∈ T, (mr : ℂ) * N * f g = c * ∫ θ, S θ * φ θ g⁻¹ * D θ := by
    intro g hg
    have e : (fun θ => S θ * φ θ g⁻¹ * D θ) =
        fun θ => ∑ g' ∈ T, (mr : ℂ) * f g' * (φ θ (g⁻¹ * g') * D θ) := by
      funext θ
      rw [← hA θ g⁻¹, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun g' _ => by ring
    have hsum := integral_finsetSum T fun g' _ =>
      hI (fun θ => (mr : ℂ) * f g' * (φ θ (g⁻¹ * g') * D θ))
        (continuous_const.mul ((hφc _).mul hDc))
    rw [e, hsum]
    simp_rw [integral_const_mul]
    rw [Finset.mul_sum]
    have hs : ∀ g' ∈ T, c * ((mr : ℂ) * f g' * ∫ θ, φ θ (g⁻¹ * g') * D θ) =
        if g = g' then (mr : ℂ) * N * f g else 0 := by
      intro g' hg'
      rw [show c * ((mr : ℂ) * f g' * ∫ θ, φ θ (g⁻¹ * g') * D θ) =
        (mr : ℂ) * f g' * (c * ∫ θ, φ θ (g⁻¹ * g') * D θ) by ring]
      by_cases hgg : g = g'
      · subst hgg
        rw [inv_mul_cancel, hintK 1 K.one_mem, if_pos rfl]
        ring
      · rw [hint0 _ fun hk => hgg (hT1 g hg g' hg' hk), if_neg hgg]
        simp
    rw [Finset.sum_congr rfl hs, Finset.sum_ite_eq, if_pos hg]
  have h2 : (mr : ℂ) ^ 2 * N * ∑ g ∈ T, ((‖f g‖ ^ 2 : ℝ) : ℂ) =
      c * ∫ θ, ((‖S θ‖ ^ 2 : ℝ) : ℂ) * D θ := by
    calc (mr : ℂ) ^ 2 * N * ∑ g ∈ T, ((‖f g‖ ^ 2 : ℝ) : ℂ)
        = (mr : ℂ) * ∑ g ∈ T, starRingEnd ℂ (f g) * ((mr : ℂ) * N * f g) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          have := Complex.conj_mul' (f g)
          push_cast
          rw [show (mr : ℂ) * (starRingEnd ℂ (f g) * ((mr : ℂ) * N * f g)) =
            (mr : ℂ) ^ 2 * N * (starRingEnd ℂ (f g) * f g) by ring, this]
      _ = (mr : ℂ) * ∑ g ∈ T, starRingEnd ℂ (f g) * (c * ∫ θ, S θ * φ θ g⁻¹ * D θ) := by
          congr 1
          exact Finset.sum_congr rfl fun g hg => by rw [h1 g hg]
      _ = c * ∫ θ, (mr : ℂ) * ∑ g ∈ T, starRingEnd ℂ (f g) * (S θ * φ θ g⁻¹ * D θ) := by
          have hsum := integral_finsetSum T fun g _ =>
            hI (fun θ => starRingEnd ℂ (f g) * (S θ * φ θ g⁻¹ * D θ))
              (continuous_const.mul ((hSc.mul (hφc _)).mul hDc))
          rw [integral_const_mul, hsum]
          simp_rw [integral_const_mul]
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun g _ => by ring
      _ = c * ∫ θ, ((‖S θ‖ ^ 2 : ℝ) : ℂ) * D θ := by
          congr 1
          apply integral_congr_ae
          filter_upwards [hconj] with θ hθ
          have hA1 := hA θ 1
          simp only [one_mul, hone, mul_one] at hA1
          calc (mr : ℂ) * ∑ g ∈ T, starRingEnd ℂ (f g) * (S θ * φ θ g⁻¹ * D θ)
              = S θ * D θ * starRingEnd ℂ ((mr : ℂ) * ∑ g ∈ T, f g * φ θ g) := by
                simp_rw [hθ]
                set_option synthInstance.maxHeartbeats 100000 in
                  rw [map_mul, map_sum, Complex.conj_ofReal]
                simp_rw [map_mul]
                rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
                exact Finset.sum_congr rfl fun g _ => by ring
            _ = ((‖S θ‖ ^ 2 : ℝ) : ℂ) * D θ := by
                rw [hA1, mul_comm (S θ) (D θ), mul_assoc, Complex.mul_conj']
                push_cast
                ring
  have h3 : mr ^ 2 * N * ∑ g ∈ T, ‖f g‖ ^ 2 ≤ ‖c‖ * ((∫ θ, ‖S θ‖ ^ 2) * B) := by
    have hl : mr ^ 2 * N * ∑ g ∈ T, ‖f g‖ ^ 2 =
        ‖(mr : ℂ) ^ 2 * N * ∑ g ∈ T, ((‖f g‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_sum,
        ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [hl, h2, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_mul_const]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => norm_nonneg _)
      (((hSc.norm.pow 2).mul continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (Filter.Eventually.of_forall fun θ => ?_)
    show ‖((‖S θ‖ ^ 2 : ℝ) : ℂ) * D θ‖ ≤ ‖S θ‖ ^ 2 * B
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hB θ) (by positivity)
  have hpos : 0 < mr ^ 2 * (N : ℝ) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [h3]

theorem UpperTheory.Gal.Gen.planch_pf :
    UpperTheory.Gal.Gen.GammaInt → UpperTheory.Gal.Gen.GammaConj → UpperTheory.Gal.Gen.GammaEig → UpperTheory.Gal.Gen.InjAE → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.Planch := by
  intro hInt hConj hEig hInj hDens F _ _ _ _ n _ _ μ _
  have hq : 1 < qF F := by
    unfold qF
    exact Finite.one_lt_card
  have ht0 : (0 : ℝ) ≤ ((qF F : ℝ))⁻¹ := by positivity
  have ht1 : ((qF F : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hq)
  obtain ⟨_, hDc, hev, hunit⟩ := hDens n _ ht0 ht1
  have htc : Complex.ofReal ((qF F : ℝ))⁻¹ = ((qF F : ℂ))⁻¹ := by push_cast; rfl
  rw [htc] at hDc
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn isCompact_univ hDc.continuousOn
  have hm : 0 < μ.real (GLnLocal.integralGL F n) := by
    apply ENNReal.toReal_pos
    · exact ((GLnLocal.isOpen_integralGL F n).measure_pos μ
        ⟨1, (GLnLocal.integralGL F n).one_mem⟩).ne'
    · exact ((GLnLocal.isCompact_integralGL F n).measure_lt_top).ne
  have hI := hInt F n μ
  have hC := hConj F n μ
  refine ⟨‖vPoly n ((qF F : ℂ))⁻¹‖ * B / (μ.real (GLnLocal.integralGL F n) ^ 2 * n.factorial), ?_⟩
  intro h T hT
  refine sum_norm_sq_le_integral_of_plancherel (GLnLocal.integralGL F n) (fun θ y => zonalSpherical μ (pt θ) y)
    (fun θ => dens ((qF F : ℂ))⁻¹ (pt θ)) (fun θ => evalAt (pt θ) (satakeTransform μ h)) _ T
    (μ.real (GLnLocal.integralGL F n)) B n.factorial (vPoly n ((qF F : ℂ))⁻¹) hm n.factorial_pos
    (fun y => (hI y).1) hDc (hev _) (fun θ => hB θ (Set.mem_univ _))
    (fun y hy => by rw [(hI y).2, if_pos hy])
    (fun y hy => by rw [(hI y).2, if_neg hy])
    (fun θ y => ?_) hT.1 ?_ (fun θ => zonalSpherical_one _)
  · rw [← hT.2 (fun x => zonalSpherical μ (pt θ) (y * x)) fun g k hk => by
      rw [← mul_assoc]
      exact zonalSpherical_mul_right _ _ hk]
    exact hEig F n μ (pt θ) h y
  · filter_upwards [hInj n] with θ hθ
    intro y
    exact hC (pt θ) hθ (hunit θ) y
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RFormula
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma det_vand_comp {n : ℕ} (v : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    (Matrix.vandermonde (v ∘ σ)).det =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (Matrix.vandermonde v).det := by
  have h : Matrix.vandermonde (v ∘ σ) = (Matrix.vandermonde v).submatrix σ id := by
    ext i j; simp [Matrix.vandermonde_apply]
  rw [h, Matrix.det_permute]

private lemma prod_prs {n : ℕ} (f : Fin n → Fin n → ℂ) :
    ∏ p ∈ prs n, f p.1 p.2 = ∏ i, ∏ j ∈ Finset.Ioi i, f i j := by
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j; simp

private lemma det_rev {n : ℕ} (v : Fin n → ℂ) :
    (Matrix.vandermonde (v ∘ Fin.revPerm)).det = ∏ p ∈ prs n, (v p.1 - v p.2) := by
  rw [Matrix.det_vandermonde, ← prod_prs (fun i j => (v ∘ Fin.revPerm) j - (v ∘ Fin.revPerm) i)]
  refine Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1))
    (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa [Fin.rev_lt_rev] using hp
  · intro p hp
    simpa [Fin.rev_lt_rev] using hp
  · intro p _; simp
  · intro p _; simp
  · intro p _; simp

private lemma sign_sq_one {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

private lemma prod_comp {n : ℕ} (v : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    ∏ p ∈ prs n, (v (σ p.1) - v (σ p.2)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ p ∈ prs n, (v p.1 - v p.2) := by
  have h1 := det_rev (v ∘ σ)
  have h2 := det_rev v
  rw [det_vand_comp] at h1 h2
  have h3 := det_vand_comp v σ
  simp only [Function.comp_apply] at h1
  rw [← h1, ← h2, h3]
  ring

private lemma evalAt_alternant {n : ℕ} (z : Fin n → ℂˣ) :
    evalAt z (alternant (staircase n)) = ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [alternant_eq_det]
    exact (Finset.prod_of_isEmpty _).symm
  · have h := det_rev (fun i => (z i : ℂ))
    rw [det_vand_comp] at h
    rw [alternant_staircase_eq_vdm hn, map_mul, evalAt_vdm_det, ← h, mul_comm]
    simp

theorem UpperTheory.Gal.Gen.rFormula_pf :
    UpperTheory.Gal.Gen.RFormula := by
  intro n t l z hz
  have hD : ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp h => ?_
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    exact hlt.ne (hz (Units.ext (sub_eq_zero.mp h)))
  have key := congrArg (evalAt z) (alternant_mul_altQuot (monomial l * hlFactor n t))
  rw [map_mul, evalAt_antisymm, evalAt_alternant] at key
  refine mul_left_cancel₀ hD ?_
  have hR : hlR t l = altQuot (monomial l * hlFactor n t) := rfl
  rw [hR, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hs := sign_sq_one σ
  have hc : ∏ p ∈ prs n, ((z (σ p.1) : ℂ) - (z (σ p.2) : ℂ)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) :=
    prod_comp (fun i => (z i : ℂ)) σ
  rw [map_mul, monomial, evalAt_single, one_mul, evalAt_hlFactor, Finset.prod_div_distrib, hc]
  simp only [Function.comp_apply]
  have hs0 : ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one hs
  field_simp
  linear_combination ((monomialChar l (z ∘ σ)) * ∏ p ∈ prs n, ((z (σ p.1) : ℂ) - t * (z (σ p.2) : ℂ))) * hs
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RIntPf
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.rInt_pf :
    UpperTheory.Gal.Gen.InjAE → UpperTheory.Gal.Gen.RDens → UpperTheory.Gal.Gen.HalfInt → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.RInt := by
  intro h1 h2 h3 h4 n t ht0 ht1 l hl
  obtain ⟨hh, -, hev, hnorm⟩ := h4 n t ht0 ht1
  have hpt : ∀ (θ : Fin n → UnitAddCircle) (σ : Equiv.Perm (Fin n)), pt θ ∘ ⇑σ = pt (θ ∘ ⇑σ) :=
    fun _ _ => rfl
  set F : (Fin n → UnitAddCircle) → ℂ := fun θ => monomialChar l (pt θ) * half (t : ℂ) (pt θ) with hF
  have hmc : Continuous fun θ : Fin n → UnitAddCircle => monomialChar l (pt θ) := by
    have := hev (AddMonoidAlgebra.single l 1)
    simpa [evalAt_single] using this
  have hFc : Continuous F := hmc.mul hh
  have hperm : ∀ σ : Equiv.Perm (Fin n),
      ∫ θ : Fin n → UnitAddCircle, F (θ ∘ ⇑σ) = ∫ θ : Fin n → UnitAddCircle, F θ := by
    intro σ
    have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => UnitAddCircle) σ.symm
    rw [← hmp.integral_comp' F]
    congr 1
    funext θ
    congr 1
    funext j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  have hae : (fun θ : Fin n → UnitAddCircle => evalAt (pt θ) (hlR (t : ℂ) l) * dens (t : ℂ) (pt θ)) =ᵐ[volume]
      fun θ => ∑ σ : Equiv.Perm (Fin n), F (θ ∘ ⇑σ) := by
    filter_upwards [h1 n] with θ hθ
    rw [h2 n t ht0 ht1 l (pt θ) hθ (hnorm θ)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hpt]
  rw [integral_congr_ae hae, integral_finsetSum]
  · simp_rw [hperm]
    rw [hF, h3 n t ht0 ht1 l hl, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    split_ifs <;> simp
  · intro σ _
    have hc : Continuous fun θ : Fin n → UnitAddCircle => θ ∘ ⇑σ :=
      continuous_pi fun i => continuous_apply (σ i)
    exact (hFc.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end

