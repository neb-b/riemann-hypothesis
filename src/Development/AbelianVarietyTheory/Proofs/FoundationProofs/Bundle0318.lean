module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0302

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjBlockLowerMemPrincipalSeriesCongruence
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

namespace GlobalTheory.PsType

theorem conj_blockLower_mem_theta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ g ∈ grp ψ, (∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → g.val a b = 0) → z⁻¹ * g * z ∈ grp ψ ∧ theta ψ (z⁻¹ * g * z) = theta ψ g := by
  intro k _ _ _ _ n ψ r ϖ hϖ hv z hz g hg hup
  set d : Fin n → k := fun i => if (i : ℕ) < r then ϖ else 1 with hd
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i; simp only [hd]; split_ifs <;> simp [hϖ]
  have h2 : diagonal (fun i => (d i)⁻¹) * z.val = 1 := by
    rw [hz, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hd0 i)
  have hzi : (z⁻¹).val = diagonal (fun i => (d i)⁻¹) := by
    calc (z⁻¹).val = (diagonal (fun i => (d i)⁻¹) * z.val) * (z⁻¹).val := by rw [h2, Matrix.one_mul]
      _ = diagonal (fun i => (d i)⁻¹) := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hent : ∀ i j, (z⁻¹ * g * z).val i j = (d i)⁻¹ * g.val i j * d j := by
    intro i j
    rw [Units.val_mul, Units.val_mul, hzi, hz, mul_diagonal, diagonal_mul]
  have hupper : ∀ i j : Fin n, i < j → (z⁻¹ * g * z).val i j = g.val i j := by
    intro i j hij
    rw [hent]
    have hij' : (i : ℕ) < j := hij
    by_cases hi : (i : ℕ) < r
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_pos hi, if_pos hj]; field_simp
      · rw [hup i j hi (not_lt.1 hj)]; simp
    · have hj : ¬ (j : ℕ) < r := by omega
      simp only [hd, if_neg hi, if_neg hj]; simp
  have hle : ∀ i j, valuation k ((z⁻¹ * g * z).val i j) ≤ valuation k (g.val i j) := by
    intro i j
    rw [hent]
    by_cases hi : (i : ℕ) < r
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_pos hi, if_pos hj]
        have : ϖ⁻¹ * g.val i j * ϖ = g.val i j := by field_simp
        rw [this]
      · rw [hup i j hi (not_lt.1 hj)]; simp
    · by_cases hj : (j : ℕ) < r
      · simp only [hd, if_neg hi, if_pos hj, inv_one, one_mul, map_mul]
        calc valuation k (g.val i j) * valuation k ϖ ≤ valuation k (g.val i j) * 1 := by
              gcongr
          _ = _ := mul_one _
      · simp only [hd, if_neg hi, if_neg hj]; simp
  have hdet : (z⁻¹ * g * z).val.det = g.val.det := by
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul]
  have hminor : ∀ m, minor (z⁻¹ * g * z) m = minor g m := by
    intro m
    simp only [minor]
    set G := g.val.toSquareBlockProp (fun i => i ≤ m) with hG
    have e : (z⁻¹ * g * z).val.toSquareBlockProp (fun i => i ≤ m) =
        of fun (i j : {a // a ≤ m}) => (d i)⁻¹ * (of fun (i j : {a // a ≤ m}) => d j * G i j) i j := by
      ext i j
      simp only [hG, toSquareBlockProp_def, toBlock_apply, of_apply, hent]
      ring
    rw [e, det_mul_column (fun i : {a // a ≤ m} => (d i)⁻¹), det_mul_row (fun j : {a // a ≤ m} => d j) G,
      ← mul_assoc, ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_one (fun (i : {a // a ≤ m}) _ => inv_mul_cancel₀ (hd0 i.1)), one_mul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hgk := (GlobalTheory.LocStd.mem_KO_iff_det.1 hg.1)
    refine GlobalTheory.LocStd.mem_KO_iff_det.2 ⟨fun i j => ?_, by rw [hdet]; exact hgk.2⟩
    exact (Valuation.mem_integer_iff _ _).2 ((hle i j).trans ((Valuation.mem_integer_iff _ _).1 (hgk.1 i j)))
  · intro i j hij
    rw [hupper i j hij]
    exact hg.2 i j hij
  · simp only [theta, hminor]

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp
open scoped ENNReal Pointwise InnerProductSpace ComplexConjugate

namespace GlobalTheory.CuspAE

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ]
  {μ : Measure G} [μ.IsHaarMeasure] {φ : G → ℂ} {S : Set G}


omit [LocallyCompactSpace G] in
theorem exists_setIntegral_norm_le (hS : IsCompact S) :
    ∃ c : ℝ, ∀ F : L2 Γ μ, ∫ y in S, ‖lift Γ F y‖ ∂μ ≤ c * ‖F‖ := by
  set a : ℝ≥0∞ := ({γ : Γ | (γ : G) ∈ S * S⁻¹}.encard : ℝ≥0∞) with ha
  have ha' : a ≠ ∞ := by simpa [ha] using finite_mem_compact (Γ := Γ) (hS.mul hS.inv)
  have hle : (μ.restrict S).map (mk Γ) ≤ a • quotMeasure Γ μ := Measure.le_iff.2 fun A hA => by
    rw [Measure.map_apply measurable_mk hA, Measure.restrict_apply (measurable_mk hA),
      ← lintegral_indicator_one ((measurable_mk hA).inter hS.measurableSet),
      lintegral_eq_lintegral_tsum (Γ := Γ)
        (measurable_one.indicator ((measurable_mk hA).inter hS.measurableSet)).aemeasurable,
      Measure.smul_apply, smul_eq_mul, ← lintegral_indicator_one hA, ← lintegral_const_mul' _ _ ha']
    refine lintegral_mono fun q => le_trans (le_of_eq (tsum_congr fun γ => ?_))
      (AutomorphicL2Local.tsum_indicator_le Γ S q.out _)
    by_cases h1 : (γ : G) * q.out ∈ S <;> by_cases h2 : q ∈ A <;> simp [h1, h2]
  have hμ : μ S ≠ ∞ := hS.measure_lt_top.ne
  refine ⟨(a ^ (1 / 2 : ℝ) * μ S ^ (1 / 2 : ℝ)).toReal, fun F => ?_⟩
  have hm : AEStronglyMeasurable (lift Γ F) (μ.restrict S) :=
    ((Lp.stronglyMeasurable F).comp_measurable measurable_mk).aestronglyMeasurable
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm
  have h2 : eLpNorm (lift Γ F) 2 (μ.restrict S) ≤ a ^ (1 / 2 : ℝ) * eLpNorm F 2 (quotMeasure Γ μ) := by
    refine (eLpNorm_map_measure (Lp.stronglyMeasurable F).aestronglyMeasurable measurable_mk.aemeasurable).ge.trans
      ((eLpNorm_mono_measure _ hle).trans (le_of_eq ?_))
    rw [eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ (Lp.stronglyMeasurable F).aestronglyMeasurable]
    norm_num
  rw [integral_norm_eq_lintegral_enorm hm, ← eLpNorm_one_eq_lintegral_enorm hm, Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (by have := Lp.eLpNorm_ne_top F; finiteness) (h1.trans ?_)
  rw [mul_right_comm, Measure.restrict_apply_univ]
  norm_num
  gcongr


omit [SecondCountableTopology G] [LocallyCompactSpace G] in
theorem setIntegral_norm_mul_left_le (hi : LocallyIntegrable φ μ) (hS : IsCompact S) {C : Set G} (hC : IsCompact C)
    {k : G} (hk : ∀ y ∈ S, k * y ∈ C) :
    IntegrableOn (fun y => φ (k * y)) S μ ∧ ∫ y in S, ‖φ (k * y)‖ ∂μ ≤ ∫ y in C, ‖φ y‖ ∂μ := by
  have hp := measurePreserving_mul_left μ k
  have he := measurableEmbedding_mulLeft k
  have h1 : IntegrableOn (fun y => φ (k * y)) ((k * ·) ⁻¹' C) μ :=
    (hp.integrableOn_comp_preimage he).2 (hi.integrableOn_isCompact hC)
  refine ⟨h1.mono_set hk, ?_⟩
  rw [← hp.setIntegral_preimage_emb he (fun y => ‖φ y‖) C]
  exact setIntegral_mono_set h1.norm (.of_forall fun _ => norm_nonneg _) (.of_forall hk)


omit [SecondCountableTopology G] [LocallyCompactSpace G] [DiscreteTopology Γ] in
theorem exists_compact_bound (hc : Cocompact Γ N) (hS : IsCompact S) : ∃ C : Set G, IsCompact C ∧
    ∀ φ : G → ℂ, LeftInv Γ φ → LocallyIntegrable φ μ → ∀ n : N,
      IntegrableOn (fun y => φ (n * y)) S μ ∧ ∫ y in S, ‖φ (n * y)‖ ∂μ ≤ ∫ y in C, ‖φ y‖ ∂μ := by
  obtain ⟨K, hK, hs⟩ := hc
  have hC := (hK.image continuous_subtype_val).mul hS
  refine ⟨_, hC, fun φ hφ hi n => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hs n
  simp only [← fun y => leftInv_integrand hφ y γ hγ n]
  exact setIntegral_norm_mul_left_le hi hS hC fun y hy => mul_mem_mul ⟨_, hk, rfl⟩ hy

variable [LocallyCompactSpace N]

theorem integrable_prod (hc : Cocompact Γ N) (hφ : LeftInv Γ φ) (hm : StronglyMeasurable φ)
    (hi : LocallyIntegrable φ μ) (hS : IsCompact S) :
    Integrable (fun p : Quot (Γ.subgroupOf N) × G => φ ((p.1.out : N) * p.2))
      ((probMeasure Γ N).prod (μ.restrict S)) := by
  have := hc.isProbabilityMeasure
  obtain ⟨C, -, hC⟩ := exists_compact_bound (μ := μ) hc hS
  have e : (fun p : Quot (Γ.subgroupOf N) × G => φ ((p.1.out : N) * p.2)) =
      fun p => φ ((sec (Γ.subgroupOf N) p.1 : N) * p.2) := funext fun p =>
    (leftInv_integrand hφ p.2).eq_of_mk_eq ((Quotient.out_eq _).trans (mk_sec _).symm)
  have hsec : Measurable (sec (Γ.subgroupOf N)) := by
    intro s hs
    have h : mk (Γ.subgroupOf N) ⁻¹' (sec (Γ.subgroupOf N) ⁻¹' s) =
        ⋃ γ : Γ.subgroupOf N, (fun x : N => (γ : N) * x) ⁻¹' (s ∩ stdDom (Γ.subgroupOf N)) := by
      ext x
      simp only [mem_preimage, mem_iUnion, mem_inter_iff]
      refine ⟨fun h => ?_, fun ⟨γ, h1, h2⟩ => by rwa [sec_eq h2 (mk_mul γ x)]⟩
      obtain ⟨γ, e⟩ := mk_eq_iff.1 (mk_sec (mk (Γ.subgroupOf N) x)).symm
      exact ⟨γ, e ▸ h, e ▸ sec_mem _⟩
    change MeasurableSet (mk (Γ.subgroupOf N) ⁻¹' (sec (Γ.subgroupOf N) ⁻¹' s))
    rw [h]
    exact .iUnion fun γ => measurable_const_mul _ (hs.inter (measurableSet_stdDom _))
  have hm' : StronglyMeasurable fun p : Quot (Γ.subgroupOf N) × G => φ ((p.1.out : N) * p.2) :=
    e ▸ hm.comp_measurable
      ((measurable_subtype_coe.comp (hsec.comp measurable_fst)).mul measurable_snd)
  refine (integrable_prod_iff hm'.aestronglyMeasurable).2 ⟨.of_forall fun q => (hC φ hφ hi q.out).1, ?_⟩
  refine .of_bound hm'.norm.integral_prod_right'.aestronglyMeasurable (∫ y in C, ‖φ y‖ ∂μ) (.of_forall fun q => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact (hC φ hφ hi q.out).2

theorem setIntegral_constTermOn (hc : Cocompact Γ N) (hφ : LeftInv Γ φ) (hm : StronglyMeasurable φ)
    (hi : LocallyIntegrable φ μ) (hS : IsCompact S) :
    ∫ y in S, constTermOn Γ N φ y ∂μ = ∫ q, ∫ y in S, φ ((q.out : N) * y) ∂μ ∂probMeasure Γ N := by
  have := hc.isProbabilityMeasure
  exact (integral_integral_swap (f := fun (q : Quot (Γ.subgroupOf N)) y => φ ((q.out : N) * y))
    (integrable_prod hc hφ hm hi hS)).symm

theorem locallyIntegrable_constTermOn (hc : Cocompact Γ N) (hφ : LeftInv Γ φ) (hm : StronglyMeasurable φ)
    (hi : LocallyIntegrable φ μ) : LocallyIntegrable (constTermOn Γ N φ) μ := by
  have := hc.isProbabilityMeasure
  exact locallyIntegrable_iff.2 fun S hS => (integrable_prod hc hφ hm hi hS).integral_prod_right

theorem constTermOn_convR (hc : Cocompact Γ N) (hφ : LeftInv Γ φ) (hm : StronglyMeasurable φ)
    (hi : LocallyIntegrable φ μ) {f : G → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) (x : G) :
    constTermOn Γ N (convR μ f φ) x = convR μ f (constTermOn Γ N φ) x := by
  have := hc.isProbabilityMeasure
  have hs' : HasCompactSupport fun y => f (x⁻¹ * y) := hs.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hs
  have h0 : ∀ u : G → ℂ, ∫ y in tsupport fun y => f (x⁻¹ * y), f (x⁻¹ * y) * u y ∂μ = ∫ y, f (x⁻¹ * y) * u y ∂μ :=
    fun u => setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [image_eq_zero_of_notMem_tsupport (f := fun y => f (x⁻¹ * y)) hy, zero_mul]
  have h1 := integral_integral_swap
    (f := fun (q : Quot (Γ.subgroupOf N)) y => f (x⁻¹ * y) * φ ((q.out : N) * y))
    ((integrable_prod hc hφ hm hi hs'.isCompact).bdd_mul (c := M)
      (Continuous.aestronglyMeasurable (f := fun y => f (x⁻¹ * y)) (by fun_prop)).comp_snd (.of_forall fun _ => hM _))
  simp only [h0, integral_const_mul] at h1
  rw [convR_eq]
  refine Eq.trans (integral_congr_ae (.of_forall fun q => ?_)) h1
  beta_reduce
  rw [← integral_mul_left_eq_self _ x]
  simp [convR, mul_assoc]

variable [μ.IsMulRightInvariant]


omit [LocallyCompactSpace N] in
theorem locallyIntegrable_lift (F : L2 Γ μ) : LocallyIntegrable (lift Γ F) μ :=
  locallyIntegrable_iff.2 fun C hC => (AutomorphicL2Local.memLp_restrict_compact G Γ μ F C hC).2

theorem continuous_setIntegral_constTermOn (hc : Cocompact Γ N) (hS : IsCompact S) :
    Continuous fun F : L2 Γ μ => ∫ y in S, constTermOn Γ N (lift Γ F) y ∂μ := by
  have := hc.isProbabilityMeasure
  obtain ⟨C, hC, h⟩ := exists_compact_bound (μ := μ) hc hS
  obtain ⟨c, hb⟩ := exists_setIntegral_norm_le (Γ := Γ) (μ := μ) hC
  have hm : ∀ F : L2 Γ μ, StronglyMeasurable (lift Γ F) := fun F =>
    (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  refine (LipschitzWith.of_dist_le' (K := c) fun F F' => ?_).continuous
  have hp := fun F : L2 Γ μ =>
    (integrable_prod hc (leftInv_lift F) (hm F) (locallyIntegrable_lift F) hS).integral_prod_left
  have h' := fun F : L2 Γ μ => h _ (leftInv_lift F) (locallyIntegrable_lift F)
  simp only [setIntegral_constTermOn hc (leftInv_lift _) (hm _) (locallyIntegrable_lift _) hS, dist_eq_norm]
  rw [← integral_sub (hp F) (hp F')]
  refine (norm_integral_le_of_norm_le_const (C := c * ‖F - F'‖) (.of_forall fun q => ?_)).trans (by simp)
  rw [← integral_sub (h' F q.out).1 (h' F' q.out).1]
  refine (norm_integral_le_integral_norm _).trans (le_trans (le_of_eq ?_) ((h' (F - F') q.out).2.trans (hb _)))
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [(measurePreserving_mul_left μ ((q.out : N) : G)).quasiMeasurePreserving.ae
    (ae_quotMeasure_iff.1 (Lp.coeFn_sub F F'))] with y hy
  exact congrArg norm hy.symm

theorem constTermOn_ae_eq_zero (hc : Cocompact Γ N) {F : L2 Γ μ} (hF : F ∈ closure {F : L2 Γ μ |
    ∃ φ, Continuous φ ∧ LeftInv Γ φ ∧ constTermOn Γ N φ = 0 ∧ lift Γ F =ᵐ[μ] φ}) :
    constTermOn Γ N (lift Γ F) =ᵐ[μ] 0 := by
  have hm : ∀ F : L2 Γ μ, StronglyMeasurable (lift Γ F) := fun F =>
    (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    (locallyIntegrable_constTermOn hc (leftInv_lift _) (hm F) (locallyIntegrable_lift F)) fun S hS => ?_
  refine closure_minimal ?_ (isClosed_eq (continuous_setIntegral_constTermOn hc hS) continuous_const) hF
  rintro F' ⟨φ, h1, h2, h3, h4⟩
  have h5 := setIntegral_constTermOn (μ := μ) hc h2 h1.stronglyMeasurable h1.locallyIntegrable hS
  rw [h3] at h5
  rw [mem_setOf_eq, setIntegral_constTermOn hc (leftInv_lift _) (hm _) (locallyIntegrable_lift _) hS]
  refine Eq.trans (integral_congr_ae (.of_forall fun q => integral_congr_ae (ae_restrict_of_ae ?_)))
    (h5.symm.trans (by simp))
  exact (measurePreserving_mul_left μ ((q.out : N) : G)).quasiMeasurePreserving.ae h4


omit [LocallyCompactSpace N] in
theorem mem_of_forall_Rop_mem {W : Submodule ℂ (L2 Γ μ)} (hW : IsClosed (W : Set (L2 Γ μ))) {F : L2 Γ μ}
    (h : ∀ f : G → ℂ, Continuous f → HasCompactSupport f → Rop Γ μ f F ∈ W) : F ∈ W := by
  have := hW.completeSpace_coe
  rw [← W.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro w hw
  have hu : Continuous fun g => ⟪w, R Γ μ g F⟫_ℂ := continuous_const.inner (continuous_R F)
  obtain ⟨b, hb1, -, hbc, hb⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : G)))
    isClosed_empty (disjoint_empty _)
  have hf : Continuous fun g => (b g : ℂ) * conj ⟪w, R Γ μ g F⟫_ℂ := by fun_prop
  have hs : HasCompactSupport fun g => (b g : ℂ) * conj ⟪w, R Γ μ g F⟫_ℂ :=
    (hbc.comp_left (g := Complex.ofReal) rfl).mul_right
  have hR := isRepOp_Rop (Γ := Γ) (hf.integrable_of_hasCompactSupport hs (μ := μ)) F
  have h1 := (W.mem_orthogonal' _).1 hw _ (h _ hf hs)
  rw [hR.2] at h1
  replace h1 := (integral_inner (𝕜 := ℂ) hR.1 w).trans h1
  have h2 : ∫ g, b g * ‖⟪w, R Γ μ g F⟫_ℂ‖ ^ 2 ∂μ = 0 := by
    rw [← Complex.ofReal_inj, ← integral_complex_ofReal, Complex.ofReal_zero, ← h1]
    refine integral_congr_ae (.of_forall fun g => ?_)
    beta_reduce
    rw [inner_smul_right, mul_assoc, Complex.conj_mul']
    simp
  by_contra h0
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (b.continuous.mul (hu.norm.pow 2)) hbc.mul_right
    (fun g => mul_nonneg (hb g).1 (sq_nonneg _)) ?_).ne' h2
  simpa [hb1 (mem_singleton _)] using h0

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_L2cusp_iff_isCuspAE : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (F : DividedPowerChartLift V μ), F ∈ L2cusp V μ ↔ IsCuspAE V μ F := by
  intro D V μ _ _ F
  refine ⟨fun h 𝔉 h𝔉 => constTermOn_ae_eq_zero (cocompact_flag D V 𝔉) (closure_mono ?_ h), fun h => ?_⟩
  · rintro F' ⟨φ, hφ, e⟩
    exact ⟨φ, hφ.1, hφ.2.1, T.constantTermAlongFlag_eq_zero_of_cuspidal D V φ hφ 𝔉 h𝔉, e⟩
  · refine mem_of_forall_Rop_mem (isSubrep_L2cusp V μ).1 fun f hf hs => ?_
    have hl := (leftInv_lift (Γ := GQ V) F).convR (μ := μ) f
    refine mem_L2cusp_of_ae_eq ⟨(AutomorphicL2Local.continuous_convR_lift _ _ μ f hf hs F).2, hl,
      isCuspFun_of_forall_flag hl fun 𝔉 h𝔉 => funext fun x => ?_⟩
      (AutomorphicL2Pointwise.lift_Rop_eq_convR _ _ μ f (hf.integrable_of_hasCompactSupport hs) F).2
    refine (constTermOn_convR (cocompact_flag D V 𝔉) (leftInv_lift _)
      ((Lp.stronglyMeasurable F).comp_measurable measurable_mk) (locallyIntegrable_lift F) hf hs x).trans ?_
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [(measurePreserving_mul_left μ x).quasiMeasurePreserving.ae (h 𝔉 h𝔉)] with y hy
    exact mul_eq_zero_of_right _ hy

end GlobalTheory.CuspAE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsStripClearingUpperRightPrincipalSeriesCong
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

namespace GlobalTheory.PsType.ClearBlock

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_congr (χ : kˣ →* ℂˣ) {x y : k} (h : valuation k x = valuation k y) : Triv χ x ↔ Triv χ y := by
  unfold Triv; rw [h]

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ 0 := by
  intro u _ h
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm (by simpa using h) zero_le'
  rw [Valuation.zero_iff, sub_eq_zero] at h0
  have : u = 1 := Units.ext h0
  simp [this]

theorem res_zero_iff (x : 𝒪[k]) : IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem val_det_eq_one {n r : ℕ} {M M' : Matrix (Fin n) (Fin n) k}
    (hM : ∀ i j, valuation k (M i j) ≤ 1) (hM' : ∀ i j, valuation k (M' i j) ≤ 1)
    (hsame : ∀ i j : Fin n, ((i : ℕ) < r ↔ (j : ℕ) < r) → M i j = M' i j)
    (hur : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → valuation k (M i j) < 1)
    (hur' : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → valuation k (M' i j) < 1)
    (hd : valuation k M.det = 1) : valuation k M'.det = 1 := by
  let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨M i j, (Valuation.mem_integer_iff _ _).2 (hM i j)⟩
  let A' : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨M' i j, (Valuation.mem_integer_iff _ _).2 (hM' i j)⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = M := rfl
  have hA' : (algebraMap 𝒪[k] k).mapMatrix A' = M' := rfl
  have hI := Valuation.integer.integers (valuation k)
  have key : ∀ B : Matrix (Fin n) (Fin n) 𝒪[k], (∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → valuation k (B i j : k) < 1) →
      ((IsLocalRing.residue 𝒪[k]).mapMatrix B).det =
        (toSquareBlockProp ((IsLocalRing.residue 𝒪[k]).mapMatrix B) (fun i => r ≤ (i : ℕ))).det *
        (toSquareBlockProp ((IsLocalRing.residue 𝒪[k]).mapMatrix B) (fun i => ¬ r ≤ (i : ℕ))).det := by
    intro B hB
    refine twoBlockTriangular_det _ _ fun i hi j hj => ?_
    exact (res_zero_iff _).2 (hB i j (by omega) hj)
  have e1 : ((IsLocalRing.residue 𝒪[k]).mapMatrix A).det = ((IsLocalRing.residue 𝒪[k]).mapMatrix A').det := by
    rw [key A hur, key A' hur']
    congr 2
    · ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toSquareBlockProp_def, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      congr 1; exact Subtype.ext (hsame i j (by omega))
    · ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toSquareBlockProp_def, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      congr 1; exact Subtype.ext (hsame i j (by omega))
  have u1 : IsUnit A.det := hI.isUnit_iff_valuation_eq_one.2 (by rw [RingHom.map_det, hA, hd])
  have u2 : IsUnit A'.det := by
    by_contra hc
    have h0 : IsLocalRing.residue 𝒪[k] A'.det = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hc
    rw [RingHom.map_det, ← e1, ← RingHom.map_det, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h0
    exact h0 u1
  have := hI.isUnit_iff_valuation_eq_one.1 u2
  rwa [RingHom.map_det, hA'] at this

end GlobalTheory.PsType.ClearBlock

namespace GlobalTheory.PsType


open ClearBlock in
theorem clear_upper_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), Ordered ψ → Cut ψ r → ∀ j ∈ grp ψ, ∃ y ∈ strip ψ r ϖ 0,
      ∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → (y⁻¹ * j).val a b = 0 := by
  intro k _ _ _ _ n ψ r ϖ hord hcut g hg
  have hint : ∀ a b, valuation k (g.val a b) ≤ 1 := GlobalTheory.BlockType.val_le_one_of_mem_KO hg.1
  have hur : ∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → valuation k (g.val a b) < 1 := by
    intro a b ha hb
    refine lt_of_le_of_ne (hint a b) fun h1 => hcut a b ha hb ?_
    exact (triv_congr _ (h1.trans (map_one _).symm)).1 (hg.2 a b (Fin.lt_iff_val_lt_val.2 (by omega)))
  have hdet : valuation k g.val.det = 1 := (GlobalTheory.LocStd.mem_KO_iff_det.1 hg.1).2
  obtain ⟨Dm, hDm⟩ : ∃ Dm : Matrix (Fin n) (Fin n) k, ∀ a b, Dm a b = if ((a : ℕ) < r ↔ (b : ℕ) < r) then g.val a b else 0 :=
    ⟨fun a b => _, fun _ _ => rfl⟩
  obtain ⟨Um, hUm⟩ : ∃ Um : Matrix (Fin n) (Fin n) k, ∀ a b, Um a b = if r ≤ (a : ℕ) ∧ (b : ℕ) < r then 0 else g.val a b :=
    ⟨fun a b => _, fun _ _ => rfl⟩
  have hDint : ∀ a b, valuation k (Dm a b) ≤ 1 := fun a b => by
    rw [hDm]; split_ifs
    · exact hint a b
    · simp
  have hUint : ∀ a b, valuation k (Um a b) ≤ 1 := fun a b => by
    rw [hUm]; split_ifs
    · simp
    · exact hint a b
  have hDdet : valuation k Dm.det = 1 :=
    val_det_eq_one hint hDint (fun a b h => by rw [hDm, if_pos h]) hur
      (fun a b ha hb => by rw [hDm, if_neg (by omega)]; simp) hdet
  have hUdet : valuation k Um.det = 1 :=
    val_det_eq_one hint hUint (fun a b h => by rw [hUm, if_neg (by omega)]) hur
      (fun a b ha hb => by rw [hUm, if_neg (by omega)]; exact hur a b ha hb) hdet
  obtain ⟨Dg, hDK, hDv⟩ := GlobalTheory.LocStd.mem_image_KO.2
    ⟨fun a b => (Valuation.mem_integer_iff _ _).2 (hDint a b), hDdet⟩
  obtain ⟨Ug, hUK, hUv⟩ := GlobalTheory.LocStd.mem_image_KO.2
    ⟨fun a b => (Valuation.mem_integer_iff _ _).2 (hUint a b), hUdet⟩
  have hD : Dg ∈ grp ψ := ⟨hDK, fun a b hab => by
    rw [hDv, hDm]; split_ifs
    · exact hg.2 a b hab
    · exact triv_zero _⟩
  have hU : Ug ∈ grp ψ := ⟨hUK, fun a b hab => by
    rw [hUv, hUm]; split_ifs
    · exact triv_zero _
    · exact hg.2 a b hab⟩
  have hy : Ug * Dg⁻¹ ∈ grp ψ := _root_.GlobalTheory.PsType.grp_mul_closed k n ψ hord Ug hU _ (_root_.GlobalTheory.PsType.grp_inv_mem k n ψ hord Dg hD)
  set Di : Matrix (Fin n) (Fin n) k := ((Dg⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hDi
  have hDi1 : Dm * Di = 1 := by rw [← hDv]; exact Dg.mul_inv
  have hDi2 : Di * Dm = 1 := by rw [← hDv]; exact Dg.inv_mul
  let Q : Matrix (Fin n) (Fin n) k := diagonal fun a => if (a : ℕ) < r then (0 : k) else 1
  have hDQ : Dm * Q = Q * Dm := by
    ext a b
    simp only [Q, mul_diagonal, diagonal_mul, hDm]
    by_cases ha : (a : ℕ) < r <;> by_cases hb : (b : ℕ) < r <;> simp [ha, hb]
  have hQDi : Di * Q = Q * Di := calc
    Di * Q = Di * Q * (Dm * Di) := by rw [hDi1, Matrix.mul_one]
    _ = Di * (Dm * Q) * Di := by rw [hDQ]; simp only [Matrix.mul_assoc]
    _ = (Di * Dm) * Q * Di := by simp only [Matrix.mul_assoc]
    _ = Q * Di := by rw [hDi2, Matrix.one_mul]
  have hDioff : ∀ l b : Fin n, r ≤ (l : ℕ) → (b : ℕ) < r → Di l b = 0 := by
    intro l b hl hb
    have := congrFun (congrFun hQDi l) b
    simp only [Q, mul_diagonal, diagonal_mul, if_pos hb, if_neg (Nat.not_lt.2 hl)] at this
    simpa using this.symm
  refine ⟨Ug * Dg⁻¹, ?_, ?_⟩
  · have hyv : (Ug * Dg⁻¹).val = (Um - Dm) * Di + 1 := by
      rw [Units.val_mul, hUv, Matrix.sub_mul, hDi1, sub_add_cancel]
    intro a b
    split_ifs with hab
    · rw [pow_zero, one_mul]
      exact ⟨GlobalTheory.BlockType.val_le_one_of_mem_KO hy.1 a b,
        hy.2 a b (Fin.lt_iff_val_lt_val.2 (by omega))⟩
    · rw [hyv, Matrix.add_apply, Matrix.mul_apply]
      rw [Finset.sum_eq_zero, zero_add]
      intro l _
      rw [Matrix.sub_apply]
      by_cases ha : (a : ℕ) < r
      · have hb : (b : ℕ) < r := by omega
        by_cases hl : (l : ℕ) < r
        · simp [hUm, hDm, ha, hl, Nat.not_le.2 ha]
        · rw [hDioff l b (by omega) hb, mul_zero]
      · by_cases hl : (l : ℕ) < r <;> simp [hUm, hDm, ha, hl]
  · intro a b ha hb
    set Ui : Matrix (Fin n) (Fin n) k := ((Ug⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hUi
    have hUi1 : Ui * Um = 1 := by rw [← hUv]; exact Ug.inv_mul
    have e : ((Ug * Dg⁻¹)⁻¹ * g).val = Dm + Dm * Ui * (g.val - Um) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, hDv, Matrix.mul_sub, Matrix.mul_assoc Dm Ui Um, hUi1,
        Matrix.mul_one, add_sub_cancel]
    rw [e, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero]
    · rw [hDm, if_neg (by omega), zero_add]
    · intro l _
      rw [Matrix.sub_apply, hUm, if_neg (by omega), sub_self, mul_zero]

end GlobalTheory.PsType
end
end

