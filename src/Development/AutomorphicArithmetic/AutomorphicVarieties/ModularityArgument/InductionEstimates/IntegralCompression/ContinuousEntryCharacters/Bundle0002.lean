module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

private abbrev M4 : Type := Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ
private abbrev MS : Type := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ

private noncomputable def rx (M : MS) : M4 := reindex finSumFinEquiv finSumFinEquiv M

private theorem rx_mul (M N : MS) : rx M * rx N = rx (M * N) := by
  simp [rx, reindex_apply, submatrix_mul_equiv]

private theorem rx_star (M : MS) : star (rx M) = rx (star M) := by
  ext i j
  simp [rx, reindex_apply, star_eq_conjTranspose]

private theorem rx_one : rx (1 : MS) = 1 := by
  simp [rx, reindex_apply]

private theorem rx_mem {M : MS} (h : M * star M = 1) : rx M ∈ unitaryGroup (Fin (2 + 2)) ℂ := by
  rw [mem_unitaryGroup_iff, rx_star, rx_mul, h, rx_one]

private theorem blk_mem (a b : U2) :
    rx (fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ)) ∈
      unitaryGroup (Fin (2 + 2)) ℂ := by
  apply rx_mem
  rw [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply]
  have ha := mem_unitaryGroup_iff.1 a.2
  have hb := mem_unitaryGroup_iff.1 b.2
  rw [star_eq_conjTranspose] at ha hb
  simp [ha, hb, fromBlocks_one]

private theorem bd_val (a b : U2) : (bd a b : M4) =
    rx (fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ)) :=
  Classical.epsilon_spec (p := fun k : U4 => (k : M4) =
    reindex finSumFinEquiv finSumFinEquiv (fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ)))
    ⟨⟨_, blk_mem a b⟩, rfl⟩

private theorem sw_mem : rx (fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∈
    unitaryGroup (Fin (2 + 2)) ℂ := by
  apply rx_mem
  rw [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply]
  simp [fromBlocks_one]

private theorem long_weyl_element_val : (w4 : M4) = rx (fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0) :=
  Classical.epsilon_spec (p := fun k : U4 => (k : M4) =
    reindex finSumFinEquiv finSumFinEquiv (fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0))
    ⟨⟨_, sw_mem⟩, rfl⟩

private theorem dg_mem (θ : Fin (2 + 2) → ℝ) :
    (diagonal fun i => Complex.exp (Complex.I * θ i) : M4) ∈ unitaryGroup (Fin (2 + 2)) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext i
  change Complex.exp (Complex.I * θ i) * star (Complex.exp (Complex.I * θ i)) = 1
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

private theorem dg_val (θ : Fin (2 + 2) → ℝ) :
    (dg θ : M4) = diagonal fun i => Complex.exp (Complex.I * θ i) :=
  Classical.epsilon_spec (p := fun k : U4 => (k : M4) = diagonal fun i => Complex.exp (Complex.I * θ i))
    ⟨⟨_, dg_mem θ⟩, rfl⟩

private theorem bd_mul (a b a' b' : U2) : bd a b * bd a' b' = bd (a * a') (b * b') := by
  apply Subtype.ext
  show (bd a b : M4) * (bd a' b' : M4) = (bd (a * a') (b * b') : M4)
  rw [bd_val, bd_val, bd_val, rx_mul, fromBlocks_multiply]
  simp

private theorem bd_one : bd 1 1 = 1 := by
  apply Subtype.ext
  show (bd 1 1 : M4) = 1
  rw [bd_val]
  simp [fromBlocks_one, rx_one]

private theorem bd_cont : Continuous (fun p : U2 × U2 => bd p.1 p.2) := by
  refine continuous_induced_rng.2 ?_
  have : (fun p : U2 × U2 => ((bd p.1 p.2 : U4) : M4)) = fun p : U2 × U2 =>
      rx (fromBlocks (p.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (p.2 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    funext p; exact bd_val _ _
  show Continuous (fun p : U2 × U2 => ((bd p.1 p.2 : U4) : M4))
  rw [this]
  simp only [rx, reindex_apply]
  refine Continuous.matrix_submatrix ?_ _ _
  exact Continuous.matrix_fromBlocks (continuous_subtype_val.comp continuous_fst) continuous_const
    continuous_const (continuous_subtype_val.comp continuous_snd)

private theorem long_weyl_element_sq : w4 * w4 = 1 := by
  apply Subtype.ext
  show (w4 : M4) * (w4 : M4) = 1
  rw [long_weyl_element_val, rx_mul, fromBlocks_multiply]
  simp [fromBlocks_one, rx_one]

private theorem long_weyl_swaps_block_diagonal (a b : U2) : w4 * bd a b = bd b a * w4 := by
  apply Subtype.ext
  show (w4 : M4) * (bd a b : M4) = (bd b a : M4) * (w4 : M4)
  rw [long_weyl_element_val, bd_val, bd_val, rx_mul, rx_mul, fromBlocks_multiply, fromBlocks_multiply]
  simp

private theorem dg_neg (θ : Fin (2 + 2) → ℝ) : dg θ * dg (-θ) = 1 := by
  apply Subtype.ext
  show (dg θ : M4) * (dg (-θ) : M4) = 1
  rw [dg_val, dg_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← Complex.exp_add]
  simp

private theorem dg_bd (a b c d : ℝ) : dg ![a, b, c, d] = bd (tC a b) (tC c d) := by
  apply Subtype.ext
  show (dg ![a, b, c, d] : M4) = (bd (tC a b) (tC c d) : M4)
  rw [dg_val, bd_val]
  have e0 : (finSumFinEquiv (m := 2) (n := 2)).symm 0 = Sum.inl 0 := by
    rw [Equiv.symm_apply_eq]; rfl
  have e1 : (finSumFinEquiv (m := 2) (n := 2)).symm 1 = Sum.inl 1 := by
    rw [Equiv.symm_apply_eq]; rfl
  have e2 : (finSumFinEquiv (m := 2) (n := 2)).symm 2 = Sum.inr 0 := by
    rw [Equiv.symm_apply_eq]; rfl
  have e3 : (finSumFinEquiv (m := 2) (n := 2)).symm 3 = Sum.inr 1 := by
    rw [Equiv.symm_apply_eq]; rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rx, reindex_apply, mul_comm, e0, e1, e2, e3]

private theorem chi_inj (ν ν' : Fin (2 + 2) → ℤ) (h : ∀ θ, chi ν θ = chi ν' θ) : ν = ν' := by
  funext i
  by_contra hne
  have hd : ((ν i - ν' i : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 hne
  set t : ℝ := Real.pi / ((ν i - ν' i : ℤ) : ℝ) with ht
  have h1 := h (Pi.single i t)
  simp only [chi] at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
  have s : ∀ μ : Fin (2 + 2) → ℤ, ∑ j, (μ j : ℂ) * ((Pi.single i t : Fin (2 + 2) → ℝ) j : ℂ) = (μ i : ℂ) * t := by
    intro μ
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  rw [s, s] at hn
  have hdC : ((ν i : ℂ) - (ν' i : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 hne
  have htC : (t : ℂ) = (Real.pi : ℂ) / ((ν i : ℂ) - (ν' i : ℂ)) := by
    simp [ht]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : ((ν i : ℂ) - (ν' i : ℂ)) * t = 2 * n * Real.pi := by
    have : Complex.I * (((ν i : ℂ) - (ν' i : ℂ)) * t) = Complex.I * (2 * n * Real.pi) := by
      linear_combination hn
    exact mul_left_cancel₀ Complex.I_ne_zero this
  rw [htC, mul_div_cancel₀ _ hdC] at key
  have k2 : (1 : ℂ) = 2 * n := by
    apply mul_right_cancel₀ hpi
    linear_combination key
  have k3 : (1 : ℤ) = 2 * n := by exact_mod_cast k2
  omega

private noncomputable def hm : Measure U4 := Measure.haarMeasure ⊤

private theorem hm_haar : Haar4 hm ∧ hm.IsOpenPosMeasure := by
  haveI : hm.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  haveI : IsProbabilityMeasure hm := ⟨by
    simpa [hm] using Measure.haarMeasure_self (G := U4) (K₀ := ⊤)⟩
  haveI : hm.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    haveI : (Measure.map (· * g) hm).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right hm g
    haveI : IsProbabilityMeasure (Measure.map (· * g) hm) :=
      inferInstance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  haveI : hm.IsInvInvariant := by
    refine ⟨?_⟩
    haveI : hm.inv.IsHaarMeasure :=
      { lt_top_of_isCompact := fun K hK => by
          rw [Measure.inv_apply]; exact hK.inv.measure_lt_top
        toIsOpenPosMeasure := ⟨fun U hU hne => by
          rw [Measure.inv_apply]; exact hU.inv.measure_ne_zero hm (by simpa using hne)⟩ }
    haveI : IsProbabilityMeasure hm.inv := by
      rw [Measure.inv]; infer_instance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  exact ⟨⟨inferInstance, fun k => measurePreserving_mul_left hm k,
    fun k => measurePreserving_mul_right hm k, Measure.measurePreserving_inv hm⟩, inferInstance⟩

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4 :
    (∀ a b : U2, (bd a b : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) = reindex finSumFinEquiv finSumFinEquiv (fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ))) ∧
      (∀ a b a' b', bd a b * bd a' b' = bd (a * a') (b * b')) ∧ bd 1 1 = 1 ∧ (∀ a b, (bd a b)⁻¹ = bd a⁻¹ b⁻¹) ∧ Continuous (fun p : U2 × U2 => bd p.1 p.2) ∧
      w4 * w4 = 1 ∧ (∀ a b, w4 * bd a b = bd b a * w4) ∧ (∀ θ, (dg θ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) = diagonal fun i => Complex.exp (Complex.I * θ i)) ∧
      (∀ a b c d : ℝ, dg ![a, b, c, d] = bd (tC a b) (tC c d)) ∧ (∀ θ, (dg θ)⁻¹ = dg (-θ)) ∧
      (∀ ν ν', (∀ θ, chi ν θ = chi ν' θ) → ν = ν') ∧ CompactSpace U4 ∧ ∃ μ : Measure U4, Haar4 μ ∧ μ.IsOpenPosMeasure := by
  refine ⟨bd_val, bd_mul, bd_one, fun a b => ?_, bd_cont, long_weyl_element_sq, long_weyl_swaps_block_diagonal, dg_val, dg_bd,
    fun θ => inv_eq_of_mul_eq_one_right (dg_neg θ), chi_inj, inferInstance, hm, hm_haar.1, hm_haar.2⟩
  apply inv_eq_of_mul_eq_one_right
  rw [bd_mul, mul_inv_cancel, mul_inv_cancel, bd_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.RepsRight
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem simp_int {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (ν : Measure X) [IsFiniteMeasure ν]
    (s : SimpleFunc X X) (F : X → E) : ∫ k, F (s k) ∂ν = ∑ x ∈ s.range, ν.real (s ⁻¹' {x}) • F x := by
  have h : (fun k => F (s k)) = fun k => ∑ x ∈ s.range, (s ⁻¹' {x}).indicator (fun _ => F x) k := by
    funext k
    rw [Finset.sum_eq_single (s k)]
    · simp
    · intro b _ hb
      exact Set.indicator_of_notMem (by simpa using fun h => hb h.symm) _
    · intro h
      exact absurd (s.mem_range_self k) h
  rw [h, integral_finsetSum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_indicator_const _ (s.measurableSet_preimage _)]
  · intro x _
    exact (integrable_const (F x)).indicator (s.measurableSet_preimage _)

private theorem simp_lim {X E : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure X) [IsFiniteMeasure ν] (s : ℕ → SimpleFunc X X) (hs : ∀ k, Tendsto (fun i => s i k) atTop (𝓝 k)) (G : X → E) (hG : Continuous G) :
    Tendsto (fun i => ∫ k, G (s i k) ∂ν) atTop (𝓝 (∫ k, G k ∂ν)) := by
  obtain ⟨C, hC⟩ := (isCompact_range hG).isBounded.exists_norm_le
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun i => ?_) (integrable_const C) (fun i => Eventually.of_forall fun k => hC _ ⟨_, rfl⟩)
    (Eventually.of_forall fun k => (hG.tendsto k).comp (hs k))
  exact ((s i).map G).aestronglyMeasurable

private theorem cont_int {X Y : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    (ν : Measure X) [IsFiniteMeasure ν] (f : Y → X → ℂ) (hf : Continuous fun p : Y × X => f p.1 p.2) :
    Continuous fun y => ∫ k, f y k ∂ν := by
  let c : C(Y, C(X, ℂ)) := ContinuousMap.curry ⟨fun p : Y × X => f p.1 p.2, hf⟩
  have hI : Continuous fun g : C(X, ℂ) => ∫ k, g k ∂ν := by
    refine Metric.continuous_iff.2 fun g ε hε => ?_
    refine ⟨ε / (ν.real Set.univ + 1), by positivity, fun h hh => ?_⟩
    rw [dist_eq_norm, ← integral_sub (h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have hb : ∀ k, ‖h k - g k‖ ≤ dist h g := fun k => by
      rw [← dist_eq_norm]; exact ContinuousMap.dist_apply_le_dist k
    refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hb)).trans_lt ?_
    have hp : 0 < ν.real Set.univ + 1 := by positivity
    calc dist h g * ν.real Set.univ ≤ dist h g * (ν.real Set.univ + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) dist_nonneg
      _ < ε := (lt_div_iff₀ hp).1 hh
  exact hI.comp c.continuous

variable {μ : Measure (G1 K n)} [μ.IsHaarMeasure]

private theorem reps_ext' {v w : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) (hw : Reps μ w φ) : v = w := by
  refine Lp.ext ?_
  have hm := map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K n) μ)
  refine Measure.ae_le_iff_absolutelyContinuous.2 (hm ▸ Measure.AbsolutelyContinuous.rfl :
    quotientMeasure (Gam K n) μ ≪ Measure.map (mk (Gam K n)) (μ.restrict (fundamentalDomain (Gam K n)))) ?_
  refine (ae_map_iff (measurable_mk _).aemeasurable
    ((Lp.stronglyMeasurable v).measurableSet_eq_fun (Lp.stronglyMeasurable w))).2 (ae_restrict_of_ae ?_)
  filter_upwards [hv, hw] with y h1 h2
  rw [h1, h2]

private theorem reps_sum' {ι : Type} (s : Finset ι) (c : ι → ℂ) {v : ι → L2 μ} {φ : ι → G1 K n → ℂ} (h : ∀ i ∈ s, Reps μ (v i) (φ i)) :
    Reps μ (∑ i ∈ s, c i • v i) fun y => ∑ i ∈ s, c i * φ i y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy
    simpa only [Finset.sum_empty, Pi.zero_apply] using hy
  | insert a s ha ih =>
    filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_add (c a • v a) (∑ i ∈ s, c i • v i)),
      MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_smul (c a) (v a)), h a (Finset.mem_insert_self _ _),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)] with y h1 h2 h3 h4
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, Pi.add_apply, h2, h4, Pi.smul_apply, h3, smul_eq_mul]

private theorem reps_right' {v : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) (g : G1 K n) :
    Reps μ (rightRegularRep (Gam K n) μ g v) fun y => φ (y * g) := by
  filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (coeFn_rightRegularRep (Gam K n) μ g v),
    MeasureTheory.QuasiMeasurePreserving.ae (measurePreserving_mul_right μ g).quasiMeasurePreserving hv] with y h1 h2
  rw [h1, rightMul_mk, h2]

private theorem reps_int {X : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (a : X → ℂ) (ha : Continuous a) (u : X → G1 K n) (hu : Continuous u)
    {v : LL μ} {φ : G1 K n → ℂ} (hφ : Continuous φ) (hv : Reps μ v φ) :
    Reps μ (∫ k, a k • rightRegularRep (Gam K n) μ (u k) v ∂ν) fun y => ∫ k, a k * φ (y * u k) ∂ν := by
  letI := TopologicalSpace.metrizableSpaceMetric X
  haveI : TopologicalSpace.SeparableSpace (Set.univ : Set X) := inferInstance
  let s : ℕ → SimpleFunc X X := fun i => SimpleFunc.approxOn id measurable_id Set.univ (Classical.arbitrary X) (Set.mem_univ _) i
  have hs : ∀ k, Tendsto (fun i => s i k) atTop (𝓝 k) := fun k =>
    SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ _) (by simp)
  let G : X → LL μ := fun k => a k • rightRegularRep (Gam K n) μ (u k) v
  have hG : Continuous G := ha.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp hu)
  let W : ℕ → LL μ := fun i => ∫ k, G (s i k) ∂ν
  let P : ℕ → G1 K n → ℂ := fun i y => ∫ k, a (s i k) * φ (y * u (s i k)) ∂ν
  have hW : ∀ i, Reps μ (W i) (P i) := fun i => by
    have e1 : W i = ∑ x ∈ (s i).range, ((ν.real (s i ⁻¹' {x}) : ℂ) * a x) • rightRegularRep (Gam K n) μ (u x) v := by
      show ∫ k, G (s i k) ∂ν = _
      rw [simp_int]
      refine Finset.sum_congr rfl fun x _ => ?_
      show ν.real (s i ⁻¹' {x}) • (a x • rightRegularRep (Gam K n) μ (u x) v) = _
      rw [mul_smul, Complex.coe_smul]
      rfl
    have e2 : P i = fun y => ∑ x ∈ (s i).range, ((ν.real (s i ⁻¹' {x}) : ℂ) * a x) * φ (y * u x) := by
      funext y
      refine (simp_int ν (s i) (fun x => a x * φ (y * u x))).trans (Finset.sum_congr rfl fun x _ => ?_)
      rw [Complex.real_smul, mul_assoc]
    rw [e1, e2]
    exact reps_sum' _ _ fun x _ => reps_right' hv (u x)
  have hWl : Tendsto W atTop (𝓝 (∫ k, G k ∂ν)) := simp_lim ν s hs G hG
  have hPl : ∀ y, Tendsto (fun i => P i y) atTop (𝓝 (∫ k, a k * φ (y * u k) ∂ν)) := fun y =>
    simp_lim ν s hs (fun k => a k * φ (y * u k)) (ha.mul (hφ.comp (continuous_const.mul hu)))
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hWl).exists_seq_tendsto_ae
  have h1 := MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) hns
  have h2 : ∀ᵐ y ∂μ, ∀ i, (W i : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) = P i y := ae_all_iff.2 hW
  filter_upwards [h1, h2] with y hy1 hy2
  simp only [hy2] at hy1
  exact tendsto_nhds_unique hy1 ((hPl y).comp hmono.tendsto_atTop)

private theorem cont_ae_eq {f g : G1 K n → ℂ} (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[μ] g) : f = g :=
  Continuous.ae_eq_iff_eq μ hf hg |>.1 h
end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.ptPi :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (v : LL μ) (φ : G1 K 2 → ℂ), Continuous φ → Reps μ v φ →
      (∀ i n q, C.Pi μ i n q v = 0 → ∀ x, ∫ m, conj (KT.psi n q n m) * φ (x * C.un i m) ∂μK = 0) ∧
      ∀ (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), IdemA κ p → (pOp μ κ p v = v ↔ FixA κ p φ) := by
  intro K _ _ _ ι _ C μ _ v φ hφ hv
  haveI : TopologicalSpace.MetrizableSpace U2 := inferInstance
  haveI : CompactSpace U2 := inferInstance
  have hcu : ∀ i, Continuous (C.un i) := fun i => by
    have hm : Continuous (fun x : U2 => (Pi.mulSingle i x : ι → U2)) := by
      refine continuous_pi fun j => ?_
      by_cases h : j = i
      · subst h
        simpa using continuous_id'
      · simpa [Pi.mulSingle_eq_of_ne h] using continuous_const
    unfold Co.un arc1
    exact continuous_archP.comp (continuous_subtype_val.comp ((C.Φ 2).symm.continuous.comp hm))
  have hca : Continuous (arc1 : archCompact K 2 → G1 K 2) := continuous_archP.comp continuous_subtype_val
  haveI : TopologicalSpace.MetrizableSpace (archCompact K 2) := (C.Φ 2).toHomeomorph.isEmbedding.metrizableSpace
  haveI : CompactSpace (archCompact K 2) := (C.Φ 2).toHomeomorph.symm.compactSpace
  refine ⟨fun i n q h0 x => ?_, fun κ p hp => ?_⟩
  · have hT : Continuous (T n q) := continuous_const.mul (Complex.continuous_conj.comp (KT.continuous_psi n q n))
    have hr := reps_int μK (T n q) hT (C.un i) (hcu i) hφ hv
    have hc : Continuous fun y => ∫ m, T n q m * φ (y * C.un i m) ∂μK :=
      cont_int μK _ (hT.comp continuous_snd |>.mul (hφ.comp (continuous_fst.mul ((hcu i).comp continuous_snd))))
    have h0' : (∫ m, T n q m • rightRegularRep (Gam K 2) μ (C.un i m) v ∂μK) = 0 := h0
    rw [h0'] at hr
    have hz : Reps μ (0 : LL μ) fun _ => 0 := by
      filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K 2) μ) (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K 2) μ))] with y hy
      simpa only [Pi.zero_apply] using hy
    have he : (fun y => ∫ m, T n q m * φ (y * C.un i m) ∂μK) = fun _ => 0 := by
      refine cont_ae_eq (μ := μ) hc continuous_const ?_
      filter_upwards [hr, hz] with y h1 h2
      rw [← h1, h2]
    have hx := congrFun he x
    have hN : ((KT.normSqInt n q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (KT.normSqInt_pos n q).ne'
    simp only [T, mul_assoc] at hx
    rw [integral_const_mul] at hx
    exact (mul_eq_zero.1 hx).resolve_left (inv_ne_zero hN)
  · haveI := hp.haar.prob
    have hr : Reps μ (pOp μ κ p v) fun y => ∫ k, p k * φ (y * arc1 k) ∂κ := reps_int κ p hp.cont arc1 hca hφ hv
    have hc : Continuous fun y => ∫ k, p k * φ (y * arc1 k) ∂κ :=
      cont_int κ _ (hp.cont.comp continuous_snd |>.mul (hφ.comp (continuous_fst.mul (hca.comp continuous_snd))))
    constructor
    · intro h
      rw [h] at hr
      have he : (fun y => ∫ k, p k * φ (y * arc1 k) ∂κ) = φ := by
        refine cont_ae_eq (μ := μ) hc hφ ?_
        filter_upwards [hr, hv] with y h1 h2
        rw [← h1, h2]
      exact fun g => congrFun he g
    · intro h
      have : (fun y => ∫ k, p k * φ (y * arc1 k) ∂κ) = φ := funext h
      rw [this] at hr
      exact reps_ext' hr hv
end

