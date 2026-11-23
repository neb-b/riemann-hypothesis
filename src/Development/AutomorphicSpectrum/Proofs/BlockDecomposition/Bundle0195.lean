module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0148

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDomainFacts
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal

namespace GlobalTheory.CompanionTheory.DenseCpt

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

theorem val_emb (n : ℕ) : IsOpenEmbedding (Units.val : G n → Mat n) := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℂ) (α := ℂ)
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact Units.isOpenEmbedding_val

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem val_mem {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem continuous_extend {n : ℕ} {V : Type} [NormedAddCommGroup V] {b : G n → V} (hb : Continuous b)
    (hs : HasCompactSupport b) : Continuous (Function.extend (Units.val : G n → Mat n) b 0) := by
  have he := val_emb n
  refine continuous_of_tsupport fun x h => ?_
  obtain ⟨u, -, rfl⟩ := hs.tsupport_extend_zero_subset he.continuous h
  rw [← he.continuousAt_iff]
  have : Function.extend (Units.val : G n → Mat n) b 0 ∘ Units.val = b :=
    funext fun y => he.injective.extend_apply _ _ _
  rw [this]
  exact hb.continuousAt

theorem exists_smooth {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {b : G n → V}
    (hb : Continuous b) (hs : HasCompactSupport b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : Mat n → V, ContDiff ℝ ∞ f ∧ (∀ y : G n, dist (b y) (f y.val) ≤ δ) ∧
      ∀ y, y ∉ (Units.val : G n → Mat n) '' tsupport b → f y = 0 := by
  have he := val_emb n
  obtain ⟨f, hf, hd, hsu⟩ := (continuous_extend hb hs).exists_contDiff_approx ⊤ (ε := fun _ => δ)
    continuous_const fun _ => hδ
  refine ⟨f, hf, fun y => ?_, fun y hy => ?_⟩
  · have := hd y.val
    rw [show Function.extend (Units.val : G n → Mat n) b 0 y.val = b y from he.injective.extend_apply _ _ _] at this
    rw [dist_comm]; exact this.le
  · by_contra hne
    have h1 := hsu (Function.mem_support.2 hne)
    exact hy (hs.tsupport_extend_zero_subset he.continuous (subset_tsupport _ h1))

theorem cpt_of {n : ℕ} {V : Type} [Zero V] (hL : LgFacts) {K : Set (G n)} (hK : IsCompact K) {f : Mat n → V}
    (hf : ∀ y, y ∉ (Units.val : G n → Mat n) '' K → f y = 0) : Cpt f := by
  have he := val_emb n
  have hc : IsCompact ((Units.val : G n → Mat n) '' K) := hK.image he.continuous
  have hsub : (Units.val : G n → Mat n) '' K ⊆ GLs n := by
    rintro _ ⟨u, -, rfl⟩; exact val_mem u
  have hcont : ContinuousOn (lg : Mat n → ℝ) ((Units.val : G n → Mat n) '' K) :=
    ((hL n).2.2.2.1.continuousOn).mono hsub
  obtain ⟨R, hR⟩ := (hc.image_of_continuousOn hcont).bddAbove
  refine ⟨R, fun y _ hy => hf y fun hm => ?_⟩
  exact absurd (hR ⟨y, hm, rfl⟩) (not_le.2 hy)

theorem denseD : DenseD := by
  intro n _ _ μ _ V _ _ hL
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (G n) := (val_emb n).isInducing.secondCountableTopology
  haveI : LocallyCompactSpace (G n) := (val_emb n).locallyCompactSpace
  intro x
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  have hp : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨b, hbs, hbd, hbc, hbm⟩ := (Lp.memLp x).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ε := ENNReal.ofReal (ε / 2)) (by simpa using hε2)
  set K := tsupport b with hKdef
  have hKc : IsCompact K := hbs
  set m : ℝ≥0∞ := μ K ^ (1 / (2 : ℝ≥0∞).toReal) with hm
  have hmt : m ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hKc.measure_lt_top.ne
  set c : ℝ := (ε / 2) / (m.toReal + 1) with hc
  have hm0 : 0 ≤ m.toReal := ENNReal.toReal_nonneg
  have hcpos : 0 < c := by positivity
  obtain ⟨f, hf, hd, hz⟩ := exists_smooth hbc hbs hcpos
  have hcf : Continuous fun y : G n => f y.val := hf.continuous.comp Units.continuous_val
  have hsupp : Function.support (fun y : G n => f y.val) ⊆ K := by
    intro y hy
    by_contra hyK
    exact hy (hz _ fun ⟨u, hu, he⟩ => hyK (Units.ext he ▸ hu))
  have hcs : HasCompactSupport fun y : G n => f y.val :=
    HasCompactSupport.of_support_subset_isCompact hKc hsupp
  have hg : MemLp (fun y : G n => f y.val) 2 μ := hcf.memLp_of_hasCompactSupport hcs
  have hbg : eLpNorm (b - fun y : G n => f y.val) 2 μ ≤ ENNReal.ofReal (ε / 2) := by
    refine (eLpNorm_sub_le_of_dist_bdd μ hp hKc.measurableSet.nullMeasurableSet hcpos.le
      (hbm.aestronglyMeasurable.sub hg.aestronglyMeasurable) hd (subset_tsupport b) hsupp).trans ?_
    change ENNReal.ofReal c * m ≤ _
    conv_lhs => rw [← ENNReal.ofReal_toReal hmt]
    rw [← ENNReal.ofReal_mul hcpos.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨hg.toLp _, ⟨f, hf.contDiffOn, cpt_of hL hKc hz, ?_⟩, ?_⟩
  · simp only [cls]; rw [dite_eq_left hg]
  · rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
      ← ENNReal.le_ofReal_iff_toReal_le ((Lp.memLp x).sub (Lp.memLp (hg.toLp _))).eLpNorm_ne_top hε.le]
    have h1 : eLpNorm (⇑x - ⇑(hg.toLp _)) 2 μ = eLpNorm (⇑x - fun y : G n => f y.val) 2 μ :=
      eLpNorm_congr_ae (by filter_upwards [hg.coeFn_toLp] with y hy; simp [hy])
    rw [h1]
    have h2 : (⇑x - fun y : G n => f y.val) = (⇑x - b) + (b - fun y : G n => f y.val) := by
      ext y; simp
    rw [h2]
    refine (eLpNorm_add_le (p := 2) (by norm_num)).trans ?_
    calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hbd hbg
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hε2.le hε2.le]; congr 1; ring

end GlobalTheory.CompanionTheory.DenseCpt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivIntegralCompactSupport
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd.IntDeriv

variable {n : ℕ}

theorem hasDerivAt_fderiv {ρ : ℝ → Mat n → ℝ} (h : Sm ρ) (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    HasDerivAt (fun r => ρ r y) (fderiv ℝ (Function.uncurry ρ) (s, y) (1, 0)) s := by
  have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) := isOpen_univ.prod isOpen_GLs
  have hd : DifferentiableAt ℝ (Function.uncurry ρ) (s, y) :=
    ((h.contDiffAt (hopen.mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt (by simp))
  have hc : HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : Mat n)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  have hd' : HasFDerivAt (Function.uncurry ρ) (fderiv ℝ (Function.uncurry ρ) (s, y))
      ((fun r : ℝ => (r, y)) s) := hd.hasFDerivAt
  exact hd'.comp_hasDerivAt s hc

theorem hasDerivAt_dt {ρ : ℝ → Mat n → ℝ} (h : Sm ρ) (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    HasDerivAt (fun r => ρ r y) (dt ρ s y) s := by
  have h2 := hasDerivAt_fderiv h s hy
  have : dt ρ s y = fderiv ℝ (Function.uncurry ρ) (s, y) (1, 0) := h2.deriv
  rw [this]; exact h2

theorem continuousOn_dt {ρ : ℝ → Mat n → ℝ} (h : Sm ρ) :
    ContinuousOn (Function.uncurry (dt ρ)) (Set.univ ×ˢ GLs n) := by
  have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) := isOpen_univ.prod isOpen_GLs
  have hc : ContinuousOn (fderiv ℝ (Function.uncurry ρ)) (Set.univ ×ˢ GLs n) :=
    ContDiffOn.continuousOn_fderiv_of_isOpen h hopen (by simp)
  have h1 : ContinuousOn (fun p : ℝ × Mat n => fderiv ℝ (Function.uncurry ρ) p (1, 0))
      (Set.univ ×ˢ GLs n) := hc.clm_apply continuousOn_const
  refine h1.congr ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact (hasDerivAt_fderiv h s hy).deriv

theorem continuous_val_G : Continuous (fun y : G n => (y.val : Mat n)) := Units.continuous_val

theorem continuous_comp_val {W : Type} [TopologicalSpace W] {f : ℝ → Mat n → W}
    (h : ContinuousOn (Function.uncurry f) (Set.univ ×ˢ GLs n)) :
    Continuous (fun p : ℝ × G n => f p.1 p.2.val) := by
  have hm : Continuous (fun p : ℝ × G n => ((p.1, p.2.val) : ℝ × Mat n)) :=
    continuous_fst.prodMk (continuous_val_G.comp continuous_snd)
  exact h.comp_continuous hm (fun p => ⟨Set.mem_univ _, val_mem_GLs p.2⟩)

theorem hasDerivAt_integral_compact {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (ρ : ℝ → Mat n → ℝ) (hρ : Sm ρ) (K : Set (G n)) (hK : IsCompact K)
    (s₀ ε : ℝ) (hε : 0 < ε)
    (hv : ∀ s ∈ Metric.ball s₀ ε, ∀ y : G n, y ∉ K → ρ s y.val = 0) :
    HasDerivAt (fun s => ∫ y : G n, ρ s y.val ∂μ) (∫ y : G n, dt ρ s₀ y.val ∂μ) s₀ := by
  have hF : Continuous (fun p : ℝ × G n => ρ p.1 p.2.val) := continuous_comp_val hρ.continuousOn
  have hF' : Continuous (fun p : ℝ × G n => dt ρ p.1 p.2.val) :=
    continuous_comp_val (continuousOn_dt hρ)
  have hFs : ∀ s, Continuous (fun y : G n => ρ s y.val) := fun s =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hFs' : ∀ s, Continuous (fun y : G n => dt ρ s y.val) := fun s =>
    hF'.comp (continuous_const.prodMk continuous_id)
  have hKm : MeasurableSet K := hK.measurableSet
  have hv' : ∀ s ∈ Metric.ball s₀ ε, ∀ y : G n, y ∉ K → dt ρ s y.val = 0 := by
    intro s hs y hy
    have hev : (fun r => ρ r y.val) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hs] with r hr using hv r hr y hy
    have : dt ρ s y.val = deriv (fun r => ρ r y.val) s := rfl
    rw [this, hev.deriv_eq]; simp
  have hint : ∀ s ∈ Metric.ball s₀ ε, Integrable (fun y : G n => ρ s y.val) μ := by
    intro s hs
    refine (hFs s).integrable_of_hasCompactSupport (HasCompactSupport.intro hK ?_)
    exact fun y hy => hv s hs y hy
  have hint' : Integrable (fun y : G n => dt ρ s₀ y.val) μ := by
    refine (hFs' s₀).integrable_of_hasCompactSupport (HasCompactSupport.intro hK ?_)
    exact fun y hy => hv' s₀ (Metric.mem_ball_self hε) y hy
  have hs₀ : s₀ ∈ Metric.ball s₀ ε := Metric.mem_ball_self hε
  obtain ⟨M, hM⟩ := ((isCompact_closedBall s₀ (ε / 2)).prod hK).exists_bound_of_continuousOn
    hF'.continuousOn
  have hball : Metric.ball s₀ (ε / 2) ⊆ Metric.ball s₀ ε := Metric.ball_subset_ball (by linarith)
  have hbound : ∀ᵐ y ∂μ, ∀ s ∈ Metric.ball s₀ (ε / 2),
      ‖dt ρ s (y : G n).val‖ ≤ K.indicator (fun _ => M) y := by
    refine Filter.Eventually.of_forall fun y s hs => ?_
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      exact hM (s, y) ⟨Metric.ball_subset_closedBall hs, hy⟩
    · rw [Set.indicator_of_notMem hy, hv' s (hball hs) y hy]; simp
  have hbi : Integrable (K.indicator (fun _ : G n => M)) μ :=
    (integrable_indicator_iff hKm).2 (integrableOn_const hK.measure_lt_top.ne)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun s (y : G n) => ρ s y.val) (F' := fun s (y : G n) => dt ρ s y.val)
    (x₀ := s₀) (s := Metric.ball s₀ (ε / 2)) (bound := K.indicator (fun _ => M))
    (Metric.ball_mem_nhds s₀ (by linarith))
    (Filter.Eventually.of_forall fun s => (hFs s).aestronglyMeasurable)
    (hint s₀ hs₀) hint'.aestronglyMeasurable hbound hbi
    (Filter.Eventually.of_forall fun y s _ => hasDerivAt_dt hρ s (val_mem_GLs y))
  exact this.2

end GlobalTheory.CompanionTheory.WaveSpd.IntDeriv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeAsRightWords
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.Expand

variable {n : ℕ}

def co (q : Idx n) (M : Mat n) : ℝ := if q.1 then (M q.2.1 q.2.2).re else (M q.2.1 q.2.2).im

theorem sum_single_ite (a b : Fin n) (g : Fin n → Fin n → ℂ) :
    ∑ x, ∑ i, (if x = a ∧ i = b then g x i else 0) = g a b := by
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp),
    Finset.sum_eq_single b (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem sum_co_smul (M : Mat n) : ∑ q : Idx n, co q M • bs q = M := by
  ext a b
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, co, bs, Matrix.sum_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.single_apply, if_true, Bool.false_eq_true, if_false, smul_ite,
    smul_zero]
  rw [sum_single_ite a b (fun x i => (M x i).re • (1 : ℂ)),
    sum_single_ite a b (fun x i => (M x i).im • Complex.I)]
  simp [Complex.ext_iff]

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y i j) :=
  contDiff_apply_apply ℝ i j

theorem contDiff_det (F : Mat n → Mat n) (h : ∀ i j, ContDiff ℝ ∞ (fun y => F y i j)) :
    ContDiff ℝ ∞ (fun y => (F y).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_adjugate (i k : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y.adjugate i k) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det (fun y => y.updateRow k (Pi.single i 1)) fun a b => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry a b

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne.preimage (contDiff_det (n := n) id contDiff_entry).continuous

theorem contDiffOn_inv_entry (i k : Fin n) :
    ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹ i k) (GLs n) := by
  have h : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹ * y.adjugate i k) (GLs n) :=
    ((contDiff_det (n := n) id contDiff_entry).contDiffOn.inv fun y hy => hy).mul
      (contDiff_adjugate i k).contDiffOn
  refine h.congr fun y _ => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]

theorem co_smooth (p q : Idx n) :
    ContDiffOn ℝ ∞ (fun y : Mat n => co q (y⁻¹ * bs p)) (GLs n) := by
  have he : ∀ a b, ContDiffOn ℝ ∞ (fun y : Mat n => (y⁻¹ * bs p) a b) (GLs n) := by
    intro a b
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun k _ => (contDiffOn_inv_entry a k).mul contDiffOn_const
  rcases q with ⟨_ | _, a, b⟩
  · simpa [co, Function.comp_def] using Complex.imCLM.contDiff.comp_contDiffOn (he a b)
  · simpa [co, Function.comp_def] using Complex.reCLM.contDiff.comp_contDiffOn (he a b)

theorem contDiff_mul_right (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (contDiff_entry a k).mul contDiff_const

theorem Rw_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Idx n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    exact (ih.fderiv_of_isOpen isOpen_GLs (by simp)).clm_apply
      (contDiff_mul_right (bs p)).contDiffOn

theorem fderiv_mul_expand {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Mat n → V)
    (y M : Mat n) : fderiv ℝ H y (y * M) = ∑ q, co q M • Rd (bs q) H y := by
  conv_lhs => rw [← sum_co_smul M]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.mul_smul, map_smul]
  rfl

theorem fderiv_expand {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Mat n → V)
    {y : Mat n} (hy : y ∈ GLs n) (X : Mat n) :
    fderiv ℝ H y X = ∑ q, co q (y⁻¹ * X) • Rd (bs q) H y := by
  have hu : IsUnit y.det := isUnit_iff_ne_zero.2 hy
  rw [← fderiv_mul_expand, Matrix.mul_nonsing_inv_cancel_left y X hu]

theorem exists_integralCombination_of_mem_completedLattice (L : List (Idx n)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → Mat n → ℝ) (w : ι → List (Idx n)),
      (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
        ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  induction L with
  | nil =>
    exact ⟨Unit, inferInstance, fun _ _ => 1, fun _ => [], fun _ => contDiffOn_const,
      fun V _ _ f _ y _ => by simp [Dw_nil, Rw]⟩
  | cons p L ih =>
    obtain ⟨ι, _, c, w, hc, h⟩ := ih
    refine ⟨ι ⊕ (ι × Idx n), inferInstance,
      Sum.elim (fun i y => fderiv ℝ (c i) y (bs p)) (fun e y => c e.1 y * co e.2 (y⁻¹ * bs p)),
      Sum.elim w (fun e => e.2 :: w e.1), ?_, ?_⟩
    · rintro (i | ⟨i, q⟩)
      · exact ((hc i).fderiv_of_isOpen isOpen_GLs (by simp)).clm_apply contDiffOn_const
      · exact (hc i).mul (co_smooth p q)
    · intro V _ _ f hf y hy
      have hev : Dw L f =ᶠ[nhds y] fun z => ∑ i, c i z • Rw (w i) f z := by
        filter_upwards [isOpen_GLs.mem_nhds hy] with z hz using h V f hf z hz
      have hdc : ∀ i, DifferentiableAt ℝ (c i) y := fun i =>
        ((hc i).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
      have hdr : ∀ i, DifferentiableAt ℝ (Rw (w i) f) y := fun i =>
        ((Rw_smooth hf (w i)).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
      show fderiv ℝ (Dw L f) y (bs p) = _
      have hd : HasFDerivAt (fun z => ∑ i, c i z • Rw (w i) f z)
          (∑ i, (c i y • fderiv ℝ (Rw (w i) f) y +
            (fderiv ℝ (c i) y).smulRight (Rw (w i) f y))) y :=
        HasFDerivAt.fun_sum fun i _ => (hdc i).hasFDerivAt.fun_smul (hdr i).hasFDerivAt
      rw [hev.fderiv_eq, hd.fderiv]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [add_comm]
      congr 1
      rw [fderiv_expand _ hy, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [mul_smul]
      rfl

theorem Dw_eq_comb : ∀ (n : ℕ) (L : List (Idx n)), ∃ (m : ℕ) (c : Fin m → Mat n → ℝ) (w : Fin m → List (Idx n)),
    (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
      ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  intro n L
  obtain ⟨ι, _, c, w, hc, h⟩ := exists_integralCombination_of_mem_completedLattice L
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => c (e.symm i), fun i => w (e.symm i), fun i => hc _, ?_⟩
  intro V _ _ f hf y hy
  rw [h V f hf y hy]
  exact (Equiv.sum_comp e.symm fun i => c i y • Rw (w i) f y).symm

end GlobalTheory.CompanionTheory.SobGL.Expand
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityPointwiseEstimate
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem pointwise_energy_ineq : ∀ {W ι : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι] (w v : W) (Y : ι → W) (L : ι → ℝ) (A : W →L[ℝ] W) (C₁ C c φ : ℝ), 0 ≤ C₁ → C₁ * (1 + Fintype.card ι) ≤ C → c ≤ 0 → 0 ≤ φ → (∀ p, |L p| ≤ C₁) → c * C * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2) + φ * (2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ) - (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ ≤ (‖A‖ + 1) * (φ * (‖w‖ ^ 2 + (1 / 4) * ∑ p, ‖Y p‖ ^ 2 + ‖v‖ ^ 2)) := by
  intro W ι _ _ _ w v Y L A C₁ C c φ hC₁ hC hc hφ hL
  have hS0 : 0 ≤ ∑ p, ‖Y p‖ ^ 2 := Finset.sum_nonneg fun p _ => by positivity
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ p, ‖Y p‖ ^ 2 := ⟨_, rfl⟩
  rw [← hS] at hS0 ⊢
  obtain ⟨D, hD⟩ : ∃ D, D = ‖w‖ ^ 2 + (1 / 4) * S + ‖v‖ ^ 2 := ⟨_, rfl⟩
  rw [← hD]
  have hw2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hv2 : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hwD : ‖w‖ ^ 2 ≤ D := by rw [hD]; linarith
  have hSD : (1 / 4) * S ≤ D := by rw [hD]; linarith

  have hterm : ∀ p, -(c * L p * ⟪Y p, w⟫_ℝ) ≤ (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by
    intro p
    have hin : |⟪Y p, w⟫_ℝ| ≤ ‖Y p‖ * ‖w‖ := abs_real_inner_le_norm _ _
    have hmul : |L p * ⟪Y p, w⟫_ℝ| ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by
      rw [abs_mul]
      have h2 : ‖Y p‖ * ‖w‖ ≤ (1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2) := by
        nlinarith [sq_nonneg (‖Y p‖ - ‖w‖)]
      exact mul_le_mul (hL p) (hin.trans h2) (abs_nonneg _) hC₁
    have hle : L p * ⟪Y p, w⟫_ℝ ≤ C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) :=
      (le_abs_self _).trans hmul
    have := mul_le_mul_of_nonneg_left hle (neg_nonneg.2 hc)
    calc -(c * L p * ⟪Y p, w⟫_ℝ) = (-c) * (L p * ⟪Y p, w⟫_ℝ) := by ring
      _ ≤ (-c) * (C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))) := this
      _ = (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) := by ring
  have hsum : -(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ
      ≤ (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2) := by
    have h1 : ∑ p, -(c * L p * ⟪Y p, w⟫_ℝ)
        ≤ ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2)) :=
      Finset.sum_le_sum fun p _ => hterm p
    have h2 : ∑ p, (-c) * C₁ * ((1 / 2) * (‖Y p‖ ^ 2 + ‖w‖ ^ 2))
        = (-c) * C₁ * ((1 / 2) * (S + (Fintype.card ι : ℝ) * ‖w‖ ^ 2)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← hS]
      simp [Finset.card_univ]
    rw [Finset.sum_neg_distrib, h2] at h1
    linarith
  have hN0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hbr : (1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2
      ≤ (1 + (Fintype.card ι : ℝ)) * D := by
    nlinarith [mul_le_mul_of_nonneg_left hwD hN0, mul_nonneg hN0 hw2]
  have hcC : (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2)
      ≤ (-c) * C * D := by
    have hnc : 0 ≤ -c := neg_nonneg.2 hc
    calc (-c) * C₁ * ((1 / 4) * S + (1 / 4) * (Fintype.card ι : ℝ) * ‖w‖ ^ 2)
        ≤ (-c) * C₁ * ((1 + (Fintype.card ι : ℝ)) * D) :=
          mul_le_mul_of_nonneg_left hbr (mul_nonneg hnc hC₁)
      _ = (-c) * (C₁ * (1 + (Fintype.card ι : ℝ))) * D := by ring
      _ ≤ (-c) * C * D :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hnc) hD0

  have hAv : ⟪A v, w⟫_ℝ ≤ ‖A‖ * ‖v‖ * ‖w‖ :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg _))
  have hwv : ⟪w, v⟫_ℝ ≤ ‖w‖ * ‖v‖ := real_inner_le_norm _ _
  have hvw : 2 * (‖v‖ * ‖w‖) ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖v‖ - ‖w‖)]
  have hvwD : 2 * (‖v‖ * ‖w‖) ≤ D := by rw [hD] at *; linarith
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hbrack : 2 * ⟪A v, w⟫_ℝ + 2 * ⟪w, v⟫_ℝ ≤ (‖A‖ + 1) * D := by
    have h3 : ‖A‖ * (2 * (‖v‖ * ‖w‖)) ≤ ‖A‖ * D := mul_le_mul_of_nonneg_left hvwD hA0
    nlinarith
  have hφ' := mul_le_mul_of_nonneg_left hbrack hφ
  have hrew : (1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ
      = -(-(1 / 2) * ∑ p, c * L p * ⟪Y p, w⟫_ℝ) := by ring
  rw [hrew]
  nlinarith

end GlobalTheory.CompanionTheory.WaveSpd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentity
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem gser_mul_prod : ∀ (n : ℕ) (c : Fin n → ℂ),
    (1 - PowerSeries.X * gser c) * ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) := by
  intro n c
  have h := GlobalTheory.Dec.GelfSepProof.gen (fun a => c a + ((n : ℂ) - 1) / 2)
  have e : gser c = PowerSeries.mk (fun k => ∑ a, ∑ b,
      (Formalism.REAL.Amat (fun a => c a + ((n : ℂ) - 1) / 2) ^ k) a b) := rfl
  rw [e]
  simpa only [map_add (f := _), map_one] using h

end GlobalTheory.CompanionTheory.WaveMult
end
end

