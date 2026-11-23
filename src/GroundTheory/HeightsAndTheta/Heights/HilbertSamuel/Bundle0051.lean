module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNormalLocusRep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace NormalLocusRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_mul_zpow_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {d : K → ℕ} {g : MRing ι}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) ∈ chartRingZ y c := by
  rw [NmSectionsRationalProof.aeval_mul_prod_zpow y c hg, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem isFractionRing_chartRingZ (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : IsFractionRing (chartRingZ y c) Ω := by
  refine IsFractionRing.of_field (chartRingZ y c) Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  refine ⟨⟨_, aeval_mul_zpow_mem y c hg⟩, ⟨_, aeval_mul_zpow_mem y c hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charZero_of_isHorizontal (y : (Σ k, ι k) → Ω) (hH : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (n : ℤ)) = 0
    rw [mConeMap, aeval_C, MvPolynomial.algebraMap_apply]
    simp [hn]
  rw [hH, Ideal.mem_bot] at hmem
  exact_mod_cast hmem


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charZero_chartRingZ [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : CharZero (chartRingZ y c) :=
  charZero_of_inj_zero fun n hn => by
    have : ((n : chartRingZ y c) : Ω) = 0 := by rw [hn]; rfl
    exact_mod_cast this

theorem finiteType_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Algebra.FiniteType ℤ (chartRingZ y c) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

theorem exists_conductor [CharZero Ω] (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ a ∈ chartRingZ y c, a ≠ 0 ∧ ∀ t ∈ integralClosure (chartRingZ y c) Ω, a * t ∈ chartRingZ y c := by
  classical
  set A := chartRingZ y c
  have := isFractionRing_chartRingZ y hbir c hc
  have := charZero_chartRingZ y c
  have := finiteType_chartRingZ y c
  have : Module.Finite A (integralClosure A Ω) :=
    Model.finite_integralClosure_fractionRing_of_charZero A Ω
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A (integralClosure A Ω)).FG)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (S.image ((↑) : integralClosure A Ω → Ω))
  have hb0 : ((b : A) : Ω) ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext h0)
  refine ⟨((b : A) : Ω), (b : A).2, hb0, fun t ht => ?_⟩
  have htop : (⟨t, ht⟩ : integralClosure A Ω) ∈ Submodule.span A (S : Set (integralClosure A Ω)) := by
    rw [hS]; trivial
  suffices key : ∀ x ∈ Submodule.span A (S : Set (integralClosure A Ω)), ((b : A) : Ω) * (x : Ω) ∈ A from
    key _ htop
  intro x hx
  set_option synthInstance.maxHeartbeats 200000 in
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr⟩ := hb (x : Ω) (Finset.mem_image_of_mem _ hx)
    rw [show ((b : A) : Ω) * (x : Ω) = (b : A) • (x : Ω) by rw [Algebra.smul_def]; rfl, ← hr]
    exact r.2
  | zero => simp
  | add x z _ _ hx hz =>
    simp only [Subalgebra.coe_add, mul_add]
    exact add_mem hx hz
  | smul r x _ hx =>
    have : ((b : A) : Ω) * (((r : A) • x : integralClosure A Ω) : Ω) = (r : Ω) * (((b : A) : Ω) * (x : Ω)) := by
      rw [Subalgebra.coe_smul, Algebra.smul_def]
      show _ * ((r : Ω) * _) = _
      ring
    rw [this]
    exact mul_mem r.2 hx


omit [Fintype K] in
theorem isMultiHomog_prod {J : Type} (s : Finset J) (H : J → MRing ι) (N : J → K → ℕ)
    (hH : ∀ j ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (H j) (N j)) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ j ∈ s, H j) (∑ j ∈ s, N j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocalRep.isMultiHomog_C (ι := ι) 1
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact LocalRep.isMultiHomog_mul (hH j (Finset.mem_insert_self j s))
      (ih fun i hi => hH i (Finset.mem_insert_of_mem hi))

theorem notMem_mCoordIdeal (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d)
    (h0 : aeval y f ≠ 0) : f ∉ mCoordIdeal y := by
  intro hmem
  have h := (RingHom.mem_ker).mp hmem
  erw [ConeTrdeg.mConeMap_of_isMultiHomog y hf] at h
  exact mul_ne_zero (MvPolynomial.C_ne_zero.2 h0)
    (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)) h

end NormalLocusRep


open NormalLocusRep in
theorem NormalLocusRep.proof : NormalLocusRep.Statement := by
  intro K _ ι _ Ω _ y D hV hbir
  classical
  have := charZero_of_isHorizontal y hV.2.2.1

  have hchart : ∀ c : ∀ k, ι k, ∃ (N : K → ℕ) (H : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog H N ∧ aeval y H ≠ 0 ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ integralClosure (chartRingZ y c) Ω,
        (aeval y H * ∏ k, y ⟨k, c k⟩ ^ (-(N k : ℤ))) * t ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨a, ha, ha0, hcond⟩ := exists_conductor y hbir c hc
      obtain ⟨N, H, hH, he⟩ := LocalRep.exists_form_of_mem_chartRingZ y c hc ha
      have hP : ∀ N' : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ N' k) ≠ 0 := fun N' =>
        Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
      have hHa : aeval y H * ∏ k, y ⟨k, c k⟩ ^ (-(N k : ℤ)) = a := by
        rw [he, mul_assoc, ← Finset.prod_mul_distrib]
        rw [Finset.prod_eq_one fun k _ => by
          rw [← zpow_natCast, ← zpow_add₀ (hc k), add_neg_cancel, zpow_zero], mul_one]
      refine ⟨N, H, hH, ?_, fun _ t ht => ?_⟩
      · rw [he]
        exact mul_ne_zero ha0 (hP N)
      · rw [hHa]
        exact hcond t ht
    · exact ⟨0, C 1, LocalRep.isMultiHomog_C 1, by simp, fun h => absurd h hc⟩
  choose N H hH hH0 hcond using hchart
  refine ⟨∑ c, N c, ∏ c, H c, isMultiHomog_prod _ H N fun c _ => hH c,
    notMem_mCoordIdeal y (isMultiHomog_prod _ H N fun c _ => hH c)
      (by rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun c _ => hH0 c), ?_⟩
  intro a τ s hs z hz hfz

  choose c hzc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hzc k
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y (X ⟨k, c k⟩) = 0
      simp [mConeMap, h0]
    simpa using hz.2 _ hmem
  have hHz : eval z (map (Int.castRingHom ℂ) (H c)) ≠ 0 := by
    rw [map_prod, map_prod] at hfz
    exact (Finset.prod_ne_zero_iff.mp hfz) c (Finset.mem_univ c)
  have hx := hcond c hyc _ (hs c hyc)
  obtain ⟨M, G, hG, hGe⟩ := LocalRep.exists_form_of_mem_chartRingZ y c hyc hx
  refine ⟨M + (N c + fun k => ((τ : ℤ) * a k).toNat), N c + (M + fun k => (-((τ : ℤ) * a k)).toNat),
    G * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N c + fun k => ((τ : ℤ) * a k).toNat) k,
    H c * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (M + fun k => (-((τ : ℤ) * a k)).toNat) k,
    LocalRep.isMultiHomog_mul hG (LocalRep.isMultiHomog_chartMono c _),
    LocalRep.isMultiHomog_mul (hH c) (LocalRep.isMultiHomog_chartMono c _), fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  ·
    have hz' : ∀ p q : K → ℤ, (∏ k, y ⟨k, c k⟩ ^ p k) * ∏ k, y ⟨k, c k⟩ ^ q k =
        ∏ k, y ⟨k, c k⟩ ^ (p k + q k) := fun p q => by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => (zpow_add₀ (hyc k) _ _).symm
    have hnat : ∀ p : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ p k) = ∏ k, y ⟨k, c k⟩ ^ (p k : ℤ) := fun p =>
      Finset.prod_congr rfl fun k _ => (zpow_natCast _ _).symm
    have key : (∏ k, y ⟨k, c k⟩ ^ (-(N c k : ℤ))) * (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) *
        (∏ k, y ⟨k, c k⟩ ^ M k) * (∏ k, y ⟨k, c k⟩ ^ (N c k + ((τ : ℤ) * a k).toNat)) =
        ∏ k, y ⟨k, c k⟩ ^ (M k + (-((τ : ℤ) * a k)).toNat) := by
      simp only [hnat]
      rw [hz', hz', hz']
      refine Finset.prod_congr rfl fun k _ => ?_
      congr 1
      push_cast
      omega
    simp only [map_mul, map_prod, map_pow, aeval_X, Pi.add_apply]
    rw [hGe]
    linear_combination (s * aeval y (H c)) * key
  · simp only [map_mul, map_prod, map_pow, map_X, eval_X]
    exact mul_ne_zero hHz (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionSupBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

namespace ResolutionSupBound

theorem eval_smul_homog {ι : Type*} {f : MvPolynomial ι ℂ} {n : ℕ} (hf : f.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) f = c ^ n * eval z f := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : e.degree = n := by
    by_contra h
    exact (mem_support_iff.mp he) (hf.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : e.degree = ∑ i ∈ e.support, e i := rfl
  rw [← hdeg, hs]
  ring

theorem ptNorm_smul {ι : Type*} (m : ConeMetric ℂ ι) {n : ℕ} {f : MvPolynomial ι ℂ} (hf : f.IsHomogeneous n)
    {c : ℂ} (hc : c ≠ 0) (z : ι → ℂ) :
    ptNorm m (RingHom.id ℂ) n f (c • z) = ptNorm m (RingHom.id ℂ) n f z := by
  have hc' : (0 : ℝ) < ‖c‖ ^ n := pow_pos (norm_pos_iff.2 hc) n
  simp only [ptNorm, MvPolynomial.map_id, eval_smul_homog hf, m.smul, norm_mul, norm_pow, mul_pow]
  exact mul_div_mul_left _ _ hc'.ne'

theorem proof (hI : ResolutionImageSup.Statement) (hND : NonvanishingDense.Statement) :
    ResolutionSupBound.Statement := by
  intro D Ω _ _ κ _ d
  obtain ⟨C, hC⟩ := hI D Ω κ d
  refine ⟨C, fun n hn f hf z hz => ?_⟩
  set B := C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) ∧ eval w (map (Int.castRingHom ℂ) g) ≠ 0}
  have hzm : z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := by
    refine ⟨fun _ => ?_, hz.2⟩
    by_contra h
    simp only [not_exists, not_not] at h
    exact hz.1 (funext fun q => h q.2)
  have hzS : z ∈ closure S := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hzm
  have key : ∀ w ∈ S, ptNorm d.m (RingHom.id ℂ) n f w ≤ B := by
    rintro w ⟨hw, hwg⟩
    obtain ⟨y, c, hc, hyc⟩ := d.R.surj w hw fun h => hwg (h.2 g hgJ)
    have hy : resPt d y = c () • w := by
      rw [resPt, hyc]
      rfl
    rw [← ptNorm_smul d.m hf (hc ()), ← hy]
    exact hC n hn f hf y
  have hρ : ContinuousAt d.m.ρ z :=
    (d.smooth.continuousOn).continuousAt (isOpen_ne.mem_nhds hz.1)
  have hcont : ContinuousAt (ptNorm d.m (RingHom.id ℂ) n f) z := by
    unfold ptNorm
    simp only [MvPolynomial.map_id]
    exact ((MvPolynomial.continuous_eval f).norm.continuousAt).div (hρ.pow n)
      (pow_pos (d.m.pos z hz.1) n).ne'
  have := mem_closure_iff_nhdsWithin_neBot.1 hzS
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall key)

end ResolutionSupBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSHProps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi (sqSum)
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi (levi_Phi leviForm_phi_nonneg isOpen_noZeroBlock blk)

namespace ScaledFSHProps

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm : IsSmoothHerm (scaledFSH ι) :=
  (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) 1).mul
    (contDiffOn_const (c := Real.exp (-(-1 : ℝ))))

theorem log_h_eventuallyEq {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (fun y => Real.log ((scaledFSH ι).h y)) =ᶠ[𝓝 z]
      fun y => (∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) + 1 := by
  filter_upwards [isOpen_noZeroBlock.mem_nhds hz] with y hy
  have hρ : ∀ k, (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy k
    exact ((fsMetric (ι := ι k)).pos _ fun h0 => hi (congrFun h0 i)).ne'
  rw [scaledFSH_h, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hρ k) (Real.exp_pos 1).ne',
    Real.log_exp, Real.log_prod fun k _ => hρ k]

theorem leviForm_log_h_nonneg {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    0 ≤ leviForm (fun y => Real.log ((scaledFSH ι).h y)) z w := by
  have hd : fderiv ℝ (fun y => Real.log ((scaledFSH ι).h y)) =ᶠ[𝓝 z]
      fderiv ℝ (fun y => ∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) := by
    filter_upwards [(log_h_eventuallyEq hz).fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
    exact fderiv_add_const (1 : ℝ)
  have hL : leviForm (fun y => Real.log ((scaledFSH ι).h y)) z w =
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) z w := by
    unfold leviForm
    rw [hd.fderiv_eq]
  rw [hL, levi_Phi hz w]
  refine Finset.sum_nonneg fun k _ => leviForm_phi_nonneg ?_ _
  obtain ⟨i, hi⟩ := hz k
  refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2) ?_).ne'
  exact Finset.single_le_sum (f := fun j => ‖blk k z j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem isSemipositiveRel (P0 P : Ideal (MRing ι)) : IsSemipositiveRel P0 P (scaledFSH ι) :=
  ⟨isSmoothHerm, fun _ hz w _ => leviForm_log_h_nonneg hz.1 w⟩

theorem isConjInvariantH : IsConjInvariantH (scaledFSH ι) := by
  intro z
  rw [scaledFSH_h, scaledFSH_h]
  simp [fsMetric, EuclideanSpace.norm_eq]

theorem norm_le_rho (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    ‖z ⟨k, i⟩‖ ≤ (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := by
  show ‖z ⟨k, i⟩‖ ≤ ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖
  simpa using PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) i

theorem monomialsBounded (P : Ideal (MRing ι)) : MonomialsBounded P (scaledFSH ι) (fun _ => 1) := by
  intro z _ μ hμ
  rw [scaledFSH_h, norm_prod, Fintype.prod_sigma]
  have hρ : ∀ k, 0 ≤ (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := fun k => norm_nonneg _
  have hblk : ∀ k, ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := by
    intro k
    calc ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ ∏ i, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) ^ μ ⟨k, i⟩ := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_rho z k i) _
      _ = (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := by
          rw [Finset.prod_pow_eq_pow_sum, hμ k]
          exact pow_one _
  calc ∏ k, ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ ∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) :=
        Finset.prod_le_prod₀ (fun k _ => Finset.prod_nonneg fun i _ => norm_nonneg _) fun k _ => hblk k
    _ ≤ (∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩)) * Real.exp 1 :=
        le_mul_of_one_le_right (Finset.prod_nonneg fun k _ => hρ k) (Real.one_le_exp zero_le_one)

end ScaledFSHProps

theorem ScaledFSHProps.proof : ScaledFSHProps.Statement := fun _ _ _ _ P P0 =>
  ⟨ScaledFSHProps.isSemipositiveRel P0 P, ScaledFSHProps.isConjInvariantH, ScaledFSHProps.monomialsBounded P⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionRingFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem SectionRingFinite.proof (hL : SectionLatticeFinite.Statement) (hS : SectionSpanStep.Statement) :
    SectionRingFinite.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  classical
  obtain ⟨n₀, hn₀⟩ := hS K ι Ω y a q w hy hw hgen
  choose G hG using fun m : ℕ => _root_.AddSubgroup.isAddFG_iff.mp (hL K ι Ω y a m hy)
  set P : Finset (ℕ × Ω) :=
    (Finset.range (n₀ + 1)).biUnion fun m => (G m).image fun g => (m, g) with hP
  have memP : ∀ m g, m ≤ n₀ → g ∈ G m → (m, g) ∈ P := by
    intro m g hm hg
    rw [hP, Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.2 (Nat.lt_succ_of_le hm), Finset.mem_image.2 ⟨g, hg, rfl⟩⟩
  have ofP : ∀ x ∈ P, x.2 ∈ chartLat y a x.1 := by
    intro x hx
    rw [hP, Finset.mem_biUnion] at hx
    obtain ⟨m, _, hx⟩ := hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    rw [← hG m]
    exact AddSubgroup.subset_closure hg
  let f : Fin P.card → ℕ × Ω := fun i => (P.equivFin.symm i).1
  let T : ℕ → Set Ω := fun n =>
    {s | ∃ (i : Fin P.card) (μ : Fin q → ℕ), (f i).1 + ∑ j, μ j = n ∧ s = (f i).2 * ∏ j, w j ^ μ j}
  have base : ∀ n, n ≤ n₀ → chartLat y a n ≤ AddSubgroup.closure (T n) := by
    intro n hn
    rw [← hG n, AddSubgroup.closure_le]
    intro g hg
    apply AddSubgroup.subset_closure
    refine ⟨P.equivFin ⟨(n, g), memP n g hn hg⟩, 0, ?_, ?_⟩ <;> simp [f]
  have step : ∀ n (j : Fin q), ∀ s ∈ AddSubgroup.closure (T n),
      s * w j ∈ AddSubgroup.closure (T (n + 1)) := by
    intro n j s hs
    induction hs using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, μ, hdeg, rfl⟩ := hx
      apply AddSubgroup.subset_closure
      refine ⟨i, μ + Pi.single j 1, ?_, ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [← hdeg, Finset.sum_pi_single']
        simp [add_assoc]
      · have hprod : ∏ k, w k ^ ((μ + Pi.single j 1 : Fin q → ℕ) k) = (∏ k, w k ^ μ k) * w j := by
          simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
          congr 1
          rw [Fintype.prod_eq_single j]
          · simp
          · intro k hk
            simp [hk]
        rw [hprod, mul_assoc]
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
    | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  refine ⟨P.card, fun i => (f i).1, fun i => (f i).2, fun i => ofP _ (P.equivFin.symm i).2, ?_⟩
  intro n
  induction n with
  | zero => exact base 0 (Nat.zero_le _)
  | succ n ih =>
    by_cases h : n + 1 ≤ n₀
    · exact base _ h
    · have hn : n₀ ≤ n := by omega
      refine (hn₀ n hn).trans ?_
      rw [AddSubgroup.closure_le]
      rintro t ⟨s, hs, j, rfl⟩
      exact step n j s (ih hs)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormCharpoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def pullField (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ {x | ∃ i j, aeval y (L j) ≠ 0 ∧ x = aeval y (L i) / aeval y (L j)}

end Defs

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

