module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoRescaledIntegralOfDensityOne
section
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.VagueRescale

theorem integral_le_of_small_balls {d : ℕ} (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] (κ : ℝ) (hκ : 0 ≤ κ)
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (h : ∀ x ∈ U, ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : ∀ x, 0 ≤ f x) (hU : ∀ x ∉ U, f x = 0) :
    ∫ x, f x ∂μ ≤ κ * ∫ x, f x ∂ν := by
  have hcν : ∀ A, (κ.toNNReal • ν) A = ENNReal.ofReal κ * ν A := fun A => by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]; rfl

  have hsub : ∀ s ⊆ U, μ s ≤ (κ.toNNReal • ν) s := by
    intro s hs
    refine (Besicovitch.vitaliFamily μ).measure_le_of_frequently_le (κ.toNNReal • ν)
      (Measure.AbsolutelyContinuous.refl μ) s fun x hx => ?_
    have hfr := (Besicovitch.tendsto_filterAt μ x).frequently
      (p := fun a => μ a ≤ ENNReal.ofReal κ * ν a) (h x (hs hx)).frequently
    exact hfr.mono fun a ha => ha.trans_eq (hcν a).symm
  have hle : μ.restrict U ≤ κ.toNNReal • ν.restrict U := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, ← Measure.smul_apply]
    exact hsub _ Set.inter_subset_right
  calc ∫ x, f x ∂μ = ∫ x, f x ∂(μ.restrict U) := (setIntegral_eq_integral_of_forall_compl_eq_zero hU).symm
    _ ≤ ∫ x, f x ∂(κ.toNNReal • ν.restrict U) :=
        integral_mono_measure hle (Filter.Eventually.of_forall h0) (hf.integrable_of_hasCompactSupport hc)
    _ = κ * ∫ x, f x ∂ν := by
        rw [integral_smul_nnreal_measure, setIntegral_eq_integral_of_forall_compl_eq_zero hU,
          NNReal.smul_def, Real.coe_toNNReal _ hκ, smul_eq_mul]

private theorem rescaled_integral_comparable_of_nonneg_compactSupport {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ν] (κ δ : ℝ) (hκ : 1 < κ)
    (hball : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ →
      ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ν (Metric.closedBall x r) ≤ ENNReal.ofReal κ * volume (Metric.closedBall x r) ∧
        volume (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (h0 : ∀ x, 0 ≤ φ x) (R r : ℝ) (hR : ∀ x : EuclideanSpace ℝ (Fin d), R ≤ ‖x‖ → φ x = 0)
    (hr : 0 < r) (hrR : r * R < δ) :
    (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν ≤ κ * ∫ x, φ x ∧
      ∫ x, φ x ≤ κ * ((r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin d) => r⁻¹ • x) :=
    (continuous_const_smul _).measurable
  have hJ : ∫ x, φ x ∂(ν.map (fun x => r⁻¹ • x)) = ∫ x, φ (r⁻¹ • x) ∂ν :=
    integral_map hmeas.aemeasurable hφ.aestronglyMeasurable
  have hrd : 0 < r ^ d := pow_pos hr d

  have hpre : ∀ (y : EuclideanSpace ℝ (Fin d)) (s : ℝ), 0 ≤ s →
      (ν.map (fun x => r⁻¹ • x)) (Metric.closedBall y s) = ν (Metric.closedBall (r • y) (r * s)) := by
    intro y s hs
    rw [Measure.map_apply hmeas Metric.isClosed_closedBall.measurableSet, Set.preimage_smul_inv₀ hr.ne',
      smul_closedBall _ _ hs, Real.norm_of_nonneg hr.le]
  have hvol : ∀ (y : EuclideanSpace ℝ (Fin d)) (s : ℝ), 0 ≤ s →
      volume (Metric.closedBall (r • y) (r * s)) =
        ENNReal.ofReal (r ^ d) * volume (Metric.closedBall y s) := by
    intro y s hs
    rw [Measure.addHaar_closedBall' _ _ (mul_nonneg hr.le hs), Measure.addHaar_closedBall' _ _ hs,
      finrank_euclideanSpace_fin, mul_pow, ENNReal.ofReal_mul (pow_nonneg hr.le _), mul_assoc]
  have hcv : ∀ A, ((r ^ d).toNNReal • volume : Measure (EuclideanSpace ℝ (Fin d))) A =
      ENNReal.ofReal (r ^ d) * volume A := fun A => by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]; rfl
  have hscale : Filter.Tendsto (fun s : ℝ => r * s) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_const_mul r).tendsto (0 : ℝ))
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hr hs
  set U : Set (EuclideanSpace ℝ (Fin d)) := {y | r * ‖y‖ < δ} with hU
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin d), ‖r • y‖ = r * ‖y‖ := fun y => by
    rw [norm_smul, Real.norm_of_nonneg hr.le]
  have hvan : ∀ y ∉ U, φ y = 0 := by
    intro y hy
    simp only [hU, Set.mem_setOf_eq, not_lt] at hy
    refine hR y ?_
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_lt_mul_of_pos_left hlt hr]
  have hnear : ∀ y ∈ U, ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (ν (Metric.closedBall (r • y) (r * s)) ≤
          ENNReal.ofReal κ * volume (Metric.closedBall (r • y) (r * s)) ∧
        volume (Metric.closedBall (r • y) (r * s)) ≤
          ENNReal.ofReal κ * ν (Metric.closedBall (r • y) (r * s))) ∧ 0 < s := by
    intro y hy
    have hy' : ‖r • y‖ < δ := by rw [hnorm]; exact hy
    filter_upwards [hscale.eventually (hball _ hy'), self_mem_nhdsWithin] with s hs hs0
    exact ⟨hs, hs0⟩
  have A1 := integral_le_of_small_balls (ν.map (fun x => r⁻¹ • x)) ((r ^ d).toNNReal • volume) κ
    (by linarith) U (fun y hy => (hnear y hy).mono fun s hs => by
      rw [hpre y s hs.2.le, hcv, ← hvol y s hs.2.le]; exact hs.1.1) φ hφ hc h0 hvan
  have A2 := integral_le_of_small_balls ((r ^ d).toNNReal • volume) (ν.map (fun x => r⁻¹ • x)) κ
    (by linarith) U (fun y hy => (hnear y hy).mono fun s hs => by
      rw [hpre y s hs.2.le, hcv, ← hvol y s hs.2.le]; exact hs.1.2) φ hφ hc h0 hvan
  have hvolint : ∫ x, φ x ∂((r ^ d).toNNReal • volume) = r ^ d * ∫ x, φ x := by
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Real.coe_toNNReal _ hrd.le, smul_eq_mul]
  rw [hJ, hvolint] at A1 A2
  constructor
  · rw [inv_mul_le_iff₀ hrd]
    linarith
  · rw [show κ * ((r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) = (κ * ∫ x, φ (r⁻¹ • x) ∂ν) / r ^ d by
      field_simp, le_div_iff₀ hrd]
    linarith

theorem tendsto_of_nonneg {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    (h : ∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ →
      ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ν (Metric.closedBall x r) ≤ ENNReal.ofReal κ * volume (Metric.closedBall x r) ∧
        volume (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (h0 : ∀ x, 0 ≤ φ x) :
    Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, φ x)) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x : EuclideanSpace ℝ (Fin d), R ≤ ‖x‖ → φ x = 0 := by
    obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall 0
    refine ⟨R₀ + 1, fun x hx => ?_⟩
    by_contra hne
    have hx' := hR₀ (subset_tsupport φ (Function.mem_support.2 hne))
    rw [Metric.mem_closedBall, dist_zero_right] at hx'
    linarith
  have hL0 : 0 ≤ ∫ x, φ x := integral_nonneg h0
  have key : ∀ κ : ℝ, 1 < κ → ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν ≤ κ * ∫ x, φ x ∧
        ∫ x, φ x ≤ κ * ((r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) := by
    intro κ hκ
    obtain ⟨δ, hδ, hball⟩ := h κ hκ
    have hlin : Filter.Tendsto (fun r : ℝ => r * R) (nhds 0) (nhds 0) := by
      have := ((continuous_mul_const R).tendsto (0 : ℝ))
      rwa [zero_mul] at this
    filter_upwards [(hlin.mono_left nhdsWithin_le_nhds).eventually (eventually_lt_nhds hδ),
      self_mem_nhdsWithin] with r hrR hr
    exact rescaled_integral_comparable_of_nonneg_compactSupport ν κ δ hκ hball φ hφ hc h0 R r hR hr hrR
  rw [Metric.tendsto_nhds]
  intro ε hε
  set L := ∫ x, φ x with hLdef
  set η : ℝ := min 1 (ε / (2 * (L + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η * (2 * (L + 1)) ≤ ε := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  filter_upwards [key (1 + η) (by linarith)] with r hr
  obtain ⟨hu, hl⟩ := hr
  set I := (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν
  have h6 : 0 ≤ η * L := mul_nonneg hη.le hL0
  have h3 : η * I ≤ η * ((1 + η) * L) := mul_le_mul_of_nonneg_left hu hη.le
  have h4 : η * (η * L) ≤ 1 * (η * L) := mul_le_mul_of_nonneg_right hη1 h6
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

end GlobalTheory.VagueRescale

namespace GlobalTheory

theorem tendsto_rescaled_integral_of_density_one :
    ∀ (d : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ν →
    (∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ →
      ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ν (Metric.closedBall x r) ≤ ENNReal.ofReal κ * volume (Metric.closedBall x r) ∧
        volume (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r)) →
    ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, Continuous φ → HasCompactSupport φ →
    Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, φ x)) := by
  intro d ν hν h φ hφ hc
  have hsplit : ∀ t : ℝ, max t 0 - max (-t) 0 = t := by
    intro t
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, max_eq_right (by linarith)]; ring
    · rw [max_eq_right ht, max_eq_left (by linarith)]; ring
  have hp : Continuous (fun x => max (φ x) 0) := hφ.max continuous_const
  have hm : Continuous (fun x => max (-φ x) 0) := hφ.neg.max continuous_const
  have hpc : HasCompactSupport (fun x => max (φ x) 0) :=
    hc.comp_left (g := fun t : ℝ => max t 0) (by simp)
  have hmc : HasCompactSupport (fun x => max (-φ x) 0) :=
    hc.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)
  have Tp := VagueRescale.tendsto_of_nonneg ν h _ hp hpc (fun x => le_max_right _ _)
  have Tm := VagueRescale.tendsto_of_nonneg ν h _ hm hmc (fun x => le_max_right _ _)
  have hint : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, Continuous g → HasCompactSupport g →
      ∀ r : ℝ, Integrable (fun x => g (r⁻¹ • x)) ν := by
    intro g hg hgc r
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
    exact Integrable.of_bound (hg.comp (continuous_const_smul _)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => hC _)
  have heq : (fun r : ℝ => (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) = fun r =>
      (r ^ d)⁻¹ * ∫ x, max (φ (r⁻¹ • x)) 0 ∂ν - (r ^ d)⁻¹ * ∫ x, max (-φ (r⁻¹ • x)) 0 ∂ν := by
    funext r
    rw [← mul_sub, ← integral_sub (hint _ hp hpc r) (hint _ hm hmc r)]
    simp only [hsplit]
  have hvol : ∫ x, φ x = (∫ x, max (φ x) 0) - ∫ x, max (-φ x) 0 := by
    rw [← integral_sub (hp.integrable_of_hasCompactSupport hpc) (hm.integrable_of_hasCompactSupport hmc)]
    simp only [hsplit]
  rw [heq, hvol]
  exact Tp.sub Tm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaSmulCompletedLatticeIffTypePrimeMul
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.ThetaG

open IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem mem_lat_span_smul_iff (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin n → E)) (a : 𝓞 E) (x : Fin n → (A.loc p).Ep) :
    x ∈ A.lat p (Ideal.span {a} • Λ) ↔ ∃ z ∈ A.lat p Λ, x = (A.loc p).ιE (a : E) • z := by
  let φ : (Fin n → (A.loc p).Ep) →ₗ[(A.L p).O] (Fin n → (A.loc p).Ep) :=
    (LinearMap.lsmul (A.loc p).Ep (Fin n → (A.loc p).Ep) ((A.loc p).ιE (a : E))).restrictScalars (A.L p).O
  have hφ : ∀ v, φ v = (A.loc p).ιE (a : E) • v := fun v => rfl
  have hbc : ∀ v : Fin n → E, A.bc p (a • v) = φ (A.bc p v) := by
    intro v
    funext i
    show (A.loc p).ιE ((a : E) * v i) = (A.loc p).ιE (a : E) * (A.loc p).ιE (v i)
    exact map_mul _ _ _
  have hset : A.bc p '' ((Ideal.span {a} • Λ : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
      φ '' (A.bc p '' (Λ : Set (Fin n → E))) := by
    rw [Submodule.ideal_span_singleton_smul, Submodule.coe_pointwise_smul, ← Set.image_smul,
      Set.image_image, Set.image_image]
    exact Set.image_congr fun v _ => hbc v
  have heq : A.lat p (Ideal.span {a} • Λ) = (A.lat p Λ).map φ := by
    unfold Places.lat
    rw [hset, Submodule.map_span]
  rw [heq, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem smul_mem_iff_of_unit {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (O : Subring R)
    (N : Submodule O M) (θ s w b : R) (hw : w ∈ O) (hb : b ∈ O) (hs : s = θ * b) (hwb : w * b = 1) (x : M) :
    (∃ y ∈ N, x = θ • y) ↔ ∃ z ∈ N, x = s • z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(⟨w, hw⟩ : O) • y, N.smul_mem _ hy, ?_⟩
    rw [Subring.smul_def, smul_smul, hs, mul_assoc, mul_comm b w, hwb, mul_one]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(⟨b, hb⟩ : O) • z, N.smul_mem _ hz, ?_⟩
    rw [Subring.smul_def, smul_smul, hs]

theorem resChar_eq_of_mem (p : HeightOneSpectrum (𝓞 F)) {q : ℕ} (hq : q.Prime)
    (h : ((q : ℕ) : 𝓞 F) ∈ p.asIdeal) : Formalism.MainNotions.S.Loc.resChar p = q := by
  unfold Formalism.MainNotions.S.Loc.resChar
  haveI := p.isPrime
  have h0 : ((q : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h
  rcases hq.eq_one_or_self_of_dvd _ (ringChar.dvd h0) with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

end GlobalTheory.HL.ThetaG

namespace GlobalTheory.HL.ThetaG

open IsDedekindDomain ValuativeRel

theorem inTh_lat_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ (Λ : G.Lt) (x : (G.S (below D P)).V), (G.S (below D P)).InTh ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) Λ) x ↔ x ∈ (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  intro D X Y T T' F00 F'0 FP G c P hP Λ x
  haveI := P.isPrime
  have hmem : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      Formalism.MainNotions.S.Loc.resChar (below D P) = D.host.g i := by
    intro i hi
    apply resChar_eq_of_mem (below D P) (D.host.g_prime i)
    change _ ∈ Ideal.comap _ P.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hi
  have hg : ((gS D : ℕ) : 𝓞 D.host.E) =
      ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    unfold Formalism.MainNotions.S.Lat.gS
    push_cast
    ring
  obtain ⟨i, j, hij, hi, hgij⟩ : ∃ i j : Fin 2, D.host.g i ≠ D.host.g j ∧
      ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧
      ((gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g i : ℕ) : 𝓞 D.host.E) * ((D.host.g j : ℕ) : 𝓞 D.host.E) := by
    rw [hg] at hP
    rcases P.isPrime.mem_or_mem hP with h | h
    · exact ⟨0, 1, D.host.g_ne, h, hg⟩
    · exact ⟨1, 0, D.host.g_ne.symm, h, by rw [hg, mul_comm]⟩
  have hres := hmem i hi
  have hj : ((D.host.g j : ℕ) : 𝓞 D.host.F) ∉ (below D P).asIdeal := by
    intro hj'
    exact hij (hres.symm.trans (resChar_eq_of_mem (below D P) (D.host.g_prime j) hj'))
  have hsome : ((D.s.atP (below D P)).split).isSome = true :=
    (D.s_split (below D P)).2 (by rw [hres]; fin_cases i <;> simp)
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.1 hsome
  have hA := (Y.agree (below D P)).2.2.2.2.2
  rw [hsg] at hA
  obtain ⟨g', hM, hq⟩ : ∃ g', (Y.M (below D P)).split = some g' ∧ g'.q = sg.q := by
    cases hM : (Y.M (below D P)).split with
    | none => rw [hM] at hA; exact hA.elim
    | some g' => rw [hM] at hA; exact ⟨g', rfl, hA.2⟩
  have hgg := (c.c (below D P)).gg_some g' hM
  have hth : (G.S (below D P)).th = ((D.host.g i : ℕ) : (D.s.atP (below D P)).Fp) := by
    unfold Frames.th
    rw [if_pos hgg.1, hgg.2, hq, sg.q_eq, hres]
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).char0
  have hgj0 : ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have hval : (below D P).valuation D.host.F ((D.host.g j : ℕ) : D.host.F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F)]
    exact le_antisymm ((below D P).valuation_le_one _)
      (not_lt.1 fun hlt => hj (((below D P).valuation_lt_one_iff_mem (K := D.host.F) _).1 hlt))
  have hint : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιF ((D.host.g j : ℕ) : D.host.F)⁻¹ ∈ 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp] :=
    (GlobalTheory.HL.PlacesInt.mem_int_iff ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)) _).2 (by rw [map_inv₀, hval, inv_one])
  have hιF : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιF ((D.host.g j : ℕ) : D.host.F)⁻¹ =
      ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp)⁻¹ := by
    rw [map_inv₀, map_natCast]
  let w : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep :=
    algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp)⁻¹
  have hwO : w ∈ ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O := by
    rw [hιF] at hint
    refine (((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O_def _).2 ?_
    have : IsIntegral 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp]
        (algebraMap 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp] ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep ⟨_, hint⟩) :=
      isIntegral_algebraMap
    exact this
  have hw : w * ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = 1 := by
    simp only [w]
    rw [← map_natCast (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep), ← map_mul,
      inv_mul_cancel₀ hgj0, map_one]
  have huO : ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) ∈
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O :=
    natCast_mem _ _
  have hι : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (((((D.host.g i : ℕ) : 𝓞 D.host.E) * ((D.host.g j : ℕ) : 𝓞 D.host.E) :
      𝓞 D.host.E)) : D.host.E) =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) * ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    push_cast
    rw [map_mul, map_natCast, map_natCast]
  have hθE : algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep (G.S (below D P)).th =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    rw [hth]
    exact map_natCast _ _
  have hιS : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE ((((gS D : ℕ) : 𝓞 D.host.E)) : D.host.E) =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) *
        ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    rw [hgij]
    exact hι
  obtain ⟨a, ha⟩ : ∃ a : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep, ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep, ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = b := ⟨_, rfl⟩
  rw [ha, hb] at hιS
  rw [ha] at hθE
  rw [hb] at hw huO
  clear_value w
  have hs : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE ((((gS D : ℕ) : 𝓞 D.host.E)) : D.host.E) =
      algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep (G.S (below D P)).th * b := by
    rw [hιS, hθE]
  unfold Frames.InTh
  rw [mem_lat_span_smul_iff]
  exact smul_mem_iff_of_unit _ _ _ _ w b hwO huO hs hw x

end GlobalTheory.HL.ThetaG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySubgroupChartSurjectiveNearOrigin
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Filter Topology Metric

noncomputable section

namespace GlobalTheory.GaugeSubChartSurj

theorem exists_ball_subset {V M : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] (ι : V →L[ℝ] M) (p : M →L[ℝ] V)
    (hp : ∀ x, p (ι x) = x) {f : M → M} (hf : HasStrictFDerivAt f (ContinuousLinearMap.id ℝ M) 0)
    (h0 : f 0 = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : V, ‖x‖ < ρ → ∃ y : V, ‖f (ι y)‖ < δ ∧ p (f (ι y)) = x := by
  have hf' : HasStrictFDerivAt f (ContinuousLinearMap.id ℝ M) (ι 0) := by rwa [map_zero]
  have h1 := hf'.comp (0 : V) ι.hasStrictFDerivAt
  have h2 := p.hasStrictFDerivAt.comp (0 : V) h1
  have h3 : p.comp ((ContinuousLinearMap.id ℝ M).comp ι) =
      (ContinuousLinearEquiv.refl ℝ V : V →L[ℝ] V) := by
    ext1 x; exact hp x
  rw [h3] at h2
  have h4 := h2.map_nhds_eq_of_equiv
  simp only [map_zero, h0] at h4
  have h5 : Tendsto (fun y => f (ι y)) (𝓝 0) (𝓝 0) := by
    have := h1.continuousAt.tendsto
    simpa only [map_zero, h0] using this
  have h6 : (fun y => f (ι y)) ⁻¹' ball 0 δ ∈ 𝓝 (0 : V) := h5 (ball_mem_nhds 0 hδ)
  have h7 := image_mem_map (m := fun y => p (f (ι y))) h6
  rw [h4] at h7
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.1 h7
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hsub (mem_ball_zero_iff.2 hx)
  exact ⟨y, mem_ball_zero_iff.1 hy, hyx⟩

variable {n d : ℕ}

def comb (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun x := ∑ i, x i • E i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

def coord (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun X := WithLp.toLp 2 (fun i => ((X * (E i)ᴴ).trace).re)
  map_add' X Y := by ext i; simp [Matrix.add_mul]
  map_smul' c X := by ext i; simp

theorem coord_comb (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (x : EuclideanSpace ℝ (Fin d)) :
    coord E (comb E x) = x := by
  ext k
  change (((∑ i, x i • E i) * (E k)ᴴ).trace).re = x k
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
    Complex.smul_re, hE]
  simp


open scoped Matrix.Norms.Frobenius in
theorem chart_surj : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < ρ → ∃ g : Formalism.REAL.UJ ε, uMat g - 1 ∈ A ∧ Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < δ ∧ (WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) = x := by
  intro n ε A d E hA hE hs δ hδ
  obtain ⟨ρ, hρ, h⟩ := exists_ball_subset (LinearMap.toContinuousLinearMap (comb E))
    (LinearMap.toContinuousLinearMap (coord E)) (coord_comb E hE)
    (f := fun Y => NormedSpace.exp Y - 1)
    (HasStrictFDerivAt.sub_const (f := NormedSpace.exp) 1 CompactDualExists.exp_strict)
    (sub_eq_zero.2 (NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ))) hδ
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := h x hx
  have hm : comb E y ∈ A ∧ Formalism.REAL.inG ε (comb E y) :=
    (hs (∑ i, y i • E i)).2 (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
  refine ⟨GaugeConst.expJ ε ⟨comb E y, hm.2⟩, GaugeSubExists.exp_sub_one_mem A hA hm.1, ?_, hyx⟩
  rw [GaugeConst.sqrt_hs]
  exact hy

end GlobalTheory.GaugeSubChartSurj
end
end

