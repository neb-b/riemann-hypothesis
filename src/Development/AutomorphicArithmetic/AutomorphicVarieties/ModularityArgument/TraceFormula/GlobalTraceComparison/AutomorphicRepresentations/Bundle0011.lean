module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0007
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0008
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.FlipHalf
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory Filter Topology

private lemma flip_half (β : ℝ → ℝ) (hi : Integrable β) (h1 : ∫ t, β t = 1) (c : ℝ) :
    Integrable (fun s : ℝ => β (-(s + c) - s)) ∧ ∫ s : ℝ, β (-(s + c) - s) = 1 / 2 := by
  have e : ∀ s : ℝ, β (-(s + c) - s) = (fun y => β (y - c)) ((-2 : ℝ) * s) := by
    intro s
    show β _ = β _
    congr 1
    ring
  have hg : Integrable (fun y => β (y - c)) := hi.comp_sub_right c
  refine ⟨?_, ?_⟩
  · simp_rw [e]
    exact hg.comp_mul_left' (by norm_num)
  · simp_rw [e]
    rw [Measure.integral_comp_mul_left (fun y => β (y - c)) (-2 : ℝ),
      integral_sub_right_eq_self β c, h1]
    norm_num

private lemma flip_core {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z] (ν : Measure X) [SFinite ν]
    (μ : Measure Z) [SFinite μ] (l : X → ℝ) (l' : Z → ℝ) (F : ℝ → X → ℂ) (m : Z → ℂ) (d : X → ℝ)
    (hl : Measurable l) (hl' : Measurable l') (hF : Measurable (Function.uncurry F))
    (hm : Integrable m μ) (hd : Integrable d ν)
    (hb : ∀ s x, |s - l x| ≤ 1 → ‖F s x‖ ≤ d x)
    (hh : ∀ (s : ℝ) (u : ℝ → ℂ), Continuous u → HasCompactSupport u →
      ∫ x, F s x * u (l x) ∂ν = ∫ z, m z * u (-(s + l' z)) ∂μ)
    (β : ℝ → ℝ) (hc : Continuous β) (hs : HasCompactSupport β) (h0 : ∀ t, 0 ≤ β t)
    (h1 : ∫ t, β t = 1) (hr : ∀ t, β t ≠ 0 → |t| ≤ 1) :
    Integrable (fun x => ∫ s : ℝ, F s x * (β (l x - s) : ℂ)) ν ∧
      (∀ x, ‖∫ s : ℝ, F s x * (β (l x - s) : ℂ)‖ ≤ d x) ∧
      ∫ x, (∫ s : ℝ, F s x * (β (l x - s) : ℂ)) ∂ν = (∫ z, m z ∂μ) / 2 := by
  have hi : Integrable β := hc.integrable_of_hasCompactSupport hs
  have hd0 : ∀ x, 0 ≤ d x := fun x => (norm_nonneg _).trans (hb (l x) x (by simp))
  have hpt : ∀ x s, ‖F s x * (β (l x - s) : ℂ)‖ ≤ d x * β (l x - s) := by
    intro x s
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _)]
    by_cases h : β (l x - s) = 0
    · simp [h]
    · have := hr _ h
      rw [abs_sub_comm] at this
      exact mul_le_mul_of_nonneg_right (hb s x this) (h0 _)
  have hmeas : Measurable (fun p : X × ℝ => F p.2 p.1 * (β (l p.1 - p.2) : ℂ)) := by
    have a : Measurable (fun p : X × ℝ => F p.2 p.1) :=
      hF.comp (measurable_snd.prodMk measurable_fst)
    have b : Measurable (fun p : X × ℝ => β (l p.1 - p.2)) :=
      hc.measurable.comp ((hl.comp measurable_fst).sub measurable_snd)
    exact a.mul (Complex.measurable_ofReal.comp b)
  have hsec : ∀ x, Integrable (fun s : ℝ => F s x * (β (l x - s) : ℂ)) := by
    intro x
    have hmaj : Integrable (fun s : ℝ => d x * β (l x - s)) := (hi.comp_sub_left (l x)).const_mul _
    refine hmaj.mono' ?_ (Eventually.of_forall fun s => hpt x s)
    exact (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hle : ∀ x, ∫ s : ℝ, ‖F s x * (β (l x - s) : ℂ)‖ ≤ d x := by
    intro x
    have hmaj : Integrable (fun s : ℝ => d x * β (l x - s)) := (hi.comp_sub_left (l x)).const_mul _
    calc ∫ s : ℝ, ‖F s x * (β (l x - s) : ℂ)‖ ≤ ∫ s : ℝ, d x * β (l x - s) :=
          integral_mono (hsec x).norm hmaj (fun s => hpt x s)
      _ = d x := by
          rw [integral_const_mul, integral_sub_left_eq_self β volume (l x), h1, mul_one]
  have hprod : Integrable (fun p : X × ℝ => F p.2 p.1 * (β (l p.1 - p.2) : ℂ)) (ν.prod volume) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall hsec, ?_⟩
    refine hd.mono' hmeas.aestronglyMeasurable.norm.integral_prod_right' (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hle x
  refine ⟨hprod.integral_prod_left, fun x => (norm_integral_le_integral_norm _).trans (hle x), ?_⟩
  have hsw := integral_integral_swap (f := fun x (s : ℝ) => F s x * (β (l x - s) : ℂ)) hprod
  rw [hsw]
  have hstep : ∀ s : ℝ, ∫ x, F s x * (β (l x - s) : ℂ) ∂ν =
      ∫ z, m z * (β (-(s + l' z) - s) : ℂ) ∂μ := by
    intro s
    have hu : HasCompactSupport (fun t : ℝ => ((β (t - s) : ℝ) : ℂ)) := by
      have : HasCompactSupport (fun t : ℝ => β (t - s)) := hs.comp_homeomorph (Homeomorph.subRight s)
      exact this.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
    exact hh s (fun t => ((β (t - s) : ℝ) : ℂ)) (by fun_prop) hu
  simp_rw [hstep]
  have hmeas2 : AEStronglyMeasurable
      (fun p : ℝ × Z => m p.2 * (β (-(p.1 + l' p.2) - p.1) : ℂ)) ((volume : Measure ℝ).prod μ) := by
    have a : AEStronglyMeasurable (fun p : ℝ × Z => m p.2) ((volume : Measure ℝ).prod μ) :=
      hm.aestronglyMeasurable.comp_snd
    have b : Measurable (fun p : ℝ × Z => β (-(p.1 + l' p.2) - p.1)) :=
      hc.measurable.comp (((measurable_fst.add (hl'.comp measurable_snd)).neg).sub measurable_fst)
    exact a.mul (Complex.measurable_ofReal.comp b).aestronglyMeasurable
  have hnorm : ∀ z, ∫ s : ℝ, ‖m z * (β (-(s + l' z) - s) : ℂ)‖ = ‖m z‖ / 2 := by
    intro z
    have : ∀ s : ℝ, ‖m z * (β (-(s + l' z) - s) : ℂ)‖ = ‖m z‖ * β (-(s + l' z) - s) := by
      intro s
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _)]
    simp_rw [this]
    rw [integral_const_mul, (flip_half β hi h1 (l' z)).2]
    ring
  have hprod2 : Integrable (fun p : ℝ × Z => m p.2 * (β (-(p.1 + l' p.2) - p.1) : ℂ))
      ((volume : Measure ℝ).prod μ) := by
    rw [integrable_prod_iff' hmeas2]
    refine ⟨Eventually.of_forall fun z => ?_, ?_⟩
    · have := (flip_half β hi h1 (l' z)).1.ofReal (𝕜 := ℂ)
      exact this.const_mul (m z)
    · simp_rw [hnorm]
      exact hm.norm.div_const 2
  have hsw2 := integral_integral_swap (f := fun (s : ℝ) z => m z * (β (-(s + l' z) - s) : ℂ)) hprod2
  rw [hsw2]
  have hin : ∀ z, ∫ s : ℝ, m z * (β (-(s + l' z) - s) : ℂ) = m z / 2 := by
    intro z
    rw [integral_const_mul, integral_complex_ofReal, (flip_half β hi h1 (l' z)).2]
    push_cast
    ring
  simp_rw [hin]
  exact integral_div 2 m

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.flip_pf :
    Flip := by
  intro X Z _ _ ν _ μ _ l l' F m d hl hl' hF hFc hm hd hb hh
  have hmeas : Measurable (fun x => F (l x) x) := hF.comp (hl.prodMk measurable_id)
  refine ⟨hd.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun x => hb (l x) x (by simp)), ?_⟩
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun k =>
    ⟨1 / (2 * ((k : ℝ) + 1)), 1 / ((k : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      exact one_div_lt_one_div_of_lt this (by linarith)⟩
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let β : ℕ → ℝ → ℝ := fun k => (φ k).normed volume
  have hr : ∀ k t, β k t ≠ 0 → |t| ≤ 1 := by
    intro k t ht
    have hmem : t ∈ Function.support ((φ k).normed volume) := ht
    rw [(φ k).support_normed_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
    have : (φ k).rOut ≤ 1 := by
      show 1 / ((k : ℝ) + 1) ≤ 1
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := by positivity
      linarith
    linarith
  have hcore := fun k => flip_core ν μ l l' F m d hl hl' hF hm hd hb hh (β k)
    (φ k).continuous_normed (φ k).hasCompactSupport_normed (fun t => (φ k).nonneg_normed t)
    (φ k).integral_normed (hr k)
  have hlim : Tendsto (fun k => ∫ x, (∫ s : ℝ, F s x * (β k (l x - s) : ℂ)) ∂ν) atTop
      (𝓝 (∫ x, F (l x) x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence d (fun k => (hcore k).1.aestronglyMeasurable) hd
      (fun k => Eventually.of_forall (hcore k).2.1) (Eventually.of_forall fun x => ?_)
    have := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure ℝ))
      (g := fun s => F s x) hφ (hFc x) (l x)
    refine this.congr fun k => ?_
    rw [convolution_eq_swap]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp [β, mul_comm]
  have hconst : Tendsto (fun k => ∫ x, (∫ s : ℝ, F s x * (β k (l x - s) : ℂ)) ∂ν) atTop
      (𝓝 ((∫ z, m z ∂μ) / 2)) := by
    simp_rw [fun k => (hcore k).2.2]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hconst
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.GFacPf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

theorem gFac_pf : FinFac → DropP → GFac := by
  intro hF hD E _ _ _ n ι _ s
  obtain ⟨p, hp⟩ := hF E n ι s
  refine ⟨p, fun m x y => ?_⟩
  have hd := hD E n ι s m
  rw [hd x y]
  simp only [hd (ac E n (ldet x) * p.x _) y, Gk, ContinuousLinearMap.comp_apply]
  have hmem : ∀ i, (piSp s.D s.π ι).starProjection (m.Uπ (s.k₂ y i)) ∈ piSp s.D s.π ι := fun i =>
    Submodule.starProjection_apply_mem _ _
  calc _ = ∑ i, ∑ b, (p.w b).1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * p.x b) i)
          ((piSp s.D s.π ι).starProjection (m.Uπ (s.k₂ y i))) :=
        Finset.sum_congr rfl fun i _ => hp _ (hmem i) x i
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.KerRight
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open NumberField PositivityTheory.Rg.BcB.E MeasureTheory

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem ker_left (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {γ : H E n 0}
    (hγ : γ ∈ ratH E n 0) (x y : H E n 0) : kerH φ (γ * x) y = kerH φ x y :=
  ((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).1

private theorem ker_right (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {γ : H E n 0}
    (hγ : γ ∈ ratH E n 0) (x y : H E n 0) : kerH φ x (γ * y) = kerH φ x y :=
  ((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).2

private theorem th_mul' (x y : H E n 0) :
    PositivityTheory.Rg.BcB.E1.th (x * y) = PositivityTheory.Rg.BcB.E1.th x * PositivityTheory.Rg.BcB.E1.th y :=
  Prod.ext (map_mul (PositivityTheory.Rg.BcB.thetaA E n) x.1 y.1) (map_mul (PositivityTheory.Rg.BcB.thetaA E 0) x.2 y.2)

private theorem th_rat {δ : H E n 0} (hδ : δ ∈ ratH E n 0) : PositivityTheory.Rg.BcB.E1.th δ ∈ ratH E n 0 := by
  obtain ⟨γ, rfl⟩ := hδ
  refine ⟨(PositivityTheory.Rg.BcB.thetaE E n γ.1, PositivityTheory.Rg.BcB.thetaE E 0 γ.2), ?_⟩
  exact Prod.ext ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E n).2.2 γ.1).symm
    ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E 0).2.2 γ.2).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.kInv_pf :
    KInv := by
  intro E _ _ _ n ι _ s
  refine ⟨fun γ x => ?_, fun γ x => ?_⟩
  · funext i
    refine ext_inner_right ℂ fun u => ?_
    rw [s.vecs.rep₁, s.vecs.rep₁]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ker_left s.D (s.t₁ i j) γ.2]
  · funext i
    refine ext_inner_left ℂ fun u => ?_
    rw [s.vecs.rep₂, s.vecs.rep₂]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [th_mul', ker_right s.D (s.t₂ j l) (th_rat γ.2)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.LdetRatMul
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped Pointwise

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ldet_rat_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (γ : ratH E n 0) (x : H E n 0) : ldet ((γ : H E n 0) * x) = ldet x := by
  obtain ⟨⟨a, b⟩, hab⟩ := γ.2
  have h1 : (γ : H E n 0).1 = ratGL E n a := by rw [← hab]; rfl
  change logAbs (((γ : H E n 0).1 * x.1).val.det) = logAbs x.1.val.det
  rw [DiscreteGroups.T1.G.Dcy.logAbs_det_mul', h1, DiscreteGroups.T1.G.Dcy.logAbs_ratGL', zero_add]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.aeEq_pf :
    Basic → AeEq := by
  intro _ E _ _ _ n D f g I hf hg hfi hgi hI hae x hx
  by_contra hne
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  set S : Set (H E n 0) := {y | ldet y ∈ I ∧ f y ≠ g y} with hS
  have hSo : IsOpen S :=
    (hI.preimage continuous_ldet).inter (isOpen_ne_fun hf hg)
  have hSx : S.Nonempty := ⟨x, hx, hne⟩
  haveI : Countable (ratH E n 0) := DiscreteGroups.T1.G.Dcy.countable_ratH'
  haveI : D.μ.IsMulLeftInvariant := D.haar.1
  haveI : D.μ.IsOpenPosMeasure := D.haar.2.2.1
  haveI : MeasurableConstSMul (ratH E n 0) (H E n 0) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun y : H E n 0 => (γ : H E n 0) * y).measurable⟩
  haveI : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ :=
    ⟨fun γ s _ => measure_preimage_mul D.μ (γ : H E n 0) s⟩
  have key : ∀ (δ : ratH E n 0) (y : H E n 0), y ∈ S → (δ : H E n 0) * y ∈ S := by
    intro δ y hy
    refine ⟨?_, ?_⟩
    · rw [ldet_rat_mul]; exact hy.1
    · rw [hfi δ y, hgi δ y]; exact hy.2
  have hinv : ∀ γ : ratH E n 0, γ • S = S := by
    intro γ
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact key γ y hy
    · intro y hy
      refine ⟨(γ⁻¹ : ratH E n 0) • y, ?_, smul_inv_smul γ y⟩
      exact key γ⁻¹ y hy
  have hnull : D.μ (S ∩ D.F) = 0 := by
    have h0 : D.ν S = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hae)
      intro y hy h
      exact hy.2 (h hy.1)
    rwa [Dom.ν, Measure.restrict_apply hSo.measurableSet] at h0
  have hz : D.μ S = 0 := D.fd.measure_zero_of_invariant S hinv hnull
  exact (hSo.measure_pos D.μ hSx).ne' hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PBasic
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem logAbs_det_centre (τ : ℝ) :
    logAbs (splitCentre E n τ).val.det = Module.finrank ℚ E * (n * τ) := by
  have h := congrArg (fun g : GA E n => logAbs g.val.det) (Dcy.splitCentre_mul_tor (E := E) (n := n) τ (fun _ => 0))
  simp only [Dcy.logAbs_det_mul', Dcy.logAbs_det_tor] at h
  simpa using h

private theorem ldet_ac (hn : 1 ≤ n) (t : ℝ) : ldet (ac E n t) = t := by
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  change logAbs (splitCentre E n (t / (n * Module.finrank ℚ E))).val.det = t
  rw [logAbs_det_centre]
  field_simp

private theorem logAbs_det_inv (g : GA E n) : logAbs (g⁻¹ : GA E n).val.det = -logAbs g.val.det := by
  have h := Dcy.logAbs_det_mul' g g⁻¹
  have h1 := Dcy.logAbs_ratGL' (E := E) (n := n) 1
  rw [map_one] at h1
  rw [mul_inv_cancel, h1] at h
  linarith

private theorem logAbs_det_theta (g : GA E n) : logAbs (thetaA E n g).val.det = -logAbs g.val.det := by
  have h : (thetaA E n g).val.det = conjAd E (g⁻¹ : GA E n).val.det := by
    change (((g⁻¹ : GA E n).val.map (conjAd E))ᵀ).det = _
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (conjAd E) _).symm
  rw [h, GlobalTheory.CompanionTheory.DegPairingProof.logAbs_conj D1.conjPlaces, logAbs_det_inv]

end SlopeTestRemainingChoices

theorem basic_pf : Basic := by
  intro E _ _ _ n hn
  refine ⟨ldet_ac hn, fun x y => Dcy.logAbs_det_mul' x.1 y.1, fun t x => ?_, fun s t => ?_, ?_, ?_, fun x => ?_, fun x => ?_,
    fun x y => ?_, ?_, continuous_ldet, ?_⟩
  · refine Prod.ext ?_ ?_
    · exact CuspidalL2GL.splitCentre_comm _ _
    · change 1 * x.2 = x.2 * 1
      rw [one_mul, mul_one]
  · refine Prod.ext ?_ (mul_one _).symm
    change splitCentre E n ((s + t) / _) = splitCentre E n (s / _) * splitCentre E n (t / _)
    rw [add_div, CuspidalL2GL.splitCentre_add]
  · refine Prod.ext ?_ rfl
    change splitCentre E n (0 / _) = 1
    rw [zero_div, CuspidalL2GL.splitCentre_zero]
  · exact (GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.comp (continuous_id.div_const _)).prodMk continuous_const
  · exact logAbs_det_theta x.1
  · exact Prod.ext ((thetaBasic_holds E n).2.1 x.1) ((thetaBasic_holds E 0).2.1 x.2)
  · exact Prod.ext (map_mul (thetaA E n) x.1 y.1) (map_mul (thetaA E 0) x.2 y.2)
  · rintro ⟨_, γ, rfl⟩
    refine ⟨Dcy.logAbs_ratGL' γ.1, ⟨(thetaE E n γ.1, thetaE E 0 γ.2), ?_⟩⟩
    exact Prod.ext ((thetaBasic_holds E n).2.2 γ.1).symm ((thetaBasic_holds E 0).2.2 γ.2).symm
  · exact (((thetaBasic_holds E n).1.comp continuous_fst).prodMk ((thetaBasic_holds E 0).1.comp continuous_snd))

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDiagInt
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.diagInt_pf :
    GFac → HalfTerm → DiagInt := by
  intro hF hH
  unfold DiagInt ForSu
  intro E _ _ _ n ι _ s m
  obtain ⟨p, hp⟩ := hF E n ι s
  have hb := fun b => (hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)).1
  have hsum := MeasureTheory.integrable_finsetSum (Finset.univ : Finset p.B) fun b _ => hb b
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.sum_apply]
  exact (hp m x x).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDropP
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.dropP_pf :
    Zero → KInv → Basic → Weak → PointRep → PComm → DropP := by
  intro hZ hK hB hW hR hC E _ _ _ n ι _ s m x y
  classical
  obtain ⟨-, -, -, -, -, -, -, hthth, hthmul, hrat, -, hthc⟩ := hB E n s.pos
  set S := piSp s.D s.π ι with hS
  set P := S.starProjection with hP
  have hmem : ∀ f, P f ∈ S := fun f => Submodule.starProjection_apply_mem S f
  have hPP : ∀ f, P (P f) = P f := fun f => (Submodule.starProjection_eq_self_iff).2 (hmem f)
  have hUπ : ∀ f, m.Uπ f = m.U (P f) := fun f => by
    have h2 : f - P f ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal f
    have hdec : P f + (f - P f) = f := by abel
    calc m.Uπ f = m.Uπ (P f + (f - P f)) := by rw [hdec]
      _ = m.U (P f) := by rw [map_add (f := _), m.pp.1 _ (hmem f), m.pp.2 _ h2, add_zero]
  have C₁ : ∀ f, P (s.T₁ f) = s.T₁ (P f) := hC E n s.pos s.D s.π s.fix ι s.Φ₁ s.T₁ s.t₁ s.o₁
  have C₂ : ∀ f, P (s.T₂ f) = s.T₂ (P f) := hC E n s.pos s.D s.π s.fix ι s.Φ₂ s.T₂ s.t₂ s.o₂
  have C₃ : ∀ f, P ((s.T₁ * m.U * s.T₂) f) = (s.T₁ * m.U * s.T₂) (P f) := hC E n s.pos s.D s.π s.fix ι m.Φ (s.T₁ * m.U * s.T₂) m.t m.o
  set Q : Hs (ι := ι) s.D →L[ℂ] Hs (ι := ι) s.D := (ContinuousLinearMap.id ℂ _ - P) ∘L m.Uπ with hQ
  have hQa : ∀ f, Q f = m.Uπ f - P (m.Uπ f) := fun f => rfl
  have key : ∀ g, s.T₁ (Q (s.T₂ g)) = 0 := fun g => by
    have e : s.T₁ (m.U (s.T₂ (P g))) = (s.T₁ * m.U * s.T₂) (P g) := rfl
    rw [hQa, map_sub, ← C₁, hUπ, C₂, e, ← C₃, hPP, sub_self]
  have hz : ∀ g i, inner ℂ (s.k₁ x i) (Q (s.T₂ g)) = 0 := fun g i => by
    have h0 := hR E n ι s s.Φ₁ s.T₁ s.t₁ s.o₁ (Q (s.T₂ g)) 0 (by rw [map_zero]; exact key g) x i
    rw [h0]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : (((0 : Hs (ι := ι) s.D) j : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) =ᵐ[s.D.ν] 0 := Lp.coeFn_zero _ _ _
    rw [integral_congr_ae (g := fun _ => (0 : ℂ)) (hj.mono fun z hz => by rw [hz]; simp)]
    simp
  set f : H E n 0 → ℂ := fun z => ∑ i, inner ℂ (s.k₁ x i) (Q (s.k₂ (th z) i)) with hf
  have hfc : Continuous f := continuous_finsetSum _ fun i _ =>
    continuous_const.inner (Q.continuous.comp ((s.vecs.cont i).2.comp hthc))
  have hfi : Inv f := fun γ z => by
    have h := (hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th z)
    simp only [hf, hthmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show s.k₂ (th (γ : H E n 0) * th z) = s.k₂ (th z) from h]
  have hf0 := hZ E n s.D f Set.univ hfc hfi isOpen_univ (fun v _ => by
    have hw := fun i => hW E n ι s v (ContinuousLinearMap.adjoint Q (s.k₁ x i)) i
    have hpt : ∀ z, (v : H E n 0 → ℂ) z * f z =
        ∑ i, (v : H E n 0 → ℂ) z * inner ℂ (ContinuousLinearMap.adjoint Q (s.k₁ x i)) (s.k₂ (th z) i) := fun z => by
      simp only [hf, Finset.mul_sum, ContinuousLinearMap.adjoint_inner_left]
    simp only [hpt]
    rw [integral_finsetSum _ fun i _ => (hw i).1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hw i).2, ContinuousLinearMap.adjoint_inner_left]
    exact hz _ i)
  have h1 := hf0 (th y) (Set.mem_univ _)
  simp only [hf, hthth, hQa, inner_sub_right, Finset.sum_sub_distrib] at h1
  exact sub_eq_zero.1 h1
end

