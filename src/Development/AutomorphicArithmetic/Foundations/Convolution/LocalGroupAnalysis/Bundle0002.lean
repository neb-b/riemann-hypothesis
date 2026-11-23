module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotOpen
section
noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

section

variable {G T : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [T2Space T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]

private lemma uni_comap (μ : Measure G) (hμ : Uni μ) (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    Uni (μ.comap fun u : U => (u : G)) := by
  obtain ⟨h1, h2⟩ := hμ
  haveI := h1
  haveI := h2
  have hUm : MeasurableSet (U : Set G) := hU.measurableSet
  have emb : MeasurableEmbedding (fun u : U => (u : G)) := MeasurableEmbedding.subtype_coe hUm
  have hH : (μ.comap U.subtype).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) μ hU.isOpenEmbedding_subtypeVal
  refine ⟨hH, ⟨?_⟩⟩
  ext s hs
  rw [Measure.inv_apply, emb.comap_apply, emb.comap_apply]
  have e : (fun u : U => (u : G)) '' s⁻¹ = ((fun u : U => (u : G)) '' s)⁻¹ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u⁻¹, hu, by simp⟩
    · intro hx
      obtain ⟨u, hu, hux⟩ := hx
      refine ⟨u⁻¹, by simpa using hu, ?_⟩
      have hux' : (u : G) = x⁻¹ := hux
      simp [hux']
  rw [e, Measure.measure_inv]

private def ext0 (U : Subgroup G) (r : U → ℝ≥0∞) : G → ℝ≥0∞ :=
  Function.extend (fun u : U => (u : G)) r 0

private lemma ext0_coe (U : Subgroup G) (r : U → ℝ≥0∞) (u : U) : ext0 U r (u : G) = r u :=
  Subtype.val_injective.extend_apply _ _ _

private lemma extendByZero_not_mem (U : Subgroup G) (r : U → ℝ≥0∞) {g : G} (hg : g ∉ U) : ext0 U r g = 0 := by
  unfold ext0
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨u, rfl⟩
    exact hg u.2

private lemma nrm_on_coset (j : T →* G) (ν : Measure T) (U : Subgroup G)
    (hV : MeasurableSet ((U.comap j : Subgroup T) : Set T)) (i : U.comap j →* U)
    (hi : ∀ t, (i t : G) = j t) (r : U → ℝ≥0∞)
    (h₀ : ∀ x, ∫⁻ t, r (i t * x) ∂(ν.comap fun t : U.comap j => (t : T)) = 1) (u : U) :
    ∫⁻ t, ext0 U r (j t * u) ∂ν = 1 := by
  have e : (fun t => ext0 U r (j t * u)) =
      ((U.comap j : Subgroup T) : Set T).indicator (fun t => ext0 U r (j t * u)) := by
    funext t
    by_cases ht : t ∈ U.comap j
    · rw [Set.indicator_of_mem (by exact ht)]
    · rw [Set.indicator_of_notMem (by exact ht)]
      apply extendByZero_not_mem
      intro hmem
      apply ht
      have h2 : j t = (j t * u) * (u : G)⁻¹ := by group
      rw [Subgroup.mem_comap, h2]
      exact U.mul_mem hmem (U.inv_mem u.2)
  have h := lintegral_subtype_comap hV (μ := ν) (fun t => ext0 U r (j t * u))
  rw [e, lintegral_indicator hV, ← h, ← h₀ u]
  refine lintegral_congr fun t => ?_
  have h3 : j (t : T) * (u : G) = ((i t * u : U) : G) := by simp [hi]
  rw [h3, ext0_coe]

open Classical in
private lemma isNrm_glue (j : T →* G) (ν : Measure T) (hν : Uni ν) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (hV : MeasurableSet ((U.comap j : Subgroup T) : Set T))
    (i : U.comap j →* U) (hi : ∀ t, (i t : G) = j t) (r : U → ℝ≥0∞)
    (h₀ : IsNrm i (ν.comap fun t : U.comap j => (t : T)) r) (r' : G → ℝ≥0∞) (h' : IsNrm j ν r') :
    IsNrm j ν ((Set.range j * (U : Set G)).piecewise (ext0 U r) r') := by
  haveI := hν.2
  haveI := hν.1
  haveI : ν.IsMulRightInvariant := by
    have h2 : (ν.inv).IsMulRightInvariant := inferInstance
    rwa [Measure.IsInvInvariant.inv_eq_self] at h2
  have hS : IsOpen (Set.range j * (U : Set G)) := hU.mul_left
  have hm : Measurable (ext0 U r) :=
    (MeasurableEmbedding.subtype_coe hU.measurableSet).measurable_extend h₀.1 measurable_const
  refine ⟨hm.piecewise hS.measurableSet h'.1, fun x => ?_⟩
  by_cases hx : x ∈ Set.range j * (U : Set G)
  · obtain ⟨_, ⟨s, rfl⟩, u, hu, rfl⟩ := hx
    have e : ∀ t, (Set.range j * (U : Set G)).piecewise (ext0 U r) r' (j t * (j s * u)) =
        ext0 U r (j (t * s) * u) := by
      intro t
      rw [Set.piecewise_eq_of_mem, map_mul, mul_assoc]
      exact ⟨j (t * s), ⟨_, rfl⟩, u, hu, by simp [mul_assoc]⟩
    refine Eq.trans (lintegral_congr e) ((lintegral_mul_right_eq_self (μ := ν)
      (fun t => ext0 U r (j t * u)) s).trans ?_)
    exact nrm_on_coset j ν U hV i hi r h₀.2 ⟨u, hu⟩
  · have e : ∀ t, (Set.range j * (U : Set G)).piecewise (ext0 U r) r' (j t * x) = r' (j t * x) := by
      intro t
      apply Set.piecewise_eq_of_notMem
      intro hm2
      apply hx
      obtain ⟨_, ⟨s, rfl⟩, u, hu, hxe⟩ := hm2
      refine ⟨j (t⁻¹ * s), ⟨_, rfl⟩, u, hu, ?_⟩
      have hxe' : j s * u = j t * x := hxe
      change j (t⁻¹ * s) * u = x
      rw [map_mul, map_inv, mul_assoc, hxe', inv_mul_cancel_left]
    exact (lintegral_congr e).trans (h'.2 x)

end

end UpperTheory.ConvolutionTheory.G

open MeasureTheory Topology UpperTheory.ConvolutionTheory.G in
theorem UpperTheory.ConvolutionTheory.G.quotOpen_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotOpen := by
  classical
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν h U hU i hi
  obtain ⟨hμ, hj, hν⟩ := id h
  have hV : IsOpen ((U.comap j : Subgroup T) : Set T) := hU.preimage hj.continuous
  have hUm : MeasurableSet (U : Set G) := hU.measurableSet
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  haveI : SecondCountableTopology (U.comap j) :=
    TopologicalSpace.Subtype.secondCountableTopology ((U.comap j : Subgroup T) : Set T)
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (U.comap j) := hV.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hUc : IsClosedEmbedding (fun u : U => (u : G)) :=
    (Subgroup.isClosed_of_isOpen U hU).isClosedEmbedding_subtypeVal
  have hVc : IsClosedEmbedding (fun t : U.comap j => (t : T)) :=
    (Subgroup.isClosed_of_isOpen _ hV).isClosedEmbedding_subtypeVal
  have hic : IsClosedEmbedding i := by
    have h1 : IsClosedEmbedding ((fun u : U => (u : G)) ∘ i) := by
      have h2 : ((fun u : U => (u : G)) ∘ i) = j ∘ (fun t : U.comap j => (t : T)) := by
        funext t
        exact hi t
      rw [h2]
      exact hj.comp hVc
    exact (IsClosedEmbedding.of_comp_iff hUc).1 h1
  have hs : Pair (μ.comap fun u : U => (u : G)) i (ν.comap fun t : U.comap j => (t : T)) :=
    ⟨uni_comap μ hμ U hU, hic, uni_comap ν hν _ hV⟩
  refine ⟨hs, fun F hFm hFi hFs => ?_⟩
  obtain ⟨r₀, -, hr₀, -⟩ := hN U (U.comap j) _ i _ hs
  obtain ⟨r', -, hr', -⟩ := hN G T μ j ν h
  have hg := isNrm_glue j ν hν U hU hV.measurableSet i hi _ hr₀ _ hr'
  obtain ⟨hQ1, -, hQ3⟩ := hE G T μ j ν h F hFm hFi _ hg
  have hFm' : Measurable (fun u : U => F u) := hFm.comp measurable_subtype_coe
  have hFi' : ∀ (t : U.comap j) (g : U), F ((i t * g : U) : G) = F g := by
    intro t g
    simp [hi, hFi]
  obtain ⟨hq1, -, hq3⟩ := hE U (U.comap j) _ i _ hs (fun u => F u) hFm' hFi' _ hr₀
  have key : (fun x => F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ)) =
      (U : Set G).indicator (fun x => F x * (((ext0 U fun u => (r₀ u : ENNReal)) x).toReal : ℂ)) := by
    funext x
    by_cases hxU : x ∈ (U : Set G)
    · rw [Set.indicator_of_mem hxU, Set.piecewise_eq_of_mem]
      exact ⟨1, ⟨1, map_one j⟩, x, hxU, one_mul x⟩
    · rw [Set.indicator_of_notMem hxU]
      by_cases hxS : x ∈ Set.range j * (U : Set G)
      · rw [Set.piecewise_eq_of_mem _ _ _ hxS, extendByZero_not_mem U _ hxU]
        simp
      · have : F x = 0 := by
          by_contra h0
          exact hxS (hFs x h0)
        simp [this]
  have cmp : (fun x => F x * (((ext0 U fun u => (r₀ u : ENNReal)) x).toReal : ℂ)) ∘
      (fun u : U => (u : G)) = fun u : U => F u * (((r₀ u : ENNReal)).toReal : ℂ) := by
    funext u
    simp only [Function.comp]
    rw [show ext0 U (fun u => (r₀ u : ENNReal)) (u : G) = _ from ext0_coe U _ u]
  have i1 : Integrable (fun x => F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ)) μ ↔
      Integrable (fun u : U => F u * (((r₀ u : ENNReal)).toReal : ℂ))
        (μ.comap fun u : U => (u : G)) := by
    rw [key, integrable_indicator_iff hUm, integrableOn_iff_comap_subtypeVal hUm]
    exact Iff.of_eq (congrArg (fun f => Integrable f (μ.comap fun u : U => (u : G))) cmp)
  have i2 : ∫ x, F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ) ∂μ =
      ∫ u : U, F u * (((r₀ u : ENNReal)).toReal : ℂ) ∂(μ.comap fun u : U => (u : G)) := by
    rw [key, integral_indicator hUm, ← integral_subtype_comap hUm]
    exact congrArg (fun f => ∫ u : U, f u ∂(μ.comap fun u : U => (u : G))) cmp
  exact ⟨hQ1.trans (i1.trans hq1.symm), hQ3.trans (i2.trans hq3.symm)⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotPi
section
open MeasureTheory Topology
open scoped ENNReal

private theorem lintegral_pi_one {ι : Type} [Fintype ι] {T : ι → Type} [∀ i, MeasurableSpace (T i)]
    (ν : ∀ i, Measure (T i)) [∀ i, SigmaFinite (ν i)] (f : ∀ i, T i → NNReal)
    (hf : ∀ i, Measurable (f i)) (h1 : ∀ i, ∫⁻ t, (f i t : ℝ≥0∞) ∂(ν i) = 1) :
    ∫⁻ t, ((∏ i, f i (t i) : NNReal) : ℝ≥0∞) ∂(Measure.pi ν) = 1 := by
  have hint : ∀ i, Integrable (fun t => (f i t : ℝ)) (ν i) := fun i => by
    have := integrable_toReal_of_lintegral_ne_top (μ := ν i) (f := fun t => (f i t : ℝ≥0∞))
      (hf i).coe_nnreal_ennreal.aemeasurable (by rw [h1 i]; exact ENNReal.one_ne_top)
    simpa using this
  have hI : ∀ i, ∫ t, (f i t : ℝ) ∂(ν i) = 1 := fun i => by
    have := lintegral_coe_eq_integral (f i) (hint i)
    rw [h1 i] at this
    exact ENNReal.ofReal_eq_one.1 this.symm
  have hP : Integrable (fun t : ∀ i, T i => ((∏ i, f i (t i) : NNReal) : ℝ)) (Measure.pi ν) := by
    simp only [NNReal.coe_prod]
    exact Integrable.fintype_prod_dep hint
  rw [lintegral_coe_eq_integral _ hP]
  simp only [NNReal.coe_prod]
  rw [integral_fintype_prod_eq_prod (fun i t => (f i t : ℝ))]
  simp [hI]

theorem UpperTheory.ConvolutionTheory.G.quotPi_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotPi := by
  intro hN hE ι _ G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP J hJ
  haveI : ∀ i, (μ i).IsHaarMeasure := fun i => (hP i).1.1
  haveI : ∀ i, (μ i).IsInvInvariant := fun i => (hP i).1.2
  haveI : ∀ i, (ν i).IsHaarMeasure := fun i => (hP i).2.2.1
  haveI : ∀ i, (ν i).IsInvInvariant := fun i => (hP i).2.2.2
  have hJe : (J : (∀ i, T i) → ∀ i, G i) = Pi.map (fun i => (j i : T i → G i)) := by
    funext t i
    exact hJ t i
  have hPair : UpperTheory.ConvolutionTheory.G.Pair (Measure.pi μ) J (Measure.pi ν) := by
    refine ⟨⟨inferInstance, inferInstance⟩, ?_, ⟨inferInstance, inferInstance⟩⟩
    rw [hJe]
    exact IsClosedEmbedding.piMap fun i => (hP i).2.1
  refine ⟨hPair, fun F hF => ?_⟩
  choose ρ hρc hρn _ using fun i => hN (G i) (T i) (μ i) (j i) (ν i) (hP i)
  have hR : UpperTheory.ConvolutionTheory.G.IsNrm J (Measure.pi ν)
      (fun g => ((∏ i, ρ i (g i) : NNReal) : ℝ≥0∞)) := by
    refine ⟨?_, fun x => ?_⟩
    · exact (Finset.measurable_prod _ fun i _ =>
        (hρc i).measurable.comp (measurable_pi_apply i)).coe_nnreal_ennreal
    · have := lintegral_pi_one ν (fun i t => ρ i (j i t * x i))
        (fun i => ((hρc i).comp ((hP i).2.1.continuous.mul continuous_const)).measurable)
        (fun i => (hρn i).2 (x i))
      simpa only [Pi.mul_apply, hJ] using this
  have hFm : Measurable fun g : ∀ i, G i => ∏ i, F i (g i) :=
    Finset.measurable_prod _ fun i _ => (hF i).1.comp (measurable_pi_apply i)
  have hFi : ∀ t g, (fun g : ∀ i, G i => ∏ i, F i (g i)) (J t * g) =
      (fun g : ∀ i, G i => ∏ i, F i (g i)) g := fun t g => by
    simp only [Pi.mul_apply, hJ, (hF _).2]
  obtain ⟨h1, -, h2⟩ := hE _ _ _ _ _ hPair _ hFm hFi _ hR
  have hloc := fun i => hE (G i) (T i) (μ i) (j i) (ν i) (hP i) (F i) (hF i).1 (hF i).2 _ (hρn i)
  have hfun : (fun x : ∀ i, G i => (∏ i, F i (x i)) *
      ((((∏ i, ρ i (x i) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ)) =
      fun x => ∏ i, (F i (x i) * (((ρ i (x i) : ℝ≥0∞).toReal : ℝ) : ℂ)) := by
    funext x
    simp only [ENNReal.coe_toReal, NNReal.coe_prod, Complex.ofReal_prod, Finset.prod_mul_distrib]
  refine ⟨fun hq => h1.2 ?_, ?_⟩
  · rw [hfun]
    exact Integrable.fintype_prod_dep
      (f := fun i x => F i x * (((ρ i x : ℝ≥0∞).toReal : ℝ) : ℂ)) fun i => (hloc i).1.1 (hq i)
  · rw [h2, hfun, integral_fintype_prod_eq_prod
      (fun i x => F i x * (((ρ i x : ℝ≥0∞).toReal : ℝ) : ℂ))]
    exact Finset.prod_congr rfl fun i _ => (hloc i).2.2.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotProd
section
open MeasureTheory Topology
open scoped ENNReal

private theorem UpperTheory.ConvolutionTheory.G.uni_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [LocallyCompactSpace G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G']
    {μ : Measure G} {μ' : Measure G'} (h : UpperTheory.ConvolutionTheory.G.Uni μ) (h' : UpperTheory.ConvolutionTheory.G.Uni μ') :
    UpperTheory.ConvolutionTheory.G.Uni (μ.prod μ') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨inferInstance, ⟨?_⟩⟩
  have e : (Inv.inv : G × G' → G × G') = Prod.map Inv.inv Inv.inv := rfl
  rw [Measure.inv_def, e, ← Measure.map_prod_map _ _ measurable_inv measurable_inv,
    Measure.map_inv_eq_self, Measure.map_inv_eq_self]

theorem UpperTheory.ConvolutionTheory.G.quotProd_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotProd := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν hP μ' j' ν' hP'
  have hPP : UpperTheory.ConvolutionTheory.G.Pair (μ.prod μ') (j.prodMap j') (ν.prod ν') :=
    ⟨UpperTheory.ConvolutionTheory.G.uni_prod hP.1 hP'.1, hP.2.1.prodMap hP'.2.1, UpperTheory.ConvolutionTheory.G.uni_prod hP.2.2 hP'.2.2⟩
  refine ⟨hPP, fun F F' hF hFi hF' hFi' => ?_⟩
  obtain ⟨ρ, hc, hρ, -⟩ := hN G T μ j ν hP
  obtain ⟨ρ', hc', hρ', -⟩ := hN G' T' μ' j' ν' hP'
  haveI := hP.1.1
  haveI := hP'.1.1
  haveI := hP.2.2.1
  haveI := hP'.2.2.1
  have hj : Measurable j := hP.2.1.continuous.measurable
  have hj' : Measurable j' := hP'.2.1.continuous.measurable
  have hρρ : UpperTheory.ConvolutionTheory.G.IsNrm (j.prodMap j') (ν.prod ν')
      (fun g : G × G' => (ρ g.1 : ℝ≥0∞) * (ρ' g.2 : ℝ≥0∞)) := by
    refine ⟨(hρ.1.comp measurable_fst).mul (hρ'.1.comp measurable_snd), fun x => ?_⟩
    have := lintegral_prod_mul (μ := ν) (ν := ν') (f := fun t => (ρ (j t * x.1) : ℝ≥0∞))
      (g := fun t => (ρ' (j' t * x.2) : ℝ≥0∞))
      (hρ.1.comp (hj.mul_const _)).aemeasurable (hρ'.1.comp (hj'.mul_const _)).aemeasurable
    rw [hρ.2 x.1, hρ'.2 x.2, mul_one] at this
    exact this
  have hm : Measurable (fun g : G × G' => F g.1 * F' g.2) :=
    (hF.comp measurable_fst).mul (hF'.comp measurable_snd)
  have hi : ∀ (t : T × T') (g : G × G'),
      (fun g : G × G' => F g.1 * F' g.2) (j.prodMap j' t * g) = (fun g : G × G' => F g.1 * F' g.2) g := by
    intro t g
    show F (j t.1 * g.1) * F' (j' t.2 * g.2) = _
    rw [hFi, hFi']
  obtain ⟨a1, -, a3⟩ := hE G T μ j ν hP F hF hFi _ hρ
  obtain ⟨b1, -, b3⟩ := hE G' T' μ' j' ν' hP' F' hF' hFi' _ hρ'
  obtain ⟨c1, -, c3⟩ := hE (G × G') (T × T') _ _ _ hPP _ hm hi _ hρρ
  have key : (fun x : G × G' => F x.1 * F' x.2 * ((((ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)).toReal : ℝ) : ℂ)) =
      fun x : G × G' => (F x.1 * (((ρ x.1 : ℝ≥0∞).toReal : ℝ) : ℂ)) * (F' x.2 * (((ρ' x.2 : ℝ≥0∞).toReal : ℝ) : ℂ)) := by
    funext x
    rw [ENNReal.toReal_mul, Complex.ofReal_mul]
    ring
  refine ⟨fun h h' => ?_, ?_⟩
  · rw [c1, key]
    exact (a1.1 h).mul_prod (b1.1 h')
  · rw [c3, key, a3, b3]
    exact integral_prod_mul (fun x => F x * (((ρ x : ℝ≥0∞).toReal : ℝ) : ℂ))
      (fun x => F' x * (((ρ' x : ℝ≥0∞).toReal : ℝ) : ℂ))
end

