module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0257
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralGaussianHermitianNormFibreEqDeriv
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.GaussFibre

theorem eq_ofReal_deriv (G : ℝ → ℝ≥0∞) (F m : ℝ → ℝ) (β d : ℝ) (hβ : β ≠ 0)
    (hF : HasDerivAt F d β) (hm : ContinuousAt m 1) (hm1 : m 1 = 1)
    (hint : ∀ a b : ℝ, a ≤ b → (0 : ℝ) ∉ Set.Ioc a b →
      ∫⁻ y in Set.Ioc a b, G y = ENNReal.ofReal (F b - F a))
    (hup : ∀ t, 1 ≤ t → G (t * β) ≤ ENNReal.ofReal (m t) * G β)
    (hlo : ∀ t, 0 < t → t ≤ 1 → ENNReal.ofReal (m t) * G β ≤ G (t * β)) :
    G β = ENNReal.ofReal d := by
  have hsl : Tendsto (fun t : ℝ => ENNReal.ofReal (slope F β (t * β))) (𝓝[≠] 1)
      (𝓝 (ENNReal.ofReal d)) := by
    refine (ENNReal.continuous_ofReal.tendsto d).comp
      ((hasDerivAt_iff_tendsto_slope.1 hF).comp ?_)
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => t * β) (𝓝 1) (𝓝 (1 * β)) :=
        (continuous_id.mul continuous_const).tendsto 1
      rw [one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht h
      exact ht (mul_right_cancel₀ hβ ((h : t * β = β).trans (one_mul β).symm))
  have hmem : ∀ t y, y ∈ Set.uIoc β (t * β) → ∃ s ∈ Set.uIcc 1 t, s * β = y := by
    intro t y hy
    have h1 := Set.uIoc_subset_uIcc hy
    have h2 := Set.image_mul_const_uIcc β 1 t
    rw [one_mul] at h2
    rw [← h2] at h1
    exact h1
  have hI : ∀ t, 0 < t → t ≠ 1 → ∫⁻ y in Set.uIoc β (t * β), G y =
      ENNReal.ofReal (slope F β (t * β)) * volume (Set.uIoc β (t * β)) := by
    intro t ht ht1
    have h0 : (0 : ℝ) ∉ Set.uIoc β (t * β) := by
      intro h
      obtain ⟨s, hs, hs0⟩ := hmem t 0 h
      have : 0 < s := lt_of_lt_of_le (lt_min one_pos ht) hs.1
      exact (mul_ne_zero this.ne' hβ) hs0
    have hne : t * β - β ≠ 0 := by
      intro h
      exact ht1 (mul_right_cancel₀ hβ ((sub_eq_zero.1 h).trans (one_mul β).symm))
    rw [Real.volume_uIoc, ← ENNReal.ofReal_mul' (abs_nonneg _), slope_def_field]
    rcases le_total β (t * β) with h | h
    · rw [Set.uIoc_of_le h] at h0 ⊢
      rw [hint _ _ h h0, abs_of_nonneg (sub_nonneg.2 h), div_mul_cancel₀ _ hne]
    · rw [Set.uIoc_of_ge h] at h0 ⊢
      rw [hint _ _ h h0, abs_of_nonpos (sub_nonpos.2 h), mul_neg, div_mul_cancel₀ _ hne, neg_sub]
  have hv0 : ∀ t, t ≠ 1 → volume (Set.uIoc β (t * β)) ≠ 0 := by
    intro t ht1
    have hne : t * β - β ≠ 0 := by
      intro h
      exact ht1 (mul_right_cancel₀ hβ ((sub_eq_zero.1 h).trans (one_mul β).symm))
    rw [Real.volume_uIoc]
    exact (ENNReal.ofReal_pos.2 (abs_pos.2 hne)).ne'
  have hvt : ∀ t, volume (Set.uIoc β (t * β)) ≠ ⊤ := by
    intro t
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  have hev : ∀ p : ℝ → Prop, (∀ᶠ s in 𝓝 (1 : ℝ), p s) →
      ∀ᶠ t in 𝓝 (1 : ℝ), ∀ s ∈ Set.uIcc 1 t, p s := by
    intro p hp
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 hp
    refine Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun t ht s hs => h ?_⟩
    rw [Real.dist_eq] at ht ⊢
    exact (Set.abs_sub_left_of_mem_uIcc hs).trans_lt ht
  have hK : ∀ l : Filter ℝ, l ≤ 𝓝 1 →
      Tendsto (fun r : ℝ => ENNReal.ofReal r * G β) l (𝓝 (G β)) := by
    intro l hl
    have := ENNReal.Tendsto.mul_const (b := G β)
      ((ENNReal.continuous_ofReal.tendsto 1).mono_left hl) (Or.inl (by simp))
    simpa using this
  apply le_antisymm
  · refine le_of_tendsto (hK (𝓝[<] 1) nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : r < 1)
    refine ge_of_tendsto (hsl.mono_left (nhdsLT_le_nhdsNE 1)) ?_
    have h1 : ∀ᶠ s in 𝓝 (1 : ℝ), r < m s ∧ 0 < s :=
      (hm.eventually (lt_mem_nhds (hr.trans_eq hm1.symm))).and (lt_mem_nhds one_pos)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hev _ h1)] with t (ht : t < 1) hs
    rw [← ENNReal.mul_le_mul_iff_left (hv0 t ht.ne) (hvt t),
      ← hI t (hs t Set.right_mem_uIcc).2 ht.ne, ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_uIoc fun y hy => ?_
    obtain ⟨s, hs', rfl⟩ := hmem t y hy
    refine le_trans ?_ (hlo s (hs s hs').2 (hs'.2.trans (max_le le_rfl ht.le)))
    gcongr
    exact (hs s hs').1.le
  · refine ge_of_tendsto (hK (𝓝[>] 1) nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 1 < r)
    refine le_of_tendsto (hsl.mono_left (nhdsGT_le_nhdsNE 1)) ?_
    have h1 : ∀ᶠ s in 𝓝 (1 : ℝ), m s < r := hm.eventually (gt_mem_nhds (hm1.trans_lt hr))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hev _ h1)] with t (ht : 1 < t) hs
    rw [← ENNReal.mul_le_mul_iff_left (hv0 t ht.ne') (hvt t),
      ← hI t (one_pos.trans ht) ht.ne', ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_uIoc fun y hy => ?_
    obtain ⟨s, hs', rfl⟩ := hmem t y hy
    refine le_trans (hup s ((le_min le_rfl ht.le).trans hs'.1)) ?_
    gcongr
    exact (hs s hs').le

variable {P Q : ℕ}

theorem gaussSp_pos (y : Sp P Q) : 0 < gaussSp y := Real.exp_pos _

theorem integrable_gaussSp : Integrable (gaussSp : Sp P Q → ℝ) := by
  have h1 : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
    have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 1) (by simp) 0 0).norm
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  have h2 := Integrable.fintype_prod (ι := Fin P ⊕ Fin Q) (μ := fun _ => (volume : Measure ℂ))
    (f := fun _ (z : ℂ) => Real.exp (-‖z‖ ^ 2)) (fun _ => h1)
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only [gaussSp, ← Real.exp_sum, Finset.sum_neg_distrib]

theorem gaussSp_smul (c : ℝ) (y : Sp P Q) :
    gaussSp (c • y) = Real.exp (-(c ^ 2 * ∑ i, ‖y i‖ ^ 2)) := by
  simp only [gaussSp, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]

theorem shell {fib : ℝ → Measure (Sp P Q)} (h : IsDxDq fib) (a b : ℝ) (hab : a ≤ b)
    (h0 : (0 : ℝ) ∉ Set.Ioc a b) :
    ∫⁻ t in Set.Ioc a b, ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib t) =
      ENNReal.ofReal (2 ^ (P + Q) * (∫ y in {y : Sp P Q | qf y ≤ b}, gaussSp y) -
        2 ^ (P + Q) * ∫ y in {y : Sp P Q | qf y ≤ a}, gaussSp y) := by
  have hq : Measurable (qf : Sp P Q → ℝ) := GlobalTheory.RealPlaceCompare.continuous_qf.measurable
  have hO : MeasurableSet {x : Sp P Q | x ≠ 0} := isOpen_ne.measurableSet
  have hg : Measurable fun y : Sp P Q => ENNReal.ofReal (gaussSp y) :=
    ENNReal.measurable_ofReal.comp continuous_gaussSp.measurable
  have key := GlobalTheory.IsFibreFamily_lintegral_preimage hq isOpen_ne subset_rfl h
    (({x : Sp P Q | x ≠ 0}).indicator fun y => ENNReal.ofReal (gaussSp y)) (hg.indicator hO)
    (fun v hv => Set.indicator_of_notMem hv _) (Set.Ioc a b) measurableSet_Ioc
  have hsub : qf ⁻¹' Set.Ioc a b ⊆ {x : Sp P Q | x ≠ 0} := by
    rintro x hx rfl
    apply h0
    simpa [qf] using hx
  rw [Set.indicator_indicator, Set.inter_eq_left.2 hsub,
    lintegral_indicator (hq measurableSet_Ioc), Measure.restrict_restrict (hq measurableSet_Ioc),
    Set.inter_eq_left.2 hsub] at key
  have e0 : ∀ t, ∫⁻ y, ({x : Sp P Q | x ≠ 0}).indicator (fun y => ENNReal.ofReal (gaussSp y)) y
      ∂(fib t) = ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib t) := by
    intro t
    have h1 : ∀ᵐ y ∂(fib t), y ∈ qf ⁻¹' {id t} ∩ {x : Sp P Q | x ≠ 0} := h.1 t
    apply lintegral_congr_ae
    filter_upwards [h1] with y hy using Set.indicator_of_mem hy.2 _
  simp only [e0] at key
  have e1 : qf ⁻¹' Set.Ioc a b = {x : Sp P Q | qf x ≤ b} \ {x | qf x ≤ a} := by
    ext x; simp [and_comm]
  rw [← key, ← mul_sub, ← setIntegral_sdiff (s := {x : Sp P Q | qf x ≤ b})
      (t := {x : Sp P Q | qf x ≤ a}) (measurableSet_le hq measurable_const)
      integrable_gaussSp.integrableOn (fun x (hx : qf x ≤ a) => (hx.trans hab : qf x ≤ b)), ← e1,
    ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal integrable_gaussSp.integrableOn
      (Eventually.of_forall fun y => (gaussSp_pos y).le),
    dx, Measure.restrict_smul, lintegral_smul_measure, ENNReal.ofReal_pow (by norm_num)]
  simp

theorem gauss_fibre : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β d : ℝ), IsDxDq fib → β ≠ 0 → HasDerivAt (fun t : ℝ => ∫ y in {y : Sp P Q | qf y ≤ t}, gaussSp y) d β → ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib β) = ENNReal.ofReal (2 ^ (P + Q) * d) := by
  intro P Q fib β d h hβ hF
  have hg : Measurable fun y : Sp P Q => ENNReal.ofReal (gaussSp y) :=
    ENNReal.measurable_ofReal.comp continuous_gaussSp.measurable
  refine eq_ofReal_deriv (fun t => ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib t)) _
    (fun t => t ^ (P + Q) / t) β _ hβ (hF.const_mul (2 ^ (P + Q) : ℝ))
    ((continuousAt_id.pow _).div continuousAt_id one_ne_zero) (by simp)
    (fun a b hab h0 => shell h a b hab h0) (fun t ht => ?_) (fun t ht ht1 => ?_)
  · have ht0 : 0 < t := one_pos.trans_le ht
    rw [_root_.GlobalTheory.FibreScaling.lintegral_fibre_scale P Q fib β t h hβ ht0 _ hg]
    gcongr with y
    rw [gaussSp_smul, Real.sq_sqrt ht0.le, gaussSp]
    have : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [_root_.GlobalTheory.FibreScaling.lintegral_fibre_scale P Q fib β t h hβ ht _ hg]
    gcongr with y
    rw [gaussSp_smul, Real.sq_sqrt ht.le, gaussSp]
    have : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
    exact Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.GaussFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilpotentOfStrict
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.UnitriHaar

theorem map_add_nilpotent {k G : Type*} [NormedField k] [IsUltrametricDist k] [ProperSpace k]
    [AddCommGroup G] [Module k G] [Module.Finite k G] [TopologicalSpace G] [IsModuleTopology k G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (N : Module.End k G) (hN : IsNilpotent N) : μ.map (fun x => x + N x) = μ := by
  have : IsTopologicalAddGroup G := IsModuleTopology.topologicalAddGroup k G
  let e₀ : G ≃ₗ[k] (Fin (Module.finrank k G) → k) := (Module.finBasis k G).equivFun
  let e : G ≃ₜ (Fin (Module.finrank k G) → k) :=
    { e₀.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₀.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap }
  have : LocallyCompactSpace G := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology G := e.secondCountableTopology
  have hc : ∀ f : Module.End k G, Continuous f := fun f => IsModuleTopology.continuous_of_linearMap f
  let K₀ := IsUltrametricDist.closedBall_openAddSubgroup (Fin (Module.finrank k G) → k) one_pos
  let K : AddSubgroup G := K₀.toAddSubgroup.comap e₀.toLinearMap.toAddMonoidHom
  have hKo : IsOpen (K : Set G) := K₀.isOpen.preimage e.continuous
  have hKc : IsCompact (K : Set G) :=
    e.isCompact_preimage.2 (isCompact_closedBall (0 : Fin (Module.finrank k G) → k) 1)
  obtain ⟨m, hm⟩ := hN
  let B : AddSubgroup G := ⨅ j : ℕ, K.comap (N ^ j).toAddMonoidHom
  have hB : ∀ x, x ∈ B ↔ ∀ j : ℕ, (N ^ j) x ∈ K := fun x => by
    simp [B, AddSubgroup.mem_iInf]
  have hBo : IsOpen (B : Set G) := by
    have : (B : Set G) = ⋂ j ∈ Finset.range m, (N ^ j : Module.End k G) ⁻¹' (K : Set G) := by
      ext x
      simp only [SetLike.mem_coe, hB, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
      refine ⟨fun h j _ => h j, fun h j => ?_⟩
      by_cases hj : j < m
      · exact h j hj
      · rw [pow_eq_zero_of_le (not_lt.1 hj) hm]; exact K.zero_mem
    rw [this]
    exact isOpen_biInter_finset fun j _ => hKo.preimage (hc _)
  have hBc : IsCompact (B : Set G) :=
    hKc.of_isClosed_subset (B.isClosed_of_isOpen hBo) fun x hx => by
      simpa using (hB x).1 hx 0
  have hNB : ∀ x ∈ B, N x ∈ B := fun x hx => (hB _).2 fun j => by
    rw [← Module.End.mul_apply, ← pow_succ]; exact (hB x).1 hx _
  have hNp : ∀ (j : ℕ), ∀ x ∈ B, ((-N) ^ j) x ∈ B := fun j => by
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
      exact B.neg_mem (hNB _ (ih x hx))
  have hm' : (-N) ^ m = 0 := by rw [neg_pow, hm, mul_zero]
  have h1 : (∑ j ∈ Finset.range m, (-N) ^ j) * (1 + N) = 1 := by
    have := geom_sum_mul_neg (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  have h2 : (1 + N) * (∑ j ∈ Finset.range m, (-N) ^ j) = 1 := by
    have := mul_neg_geom_sum (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  let L : G ≃ₜ+ G :=
    { toFun := fun x => x + N x
      invFun := (∑ j ∈ Finset.range m, (-N) ^ j : Module.End k G)
      left_inv := fun x => LinearMap.congr_fun h1 x
      right_inv := fun x => LinearMap.congr_fun h2 x
      map_add' := fun x y => by rw [map_add (f := _)]; abel
      continuous_toFun := continuous_id.add (hc N)
      continuous_invFun := hc _ }
  have hLB : L ⁻¹' (B : Set G) = B := by
    ext x
    refine ⟨fun hx => ?_, fun hx => B.add_mem hx (hNB x hx)⟩
    have : x = (∑ j ∈ Finset.range m, (-N) ^ j : Module.End k G) (L x) := (L.left_inv x).symm
    rw [this, LinearMap.sum_apply]
    exact B.sum_mem fun j _ => hNp j _ hx
  change μ.map L = μ
  have : (μ.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have h3 := Measure.isAddLeftInvariant_eq_smul (μ.map L) μ
  have h4 : μ.map L B = μ B := by
    rw [Measure.map_apply (show Continuous L from L.continuous).measurable hBo.measurableSet, hLB]
  have h5 : μ B ≠ 0 := (hBo.measure_pos μ ⟨0, B.zero_mem⟩).ne'
  have h6 : μ B ≠ ⊤ := hBc.measure_lt_top.ne
  have h7 : Measure.addHaarScalarFactor (μ.map L) μ = 1 := by
    rw [h3, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h4
    have := (ENNReal.mul_left_inj h5 h6).1 (h4.trans (one_mul _).symm)
    exact_mod_cast this
  rw [h3, h7, one_smul]

theorem nilpotent_of_strict {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ a b, ¬ a < b → A a b = 0) : A ^ n = 0 := by
  have : ∀ (j : ℕ) (a b : Fin n), b.val < a.val + j → (A ^ j) a b = 0 := fun j => by
    induction j with
    | zero => intro a b h; rw [pow_zero, Matrix.one_apply_ne]; rintro rfl; omega
    | succ j ih =>
      intro a b h
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : c < b
      · rw [ih a c (by have : c.val < b.val := hc; omega), zero_mul]
      · rw [hA c b hc, mul_zero]
  exact Matrix.ext fun a b => this n a b (by omega)

def strictOf (R : Type*) [CommRing R] (n : ℕ) :
    ({p : Fin n × Fin n // p.1 < p.2} → R) →ₗ[R] Matrix (Fin n) (Fin n) R where
  toFun x := Matrix.of fun a b => if h : a < b then x ⟨(a, b), h⟩ else 0
  map_add' x y := by ext a b; simp only [Matrix.add_apply, Matrix.of_apply]; split_ifs <;> simp
  map_smul' c x := by ext a b; simp only [Matrix.smul_apply, Matrix.of_apply]; split_ifs <;> simp

def above (R : Type*) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →ₗ[R] ({p : Fin n × Fin n // p.1 < p.2} → R) where
  toFun A p := A p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_nilpotent {R : Type*} [CommRing R] {n : ℕ} (u : Matrix (Fin n) (Fin n) R)
    (h1 : ∀ i, u i i = 1) (h0 : ∀ i j, j < i → u i j = 0) :
    ∃ N : Module.End R ({p : Fin n × Fin n // p.1 < p.2} → R), IsNilpotent N ∧
      ∀ x : {p : Fin n × Fin n // p.1 < p.2} → R,
        (fun p : {p : Fin n × Fin n // p.1 < p.2} => (u * Matrix.of (fun a b : Fin n =>
          (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : R))) p.1.1 p.1.2) =
        above R n u + (x + N x) := by
  have hu : ∀ a b, ¬ a < b → (u - 1) a b = 0 := fun a b h => by
    rcases (not_lt.1 h).eq_or_lt with rfl | h
    · simp [h1]
    · simp [h0 a b h, Matrix.one_apply_ne h.ne']
  have hs : ∀ x a b, ¬ a < b → strictOf R n x a b = 0 := fun x a b h => dif_neg h
  have has : ∀ x, above R n (strictOf R n x) = x := fun x => funext fun p => dif_pos p.2
  let N : Module.End R ({p : Fin n × Fin n // p.1 < p.2} → R) :=
    above R n ∘ₗ LinearMap.mulLeft R (u - 1) ∘ₗ strictOf R n
  have hN : ∀ x, strictOf R n (N x) = (u - 1) * strictOf R n x := fun x => by
    ext a b
    by_cases h : a < b
    · exact dif_pos h
    · rw [hs _ a b h, Matrix.mul_apply]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      by_cases hc : a < c
      · rw [hs x c b fun h' => h (hc.trans h'), mul_zero]
      · rw [hu a c hc, zero_mul]
  have hp : ∀ (j : ℕ) x, strictOf R n ((N ^ j) x) = (u - 1) ^ j * strictOf R n x := fun j => by
    induction j with
    | zero => simp
    | succ j ih => intro x; rw [pow_succ', pow_succ', Module.End.mul_apply, hN, ih, mul_assoc]
  refine ⟨N, ⟨n, LinearMap.ext fun x => ?_⟩, fun x => ?_⟩
  · rw [← has ((N ^ n) x), hp, nilpotent_of_strict _ hu, zero_mul, map_zero, LinearMap.zero_apply]
  · have : Matrix.of (fun a b : Fin n =>
        (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : R)) = 1 + strictOf R n x := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp [hs x a a (lt_irrefl a)]
      · simp [hab, strictOf]
    rw [this]
    change above R n (u * (1 + strictOf R n x)) = _
    have h2 : u * (1 + strictOf R n x) = u + (strictOf R n x + (u - 1) * strictOf R n x) := by
      noncomm_ring
    rw [h2, map_add (f := _), map_add (f := _), has]
    rfl


open GlobalTheory.GaugeEx in
theorem map_unitri_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (r : ℕ) (μU : Measure ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E)), μU.IsAddHaarMeasure → ∀ u : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → μU.map (fun (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}) => (u * Matrix.of (fun a b : Fin (r + 1) => (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E))) p.1.1 p.1.2) = μU := by
  intro F E _ _ _ _ _ v r μ hμ u h1 h0
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨N, hN, hx⟩ := exists_nilpotent u h1 h0
  have hN' : IsNilpotent (N.restrictScalars (Fv F v) : Module.End (Fv F v) _) := by
    obtain ⟨m, hm⟩ := hN
    refine ⟨m, LinearMap.ext fun x => ?_⟩
    have := LinearMap.congr_fun hm x
    rw [Module.End.pow_apply] at this ⊢
    exact this
  have h2 := map_add_nilpotent μ _ hN'
  have hc : Continuous fun x => x + N.restrictScalars (Fv F v) x :=
    continuous_id.add (IsModuleTopology.continuous_of_linearMap _)
  rw [funext hx]
  refine Eq.trans ?_ (map_add_left_eq_self μ (above _ (r + 1) u))
  conv_rhs => rw [← h2]
  rw [Measure.map_map (measurable_const_add _) hc.measurable]
  rfl

end GlobalTheory.UnitriHaar
end

