module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import ReciprocityTheory.SemistableReduction.Bundle0002
public import Lemmata.IterateZero.IterZero

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.MeasurePreservingSphereMap
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric
open scoped Pointwise

def sphereMap {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
    (z : UnitSphereC n) : UnitSphereC n :=
  ⟨U z, by rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
           exact mem_sphere_zero_iff_norm.mp z.2⟩

theorem continuous_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    Continuous (sphereMap U) :=
  (U.continuous.comp continuous_subtype_val).subtype_mk _

theorem toSphere_map_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    Measure.map (sphereMap U) (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere =
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  have hmeas := (continuous_sphereMap U).measurable
  ext s hs
  rw [Measure.map_apply hmeas hs, Measure.toSphere_apply' _ (hmeas hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hset : (Set.Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap U ⁻¹' s) :
      Set (EuclideanSpace ℂ (Fin n)))) = U ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    simp only [Set.mem_smul, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨r, hr, U z, ⟨sphereMap U z, hz, rfl⟩, (map_smul U r (z : EuclideanSpace ℂ (Fin n))).symm⟩
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, hxy⟩
      refine ⟨r, hr, U.symm z, ⟨sphereMap U.symm z, ?_, rfl⟩, ?_⟩
      · have : sphereMap U (sphereMap U.symm z) = z := Subtype.ext (by simp [sphereMap])
        rw [this]; exact hz
      · rw [← map_smul, hxy]; simp
  rw [hset]
  have hU : MeasurePreserving (U.toHomeomorph.toMeasurableEquiv) volume volume :=
    U.measurePreserving
  exact hU.measure_preimage_equiv _

theorem measurePreserving_sphereMap {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (sphereMap U) (sphereProb n) (sphereProb n) := by
  refine ⟨(continuous_sphereMap U).measurable, ?_⟩
  unfold sphereProb ProbabilityTheory.cond
  have hmeas : AEMeasurable (sphereMap U) (volume.toSphere) :=
    (continuous_sphereMap U).measurable.aemeasurable
  rw [Measure.restrict_univ, Measure.map_smul _ hmeas, toSphere_map_sphereMap]

def rotCL {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (innerSL ℂ u).smulRight u + t • (ContinuousLinearMap.id ℂ _ - (innerSL ℂ u).smulRight u)

theorem rotCL_apply {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (t : ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    rotCL u t x = inner ℂ u x • u + t • (x - inner ℂ u x • u) := by
  simp [rotCL]

theorem norm_rotCL {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} {t : ℂ} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1)
    (x : EuclideanSpace ℂ (Fin n)) : ‖rotCL u t x‖ = ‖x‖ := by
  have huu : inner ℂ u u = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have horth : inner ℂ u (x - inner ℂ u x • u) = 0 := by
    rw [inner_sub_right, inner_smul_right, huu, mul_one, sub_self]
  have h1 : inner ℂ (inner ℂ u x • u) (t • (x - inner ℂ u x • u)) = 0 := by
    rw [inner_smul_left, inner_smul_right, horth]; simp
  have h2 : inner ℂ (inner ℂ u x • u) (x - inner ℂ u x • u) = 0 := by
    rw [inner_smul_left, horth]; simp
  have hx : x = inner ℂ u x • u + (x - inner ℂ u x • u) := by abel
  have key : ‖rotCL u t x‖ * ‖rotCL u t x‖ = ‖x‖ * ‖x‖ := by
    rw [rotCL_apply, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h1,
      norm_smul t (x - inner ℂ u x • u), ht, one_mul]
    conv_rhs => rw [hx, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h2]
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp key

def rotIso {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} {t : ℂ} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := ((rotCL u t : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)
      norm_map' := norm_rotCL hu ht } rfl

def rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) :
    UnitSphereC n → UnitSphereC n :=
  sphereMap (rotIso hu (t := circleMap 0 1 θ) (by simp [norm_circleMap_zero]))

theorem coe_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ)
    (z : UnitSphereC n) :
    (rotS hu θ z : EuclideanSpace ℂ (Fin n)) =
      inner ℂ u (z : EuclideanSpace ℂ (Fin n)) • u +
        circleMap 0 1 θ • ((z : EuclideanSpace ℂ (Fin n)) - inner ℂ u (z : EuclideanSpace ℂ (Fin n)) • u) :=
  rotCL_apply u _ _

theorem measurePreserving_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) :
    MeasurePreserving (rotS hu θ) (sphereProb n) (sphereProb n) :=
  measurePreserving_sphereMap _

theorem continuous_rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) :
    Continuous (fun p : ℝ × UnitSphereC n => rotS hu p.1 p.2) := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_rotS]
  have hc : Continuous fun p : ℝ × UnitSphereC n => (p.2 : EuclideanSpace ℂ (Fin n)) :=
    continuous_subtype_val.comp continuous_snd
  have hθ : Continuous fun p : ℝ × UnitSphereC n => circleMap 0 1 p.1 :=
    (continuous_circleMap 0 1).comp continuous_fst
  have hi : Continuous fun p : ℝ × UnitSphereC n => inner ℂ u (p.2 : EuclideanSpace ℂ (Fin n)) :=
    continuous_const.inner hc
  exact (hi.smul continuous_const).add (hθ.smul (hc.sub (hi.smul continuous_const)))

theorem sphereProb_inner_eq_zero {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : u ≠ 0) :
    sphereProb n {z | inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0} = 0 := by
  set s : Set (UnitSphereC n) := {z | inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0}
  have hs : MeasurableSet s :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  let P : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    LinearMap.ker (((innerSL ℂ u : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ).restrictScalars ℝ)
  have hP : P ≠ ⊤ := by
    intro h
    have hmem : u ∈ P := h ▸ Submodule.mem_top
    simp only [P, LinearMap.mem_ker, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply] at hmem
    exact hu (inner_self_eq_zero.mp hmem)
  have hsub : Set.Ioo (0 : ℝ) 1 • ((↑) '' s : Set (EuclideanSpace ℂ (Fin n))) ⊆ (P : Set (EuclideanSpace ℂ (Fin n))) := by
    rintro _ ⟨r, -, y, ⟨z, hz, rfl⟩, rfl⟩
    show (((innerSL ℂ u : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ).restrictScalars ℝ) (r • (z : EuclideanSpace ℂ (Fin n))) = 0
    rw [map_smul]
    simp only [LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    rw [show inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0 from hz, smul_zero]
  have h0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere s = 0 := by
    rw [Measure.toSphere_apply' _ hs]
    rw [measure_mono_null hsub (Measure.addHaar_submodule _ P hP), mul_zero]
  simp [sphereProb, ProbabilityTheory.cond, h0]

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.OnePolyGrowth
section
namespace ReciprocityTheory.MultiplicativeHeights

open Filter Topology Function Metric Polynomial

theorem entire_poly_of_growth (k : ℕ) : ∀ (g : ℂ → ℂ) (A : ℝ), Differentiable ℂ g →
    (∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t, g t = P.eval t := by
  first | exact Bl.IterateZero.goal1 .. | (apply Bl.IterateZero.goal1 <;> assumption) | (intros; apply Bl.IterateZero.goal1 <;> assumption)

theorem exists_entire_of_finite_growth (f : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (k : ℕ) (hB : B.Finite)
    (hf : DifferentiableOn ℂ f Bᶜ) (hb : ∀ t ∉ B, ‖f t‖ ≤ A * (1 + ‖t‖) ^ k) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ t ∉ B, g t = f t := by
  classical
  let g : ℂ → ℂ := fun t => if t ∈ B then limUnder (𝓝[≠] t) f else f t
  refine ⟨g, fun c => ?_, fun t ht => if_neg ht⟩
  by_cases hc : c ∈ B
  · have hU : IsOpen (B \ {c})ᶜ := (hB.sdiff).isClosed.isOpen_compl
    set s : Set ℂ := (B \ {c})ᶜ ∩ ball c 1 with hs
    have hsn : s ∈ 𝓝 c := inter_mem (hU.mem_nhds (fun h => h.2 rfl)) (ball_mem_nhds c one_pos)
    have hsub : s \ {c} ⊆ Bᶜ := by
      rintro t ⟨⟨h1, -⟩, h2⟩ htB
      exact h1 ⟨htB, h2⟩
    have hbdd : BddAbove (norm ∘ f '' (s \ {c})) := by
      refine ⟨|A| * (2 + ‖c‖) ^ k, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have htc : ‖t‖ ≤ ‖c‖ + 1 := by
        have h := ht.1.2
        rw [mem_ball, dist_eq_norm] at h
        have := norm_le_norm_add_norm_sub' t c
        linarith [norm_sub_rev t c]
      calc ‖f t‖ ≤ A * (1 + ‖t‖) ^ k := hb t (hsub ht)
        _ ≤ |A| * (1 + ‖t‖) ^ k := mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
        _ ≤ |A| * (2 + ‖c‖) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k)
              (abs_nonneg A)
    have hdiff := Complex.differentiableOn_update_limUnder_of_bddAbove hsn
      (hf.mono hsub) hbdd
    refine (hdiff.differentiableAt hsn).congr_of_eventuallyEq ?_
    filter_upwards [hsn] with t ht
    by_cases htc : t = c
    · subst htc
      simp [g, hc]
    · have htB : t ∉ B := fun h => ht.1 ⟨h, htc⟩
      simp [g, htB, update_of_ne htc]
  · have hO : IsOpen Bᶜ := hB.isClosed.isOpen_compl
    refine (hf.differentiableAt (hO.mem_nhds hc)).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hc] with t ht
    exact if_neg ht

theorem onePolyGrowth_holds : OnePolyGrowthStatement := by
  intro f B A k hB hf hb
  obtain ⟨g, hg, hgf⟩ := exists_entire_of_finite_growth f B A k hB hf hb
  have hclosed : IsClosed {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} :=
    isClosed_le (continuous_norm.comp hg.continuous)
      (continuous_const.mul ((continuous_const.add continuous_norm).pow k))
  have hsub : Bᶜ ⊆ {t : ℂ | ‖g t‖ ≤ A * (1 + ‖t‖) ^ k} := fun t ht => by
    simpa [hgf t ht] using hb t ht
  have hall : ∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k := by
    have hd : Dense Bᶜ := hB.countable.dense_compl ℂ
    intro t
    have : t ∈ closure Bᶜ := by rw [hd.closure_eq]; trivial
    exact closure_minimal hsub hclosed this
  obtain ⟨P, hPd, hP⟩ := entire_poly_of_growth k g A hg hall
  exact ⟨P, hPd, fun t ht => by rw [← hgf t ht, hP t]⟩

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.SJCoreB
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric Set Real

theorem integral_volumeIoiPow (k : ℕ) (g : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), g r ∂(Measure.volumeIoiPow k) = ∫ r in Ioi (0 : ℝ), r ^ k * g r := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ k * g r)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k)]

theorem integrable_volumeIoiPow {k : ℕ} {g : ℝ → ℝ}
    (h : IntegrableOn (fun r ↦ r ^ k * g r) (Ioi 0)) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ g r) (Measure.volumeIoiPow k) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h2 := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp h
  refine h2.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k), mul_comm]

theorem finrank_euclidean_complex (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

private theorem homeomorphUnitSphereProd_smul_eq {n : ℕ} (x : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n)))) :
    ((homeomorphUnitSphereProd _ x).2 : ℝ) •
      ((homeomorphUnitSphereProd _ x).1 : EuclideanSpace ℂ (Fin n)) = x := by
  have hx : ‖(x : EuclideanSpace ℂ (Fin n))‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
  simp [homeomorphUnitSphereProd, homeomorphSphereProd, smul_smul, hx]

theorem integral_polar {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℂ (Fin n) → ℝ) :
    ∫ x, f x = ∫ p : UnitSphereC n × Ioi (0 : ℝ), f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n)))
      ∂((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integral_comp
      (homeomorphUnitSphereProd _).measurableEmbedding
      (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))]
  simp only [homeomorphUnitSphereProd_smul_eq]
  rw [integral_subtype_comap (measurableSet_singleton 0).compl
    (fun x : EuclideanSpace ℂ (Fin n) ↦ f x)]
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)
  rw [Measure.restrict_congr_set (show ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[volume] univ from
    ae_eq_univ.mpr (by rw [compl_compl]; exact measure_singleton 0)), Measure.restrict_univ]

theorem integrable_polar (n : ℕ) {f : EuclideanSpace ℂ (Fin n) → ℝ} (hf : Integrable f) :
    Integrable (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integrable_comp_emb
      (homeomorphUnitSphereProd _).measurableEmbedding]
  have h2 := (integrableOn_iff_comap_subtypeVal (measurableSet_singleton
    (0 : EuclideanSpace ℂ (Fin n))).compl).mp hf.integrableOn
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, homeomorphUnitSphereProd_smul_eq]

def conjVec {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ star (WithLp.ofLp c i))

theorem inner_conjVec {n : ℕ} (c x : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (conjVec c) x = ∑ i, WithLp.ofLp c i * WithLp.ofLp x i := by
  simp [conjVec, PiLp.inner_apply, mul_comm]

theorem norm_conjVec {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : ‖conjVec c‖ = ‖c‖ := by
  simp [conjVec, EuclideanSpace.norm_eq]

theorem sphere_linear_zero_null {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} = 0 := by
  let K : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    (LinearMap.ker (innerₛₗ ℂ (conjVec c))).restrictScalars ℝ
  have hK : K ≠ ⊤ := by
    intro h
    have hm : conjVec c ∈ K := h ▸ Submodule.mem_top
    have hm' : inner ℂ (conjVec c) (conjVec c) = 0 := hm
    rw [inner_self_eq_zero] at hm'
    exact hc (by rw [← norm_eq_zero, ← norm_conjVec c, hm', norm_zero])
  have hset : {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} =
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, spherePoint, inner_conjVec]
  have hs : MeasurableSet
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  rw [hset, Measure.toSphere_apply' _ hs,
    measure_mono_null ?_ (Measure.addHaar_submodule _ K hK), mul_zero]
  rintro _ ⟨t, -, _, ⟨z, hz, rfl⟩, rfl⟩
  exact K.smul_mem t hz

def gaussLogC (a : ℝ) : ℝ := ∫ z : ℂ, log (a * ‖z‖) * exp (-‖z‖ ^ 2)

def gaussOneC : ℝ := ∫ z : ℂ, exp (-‖z‖ ^ 2)

private theorem integrableOn_rpow_mul_exp_neg_sq_Ioi (s : ℝ) (hs : -1 < s) :
    IntegrableOn (fun y : ℝ ↦ y ^ s * exp (-1 * y ^ 2)) (Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_mul_sq one_pos hs

theorem integrable_gaussOneC : Integrable (fun z : ℂ ↦ exp (-‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar volume (f := fun y : ℝ ↦ exp (-y ^ 2))).mpr ?_
  have hd : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  simp only [hd, pow_one, smul_eq_mul]
  refine (integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).congr_fun
    (fun y _ ↦ by simp [Real.rpow_one]) measurableSet_Ioi

private theorem mul_abs_log_mul_le {a : ℝ} (ha : 0 < a) (y : ℝ) (hy : 0 < y) :
    y * |log (a * y)| ≤ |log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) + 2 * y ^ (1 / 2 : ℝ) := by
  have h1 : log y ≤ 2 * y ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hy.le (show (0 : ℝ) < 1 / 2 by norm_num)
    linarith
  have h2 : -log y ≤ 2 * y ^ (-1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div (inv_pos.mpr hy).le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [Real.log_inv, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le] at this
    have e : (-(1 / 2 : ℝ)) = -1 / 2 := by norm_num
    rw [e] at this
    linarith
  have p1 := Real.rpow_nonneg hy.le (1 / 2 : ℝ)
  have p2 := Real.rpow_nonneg hy.le (-1 / 2 : ℝ)
  have habs : |log y| ≤ 2 * y ^ (1 / 2 : ℝ) + 2 * y ^ (-1 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hlog : |log (a * y)| ≤ |log a| + |log y| := by
    rw [Real.log_mul ha.ne' hy.ne']; exact abs_add_le _ _
  have e1 : y * y ^ (1 / 2 : ℝ) = y ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy, Real.rpow_one]
  have e2 : y * y ^ (-1 / 2 : ℝ) = y ^ (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = 1 + (-1 / 2) by norm_num, Real.rpow_add hy, Real.rpow_one]
  calc y * |log (a * y)| ≤ y * (|log a| + (2 * y ^ (1 / 2 : ℝ) + 2 * y ^ (-1 / 2 : ℝ))) := by
        gcongr; exact hlog.trans (by linarith)
    _ = |log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) + 2 * y ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]; linear_combination 2 * e1 + 2 * e2

theorem integrable_gaussLogC {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ ↦ log (a * ‖z‖) * exp (-‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar volume
    (f := fun y : ℝ ↦ log (a * y) * exp (-y ^ 2))).mpr ?_
  have hd : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  simp only [hd, pow_one, smul_eq_mul]
  have hg : IntegrableOn (fun y : ℝ ↦ (|log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) +
      2 * y ^ (1 / 2 : ℝ)) * exp (-1 * y ^ 2)) (Ioi 0) := by
    have := (((integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).const_mul |log a|).add
      ((integrableOn_rpow_mul_exp_neg_sq_Ioi (3 / 2) (by norm_num)).const_mul 2)).add
      ((integrableOn_rpow_mul_exp_neg_sq_Ioi (1 / 2) (by norm_num)).const_mul 2)
    refine this.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ ↦ ?_)
    simp only [Pi.add_apply]
    ring
  refine Integrable.mono' hg (by fun_prop) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦ ?_
  have hy' : (0 : ℝ) < y := hy
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hy', abs_of_pos (exp_pos _), neg_one_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_abs_log_mul_le ha y hy') (exp_pos _).le

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.TorusLexB
section
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder

open MeasureTheory ComplexConjugate

theorem torusProb_isProb (ι : Type) [Fintype ι] : IsProbabilityMeasure (torusProb ι) := by
  constructor
  rw [torusProb, Measure.pi_univ]
  simp [Real.volume_Ioc]

noncomputable def torusFactor (a b : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ a *
    conj (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ b

theorem torus_one_dim (a b : ℕ) :
    ∫ x in Set.Ioc (0 : ℝ) 1, torusFactor a b x = if a = b then 1 else 0 := by
  have key : ∀ x : ℝ, torusFactor a b x =
      Complex.exp ((2 * Real.pi * Complex.I * ((a : ℂ) - b)) * x) := by
    intro x
    simp only [torusFactor, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [← intervalIntegral.integral_of_le zero_le_one]
  simp_rw [key]
  split_ifs with h
  · subst h; simp
  · have hab : ((a : ℂ) - b) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hc : (2 * Real.pi * Complex.I * ((a : ℂ) - b)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) hab
      exact_mod_cast Real.pi_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) - b) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨(a : ℤ) - b, by push_cast; ring⟩
    rw [h1]; simp

noncomputable def torusMono {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) : ℂ :=
  ∏ i, torusPoint θ i ^ s i

theorem norm_torusPoint {ι : Type} (θ : ι → ℝ) (i : ι) : ‖torusPoint θ i‖ = 1 := by
  simp only [torusPoint]
  have h : 2 * (Real.pi : ℂ) * Complex.I * (θ i : ℂ) = ((2 * Real.pi * θ i : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem norm_torusMono {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) :
    ‖torusMono θ s‖ = 1 := by
  simp [torusMono, norm_prod, norm_pow, norm_torusPoint]

theorem continuous_torusPoint {ι : Type} : Continuous (fun θ : ι → ℝ => torusPoint θ) := by
  exact continuous_pi fun i => by simp only [torusPoint]; fun_prop

theorem torus_orth {ι : Type} [Fintype ι] (s t : ι →₀ ℕ) :
    ∫ θ, torusMono θ t * conj (torusMono θ s) ∂(torusProb ι) = if t = s then 1 else 0 := by
  classical
  have h : ∀ θ : ι → ℝ, torusMono θ t * conj (torusMono θ s) =
      ∏ i, torusFactor (t i) (s i) (θ i) := by
    intro θ
    simp only [torusMono, torusFactor, torusPoint, map_prod, map_pow, ← Finset.prod_mul_distrib]
  simp_rw [h]
  rw [torusProb, integral_fintype_prod_eq_prod (f := fun i x => torusFactor (t i) (s i) x)]
  simp_rw [torus_one_dim]
  split_ifs with hts
  · subst hts; simp
  · have : ∃ i, t i ≠ s i := by
      by_contra hc; push_neg at hc; exact hts (Finsupp.ext hc)
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem integrable_of_bdd {ι : Type} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    {g : (ι → ℝ) → E} (hg : Continuous g) (C : ℝ) (hC : ∀ θ, ‖g θ‖ ≤ C) :
    Integrable g (torusProb ι) := by
  haveI := torusProb_isProb ι
  exact Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem eval_torus {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    MvPolynomial.eval (torusPoint θ) f = ∑ s ∈ f.support, f.coeff s * torusMono θ s := by
  rw [MvPolynomial.eval_eq']; rfl

theorem norm_eval_torus_le {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    ‖MvPolynomial.eval (torusPoint θ) f‖ ≤ ∑ s ∈ f.support, ‖f.coeff s‖ := by
  rw [eval_torus]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [norm_mul, norm_torusMono, mul_one]

theorem continuous_eval_torus {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    Continuous (fun θ : ι → ℝ => MvPolynomial.eval (torusPoint θ) f) := by
  exact (MvPolynomial.continuous_eval f).comp continuous_torusPoint

end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
end

