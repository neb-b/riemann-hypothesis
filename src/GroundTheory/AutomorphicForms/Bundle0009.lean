module

public import Mathlib
public import GroundTheory.AutomorphicForms.SmoothRep
public import GroundTheory.AutomorphicForms.QuotientMeasure
public import GroundTheory.AutomorphicForms.TraceClass

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.Induction
section
noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology Pointwise

section RightTranslation

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]

def rightTranslation : Representation ℂ G (G → W) where
  toFun g := LinearMap.funLeft ℂ W (· * g)
  map_one' := by
    ext f x
    simp [LinearMap.funLeft_apply]
  map_mul' g h := by
    ext f x
    simp [LinearMap.funLeft_apply, Module.End.mul_apply, mul_assoc]

@[simp]
theorem rightTranslation_apply (g : G) (f : G → W) (x : G) :
    rightTranslation g f x = f (x * g) := rfl

end RightTranslation

section Induced

variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W)

def indSpace : Submodule ℂ (G → W) where
  carrier := {f | (∀ h : H, ∀ g : G, f ((h : G) * g) = σ h (f g)) ∧
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, ∀ g : G, f (g * k) = f g}
  add_mem' := by
    rintro f₁ f₂ ⟨h₁, K₁, hK₁, hf₁⟩ ⟨h₂, K₂, hK₂, hf₂⟩
    refine ⟨fun h g => by simp [h₁ h g, h₂ h g], K₁ ⊓ K₂, ?_, fun k hk g => ?_⟩
    · rw [Subgroup.coe_inf]
      exact hK₁.inter hK₂
    · simp [hf₁ k (Subgroup.mem_inf.1 hk).1 g, hf₂ k (Subgroup.mem_inf.1 hk).2 g]
  zero_mem' := ⟨fun h g => by simp, ⊤, by simp, fun k _ g => rfl⟩
  smul_mem' := by
    rintro c f ⟨h₁, K, hK, hf⟩
    exact ⟨fun h g => by simp [h₁ h g], K, hK, fun k hk g => by simp [hf k hk g]⟩

variable {H σ} in
theorem mem_indSpace {f : G → W} :
    f ∈ indSpace H σ ↔ (∀ h : H, ∀ g : G, f ((h : G) * g) = σ h (f g)) ∧
      ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, ∀ g : G, f (g * k) = f g :=
  Iff.rfl


variable [IsTopologicalGroup G]


variable {H σ} in
theorem rightTranslation_mem_indSpace {f : G → W} (hf : f ∈ indSpace H σ) (g : G) :
    rightTranslation g f ∈ indSpace H σ := by
  obtain ⟨h₁, K, hK, hfK⟩ := hf
  refine ⟨fun h x => ?_, K.comap (MulAut.conj g⁻¹).toMonoidHom, ?_, fun k hk x => ?_⟩
  · show f ((h : G) * x * g) = σ h (f (x * g))
    rw [mul_assoc, h₁]
  · rw [Subgroup.coe_comap]
    have : ⇑(MulAut.conj g⁻¹).toMonoidHom = fun x : G => g⁻¹ * x * g⁻¹⁻¹ := by
      ext x
      simp
    rw [this]
    exact hK.preimage (by fun_prop)
  · have := hfK _ hk (x * g)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
    simp only [rightTranslation_apply]
    rw [← this]
    congr 1
    group


def indRep : Representation ℂ G (indSpace H σ) :=
  (rightTranslation (W := W)).subrepresentation (indSpace H σ) fun g f hf =>
    rightTranslation_mem_indSpace (H := H) (σ := σ) (f := f) hf g

@[simp]
theorem coe_indRep_apply (g : G) (f : indSpace H σ) (x : G) :
    (indRep H σ g f : G → W) x = (f : G → W) (x * g) := rfl

theorem isSmooth_indRep : IsSmooth (indRep H σ) := by
  intro f
  obtain ⟨-, K, hK, hfK⟩ := f.2
  refine Subgroup.isOpen_mono (fun k hk => ?_) hK
  rw [mem_stabilizerOf]
  exact Subtype.ext (funext fun x => hfK k hk x)

section Frobenius

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)

def evalOne : indSpace H σ →ₗ[ℂ] W :=
  LinearMap.proj (R := ℂ) (φ := fun _ : G => W) 1 ∘ₗ (indSpace H σ).subtype

omit [IsTopologicalGroup G] in
@[simp]
theorem evalOne_apply (f : indSpace H σ) : evalOne H σ f = (f : G → W) 1 := rfl

theorem evalOne_indRep (h : H) (f : indSpace H σ) :
    evalOne H σ (indRep H σ h f) = σ h (evalOne H σ f) := by
  simpa using f.2.1 h 1

def frobeniusFun (Φ : Representation.IntertwiningMap π (indRep H σ)) :
    Representation.IntertwiningMap (π.comp H.subtype) σ where
  toLinearMap := evalOne H σ ∘ₗ Φ.toLinearMap
  isIntertwining' h := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
      Subgroup.coe_subtype, Representation.IntertwiningMap.toLinearMap_apply]
    rw [Representation.IntertwiningMap.isIntertwining _ _ Φ, evalOne_indRep]

variable {π}

def frobeniusInv (hπ : IsSmooth π) (φ : Representation.IntertwiningMap (π.comp H.subtype) σ) :
    Representation.IntertwiningMap π (indRep H σ) where
  toFun v := ⟨fun g => φ (π g v), fun h g => by
      simp only [map_mul, Module.End.mul_apply]
      exact Representation.IntertwiningMap.isIntertwining _ _ φ h (π g v),
    stabilizerOf π v, hπ v, fun k hk g => by
      simp [map_mul, Module.End.mul_apply, mem_stabilizerOf.1 hk]⟩
  map_add' v w := Subtype.ext (funext fun g => by simp)
  map_smul' c v := Subtype.ext (funext fun g => by simp)
  isIntertwining' g := LinearMap.ext fun v => Subtype.ext (funext fun x => by
    simp [map_mul, Module.End.mul_apply])

@[simp]
theorem frobeniusInv_apply (hπ : IsSmooth π)
    (φ : Representation.IntertwiningMap (π.comp H.subtype) σ) (v : V) (g : G) :
    (frobeniusInv H σ hπ φ v : G → W) g = φ (π g v) := rfl

def frobenius (hπ : IsSmooth π) :
    Representation.IntertwiningMap π (indRep H σ) ≃ₗ[ℂ]
      Representation.IntertwiningMap (π.comp H.subtype) σ where
  toFun := frobeniusFun H σ π
  map_add' Φ Ψ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => by
    simp [frobeniusFun])
  map_smul' c Φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => by
    simp [frobeniusFun])
  invFun := frobeniusInv H σ hπ
  left_inv Φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v =>
    Subtype.ext (funext fun x => by
      simp only [Representation.IntertwiningMap.toLinearMap_apply, frobeniusInv_apply]
      show (evalOne H σ) (Φ (π x v)) = _
      rw [Representation.IntertwiningMap.isIntertwining _ _ Φ, evalOne_apply, coe_indRep_apply, one_mul]))
  right_inv φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => by
    show (evalOne H σ) (frobeniusInv H σ hπ φ v) = φ v
    simp)

end Frobenius

end Induced

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.QuotientRightRegular
section
open MeasureTheory Topology Filter Set
open scoped ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

theorem compMeasurePreserving_congr {α : Type*} [MeasurableSpace α] {ν : Measure α} {p : ℝ≥0∞}
    {f f' : α → α} (h : f = f') (hf : MeasurePreserving f ν ν) (hf' : MeasurePreserving f' ν ν)
    (φ : Lp ℂ p ν) :
    Lp.compMeasurePreserving f hf φ = Lp.compMeasurePreserving f' hf' φ := by
  subst h
  rfl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
  [μ.IsMulRightInvariant]

def rightTranslate (g : G) :
    Lp ℂ 2 (quotientMeasure Γ μ) ≃ₗᵢ[ℂ] Lp ℂ 2 (quotientMeasure Γ μ) where
  toLinearEquiv :=
    { Lp.compMeasurePreservingₗ ℂ (rightMul Γ g) (measurePreserving_rightMul μ g) with
      invFun := Lp.compMeasurePreservingₗ ℂ (rightMul Γ g⁻¹) (measurePreserving_rightMul μ g⁻¹)
      left_inv := fun φ ↦ by
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ) = φ
        rw [← Lp.compMeasurePreserving_comp_apply, compMeasurePreserving_congr _ _
          (MeasurePreserving.id _), Lp.compMeasurePreserving_id_apply]
        rw [← rightMul_mul, inv_mul_cancel, rightMul_one]
      right_inv := fun φ ↦ by
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ) = φ
        rw [← Lp.compMeasurePreserving_comp_apply, compMeasurePreserving_congr _ _
          (MeasurePreserving.id _), Lp.compMeasurePreserving_id_apply]
        rw [← rightMul_mul, mul_inv_cancel, rightMul_one] }
  norm_map' φ := Lp.norm_compMeasurePreserving φ _

theorem coeFn_rightTranslate (g : G) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    rightTranslate Γ μ g φ =ᵐ[quotientMeasure Γ μ] fun x ↦ φ (rightMul Γ g x) :=
  Lp.coeFn_compMeasurePreserving φ _

def rightRegular : G →* (Lp ℂ 2 (quotientMeasure Γ μ) ≃ₗᵢ[ℂ] Lp ℂ 2 (quotientMeasure Γ μ)) where
  toFun := rightTranslate Γ μ
  map_one' := by
    ext1 φ
    change Lp.compMeasurePreserving _ _ φ = φ
    rw [compMeasurePreserving_congr (rightMul_one Γ) _ (MeasurePreserving.id _),
      Lp.compMeasurePreserving_id_apply]
  map_mul' g h := by
    ext1 φ
    rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
    change Lp.compMeasurePreserving _ _ φ =
      Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ φ)
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact compMeasurePreserving_congr (rightMul_mul Γ g h) _ _ φ

section Continuity

variable [IsFiniteMeasureOnCompacts μ]


omit [μ.IsMulRightInvariant] in
theorem tendsto_lintegral_rightMul_sub {ψ : RightCosetSpace Γ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (g₀ : G) :
    Tendsto (fun g ↦ ∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
      ∂quotientMeasure Γ μ) (𝓝 g₀) (𝓝 0) := by
  obtain ⟨N, hN, hNn⟩ := exists_compact_mem_nhds g₀
  set K : Set (RightCosetSpace Γ) :=
    (fun p : RightCosetSpace Γ × G ↦ rightMul Γ p.2⁻¹ p.1) '' (tsupport ψ ×ˢ N) with hKdef
  have hK : IsCompact K := (hs.prod hN).image
    ((continuous_rightMul_prod Γ).comp (continuous_fst.prodMk continuous_snd.inv))
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  have hzero : ∀ g ∈ N, ∀ x ∉ K, ψ (rightMul Γ g x) = 0 := by
    intro g hg x hx
    by_contra h
    refine hx ⟨(rightMul Γ g x, g), ⟨subset_tsupport ψ h, hg⟩, ?_⟩
    change rightMul Γ g⁻¹ (rightMul Γ g x) = x
    rw [rightMul_rightMul, mul_inv_cancel, rightMul_one, id]
  have hg₀N : g₀ ∈ N := mem_of_mem_nhds hNn
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * M) ^ (2 : ℝ) with hc_def
  have hmeas : ∀ g, Measurable fun x ↦ ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ) :=
    fun g ↦ (((hc.comp (continuous_rightMul Γ g)).sub
      (hc.comp (continuous_rightMul Γ g₀))).measurable.enorm).pow_const _
  suffices key : Tendsto (fun g ↦ ∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
      ∂quotientMeasure Γ μ) (𝓝 g₀) (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂quotientMeasure Γ μ)) by
    rwa [lintegral_zero] at key
  refine tendsto_lintegral_filter_of_dominated_convergence (K.indicator fun _ ↦ c)
    (Eventually.of_forall hmeas) ?_ ?_ ?_
  · filter_upwards [hNn] with g hg
    refine Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖
          ≤ ‖ψ (rightMul Γ g x)‖ + ‖ψ (rightMul Γ g₀ x)‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith [hM (rightMul Γ g x), hM (rightMul Γ g₀ x)]
    · rw [hzero g hg x hx, hzero g₀ hg₀N x hx, sub_self, enorm_zero,
        ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
  · rw [lintegral_indicator_const hK.measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hK.measure_lt_top.ne
  · refine Eventually.of_forall fun x ↦ ?_
    have hcont : Continuous fun g ↦ ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ) :=
      (ENNReal.continuous_rpow_const).comp (continuous_enorm.comp
        ((hc.comp ((continuous_rightMul_prod Γ).comp
          (continuous_const.prodMk continuous_id))).sub continuous_const))
    have := hcont.tendsto g₀
    rwa [sub_self, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at this

theorem tendsto_rightRegular_of_continuous {ψ : RightCosetSpace Γ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (g₀ : G) :
    Tendsto (fun g ↦ rightRegular Γ μ g ((hc.memLp_of_hasCompactSupport hs).toLp ψ)) (𝓝 g₀)
      (𝓝 (rightRegular Γ μ g₀ ((hc.memLp_of_hasCompactSupport hs).toLp ψ))) := by
  have hψ : MemLp ψ 2 (quotientMeasure Γ μ) := hc.memLp_of_hasCompactSupport hs
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hae : ∀ g, ⇑(rightRegular Γ μ g (hψ.toLp ψ)) =ᵐ[quotientMeasure Γ μ]
      fun x ↦ ψ (rightMul Γ g x) := fun g ↦
    (coeFn_rightTranslate Γ μ g _).trans
      ((measurePreserving_rightMul μ g).quasiMeasurePreserving.ae_eq_comp hψ.coeFn_toLp)
  have heq : ∀ g, eLpNorm (⇑(rightRegular Γ μ g (hψ.toLp ψ)) - ⇑(rightRegular Γ μ g₀ (hψ.toLp ψ)))
      2 (quotientMeasure Γ μ) = (∫⁻ x, ‖ψ (rightMul Γ g x) - ψ (rightMul Γ g₀ x)‖ₑ ^ (2 : ℝ)
        ∂quotientMeasure Γ μ) ^ (1 / (2 : ℝ)) := fun g ↦ by
    rw [eLpNorm_congr_ae ((hae g).sub (hae g₀))]
    exact eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (((hc.comp (continuous_rightMul Γ g)).sub
        (hc.comp (continuous_rightMul Γ g₀))).measurable.aestronglyMeasurable)
  simp_rw [heq]
  have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp
    (tendsto_lintegral_rightMul_sub Γ μ hc hs g₀)
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this

theorem continuous_rightRegular_apply (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    Continuous fun g ↦ rightRegular Γ μ g φ := by
  refine continuous_iff_continuousAt.2 fun g₀ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨ψ, hs, hψφ, hc, hmem⟩ := (Lp.memLp φ).exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (ε := ENNReal.ofReal (ε / 4)) (by simpa using hε4)
  set φ₀ : Lp ℂ 2 (quotientMeasure Γ μ) := (hc.memLp_of_hasCompactSupport hs).toLp ψ
  have hd : dist φ φ₀ ≤ ε / 4 := by
    rw [Lp.dist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub (MemLp.coeFn_toLp _))]
    exact ENNReal.toReal_le_of_le_ofReal hε4.le hψφ
  filter_upwards [Metric.tendsto_nhds.1 (tendsto_rightRegular_of_continuous Γ μ hc hs g₀) (ε / 4)
    hε4] with g hg
  calc dist (rightRegular Γ μ g φ) (rightRegular Γ μ g₀ φ)
      ≤ dist (rightRegular Γ μ g φ) (rightRegular Γ μ g φ₀) +
          (dist (rightRegular Γ μ g φ₀) (rightRegular Γ μ g₀ φ₀) +
            dist (rightRegular Γ μ g₀ φ₀) (rightRegular Γ μ g₀ φ)) :=
        (dist_triangle _ _ _).trans (add_le_add le_rfl (dist_triangle _ _ _))
    _ = dist φ φ₀ + (dist (rightRegular Γ μ g φ₀) (rightRegular Γ μ g₀ φ₀) + dist φ₀ φ) := by
        rw [LinearIsometryEquiv.dist_map, LinearIsometryEquiv.dist_map]
    _ < ε := by
        rw [dist_comm φ₀ φ]
        linarith

end Continuity

end RightCosetSpace

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.TraceNormComp
section
namespace GroundTheory.Automorphic

open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem eq_zero_of_hsNormSq_eq_zero {T : H →L[ℂ] H} (h : hsNormSq T = 0) : T = 0 := by
  ext x
  have hx := enorm_apply_sq_le T x
  rw [h, zero_mul, nonpos_iff_eq_zero, pow_eq_zero_iff two_ne_zero, enorm_eq_zero] at hx
  simpa using hx

theorem eq_zero_of_hsNorm_eq_zero {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (h : hsNorm T = 0) :
    T = 0 := by
  refine eq_zero_of_hsNormSq_eq_zero ?_
  rw [hsNorm, Real.sqrt_eq_zero ENNReal.toReal_nonneg, ENNReal.toReal_eq_zero_iff] at h
  exact h.resolve_right hT.ne

theorem traceNorm_comp_le {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : (traceNorm (A.comp B)).toReal ≤ hsNorm A * hsNorm B := by
  have key : ∀ t : ℝ, 0 < t → 2 * (traceNorm (A.comp B)).toReal ≤
      t ^ 2 * hsNorm A ^ 2 + (t⁻¹) ^ 2 * hsNorm B ^ 2 := by
    intro t ht
    have hAB : A.comp B = ((t : ℂ) • A).comp (((t⁻¹ : ℝ) : ℂ) • B) := by
      ext x
      simp only [comp_apply, smul_apply, map_smul, smul_smul]
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_smul]
    have h := two_mul_traceNorm_comp_le ((t : ℂ) • A) (((t⁻¹ : ℝ) : ℂ) • B)
    rw [← hAB, hsNormSq_smul, hsNormSq_smul] at h
    have hfin : ‖(t : ℂ)‖ₑ ^ 2 * hsNormSq A + ‖((t⁻¹ : ℝ) : ℂ)‖ₑ ^ 2 * hsNormSq B ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hA.ne, ENNReal.mul_ne_top (by simp) hB.ne⟩
    have h' := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) hA.ne)
      (ENNReal.mul_ne_top (by simp) hB.ne), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_pow, toReal_enorm, toReal_enorm, ← hsNorm_sq,
      ← hsNorm_sq, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos ht, abs_of_pos (inv_pos.2 ht)] at h'
    simpa using h'
  rcases (hsNorm_nonneg A).eq_or_lt with ha | ha
  · rw [eq_zero_of_hsNorm_eq_zero hA ha.symm, zero_comp, traceNorm_zero, ENNReal.toReal_zero]
    exact mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)
  rcases (hsNorm_nonneg B).eq_or_lt with hb | hb
  · rw [eq_zero_of_hsNorm_eq_zero hB hb.symm, comp_zero, traceNorm_zero, ENNReal.toReal_zero]
    exact mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)
  have h := key (Real.sqrt (hsNorm B / hsNorm A)) (Real.sqrt_pos.2 (div_pos hb ha))
  rw [inv_pow, Real.sq_sqrt (div_nonneg hb.le ha.le)] at h
  have e : hsNorm B / hsNorm A * hsNorm A ^ 2 + (hsNorm B / hsNorm A)⁻¹ * hsNorm B ^ 2 =
      2 * (hsNorm A * hsNorm B) := by
    field_simp
    ring
  linarith

end

end GroundTheory.Automorphic
end

