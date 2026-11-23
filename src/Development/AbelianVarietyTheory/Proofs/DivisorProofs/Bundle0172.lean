module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalIntegralComm
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.SchwartzIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weightedDeriv (k m : ℕ) (f : 𝓢(E, ℂ)) : E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x)
    ((continuous_norm.pow k).smul ((f.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k m f) (fun x => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact f.le_seminorm ℂ k m x)

theorem weightedDeriv_apply (k m : ℕ) (f : 𝓢(E, ℂ)) (x : E) :
    weightedDeriv k m f x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x := rfl

theorem norm_weightedDeriv_le (k m : ℕ) (f : 𝓢(E, ℂ)) :
    ‖weightedDeriv k m f‖ ≤ SchwartzMap.seminorm ℂ k m f :=
  (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr fun x => by
    rw [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact f.le_seminorm ℂ k m x

theorem seminorm_le_norm_weightedDeriv (k m : ℕ) (f : 𝓢(E, ℂ)) :
    SchwartzMap.seminorm ℂ k m f ≤ ‖weightedDeriv k m f‖ :=
  SchwartzMap.seminorm_le_bound ℂ k m f (norm_nonneg _) fun x => by
    have h := (weightedDeriv k m f).norm_coe_le_norm x
    rwa [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h

def weightedDerivCLM (k m : ℕ) :
    𝓢(E, ℂ) →L[ℂ] (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (weightedDeriv k m)
    (fun f g => by
      ext x : 1
      simp only [weightedDeriv_apply, add_apply, FunLike.coe_add]
      rw [iteratedFDeriv_add_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
        ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt, smul_add])
    (fun a f => by
      ext x : 1
      simp only [weightedDeriv_apply, FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [iteratedFDeriv_const_smul_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt,
        smul_comm])
    ⟨{(k, m)}, 1, zero_le_one, fun f => by
      simpa [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] using norm_weightedDeriv_le k m f⟩

theorem weightedDerivCLM_apply (k m : ℕ) (f : 𝓢(E, ℂ)) : weightedDerivCLM k m f = weightedDeriv k m f := rfl

section Param

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] {ν : Measure W}

theorem continuous_iteratedFDeriv_param {G : W → 𝓢(E, ℂ)} (hG : Continuous G) (m : ℕ) (y : E) :
    Continuous fun w => iteratedFDeriv ℝ m (G w) y := by
  have h := ((BoundedContinuousFunction.evalCLM ℂ y).comp (weightedDerivCLM (E := E) 0 m)).continuous.comp hG
  refine h.congr fun w => ?_
  simp [weightedDerivCLM_apply, weightedDeriv_apply]

theorem integrable_iteratedFDeriv_param {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) (m : ℕ) (y : E) :
    Integrable (fun w => iteratedFDeriv ℝ m (G w) y) ν :=
  (hint 0 m).mono' (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable
    (.of_forall fun w => (G w).norm_iteratedFDeriv_le_seminorm ℂ m y)

theorem iteratedFDeriv_eq_integral {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) {g : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = ∫ w, G w x ∂ν) (m : ℕ) :
    iteratedFDeriv ℝ m g = fun x => ∫ w, iteratedFDeriv ℝ m (G w) x ∂ν := by
  induction m with
  | zero =>
    funext x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, hg x]
    exact ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toLinearIsometry.integral_comp_comm _).symm
  | succ m ih =>
    funext x
    set Ψ := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℂ
    have key : ∀ (f : E → ℂ) (y : E), iteratedFDeriv ℝ (m + 1) f y = Ψ.symm (fderiv ℝ (iteratedFDeriv ℝ m f) y) := by
      intro f y
      rw [iteratedFDeriv_succ_eq_comp_left]
      rfl
    have hdiff : ∀ w, Differentiable ℝ (iteratedFDeriv ℝ m (G w)) := fun w =>
      ((G w).smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top m)
    have hF' : ∀ w y, fderiv ℝ (iteratedFDeriv ℝ m (G w)) y = Ψ (iteratedFDeriv ℝ (m + 1) (G w) y) := by
      intro w y
      rw [key, LinearIsometryEquiv.apply_symm_apply]
    have hd : HasFDerivAt (fun y => ∫ w, iteratedFDeriv ℝ m (G w) y ∂ν)
        (∫ w, fderiv ℝ (iteratedFDeriv ℝ m (G w)) x ∂ν) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun w => SchwartzMap.seminorm ℂ 0 (m + 1) (G w))
        Filter.univ_mem (.of_forall fun y => (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable)
        (integrable_iteratedFDeriv_param hG hint m x) ?_ (.of_forall fun w y _ => ?_) (hint 0 (m + 1))
        (.of_forall fun w y _ => (hdiff w y).hasFDerivAt)
      · simp_rw [hF']
        exact (Ψ.continuous.comp (continuous_iteratedFDeriv_param hG (m + 1) x)).aestronglyMeasurable
      · rw [norm_fderiv_iteratedFDeriv]
        exact (G w).norm_iteratedFDeriv_le_seminorm ℂ (m + 1) y
    rw [key, ih, hd.fderiv]
    have := Ψ.symm.toLinearIsometry.integral_comp_comm (μ := ν) (fun w => fderiv ℝ (iteratedFDeriv ℝ m (G w)) x)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at this
    rw [← this]
    simp_rw [hF', LinearIsometryEquiv.symm_apply_apply]

abbrev Target (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset (ℕ × ℕ)) : Type :=
  (i : s) → (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ)

def embed (s : Finset (ℕ × ℕ)) : 𝓢(E, ℂ) →L[ℂ] Target E s :=
  ContinuousLinearMap.pi fun i => weightedDerivCLM i.1.1 i.1.2

theorem embed_apply (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) (i : s) : embed s f i = weightedDeriv i.1.1 i.1.2 f := rfl

theorem norm_embed_le (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) :
    ‖embed s f‖ ≤ ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 f :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => apply_nonneg _ _)).mpr fun i =>
    (norm_weightedDeriv_le _ _ f).trans
      (Finset.single_le_sum (f := fun j : ℕ × ℕ => SchwartzMap.seminorm ℂ j.1 j.2 f)
        (fun j _ => apply_nonneg _ _) i.2)

theorem seminorm_le_norm_embed (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) {i : ℕ × ℕ} (hi : i ∈ s) :
    SchwartzMap.seminorm ℂ i.1 i.2 f ≤ ‖embed s f‖ :=
  (seminorm_le_norm_weightedDeriv _ _ f).trans (norm_le_pi_norm (embed s f) ⟨i, hi⟩)

theorem clm_apply_eq_integral (L : 𝓢(E, ℂ) →L[ℂ] ℂ) {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) {g : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = ∫ w, G w x ∂ν) : L g = ∫ w, L (G w) ∂ν := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp (L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ)) (continuous_norm.comp L.continuous)
  have hL : ∀ f, ‖L f‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) f := fun f => hC f
  set t := insert ((0 : ℕ), (0 : ℕ)) s
  have hLt : ∀ f, ‖L f‖ ≤ C * ‖embed t f‖ := fun f => (hL f).trans (mul_le_mul_of_nonneg_left
    (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi =>
      seminorm_le_norm_embed t f (Finset.mem_insert_of_mem hi)) C.2)
  have hinj : Function.Injective (embed (E := E) t) := by
    refine (injective_iff_map_eq_zero (embed (E := E) t)).mpr fun f hf => ?_
    ext x
    have h1 := seminorm_le_norm_embed t f (Finset.mem_insert_self _ _)
    rw [hf, norm_zero] at h1
    have h2 := (f.norm_le_seminorm ℂ x).trans h1
    simpa using h2
  let Φ : 𝓢(E, ℂ) →ₗ[ℂ] Target E t := (embed (E := E) t : 𝓢(E, ℂ) →ₗ[ℂ] Target E t)
  let e := LinearEquiv.ofInjective Φ hinj
  have he : ∀ y : LinearMap.range Φ, embed t (e.symm y) = y := fun y => by
    have := congrArg Subtype.val (e.apply_symm_apply y)
    exact (LinearEquiv.ofInjective_apply Φ (e.symm y)).symm.trans this
  let f0 : LinearMap.range Φ →ₗ[ℂ] ℂ := (L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ).comp e.symm.toLinearMap
  let f1 : StrongDual ℂ (LinearMap.range Φ) := f0.mkContinuous C fun y => by
    show ‖L (e.symm y)‖ ≤ C * ‖(y : Target E t)‖
    rw [← he]
    exact hLt _
  obtain ⟨ℓ, hℓ, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) f1
  have hLℓ : ∀ f, L f = ℓ (embed t f) := by
    intro f
    have h1 := hℓ ⟨embed t f, LinearMap.mem_range_self Φ f⟩
    have h2 : e.symm ⟨embed t f, LinearMap.mem_range_self Φ f⟩ = f := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    have h3 : ℓ (embed t f) = f1 ⟨embed t f, LinearMap.mem_range_self Φ f⟩ := h1
    rw [h3, LinearMap.mkContinuous_apply]
    show L f = L (e.symm _)
    rw [h2]
  have hcont : Continuous fun w => embed t (G w) := (embed t).continuous.comp hG
  haveI : SecondCountableTopology W := inferInstance
  haveI : SecondCountableTopologyEither W (Target E t) := secondCountableTopologyEither_of_left _ _
  have hInt : Integrable (fun w => embed t (G w)) ν :=
    (MeasureTheory.integrable_finsetSum t fun i _ => hint i.1 i.2).mono' hcont.aestronglyMeasurable
      (.of_forall fun w => norm_embed_le t (G w))
  have hemb : embed t g = ∫ w, embed t (G w) ∂ν := by
    funext i
    refine BoundedContinuousFunction.ext fun x => ?_
    have h1 := ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun i : t => E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ) i)).integral_comp_comm hInt
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      BoundedContinuousFunction.evalCLM_apply] at h1
    rw [← h1]
    simp only [embed_apply, weightedDeriv_apply]
    rw [integral_smul, iteratedFDeriv_eq_integral hG hint hg]
  rw [hLℓ g, hemb, ← ℓ.integral_comp_comm hInt]
  simp_rw [← hLℓ]

end Param

theorem clm_integral_interchange : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (ν : Measure W) [SigmaFinite ν] (n : ℕ) (L : Sch (Fin n) →L[ℂ] ℂ)
    (G : W → Sch (Fin n)) (c : W → ℂ) (g : Sch (Fin n)), Continuous G → Continuous c →
    (∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) ν) →
    (∀ x, g x = ∫ w, c w * G w x ∂ν) → L g = ∫ w, c w * L (G w) ∂ν := by
  intro W _ _ _ _ _ ν _ n L G c g hG hc hint hg
  have hG' : Continuous fun w => c w • G w := hc.smul hG
  have hint' : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (c w • G w)) ν := by
    intro k m
    simpa only [map_smul_eq_mul] using hint k m
  have hg' : ∀ x, g x = ∫ w, (c w • G w) x ∂ν := by
    intro x
    rw [hg x]
    rfl
  rw [clm_apply_eq_integral L hG' hint' hg']
  simp only [map_smul, smul_eq_mul]

end GlobalTheory.SchwartzIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormLinearPhaseSecondOrderLe
section
open scoped SchwartzMap

namespace GlobalTheory.LinearPhase

open Complex GlobalTheory.CharFormDeriv

theorem seminorm_phase_sub_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f) ≤ C * t ^ 2 := by
  intro V _ _ L c f k n
  set L' : V →L[ℝ] ℝ := (-(2 * Real.pi)) • L with hL'
  have hL'x : ∀ x, ((L' x : ℝ) : ℂ) = -(2 * Real.pi) * (L x : ℂ) := fun x => by
    simp [hL']
  set K := 3 * 2 ^ n * (1 + ‖L'‖) ^ (n + 2) *
      (2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)
      with hK
  have hgt : Function.HasTemperateGrowth (fun x : V => ((L x : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp L).hasTemperateGrowth
  set g : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f with hgdef
  have hg : ∀ x, g x = (L x : ℂ) * f x := fun x => by
    rw [hgdef, SchwartzMap.smulLeftCLM_apply_apply hgt, smul_eq_mul]
  refine ⟨K + 2 * |2 * Real.pi * c| *
    (SchwartzMap.seminorm ℂ k n f + 2 * Real.pi * SchwartzMap.seminorm ℂ k n g), fun t ht1 => ?_⟩
  set a : ℂ := Complex.exp (((-(2 * Real.pi * c * t ^ 2) : ℝ) : ℂ) * I) with ha
  have hfun : (fun x : V => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
      = fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ)) := by
    funext x
    rw [ha, ← Complex.exp_add, hL'x]
    congr 1
    push_cast
    ring
  have het : Function.HasTemperateGrowth fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ)) :=
    (Function.HasTemperateGrowth.const a).mul (hasTemperateGrowth_char L' t)
  rw [hfun]
  set A : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x : V => Complex.exp ((I * t) * (L' x : ℂ))) f with hAdef
  have hA : ∀ x, A x = Complex.exp ((I * t) * (L' x : ℂ)) * f x := fun x => by
    rw [hAdef, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_char L' t), smul_eq_mul]
  set E : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ))) f with hEdef
  have hE : ∀ x, E x = a * Complex.exp ((I * t) * (L' x : ℂ)) * f x := fun x => by
    rw [hEdef, SchwartzMap.smulLeftCLM_apply_apply het, smul_eq_mul]
  rcases eq_or_ne t 0 with ht0 | ht0
  · have h0 : E - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • g = 0 := by
      ext x
      simp only [SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hE, ha, ht0]
      simp
    rw [h0, map_zero, ht0]
    simp
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  set u : 𝓢(V, ℂ) := (t : ℂ)⁻¹ • (A - f) + (2 * Real.pi * I : ℂ) • g with hudef
  have hu : ∀ x, u x = rem t (L' x) * f x := fun x => by
    simp only [hudef, SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hA, hg,
      rem, smul_eq_mul, hL'x]
    ring
  have hub : SchwartzMap.seminorm ℂ k n u ≤ |t| * K := seminorm_rem_mul_le L' f u ht0 ht1 hu k n
  have hid : E - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • g
      = (a * t) • u + ((a - 1) • f + (-((a - 1) * t * (2 * Real.pi * I))) • g) := by
    ext x
    simp only [hudef, SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hA, hE,
      smul_eq_mul]
    field_simp
    ring
  have hna : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hna1 : ‖a - 1‖ ≤ 2 * |2 * Real.pi * c| * t ^ 2 := by
    refine (norm_cexp_mul_I_sub_one_le _).trans (le_of_eq ?_)
    rw [abs_neg, abs_mul (2 * Real.pi * c), abs_of_nonneg (sq_nonneg t)]
    ring
  have hpf := apply_nonneg (SchwartzMap.seminorm ℂ k n) f
  have hpg := apply_nonneg (SchwartzMap.seminorm ℂ k n) g
  have hpi := Real.pi_pos
  have hn1 : ‖a * t‖ = |t| := by rw [norm_mul, hna, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖-((a - 1) * t * (2 * Real.pi * I))‖ ≤ 2 * |2 * Real.pi * c| * t ^ 2 * (2 * Real.pi) := by
    have h2 : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos hpi]
    rw [norm_neg, norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_eq_abs]
    calc ‖a - 1‖ * |t| * (2 * Real.pi) ≤ (2 * |2 * Real.pi * c| * t ^ 2) * 1 * (2 * Real.pi) := by
          gcongr
      _ = _ := by ring
  rw [hid]
  calc SchwartzMap.seminorm ℂ k n ((a * t) • u + ((a - 1) • f + (-((a - 1) * t * (2 * Real.pi * I))) • g))
      ≤ SchwartzMap.seminorm ℂ k n ((a * t) • u) + (SchwartzMap.seminorm ℂ k n ((a - 1) • f) +
          SchwartzMap.seminorm ℂ k n ((-((a - 1) * t * (2 * Real.pi * I))) • g)) :=
        (map_add_le_add _ _ _).trans (by gcongr; exact map_add_le_add _ _ _)
    _ = |t| * SchwartzMap.seminorm ℂ k n u + (‖a - 1‖ * SchwartzMap.seminorm ℂ k n f +
          ‖-((a - 1) * t * (2 * Real.pi * I))‖ * SchwartzMap.seminorm ℂ k n g) := by
        rw [map_smul_eq_mul, map_smul_eq_mul, map_smul_eq_mul, hn1]
    _ ≤ |t| * (|t| * K) + (2 * |2 * Real.pi * c| * t ^ 2 * SchwartzMap.seminorm ℂ k n f +
          2 * |2 * Real.pi * c| * t ^ 2 * (2 * Real.pi) * SchwartzMap.seminorm ℂ k n g) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← sq, sq_abs]; ring

end GlobalTheory.LinearPhase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslateTaylorSecondOrder
section
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

namespace GlobalTheory.SchwartzTranslateUnif

open GlobalTheory.SchwartzTranslate

theorem seminorm_lineDerivOp_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V)
    (g : 𝓢(V, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a g)
      ≤ ‖a‖ * SchwartzMap.seminorm ℂ k (n + 1) g := by
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have e : ⇑(LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a g) = fun y => fderiv ℝ g y a := by
    funext y; rw [LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [e]
  have h1 : ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x‖
      ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) g x‖ := by
    rw [← norm_iteratedFDeriv_fderiv]
    exact norm_iteratedFDeriv_clm_apply_const
      (g.smooth'.fderiv_right (m := ∞) le_rfl).contDiffAt
      (by exact_mod_cast le_top)
  have h2 := SchwartzMap.le_seminorm ℂ k (n + 1) g x
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x‖
      ≤ ‖x‖ ^ k * (‖a‖ * ‖iteratedFDeriv ℝ (n + 1) g x‖) := by gcongr
    _ = ‖a‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) g x‖) := by ring
    _ ≤ _ := by gcongr

theorem seminorm_translate_sub_le_explicit {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : V) (f : 𝓢(V, ℂ)) (k n : ℕ) (t : ℝ) (ht : |t| ≤ 1) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f
        - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f)
      ≤ 2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k n
            (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f))
          + ‖a‖ ^ k * SchwartzMap.seminorm ℂ 0 n
            (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f)))
        * t ^ 2 := by
  set f1 : 𝓢(V, ℂ) := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hf1
  set f2 : 𝓢(V, ℂ) := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f1 with hf2
  have e1 : (fun y => fderiv ℝ f y a) = f1 := by
    funext y; rw [hf1, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have e2 : (fun y => fderiv ℝ f1 y a) = f2 := by
    funext y; rw [hf2, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have hn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have c1 : ContDiff ℝ ∞ f1 := f1.smooth'
  have ct : ContDiff ℝ ∞ (fun z => f (z + t • a)) := c0.comp (contDiff_id.add contDiff_const)
  have efun : ⇑(SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • f1)
      = (fun z => f (z + t • a)) - ⇑f - t • ⇑f1 := by
    funext z
    simp
  have eit : iteratedFDeriv ℝ n
      ⇑(SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • f1) x
      = iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x
        - t • iteratedFDeriv ℝ n f1 x := by
    rw [efun, iteratedFDeriv_sub_apply (f := (fun z => f (z + t • a)) - ⇑f) (g := t • ⇑f1)
      ((ct.sub c0).of_le hn).contDiffAt
      ((c1.const_smul t).of_le hn).contDiffAt,
      iteratedFDeriv_sub_apply (ct.of_le hn).contDiffAt (c0.of_le hn).contDiffAt,
      iteratedFDeriv_const_smul_apply (c1.of_le hn).contDiffAt, iteratedFDeriv_comp_add_right]
  have key := taylor_two (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f (x + s • a))
    (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f1 (x + s • a))
    (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f2 (x + s • a))
    (fun s => by
      have := hasDerivAt_iteratedFDeriv_line a n f c0 x s
      rw [e1] at this
      exact this.const_smul (‖x‖ ^ k))
    (fun s => by
      have := hasDerivAt_iteratedFDeriv_line a n f1 c1 x s
      rw [e2] at this
      exact this.const_smul (‖x‖ ^ k))
    (2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k n f2 + ‖a‖ ^ k * SchwartzMap.seminorm ℂ 0 n f2))
    (fun s hs => by
      have hx : ‖x‖ ≤ ‖x + s • a‖ + ‖a‖ := by
        have h3 : ‖s • a‖ ≤ ‖a‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) hs
        have h4 := norm_sub_le (x + s • a) (s • a)
        rw [add_sub_cancel_right] at h4
        linarith
      have hp : ‖x‖ ^ k ≤ 2 ^ (k - 1) * (‖x + s • a‖ ^ k + ‖a‖ ^ k) :=
        (pow_le_pow_left₀ (norm_nonneg _) hx k).trans
          (add_pow_le (norm_nonneg _) (norm_nonneg _) k)
      have b1 := SchwartzMap.le_seminorm ℂ k n f2 (x + s • a)
      have b2 := SchwartzMap.le_seminorm ℂ 0 n f2 (x + s • a)
      rw [pow_zero, one_mul] at b2
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc _ ≤ 2 ^ (k - 1) * (‖x + s • a‖ ^ k + ‖a‖ ^ k)
              * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖ := by gcongr
        _ = 2 ^ (k - 1) * (‖x + s • a‖ ^ k * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖
              + ‖a‖ ^ k * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖) := by ring
        _ ≤ _ := by gcongr) t ht
  simp only [zero_smul, add_zero] at key
  rw [smul_comm t, ← smul_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  rw [eit]
  exact key

theorem seminorm_translate_sub_lineDeriv_le {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : 𝓢(X, ℂ)) (k n : ℕ) : ∃ C : ℝ, ∀ a : X, ‖a‖ ≤ 1 →
      SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f
        - LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) ≤ C * ‖a‖ ^ 2 := by
  refine ⟨2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k (n + 2) f
    + SchwartzMap.seminorm ℂ 0 (n + 2) f), fun a ha => ?_⟩
  have h := seminorm_translate_sub_le_explicit a f k n 1 (by simp)
  simp only [one_smul, Complex.ofReal_one, one_pow, mul_one] at h
  refine h.trans ?_
  have hA : ∀ j, SchwartzMap.seminorm ℂ j n
      (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f))
      ≤ ‖a‖ ^ 2 * SchwartzMap.seminorm ℂ j (n + 2) f := by
    intro j
    calc _ ≤ ‖a‖ * SchwartzMap.seminorm ℂ j (n + 1) (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) :=
          seminorm_lineDerivOp_le a _ j n
      _ ≤ ‖a‖ * (‖a‖ * SchwartzMap.seminorm ℂ j (n + 1 + 1) f) := by
          gcongr; exact seminorm_lineDerivOp_le a f j (n + 1)
      _ = _ := by ring
  have hak : ‖a‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) ha
  have h0 := hA 0
  have hk := hA k
  have s0 : 0 ≤ SchwartzMap.seminorm ℂ 0 n
      (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f)) :=
    apply_nonneg _ _
  have hmul : ‖a‖ ^ k * SchwartzMap.seminorm ℂ 0 n
      (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f))
      ≤ ‖a‖ ^ 2 * SchwartzMap.seminorm ℂ 0 (n + 2) f :=
    (mul_le_of_le_one_left s0 hak).trans h0
  calc _ ≤ 2 ^ (k - 1) * (‖a‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f
          + ‖a‖ ^ 2 * SchwartzMap.seminorm ℂ 0 (n + 2) f) := by gcongr
    _ = _ := by ring

end GlobalTheory.SchwartzTranslateUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensionalOfBoundedFormsStatement
section
open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s) := by
  first | exact @GlobalTheory.span_finiteDimensional_of_bounded_forms | exact GlobalTheory.span_finiteDimensional_of_bounded_forms | (intros; apply GlobalTheory.span_finiteDimensional_of_bounded_forms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYonedaStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda : ∀ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ) (ι : Fin (k + 1) → (B →+* T)), (∀ j, (ι j).comp a = (ι 0).comp a) → (∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) → ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A))) (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))), ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) := by
  first | (exact @GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback) | (exact GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback) | (intros; apply GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementOfKernelExistsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 → ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) → (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) → (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) → ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  first | exact @GlobalTheory.stable_complement_of_kernel_exists | exact GlobalTheory.stable_complement_of_kernel_exists | (intros; apply GlobalTheory.stable_complement_of_kernel_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleFgOfLocallyLeFgStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem : ∀ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing R] (M : Submodule R A) (s : Set R), Ideal.span s = ⊤ → (∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) → M.FG := by
  first | exact @GlobalTheory.submodule_fg_of_locally_le_fg | exact GlobalTheory.submodule_fg_of_locally_le_fg | (intros; apply GlobalTheory.submodule_fg_of_locally_le_fg <;> assumption)
end

