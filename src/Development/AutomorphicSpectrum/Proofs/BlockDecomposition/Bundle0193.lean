module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupDisintegration
section
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar

theorem leftInvariant_of_section : ∀ {Γ K X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ] [LocallyCompactSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] (e : K →* Γ) (_ : Continuous e) [MeasurableSpace X] (ρ : Measure X) [SFinite ρ] (s : X → Γ) (_ : Measurable s) (_ : ρ ≠ 0) (_ : ∀ g : Γ, ∃ a : X → X, Measurable a ∧ Measure.map a ρ = ρ ∧ ∀ᵐ x ∂ρ, ∃ k, g * s x = s (a x) * e k) (_ : ∀ A : Set Γ, IsCompact A → ρ (s ⁻¹' (A * Set.range e)) < ⊤) (μ : Measure Γ) [μ.IsHaarMeasure], ∃ c : ℝ, 0 < c ∧ ∀ F : Γ → ℂ, Continuous F → HasCompactSupport F → (∀ y k, F (y * e k) = F y) → ∫ y, F y ∂μ = c * ∫ x, F (s x) ∂ρ := by
  intro Γ K X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he _ ρ _ s hs hρ hinv hfin μ _
  obtain ⟨m, hmH, hm1⟩ : ∃ m : Measure K, m.IsHaarMeasure ∧ m Set.univ = 1 := by
    refine ⟨Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K), inferInstance, ?_⟩
    have h := Measure.haarMeasure_self (G := K) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h
  haveI := hmH
  haveI : IsFiniteMeasure m := ⟨by rw [hm1]; exact ENNReal.one_lt_top⟩
  set φ : X × K → Γ := fun p => s p.1 * e p.2 with hφ_def
  have hφ : Measurable φ := (hs.comp measurable_fst).mul (he.measurable.comp measurable_snd)
  set ν : Measure Γ := Measure.map φ (ρ.prod m) with hν_def
  have key : ∀ (B : Set Γ) (y : Γ) (k : K),
      m ((fun k' => y * e k * e k') ⁻¹' B) = m ((fun k' => y * e k') ⁻¹' B) := by
    intro B y k
    have h : (fun k' => y * e k * e k') ⁻¹' B = (fun k' => k * k') ⁻¹' ((fun k' => y * e k') ⁻¹' B) := by
      ext k'; simp [map_mul, mul_assoc]
    rw [h, measure_preimage_mul]
  have hνapp : ∀ B : Set Γ, MeasurableSet B →
      ν B = ∫⁻ x, m ((fun k => s x * e k) ⁻¹' B) ∂ρ := by
    intro B hB
    rw [hν_def, Measure.map_apply hφ hB, Measure.prod_apply (hφ hB)]
    rfl
  have hmeasψ : ∀ B : Set Γ, MeasurableSet B →
      Measurable (fun x => m ((fun k => s x * e k) ⁻¹' B)) := by
    intro B hB
    exact measurable_measure_prodMk_left (hφ hB)
  haveI : ν.IsMulLeftInvariant := by
    constructor
    intro g
    ext B hB
    rw [Measure.map_apply (measurable_const_mul g) hB, hνapp _ (measurable_const_mul g hB), hνapp B hB]
    obtain ⟨a, ha, hamap, hae⟩ := hinv g
    calc ∫⁻ x, m ((fun k => s x * e k) ⁻¹' ((fun h => g * h) ⁻¹' B)) ∂ρ
        = ∫⁻ x, m ((fun k => s (a x) * e k) ⁻¹' B) ∂ρ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          obtain ⟨k, hk⟩ := hx
          have h1 : (fun k' => s x * e k') ⁻¹' ((fun h => g * h) ⁻¹' B)
              = (fun k' => s (a x) * e k * e k') ⁻¹' B := by
            ext k'
            simp only [Set.mem_preimage]
            rw [← mul_assoc, hk]
          rw [h1, key]
      _ = ∫⁻ y, m ((fun k => s y * e k) ⁻¹' B) ∂(Measure.map a ρ) := by
          rw [lintegral_map (hmeasψ B hB) ha]
      _ = ∫⁻ y, m ((fun k => s y * e k) ⁻¹' B) ∂ρ := by rw [hamap]
  haveI : IsFiniteMeasureOnCompacts ν := by
    constructor
    intro A hA
    have hsub : φ ⁻¹' A ⊆ (s ⁻¹' (A * Set.range e)) ×ˢ Set.univ := by
      intro p hp
      refine ⟨?_, Set.mem_univ _⟩
      simp only [Set.mem_preimage] at hp ⊢
      exact Set.mem_mul.mpr ⟨s p.1 * e p.2, hp, e (p.2⁻¹), ⟨p.2⁻¹, rfl⟩, by simp [mul_assoc]⟩
    calc ν A = (ρ.prod m) (φ ⁻¹' A) := Measure.map_apply hφ hA.isClosed.measurableSet
      _ ≤ (ρ.prod m) ((s ⁻¹' (A * Set.range e)) ×ˢ Set.univ) := measure_mono hsub
      _ = ρ (s ⁻¹' (A * Set.range e)) * m Set.univ := Measure.prod_prod _ _
      _ < ⊤ := by rw [hm1, mul_one]; exact hfin A hA
  have hνeq := Measure.isMulLeftInvariant_eq_smul ν μ
  set c := ν.haarScalarFactor μ with hc_def
  have hc0 : c ≠ 0 := by
    intro h0
    have h : ν Set.univ = 0 := by rw [hνeq, h0, zero_smul]; rfl
    rw [hνapp _ MeasurableSet.univ] at h
    simp only [Set.preimage_univ, hm1, lintegral_const, one_mul] at h
    exact hρ (Measure.measure_univ_eq_zero.mp h)
  have hcR : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hc0
  refine ⟨(c : ℝ)⁻¹, inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0)), ?_⟩
  intro F hF _ hFK
  have h1 : ∫ y, F y ∂ν = ∫ x, F (s x) ∂ρ := by
    rw [hν_def, integral_map hφ.aemeasurable hF.aestronglyMeasurable]
    have h : (fun p : X × K => F (φ p)) = fun p => F (s p.1) := by
      funext p; exact hFK (s p.1) p.2
    have hf := integral_fun_fst (μ := ρ) (ν := m) (fun x => F (s x))
    rw [h, hf, measureReal_def, hm1]
    simp
  have h2 : ∫ y, F y ∂ν = ((c : ℝ) : ℂ) * ∫ y, F y ∂μ := by
    conv_lhs => rw [hνeq]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rw [← h1, h2, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hcR, Complex.ofReal_one, one_mul]

end GlobalTheory.CompanionTheory.ConeHaar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSobolevEmbedding
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.CptSobProof

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Van {V : Type} [Zero V] (R : ℝ) (f : Mat n → V) : Prop := ∀ y ∈ GLs n, R < lg y → f y = 0

theorem isOpen_GLs : IsOpen (GLs n) := by
  have h : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage h

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isOpen_far (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (R : ℝ) :
    IsOpen {y : Mat n | y ∈ GLs n ∧ R < lg y} := by
  have h := hlg.isOpen_inter_preimage isOpen_GLs (isOpen_Ioi (a := R))
  exact h

section Vanish

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {R : ℝ} {f : Mat n → V}

theorem Van.rd (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (X : Mat n) : Van R (Rd X f) := by
  intro y hy hR
  have he : f =ᶠ[𝓝 y] fun _ => (0 : V) := by
    filter_upwards [(isOpen_far hlg R).mem_nhds ⟨hy, hR⟩] with z hz using h z hz.1 hz.2
  simp [Rd, he.fderiv_eq]

theorem Van.eu (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (a b : Fin n) :
    Van R (Eu s a b f) := by
  intro y hy hR
  have h1 := h.rd hlg (Matrix.single a b 1) y hy hR
  have h2 := h.rd hlg (Matrix.single a b Complex.I) y hy hR
  cases s <;> simp [Eu, h1, h2]

theorem Van.epow (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (m : ℕ) (a b : Fin n) :
    Van R (Epow s m a b f) := by
  induction m generalizing a b with
  | zero =>
    intro y hy hR
    by_cases hab : a = b
    · simp [Epow, hab, h y hy hR]
    · simp [Epow, hab]
  | succ m ih =>
    intro y hy hR
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_eq_zero fun c _ => (ih c b).eu hlg s a c y hy hR

theorem Van.gel (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (m : ℕ) :
    Van R (gel s m f) := by
  intro y hy hR
  simp only [PositivityTheory.RgBcC.gel, Finset.sum_apply]
  exact Finset.sum_eq_zero fun a _ => h.epow hlg s m a a y hy hR

theorem Van.om (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) : Van R (Om f) := by
  intro y hy hR
  have h1 := h.gel hlg true 2 y hy hR
  have h2 := h.gel hlg false 2 y hy hR
  simp [Om, h1, h2]

theorem Van.rw (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (w : List (Bool × Fin n × Fin n)) :
    Van R (Rw w f) := by
  induction w with
  | nil => exact h
  | cons p w ih => exact ih.rd hlg (bs p)

theorem rw_smooth (hC : RCalc) (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Bool × Fin n × Fin n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact ((hC n).1 V _ ih).1 (bs p)

end Vanish

theorem memLp_of_van [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {R : ℝ} {g : Mat n → V}
    (hK : IsCompact {y : G n | lg y.val ≤ R}) (hc : ContinuousOn g (GLs n)) (hv : Van R g) :
    MemLp (fun y : G n => g y.val) 2 μ := by
  have hcont : Continuous (fun y : G n => g y.val) :=
    hc.comp_continuous Units.continuous_val val_mem_GLs
  have hsupp : HasCompactSupport (fun y : G n => g y.val) :=
    HasCompactSupport.intro hK fun y hy => hv y.val (val_mem_GLs y) (not_le.1 hy)
  exact hcont.memLp_of_hasCompactSupport hsupp

theorem cptSob : CptSob := by
  intro n _ _ μ _ V _ _ hL hC f hf hcpt
  obtain ⟨-, -, -, hs, hk, -⟩ := hL n
  obtain ⟨R, hR⟩ := hcpt
  have hv : Van R f := hR
  exact ⟨⟨hf, fun w => memLp_of_van μ (hk R) (rw_smooth hC hf w).continuousOn (hv.rw hs.continuousOn w)⟩,
    R, hv.om hs.continuousOn⟩

end GlobalTheory.CompanionTheory.CptSobProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureDensityFormula
section
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar

theorem continuous_hOf (n : ℕ) : Continuous (hOf : (Fin n × Fin n → ℝ) → Mat n) := by
  unfold hOf
  fun_prop

theorem isClosed_posSemidef (n : ℕ) : IsClosed {M : Mat n | M.PosSemidef} := by
  have h : {M : Mat n | M.PosSemidef} =
      {M : Mat n | Mᴴ = M} ∩ ⋂ x : Fin n → ℂ, {M : Mat n | 0 ≤ star x ⬝ᵥ M *ᵥ x} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [h]
  refine IsClosed.inter (isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id) ?_
  refine isClosed_iInter fun x => isClosed_le continuous_const ?_
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

theorem measurableSet_cone (n : ℕ) : MeasurableSet (cone n) := by
  have h : cone n = (hOf ⁻¹' {M : Mat n | M.PosSemidef}) ∩
      ((fun v => (hOf v : Mat n).det) ⁻¹' {(0 : ℂ)}ᶜ) := by
    ext v
    simp only [cone, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun hv => ⟨hv.posSemidef, hv.det_pos.ne'⟩,
      fun hv => (Matrix.PosSemidef.posDef_iff_det_ne_zero hv.1).2 hv.2⟩
  rw [h]
  refine MeasurableSet.inter ((isClosed_posSemidef n).preimage (continuous_hOf n)).measurableSet ?_
  exact (isClosed_singleton.isOpen_compl.preimage
    (continuous_hOf n).matrix_det).measurableSet

theorem measurable_coneW (n : ℕ) : Measurable (coneW n) := by
  have h : Continuous fun v : Fin n × Fin n → ℝ => (hOf v : Mat n).det.re :=
    Complex.continuous_re.comp (continuous_hOf n).matrix_det
  unfold coneW
  exact ((h.measurable.pow_const n).inv).ennreal_ofReal

theorem coneW_toReal_smul (n : ℕ) (f : (Fin n × Fin n → ℝ) → ℂ) {v : Fin n × Fin n → ℝ}
    (hv : v ∈ cone n) : (coneW n v).toReal • f v = f v * ((hOf v).det ^ n)⁻¹ := by
  have hpos : (0 : ℂ) < (hOf v : Mat n).det := Matrix.PosDef.det_pos hv
  obtain ⟨hre, him⟩ := Complex.pos_iff.1 hpos
  have hdet : (hOf v : Mat n).det = (((hOf v : Mat n).det.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simpa using him.symm)
  have hnn : 0 ≤ ((hOf v : Mat n).det.re ^ n)⁻¹ := inv_nonneg.2 (pow_nonneg hre.le n)
  unfold coneW
  rw [ENNReal.toReal_ofReal hnn, Complex.real_smul, mul_comm]
  congr 1
  conv_rhs => rw [hdet]
  push_cast
  rfl

theorem cone_integral : ∀ n : ℕ, (∀ᵐ v ∂(coneMeas n), v ∈ PositivityTheory.RgBcC.cone n) ∧ ∀ f : (Fin n × Fin n → ℝ) → ℂ, ∫ v, f v ∂(coneMeas n) = ∫ v in PositivityTheory.RgBcC.cone n, f v * ((hOf v).det ^ n)⁻¹ := by
  intro n
  refine ⟨?_, fun f => ?_⟩
  · exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (measurableSet_cone n))
  · unfold coneMeas
    rw [integral_withDensity_eq_integral_toReal_smul₀ (measurable_coneW n).aemeasurable
      (Eventually.of_forall fun v => ENNReal.ofReal_lt_top) f]
    exact setIntegral_congr_fun (measurableSet_cone n) fun v hv => coneW_toReal_smul n f hv

end GlobalTheory.CompanionTheory.ConeHaar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffOnUncurryOfFrame
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp.Frame

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def eps (p : Bool × Fin n × Fin n) (A : Mat n) : ℝ :=
  if p.1 then (A p.2.1 p.2.2).re else (A p.2.1 p.2.2).im

theorem contDiff_eps (p : Bool × Fin n × Fin n) : ContDiff ℝ ∞ (eps p : Mat n → ℝ) := by
  obtain ⟨b, i, j⟩ := p
  cases b
  · have e : (eps (false, i, j) : Mat n → ℝ) = Complex.imCLM ∘ fun y : Mat n => y i j := by
      funext A; simp [eps]
    rw [e]
    exact Complex.imCLM.contDiff.comp (GlobalTheory.CompanionTheory.LengthGL.contDiff_ent i j)
  · have e : (eps (true, i, j) : Mat n → ℝ) = Complex.reCLM ∘ fun y : Mat n => y i j := by
      funext A; simp [eps]
    rw [e]
    exact Complex.reCLM.contDiff.comp (GlobalTheory.CompanionTheory.LengthGL.contDiff_ent i j)

theorem sum_eps (A : Mat n) : ∑ p, eps p A • (bs p : Mat n) = A := by
  ext a b
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, eps, bs, Matrix.sum_apply, Matrix.smul_apply]
  simp [Matrix.single_apply, Finset.sum_add_distrib, ite_and]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem fderiv_frame (f : Mat n → V) {x : Mat n} (hx : x ∈ GLs n) (ξ : Mat n) :
    fderiv ℝ f x ξ = ∑ p, eps p (ξ * x⁻¹) • fderiv ℝ f x (bs p * x) := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have e : ξ = ∑ p, eps p (ξ * x⁻¹) • (bs p * x) := by
    have : ξ * x⁻¹ * x = ξ := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    conv_lhs => rw [← this, ← sum_eps (ξ * x⁻¹), Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => smul_mul_assoc _ _ _
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [e, map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

theorem contDiffOn_coeff (p : Bool × Fin n × Fin n) (ξ : Mat n) :
    ContDiffOn ℝ ∞ (fun x : Mat n => eps p (ξ * x⁻¹)) (GLs n) :=
  (contDiff_eps p).comp_contDiffOn
    ((GlobalTheory.CompanionTheory.RCalc.mulL ξ).contDiff.comp_contDiffOn GlobalTheory.CompanionTheory.LengthGL.contDiffOn_inv)

theorem contDiffOn_coeff' (p : Bool × Fin n × Fin n) (ξ : Mat n) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Mat n => eps p (ξ * z.2⁻¹)) (Set.univ ×ˢ GLs n) :=
  (contDiffOn_coeff p ξ).comp contDiff_snd.contDiffOn fun _ hz => hz.2

theorem isOpen_dom : IsOpen (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)) :=
  isOpen_univ.prod GlobalTheory.CompanionTheory.LengthGL.isOpen_GLs

theorem hasFDerivAt_uncurry {h h₀ : ℝ → Mat n → V} {hp : (Bool × Fin n × Fin n) → ℝ → Mat n → V}
    (c₀ : ContinuousOn (Function.uncurry h₀) (Set.univ ×ˢ GLs n))
    (cp : ∀ p, ContinuousOn (Function.uncurry (hp p)) (Set.univ ×ˢ GLs n))
    (ht : ∀ t, ∀ x ∈ GLs n, HasDerivAt (fun s => h s x) (h₀ t x) t)
    (hd : ∀ t, DifferentiableOn ℝ (h t) (GLs n))
    (hf : ∀ p t, ∀ x ∈ GLs n, fderiv ℝ (h t) x (bs p * x) = hp p t x)
    {t : ℝ} {x : Mat n} (hx : x ∈ GLs n) :
    HasFDerivAt (Function.uncurry h)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (h₀ t x)).coprod (fderiv ℝ (h t) x)) (t, x) := by
  have hn : (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)) ∈ nhds ((t, x) : ℝ × Mat n) :=
    isOpen_dom.mem_nhds ⟨trivial, hx⟩
  have c1 : ContinuousOn (Function.uncurry fun (t : ℝ) (x : Mat n) => (1 : ℝ →L[ℝ] ℝ).smulRight (h₀ t x))
      (Set.univ ×ˢ GLs n) := by
    rw [continuousOn_clm_apply]
    intro y
    refine ContinuousOn.congr (f := fun z : ℝ × Mat n => y • Function.uncurry h₀ z)
      ((continuousOn_const (c := y)).smul c₀) ?_
    rintro ⟨s, w⟩ -
    simp [Function.uncurry_def]
  have c2 : ContinuousOn (Function.uncurry fun (t : ℝ) (x : Mat n) => fderiv ℝ (h t) x)
      (Set.univ ×ˢ GLs n) := by
    refine continuousOn_clm_apply.2 fun ξ => ?_
    have h1 : ContinuousOn (fun z : ℝ × Mat n => ∑ p, eps p (ξ * z.2⁻¹) • hp p z.1 z.2)
        (Set.univ ×ˢ GLs n) :=
      continuousOn_finsetSum _ fun p _ => (contDiffOn_coeff' p ξ).continuousOn.smul (cp p)
    refine h1.congr ?_
    rintro ⟨s, y⟩ ⟨-, hy⟩
    have hy' : y ∈ GLs n := hy
    exact (fderiv_frame (h s) hy' ξ).trans (Finset.sum_congr rfl fun p _ => by rw [hf p s y hy'])
  have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := ((t, x) : ℝ × Mat n)) (f := h)
    (f₁ := fun t x => (1 : ℝ →L[ℝ] ℝ).smulRight (h₀ t x)) (f₂ := fun t x => fderiv ℝ (h t) x)
    ?_ ?_ (c1.continuousAt hn) (c2.continuousAt hn)
  · exact key.hasFDerivAt
  · filter_upwards [hn] with v hv
    exact (ht v.1 v.2 hv.2).hasFDerivAt
  · filter_upwards [hn] with v hv
    exact ((hd v.1 v.2 hv.2).differentiableAt (GlobalTheory.CompanionTheory.LengthGL.isOpen_GLs.mem_nhds hv.2)).hasFDerivAt

theorem contDiffOn_step (F : Set (ℝ → Mat n → V))
    (hc : ∀ h ∈ F, ContinuousOn (Function.uncurry h) (Set.univ ×ˢ GLs n))
    (hdt : ∀ h ∈ F, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, HasDerivAt (fun s => h s x) (h' t x) t)
    (hd : ∀ h ∈ F, ∀ t, DifferentiableOn ℝ (h t) (GLs n))
    (hfr : ∀ h ∈ F, ∀ p, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, fderiv ℝ (h t) x (bs p * x) = h' t x)
    (k : ℕ) (ih : ∀ h ∈ F, ContDiffOn ℝ k (Function.uncurry h) (Set.univ ×ˢ GLs n)) :
    ∀ h ∈ F, ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry h) (Set.univ ×ˢ GLs n) := by
  intro h hh
  obtain ⟨h₀, h₀F, ht⟩ := hdt h hh
  choose hp hpF hf using hfr h hh
  have hD : ∀ z ∈ (Set.univ ×ˢ GLs n : Set (ℝ × Mat n)), HasFDerivAt (Function.uncurry h)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (h₀ z.1 z.2)).coprod (fderiv ℝ (h z.1) z.2)) z := fun z hz =>
    hasFDerivAt_uncurry (hc _ h₀F) (fun p => hc _ (hpF p)) ht (hd h hh) hf hz.2
  have e : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by norm_cast
  rw [e, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_dom]
  refine ⟨fun z hz => (hD z hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_clm_apply]
  rintro ⟨τ, ξ⟩
  have h1 : ContDiffOn ℝ k (fun z : ℝ × Mat n =>
      τ • h₀ z.1 z.2 + ∑ p, eps p (ξ * z.2⁻¹) • hp p z.1 z.2) (Set.univ ×ˢ GLs n) := by
    refine ContDiffOn.add (contDiffOn_const.smul (ih _ h₀F)) (ContDiffOn.sum fun p _ => ?_)
    exact ((contDiffOn_coeff' p ξ).of_le (by exact_mod_cast le_top)).smul (ih _ (hpF p))
  refine h1.congr ?_
  rintro ⟨s, y⟩ hz
  have e1 : fderiv ℝ (Function.uncurry h) (s, y) = _ := (hD _ hz).fderiv
  refine (congrArg (fun L => L (τ, ξ)) e1).trans ?_
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply]
  rw [fderiv_frame _ hz.2]
  simp only [ContinuousLinearMap.one_apply]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by rw [hf p s y hz.2]

theorem contDiffOn_uncurry_of_frame : ∀ {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (F : Set (ℝ → Mat n → V)), (∀ h ∈ F, ContinuousOn (Function.uncurry h) (Set.univ ×ˢ GLs n)) →
    (∀ h ∈ F, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, HasDerivAt (fun s => h s x) (h' t x) t) →
    (∀ h ∈ F, ∀ t, DifferentiableOn ℝ (h t) (GLs n)) →
    (∀ h ∈ F, ∀ p, ∃ h' ∈ F, ∀ t, ∀ x ∈ GLs n, fderiv ℝ (h t) x (bs p * x) = h' t x) →
    ∀ h ∈ F, ContDiffOn ℝ ∞ (Function.uncurry h) (Set.univ ×ˢ GLs n) := by
  intro n V _ _ F hc hdt hd hfr h hh
  rw [contDiffOn_infty]
  intro k
  induction k generalizing h with
  | zero =>
    have h0 : ContDiffOn ℝ 0 (Function.uncurry h) (Set.univ ×ˢ GLs n) := contDiffOn_zero.2 (hc h hh)
    simpa using h0
  | succ k ih => exact contDiffOn_step F hc hdt hd hfr k (fun h hh => ih h hh) h hh

end GlobalTheory.CompanionTheory.WaveCp.Frame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvRightEquivariant
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem conv_right_equivariant : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)), KReg k → KReg k' → (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k' (y * k₂.1) = k' y * E.ρ k₂) → ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, conv μ E k k' (x * k₂.1) = conv μ E k k' x * E.ρ k₂ := by
  intro _ n _ _ μ _ E k k' _ _ hk' x hx k₂
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hinv : E.ρ k₂ * E.ρ k₂⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : E.ρ k₂⁻¹ * E.ρ k₂ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  let L : (E.V →L[ℂ] E.V) ≃L[ℂ] (E.V →L[ℂ] E.V) :=
    ContinuousLinearEquiv.equivOfInverse
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂))
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂⁻¹))
      (fun A => by simp [mul_assoc, hinv]) (fun A => by simp [mul_assoc, hinv'])
  have hL : ∀ A, L A = A * E.ρ k₂ := fun A => rfl
  have hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n := by
    intro y
    have h1 : ((y⁻¹ : G n).val).det ≠ 0 := by
      have := (Matrix.isUnit_iff_isUnit_det _).1 (y⁻¹ : G n).isUnit
      exact this.ne_zero
    change ((y⁻¹ : G n).val * x).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 hx
  unfold conv
  rw [← hL, ← L.integral_comp_comm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change k y.val * k' ((y⁻¹ : G n).val * (x * k₂.1)) = L (k y.val * k' ((y⁻¹ : G n).val * x))
  rw [hL, ← mul_assoc, hk' _ (hmem y) k₂, mul_assoc]

end GlobalTheory.CompanionTheory.WaveMult
end

