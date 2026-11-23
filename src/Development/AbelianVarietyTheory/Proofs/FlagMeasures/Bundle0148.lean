module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0113

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioRankFactor
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem volU_succ_eq_mul (m : ℕ) :
    volU (m + 1) = volU m * (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) * 2 ^ m) := by
  have h : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := by
    have := Nat.triangle_succ m
    simpa using this
  unfold volU sphV
  rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)), h, pow_add]
  simp only [Nat.add_sub_cancel]
  ring

theorem vInv_pos_of_numberField (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
  positivity

theorem mass_ratio_mul_unitary_volume :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ), 1 ≤ M →
      Formalism.HermitianLatticesTheory.massRatioRightSide E M * volU M ^ Formalism.HermitianLatticesTheory.fDeg E =
        rankFac E M * volU (M - 1) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  intro E _ _ _ M hM
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hv := vInv_pos_of_numberField E
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide rankFac
  simp only [Nat.add_sub_cancel]
  rw [volU_succ_eq_mul]
  set v := Formalism.HermitianLatticesTheory.vInv E
  set f := Formalism.HermitianLatticesTheory.fDeg E
  have h2 : 0 < 2 * v := by positivity
  have hfac : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hpi := Real.pi_pos.ne'
  have key : ((m.factorial : ℝ) * (v / Real.pi) ^ (m + 1)) *
      (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) * 2 ^ m) = (2 * v) ^ (m + 1) := by
    rw [div_pow, mul_pow]
    field_simp
    ring
  have hr : (2 * v) ^ ((f : ℝ) * (((m + 1 : ℕ) : ℝ) - 1 / 2)) =
      ((2 * v) ^ (m + 1)) ^ f / Real.sqrt ((2 * v) ^ f) := by
    rw [Real.sqrt_eq_rpow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul h2.le, ← Real.rpow_sub h2]
    congr 1
    push_cast
    ring
  rw [hr, ← key, mul_pow (volU m), mul_pow ((m.factorial : ℝ) * (v / Real.pi) ^ (m + 1))]
  ring

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitary
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.FlagMeas.measurable_detOn_comp {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ}
    (f : X → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f) (V : Submodule ℂ (Fin n → ℂ)) :
    Measurable fun x => _root_.GlobalTheory.FlagMeas.detOn (f x) V := by
  classical
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  let P := Submodule.linearProjOfIsCompl V W hW
  let b := Module.finBasis ℂ V
  let g : X → ℂ := fun x =>
    (Matrix.of fun i k => b.repr (P (f x *ᵥ (b k : Fin n → ℂ))) i).det
  have hg : Continuous g := by
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun i k => ?_
    have hL : Continuous fun v : Fin n → ℂ => b.repr (P v) i :=
      (((Finsupp.lapply i).comp b.repr.toLinearMap).comp P).continuous_of_finiteDimensional
    exact hL.comp (hf.matrix_mulVec continuous_const)
  have hS : IsClosed {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := by
    simp only [Set.setOf_forall]
    refine isClosed_biInter fun y _ => ?_
    exact V.closed_of_finiteDimensional.preimage (hf.matrix_mulVec continuous_const)
  have heq : (fun x => _root_.GlobalTheory.FlagMeas.detOn (f x) V) =
      fun x => if x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} then ‖g x‖ else 0 := by
    funext x
    unfold _root_.GlobalTheory.FlagMeas.detOn
    by_cases h : ∀ y ∈ V, (toLin' (f x)) y ∈ V
    · have h' : x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := fun y hy => by
        simpa [Matrix.toLin'_apply] using h y hy
      rw [dite_eq_left h, if_pos h', ← LinearMap.det_toMatrix b]
      congr 2
      ext i k
      rw [LinearMap.toMatrix_apply, Matrix.of_apply]
      congr 2
      have hm : f x *ᵥ (b k : Fin n → ℂ) = ((toLin' (f x)).restrict h (b k) : Fin n → ℂ) := by
        simp [LinearMap.restrict_apply, Matrix.toLin'_apply]
      rw [hm]
      exact (Submodule.projectionOnto_apply_left hW _).symm
    · have h' : x ∉ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := fun hx => h fun y hy => by
        simpa [Matrix.toLin'_apply] using hx y hy
      rw [dite_eq_right h, if_neg h']
  rw [heq]
  exact Measurable.ite hS.measurableSet hg.norm.measurable measurable_const


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.FlagMeas.measurable_locSize_uMat (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (i : Fin a) :
    Measurable fun g : _root_.Formalism.REAL.UJ ε => _root_.GlobalTheory.FlagMeas.locSize j W (_root_.Formalism.MainNotions.S.uMat g) i := by
  have hc : Continuous fun g : _root_.Formalism.REAL.UJ ε => _root_.Formalism.MainNotions.S.uMat g := by
    unfold _root_.Formalism.MainNotions.S.uMat
    exact Units.continuous_val.comp continuous_subtype_val
  unfold _root_.GlobalTheory.FlagMeas.locSize
  exact ((_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _).div
    (_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _)).pow_const _

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableHsNormSqAmplitudeBesselUnitary
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AmpMeas

theorem stronglyMeasurable_indicator_of_continuousOn {X W : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {S : Set X}
    (hS : MeasurableSet S) {f : X → W} (hf : ContinuousOn f S) : StronglyMeasurable (S.indicator f) := by
  classical
  haveI : ProperSpace W := FiniteDimensional.proper ℂ W
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  have := hf.measurable_piecewise (g := fun _ => (0 : W)) continuousOn_const hS
  have h2 : S.indicator f = S.piecewise f fun _ => (0 : W) := by
    funext x; by_cases hx : x ∈ S <;> simp [hx]
  rw [h2]
  exact this.stronglyMeasurable

theorem continuous_hsNormSq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Continuous fun A : Wq →L[ℂ] Wp => hsNormSq A := by
  unfold hsNormSq hsInner
  refine Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => ?_)
  have : Continuous fun A : Wq →L[ℂ] Wp => A (stdOrthonormalBasis ℂ Wq i) :=
    (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous
  exact this.inner this

theorem measurable_hsNormSq_ampJ : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (μG : Measure (Mt k r)) (c : ℝ) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) := by
  intro k r Wp _ _ _ _ Wq _ _ _ μG c Φ Φ' hH hΦ hΦ'
  haveI : SigmaFinite μG := hH.1
  have hcl : IsClosed {x : Mat k r | xᴴ * Hpk k r * x = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hcl' : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := hcl
  set S : Set (Mt k r) := {x : Mt k r | Matrix.of x ∈ GG k r} with hSdef
  have hS : MeasurableSet S := hcl'.measurableSet
  have hmul : ∀ γ x : Mat k r, γ ∈ GG k r → x ∈ GG k r → γ * x ∈ GG k r := by
    intro γ x hγ hx
    have hs' : γᴴ * Hpk k r * γ = Hpk k r := hγ
    have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
    show (γ * x)ᴴ * Hpk k r * (γ * x) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc xᴴ * γᴴ * Hpk k r * (γ * x) = xᴴ * (γᴴ * Hpk k r * γ) * x := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hs', hx']
  have hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  let F : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p =>
    (innerSL ℂ (Φ' (Matrix.of p.2))).smulRight (Φ (Matrix.of p.1 * Matrix.of p.2))
  have hcont : Continuous fun p : Wq × Wp => (innerSL ℂ p.1).smulRight p.2 := by
    have h1 : Continuous fun p : Wq × Wp => innerSL ℂ p.1 := (innerSL ℂ).continuous.comp continuous_fst
    exact ((ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous₂).comp (h1.prodMk continuous_snd)
  have h1 : ContinuousOn (fun p : Mt k r × Mt k r => Φ' (Matrix.of p.2)) (S ×ˢ S) :=
    hΦ'.comp (hof.comp continuous_snd).continuousOn fun p hp => hp.2
  have h2 : ContinuousOn (fun p : Mt k r × Mt k r => Φ (Matrix.of p.1 * Matrix.of p.2)) (S ×ˢ S) :=
    hΦ.comp ((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).continuousOn
      fun p hp => hmul _ _ hp.1 hp.2
  have hF : ContinuousOn F (S ×ˢ S) := hcont.comp_continuousOn (h1.prodMk h2)
  have hsm : StronglyMeasurable ((S ×ˢ S).indicator F) :=
    stronglyMeasurable_indicator_of_continuousOn (hS.prod hS) hF
  have hint : StronglyMeasurable fun γ => ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG :=
    hsm.integral_prod_right'
  have hm : Measurable fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG) :=
    (continuous_hsNormSq.comp_stronglyMeasurable (hint.const_smul (c : ℂ)⁻¹)).measurable
  have hae : ∀ᵐ x ∂μG, x ∈ S := by rw [ae_iff]; exact hH.2.2.1
  have heq : (S.indicator fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) =
      S.indicator fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG) := by
    refine Set.indicator_congr fun γ hγ => ?_
    unfold ampJ
    congr 2
    refine integral_congr_ae (hae.mono fun x hx => ?_)
    have : (γ, x) ∈ S ×ˢ S := ⟨hγ, hx⟩
    simp only [Set.indicator_of_mem this, F]
  rw [heq]
  exact hm.indicator hS

end GlobalTheory.Amp.AmpMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableStarProjectionKerMatrix
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [CompleteSpace E] [CompleteSpace F]

theorem kerProj_re_inner_reg (T : E →L[ℂ] F) (t : ℝ) (w : E) :
    (⟪w, (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E)) w⟫_ℂ).re
      = ‖T w‖ ^ 2 + t * ‖w‖ ^ 2 := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_add_right,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem kerProj_isUnit_reg (T : E →L[ℂ] F) {t : ℝ} (ht : 0 < t) :
    IsUnit (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E)) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  set B := ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E) with hB
  have hinj : Function.Injective B := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    have h := kerProj_re_inner_reg T t w
    rw [← hB, hw] at h
    simp only [inner_zero_right, Complex.zero_re] at h
    have h1 : t * ‖w‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖T w‖]
    have h2 : ‖w‖ ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos ht hc]
    have : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    exact norm_eq_zero.mp this
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (B : E →ₗ[ℂ] E))).mp hinj⟩

theorem kerProj_reg_estimate (T : E →L[ℂ] F) {t : ℝ} (ht : 0 < t) (k : E) (z : F)
    (hk : T k = 0) :
    ‖(t : ℂ) • Ring.inverse (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E))
      (k + ContinuousLinearMap.adjoint T z) - k‖ ^ 2 ≤ t * ‖z‖ ^ 2 := by
  have hu := kerProj_isUnit_reg T ht
  set B := ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E) with hB
  set w := (t : ℂ) • Ring.inverse B (k + ContinuousLinearMap.adjoint T z) - k with hw
  have hBk : B k = (t : ℂ) • k := by simp [hB, hk]
  have hBw : B w = (t : ℂ) • ContinuousLinearMap.adjoint T z := by
    have : B (Ring.inverse B (k + ContinuousLinearMap.adjoint T z))
        = k + ContinuousLinearMap.adjoint T z := by
      rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu]; rfl
    rw [hw, map_sub, map_smul, this, hBk, smul_add]; abel
  have h := kerProj_re_inner_reg T t w
  rw [← hB, hBw, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    Complex.re_ofReal_mul] at h
  have h1 : (⟪T w, z⟫_ℂ).re ≤ ‖T w‖ * ‖z‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : ‖T w‖ ^ 2 + t * ‖w‖ ^ 2 ≤ t * (‖T w‖ * ‖z‖) := by
    rw [← h]; exact mul_le_mul_of_nonneg_left h1 ht.le
  have h3 : t * ‖w‖ ^ 2 ≤ t * (t * ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (‖T w‖ - t * ‖z‖), sq_nonneg ‖T w‖, sq_nonneg (t * ‖z‖)]
  exact le_of_mul_le_mul_left h3 ht

theorem kerProj_reg_tendsto (T : E →L[ℂ] F) (v : E) :
    Filter.Tendsto (fun j : ℕ => (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) •
      Ring.inverse (ContinuousLinearMap.adjoint T ∘L T
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) v) Filter.atTop
      (nhds ((LinearMap.ker (T : E →ₗ[ℂ] F)).starProjection v)) := by
  set K := LinearMap.ker (T : E →ₗ[ℂ] F) with hK
  have hmem : v - K.starProjection v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have horth : Kᗮ = LinearMap.range (LinearMap.adjoint (T : E →ₗ[ℂ] F)) :=
    LinearMap.orthogonal_ker _
  rw [horth] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hz' : ContinuousLinearMap.adjoint T z = v - K.starProjection v := by
    rw [← hz]; rfl
  have hk : T (K.starProjection v) = 0 := K.starProjection_apply_mem v
  have hv : v = K.starProjection v + ContinuousLinearMap.adjoint T z := by rw [hz']; abel
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun j : ℕ => Real.sqrt ((1 / ((j : ℝ) + 1)) * ‖z‖ ^ 2))
      Filter.atTop (nhds 0) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (‖z‖ ^ 2)).sqrt
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hlim
  apply Real.le_sqrt_of_sq_le
  have := kerProj_reg_estimate T (t := 1 / ((j : ℝ) + 1)) (by positivity) _ z hk
  rwa [← hv] at this

theorem measurable_starProjection_ker_clm {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [MeasurableSpace E] [BorelSpace E] (T : X → E →L[ℂ] F) (v : X → E)
    (hT : Continuous T) (hv : Continuous v) :
    Measurable fun x => (LinearMap.ker (T x : E →ₗ[ℂ] F)).starProjection (v x) := by
  refine measurable_of_tendsto_metrizable (f := fun (j : ℕ) x => (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) •
      Ring.inverse (ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) (v x)) (fun j => ?_) ?_
  · apply Continuous.measurable
    apply Continuous.const_smul
    refine Continuous.clm_apply ?_ hv
    have hc : Continuous fun x => ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E) :=
      ((ContinuousLinearMap.adjoint.continuous.comp hT).clm_comp hT).add continuous_const
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨u, hu⟩ := kerProj_isUnit_reg (T x) (t := 1 / ((j : ℝ) + 1)) (by positivity)
    have h1 := NormedRing.inverse_continuousAt u
    rw [hu] at h1
    exact ContinuousAt.comp (f := fun x => ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) h1 hc.continuousAt
  · rw [tendsto_pi_nhds]
    intro x
    exact kerProj_reg_tendsto (T x) (v x)

end

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MultisetEq
section
open Finset Matrix

noncomputable section

namespace GlobalTheory.Dec.GelfSepProof


open PowerSeries Matrix in
theorem _root_.GlobalTheory.Dec.GelfSepProof.gen {n : ℕ} (l : Fin n → ℂ) :
    ((1 : PowerSeries ℂ) -
        PowerSeries.X * PowerSeries.mk fun (k : ℕ) ↦ ∑ a : Fin n, ∑ b : Fin n, (_root_.Formalism.REAL.Amat l ^ k) a b) *
      ∏ a : Fin n, ((1 : PowerSeries ℂ) - (PowerSeries.C : ℂ → PowerSeries ℂ) (l a) * PowerSeries.X) =
    ∏ a : Fin n,
      ((1 : PowerSeries ℂ) -
        ((PowerSeries.C : ℂ → PowerSeries ℂ) (l a) + (1 : PowerSeries ℂ)) * PowerSeries.X) := by
  have hA : ∀ a b, _root_.Formalism.REAL.Amat l a b = if a = b then l a else if a < b then -1 else 0 := by
    intro a b
    unfold _root_.Formalism.REAL.Amat
    rfl
  set A := _root_.Formalism.REAL.Amat l with hAdef
  let Y : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := A.map (PowerSeries.C : ℂ → PowerSeries ℂ)
  let B : Matrix (Fin n) (Fin n) (PowerSeries ℂ) :=
    Matrix.of fun a b => PowerSeries.mk fun k => (A ^ k) a b
  have hB : (1 - (X : PowerSeries ℂ) • Y) * B = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc]
    ext a b k
    rcases k with _ | k
    · simp [B, Matrix.one_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [B, Y, Matrix.mul_apply, Matrix.one_apply, pow_succ', PowerSeries.coeff_succ_X_mul,
          map_sum]
        split_ifs <;> simp
  let c : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := replicateCol (Fin 1) 1
  let R : Matrix (Fin 1) (Fin n) (PowerSeries ℂ) := replicateRow (Fin 1) 1
  let J : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := Matrix.of fun _ _ => 1
  let U : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := -((X : PowerSeries ℂ) • (B * c))
  have hcR : c * R = J := by
    ext a b
    simp [c, R, J, Matrix.mul_apply]
  have hBc : (1 - (X : PowerSeries ℂ) • Y) * (B * c) = c := by
    rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hfactor : (1 - (X : PowerSeries ℂ) • Y) * (1 + U * R) =
      1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J := by
    have hU : (1 - (X : PowerSeries ℂ) • Y) * U = -((X : PowerSeries ℂ) • c) := by
      show (1 - (X : PowerSeries ℂ) • Y) * -((X : PowerSeries ℂ) • (B * c)) = _
      rw [Matrix.mul_neg, Matrix.mul_smul, hBc]
    rw [mul_add, mul_one, ← Matrix.mul_assoc, hU, Matrix.neg_mul, Matrix.smul_mul, hcR]
    abel
  have hdet1 : (1 - (X : PowerSeries ℂ) • Y).det = ∏ a : Fin n, (1 - C (l a) * X) := by
    rw [Matrix.det_of_isUpperTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, hA, mul_comm]
    · intro a b hab
      have hba : b < a := hab
      simp [Y, hA, hba.ne', not_lt_of_gt hba, Matrix.one_apply_ne hba.ne']
  have hdet2 : (1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J).det =
      ∏ a : Fin n, (1 - (C (l a) + 1) * X) := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, J, hA]
      ring
    · intro a b hab
      have hab' : a < b := hab
      simp [Y, J, hA, hab'.ne, hab', Matrix.one_apply_ne hab'.ne]
  have hdet3 : (1 + U * R).det =
      1 - X * PowerSeries.mk fun k => ∑ a : Fin n, ∑ b : Fin n, (A ^ k) a b := by
    rw [Matrix.det_one_add_mul_comm, Matrix.det_unique]
    simp [U, R, B, c, Matrix.mul_apply, Finset.mul_sum, sub_eq_add_neg]
    simp only [← Finset.mul_sum]
    congr 1
    ext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [PowerSeries.coeff_mk, map_sum]
  rw [← hdet2, ← hfactor, Matrix.det_mul, hdet1, hdet3, mul_comm]



end GlobalTheory.Dec.GelfSepProof

namespace GlobalTheory.Dec

end GlobalTheory.Dec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdPartialZpow
section
open Matrix Finset Formalism.MainNotions.S GlobalTheory.Dec

namespace GlobalTheory.PhiTriangular

theorem sum_sInt_from {n : ℕ} (lam : Fin n → ℝ) (l : Fin n) :
    ∑ i : Fin n, (if l ≤ i then sInt lam i else 0) = muInt lam l := by
  let m : ℕ → ℤ := fun k => if h : k < n then muInt lam ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin n, (if l ≤ i then sInt lam i else 0) =
      m (max i.val l.val) - m (max (i.val + 1) l.val) := by
    intro i
    by_cases h : l ≤ i
    · have h' : l.val ≤ i.val := h
      rw [if_pos h, max_eq_left h', max_eq_left (by omega : l.val ≤ i.val + 1)]
      simp only [m, sInt, dif_pos i.isLt]
    · have h' : i.val < l.val := by simpa using h
      rw [if_neg h, max_eq_right h'.le, max_eq_right (by omega : i.val + 1 ≤ l.val), sub_self]
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => m (max k l.val) - m (max (k + 1) l.val)) n,
    Finset.sum_range_sub' (fun k => m (max k l.val)) n, max_eq_right (Nat.zero_le _),
    max_eq_left l.isLt.le]
  simp [m]

theorem prod_castLE_succ {n : ℕ} (d : Fin n → ℂ) (i : Fin n) :
    ∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j) = ∏ l : Fin n, if l ≤ i then d l else 1 := by
  refine Finset.prod_of_injOn (Fin.castLE i.isLt) ((Fin.castLE_injective _).injOn) (by simp) ?_ ?_
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk ⟨⟨k.val, Nat.lt_succ_of_le h⟩, by simp, rfl⟩
  · intro j _
    rw [if_pos]
    exact Nat.le_of_lt_succ j.isLt

theorem zpow_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℤ) {a : ℂ} (ha : a ≠ 0) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

theorem prod_partial_zpow {n : ℕ} (lam : Fin n → ℝ) (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) :
    ∏ i : Fin n, (∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j)) ^ (-(sInt lam i)) =
      ∏ l, d l ^ (-(muInt lam l)) := by
  simp only [prod_castLE_succ, ← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← sum_sInt_from, ← Finset.sum_neg_distrib, zpow_finset_sum _ _ (hd l)]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : l ≤ i <;> simp [h]

theorem phiTri : PhiTri := by
  intro n lam c z c' hc hc' hd hz
  have hd' : ∀ l, c l l * c' l l ≠ 0 := fun l => mul_ne_zero (hd l).1 (hd l).2
  refine ⟨fun i => ?_, ?_⟩
  · rw [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc']
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hd' _) (hz i)
  · unfold Phi
    simp only [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc', mul_zpow _ (leadMinor z _ _)]
    rw [Finset.prod_mul_distrib, prod_partial_zpow lam (fun l => c l l * c' l l) hd']

end GlobalTheory.PhiTriangular
end

