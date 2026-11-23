module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003
public import GroundTheory.AutomorphicForms.CompactFormulaCountable

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ContInfPart
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
open scoped Classical ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private theorem cont_finPart : Continuous (fun v : V4 ℚ => finPartPi v) := by
  refine continuous_pi fun i => ?_
  simp only [finPartPi]
  exact continuous_snd.comp (continuous_apply i)

private theorem cont_infPart : Continuous (fun v : V4 ℚ => infPartPi v) := by
  refine continuous_pi fun i => ?_
  simp only [infPartPi]
  fun_prop

private theorem wt_nonneg' (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (n : ℕ) (v : V4 ℚ) : 0 ≤ wt K n v := by
  unfold wt
  split_ifs <;> positivity

private theorem wt_meas (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (hK : IsCompact K) (n : ℕ) :
    Measurable (fun v : V4 ℚ => wt K n v) := by
  have hs : MeasurableSet {v : V4 ℚ | finPartPi v ∈ K} := (hK.isClosed.preimage cont_finPart).measurableSet
  unfold wt
  exact Measurable.ite hs (((continuous_const.add cont_infPart.norm).pow n).measurable.inv) measurable_const

private theorem bound (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2)
    (φ : ↥(Sm E 2)) (hφ : φ ∈ P.V) (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (hK : IsCompact K) :
    ∃ (n : ℕ) (B : ℝ), ∀ z ∈ normOneFundamentalDomain E, ∀ h : G1 E,
      (Summable fun ξ : Fin 4 → ℚ => wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ))) ∧
      (∑' ξ : Fin 4 → ℚ, wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ))) *
        ‖φ.1 (gl h * sZ D (z : IdeleGroup E))‖ ≤ B := by
  obtain ⟨c0, C0, hc0, hC0, hred⟩ := redE E
  obtain ⟨-, -, Cz, hCz, hz⟩ := zDom E
  obtain ⟨-, hsc, hnu, -⟩ := szLaws E D
  have hgl : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by fun_prop
  let C : Set (GL (Fin 2) (A E)) := (fun p : G1 E × (A E)ˣ => gl p.1 * sZ D p.2) '' (C0 ×ˢ Cz)
  have hC : IsCompact C :=
    (hC0.prod hCz).image ((hgl.comp continuous_fst).mul (hsc.comp continuous_snd))
  have hCn : ∀ k ∈ C, nu ℚ k = 1 := by
    rintro _ ⟨⟨h, z⟩, -, rfl⟩
    simp only [nu_mul, nu_gl, hnu, mul_one]
  have hc : 0 < min c0 1 := lt_min hc0 one_pos
  obtain ⟨n, r, B1, hL⟩ := latSum E D K C (min c0 1) 0 hK hC hCn hc
  obtain ⟨hLf, -, hdec⟩ := decE E P φ hφ
  obtain ⟨B2, hB2⟩ := hdec C hC (min c0 1) hc r
  refine ⟨n, B1 * B2, fun z hzD h => ?_⟩
  obtain ⟨γ, u, b, k, hk, he, hb⟩ := hred h
  obtain ⟨ρ, hρ⟩ := (orb1 E D).1 γ
  have hk' : gl k * sZ D (z : IdeleGroup E) ∈ C := ⟨(k, (z : IdeleGroup E)), ⟨hk, hz z hzD⟩, rfl⟩
  have hY : gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)) =
      gl (ratS E γ) * (gl h * sZ D (z : IdeleGroup E)) := by
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, he]
  have hg : gl (ratS E γ) = ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ) := by
    apply Units.ext
    ext i j
    rfl
  have hφX : φ.1 (gl h * sZ D (z : IdeleGroup E)) =
      φ.1 (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E))) := by
    rw [hY, hg, hLf.2]
  have hwt : ∀ ξ, D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ) =
      D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp (ρ ξ)) := by
    intro ξ
    have e : ∀ g X : GL (Fin 2) (A E), (g * X)⁻¹ * g = X⁻¹ := fun g X => by group
    rw [hY, ← hρ, ← D.act_mul, e]
  have h1 : min c0 1 ≤ ab (1 : (A ℚ)ˣ) := by
    have : ab (1 : (A ℚ)ˣ) = 1 := by simp [ab]
    rw [this]
    exact min_le_right _ _
  have hcb : min c0 1 ≤ ab b := (min_le_left _ _).trans hb
  obtain ⟨hs, hsum, -⟩ := hL 1 u b _ hk' h1 hcb
  simp only [Units.val_one, one_mul] at hs hsum
  have hf : (fun ξ : Fin 4 → ℚ => wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ))) =
      (fun ξ : Fin 4 → ℚ => wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ))) ∘
        ρ.toEquiv := by
    funext ξ
    exact congrArg (wt K n) (hwt ξ)
  have ht : ∑' ξ : Fin 4 → ℚ, wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ)) =
      ∑' ξ : Fin 4 → ℚ, wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ)) := by
    rw [hf]
    exact Equiv.tsum_eq ρ.toEquiv (fun ξ : Fin 4 → ℚ => wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ)))
  refine ⟨by rw [hf]; exact ρ.toEquiv.summable_iff.2 hs, ?_⟩
  rw [ht, hφX]
  have hs0 : 0 ≤ ∑' ξ : Fin 4 → ℚ,
      wt K n (D.act (gl (nU u * mD b) * (gl k * sZ D (z : IdeleGroup E)))⁻¹ (rp ξ)) :=
    tsum_nonneg fun _ => wt_nonneg' _ _ _
  have hab : ab b ≠ 0 := (lt_of_lt_of_le hc0 hb).ne'
  calc _ ≤ (B1 * ab b ^ r) * (B2 * (ab b)⁻¹ ^ r) :=
        mul_le_mul hsum (hB2 u b _ hk' hcb) (norm_nonneg _) (hs0.trans hsum)
    _ = B1 * B2 := by
        rw [inv_pow]
        field_simp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem cont_el (D : Dat ℚ E) : Continuous fun p : ↥(IdeleGroup.normOneSubgroup E) × G1 E =>
    gl p.2 * sZ D (p.1 : IdeleGroup E) := by
  have hgl : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by fun_prop
  obtain ⟨-, hsc, -⟩ := szLaws E D
  exact (hgl.comp continuous_snd).mul (hsc.comp (continuous_subtype_val.comp continuous_fst))

private theorem meas_proj (δ : ℚ) : Measurable fun y : Y E δ => ((y.1, y.2.1) : ↥(IdeleGroup.normOneSubgroup E) × G1 E) :=
  measurable_fst.prodMk (measurable_fst.comp measurable_snd)

private theorem meas_pY (D : Dat ℚ E) : Measurable (pY D) := by
  obtain ⟨ρ', hρc, hρ, -⟩ := actCont ℚ E D
  have hcact : ∀ v, Continuous fun x : GL (Fin 2) (A E) => D.act x v := fun v => by
    simp only [hρ]
    exact (Units.continuous_val.comp hρc).matrix_mulVec continuous_const
  haveI : MeasurableSingletonClass (Orb D.δ) := ⟨fun _ => trivial⟩
  have hc : ∀ ξ : Orb D.δ, Continuous fun x : ↥(IdeleGroup.normOneSubgroup E) × G1 E =>
      D.act (gl x.2 * sZ D (x.1 : IdeleGroup E))⁻¹ (rp ξ.1) := fun ξ => (hcact (rp ξ.1)).comp (cont_el D).inv
  have hf : Measurable fun p : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ =>
      D.act (gl p.1.2 * sZ D (p.1.1 : IdeleGroup E))⁻¹ (rp p.2.1) :=
    measurable_from_prod_countable_left fun ξ => (hc ξ).measurable
  have h2 : Measurable fun y : Y E D.δ =>
      (((y.1, y.2.1), y.2.2) : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ) :=
    (meas_proj D.δ).prodMk (measurable_snd.comp measurable_snd)
  have e : pY D = (fun p : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ =>
      D.act (gl p.1.2 * sZ D (p.1.1 : IdeleGroup E))⁻¹ (rp p.2.1)) ∘ fun y : Y E D.δ =>
      (((y.1, y.2.1), y.2.2) : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × Orb D.δ) := by
    funext y
    rfl
  rw [e]
  exact hf.comp h2

private theorem meas_el (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ) (hf : Continuous f) :
    Measurable fun y : Y E D.δ => f (el D y) := by
  have h1 : Measurable fun p : ↥(IdeleGroup.normOneSubgroup E) × G1 E => f (gl p.2 * sZ D (p.1 : IdeleGroup E)) :=
    (hf.comp (cont_el D)).measurable
  have e : (fun y : Y E D.δ => f (el D y)) = (fun p : ↥(IdeleGroup.normOneSubgroup E) × G1 E =>
      f (gl p.2 * sZ D (p.1 : IdeleGroup E))) ∘ fun y : Y E D.δ =>
      ((y.1, y.2.1) : ↥(IdeleGroup.normOneSubgroup E) × G1 E) := by
    funext y
    rfl
  rw [e]
  exact h1.comp (meas_proj D.δ)

private theorem fin_int (D : Dat ℚ E) (N : MeasE E) (f : GL (Fin 2) (A E) → ℂ) (hf : Continuous f)
    (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (hK : IsCompact K) (n : ℕ) (B : ℝ)
    (hB : ∀ z ∈ normOneFundamentalDomain E, ∀ h : G1 E,
      (Summable fun ξ : Fin 4 → ℚ => wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ))) ∧
      (∑' ξ : Fin 4 → ℚ, wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ))) *
        ‖f (gl h * sZ D (z : IdeleGroup E))‖ ≤ B) :
    Integrable (fun y => (wt K n (pY D y) : ℂ) * f (el D y)) (mY D.δ N) := by
  haveI : MeasurableSingletonClass (Orb D.δ) := ⟨fun _ => trivial⟩
  have hwm : Measurable fun y : Y E D.δ => wt K n (pY D y) := (wt_meas K hK n).comp (meas_pY D)
  have hwc : Measurable fun y : Y E D.δ => ((wt K n (pY D y) : ℝ) : ℂ) := Complex.measurable_ofReal.comp hwm
  have hm : Measurable fun y : Y E D.δ => ((wt K n (pY D y) : ℝ) : ℂ) * f (el D y) := hwc.mul (meas_el D f hf)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  obtain ⟨hZ, hDz, -⟩ := zDom E
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hZ⟩
  haveI : IsFiniteMeasure (N.μ.restrict N.D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volE E N⟩
  let g : Y E D.δ → ℝ≥0∞ := fun y => ‖((wt K n (pY D y) : ℝ) : ℂ) * f (el D y)‖ₑ
  have hg : Measurable g := hm.enorm
  have key : ∀ z ∈ normOneFundamentalDomain E, ∀ h : G1 E,
      ∫⁻ ξ : Orb D.δ, g (z, (h, ξ)) ∂Measure.count ≤ ENNReal.ofReal B := by
    intro z hz h
    obtain ⟨hs, hb⟩ := hB z hz h
    rw [lintegral_count]
    let wq : (Fin 4 → ℚ) → ℝ := fun ξ => wt K n (D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ)) *
      ‖f (gl h * sZ D (z : IdeleGroup E))‖
    have e : ∀ ξ : Orb D.δ, g (z, (h, ξ)) = ENNReal.ofReal (wq ξ.1) := by
      intro ξ
      have e1 : pY D (z, (h, ξ)) = D.act (gl h * sZ D (z : IdeleGroup E))⁻¹ (rp ξ.1) := rfl
      have e2 : el D (z, (h, ξ)) = gl h * sZ D (z : IdeleGroup E) := rfl
      simp only [g, wq]
      rw [e1, e2, ← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (wt_nonneg' _ _ _)]
    calc _ = ∑' ξ : Orb D.δ, ENNReal.ofReal (wq ξ.1) := tsum_congr e
      _ ≤ ∑' ξ : Fin 4 → ℚ, ENNReal.ofReal (wq ξ) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun ξ => ENNReal.ofReal (wq ξ)
      _ = ENNReal.ofReal (∑' ξ : Fin 4 → ℚ, wq ξ) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg (wt_nonneg' _ _ _) (norm_nonneg _))
            (hs.mul_right _)).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (by simp only [wq]; rw [tsum_mul_right]; exact hb)
  have hmY : mY D.δ N = ((normOneMeasure E).restrict (normOneFundamentalDomain E)).prod
      ((N.μ.restrict N.D).prod Measure.count) := rfl
  have hfin : ∫⁻ y, g y ∂mY D.δ N < ⊤ := by
    rw [hmY, lintegral_prod _ hg.aemeasurable]
    have hle : ∫⁻ z, ∫⁻ p, g (z, p)
          ∂((N.μ.restrict N.D).prod Measure.count) ∂((normOneMeasure E).restrict (normOneFundamentalDomain E)) ≤
        ∫⁻ _, ENNReal.ofReal B * (N.μ.restrict N.D) Set.univ
          ∂((normOneMeasure E).restrict (normOneFundamentalDomain E)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem hDz] with z hz
      have hgz : Measurable fun p : G1 E × Orb D.δ => g (z, p) := hg.comp measurable_prodMk_left
      rw [lintegral_prod (fun p : G1 E × Orb D.δ => g (z, p)) hgz.aemeasurable]
      calc _ ≤ ∫⁻ _, ENNReal.ofReal B ∂(N.μ.restrict N.D) := lintegral_mono fun h => key z hz h
        _ = _ := lintegral_const _
    refine hle.trans_lt ?_
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)) (measure_lt_top _ _)
  exact hfin

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.yInt :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.YInt := by
  intro E _ _ _ D W M N P φ hφ
  have hφc : Continuous φ.1 := (decE E P φ hφ).1.1
  refine ⟨meas_pY D, meas_el D φ.1 hφc, fun K hK => ?_⟩
  obtain ⟨n, B, hB⟩ := bound E D P φ hφ K hK
  exact ⟨n, fin_int D N φ.1 hφc K hK n B hB⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.GaloisBaseChangeSchemeActionCompSnd
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
open scoped Classical ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private noncomputable def hoD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : G1 F ≃ₜ G1 F :=
  ⟨⟨cD t, cD t⁻¹, fun g => by rw [← cD_mul_left, inv_mul_cancel, cD_one_left],
      fun g => by rw [← cD_mul_left, mul_inv_cancel, cD_one_left]⟩,
    M.continuous_cD t, M.continuous_cD t⁻¹⟩

private theorem emb_cD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : MeasurableEmbedding (cD t : G1 F → G1 F) :=
  (hoD t).measurableEmbedding

private noncomputable def tau {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (z : (A E)ˣ) : (A E)ˣ :=
  Units.map ((am E : A ℚ →+* A E) : A ℚ →* A E) (ideleNorm ℚ E z)

private theorem em_dM {E : Type} [Field E] [NumberField E] (t : (A ℚ)ˣ) :
    em E (dM t) = dM (Units.map ((am E : A ℚ →+* A E) : A ℚ →* A E) t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [em, dM, Matrix.GeneralLinearGroup.map]

private theorem gl_scalarCenter_commute {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ) (u : G1 E) :
    gl u * sZ D z = sZ D z * gl (cD (tau z) u) := by
  obtain ⟨-, -, -, -, -, -, -, -, hsc, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  have e : em E (dM (ideleNorm ℚ E z)⁻¹) = (dM (tau z))⁻¹ := by
    rw [em_dM, map_inv, dM_inv]; rfl
  rw [hsc, e, gl_cD]
  rw [← mul_assoc, ← UpperTheory.ConvolutionTheory.R2.scalar_comm z (gl u)]
  group

private theorem cD_j {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ)
    (j : G1 ℚ →* G1 E) (hj : ∀ g, gl (j g) = em E (gl g)) (g : G1 ℚ) :
    cD (tau z) (j (cD (ideleNorm ℚ E z)⁻¹ g)) = j g := by
  obtain ⟨-, -, -, -, -, -, -, hc, -, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  apply gl_injective
  have h1 := gl_scalarCenter_commute D z (j (cD (ideleNorm ℚ E z)⁻¹ g))
  rw [hj, ← hc, ← hj] at h1
  exact (mul_left_cancel h1).symm

private theorem galoisBaseChangeSchemeAction_comp_snd {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (z : (A E)ˣ) (h u r : G1 E)
    (huh : h = r * u) :
    D.act (gl h * sZ D z)⁻¹ (D.act (gl r) (rp X0)) = D.act (gl (cD (tau z) u))⁻¹ (rp X0) := by
  obtain ⟨-, -, -, -, ha, -, -, -, -, -, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  have h0 : D.act (sZ D z)⁻¹ (rp X0) = rp X0 := by
    conv_lhs => rw [← ha z]
    exact D.act_inv_act _ _
  subst huh
  rw [← D.act_mul, gl_mul, mul_assoc, gl_scalarCenter_commute D z u]
  have : (gl r * (sZ D z * gl (cD (tau z) u)))⁻¹ * gl r = (gl (cD (tau z) u))⁻¹ * (sZ D z)⁻¹ := by group
  rw [this, D.act_mul, h0]

private theorem pY_eq {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (z : ↥(IdeleGroup.normOneSubgroup E)) (p : G1 E × Orb D.δ) :
    pY D (z, p) = D.act (gl p.1 * sZ D (z : IdeleGroup E))⁻¹ (rp p.2.1) := rfl

private theorem el_eq {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (z : ↥(IdeleGroup.normOneSubgroup E)) (p : G1 E × Orb D.δ) :
    el D (z, p) = gl p.1 * sZ D (z : IdeleGroup E) := rfl

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.zOne :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.ZOne := by
  intro E _ _ _ D W M N P φ hφ j hj c hc hcs Ψ hΨ z
  obtain ⟨j', r, hj', hjc, hji, hr, hjΓ, hu⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.reps E D
  have hjj : j' = j := MonoidHom.ext fun g => gl_injective ((hj' g).trans (hj g).symm)
  subst hjj
  haveI := N.haar
  haveI := N.right
  haveI := M.haar
  haveI := M.right
  haveI : DiscreteMeasurableSpace (Orb D.δ) := ⟨fun _ => trivial⟩
  haveI : Countable (Orb D.δ) := inferInstance
  obtain ⟨hcont, hleft⟩ := (UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ).1
  simp only [pY_eq, el_eq]
  generalize ((z : IdeleGroup E) : (A E)ˣ) = zz
  have hmpE : MeasurePreserving (cD (tau zz)) N.μ N.μ := (UpperTheory.ConvolutionTheory.RankTwoDescent.invE E N).1 _
  have hmpQ : MeasurePreserving (cD (ideleNorm ℚ E zz)⁻¹ : G1 ℚ → G1 ℚ) M.μ M.μ := UpperTheory.ConvolutionTheory.R2.M.cdMeas ℚ M _
  have hq : ∀ F : G1 ℚ → ℂ, ∫ g, F (cD (ideleNorm ℚ E zz)⁻¹ g) ∂M.μ = ∫ g, F g ∂M.μ :=
    fun F => hmpQ.integral_comp (emb_cD _) F
  obtain ⟨cs, hcsd⟩ : ∃ cs : G1 E → ℂ, ∀ y, cs y = c (cD (tau zz) y) := ⟨_, fun _ => rfl⟩
  obtain ⟨f, hfd⟩ : ∃ f : G1 E → ℂ, ∀ x, f x = φ.1 (gl x * sZ D zz) := ⟨_, fun _ => rfl⟩
  have hcsC : Continuous cs := by
    rw [show cs = c ∘ cD (tau zz) from funext hcsd]
    exact hc.comp (UpperTheory.ConvolutionTheory.R2.M.continuous_cD _)
  have hfC : Continuous f := by
    rw [show f = fun x => φ.1 (gl x * sZ D zz) from funext hfd]
    exact hcont.comp (continuous_gl.mul continuous_const)
  have hcsS : HasCompactSupport cs := by
    rw [show cs = c ∘ hoD (tau zz) from funext hcsd]
    exact hcs.comp_homeomorph _
  have hΨ' : ∀ (h : G1 E) (ξ : Orb D.δ), Ψ (D.act (gl h * sZ D zz)⁻¹ (rp ξ.1)) = ∫ g, cs (j' g * ((r ξ)⁻¹ * h)) ∂M.μ := by
    intro h ξ
    have e1 : D.act (gl h * sZ D zz)⁻¹ (rp ξ.1) = D.act (gl (cD (tau zz) ((r ξ)⁻¹ * h)))⁻¹ (rp X0) := by
      rw [(hr ξ).2]
      exact galoisBaseChangeSchemeAction_comp_snd D zz h _ (r ξ) (by group)
    rw [e1, hΨ, ← hq fun g => cs (j' g * ((r ξ)⁻¹ * h))]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hcsd]
    rw [UpperTheory.ConvolutionTheory.R2.cD_mul _ (j' _) _, cD_j D zz j' hj' g]
  have hB : ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B := by
    obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.bddE E P φ hφ {sZ D zz} isCompact_singleton
    exact ⟨B, fun x => by rw [hfd]; exact hB x _ rfl⟩
  have hinv : ∀ γ ∈ Gam E, ∀ x, f (γ * x) = f x := by
    rintro _ ⟨γ, rfl⟩ x
    rw [hfd, hfd, gl_mul, gl_ratS, mul_assoc, hleft]
  obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.absUnf (G1 E) (G1 ℚ) (Orb D.δ) N.μ M.μ j' (Gam E) (Gam ℚ) N.D M.D r f cs hjc hji N.fund M.fund
    (UpperTheory.ConvolutionTheory.R2.M.volD ℚ M) (fun i => (hr i).1) hjΓ hu hfC.measurable hinv hB hcsC.measurable (hcsC.integrable_of_hasCompactSupport hcsS)
  have hL : ∀ p : G1 E × Orb D.δ, Ψ (D.act (gl p.1 * sZ D zz)⁻¹ (rp p.2.1)) * φ.1 (gl p.1 * sZ D zz) =
      (∫ g, cs (j' g * ((r p.2)⁻¹ * p.1)) ∂M.μ) * f p.1 := by
    rintro ⟨h, ξ⟩
    rw [hΨ', hfd]
  refine ⟨fun B hBB => ?_, ?_⟩
  · simp only [hL]
    refine (h1 B (fun h => by rw [hfd]; exact hBB h)).trans_eq ?_
    rw [show (∫⁻ y, ‖cs y‖ₑ ∂N.μ) = ∫⁻ y, ‖c y‖ₑ ∂N.μ by
      simp only [hcsd]; exact hmpE.lintegral_comp_emb (emb_cD _) fun y => ‖c y‖ₑ]
  · simp only [hL]
    rw [h2]
    have := hmpE.integral_comp (emb_cD (tau zz)) fun y => c y * SLP M fun x => φ.1 (x * sZ D zz * gl y)
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hcsd, SLP]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hfd]
    rw [gl_mul, hj', mul_assoc, gl_scalarCenter_commute D zz y, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerContAlt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

variable {E : Type} [Field E] [NumberField E]

private theorem continuous_em : Continuous (em E) := by
  have hM : Continuous ((AdeleBaseChange.adeleMap ℚ E).mapMatrix.toMonoidHom :
      Matrix (Fin 2) (Fin 2) (A ℚ) → Matrix (Fin 2) (Fin 2) (A E)) :=
    continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap
  exact Continuous.units_map _ hM

private theorem secondCountable_gl : SecondCountableTopology (GL (Fin 2) (A E)) := by
  haveI : SecondCountableTopology (A E) := GroundTheory.Automorphic.secondCountableTopology_adeleRing E
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (A E)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A E))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (A E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem continuous_inner (M : Meas ℚ) {f : GL (Fin 2) (A E) → ℂ} (hf : Continuous f)
    (hb : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ B : ℝ, ∀ g : G1 ℚ, ∀ k ∈ C, ‖f (em E (gl g) * k)‖ ≤ B) :
    Continuous fun k : GL (Fin 2) (A E) => ∫ g in M.D, f (em E (gl g) * k) ∂M.μ := by
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  haveI := secondCountable_gl (E := E)
  haveI : FirstCountableTopology (GL (Fin 2) (A E)) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  have hin : ∀ k, Continuous fun g : G1 ℚ => f (em E (gl g) * k) := fun k =>
    hf.comp ((continuous_em.comp Matrix.SpecialLinearGroup.continuous_toGL).mul continuous_const)
  rw [continuous_iff_continuousAt]
  intro k₀
  obtain ⟨C, hC, hk⟩ := exists_compact_mem_nhds k₀
  obtain ⟨B, hB⟩ := hb C hC
  refine continuousAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
  · exact Eventually.of_forall fun k => (hin k).aestronglyMeasurable
  · filter_upwards [hk] with k hkC
    exact ae_of_all _ fun g => hB g k hkC
  · exact ae_of_all _ fun g => (hf.comp (continuous_const.mul continuous_id)).continuousAt

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.perCont :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.PerCont := by
  intro E _ _ _ D W M N P φ hφ
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E 2 φ (P.cusp φ hφ).1.level
  obtain ⟨j, r, hj, -⟩ := reps E D
  have hbd : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C →
      ∃ B : ℝ, ∀ g : G1 ℚ, ∀ k ∈ C, ‖φ.1 (em E (gl g) * k)‖ ≤ B := by
    intro C hC
    obtain ⟨B, hB⟩ := bddE E P φ hφ C hC
    exact ⟨B, fun g k hk => by rw [← hj g]; exact hB (j g) k hk⟩
  have hΦ := continuous_inner M hc hbd
  set Φ : GL (Fin 2) (A E) → ℂ := fun k => ∫ g in M.D, φ.1 (em E (gl g) * k) ∂M.μ with hΦdef
  obtain ⟨hfin, hmeas, CZ, hCZ, hmem⟩ := zDom E
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by simpa using hfin⟩
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  have hs : Continuous (sZ D) := (szLaws E D).2.1
  have hsz : Continuous fun z : ↥(IdeleGroup.normOneSubgroup E) => sZ D (z : IdeleGroup E) :=
    hs.comp continuous_subtype_val
  have key : ∀ h : G1 E, (UPer D M fun x => φ.1 (x * gl h)) =
      ∫ z in normOneFundamentalDomain E, Φ (sZ D (z : IdeleGroup E) * gl h) ∂normOneMeasure E := by
    intro h
    simp only [UPer, UI, SLP, hΦdef, mul_assoc]
  simp only [key]
  rw [continuous_iff_continuousAt]
  intro h₀
  obtain ⟨K, hK, hh⟩ := exists_compact_mem_nhds h₀
  have hglc : Continuous (gl : G1 E → GL (Fin 2) (A E)) := Matrix.SpecialLinearGroup.continuous_toGL
  have hCc : IsCompact ((fun p : (A E)ˣ × G1 E => sZ D p.1 * gl p.2) '' (CZ ×ˢ K)) :=
    (hCZ.prod hK).image ((hs.comp continuous_fst).mul (hglc.comp continuous_snd))
  obtain ⟨B, hB⟩ := hbd _ hCc
  refine continuousAt_of_dominated (bound := fun _ => B * (M.μ.restrict M.D).real Set.univ) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun h =>
      (hΦ.comp (hsz.mul continuous_const)).aestronglyMeasurable
  · filter_upwards [hh] with h hhK
    refine ae_restrict_of_forall_mem hmeas fun z hz => ?_
    exact norm_integral_le_of_norm_le_const (ae_of_all _ fun g =>
      hB g _ ⟨(((z : IdeleGroup E) : (A E)ˣ), h), ⟨hmem z hz, hhK⟩, rfl⟩)
  · exact ae_of_all _ fun z =>
      (hΦ.comp (continuous_const.mul hglc)).continuousAt
end

