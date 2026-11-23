module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NormChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.HomCommTrivial
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ElementarySubgroupInvariance

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharDown
section
open NumberField IsDedekindDomain
open Formalism.L2.Host GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

theorem charDown : CharDown := by
  intro E _ _ _ D χ h
  have hE : Module.finrank ℚ E = 2 := by
    rw [Module.finrank_eq_card_basis D.b]
    simp
  have hθ : D.θ ≠ 0 := by
    rw [← D.b1]
    exact D.b.ne_zero 1
  have hσ : D.σ ≠ 1 := by
    intro h1
    have h2 := D.conj
    rw [h1] at h2
    have h3 : D.θ = -D.θ := by simpa using h2
    have h4 : (2 : E) * D.θ = 0 := by linear_combination h3
    exact hθ (by simpa using h4)
  refine A.normChar_of_inv hE χ fun c z => ?_
  rcases GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two D.σ hE hσ c with rfl | rfl
  · rw [one_smul]
  · have h1 := h z
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    have h2 : Units.map (D.bar : A E →* A E) z = D.σ • z := Units.ext (coe_smul_idele D.σ z).symm
    rw [← h2]
    exact h1.symm

end UpperTheory.ConvolutionTheory.RankTwoDescent
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharInt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily

private theorem char_int (r : ℚ) (hr : r ≠ 0) :
    ∫ b in fundamentalSet ℚ, ψ (b * rt r) ∂(adeleMeasure ℚ) = 0 := by
  obtain ⟨x, hx⟩ : ∃ x : A ℚ, adelicChar ℚ x ≠ 1 := by
    by_contra h
    push_neg at h
    exact adelicChar_ne_one (K := ℚ) (DFunLike.ext _ _ fun x => by simpa using h x)
  have hx' : ψ x ≠ 1 := fun h => hx (Circle.ext (by simpa [ψ] using h))
  have hper : ∀ (k : ℚ) (y : A ℚ), ψ ((rt k + y) * rt r) = ψ (y * rt r) := by
    intro k y
    rw [add_mul, Pp.ψ_add, ← map_mul, Pp.ψ_rt, one_mul]
  have h := Pp.int_add (F := ℚ) (h := fun b => ψ (b * rt r)) hper (rt r⁻¹ * x)
  have hrr : rt r⁻¹ * rt r = (1 : A ℚ) := by rw [← map_mul, inv_mul_cancel₀ hr, map_one]
  have e : ∀ b : A ℚ, ψ ((b + rt r⁻¹ * x) * rt r) = ψ (b * rt r) * ψ x := by
    intro b
    rw [add_mul, Pp.ψ_add, mul_right_comm, hrr, one_mul]
  simp only [e] at h
  rw [integral_mul_const] at h
  have h1 : (∫ b in fundamentalSet ℚ, ψ (b * rt r) ∂(adeleMeasure ℚ)) * (ψ x - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hx')

private theorem vol_one : (adeleMeasure ℚ).real (fundamentalSet ℚ) = 1 := by
  rw [measureReal_def, adeleMeasure_fundamentalSet, ENNReal.toReal_one]

private theorem fourier (S T : Set (Fin 4 → ℚ)) (q : (Fin 4 → ℚ) → ℚ) (t : ℚ) (c : (Fin 4 → ℚ) → ℂ)
    (hT : ∀ ξ, ξ ∈ T ↔ ξ ∈ S ∧ q ξ = t) (hc : Summable fun ξ : S => ‖c ξ‖) :
    ∫ b in fundamentalSet ℚ, (∑' ξ : S, ψ (b * rt (q ξ)) * c ξ) * ψ (-(b * rt t)) ∂(adeleMeasure ℚ) =
      ∑' ξ : T, c ξ := by
  have hvol : ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]
  haveI : IsProbabilityMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) := ⟨hvol⟩
  set G : S → A ℚ → ℂ := fun ξ b => ψ (b * rt (q ξ - t)) * c ξ with hG
  have hGc : ∀ ξ, Continuous (G ξ) := fun ξ =>
    (Pp.cont_ψ.comp (continuous_id.mul continuous_const)).mul continuous_const
  have hGn : ∀ ξ b, ‖G ξ b‖ = ‖c ξ‖ := fun ξ b => by simp [hG, Pp.norm_ψ]
  have e : ∀ b : A ℚ, (∑' ξ : S, ψ (b * rt (q ξ)) * c ξ) * ψ (-(b * rt t)) = ∑' ξ, G ξ b := by
    intro b
    rw [← tsum_mul_right]
    refine tsum_congr fun ξ => ?_
    have h0 : rt (q ξ - t) = rt (q ξ) - rt t := map_sub (algebraMap ℚ (A ℚ)) _ _
    have : b * rt (q ξ - t) = b * rt (q ξ) + -(b * rt t) := by
      rw [h0, mul_sub, sub_eq_add_neg]
    simp only [hG, this, Pp.ψ_add]
    ring
  simp only [e]
  have hS := hasSum_integral_of_summable_integral_norm (μ := (adeleMeasure ℚ).restrict (fundamentalSet ℚ))
    (F := G) (fun ξ => Pp.intOn (hGc ξ)) (by
      simp only [hGn, integral_const, probReal_univ, one_smul]
      exact hc)
  rw [← hS.tsum_eq]
  have term : ∀ ξ : S, ∫ b in fundamentalSet ℚ, G ξ b ∂(adeleMeasure ℚ) = T.indicator c ξ := by
    intro ξ
    simp only [hG]
    rw [integral_mul_const]
    by_cases h : q ξ = t
    · have hm : (ξ : Fin 4 → ℚ) ∈ T := (hT _).2 ⟨ξ.2, h⟩
      simp [h, hm, Set.indicator_of_mem, measureReal_def, hvol]
    · have hm : (ξ : Fin 4 → ℚ) ∉ T := fun hm => h ((hT _).1 hm).2
      rw [char_int _ (sub_ne_zero.2 h), zero_mul, Set.indicator_of_notMem hm]
  simp only [term]
  rw [tsum_subtype S (T.indicator c), tsum_subtype T c]
  refine tsum_congr fun ξ => ?_
  by_cases h : ξ ∈ T
  · simp [h, ((hT _).1 h).1]
  · by_cases h' : ξ ∈ S <;> simp [h, h']

private theorem swap3 {B Z H : Type} [MeasurableSpace B] [MeasurableSpace Z] [MeasurableSpace H]
    (m : Measure B) (μ₁ : Measure Z) (μ₂ : Measure H) [IsFiniteMeasure m] [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (f : B → Z → H → ℂ) (hf : AEStronglyMeasurable (fun p : B × Z × H => f p.1 p.2.1 p.2.2) (m.prod (μ₁.prod μ₂)))
    (C : ℝ) (hb : ∀ᵐ z ∂μ₁, ∀ b h, ‖f b z h‖ ≤ C) :
    ∫ b, ∫ z, ∫ h, f b z h ∂μ₂ ∂μ₁ ∂m = ∫ z, ∫ h, ∫ b, f b z h ∂m ∂μ₂ ∂μ₁ := by
  have hae : ∀ᵐ p ∂(m.prod (μ₁.prod μ₂)), ‖f p.1 p.2.1 p.2.2‖ ≤ C := by
    have h1 : ∀ᵐ p ∂(μ₁.prod μ₂), ∀ b h, ‖f b p.1 h‖ ≤ C := Measure.quasiMeasurePreserving_fst.ae hb
    have h2 : ∀ᵐ p ∂(m.prod (μ₁.prod μ₂)), ∀ b h, ‖f b p.2.1 h‖ ≤ C := Measure.quasiMeasurePreserving_snd.ae h1
    exact h2.mono fun p hp => hp _ _
  have hF : Integrable (fun p : B × Z × H => f p.1 p.2.1 p.2.2) (m.prod (μ₁.prod μ₂)) :=
    Integrable.of_bound hf C hae
  have s1 : ∫ b, ∫ z, ∫ h, f b z h ∂μ₂ ∂μ₁ ∂m = ∫ b, ∫ p : Z × H, f b p.1 p.2 ∂(μ₁.prod μ₂) ∂m := by
    refine integral_congr_ae (hF.prod_right_ae.mono fun b hb' => ?_)
    exact (integral_prod _ hb').symm
  have s2 : ∫ b, ∫ p : Z × H, f b p.1 p.2 ∂(μ₁.prod μ₂) ∂m = ∫ p : Z × H, ∫ b, f b p.1 p.2 ∂m ∂(μ₁.prod μ₂) :=
    integral_integral_swap (f := fun b (p : Z × H) => f b p.1 p.2) hF
  rw [s1, s2]
  exact integral_prod (fun p : Z × H => ∫ b, f b p.1 p.2 ∂m) hF.integral_prod_right

end UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily

open UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily in
private theorem coefOf (hV : VolE) :
    Maj → ThCont → Coef := by
  intro hMaj hTh E _ _ _ D W M N P ph hph φ hφ t g
  obtain ⟨hs1, hsc, hnz, hng, -, -, -, -, -, -, hq⟩ := szLaws E D
  obtain ⟨b₀, a₀, k₀, hk₀, rfl⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa ℚ g
  have hφc : Continuous φ.1 := by
    obtain ⟨ψ', hψ'⟩ := LinearMap.mem_range.mp (UpperTheory.V.Cm.mem_range_ofCusp.2 (P.cusp φ hφ))
    rw [← hψ']
    exact ψ'.2.1.continuous
  have hzc : Continuous fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E) :=
    hsc.comp continuous_subtype_val
  have hCc := (isCompact_closure_normOneFundamentalDomain E).image hzc
  have hCn : ∀ k ∈ (fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E)) '' closure (normOneFundamentalDomain E),
      nu ℚ k = 1 := by
    rintro _ ⟨u, -, rfl⟩
    exact hnz _
  have hapos : 0 < ab a₀ := (IdeleGroup.ideleModule ℚ a₀).2
  obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ _ hCc hCn (ab a₀) hapos 0
  set S : Set (Fin 4 → ℚ) := {ξ | qr D.δ ξ ≠ 0} with hS
  set T : Set (Fin 4 → ℚ) := {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = t} with hTd
  set g₀ : G1 ℚ := nU b₀ * mD a₀ * k₀ with hg₀
  let x : IdeleGroup.normOneSubgroup E → G1 E → GL (Fin 2) (A E) := fun z h => gl h * sZ D (z : IdeleGroup E)
  have hxc : Continuous fun p : IdeleGroup.normOneSubgroup E × G1 E => x p.1 p.2 := by
    have h1 : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by fun_prop
    exact (h1.comp continuous_snd).mul (hzc.comp continuous_fst)
  have hnux : ∀ z h, nu ℚ (x z h) = 1 := fun z h => by
    have : nu ℚ (x z h) = nu ℚ (gl h) * nu ℚ (sZ D (z : IdeleGroup E)) := by simp [x, nu, map_mul]
    rw [this, hng, hnz, one_mul]
  let c : IdeleGroup.normOneSubgroup E → G1 E → (Fin 4 → ℚ) → ℂ := fun z h ξ => (W.Om g₀ (W.L (x z h) ph)).1 (rp ξ)
  have hterm : ∀ b z h ξ, (W.Om (nU b * g₀) (W.L (x z h) ph)).1 (rp ξ) = ψ (b * rt (qr D.δ ξ)) * c z h ξ := by
    intro b z h ξ
    rw [map_mul, Module.End.mul_apply, W.Om_n, hq]
  have hmaj := fun (b : A ℚ) (z : IdeleGroup.normOneSubgroup E) (hz : z ∈ normOneFundamentalDomain E) (h : G1 E) =>
    hB b a₀ k₀ hk₀ le_rfl h (sZ D (z : IdeleGroup E)) ⟨z, subset_closure hz, rfl⟩
  have hsum : ∀ z ∈ normOneFundamentalDomain E, ∀ h, Summable fun ξ : S => ‖c z h ξ‖ := fun z hz h =>
    (hmaj b₀ z hz h).1.subtype (fun ξ => ξ ∈ S)
  have hnU : ∀ b, nU (b + b₀) * mD a₀ * k₀ = nU b * g₀ := by
    intro b
    rw [UpperTheory.ConvolutionTheory.R2.M.nU_add]
    simp only [hg₀, mul_assoc]
  let T' : A ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ := fun b z h =>
    ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1 * φ.1 (x z h)
  let f : A ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ := fun b z h => T' b z h * ψ (-(b * rt t))
  have hbd : ∀ z ∈ normOneFundamentalDomain E, ∀ b h, ‖f b z h‖ ≤ B := by
    intro z hz b h
    have h1 := (hmaj (b + b₀) z hz h).1
    have h3 := (hmaj (b + b₀) z hz h).2.2
    simp only [hnU, pow_zero, mul_one] at h1 h3
    have h2 : ‖ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1‖ ≤
        ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, ‖(W.Om (nU b * g₀) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 (rp ξ.1)‖ :=
      norm_tsum_le_tsum_norm (h1.subtype (fun ξ => ξ ∈ S))
    calc ‖f b z h‖ = ‖ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1‖ * ‖φ.1 (x z h)‖ := by
          simp only [f, T', norm_mul, Pp.norm_ψ, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ B := h3
  have hNc : Continuous fun b : A ℚ => nU b := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    fin_cases i <;> fin_cases j <;> simp [nU] <;> fun_prop
  have hcont : Continuous fun p : A ℚ × IdeleGroup.normOneSubgroup E × G1 E => f p.1 p.2.1 p.2.2 := by
    have hp : Continuous fun p : A ℚ × IdeleGroup.normOneSubgroup E × G1 E => (nU p.1 * g₀, x p.2.1 p.2.2) :=
      ((hNc.comp continuous_fst).mul continuous_const).prodMk (hxc.comp continuous_snd)
    have h1 := (hTh E D W M N P ph hph S).comp_continuous hp (fun p => hnux _ _)
    exact (h1.mul (hφc.comp (hxc.comp continuous_snd))).mul
      (Pp.cont_ψ.comp ((continuous_fst.mul continuous_const).neg))
  haveI : IsFiniteMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) :=
    ⟨by rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top E⟩
  haveI : IsFiniteMeasure (N.μ.restrict N.D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hV E N⟩
  have step : ∀ b, fOn W N S ph φ.1 (nU b * g₀) * ψ (-(b * rt t)) =
      ∫ z in normOneFundamentalDomain E, ∫ h in N.D, f b z h ∂N.μ ∂normOneMeasure E := by
    intro b
    change (∫ z in normOneFundamentalDomain E, ∫ h in N.D, T' b z h ∂N.μ ∂normOneMeasure E) * _ = _
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    exact (integral_mul_const _ _).symm
  simp only [step]
  rw [swap3 _ _ _ f hcont.aestronglyMeasurable B
    (ae_restrict_of_forall_mem (measurableSet_normOneFundamentalDomain E) hbd), vol_one, Complex.ofReal_one, one_mul]
  change _ = ∫ z in normOneFundamentalDomain E, ∫ h in N.D, ThOn T (W.Om g₀ (W.L (x z h) ph)).1 * φ.1 (x z h) ∂N.μ ∂normOneMeasure E
  refine setIntegral_congr_fun (measurableSet_normOneFundamentalDomain E) fun z hz => ?_
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  have e : ∀ b, f b z h = ((∑' ξ : S, ψ (b * rt (qr D.δ ξ)) * c z h ξ) * ψ (-(b * rt t))) * φ.1 (x z h) := by
    intro b
    simp only [f, T', ThOn, hterm]
    ring
  simp only [e]
  rw [integral_mul_const, fourier S T (qr D.δ) t (c z h) (fun ξ => Iff.rfl) (hsum z hz h)]
  rfl

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.coef :
    Maj → ThCont → Coef :=
  coefOf volE
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CoefZero
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent
open GroundTheory.Automorphic.FourierWhittaker

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.VanishingCoefficients

variable {E : Type} [Field E] [NumberField E]

private theorem vn (q : A E) : (nU q).val = !![1, q; 0, 1] := rfl

private theorem n_add (x y : A E) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem n_zero : gl (nU (0 : A E)) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn]

private theorem cont_n : Continuous fun q : A E => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q =>
      inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, n_zero])
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

private theorem rat_n (k : E) : ∃ γ : GL (Fin 2) E, ratGL E 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap E (A E) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

private theorem rat_w : ∃ γ : GL (Fin 2) E, ratGL E 2 γ = gl (wW E) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap E (A E) (!![0, 1; -1, 0] i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (A E)) i j
  fin_cases i <;> fin_cases j <;> simp

private theorem ψ_add (x y : A ℚ) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]

private theorem ψ_rt (k : ℚ) : ψ (rt k) = 1 := by simp [ψ, adelicChar_algebraMap]

private theorem n_aE (t : (A E)ˣ) (y : A E) : gl (nU ((t : A E) * y)) * aE t = aE t * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, aE, Matrix.mul_apply, Fin.sum_univ_two]

private def Fh (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) (x : Fin 2 → A ℚ) : ℂ :=
  Φ (gl (nU (D.mkE (x 0) (x 1))) * h)

private theorem cont_Fh (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hΦ : Continuous Φ) (h : GL (Fin 2) (A E)) :
    Continuous (Fh D Φ h) :=
  hΦ.comp ((cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))).mul continuous_const)

private theorem per_Fh (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) : ∀ l ∈ vecLattice ℚ (Fin 2), ∀ x, Fh D Φ h (l + x) = Fh D Φ h x := by
  intro l hl x
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hl
  obtain ⟨γ, hγ⟩ := rat_n (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ)
  simp only [Fh, Pi.add_apply]
  rw [D.mkE_add, n_add]
  change Φ (gl (nU (D.mkE (rt (η 0)) (rt (η 1)))) * gl (nU (D.mkE (x 0) (x 1))) * h) = _
  rw [D.mkE_rt, ← hγ, mul_assoc, hL]

private theorem lin_ne (D : Dat ℚ E) {a b : ℚ} (h : a ≠ 0 ∨ b ≠ 0) : algebraMap ℚ E a + algebraMap ℚ E b * D.θ ≠ 0 := by
  intro h0
  have h1 : algebraMap ℚ E a - algebraMap ℚ E b * D.θ = 0 := by
    have e := congrArg D.σ h0
    simpa [D.conj, sub_eq_add_neg] using e
  have ha : algebraMap ℚ E a = 0 := by linear_combination (h0 + h1) / 2
  have hb : algebraMap ℚ E b * D.θ = 0 := by linear_combination (h0 - h1) / 2
  have inj := (algebraMap ℚ E).injective
  rcases h with h | h
  · exact h (inj (by rw [ha, map_zero]))
  · refine h (inj ?_)
    rw [map_zero]
    exact (mul_eq_zero.1 hb).resolve_right D.θ_ne_zero

private theorem norm_ne (D : Dat ℚ E) {a b : ℚ} (h : a ≠ 0 ∨ b ≠ 0) : a * a - D.δ * b * b ≠ 0 := by
  intro h0
  have e : (algebraMap ℚ E a + algebraMap ℚ E b * D.θ) * (algebraMap ℚ E a + algebraMap ℚ E (-b) * D.θ) =
      algebraMap ℚ E (a * a - D.δ * b * b) := by
    have hs := D.sq
    simp only [map_sub, map_mul, map_neg]
    linear_combination (-(algebraMap ℚ E b) ^ 2) * hs
  rw [h0, map_zero] at e
  exact mul_ne_zero (lin_ne D h) (lin_ne D (a := a) (b := -b) (by simpa using h)) e

private theorem mat0 (a b d : ℚ) (x : Fin 2 → A ℚ) :
    matVec !![a, d; b, a] x 0 = UpperTheory.ConvolutionTheory.R2.rt a * x 0 + UpperTheory.ConvolutionTheory.R2.rt d * x 1 := by
  rw [matVec_apply, Fin.sum_univ_two]; rfl

private theorem mat1 (a b d : ℚ) (x : Fin 2 → A ℚ) :
    matVec !![a, d; b, a] x 1 = UpperTheory.ConvolutionTheory.R2.rt b * x 0 + UpperTheory.ConvolutionTheory.R2.rt a * x 1 := by
  rw [matVec_apply, Fin.sum_univ_two]; rfl

private def Gh (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) (u : Fin 2 → A ℚ) : ℂ :=
  Fh D Φ h u * ψ (2 * u 0)

private theorem int_Gh (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) :
    ∫ x in vecDomain ℚ (Fin 2), Gh D Φ h x ∂vecMeasure ℚ (Fin 2) = WE D Φ h := rfl

private theorem per_Gh (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) : ∀ l ∈ vecLattice ℚ (Fin 2), ∀ x, Gh D Φ h (l + x) = Gh D Φ h x := by
  intro l hl x
  have e1 := per_Fh D hL h l hl x
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hl
  have e2 : (2 : A ℚ) * ((fun i => algebraMap ℚ (A ℚ) (η i)) + x) 0 = UpperTheory.ConvolutionTheory.R2.rt (2 * η 0) + 2 * x 0 := by
    simp only [UpperTheory.ConvolutionTheory.R2.rt, map_mul, map_ofNat, mul_add, Pi.add_apply]
  simp only [Gh]
  rw [e1, e2, ψ_add, ψ_rt, one_mul]

private theorem pt_id (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) (a b : ℚ) (t : (A E)ˣ) (ht : (t : A E) = D.mkE (UpperTheory.ConvolutionTheory.R2.rt a) (UpperTheory.ConvolutionTheory.R2.rt b))
    (hγ : ∃ γ, ratGL E 2 γ = aE t) (x : Fin 2 → A ℚ) :
    Gh D Φ (aE t * h) (matVec !![a, D.δ * b; b, a] x) = Fh D Φ h x * ψ (2 * (UpperTheory.ConvolutionTheory.R2.rt a * x 0 + UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) * x 1)) := by
  obtain ⟨γ, hγ⟩ := hγ
  have e : UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) = UpperTheory.ConvolutionTheory.R2.rt D.δ * UpperTheory.ConvolutionTheory.R2.rt b := map_mul _ _ _
  have k1 : D.mkE (matVec !![a, D.δ * b; b, a] x 0) (matVec !![a, D.δ * b; b, a] x 1) =
      (t : A E) * D.mkE (x 0) (x 1) := by
    rw [ht, D.mkE_mul, mat0, mat1, e]
    congr 1
    · ring
    · ring
  simp only [Gh, Fh]
  rw [k1, mat0, ← mul_assoc, n_aE, ← hγ, mul_assoc, hL]

private theorem coef_zero (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (hW : ∀ h, WE D Φ h = 0) (h : GL (Fin 2) (A E)) (ξ : Fin 2 → ℚ) (hξ : ξ ≠ 0) :
    vecCoeff (Fh D Φ h) ξ = 0 := by
  have hδ := D.δ_ne_zero
  obtain ⟨a, ha⟩ : ∃ a : ℚ, 2 * a = -ξ 0 := ⟨-ξ 0 / 2, by ring⟩
  obtain ⟨b, hb⟩ : ∃ b : ℚ, 2 * (D.δ * b) = -ξ 1 := ⟨-ξ 1 / (2 * D.δ), by field_simp⟩
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    refine hξ (funext fun i => ?_)
    fin_cases i
    · simpa [h1] using ha.symm
    · simpa [h2] using hb.symm
  obtain ⟨M, hM⟩ : ∃ M : GL (Fin 2) ℚ, (M : Matrix (Fin 2) (Fin 2) ℚ) = !![a, D.δ * b; b, a] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, D.δ * b; b, a]
      (by rw [Matrix.det_fin_two_of]; exact norm_ne D hab), rfl⟩
  obtain ⟨t, ht, hγ⟩ : ∃ t : (A E)ˣ, (t : A E) = D.mkE (UpperTheory.ConvolutionTheory.R2.rt a) (UpperTheory.ConvolutionTheory.R2.rt b) ∧ ∃ γ, ratGL E 2 γ = aE t :=
    ⟨IdeleGroup.diagonal E (Units.mk0 _ (lin_ne D hab)), (D.mkE_rt a b).symm, exists_ratGL_aE _⟩
  have h1 := setIntegral_comp_matVec M (per_Gh D hL (aE t * h))
  rw [int_Gh, hW, hM] at h1
  rw [vecCoeff, ← h1]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have k2 : (2 : A ℚ) * (UpperTheory.ConvolutionTheory.R2.rt a * x 0 + UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) * x 1) = -pair ξ x := by
    have e2 : (2 : A ℚ) = UpperTheory.ConvolutionTheory.R2.rt (2 : ℚ) := (map_ofNat _ 2).symm
    have e0 : (2 : A ℚ) * UpperTheory.ConvolutionTheory.R2.rt a = -UpperTheory.ConvolutionTheory.R2.rt (ξ 0) := by
      rw [← map_neg, ← ha, e2]; exact (map_mul _ _ _).symm
    have e1 : (2 : A ℚ) * UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) = -UpperTheory.ConvolutionTheory.R2.rt (ξ 1) := by
      rw [← map_neg, ← hb, e2]; exact (map_mul _ _ _).symm
    rw [pair, Fin.sum_univ_two]
    linear_combination (x 0) * e0 + (x 1) * e1
  beta_reduce
  rw [pt_id D hL h a b t ht hγ x, k2]
  rfl

private theorem n_inv (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hΦ : Continuous Φ)
    (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g) (hW : ∀ h, WE D Φ h = 0) (b : A E) (h : GL (Fin 2) (A E)) :
    Φ (gl (nU b) * h) = Φ h := by
  obtain ⟨u, v, rfl⟩ := D.exists_mkE b
  set F := Fh D Φ h with hF
  have hFc : Continuous F := cont_Fh D hΦ h
  have hFper : ∀ l ∈ vecLattice ℚ (Fin 2), ∀ x, F (l + x) = F x := per_Fh D hL h
  set a : Fin 2 → A ℚ := ![u, v] with ha
  have hTper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ x, F (ξ + x + a) = F (x + a) := fun ξ hξ x => by
    rw [add_assoc, hFper ξ hξ]
  set G : (Fin 2 → A ℚ) → ℂ := fun y => F (y + a) - F y with hG
  have hGc : Continuous G := (hFc.comp (continuous_id.add continuous_const)).sub hFc
  have hGper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ x, G (ξ + x) = G x := fun ξ hξ x => by
    simp only [hG]
    rw [hTper ξ hξ, hFper ξ hξ]
  have hint : ∀ (f : (Fin 2 → A ℚ) → ℂ), Continuous f → ∀ ξ : Fin 2 → ℚ,
      IntegrableOn (fun x => f x * (adelicChar ℚ (-pair ξ x) : ℂ)) (vecDomain ℚ (Fin 2))
        (vecMeasure ℚ (Fin 2)) := fun f hf ξ =>
    ((hf.mul (continuous_adelicChar_neg_pair ξ)).continuousOn.integrableOn_compact
      isCompact_closure_vecDomain).mono_set subset_closure
  have hcoef : ∀ ξ, vecCoeff G ξ = 0 := by
    intro ξ
    have e1 : vecCoeff G ξ = vecCoeff (fun x => F (x + a)) ξ - vecCoeff F ξ := by
      unfold vecCoeff
      refine Eq.trans ?_ (integral_sub (hint _ (hFc.comp (continuous_id.add continuous_const) :
        Continuous fun x => F (x + a)) ξ) (hint _ hFc ξ))
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show (F (x + a) - F x) * _ = F (x + a) * _ - F x * _
      ring
    rw [e1, vecCoeff_translate hFper]
    by_cases h1 : ξ = 0
    · have hp : pair ξ a = 0 := by
        simp [pair, h1]
      rw [hp, AddChar.map_zero_eq_one, Circle.coe_one, one_mul, sub_self]
    · rw [coef_zero D hL hW h ξ h1, mul_zero, sub_zero]
  have hG0 := congrFun (GlobalTheory.CompanionTheory.AdelicFourier.eq_zero_of_vecCoeff_eq_zero hGc hGper hcoef) 0
  have h1 : F (0 + a) = F 0 := sub_eq_zero.1 hG0
  have e2 : F (0 + a) = Φ (gl (nU (D.mkE u v)) * h) := by
    simp [hF, Fh, ha]
  have e3 : F 0 = Φ h := by
    simp only [hF, Fh, Pi.zero_apply]
    rw [D.mkE_zero, n_zero, one_mul]
  rw [← e2, h1, e3]

end UpperTheory.ConvolutionTheory.RankTwoDescent.VanishingCoefficients

end

open UpperTheory.ConvolutionTheory.RankTwoDescent.VanishingCoefficients in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.killW :
    KillW := by
  intro E _ _ D Φ hΦ hL hW h g
  have gm : ∀ x y : G1 E, gl (x * y) = gl x * gl y := fun _ _ => Units.ext rfl
  have g1 : gl (1 : G1 E) = 1 := Units.ext rfl
  let H : Subgroup (G1 E) :=
    { carrier := {s | ∀ g, Φ (gl s * g) = Φ g}
      mul_mem' := fun {x y} hx hy g => by
        rw [gm, mul_assoc, hx, hy]
      one_mem' := fun g => by rw [g1, one_mul]
      inv_mem' := fun {x} hx g => by
        rw [← hx (gl x⁻¹ * g), ← mul_assoc, ← gm, mul_inv_cancel, g1, one_mul] }
  have hH : H = ⊤ := eq_top_of_nU_wW H (fun b g => n_inv D hΦ hL hW b g) (fun g => by
    obtain ⟨γ, hγ⟩ := rat_w (E := E)
    rw [← hγ, hL])
  have : h ∈ H := hH ▸ Subgroup.mem_top h
  exact this g
end

