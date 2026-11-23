module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0002
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0021
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0013
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0011
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0014
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ContOn
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Nz

private theorem X_two_pi (t : ℝ) : X (t + 2 * Real.pi) = X t := by
  refine Units.ext ?_
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [X, Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem rot_per : Function.Periodic rot (2 * Real.pi) := fun t => by
  rw [rot_eq, rot_eq, X_two_pi]

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem dec_of {D : Dat ℚ E} {ω : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (h : admitted D ω φ) (r : ℕ) :
    ∃ B : ℝ, ∀ y t, y ≠ 0 → ‖Wo D φ (em E (aE (iy y) * rot t))‖ ≤ B * ((1 + |y|) ^ r)⁻¹ := by
  have hC : IsCompact (Set.range fun t => em E (rot t)) :=
    Function.Periodic.compact_of_continuous (c := 2 * Real.pi)
      (fun t => by simp only [rot_per t]) (by positivity) (cont_em.comp cont_rot)
  obtain ⟨K, -, hK⟩ := h.wdec _ hC
  obtain ⟨B, hB⟩ := hK r
  refine ⟨B, fun y t hy => ?_⟩
  have h1 := (hB (iy y) (em E (rot t)) ⟨t, rfl⟩).1
  rwa [re_iy hy, ← map_mul] at h1

private theorem pack {D : Dat ℚ E} {ω χ : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (h : admitted D ω φ)
    (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) (k : ℕ) {s : ℂ} (hs : 1 - (k : ℝ) < s.re) :
    (∀ t, Integrable fun y : ℝ => Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)) ∧
    Continuous fun t => ∫ y : ℝ, Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2) :=
  UpperTheory.integrable_and_continuous_mellinIntegral_of_rapidDecay (fun y t => Wo D φ (em E (aE (iy y) * rot t))) (fun y => ((χ.1 (iy y) : ℂˣ) : ℂ)) k s
    (contOn_Wo D h.cont h.bdd) ((Units.continuous_val.comp χ.2.1).comp_continuousOn contOn_iy) (fun y => hχ _)
    (dec_of h) hs

private theorem zero_of {D : Dat ℚ E} {ω χ : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (h : admitted D ω φ)
    (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) (k : ℕ) {s : ℂ} (hs : 1 - (k : ℝ) < s.re)
    (hM : ∀ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous (2 * e) → Mk D χ k φ p s = 0) :
    ∫ y : ℝ, Wo D φ (em E (aE (iy y))) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2) = 0 := by
  have h0 := UpperTheory.eq_zero_of_orthogonal_even_homogeneous_trig _ (pack h hχ k hs).2
    (fun t => by simp only [Wo_rot_pi D ω h.cen]) hM 0
  simpa only [rot_zero, mul_one] using h0

private theorem unit_of {ω χ : HChar ℚ} (hω : Unit1 ω) (hχ : ∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) (a : IdeleGroup ℚ) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) (hχ a)
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, hω a, mul_one, Units.val_one, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1

private theorem contOn_chi (χ : HChar ℚ) : ContinuousOn (fun y : ℝ => ((χ.1 (iy y) : ℂˣ) : ℂ)) ({0}ᶜ : Set ℝ) :=
  (Units.continuous_val.comp χ.2.1).comp_continuousOn contOn_iy

private theorem continuousOn_wo_compl_zero_of_adm {D : Dat ℚ E} {ω : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (hA : admitted D ω φ) :
    ContinuousOn (fun y : ℝ => Wo D φ (em E (aE (iy y)))) ({0}ᶜ : Set ℝ) := by
  rw [continuousOn_iff_continuous_restrict]
  refine cont_Wo D hA.cont hA.bdd (c := fun y : ({0}ᶜ : Set ℝ) => em E (aE (iy y))) ?_
  exact continuousOn_iff_continuous_restrict.1 (cont_em.comp_continuousOn (continuous_aE.comp_continuousOn contOn_iy))

private noncomputable def GG (D : Dat ℚ E) (χ : HChar ℚ) (k : ℕ) (s : ℂ) (φ : GL (Fin 2) (A E) → ℂ) (y : ℝ) : ℂ :=
  Wo D φ (em E (aE (iy y))) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)

private theorem GG_int {D : Dat ℚ E} {ω χ : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (hA : admitted D ω φ)
    (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) (k : ℕ) {s : ℂ} (hs : 1 - (k : ℝ) < s.re) : Integrable (GG D χ k s φ) := by
  have h := (pack hA hχ k hs).1 0
  simp only [rot_zero, mul_one] at h
  exact h

private theorem GG_cont {D : Dat ℚ E} {ω : HChar ℚ} (χ : HChar ℚ) {φ : GL (Fin 2) (A E) → ℂ} (hA : admitted D ω φ) (k : ℕ) (s : ℂ) :
    ContinuousAt (GG D χ k s φ) 1 := by
  have hne : ({0}ᶜ : Set ℝ) ∈ 𝓝 (1 : ℝ) := isOpen_compl_singleton.mem_nhds (by simp)
  have h1 := (continuousOn_wo_compl_zero_of_adm hA).continuousAt hne
  have h4 := (contOn_chi χ).continuousAt hne
  have h5 : ContinuousAt (fun y : ℝ => ((|y| : ℝ) : ℂ) ^ (s - 2)) 1 := by
    refine ContinuousAt.cpow (by fun_prop) continuousAt_const ?_
    simp
  have h6 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ k) 1 := by fun_prop
  exact ((h1.mul h4).mul h6).mul h5

private theorem GG_four {D : Dat ℚ E} {φ : GL (Fin 2) (A E) → ℂ} (χ : HChar ℚ) (hL : ∀ γ g, φ (ratGL E 2 γ * g) = φ g) (k : ℕ) (s : ℂ) (u : ℝ) :
    ∫ y : ℝ, GG D χ k s φ y * Complex.exp (2 * Real.pi * Complex.I * ((y * u : ℝ) : ℂ)) =
      ∫ y : ℝ, GG D χ k s (fun g => φ (g * hU D u)) y := by
  refine integral_congr_ae ?_
  have hae : ∀ᵐ y : ℝ, y ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [hae] with y hy
  simp only [GG]
  rw [Wo_hU D hL hy u]
  ring

private theorem GG_one (D : Dat ℚ E) (χ : HChar ℚ) (k : ℕ) (s : ℂ) (φ : GL (Fin 2) (A E) → ℂ) : GG D χ k s φ 1 = Wo D φ 1 := by
  simp [GG, iy_one]

end

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.nonZ_of :
    NonZ := by
  intro E _ _ _ D P ω χ hcen hω hχ hAll L N φ hG hW k s hs
  by_contra hcon
  push_neg at hcon
  have hχ1 := unit_of hω hχ
  have hA : admitted D ω φ := hAll φ hG.mem
  have hzero : ∀ u : ℝ, ∫ y : ℝ, GG D χ k s φ y * Complex.exp (2 * Real.pi * Complex.I * ((y * u : ℝ) : ℂ)) = 0 := by
    intro u
    have hGu := Gd_translate hG u
    rw [GG_four χ hA.left]
    exact zero_of (hAll _ hGu.mem) hχ1 k hs fun e p hp => hcon _ e p hGu hp
  have h1 := UpperTheory.eq_zero_at_one_of_fourierIntegral_eq_zero _ (GG_int hA hχ1 k hs) (GG_cont χ hA k s) hzero
  exact hW ((GG_one D χ k s φ).symm.trans h1)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ThetaPhi
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E]

private theorem thetaPhi (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2))
    (C C' : Set (GL (Fin 2) (A ℚ))) (hC : IsCompact C) (hC' : IsCompact C') (n : ℕ) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ g : G1 ℚ, ∀ k ∈ C, ∀ k' ∈ C',
      ‖φ (em E (gl g * k)) * ThR Φ t (gl g * k')‖ ≤ B * Real.exp (-((n : ℝ) * t)) := by
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red ℚ
  have hK : IsCompact (KK ℚ) := (UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ).2
  have cpt : ∀ S : Set (GL (Fin 2) (A ℚ)), IsCompact S →
      IsCompact ((fun p : G1 ℚ × GL (Fin 2) (A ℚ) => gl p.1 * p.2) '' (KK ℚ ×ˢ S)) := fun S hS =>
    (hK.prod hS).image ((UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_fst).mul continuous_snd)
  obtain ⟨r, B₁, h₁⟩ := UpperTheory.norm_thetaSeries_siegelSet_le_exp Φ hΦ _ (cpt C' hC') c hc n
  obtain ⟨B₂, h₂⟩ := UpperTheory.norm_admissible_baseChange_siegelSet_le D ω φ hφ _ (cpt C hC) c hc r
  refine ⟨B₂ * B₁, fun t ht g k hk k' hk' => ?_⟩
  obtain ⟨γ, b, a, κ, hκ, hg, hca⟩ := hred g
  have ea : ∀ h : GL (Fin 2) (A ℚ), gl (nU b * mD a * κ) * h = gl (nU b * mD a) * (gl κ * h) := fun h => by
    have hm : gl (nU b * mD a * κ) = gl (nU b * mD a) * gl κ := map_mul _ _ _
    rw [hm, mul_assoc]
  have e1 : φ (em E (gl g * k)) = φ (em E (gl (nU b * mD a) * (gl κ * k))) := by
    rw [← ea, ← hg, UpperTheory.automorphicForm_baseChange_ratSL2_mul_invariant D ω φ hφ]
  have e2 : ThR Φ t (gl g * k') = ThR Φ t (gl (nU b * mD a) * (gl κ * k')) := by
    rw [← ea, ← hg, UpperTheory.thetaSeries_ratSL2_mul_invariant]
  have p₂ := h₂ b a _ ⟨(κ, k), ⟨hκ, hk⟩, rfl⟩ hca
  have p₁ := h₁ t ht b a _ ⟨(κ, k'), ⟨hκ, hk'⟩, rfl⟩ hca
  have hab : 0 < ab a := UpperTheory.ConvolutionTheory.R2.M.ab_pos a
  rw [e1, e2, norm_mul]
  calc _ ≤ (B₂ * (ab a)⁻¹ ^ r) * (B₁ * Real.exp (-((n : ℝ) * t)) * ab a ^ r) :=
        mul_le_mul p₂ p₁ (norm_nonneg _) ((norm_nonneg _).trans p₂)
    _ = B₂ * B₁ * Real.exp (-((n : ℝ) * t)) := by
        rw [inv_pow]; field_simp

private theorem measPhi (ω : HChar ℚ) (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ) {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (h : X → GL (Fin 2) (A ℚ)) (hh : Continuous h) : Measurable fun x => φ (em E (h x)) :=
  (hφ.cont.comp ((UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).1.comp hh)).measurable

private theorem irMeas (D : Dat ℚ E) (ω χ : HChar ℚ) (M : Meas ℚ) (U : UMeas) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2)) : StronglyMeasurable (Ir M U χ φ Φ) := by
  haveI := U.prob
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  have hdM := (UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).2.1
  have hc : Continuous fun p : (ℝ × IdeleGroup ℚ) × G1 ℚ => gl p.2 * dM p.1.2 :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hdM.comp (continuous_snd.comp continuous_fst))
  have h1 : StronglyMeasurable fun p : (ℝ × IdeleGroup ℚ) × G1 ℚ =>
      φ (em E (gl p.2 * dM p.1.2)) * ThR Φ p.1.1 (gl p.2 * dM p.1.2) :=
    ((measPhi ω D φ hφ _ hc).mul (UpperTheory.measurable_thetaSeries_comp_continuous Φ hΦ _ _ (continuous_fst.comp continuous_fst) hc)).stronglyMeasurable
  have h2 := h1.integral_prod_right' (ν := M.μ.restrict M.D)
  have hχ : StronglyMeasurable fun x : ℝ × IdeleGroup ℚ => ((χ.1 x.2 : ℂˣ) : ℂ) :=
    (Units.continuous_val.comp (χ.2.1.comp continuous_snd)).stronglyMeasurable
  exact (hχ.mul h2).integral_prod_right' (ν := U.υ)

private theorem irDecay (D : Dat ℚ E) (ω χ : HChar ℚ) (M : Meas ℚ) (U : UMeas) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) (hP : Per M U χ φ = 0)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2)) (n : ℕ) :
    ∃ B : ℝ, ∀ t, ‖Ir M U χ φ Φ t‖ ≤ B * Real.exp (-((n : ℝ) * |t|)) := by
  haveI := U.prob
  obtain ⟨hUc, hU1⟩ := UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one
  have hdM := (UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).2.1
  obtain ⟨Ψ, hΨ, hpois⟩ := UpperTheory.thetaSeries_poisson_functional_equation Φ hΦ
  set C : Set (GL (Fin 2) (A ℚ)) := (fun u : (A ℚ)ˣ => dM u) '' UU with hCdef
  set C' : Set (GL (Fin 2) (A ℚ)) := (fun u : (A ℚ)ˣ => (gl (wW ℚ))⁻¹ * dM u⁻¹) '' UU with hC'def
  have hC : IsCompact C := hUc.image hdM
  have hc' : Continuous fun u : (A ℚ)ˣ => (gl (wW ℚ))⁻¹ * dM u⁻¹ := continuous_const.mul (hdM.comp continuous_inv)
  have hC' : IsCompact C' := hUc.image hc'
  obtain ⟨Bp, hBp⟩ := thetaPhi D ω φ hφ Φ hΦ C C hC hC n
  obtain ⟨Bm, hBm⟩ := thetaPhi D ω φ hφ Ψ hΨ C C' hC hC' (n + 2)
  set V : ℝ := M.μ.real M.D with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  obtain ⟨Bφ, hBφ⟩ := hφ.bdd
  have hcu : Continuous fun p : IdeleGroup ℚ × G1 ℚ => gl p.2 * dM p.1 :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hdM.comp continuous_fst)
  have hcu' : Continuous fun p : IdeleGroup ℚ × G1 ℚ => gl p.2 * ((gl (wW ℚ))⁻¹ * dM p.1⁻¹) :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hc'.comp continuous_fst)
  have mφ : Measurable fun p : IdeleGroup ℚ × G1 ℚ => φ (em E (gl p.2 * dM p.1)) := measPhi ω D φ hφ _ hcu
  refine ⟨(|Bp| + |Bm|) * V, fun t => ?_⟩
  rcases le_or_gt 0 t with ht | ht
  ·
    have hb : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u)‖ ≤ Bp * Real.exp (-((n : ℝ) * t)) :=
      fun u hu g => hBp t ht g _ ⟨u, hu, rfl⟩ _ ⟨u, hu, rfl⟩
    have hm : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) => φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u)) :=
      mφ.mul (UpperTheory.measurable_thetaSeries_comp_continuous Φ hΦ _ _ continuous_const hcu)
    have := (UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm hb).2.2
    rw [abs_of_nonneg ht]
    refine le_trans this ?_
    have hex := Real.exp_pos (-((n : ℝ) * t))
    have : Bp ≤ |Bp| + |Bm| := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    calc Bp * Real.exp (-((n : ℝ) * t)) * V ≤ (|Bp| + |Bm|) * Real.exp (-((n : ℝ) * t)) * V := by gcongr
      _ = _ := by ring
  ·
    set e : ℂ := (Real.exp (-(2 * t)) : ℂ) with he
    set c₀ : ℂ := -Φ 0 + e * Ψ 0 with hc₀
    have hb1 : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u))‖ ≤ Bφ := fun _ _ _ => hBφ _
    have hb2 : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹))‖ ≤
        Bm * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) :=
      fun u hu g => hBm (-t) (by linarith) g _ ⟨u, hu, rfl⟩ _ ⟨u, hu, rfl⟩
    have hm1 : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) => φ (em E (gl g * dM u))) := mφ
    have hm2 : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) =>
        φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹))) :=
      mφ.mul (UpperTheory.measurable_thetaSeries_comp_continuous Ψ hΨ _ _ continuous_const hcu')
    obtain ⟨i1, j1, -⟩ := UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm1 hb1
    obtain ⟨i2, j2, n2⟩ := UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm2 hb2
    have hae : ∀ᵐ u ∂U.υ, u ∈ UU := by
      have := U.supp
      exact measure_eq_zero_iff_ae_notMem.1 this |>.mono fun u hu => by simpa using hu
    have key : Ir M U χ φ Φ t = c₀ * Per M U χ φ + e * ∫ u, ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D,
        φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) ∂M.μ ∂U.υ := by
      unfold Per
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (j1.const_mul _) (j2.const_mul _)]
      unfold Ir
      refine integral_congr_ae (hae.mono fun u hu => ?_)
      have hin : ∫ g in M.D, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) ∂M.μ =
          c₀ * (∫ g in M.D, φ (em E (gl g * dM u)) ∂M.μ) + e * ∫ g in M.D,
            φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) ∂M.μ := by
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((i1 u hu).const_mul _) ((i2 u hu).const_mul _)]
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        simp only []
        rw [hpois t g u (hU1 u hu)]
        ring
      simp only []
      rw [hin]
      ring
    rw [key, hP, mul_zero, zero_add, norm_mul, he, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, abs_of_neg ht]
    refine (mul_le_mul_of_nonneg_left n2 (Real.exp_pos _).le).trans ?_
    have hex : Real.exp (-(2 * t)) * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) = Real.exp (-((n : ℝ) * -t)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have : Bm ≤ |Bp| + |Bm| := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
    have hpos := Real.exp_pos (-((n : ℝ) * -t))
    calc Real.exp (-(2 * t)) * (Bm * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) * V)
        = Bm * (Real.exp (-(2 * t)) * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t)))) * V := by ring
      _ = Bm * Real.exp (-((n : ℝ) * -t)) * V := by rw [hex]
      _ ≤ (|Bp| + |Bm|) * Real.exp (-((n : ℝ) * -t)) * V := by gcongr
      _ = _ := by ring

theorem ent_of :
    Ent := by
  intro E _ _ _ D P ω χ _ hω hχ M U φ hφ hP Φ hΦ
  have hχ1 : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := fun a => by
    have h := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) (hχ a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one] at h
    rw [show ‖((ω.1 a : ℂˣ) : ℂ)‖ = 1 from hω a, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  exact UpperTheory.differentiable_integral_exp_mul_of_rapid_decay _ (irMeas D ω χ M U φ hφ Φ hΦ).aestronglyMeasurable fun n => irDecay D ω χ M U φ hφ hχ1 hP Φ hΦ n

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
end

