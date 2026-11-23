module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
public import GroundTheory.AutomorphicForms.Bundle0019
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
public import GroundTheory.GlobalFields.TateThesis.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.AutomorphicFormBaseChangeRatSL2MulInvariant
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.automorphicForm_baseChange_ratSL2_mul_invariant :
    ∀ {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (g : G1 ℚ) (h : GL (Fin 2) (A ℚ)), φ (em E (gl (ratS ℚ γ * g) * h)) = φ (em E (gl g * h)) := by
  intro E _ _ D ω φ hφ γ g h
  have key : em E (gl (ratS ℚ γ)) =
      ratGL E 2 (Matrix.GeneralLinearGroup.map (algebraMap ℚ E) (Matrix.SpecialLinearGroup.toGL γ)) := by
    apply Units.ext
    ext i j
    simpa [UpperTheory.ConvolutionTheory.RankTwoDescent.em, gl, ratS, ratGL, Matrix.GeneralLinearGroup.map, Matrix.SpecialLinearGroup.map, Matrix.SpecialLinearGroup.toGL] using
      (AdeleBaseChange.adeleMap_algebraMap (K := ℚ) (L := E) (γ.1 i j))
  have e : gl (ratS ℚ γ * g) * h = gl (ratS ℚ γ) * (gl g * h) := by
    rw [gl, gl, map_mul, mul_assoc]
  rw [e, map_mul, key]
  exact hφ.left _ _
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ContinuousGL2BaseChangeDiagUnitInfiniteIdele
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele :
    ∀ (E : Type) [Field E] [NumberField E], Continuous (em E) ∧ Continuous (dM : (A ℚ)ˣ → GL (Fin 2) (A ℚ)) ∧ Continuous (fun t : ℝ => iy (Real.exp t)) := by
  intro E _ _
  refine ⟨?_, ?_, ?_⟩
  · have hc : Continuous (AdeleBaseChange.adeleMap ℚ E) := AdeleBaseChange.continuous_adeleMap
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map hc
    · exact Units.continuous_coe_inv.matrix_map hc
  · refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_val
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_coe_inv
  · let u : ℝ → (TR.Rinf ℚ)ˣ := fun t =>
      ⟨fun _ => Real.exp t, fun _ => (Real.exp t)⁻¹,
        funext fun _ => mul_inv_cancel₀ (Real.exp_ne_zero t),
        funext fun _ => inv_mul_cancel₀ (Real.exp_ne_zero t)⟩
    have hu : Continuous u := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_pi fun _ => Real.continuous_exp
      · exact continuous_pi fun _ => (Real.continuous_exp.inv₀ Real.exp_ne_zero)
    have he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (u t) := by
      funext t
      simp only [iy, dif_neg (Real.exp_ne_zero t)]
      rfl
    rw [he]
    exact (TR.continuous_infId ℚ).comp hu
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.CuspSubspaceTranslateEqSmulSpecialTranslate
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem cinf_sq {E : Type} [Field E] (y : (Cinf E)ˣ) : ∃ r : (Cinf E)ˣ, r ^ 2 = y := by
  have hy : ∀ w, y.val w ≠ 0 := fun w h => by
    have := congrFun y.mul_inv w
    simp [h] at this
  choose z hz using fun w => IsAlgClosed.exists_pow_nat_eq (y.val w) (n := 2) (by norm_num)
  have hz0 : ∀ w, z w ≠ 0 := fun w h => hy w (by rw [← hz w, h]; simp)
  refine ⟨⟨z, fun w => (z w)⁻¹, funext fun w => mul_inv_cancel₀ (hz0 w), funext fun w => inv_mul_cancel₀ (hz0 w)⟩, Units.ext (funext fun w => ?_)⟩
  exact hz w

private theorem pInf_infId {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r : (Cinf E)ˣ) :
    Units.map (pInf E).toMonoidHom (infId E r) = r := by
  have h : ∀ x, pInf E (GlobalTheory.CuspRep.sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  refine Units.ext ?_
  change pInf E (1 - GlobalTheory.CuspRep.sInf E 1 + GlobalTheory.CuspRep.sInf E r.val) = r.val
  simp [h]

private theorem dM_fin {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (t : (A E)ˣ)
    (ht : pInf E (t : A E) = 1) : ∃ k, dM t = finGL E 2 k := by
  refine ⟨GeneralLinearGroup.map (pFin E) (dM t), ?_⟩
  have h : GeneralLinearGroup.map (pInf E) (dM t) = 1 := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht]
  conv_lhs => rw [← infGL_mul_finGL (dM t), h, map_one, one_mul]

theorem UpperTheory.cuspSubspace_translate_eq_smul_special_translate :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar ℚ), CenN P ω → ∀ f ∈ P.V, ∀ x : GL (Fin 2) (A E), ∃ (c : ℂ) (f' : Sm E 2) (h : G1 E), f' ∈ P.V ∧ ∀ g, f.1 (g * x) = c * f'.1 (g * gl h) := by
  intro E _ _ _ P ω hω f hf x
  obtain ⟨g0, hg0⟩ := exists_gl_mul_dM x
  obtain ⟨r, hr⟩ := cinf_sq (Units.map (pInf E).toMonoidHom (GeneralLinearGroup.det x))
  obtain ⟨s, hs⟩ : ∃ s : (A E)ˣ, Units.map (pInf E).toMonoidHom s = r := ⟨infId E r, pInf_infId r⟩
  obtain ⟨t, ht⟩ : ∃ t : (A E)ˣ, GeneralLinearGroup.det x = s ^ 2 * t := ⟨(s ^ 2)⁻¹ * GeneralLinearGroup.det x, by group⟩
  have ht1 : pInf E (t : A E) = 1 := by
    have h1 : Units.map (pInf E).toMonoidHom t = 1 := by
      have h2 := congrArg (Units.map (pInf E).toMonoidHom) ht
      rw [map_mul, map_pow, hs, hr] at h2
      exact (mul_eq_left.1 h2.symm)
    exact congrArg Units.val h1
  obtain ⟨k, hk⟩ := dM_fin t ht1
  refine ⟨((ω.1 (ideleNorm ℚ E s) : ℂˣ) : ℂ), act (.fin k) f, g0 * (mD s)⁻¹, P.stable (.fin k) f hf, fun g => ?_⟩
  have hx : x = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (gl (g0 * (mD s)⁻¹) * dM t) := by
    have e : dM (s ^ 2) = (gl (mD s))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
      rw [← gl_mD_mul_dM_sq, inv_mul_cancel_left]
    rw [gl_mul, gl_inv]
    conv_lhs => rw [hg0, ht, dM_mul, e]
    rw [scalar_comm s (gl g0 * (gl (mD s))⁻¹ * dM t), mul_assoc (gl (mD s))⁻¹, scalar_comm s (dM t)]
    simp only [mul_assoc]
  have hg : g * x = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (g * gl (g0 * (mD s)⁻¹) * finGL E 2 k) := by
    rw [hx, hk, ← mul_assoc g, ← scalar_comm s g, mul_assoc, mul_assoc]
  rw [hg, hω f hf]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.DifferentiableIntegralExpMulOfRapidDecay
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.differentiable_integral_exp_mul_of_rapid_decay :
    ∀ I : ℝ → ℂ, AEStronglyMeasurable I volume → (∀ n : ℕ, ∃ B : ℝ, ∀ t, ‖I t‖ ≤ B * Real.exp (-((n : ℝ) * |t|))) →
        Differentiable ℂ fun s : ℂ => ∫ t : ℝ, Complex.exp (2 * s * t) * I t := by
  intro I hI hdec s₀
  have hexp : Integrable (fun t : ℝ => Real.exp (-|t|)) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_exp_Iic (0 : ℝ)).congr_fun (fun t ht => ?_) measurableSet_Iic
      simp [abs_of_nonpos (Set.mem_Iic.mp ht)]
    · refine (exp_neg_integrableOn_Ioi 0 (zero_lt_one (α := ℝ))).congr_fun (fun t ht => ?_)
        measurableSet_Ioi
      simp [abs_of_pos (Set.mem_Ioi.mp ht)]
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (|s₀.re| + 1) + 2)
  obtain ⟨B, hB⟩ := hdec n
  have hB0 : 0 ≤ B := by
    have h := hB 0
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  have key : ∀ s : ℂ, s ∈ Metric.ball s₀ 1 → ∀ t : ℝ,
      ‖Complex.exp (2 * s * t)‖ * ‖I t‖ ≤ B * Real.exp (-(2 * |t|)) := by
    intro s hs t
    have hre : |s.re| ≤ |s₀.re| + 1 := by
      have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm (s - s₀)
      have h2 : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
      have h3 := abs_sub_abs_le_abs_sub s.re s₀.re
      rw [Complex.sub_re] at h1
      linarith
    have hn1 : ‖Complex.exp (2 * s * t)‖ = Real.exp (2 * s.re * t) := by
      rw [Complex.norm_exp]
      simp
    have ht : 2 * s.re * t ≤ 2 * (|s₀.re| + 1) * |t| := by
      have h1 : s.re * t ≤ |s.re| * |t| := by
        rw [← abs_mul]
        exact le_abs_self _
      have h2 : |s.re| * |t| ≤ (|s₀.re| + 1) * |t| :=
        mul_le_mul_of_nonneg_right hre (abs_nonneg t)
      linarith
    have hnt : (2 * (|s₀.re| + 1) + 2) * |t| ≤ (n : ℝ) * |t| :=
      mul_le_mul_of_nonneg_right hn.le (abs_nonneg t)
    calc ‖Complex.exp (2 * s * t)‖ * ‖I t‖
        ≤ Real.exp (2 * (|s₀.re| + 1) * |t|) * (B * Real.exp (-((n : ℝ) * |t|))) := by
          rw [hn1]
          exact mul_le_mul (Real.exp_le_exp.mpr ht) (hB t) (norm_nonneg _) (Real.exp_pos _).le
      _ = B * Real.exp (2 * (|s₀.re| + 1) * |t| + -((n : ℝ) * |t|)) := by
          rw [Real.exp_add]
          ring
      _ ≤ B * Real.exp (-(2 * |t|)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB0
          linarith
  have hcont : ∀ s : ℂ, Continuous fun t : ℝ => Complex.exp (2 * s * t) := fun s => by
    fun_prop
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.exp (2 * s * t) * I t) volume :=
    fun s => (hcont s).aestronglyMeasurable.mul hI
  have hmeas' : AEStronglyMeasurable
      (fun t : ℝ => (2 * (t : ℂ)) * Complex.exp (2 * s₀ * t) * I t) volume := by
    have hc : Continuous fun t : ℝ => (2 * (t : ℂ)) * Complex.exp (2 * s₀ * t) := by
      fun_prop
    exact hc.aestronglyMeasurable.mul hI
  have hF_int : Integrable (fun t : ℝ => Complex.exp (2 * s₀ * t) * I t) volume := by
    refine (hexp.const_mul B).mono' (hmeas s₀) (ae_of_all _ fun t => ?_)
    rw [norm_mul]
    refine (key s₀ (Metric.mem_ball_self one_pos) t).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB0)
    linarith [abs_nonneg t]
  have h_bound : ∀ᵐ t : ℝ ∂volume, ∀ s ∈ Metric.ball s₀ 1,
      ‖(2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t‖ ≤ 2 * B * Real.exp (-|t|) := by
    refine ae_of_all _ fun t s hs => ?_
    have hk := key s hs t
    have hnorm : ‖(2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t‖
        = 2 * |t| * (‖Complex.exp (2 * s * t)‖ * ‖I t‖) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp only [Complex.norm_ofNat]
      ring
    have habs : |t| ≤ Real.exp |t| := by
      linarith [Real.add_one_le_exp |t|]
    rw [hnorm]
    calc 2 * |t| * (‖Complex.exp (2 * s * t)‖ * ‖I t‖)
        ≤ 2 * Real.exp |t| * (B * Real.exp (-(2 * |t|))) :=
          mul_le_mul (by linarith) hk (by positivity) (by positivity)
      _ = 2 * B * (Real.exp |t| * Real.exp (-(2 * |t|))) := by ring
      _ = 2 * B * Real.exp (-|t|) := by
          rw [← Real.exp_add]
          congr 2
          ring
  have h_diff : ∀ᵐ t : ℝ ∂volume, ∀ s ∈ Metric.ball s₀ 1,
      HasDerivAt (fun x : ℂ => Complex.exp (2 * x * t) * I t)
        ((2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t) s := by
    refine ae_of_all _ fun t s _ => ?_
    have h1 : HasDerivAt (fun x : ℂ => 2 * x * (t : ℂ)) (2 * (t : ℂ)) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 : ℂ)).mul_const (t : ℂ)
    have h2 := h1.cexp.mul_const (I t)
    rwa [show Complex.exp (2 * s * t) * (2 * (t : ℂ)) * I t
        = (2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t by ring] at h2
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun t : ℝ => 2 * B * Real.exp (-|t|))
    (F := fun (s : ℂ) (t : ℝ) => Complex.exp (2 * s * t) * I t)
    (F' := fun (s : ℂ) (t : ℝ) => (2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t)
    (Metric.ball_mem_nhds s₀ one_pos) (Eventually.of_forall hmeas) hF_int hmeas' h_bound
    (hexp.const_mul (2 * B)) h_diff).2.differentiableAt
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsCommonDenomOfIsCompactUnipotentTranslates
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)


open scoped nonZeroDivisors in
private theorem den_of {Q : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hQ : IsCompact Q) :
    ∃ d : ℕ, 0 < d ∧ ∀ q : ℚ, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ Q →
      ∃ l : ℤ, (d : ℚ) * q = l := by
  obtain ⟨D, hD0, hD⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hQ
  set z : ℤ := Rat.ringOfIntegersEquiv D with hz
  have hz0 : z ≠ 0 := by
    intro h
    exact hD0 (Rat.ringOfIntegersEquiv.injective (by rw [map_zero]; exact h))
  have hdz : algebraMap (𝓞 ℚ) ℚ D = z := (Rat.ringOfIntegersEquiv_apply_coe D).symm
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz0, fun q hq => ?_⟩
  have h1 := hD _ hq
  rw [← map_mul] at h1
  have h2 : algebraMap (𝓞 ℚ) ℚ D * q ∈
      ((1 : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h1
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  have hn : ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) = (z : ℚ) * q := by
    rw [← hdz, ← hr]
    exact Rat.ringOfIntegersEquiv_apply_coe r |>.symm ▸ rfl
  rcases Int.natAbs_eq z with h | h
  · refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
    have e1 : ((z.natAbs : ℕ) : ℤ) = z := by omega
    rw [hn, show ((z.natAbs : ℕ) : ℚ) = (z : ℚ) by rw [← Int.cast_natCast, e1]]
  · refine ⟨-Rat.ringOfIntegersEquiv r, ?_⟩
    have e1 : ((z.natAbs : ℕ) : ℤ) = -z := by omega
    rw [Int.cast_neg, hn, show ((z.natAbs : ℕ) : ℚ) = -(z : ℚ) by
      rw [← Int.cast_natCast, e1, Int.cast_neg], neg_mul]

private theorem mul_int {a : ℕ} {q : ℚ} (c : ℕ) (h : ∃ l : ℤ, (a : ℚ) * q = l) :
    ∃ l : ℤ, ((c * a : ℕ) : ℚ) * q = l := by
  obtain ⟨l, hl⟩ := h
  refine ⟨c * l, ?_⟩
  push_cast
  rw [mul_assoc, hl]

theorem UpperTheory.exists_common_denom_of_isCompact_unipotent_translates :
    ∀ (L : Set (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact L → ∀ S : Set (A ℚ)ˣ, IsCompact S →
        ∃ d : ℕ, 0 < d ∧ ∀ u ∈ S, ∀ (b : FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ ξ' : Fin 2 → ℚ),
          (![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2,
              (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2]) ∈ L →
          (![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * (u : A ℚ).2,
              (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * b + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2]) ∈ L →
          (∃ l : ℤ, (d : ℚ) * ξ 0 = l) ∧ (ξ 0 = 0 → ∃ l : ℤ, (d : ℚ) * ξ 1 = l) ∧
            (ξ 0 = ξ' 0 → ∃ l : ℤ, (d : ℚ) * (ξ 1 - ξ' 1) = l) := by
  intro L hL S hS
  have hf : Continuous fun u : (A ℚ)ˣ => (u : A ℚ).2 :=
    continuous_snd.comp Units.continuous_val
  have hi : Continuous fun u : (A ℚ)ˣ => ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hp : ∀ i : Fin 2, Continuous fun v : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => v i :=
    fun i => continuous_apply i
  set Q0 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ =>
      p.1 0 * ((p.2⁻¹ : (A ℚ)ˣ) : A ℚ).2) '' (L ×ˢ S) with hQ0
  set Q2 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ => p.1 1 * (p.2 : A ℚ).2) '' (L ×ˢ S)
    with hQ2
  set Q1 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ =>
      (p.1 1 - p.2.1 1) * (p.2.2 : A ℚ).2) '' (L ×ˢ (L ×ˢ S)) with hQ1
  have c0 : IsCompact Q0 := (hL.prod hS).image
    (((hp 0).comp continuous_fst).mul (hi.comp continuous_snd))
  have c2 : IsCompact Q2 := (hL.prod hS).image
    (((hp 1).comp continuous_fst).mul (hf.comp continuous_snd))
  have c1 : IsCompact Q1 := (hL.prod (hL.prod hS)).image
    ((((hp 1).comp continuous_fst).sub ((hp 1).comp (continuous_fst.comp continuous_snd))).mul
      (hf.comp (continuous_snd.comp continuous_snd)))
  obtain ⟨d0, hd0, H0⟩ := den_of c0
  obtain ⟨d2, hd2, H2⟩ := den_of c2
  obtain ⟨d1, hd1, H1⟩ := den_of c1
  refine ⟨d1 * d2 * d0, by positivity, fun u hu b ξ ξ' h h' => ?_⟩
  have hu1 : (u : A ℚ).2 * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 = 1 := by
    have h0 : (u : A ℚ) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := Units.mul_inv u
    exact congrArg Prod.snd h0
  have hu2 : ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 * (u : A ℚ).2 = 1 := by
    rw [mul_comm, hu1]
  refine ⟨mul_int _ (H0 _ ⟨(_, u), ⟨h, hu⟩, ?_⟩), fun e => ?_, fun e => ?_⟩
  · change algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2 *
      ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 = _
    rw [mul_assoc, hu1, mul_one]
  · have := H2 (ξ 1) ⟨(_, u), ⟨h, hu⟩, by
      change (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 * (u : A ℚ).2 = _
      rw [e, map_zero, zero_mul, zero_add, mul_assoc, hu2, mul_one]⟩
    obtain ⟨l, hl⟩ := this
    refine ⟨d1 * l * d0, ?_⟩
    push_cast
    rw [← hl]
    ring
  · have := H1 (ξ 1 - ξ' 1) ⟨(_, _, u), ⟨h, h', hu⟩, by
      change ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 -
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2) * (u : A ℚ).2 = _
      rw [e, ← sub_mul, mul_assoc, hu2, mul_one, map_sub]
      ring⟩
    obtain ⟨l, hl⟩ := this
    refine ⟨d2 * l * d0, ?_⟩
    push_cast
    rw [← hl]
    ring
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsRatHeightOneSpectrumNormVEqPrimeBadIffDvd
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

theorem UpperTheory.exists_rat_heightOneSpectrum_normV_eq_prime_bad_iff_dvd :
    ∀ (p N : ℕ), p.Prime → ∃ v : H.P ℚ, normV v = p ∧ (Bad N v ↔ p ∣ N) := by
  intro p N hp
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp)
  have hne : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpr.ne_zero
  refine ⟨⟨Ideal.span {(p : 𝓞 ℚ)}, (Ideal.span_singleton_prime hpr.ne_zero).2 hpr, hne⟩, ?_, ?_⟩
  · have h : ∀ w : HeightOneSpectrum (𝓞 ℚ), normV w = Ideal.absNorm w.asIdeal := fun w => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    rw [h]
    change Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  · change (N : 𝓞 ℚ) ∈ Ideal.span {(p : 𝓞 ℚ)} ↔ p ∣ N
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_natCast,
      Int.natCast_dvd_natCast]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.MeasurableThetaSeriesCompContinuous
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem sb_le : schwartzBruhatPi (K := ℚ) (ι := Fin 2) ≤ GroundTheory.Automorphic.Adele2.schwartzBruhat2 ℚ := by
  refine Submodule.span_le.mpr ?_
  rintro F ⟨φ, g, hg, rfl⟩
  exact GroundTheory.Automorphic.Adele2.schwartzBruhatTensor2_mem φ
    (show _ ∧ _ from (mem_finiteSchwartzBruhatPi ℚ).mp hg)

private theorem cont_iy : Continuous fun t : ℝ => iy (Real.exp t) := by
  let u : ℝ → (TR.Rinf ℚ)ˣ := fun t => ⟨fun _ => Real.exp t, fun _ => (Real.exp t)⁻¹,
    funext fun _ => mul_inv_cancel₀ (Real.exp_ne_zero t), funext fun _ => inv_mul_cancel₀ (Real.exp_ne_zero t)⟩
  have hu : Continuous u := by
    refine Units.continuous_iff.mpr ⟨continuous_pi fun _ => Real.continuous_exp, continuous_pi fun _ => ?_⟩
    exact Real.continuous_exp.inv₀ Real.exp_ne_zero
  have e : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (u t) := by
    funext t
    exact dite_eq_right (Real.exp_ne_zero t)
  rw [e]
  exact (TR.continuous_infId ℚ).comp hu

private theorem summable_row {Φ : (Fin 2 → A ℚ) → ℂ} (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2))
    (a : (A ℚ)ˣ) (g : GL (Fin 2) (A ℚ)) :
    Summable fun ξ : Rw ℚ => Φ fun j => (a : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* g.val) j := by
  have hs := (GroundTheory.Automorphic.Adele2.poisson_rightTranslate (sb_le hΦ)
    (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g)).1.of_norm
  have hv : ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))
      = (a : A ℚ) • g.val := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_apply]
  refine (hs.comp_injective (Subtype.val_injective (p := fun r : Fin 2 → ℚ => r ≠ 0))).congr fun ξ => ?_
  simp only [Function.comp_apply]
  rw [hv, Matrix.vecMul_smul]
  rfl

theorem UpperTheory.measurable_thetaSeries_comp_continuous :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2) → ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
        (τ : X → ℝ) (h : X → GL (Fin 2) (A ℚ)), Continuous τ → Continuous h → Measurable fun x => ThR Φ (τ x) (h x) := by
  intro Φ hΦ X _ _ _ τ h hτ hh
  have hc := continuous_of_mem_schwartzBruhatPi hΦ
  have ha : Continuous fun x => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) :=
    Units.continuous_val.comp (cont_iy.comp hτ)
  have hg : Continuous fun x => (h x).val := Units.continuous_val.comp hh
  have hterm : ∀ ξ : Rw ℚ, Continuous fun x =>
      Φ fun j => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (h x).val) j := fun ξ =>
    hc.comp (continuous_pi fun j => ha.mul
      ((continuous_apply j).comp (continuous_const.matrix_vecMul hg)))
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (Rw ℚ)))
    (f := fun (s : Finset (Rw ℚ)) x => ∑ ξ ∈ s,
      Φ fun j => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (h x).val) j)
    (fun s => (continuous_finsetSum s fun ξ _ => hterm ξ).measurable) ?_
  exact tendsto_pi_nhds.mpr fun x => (summable_row hΦ (iy (Real.exp (τ x))) (h x)).hasSum
end

