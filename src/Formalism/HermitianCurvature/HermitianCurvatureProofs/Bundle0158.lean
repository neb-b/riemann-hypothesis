module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0153
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0114
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HsRealSmulRight
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.FourierDecayAlt.P5.HerA

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def dZv (A : ℂ → (Wq →L[ℂ] Wp)) (c : ℂ) : Wq →L[ℂ] Wp :=
  (1 / 2 : ℂ) • (fderiv ℝ A c 1 - Complex.I • fderiv ℝ A c Complex.I)

def dZbv (A : ℂ → (Wq →L[ℂ] Wp)) (c : ℂ) : Wq →L[ℂ] Wp :=
  (1 / 2 : ℂ) • (fderiv ℝ A c 1 + Complex.I • fderiv ℝ A c Complex.I)

theorem hs_real_smul_right (r : ℝ) (A C : Wq →L[ℂ] Wp) : B.hsInner A (r • C) = r * B.hsInner A C := by
  rw [show r • C = (r : ℂ) • C from rfl, hs_smul_right, Complex.conj_ofReal]

theorem hs_real_smul_left (r : ℝ) (A C : Wq →L[ℂ] Wp) : B.hsInner (r • A) C = r * B.hsInner A C := by
  rw [show r • A = (r : ℂ) • A from rfl, hs_smul_left]

def hsR (A : Wq →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun C => B.hsInner A C
      map_add' := fun C C' => hs_add_right A C C'
      map_smul' := fun r C => by simp only [RingHom.id_apply, hs_real_smul_right, Complex.real_smul] }

def hsB : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => hsR A
      map_add' := fun A A' => by ext C; simp [hsR, hs_add_left]
      map_smul' := fun r A => by ext C; simp [hsR, hs_real_smul_left, Complex.real_smul] }

theorem hsB_apply (A C : Wq →L[ℂ] Wp) : hsB A C = B.hsInner A C := rfl

theorem hs_sub_left (A A' C : Wq →L[ℂ] Wp) : B.hsInner (A - A') C = B.hsInner A C - B.hsInner A' C := by
  simp only [hsInner_eq_sum, ContinuousLinearMap.sub_apply, inner_sub_right, Finset.sum_sub_distrib]

theorem int_hs_of_cpt {a b : ℂ → (Wq →L[ℂ] Wp)} (ha : Continuous a) (hac : HasCompactSupport a)
    (hU : tsupport a ⊆ {c | c ≠ 0}) (hb : ContinuousOn b {c | c ≠ 0}) :
    Integrable (fun x => B.hsInner (a x) (b x)) := by
  have hUo : IsOpen {c : ℂ | c ≠ 0} := isOpen_ne
  have hcont2 : Continuous (fun P : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => B.hsInner P.1 P.2) :=
    Formalism.FourierDecayAlt.P.B6.hsInner_continuous
  have hc : Continuous (fun x => B.hsInner (a x) (b x)) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    by_cases hx : x ∈ tsupport a
    · exact hcont2.continuousAt.comp (ha.continuousAt.prodMk (hb.continuousAt (hUo.mem_nhds (hU hx))))
    · have h0 : a =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      have h1 : (fun x => B.hsInner (a x) (b x)) =ᶠ[𝓝 x] fun _ => 0 :=
        h0.mono fun y hy => by simp only [hy, Pi.zero_apply]; exact hsInner_zero_left _
      exact (continuousAt_const.congr h1.symm)
  have hs : HasCompactSupport (fun x => B.hsInner (a x) (b x)) := by
    refine hac.mono' fun x hx => subset_tsupport _ ?_
    intro h0
    apply hx
    simp only [h0, Pi.zero_apply]
    exact hsInner_zero_left _
  exact hc.integrable_of_hasCompactSupport hs

theorem int_dZv_hs (A G : ℂ → (Wq →L[ℂ] Wp))
    (hA : ∀ x ∈ tsupport G, DifferentiableAt ℝ A x) (hG : ∀ x ∈ tsupport A, DifferentiableAt ℝ G x)
    (h1 : Integrable (fun x => B.hsInner (fderiv ℝ A x 1) (G x)))
    (h2 : Integrable (fun x => B.hsInner (A x) (fderiv ℝ G x 1)))
    (h3 : Integrable (fun x => B.hsInner (fderiv ℝ A x Complex.I) (G x)))
    (h4 : Integrable (fun x => B.hsInner (A x) (fderiv ℝ G x Complex.I)))
    (h5 : Integrable (fun x => B.hsInner (A x) (G x))) :
    ∫ x, B.hsInner (dZv A x) (G x) = -∫ x, B.hsInner (A x) (dZbv G x) := by
  have e1 := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := hsB) (v := (1 : ℂ))
    (μ := volume) h1 h2 h5 hA hG
  have e2 := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := hsB) (v := Complex.I)
    (μ := volume) h3 h4 h5 hA hG
  simp only [hsB_apply] at e1 e2
  have l1 : ∫ x, B.hsInner (dZv A x) (G x) = (1 / 2 : ℂ) * ((∫ x, B.hsInner (fderiv ℝ A x 1) (G x)) -
      Complex.I * ∫ x, B.hsInner (fderiv ℝ A x Complex.I) (G x)) := by
    rw [← integral_const_mul, ← integral_sub h1 (h3.const_mul _), ← integral_const_mul]
    congr 1; funext x; unfold dZv
    rw [hs_smul_left, hs_sub_left, hs_smul_left]
  have l2 : ∫ x, B.hsInner (A x) (dZbv G x) = (1 / 2 : ℂ) * ((∫ x, B.hsInner (A x) (fderiv ℝ G x 1)) -
      Complex.I * ∫ x, B.hsInner (A x) (fderiv ℝ G x Complex.I)) := by
    rw [← integral_const_mul, ← integral_sub h2 (h4.const_mul _), ← integral_const_mul]
    congr 1; funext x; unfold dZbv
    rw [hs_smul_right, hs_add_right, hs_smul_right]
    simp only [map_div₀, map_one, map_ofNat, Complex.conj_I]
    ring
  rw [l1, l2, e1, e2]
  ring

theorem dZbv_inv_smul {Bf : ℂ → (Wq →L[ℂ] Wp)} {c : ℂ} (hc : c ≠ 0) (h : DifferentiableAt ℝ Bf c) :
    dZbv (fun w => (w⁻¹ : ℂ) • Bf w) c = c⁻¹ • dZbv Bf c := by
  have hinv := (hasDerivAt_inv hc).hasFDerivAt.restrictScalars ℝ
  have hs : HasFDerivAt (fun w => (w⁻¹ : ℂ) • Bf w) _ c := hinv.smul h.hasFDerivAt
  unfold dZbv
  rw [hs.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply]
  set a : ℂ := -(c ^ 2)⁻¹ with ha
  have hI : (1 : ℂ) • a + Complex.I * (Complex.I • a) = 0 := by
    simp only [smul_eq_mul, one_mul]; rw [← mul_assoc, Complex.I_mul_I]; ring
  have h2 : ((1 : ℂ) • a) • Bf c + Complex.I • ((Complex.I • a) • Bf c) = 0 := by
    rw [smul_smul Complex.I, ← add_smul, hI, zero_smul]
  calc (1 / 2 : ℂ) • (c⁻¹ • fderiv ℝ Bf c 1 + ((1 : ℂ) • a) • Bf c +
        Complex.I • (c⁻¹ • fderiv ℝ Bf c Complex.I + (Complex.I • a) • Bf c))
      = (1 / 2 : ℂ) • (c⁻¹ • fderiv ℝ Bf c 1 + Complex.I • (c⁻¹ • fderiv ℝ Bf c Complex.I)) +
          (1 / 2 : ℂ) • (((1 : ℂ) • a) • Bf c + Complex.I • ((Complex.I • a) • Bf c)) := by module
    _ = c⁻¹ • ((1 / 2 : ℂ) • (fderiv ℝ Bf c 1 + Complex.I • fderiv ℝ Bf c Complex.I)) := by
        rw [h2, smul_zero, add_zero]; module

theorem pLogAdjHS_cpt (A Bf : ℂ → (Wq →L[ℂ] Wp)) (hA : ContDiff ℝ 1 A) (hAc : HasCompactSupport A)
    (hA0 : (0 : ℂ) ∉ tsupport A) (hB : ContDiffOn ℝ 1 Bf {c | c ≠ 0}) :
    ∫ c, B.hsInner (c • dZv A c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ) =
      -∫ c, B.hsInner (A c) (conj c • dZbv Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  set U : Set ℂ := {c | c ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne
  have hAU : tsupport A ⊆ U := fun x hx h => hA0 (h ▸ hx)
  set G : ℂ → (Wq →L[ℂ] Wp) := fun w => (w⁻¹ : ℂ) • Bf w with hGdef
  have hinv : ContDiffOn ℝ 1 (fun w : ℂ => w⁻¹) U := fun x hx => (contDiffAt_inv ℝ hx).contDiffWithinAt
  have hGc : ContDiffOn ℝ 1 G U := hinv.smul hB
  have hGd : ∀ x ∈ U, DifferentiableAt ℝ G x := fun x hx =>
    (hGc.differentiableOn one_ne_zero x hx).differentiableAt (hUo.mem_nhds hx)
  have hBd : ∀ x ∈ U, DifferentiableAt ℝ Bf x := fun x hx =>
    (hB.differentiableOn one_ne_zero x hx).differentiableAt (hUo.mem_nhds hx)
  have hGf : ContinuousOn (fderiv ℝ G) U := hGc.continuousOn_fderiv_of_isOpen hUo le_rfl
  have hAd : Differentiable ℝ A := hA.differentiable one_ne_zero
  have hAf : Continuous (fderiv ℝ A) := hA.continuous_fderiv one_ne_zero
  have hDA : ∀ v : ℂ, Continuous (fun x => fderiv ℝ A x v) ∧ HasCompactSupport (fun x => fderiv ℝ A x v) ∧
      tsupport (fun x => fderiv ℝ A x v) ⊆ U := by
    intro v
    have h0 : (fun L : ℂ →L[ℝ] (Wq →L[ℂ] Wp) => L v) 0 = 0 := rfl
    refine ⟨hAf.clm_apply continuous_const,
      HasCompactSupport.comp_left (g := fun L : ℂ →L[ℝ] (Wq →L[ℂ] Wp) => L v) (hAc.fderiv (𝕜 := ℝ)) h0, ?_⟩
    exact ((tsupport_comp_subset (g := fun L : ℂ →L[ℝ] (Wq →L[ℂ] Wp) => L v) h0 (fderiv ℝ A)).trans
      (tsupport_fderiv_subset ℝ (f := A))).trans hAU
  have hGv : ∀ v : ℂ, ContinuousOn (fun x => fderiv ℝ G x v) U := fun v => hGf.clm_apply continuousOn_const
  have e := int_dZv_hs A G (fun x _ => hAd x) (fun x hx => hGd x (hAU hx))
    (int_hs_of_cpt (hDA 1).1 (hDA 1).2.1 (hDA 1).2.2 hGc.continuousOn)
    (int_hs_of_cpt hA.continuous hAc hAU (hGv 1))
    (int_hs_of_cpt (hDA Complex.I).1 (hDA Complex.I).2.1 (hDA Complex.I).2.2 hGc.continuousOn)
    (int_hs_of_cpt hA.continuous hAc hAU (hGv Complex.I))
    (int_hs_of_cpt hA.continuous hAc hAU hGc.continuousOn)
  have hL : (fun c => B.hsInner (c • dZv A c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) =
      fun c => B.hsInner (dZv A c) (G c) := by
    funext c
    by_cases hc : c = 0
    · subst hc
      show B.hsInner ((0 : ℂ) • dZv A 0) (Bf 0) / _ = B.hsInner (dZv A 0) ((0 : ℂ)⁻¹ • Bf 0)
      rw [hs_smul_left, inv_zero, hs_smul_right, map_zero]
      simp
    · have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc
      have hn : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hn, hGdef]
      simp only [hs_smul_left, hs_smul_right, map_inv₀]
      field_simp
  have hR : (fun c => B.hsInner (A c) (conj c • dZbv Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) =
      fun c => B.hsInner (A c) (dZbv G c) := by
    funext c
    by_cases hc : c = 0
    · subst hc
      have : A 0 = 0 := image_eq_zero_of_notMem_tsupport hA0
      simp [this, hsInner_zero_left]
    · have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc
      have hn : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hn, hGdef, dZbv_inv_smul hc (hBd c hc)]
      simp only [hs_smul_right, map_inv₀, Complex.conj_conj]
      field_simp
  rw [hL, hR]
  exact e

theorem dZv_smul {φ : ℂ → ℂ} {A : ℂ → (Wq →L[ℂ] Wp)} {c : ℂ} (hφ : DifferentiableAt ℝ φ c)
    (hA : DifferentiableAt ℝ A c) : dZv (fun w => φ w • A w) c = NF.dZ φ c • A c + φ c • dZv A c := by
  have h : HasFDerivAt (fun w => φ w • A w) _ c := hφ.hasFDerivAt.smul hA.hasFDerivAt
  unfold dZv NF.dZ
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  module

theorem pLogAdjHS (A Bf : ℂ → (Wq →L[ℂ] Wp)) (hA : ContDiffOn ℝ 1 A {c | c ≠ 0})
    (hB : ContDiffOn ℝ 1 Bf {c | c ≠ 0})
    (h0 : Integrable (fun c => B.hsInner (A c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)))
    (h1 : Integrable (fun c => B.hsInner (c • dZv A c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)))
    (h2 : Integrable (fun c => B.hsInner (A c) (conj c • dZbv Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ))) :
    ∫ c, B.hsInner (c • dZv A c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ) =
      -∫ c, B.hsInner (A c) (conj c • dZbv Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := exists_deriv_bump_bound
  have hUo : IsOpen {c : ℂ | c ≠ 0} := isOpen_ne
  have hAd : ∀ c ≠ 0, DifferentiableAt ℝ A c := fun c hc =>
    (hA.differentiableOn one_ne_zero c hc).differentiableAt (hUo.mem_nhds hc)
  set F : ℕ → ℂ → (Wq →L[ℂ] Wp) := fun n c => psiC n c • A c with hF
  have hFc : ∀ n, ContDiff ℝ 1 (F n) := by
    intro n
    refine contDiff_iff_contDiffAt.mpr fun c => ?_
    by_cases hc : c = 0
    · subst hc
      refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : Wq →L[ℂ] Wp))) ?_
      filter_upwards [psiL_zero_near0 n] with w hw
      simp [hF, psiC, hw]
    · exact ((psiC_contDiff n).contDiffAt.of_le (by simp)).smul (hA.contDiffAt (hUo.mem_nhds hc))
  have hψs : ∀ n, tsupport (psiC n) ⊆ tsupport (psiL n) := fun n =>
    tsupport_comp_subset (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero (psiL n)
  have hFs : ∀ n, HasCompactSupport (F n) := fun n =>
    (((psiL_hasCompactSupport n).comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).smul_right)
  have hF0 : ∀ n, (0 : ℂ) ∉ tsupport (F n) := fun n h =>
    zero_notMem_tsupport_psiL n (hψs n ((tsupport_smul_subset_left _ _) h))
  have key := fun n => pLogAdjHS_cpt (F n) Bf (hFc n) (hFs n) (hF0 n) hB
  have hLe : ∀ n, (fun c => B.hsInner (c • dZv (F n) c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) = fun c =>
      psiC n c * (B.hsInner (c • dZv A c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) +
        (c * NF.dZ (psiC n) c) * (B.hsInner (A c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) := by
    intro n; funext c
    by_cases hc : c = 0
    · subst hc; simp [hs_smul_left]
    · have hd := dZv_smul (φ := psiC n) (A := A) (((psiC_contDiff n).differentiable (by simp)) c) (hAd c hc)
      rw [show dZv (F n) c = dZv (fun w => psiC n w • A w) c from rfl, hd]
      simp only [smul_add, hs_add_left, hs_smul_left]
      ring
  have hRe : ∀ n, (fun c => B.hsInner (F n c) (conj c • dZbv Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) = fun c =>
      psiC n c * (B.hsInner (A c) (conj c • dZbv Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) +
        (0 : ℂ) * (B.hsInner (A c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) := by
    intro n; funext c; simp only [hF, hs_smul_left]; ring
  have hψm : ∀ n, AEStronglyMeasurable (psiC n) volume := fun n =>
    (psiC_contDiff n).continuous.aestronglyMeasurable
  have hvm : ∀ n, AEStronglyMeasurable (fun c : ℂ => c * NF.dZ (psiC n) c) volume := fun n =>
    (continuous_id.mul (dZ_contDiff (psiC_contDiff n)).continuous).aestronglyMeasurable
  have hae : ∀ᵐ c ∂(volume : Measure ℂ), c ≠ 0 := Measure.ae_ne volume 0
  have hL := tendsto_int_uv_ae _ _ h1 h0 (fun n => psiC n) (fun n c => c * NF.dZ (psiC n) c) C hψm hvm
    (fun n c => by simpa [psiC] using psiL_le_one n c) (fun n c => norm_c_dZ_psiC_le hC n c)
    (hae.mono fun c hc => psiC_eventually c hc)
  have hR := tendsto_int_uv_ae _ _ h2 h0 (fun n => psiC n) (fun _ _ => (0 : ℂ)) C hψm
    (fun _ => aestronglyMeasurable_const)
    (fun n c => by simpa [psiC] using psiL_le_one n c)
    (fun _ _ => by simpa using (norm_nonneg _).trans (hC 0))
    (hae.mono fun c hc => (psiC_eventually c hc).mono fun n hn => ⟨hn.1, rfl⟩)
  have hL' : Tendsto (fun n => ∫ c, B.hsInner (c • dZv (F n) c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) atTop
      (𝓝 (∫ c, B.hsInner (c • dZv A c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ))) := by
    simp only [hLe]; exact hL
  have hR' : Tendsto (fun n => ∫ c, B.hsInner (c • dZv (F n) c) (Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) atTop
      (𝓝 (-∫ c, B.hsInner (A c) (conj c • dZbv Bf c) / ((‖c‖ ^ 2 : ℝ) : ℂ))) := by
    simp only [key, hRe]; exact hR.neg
  exact tendsto_nhds_unique hL' hR'

end Formalism.FourierDecayAlt.P5.HerB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGFormJ
section
open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section betaJ

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_congrJ_left (D : RealPlaceData k r Wp Wq) {F F₂ G : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ JF.Om k r D.z D.z', JF D F g = JF D F₂ g) : beta D F G = beta D F₂ G := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ JF.Om k r D.z D.z' := hq hQ
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F₂ (bigCell k r q.1 (D.μsec q.2))))
    rw [h _ hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

theorem beta_congrJ_right (D : RealPlaceData k r Wp Wq) {F G G₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ JF.Om k r D.z D.z', JF D G g = JF D G₂ g) : beta D F G = beta D F G₂ := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ JF.Om k r D.z D.z' := hq hQ
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G₂ (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2))))
    rw [h _ hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

end betaJ

section formJ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  (P0 : M.Par) (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter)

theorem formLev_congrJ_left (x y x' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (hx : ∀ a, JC.NiceCoef (T.bs j) ε (x a)) (hy : ∀ a, JC.NiceCoef (T.bs j) ε (y a))
    (hJ : ∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) :
    D.formLev T s j w x x' = D.formLev T s j w y x' := by
  have hQQ : ∀ Y p q, BcGood (T.bs j) ε (D.QQlev T s j Y p q) := fun Y p q => bcGood_tL s Y p q
  have hR := mn_rrop_closure bcGood_closed (D.QQlev T s j) hQQ (D.positionted w)
  unfold D.formLev
  refine Finset.sum_congr rfl fun a _ => beta_congrJ_left (T.bs j) fun h hh => ?_
  rw [bc_core (D.RRlev T s j w) hR x hx a hh, bc_core (D.RRlev T s j w) hR y hy a hh]
  show (∑ b, D.ap (D.RRlev T s j w a b) (fun g => B.JF (T.bs j) (x b) g)) h =
    (∑ b, D.ap (D.RRlev T s j w a b) (fun g => B.JF (T.bs j) (y b) g)) h
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact (hR a b).2.2 _ _ (fun g hg hgG => hJ b g ⟨hgG, hg⟩) h hh.2 hh.1

theorem formLev_congrJ_right (x' x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (hJ : ∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) :
    D.formLev T s j w x' x = D.formLev T s j w x' y := by
  unfold D.formLev
  exact Finset.sum_congr rfl fun a _ => beta_congrJ_right (T.bs j) (hJ a)

theorem pairJ_congrJ_left (ε : ℝ) : ∀ (ys : List ℝ)
    (x y : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (x' : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
    (∀ a, JC.NiceCoef (T.bs j) ε (x a)) → (∀ a, JC.NiceCoef (T.bs j) ε (y a)) →
    (∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) →
    KB.pairJ (D.formLev T s j w) ys x x' = KB.pairJ (D.formLev T s j w) ys y x'
  | [], x, y, x', hx, hy, hJ => formLev_congrJ_left P0 T s j w x y x' ε hx hy hJ
  | _ :: ys, x, y, x', hx, hy, hJ => by
    simp only [KB.pairJ]
    rw [pairJ_congrJ_left ε ys (fun e => x (Fin.cons 1 e)) (fun e => y (Fin.cons 1 e)) _ (fun _ => hx _)
      (fun _ => hy _) (fun _ => hJ _),
      pairJ_congrJ_left ε ys (fun e => x (Fin.cons 0 e)) (fun e => y (Fin.cons 0 e)) _ (fun _ => hx _)
      (fun _ => hy _) (fun _ => hJ _)]

theorem pairJ_congrJ_right : ∀ (ys : List ℝ)
    (x' : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (x y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
    (∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) →
    KB.pairJ (D.formLev T s j w) ys x' x = KB.pairJ (D.formLev T s j w) ys x' y
  | [], x', x, y, hJ => formLev_congrJ_right P0 T s j w x' x y hJ
  | _ :: ys, x', x, y, hJ => by
    simp only [KB.pairJ]
    rw [pairJ_congrJ_right ys _ (fun e => x (Fin.cons 0 e)) (fun e => y (Fin.cons 0 e)) (fun _ => hJ _),
      pairJ_congrJ_right ys _ (fun e => x (Fin.cons 1 e)) (fun e => y (Fin.cons 1 e)) (fun _ => hJ _)]

end formJ

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_JA_LocLemmas
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

def CoefG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (d Bg : ℝ) : Prop :=
  ∀ Tm ∈ Θ, ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat k r),
    (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
      ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ (d + Bg * m) ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ (d + Bg * m)

def OpCCg : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (d Bg A η : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    0 < η → 0 ≤ Bg → B.SmoothCoef (B.GPos Bs) Θ → CoefG Bs Θ d Bg →
    B.CkOn ⊤ (B.GV k r) F → (∀ m : ℕ, B.InCC (A - Bg * m) m F) →
    (∀ g ∈ B.GV k r, Gf k r Bs.z Bs.z' g < η → F g = 0) →
    (B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (B.opApply Θ F)) ∧
    (B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (B.opAdj Θ F))

def AgreeOm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (J F : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set ℝ),
    J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} →
    (∀ q ∈ JF.QDom k r Bs.z Bs.z', Gf k r Bs.z Bs.z' (B.gq Bs q) ∈ U → J (B.gq Bs q) = B.JF Bs F (B.gq Bs q)) →
    ∀ g ∈ JF.Om k r Bs.z Bs.z', Gf k r Bs.z Bs.z' g ∈ U → J g = B.JF Bs F g

def ThetaJ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (UU : Set (B.Mat k r)),
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A (B.opOrder Θ) → B.SmoothCoef (B.GPos Bs) Θ → B.Commutes Bs (B.GPos Bs) Θ →
    B.CkOn ⊤ (B.GV k r) F → B.InCC A (B.opOrder Θ) F →
    UU ⊆ JF.Om k r Bs.z Bs.z' → B.CkOn (B.opOrder Θ : ℕ∞) UU (B.JF Bs F) →
    (∀ g ∈ JF.Om k r Bs.z Bs.z', B.opApply Θ (B.JF Bs F) g = B.JF Bs (B.opApply Θ F) g) ∧
      ∀ g ∈ UU, B.opAdj Θ (B.JF Bs F) g = B.JF Bs (B.opAdj Θ F) g

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

def ThetaJApply : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A (B.opOrder Θ) → B.SmoothCoef (B.GPos Bs) Θ → B.Commutes Bs (B.GPos Bs) Θ →
    B.CkOn ⊤ (B.GV k r) F → B.InCC A (B.opOrder Θ) F →
    ∀ g ∈ JF.Om k r Bs.z Bs.z', B.opApply Θ (B.JF Bs F) g = B.JF Bs (B.opApply Θ F) g

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
end

