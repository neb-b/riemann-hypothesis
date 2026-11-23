module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsExpo
section
open NumberField Formalism.L2.Host UpperTheory.V UpperTheory.V.Af GlobalTheory.HeckeGal.Model GlobalTheory.Mem.Chr.CharModel
open GlobalTheory.CuspRep (Af)

theorem UpperTheory.V.Af.Nf.absExpo :
    UpperTheory.V.Af.Nf.AbsExpo := by
  intro F _ _ _ s v
  classical
  refine TR.expo_eq_of_exp _ v s fun t => ?_
  change Complex.exp (s * logNorm F (TR.infId F (TR.expU (Pi.single v t)))) = _
  have h1 : finPart F (TR.infId F (TR.expU (Pi.single v t))) = 1 := Units.ext (by
    change (1 : Af F) - 0 + 0 = 1
    simp)
  have h2 : ∀ u, ‖(infPart F (TR.infId F (TR.expU (Pi.single v t)))).val u‖ = Real.exp ((Pi.single v t : TR.Rinf F) u) := fun u => by
    have e : (infPart F (TR.infId F (TR.expU (Pi.single v t)))).val = TR.infEq F (TR.expU (Pi.single v t)).val := by
      change 1 - TR.infEq F 1 + TR.infEq F _ = _
      simp
    rw [e]
    exact (((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal u)).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm)) _).trans
      (Real.norm_of_nonneg (Real.exp_pos _).le)
  rw [logNorm, h1, logFin_one, logInf]
  simp [h2, Pi.single_apply, InfinitePlace.mult, IsTotallyReal.isReal]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsF
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

private theorem val_one (u : (Af ℚ)ˣ) (hu : IsZU u) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (pLoc ℚ w (u : Af ℚ)) = 1 := by
  have a1 : Valued.v (pLoc ℚ w (u : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.1 w
  have a2 : Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.2 w
  have a3 : Valued.v (pLoc ℚ w (u : Af ℚ)) * Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc ℚ w (u : Af ℚ)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

theorem UpperTheory.V.Af.Nf.absF :
    UpperTheory.V.Af.Nf.AbsF := by
  intro r hr u hu
  obtain ⟨-, h2, h3, h4⟩ := UpperTheory.V.Sd.Hm.absf ℚ
  rw [h2, h3 u (val_one u hu), mul_one]
  have h := h4 r
  have hr' : (0 : ℝ) < ((r : ℚ) : ℝ) := by exact_mod_cast hr
  have e : (∏ v, |reAt v (r : ℚ)|) = ((r : ℚ) : ℝ) := by
    rw [Fintype.prod_subsingleton _ Rat.infinitePlace, reAt, eq_ratCast]
    simp [abs_of_pos hr']
  rw [e] at h
  exact eq_inv_of_mul_eq_one_right h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchBd
section
open UpperHalfPlane hiding I
open CongruenceSubgroup

theorem UpperTheory.V.Af.Nf.archBd :
    UpperTheory.V.Af.Nf.ArchBd := by
  intro k M hM f
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨C, fun x hx => ?_⟩
  unfold UpperTheory.V.Af.Nf.nsl
  set J : ℂ := (x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ) with hJdef
  set w : ℂ := (((SignType.sign x.det : ℝ)) : ℂ) *
    (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) / J) with hwdef
  have hJ0 : J ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [J] at h1 h2
    apply hx
    rw [Matrix.det_fin_two, h1, h2]
    ring
  have hn : Complex.normSq J = ‖J‖ ^ 2 := Complex.normSq_eq_norm_sq J
  have hJpos : 0 < ‖J‖ := norm_pos_iff.mpr hJ0
  have hDpos : 0 < |x.det| := abs_pos.mpr hx
  have hq : (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) / J).im =
      x.det / Complex.normSq J := by
    rw [Complex.div_im, Matrix.det_fin_two]
    simp [J]
    ring
  have himw : w.im = |x.det| / ‖J‖ ^ 2 := by
    rw [hwdef, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hq, hn]
    rcases lt_or_gt_of_ne hx with h | h
    · rw [sign_neg h, abs_of_neg h]
      simp
      ring
    · rw [sign_pos h, abs_of_pos h]
      simp
  have hw : 0 < w.im := by
    rw [himw]
    positivity
  have hτ : (ofComplex w).im = |x.det| / ‖J‖ ^ 2 := by
    rw [← himw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    all_goals rfl
  have hb := hC (ofComplex w)
  rw [hτ] at hb
  have hpow : (|x.det| / ‖J‖ ^ 2) ^ (((k : ℤ) : ℝ) / 2) = |x.det| ^ ((k : ℝ) / 2) / ‖J‖ ^ k := by
    rw [Real.div_rpow hDpos.le (by positivity), ← Real.rpow_natCast ‖J‖ 2,
      ← Real.rpow_mul hJpos.le]
    push_cast
    congr 1
    rw [show (2 : ℝ) * ((k : ℝ) / 2) = ((k : ℕ) : ℝ) by ring, Real.rpow_natCast]
  rw [hpow] at hb
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_zpow]
  calc _ ≤ |x.det| ^ ((k : ℝ) / 2) * ‖J‖ ^ (-(k : ℤ)) *
        (C / (|x.det| ^ ((k : ℝ) / 2) / ‖J‖ ^ k)) := by gcongr
    _ = C := by
      have h1 : 0 < |x.det| ^ ((k : ℝ) / 2) := by positivity
      have h2 : 0 < ‖J‖ ^ k := by positivity
      rw [zpow_neg, zpow_natCast]
      field_simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchDer
section
open UpperHalfPlane hiding I
open scoped Manifold

namespace UpperTheory.V.Af.Nf

private noncomputable def cR (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.proj i)

private noncomputable def cC (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (cR i j)

private theorem cR_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cR i j x = x i j := rfl
private theorem cC_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cC i j x = (x i j : ℂ) := rfl

private theorem key (k : ℕ) (F : ℂ → ℂ) (F' : ℂ) (hF : HasDerivAt F F' Complex.I) (x0 : Fin 2 → Fin 2 → ℝ)
    (h00 : x0 0 0 = 1) (h01 : x0 0 1 = 0) (h10 : x0 1 0 = 0) (h11 : x0 1 1 = 1) :
    ∃ L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ,
      HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ =>
        (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k : ℤ)) *
          F (((x 0 0 : ℂ) * Complex.I + x 0 1) * ((x 1 0 : ℂ) * Complex.I + x 1 1)⁻¹)) L x0 ∧
      ∀ v : Fin 2 → Fin 2 → ℝ, L v = (k : ℂ) / 2 * (v 0 0 + v 1 1) * F Complex.I - k * (v 1 0 * Complex.I + v 1 1) * F Complex.I +
        (v 0 0 * Complex.I + v 0 1 + v 1 0 - v 1 1 * Complex.I) * F' := by
  have r : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => x i j) (cR i j) x0 := fun i j => (cR i j).hasFDerivAt
  have c : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => (x i j : ℂ)) (cC i j) x0 := fun i j => (cC i j).hasFDerivAt
  have hd := ((r 0 0).fun_mul (r 1 1)).fun_sub ((r 0 1).fun_mul (r 1 0))
  have hd2 := hd.rpow_const (p := (k : ℝ) / 2) (Or.inl (by simp [h00, h01, h10, h11]))
  have hd3 := Complex.ofRealCLM.hasFDerivAt.comp x0 hd2
  have hden := ((c 1 0).mul_const Complex.I).fun_add (c 1 1)
  have hnum := ((c 0 0).mul_const Complex.I).fun_add (c 0 1)
  have hne : (x0 1 0 : ℂ) * Complex.I + x0 1 1 ≠ 0 := by simp [h10, h11]
  have hz := (hasDerivAt_zpow (-(k : ℤ)) _ (Or.inl hne)).comp_hasFDerivAt x0 hden
  have hi := (hasDerivAt_inv hne).comp_hasFDerivAt x0 hden
  have hq := hnum.fun_mul hi
  have hF2 : HasDerivAt F F' (((x0 0 0 : ℂ) * Complex.I + x0 0 1) * ((x0 1 0 : ℂ) * Complex.I + x0 1 1)⁻¹) := by
    simpa [h00, h01, h10, h11] using hF
  have hc := hF2.comp_hasFDerivAt x0 hq
  refine ⟨_, (hd3.fun_mul hz).fun_mul hc, fun v => ?_⟩
  simp [h00, h01, h10, h11, cR_apply, cC_apply]
  linear_combination (-(v 1 0 : ℂ) * F') * Complex.I_mul_I

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.archDer :
    UpperTheory.V.Af.Nf.ArchDer := by
  intro k f hf D hD
  have hF : DifferentiableAt ℂ (f ∘ ofComplex) Complex.I :=
    (UpperHalfPlane.mdifferentiable_iff.1 hf).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (by simp))
  obtain ⟨L, hL, hv⟩ := key k (f ∘ ofComplex) _ hF.hasDerivAt (Matrix.of.symm 1) (by simp) (by simp) (by simp) (by simp)
  have hpos : ∀ᶠ x : Fin 2 → Fin 2 → ℝ in nhds (Matrix.of.symm 1), 0 < x 0 0 * x 1 1 - x 0 1 * x 1 0 := by
    have hc : Continuous fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0 := by fun_prop
    exact (isOpen_lt continuous_const hc).mem_nhds (by simp)
  have hA : HasFDerivAt (arch k f) L (Matrix.of.symm 1) := by
    refine hL.congr_of_eventuallyEq (hpos.mono fun x hx => ?_)
    simp only [arch, nsl, Matrix.det_fin_two, Matrix.of_apply, abs_of_pos hx, sign_pos hx, Function.comp, coe_I,
      div_eq_mul_inv]
    simp
  have hI : (f ∘ ofComplex) Complex.I = f UpperHalfPlane.I := by
    rw [← coe_I, Function.comp, ofComplex_apply]
  simp only [hD, hA.fderiv, hv, hI]
  simp [Matrix.single]
  refine ⟨Or.inl (mul_comm _ _), ?_⟩
  linear_combination (k * f UpperHalfPlane.I) * Complex.I_mul_I
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchSm
section
open UpperHalfPlane hiding I
open scoped Manifold ContDiff

private theorem archSm_eval_eq (k : ℕ) (f : ℍ → ℂ) (hf : MDiff f) (σ : ℂ)
    (x0 : Fin 2 → Fin 2 → ℝ)
    (hD : x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0 ≠ 0)
    (hc : ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) ≠ 0)
    (him : 0 < (σ * (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))).im) :
    ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((|x 0 0 * x 1 1 - x 0 1 * x 1 0| ^ ((k : ℝ) / 2) : ℝ) : ℂ) *
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-(k : ℤ)) *
        f (ofComplex (σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
          ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))))) x0 := by
  have hre : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ => ((x i j : ℝ) : ℂ)) :=
    fun i j => Complex.ofRealCLM.contDiff.comp (by fun_prop)
  have hDd : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0) := by
    fun_prop
  have hcd : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      (x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) :=
    ((hre 1 0).mul contDiff_const).add (hre 1 1)
  have had : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      (x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) :=
    ((hre 0 0).mul contDiff_const).add (hre 0 1)
  have habs : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      |x 0 0 * x 1 1 - x 0 1 * x 1 0|) x0 :=
    ContDiffAt.comp (g := fun t : ℝ => |t|) x0 (contDiffAt_abs hD) hDd.contDiffAt
  have h1 : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((|x 0 0 * x 1 1 - x 0 1 * x 1 0| ^ ((k : ℝ) / 2) : ℝ) : ℂ)) x0 := by
    refine Complex.ofRealCLM.contDiff.contDiffAt.comp x0 ?_
    exact habs.rpow_const_of_ne (abs_ne_zero.mpr hD)
  have h2 : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-(k : ℤ))) x0 := by
    have hz : AnalyticAt ℂ (fun z : ℂ => z ^ (-(k : ℤ)))
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
      (differentiableOn_zpow (-(k : ℤ)) _ (by tauto)).analyticOnNhd isOpen_compl_singleton _ hc
    exact (hz.contDiffAt.restrict_scalars ℝ).comp x0 hcd.contDiffAt
  have hinv : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-1 : ℤ)) x0 := by
    have hz : AnalyticAt ℂ (fun z : ℂ => z ^ (-1 : ℤ))
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
      (differentiableOn_zpow (-1 : ℤ) _ (by tauto)).analyticOnNhd isOpen_compl_singleton _ hc
    exact ContDiffAt.comp (g := fun z : ℂ => z ^ (-1 : ℤ))
      (f := fun x : Fin 2 → Fin 2 → ℝ =>
        (x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) x0
      (hz.contDiffAt.restrict_scalars ℝ) hcd.contDiffAt
  have hw : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))) x0 := by
    simp only [div_eq_mul_inv, ← zpow_neg_one]
    exact contDiffAt_const.mul (had.contDiffAt.mul hinv)
  have hF : AnalyticAt ℂ (f ∘ ofComplex) (σ * (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) +
      (x0 0 1 : ℂ)) / ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))) :=
    (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet _ him
  have h3 := ContDiffAt.comp (g := f ∘ ofComplex) (f := fun x : Fin 2 → Fin 2 → ℝ =>
      σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))) x0
    (hF.contDiffAt.restrict_scalars ℝ) hw
  exact (h1.mul h2).mul h3

theorem UpperTheory.V.Af.Nf.archSm :
    UpperTheory.V.Af.Nf.ArchSm := by
  intro k f hf
  have hD : ∀ x : Fin 2 → Fin 2 → ℝ,
      (Matrix.of x).det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := by
    intro x
    simp [Matrix.det_fin_two]
  have hDc : Continuous (fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0) := by
    fun_prop
  intro x0 hx0
  refine ContDiffAt.contDiffWithinAt ?_
  have hx0' : x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0 ≠ 0 := by
    simpa [hD] using hx0
  have hc : ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    apply hx0'
    rw [h1, h2]
    ring
  have hsign : ∀ᶠ x in nhds x0, SignType.sign (x 0 0 * x 1 1 - x 0 1 * x 1 0) =
      SignType.sign (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) := by
    rcases lt_or_gt_of_ne hx0' with hneg | hpos
    · filter_upwards [hDc.continuousAt.eventually (gt_mem_nhds hneg)] with x hx
      rw [sign_neg hx, sign_neg hneg]
    · filter_upwards [hDc.continuousAt.eventually (lt_mem_nhds hpos)] with x hx
      rw [sign_pos hx, sign_pos hpos]
  have hq : (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
      ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ))).im =
      (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) /
        Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) := by
    rw [Complex.div_im]
    simp
    ring
  have hn : 0 < Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
    Complex.normSq_pos.mpr hc
  have him : 0 < ((((SignType.sign (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) : ℝ)) : ℂ) *
      (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))).im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hq]
    rcases lt_or_gt_of_ne hx0' with hneg | hpos
    · rw [sign_neg hneg]
      have : (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) /
          Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) < 0 :=
        div_neg_of_neg_of_pos hneg hn
      simp only [SignType.coe_neg, SignType.coe_one]
      linarith
    · rw [sign_pos hpos]
      simp only [SignType.coe_one, one_mul]
      exact div_pos hpos hn
  refine (archSm_eval_eq k f hf _ x0 hx0' hc him).congr_of_eventuallyEq ?_
  filter_upwards [hsign] with x hx
  unfold UpperTheory.V.Af.Nf.arch UpperTheory.V.Af.Nf.nsl
  rw [hD, hx]
  simp only [Matrix.of_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AutPer
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd Filter Topology
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private theorem map_aff {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map p (aff 1 x) = aff 1 (p x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.GeneralLinearGroup.map]

private theorem aff_comm {R : Type} [CommRing R] (x y : R) : aff 1 x * aff 1 y = aff 1 y * aff (1 : Rˣ) x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem aff_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem continuous_aff {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun x : R => aff (1 : Rˣ) x := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · change Continuous fun x : R => (!![(((1 : Rˣ)⁻¹ : Rˣ) : R), -((((1 : Rˣ)⁻¹ : Rˣ) : R) * x); 0, 1] : Matrix (Fin 2) (Fin 2) R)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem unip_eq {R : Type} [CommRing R] (x : BlockIx 2 1 → R) : unip x = aff 1 (x ⟨(0, 1), by decide⟩) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (1 + nilM x : Matrix (Fin 2) (Fin 2) R) i j = _
  fin_cases i <;> fin_cases j <;> simp [aff, nilM]

end UpperTheory.V.Af.Nf

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.autPer :
    UpperTheory.V.Af.Nf.AutPer := by
  intro φ hl ho g
  set t : GL (Fin 2) (Af ℚ) := Matrix.GeneralLinearGroup.map (pFin ℚ) g with ht
  have hc : Continuous fun x : Af ℚ => t⁻¹ * aff 1 x * t := (continuous_const.mul continuous_aff).mul continuous_const
  have h0 : t⁻¹ * aff 1 (0 : Af ℚ) * t ∈ {u | TR.finRep ℚ 2 u φ = φ} := by
    simp [aff_zero]
  obtain ⟨n, hn⟩ := (((hc.tendsto 0).comp (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ)).eventually
    (ho.mem_nhds h0)).exists
  refine ⟨n.factorial, n.factorial_pos, fun x => ?_⟩
  set N : ℕ := n.factorial with hN
  have hn' : ∀ g, φ.1 (g * finGL ℚ 2 (t⁻¹ * aff 1 (N : Af ℚ) * t)) = φ.1 g := fun g => congrFun (congrArg Subtype.val hn) g
  have e1 : g * finGL ℚ 2 (t⁻¹ * aff 1 (N : Af ℚ) * t) = finGL ℚ 2 (aff 1 (N : Af ℚ)) * g :=
    TR.ga_ext (by simp) (by simp [← ht, mul_assoc])
  have e2 : unip x * finGL ℚ 2 (aff 1 (N : Af ℚ)) = finGL ℚ 2 (aff 1 (N : Af ℚ)) * unip x :=
    TR.ga_ext (by simp) (by simp [unip_eq, map_aff, aff_comm])
  have e3 : ratGL ℚ 2 (aff 1 (N : ℚ)) = upR (aff 1 (N : ℝ)) * finGL ℚ 2 (aff 1 (N : Af ℚ)) := by
    rw [ratGL_eq, toR, toF, map_aff, map_aff, map_natCast, map_natCast]
  rw [← hn', ← hl (aff 1 (N : ℚ)) (unip x * g), e3, mul_assoc, mul_assoc, e1, mul_assoc, ← mul_assoc (unip x), e2, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AvgZero
section
open MeasureTheory
open scoped Pointwise

theorem UpperTheory.V.Af.Nf.avgZero :
    UpperTheory.V.Af.Nf.AvgZero := by
  intro G _ _ _ _ _ _ _ Γ _ μ 𝓕 hμ h𝓕 ψ hψ hinv e he N hN havg
  by_cases hint : IntegrableOn ψ 𝓕 μ
  swap
  · exact integral_undef hint
  have hΓ : ∀ (g : Γ) (x : G), ψ (g +ᵥ x) = ψ x := fun g x => hinv g g.2 x
  have hF : ∀ a : G, IsAddFundamentalDomain Γ ((fun x => a + x) '' 𝓕) μ := fun a => h𝓕.vadd_of_comm a
  have hmp : ∀ a : G, MeasurePreserving (fun x => a + x) μ μ := fun a => measurePreserving_add_left μ a
  have hem : ∀ a : G, MeasurableEmbedding (fun x : G => a + x) := fun a => measurableEmbedding_addLeft a
  have h1 : ∀ a : G, ∫ x in 𝓕, ψ (a + x) ∂μ = ∫ x in 𝓕, ψ x ∂μ := fun a => by
    rw [← (hmp a).setIntegral_image_emb (hem a) ψ 𝓕]
    exact (hF a).setIntegral_eq h𝓕 hΓ
  have h2 : ∀ a : G, ∫ x in 𝓕, ‖ψ (a + x)‖ ∂μ = ∫ x in 𝓕, ‖ψ x‖ ∂μ := fun a => by
    rw [← (hmp a).setIntegral_image_emb (hem a) (fun x => ‖ψ x‖) 𝓕]
    exact (hF a).setIntegral_eq h𝓕 fun g x => by rw [hΓ]
  have h3 : ∀ a : G, IntegrableOn (fun x => ψ (a + x)) 𝓕 μ := fun a =>
    ((hmp a).integrableOn_image (hem a)).1 (((hF a).integrableOn_iff h𝓕 hΓ).2 hint)
  have hc : Continuous (Function.uncurry fun (t : ℝ) (x : G) => ψ (e t + x)) :=
    hψ.comp ((he.comp continuous_fst).add continuous_snd)
  have hI : Integrable (Function.uncurry fun (t : ℝ) (x : G) => ψ (e t + x))
      ((volume.restrict (Set.Ioc (0 : ℝ) N)).prod (μ.restrict 𝓕)) := by
    rw [integrable_prod_iff hc.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun t => h3 (e t), ?_⟩
    simp only [Function.uncurry_apply_pair, h2]
    exact integrable_const _
  have hs := integral_integral_swap hI
  simp only [h1, ← intervalIntegral.integral_of_le hN.le, havg, integral_zero, intervalIntegral.integral_const,
    sub_zero, smul_eq_zero, hN.ne', false_or] at hs
  exact hs
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Imports
section
open UpperTheory.V in
theorem UpperTheory.V.Af.Nf.split :
    UpperTheory.V.Af.Nf.Split := by
  intro F _ _ _ a φ hφ hmem
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hmem
  have hst : ∀ t : Finset (TR.CuspSub F a), TR.IsStable (⨆ π ∈ t, π.V) := by
    intro t o x hx
    have : (⨆ π ∈ t, π.V) ≤ (⨆ π ∈ t, π.V).comap (TR.act o) :=
      iSup₂_le fun π hπ y hy =>
        (le_iSup₂ (f := fun (π : TR.CuspSub F a) (_ : π ∈ t) => π.V) π hπ) (π.stable o y hy)
    exact this hx
  induction s using Finset.induction_on with
  | empty => exact absurd (by simpa using hs) hφ
  | insert π t _ ih =>
    by_cases ht : φ ∈ ⨆ π ∈ t, π.V
    · exact ih ht
    rw [Finset.iSup_insert] at hs
    obtain ⟨ψ, hψ, w, hw, e⟩ := Submodule.mem_sup.1 hs
    rcases π.irred (π.V ⊓ ⨆ π ∈ t, π.V) inf_le_left
      (fun o x hx => ⟨π.stable o x hx.1, hst t o x hx.2⟩) with h | h
    · refine ⟨π, ⟨ψ, hψ⟩, _, ?_, hst t, disjoint_iff.2 h, ?_⟩
      · intro h0
        have h1 : ψ = 0 := congrArg Subtype.val h0
        rw [h1, zero_add] at e
        exact ht (e ▸ hw)
      · rw [← e]
        simpa using hw
    · exact absurd (e ▸ Submodule.add_mem _ (inf_eq_left.1 h hψ) hw) ht
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.MemMirabIff
section
open UpperTheory.V.Sd in
private theorem mem_mirab_iff {R : Type} [CommRing R] (g : GL (Fin 2) R) : g ∈ mirab R ↔ g 1 0 = 0 ∧ g 1 1 = 1 := by
  change Matrix.vecMul ![0, 1] (g : Matrix (Fin 2) (Fin 2) R) = ![0, 1] ↔ _
  simp [funext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

open NumberField GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V.Sd in
theorem UpperTheory.V.Af.Nf.memK :
    UpperTheory.V.Af.Nf.MemK := by
  intro M g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have e0 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 0) = 0 := ((mem_mirab_iff _).1 hk).1
    have e1 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 1) = Ideal.Quotient.mk _ 1 := ((mem_mirab_iff _).1 hk).2
    refine ⟨fun a b => (k a b).2, fun a b => ?_, ?_, ?_⟩
    · rw [← map_inv]; exact ((k⁻¹ : GL (Fin 2) ↥(Ohat ℚ)) a b).2
    · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 e0)
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
    · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 e1)
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
  · rintro ⟨ha, hb, ⟨y, hy, e⟩, ⟨z, hz, e'⟩⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) (Ohat ℚ).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin 2) ↥(Ohat ℚ) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin 2) (Af ℚ)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    have e0 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨⟨y, hy⟩, Subtype.ext e⟩)
    have e1 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 1) = Ideal.Quotient.mk _ 1 :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨z, hz⟩, Subtype.ext e'⟩)
    exact ⟨k, (mem_mirab_iff _).2 ⟨e0, e1⟩, Units.ext rfl⟩
end

