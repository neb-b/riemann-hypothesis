module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0005
public import Mathlib.Analysis.Complex.Conformal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import GroundTheory.AutomorphicForms.GL2Classical.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.DownHol
section
noncomputable section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af.Nf UpperTheory.V.Sd Topology
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Br.DescentHolomorphic


open Classical in
private def EE (i j : Fin 2) : TR.Lie ℚ 2 := TR.toL (Matrix.single i j (Pi.single Rat.infinitePlace 1))

private def AA (w : ℂ) : TR.Lie ℚ 2 := w.im • EE 0 0 + w.re • EE 0 1 + EE 1 1

private theorem AA_eq (w : ℂ) (h : w.im ≠ 0) :
    AA w = TR.toL (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (aff (Units.mk0 w.im h) w.re)).val := by
  funext i j v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  change _ = (aff (Units.mk0 w.im h) w.re).val i j
  fin_cases i <;> fin_cases j <;> simp [AA, EE, aff, Matrix.single]

private theorem rmul_AA (w : ℂ) (j : Fin 2) : TR.rmul (EE 0 j) (AA w) = w.im • EE 0 j := by
  funext a b v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  change (Matrix.of (AA w) * Matrix.of (EE 0 j)) a b Rat.infinitePlace = _
  fin_cases a <;> fin_cases b <;> fin_cases j <;> simp [AA, EE, Matrix.single, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem chart_AA (ψ : GA ℚ 2 → ℂ) (w : ℂ) (h : w.im ≠ 0) :
    TR.chart ψ 1 (AA w) = ψ (upR (aff (Units.mk0 w.im h) w.re)) := by
  rw [AA_eq w h, TR.chart_val, one_mul]
  rfl

private theorem hasFDerivAt_AA (w : ℂ) :
    HasFDerivAt AA (Complex.imCLM.smulRight (EE 0 0) + Complex.reCLM.smulRight (EE 0 1)) w :=
  (Complex.imCLM.smulRight (EE 0 0) + Complex.reCLM.smulRight (EE 0 1)).hasFDerivAt.add_const (EE 1 1)

private theorem key (k : ℕ) (φ : TR.Sm ℚ 2) (hφ : IsLow k φ) (w : ℂ) (hw : 0 < w.im) :
    DifferentiableAt ℂ (fun w : ℂ => ((w.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * TR.chart φ.1 1 (AA w)) w := by
  have hm : AA w ∈ TR.invSet ℚ 2 := by rw [AA_eq w hw.ne']; exact TR.val_mem_invSet _
  have hc := ((TR.contDiffAt_chart φ.2 1 hm).differentiableAt (by simp)).hasFDerivAt
  set D := fderiv ℝ (TR.chart φ.1 1) (AA w) with hD
  set g := upR (aff (Units.mk0 w.im hw.ne') w.re) with hg
  have he : ∀ j, (TR.Eop Rat.infinitePlace 0 j φ).1 g = (w.im : ℂ) * D (EE 0 j) := fun j => by
    have h1 := TR.chart_lieD φ.2 (EE 0 j) 1 hm
    rw [chart_AA _ w hw.ne', rmul_AA, map_smul, Complex.real_smul] at h1
    exact h1
  have h1 : (TR.Eop Rat.infinitePlace 0 1 φ).1 g - (TR.Eop Rat.infinitePlace 1 0 φ).1 g = Complex.I * k * φ.1 g :=
    congrFun (congrArg Subtype.val (hφ.wt Rat.infinitePlace)) g
  have h2 : (TR.Eop Rat.infinitePlace 0 0 φ).1 g - (TR.Eop Rat.infinitePlace 1 1 φ).1 g =
      Complex.I * ((TR.Eop Rat.infinitePlace 0 1 φ).1 g + (TR.Eop Rat.infinitePlace 1 0 φ).1 g) :=
    congrFun (congrArg Subtype.val (hφ.low Rat.infinitePlace)) g
  have h3 : (TR.Eop Rat.infinitePlace 0 0 φ).1 g + (TR.Eop Rat.infinitePlace 1 1 φ).1 g = 0 :=
    congrFun (congrArg Subtype.val (hφ.one Rat.infinitePlace)) g
  rw [he] at h1 h2 h3
  rw [he] at h2
  have h4 : (w.im : ℂ) * D (EE 0 0) = Complex.I * (w.im * D (EE 0 1)) + k / 2 * φ.1 g := by
    linear_combination (h2 + h3) / 2 - Complex.I / 2 * h1 - (k / 2 * φ.1 g) * Complex.I_mul_I
  have hp := Complex.ofRealCLM.hasFDerivAt.comp w
    ((Complex.imCLM.hasFDerivAt (x := w)).rpow_const (p := -((k : ℝ) / 2)) (Or.inl hw.ne'))
  have hF := hp.fun_mul (hc.comp w (hasFDerivAt_AA w))
  refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨hF.differentiableAt, ?_⟩
  erw [hF.fderiv]
  have hy : (w.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
  have hr : w.im ^ (-((k : ℝ) / 2) - 1) = w.im ^ (-((k : ℝ) / 2)) / w.im := Real.rpow_sub_one hw.ne' _
  simp [chart_AA _ w hw.ne', ← hg, hr]
  field_simp
  linear_combination 2 * ((w.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * h4

end UpperTheory.V.Br.DescentHolomorphic

open UpperTheory.V.Br.DescentHolomorphic in
theorem UpperTheory.V.Br.downHol :
    UpperTheory.V.Br.DownHol := by
  intro k φ hφ
  refine UpperHalfPlane.mdifferentiable_iff.2 ?_
  refine DifferentiableOn.congr (fun w hw => (key k φ hφ w hw).differentiableWithinAt) fun w hw => ?_
  have hw' : 0 < w.im := hw
  rw [Function.comp_apply, ofComplex_apply_of_im_pos hw', chart_AA _ w hw'.ne']
  rfl
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.DownLift
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
open UpperHalfPlane hiding I

namespace UpperTheory.V.Br.DescentLift

private noncomputable def sc (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Real.exp t) (Real.exp_pos t).ne')

private theorem sc_val (t : ℝ) : (sc t).val = !![Real.exp t, 0; 0, Real.exp t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sc]

private theorem sc_add (s t : ℝ) : sc (s + t) = sc s * sc t := by
  refine Units.ext ?_
  rw [Units.val_mul, sc_val, sc_val, sc_val]
  simp [Real.exp_add]

private theorem sc_zero : sc 0 = 1 := by
  refine Units.ext ?_
  rw [sc_val, Real.exp_zero, Units.val_one, Matrix.one_fin_two]

private theorem sc_inv (φ : TR.Sm ℚ 2) (h : ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) (g : GA ℚ 2) (t : ℝ) :
    φ.1 (g * upR (sc t)) = φ.1 g := by
  classical
  let X : TR.Lie ℚ 2 := TR.toL 1
  have hX : X = TR.toL (Matrix.single 0 0 (Pi.single Rat.infinitePlace 1)) +
      TR.toL (Matrix.single 1 1 (Pi.single Rat.infinitePlace 1)) := by
    ext i j u
    rw [Subsingleton.elim u Rat.infinitePlace]
    fin_cases i <;> fin_cases j <;> simp [X]
  have hL : TR.lie ℚ 2 X φ = 0 := by
    rw [hX, map_add (f := _), LinearMap.add_apply, ← h Rat.infinitePlace]
    simp only [TR.Eop]
    congr!
  let c : ℝ → GL (Fin 2) (TR.Rinf ℚ) := fun s => Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (sc s)
  have hcv : ∀ s i j v, (c s).val i j v = (sc s).val i j := fun _ _ _ _ => rfl
  have hc : HasDerivAt (fun s : ℝ => TR.toL (c s).val) X 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    have h1 : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
    show HasDerivAt (fun s => (sc s).val i j) _ 0
    simp only [sc_val]
    fin_cases i <;> fin_cases j
    · simpa [X] using h1
    · simpa [X] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa [X] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa [X] using h1
  let f : ℝ → ℂ := fun t => φ.1 (g * upR (sc t))
  have hf : ∀ t, HasDerivAt f 0 t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * upR (sc t)) c X (by simp only [c, sc_zero, map_one]) hc
    rw [← TR.lie_apply, hL] at h1
    have h2 : HasDerivAt (fun s => f (t + s)) 0 0 := by
      simpa only [f, sc_add, map_mul, mul_assoc] using! h1
    have h3 := HasDerivAt.comp_sub_const t t (f := fun s => f (t + s)) (by rw [sub_self]; exact h2)
    simpa using h3
  have h4 := is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt) (fun t => (hf t).deriv) t 0
  simpa only [f, sc_zero, map_one, mul_one] using h4

private noncomputable def rot (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] (by
    rw [Matrix.det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ])

private theorem rot_val (θ : ℝ) : (rot θ).val = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl

private theorem rot_det (θ : ℝ) : (rot θ).val.det = 1 := by
  rw [rot_val, Matrix.det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem rot_eig (φ : TR.Sm ℚ 2) (z : ℂ) (h : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z • φ) (g : GA ℚ 2) (θ : ℝ) :
    φ.1 (g * upR (rot θ)) = Complex.exp (z * θ) * φ.1 g := by
  have := rotEig ℚ φ z h (fun _ => θ) (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (rot θ)) (by
    ext i j v
    fin_cases i <;> fin_cases j <;> rfl) g
  simpa using! this

private theorem nsl_rot (k : ℕ) (f : ℍ → ℂ) (θ : ℝ) :
    nsl k f (rot θ).val UpperHalfPlane.I = Complex.exp (Complex.I * k * θ) * f UpperHalfPlane.I := by
  have e : (((rot θ).val 1 0 : ℝ) : ℂ) * (UpperHalfPlane.I : ℍ) + ((rot θ).val 1 1 : ℝ) = Complex.exp (-(θ * Complex.I)) := by
    rw [← neg_mul, Complex.exp_mul_I]
    simp [rot_val]
    ring
  have e' : (((rot θ).val 0 0 : ℝ) : ℂ) * (UpperHalfPlane.I : ℍ) + ((rot θ).val 0 1 : ℝ) =
      Complex.I * Complex.exp (-(θ * Complex.I)) := by
    rw [← neg_mul, Complex.exp_mul_I]
    simp [rot_val]
    linear_combination (Complex.sin θ) * Complex.I_mul_I
  simp only [nsl]
  rw [e, e', rot_det, mul_div_cancel_right₀ _ (Complex.exp_ne_zero _), ← Complex.exp_int_mul]
  have : ofComplex Complex.I = UpperHalfPlane.I := ofComplex_apply UpperHalfPlane.I
  simp only [abs_one, Real.one_rpow, sign_one, SignType.coe_one, Complex.ofReal_one, one_mul, this]
  congr 2
  push_cast
  ring

private theorem nsl_aff (k : ℕ) (φ : GA ℚ 2 → ℂ) (y x : ℝ) (hy : 0 < y) :
    nsl k (down k φ) (aff (Units.mk0 y hy.ne') x).val UpperHalfPlane.I = φ (upR (aff (Units.mk0 y hy.ne') x)) := by
  have hv : (aff (Units.mk0 y hy.ne') x).val = !![y, x; 0, 1] := rfl
  have hd : (!![y, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = y := by simp
  let z : ℍ := ⟨⟨x, y⟩, hy⟩
  have hz : down k φ z = ((y ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * φ (upR (aff (Units.mk0 y hy.ne') x)) := rfl
  have e : (y : ℂ) * Complex.I + x = (z : ℂ) := by
    apply Complex.ext <;> simp [z]
  simp only [nsl]
  rw [hv, hd, abs_of_pos hy, sign_pos hy]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, Complex.ofReal_one, zero_mul, zero_add, one_zpow, mul_one, div_one, SignType.coe_one, one_mul, coe_I]
  rw [e, ofComplex_apply, hz, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hy]
  simp

private theorem iwasawa (h : GL (Fin 2) ℝ) (hh : 0 < h.val.det) :
    ∃ (y : ℝ) (hy : 0 < y) (x θ t : ℝ), h = aff (Units.mk0 y hy.ne') x * rot θ * sc t := by
  set a := h.val 0 0 with ha
  set b := h.val 0 1 with hb
  set c := h.val 1 0 with hc
  set d := h.val 1 1 with hd
  rw [Matrix.det_fin_two, ← ha, ← hb, ← hc, ← hd] at hh
  let w : ℂ := ⟨d, -c⟩
  have hw : w ≠ 0 := by
    intro h0
    have h1 : d = 0 := congrArg Complex.re h0
    have h2 : -c = 0 := congrArg Complex.im h0
    rw [h1, neg_eq_zero.1 h2] at hh
    simp at hh
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h1 : ‖w‖ * Real.cos w.arg = d := Complex.norm_mul_cos_arg w
  have h2 : ‖w‖ * Real.sin w.arg = -c := Complex.norm_mul_sin_arg w
  have h3 : ‖w‖ ^ 2 = c ^ 2 + d ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [w]; ring
  have hn : 0 < c ^ 2 + d ^ 2 := h3 ▸ pow_pos hr 2
  refine ⟨(a * d - b * c) / (c ^ 2 + d ^ 2), div_pos hh hn, (a * c + b * d) / (c ^ 2 + d ^ 2), w.arg, Real.log ‖w‖, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, sc_val, rot_val, Real.exp_log hr]
  change _ = !![(a * d - b * c) / (c ^ 2 + d ^ 2), (a * c + b * d) / (c ^ 2 + d ^ 2); 0, 1] * _ * _
  rw [Matrix.eta_fin_two h.val, ← ha, ← hb, ← hc, ← hd, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  refine congrArg₂ (fun p q => ![p, q]) (congrArg₂ (fun p q => ![p, q]) ?_ ?_) (congrArg₂ (fun p q => ![p, q]) ?_ ?_)
  · field_simp
    linear_combination (-(a * d - b * c)) * h1 + (a * c + b * d) * h2
  · field_simp
    linear_combination (-(a * d - b * c)) * h2 - (a * c + b * d) * h1
  · linear_combination h2
  · linear_combination -h1

private theorem pos_case (k : ℕ) (φ : TR.Sm ℚ 2) (hφ : IsLow k φ) (h : GL (Fin 2) ℝ) (hh : 0 < h.val.det) :
    φ.1 (upR h) = nsl k (down k φ.1) h.val UpperHalfPlane.I := by
  obtain ⟨y, hy, x, θ, t, rfl⟩ := iwasawa h hh
  have e : (aff (Units.mk0 y hy.ne') x * rot θ * sc t).val = Real.exp t • ((aff (Units.mk0 y hy.ne') x).val * (rot θ).val) := by
    rw [Units.val_mul, Units.val_mul, sc_val]
    ext i j
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  rw [e, (nslMul k _).2.2.1 _ _ (Real.exp_pos t),
    ← (nslMul k _).1 _ _ (Matrix.isUnits_det_units _).ne_zero (by rw [rot_det]; exact one_pos), nsl_rot, nsl_aff k _ y x hy,
    map_mul, map_mul, sc_inv φ hφ.one, rot_eig φ _ hφ.wt]

private def epsQ : GL (Fin 2) ℚ := ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

private theorem toR_epsQ : (toR epsQ).val = eps := by
  ext i j
  show Rat.castHom ℝ (epsQ.val i j) = _
  fin_cases i <;> fin_cases j <;> simp [epsQ, eps]

private theorem toF_epsQ (N : ℕ) : toF epsQ ∈ K1G N := by
  have h : ∀ a b, (toF epsQ).val a b ∈ Ohat ℚ := fun a b => by
    show algebraMap ℚ (Af ℚ) (epsQ.val a b) ∈ _
    fin_cases a <;> fin_cases b <;> simp [epsQ, one_mem, zero_mem]
  refine (memK N _).2 ⟨h, ?_, ⟨0, zero_mem _, ?_⟩, 0, zero_mem _, ?_⟩
  · rw [← map_inv]
    exact h
  · show algebraMap ℚ (Af ℚ) (epsQ.val 1 0) = _
    simp [epsQ]
  · show algebraMap ℚ (Af ℚ) (epsQ.val 1 1) - 1 = _
    simp [epsQ]

end UpperTheory.V.Br.DescentLift

open UpperTheory.V.Br.DescentLift in
theorem UpperTheory.V.Br.downLift :
    UpperTheory.V.Br.DownLift := by
  intro k N _ φ hr hφ hK γ h u hu
  have hfin : ∀ u ∈ K1G N, ∀ g, φ.1 (g * finGL ℚ 2 u) = φ.1 g := fun u hu g =>
    congrFun (congrArg Subtype.val (hK u hu)) g
  rw [hr, hfin u hu]
  rcases lt_or_gt_of_ne (Matrix.isUnits_det_units h).ne_zero with hd | hd
  · have e : (toR epsQ * h).val = eps * h.val := by rw [Units.val_mul, toR_epsQ]
    have hd' : 0 < (toR epsQ * h).val.det := by
      rw [e, Matrix.det_mul]
      simpa [eps, Matrix.det_fin_two_of] using hd
    rw [← (nslMul k _).2.1, ← e, ← pos_case k φ hφ _ hd', ← hr epsQ (upR h), ratGL_eq, mul_assoc, ← upR_comm, ← mul_assoc,
      hfin _ (toF_epsQ N), map_mul]
  · exact pos_case k φ hφ h hd
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelP
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br

open UpperTheory.V.Af

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}

private theorem infOf_of_weights {m : Fin n → ℤ} {x : Multiset ℂ}
    (h : (Finset.univ.val.map fun i => -m i).map (fun k : ℤ => (k : ℂ)) = x.map fun z => ((n : ℂ) - 1) / 2 - z) :
    x = infOf m := by
  have h2 := congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) h
  simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id'] at h2
  rw [← h2, infOf]
  exact Multiset.map_congr rfl fun i _ => by push_cast; ring

end UpperTheory.V.Br


end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PerZero
section
open Filter Topology Asymptotics Function
open scoped Real

private theorem UpperTheory.V.Br.per_tendsto {g : ℂ → ℂ} {h : ℝ} (hh : 0 < h) (hp : Periodic g h)
    (hd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ g z) (C : ℝ) (m : ℕ)
    (hb : ∀ z : ℂ, 1 ≤ z.im → |z.re| ≤ h → ‖g z‖ ≤ C * z.im ^ m) :
    ∃ c, Tendsto g (comap Complex.im atTop) (𝓝 c) := by
  have hb' : ∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ C * z.im ^ m := by
    intro z hz
    have h1 := hp.sub_int_mul_eq (x := z) ⌊z.re / h⌋
    have h2 := Int.sub_floor_div_mul_nonneg z.re hh
    have h3 := Int.sub_floor_div_mul_lt z.re hh
    have h4 := hb (z - (⌊z.re / h⌋ : ℤ) * (h : ℂ)) (by simpa using hz)
      (by simp only [Complex.sub_re, Complex.mul_re, Complex.intCast_re, Complex.ofReal_re,
            Complex.intCast_im, Complex.ofReal_im, mul_zero, sub_zero]
          rw [abs_of_nonneg h2]; exact h3.le)
    rw [h1] at h4
    simpa using h4
  have hev : ∀ A : ℝ, ∀ᶠ z : ℂ in comap Complex.im atTop, A ≤ z.im := fun A =>
    tendsto_comap.eventually (eventually_ge_atTop A)
  have hD := Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hp
    ((hev 1).mono fun z hz => hd z (by linarith))
  have hO : Periodic.cuspFunction h g =O[𝓝[≠] 0] fun q : ℂ => |Real.log ‖q‖| ^ (m : ℝ) := by
    refine IsBigO.of_bound (|C| * (h / (2 * π)) ^ m) ?_
    filter_upwards [(Periodic.invQParam_tendsto hh).eventually (hev 1), self_mem_nhdsWithin] with q hq hq0
    rw [Periodic.cuspFunction_eq_of_nonzero h g hq0]
    refine (hb' _ hq).trans ((le_abs_self _).trans (le_of_eq ?_))
    have : 0 < h / (2 * π) := by positivity
    rw [Periodic.im_invQParam, abs_mul, abs_pow, abs_mul, neg_div, abs_neg, abs_of_pos this,
      Real.rpow_natCast, Real.norm_eq_abs, abs_pow, abs_abs, mul_pow, mul_assoc]
  have ho : (fun q : ℂ => |Real.log ‖q‖| ^ (m : ℝ)) =o[𝓝[≠] 0] fun q : ℂ => (q - 0)⁻¹ := by
    have := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (m : ℝ) (s := -1) (by norm_num)).comp_tendsto
      (tendsto_norm_nhdsNE_zero (E := ℂ))
    refine IsLittleO.of_norm_right ?_
    simpa [Function.comp_def, Real.rpow_neg_one] using this
  have hc : (fun _ : ℂ => Periodic.cuspFunction h g 0) =o[𝓝[≠] 0] fun q : ℂ => (q - 0)⁻¹ := by
    refine isLittleO_const_left.2 (Or.inr ?_)
    simpa [Function.comp_def] using (tendsto_inv_nhdsGT_zero.comp (tendsto_norm_nhdsNE_zero (E := ℂ)))
  have hT := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hD
    ((hO.trans_isLittleO ho).sub hc)
  exact ⟨_, by
    simpa only [Function.comp_def, Periodic.eq_cuspFunction hh.ne' hp] using
      hT.comp (Periodic.qParam_tendsto hh)⟩

theorem UpperTheory.V.Br.perZero :
    UpperTheory.V.Br.PerZero := by
  intro f N hN hf hper ⟨C, m, hb⟩ hint
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine GroundTheory.Automorphic.GL2Classical.isZeroAtImInfty_of_integral_vadd_eq_zero hN' hper hf ?_ hint
  obtain ⟨c, hc⟩ := UpperTheory.V.Br.per_tendsto hN'
    (GroundTheory.Automorphic.GL2Classical.periodic_comp_ofComplex_of_vadd hper)
    (fun z hz => (UpperHalfPlane.mdifferentiable_iff.1 hf).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)) C m
    (fun z hz hr => by
      have h0 : 0 < z.im := by linarith
      have := hb ⟨z, h0⟩ hz hr
      simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h0] using this)
  have h2 : Tendsto f UpperHalfPlane.atImInfty (𝓝 c) := by
    have := hc.comp (show Tendsto ((↑) : UpperHalfPlane → ℂ) UpperHalfPlane.atImInfty
      (comap Complex.im atTop) from tendsto_comap_iff.2 tendsto_comap)
    simpa [Function.comp_def] using this
  exact h2.isBigO_one ℝ
end

