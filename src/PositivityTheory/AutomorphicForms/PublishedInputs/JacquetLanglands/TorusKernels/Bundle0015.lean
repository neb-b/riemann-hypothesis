module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.AutomorphicFormsLeSm
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicKernelAlgebraProof
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HyperbolicKernelAlgebraLemmas

variable {F : Type} [Field F] [NumberField F]

def rotA (θ : TR.Rinf F) : GL (Fin 2) (TR.Rinf F) where
  val := !![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)]
  inv := !![fun v => Real.cos (θ v), fun v => -Real.sin (θ v); fun v => Real.sin (θ v), fun v => Real.cos (θ v)]
  val_inv := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith
  inv_val := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith

omit [NumberField F] in
theorem rotA_add (θ η : TR.Rinf F) : rotA (θ + η) = rotA θ * rotA η := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rotA, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

omit [NumberField F] in
theorem rotA_zero : rotA (0 : TR.Rinf F) = 1 := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rotA]

theorem rotA_deriv (θ : TR.Rinf F) :
    HasDerivAt (fun t : ℝ => TR.toL (rotA (t • θ)).val) (TR.toL !![0, θ; -θ, 0]) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
  have h : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)
  fin_cases i <;> fin_cases j
  · simpa [rotA] using h.cos
  · simpa [rotA] using h.sin
  · simpa [rotA] using h.sin.fun_neg
  · simpa [rotA] using h.cos

variable [IsTotallyReal F]

theorem lie_rotV {k : InfinitePlace F → ℕ} {φ : TR.Sm F 2}
    (hw : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k v) • φ) (θ : TR.Rinf F) :
    TR.lie F 2 (TR.toL !![0, θ; -θ, 0]) φ = (∑ v, Complex.I * k v * ((θ v : ℝ) : ℂ)) • φ := by
  classical
  have e : (TR.toL !![0, θ; -θ, 0] : TR.Lie F 2) = ∑ v, θ v • ((TR.toL (Matrix.single 0 1 (Pi.single v 1)) : TR.Lie F 2) -
      TR.toL (Matrix.single 1 0 (Pi.single v 1))) := by
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [Finset.sum_apply, Matrix.single, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, ← hw v]
  simp only [TR.Eop]
  congr!

theorem rot_eq {k : InfinitePlace F → ℕ} {φ : TR.Sm F 2}
    (hw : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k v) • φ) (θ : TR.Rinf F) (g : GA F 2) :
    φ.1 (g * TR.infGL F 2 (rotA θ)) * Complex.exp (-∑ v, Complex.I * k v * ((θ v : ℝ) : ℂ)) = φ.1 g := by
  set s : ℂ := ∑ v, Complex.I * k v * ((θ v : ℝ) : ℂ) with hs
  set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rotA (t • θ))) with hf
  have hd : ∀ t, HasDerivAt f (s * f t) t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * TR.infGL F 2 (rotA (t • θ))) (fun u : ℝ => rotA (u • θ)) _
      (by simp [rotA_zero]) (rotA_deriv θ)
    rw [← TR.lie_apply, lie_rotV hw] at h1
    have h2 : HasDerivAt (fun u : ℝ => f (t + u)) (s * f t) 0 := by
      convert h1 using 2
      · simp only [hf, add_smul, rotA_add, map_mul, mul_assoc]
    have h3 := HasDerivAt.comp_add_const t (-t) (f := fun u : ℝ => f (t + u)) (by simpa using h2)
    simpa using h3
  have he : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-s * t)) (Complex.exp (-s * t) * -s) t := fun t => by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-s)).cexp
  have hz : ∀ t, HasDerivAt (fun t : ℝ => f t * Complex.exp (-s * t)) 0 t := fun t => by
    have := (hd t).fun_mul (he t)
    rwa [show s * f t * Complex.exp (-s * t) + f t * (Complex.exp (-s * t) * -s) = 0 by ring] at this
  have hc := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv) 1 0
  simpa [hf, rotA_zero] using hc

theorem infGL_scalar (ρ : (TR.Rinf F)ˣ) :
    TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) ρ) = Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.infId F ρ) := by
  have h1 : TR.pInf F (TR.infId F ρ).val = ρ.val := by
    change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
    have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
    simp [h]
  have h2 : pFin F (TR.infId F ρ).val = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h1]
  · rw [TR.pFin_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h2]

theorem fin_expU {ω : HChar F} (h : IsOfFinOrder ω) (z : TR.Rinf F) : ω.1 (TR.infId F (TR.expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : TR.expU z = TR.expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, TR.expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

theorem scal {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2}
    (hφ : IsHolV k c ω φ) (z : TR.Rinf F) (h : GA F 2) :
    φ.1 (h * TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.expU z))) = φ.1 h := by
  rw [infGL_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent, fin_expU hω]
  simp

theorem inf_fin_comm (y : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    TR.infGL F 2 y * finGL F 2 x = finGL F 2 x * TR.infGL F 2 y :=
  TR.ga_ext (by simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one, one_mul])
    (by simp only [map_mul, TR.pFin_infGL, pFin_finGL, mul_one, one_mul])

theorem stab {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2}
    (hφ : IsHolV k c ω φ) (r : GL (Fin 2) (TR.Rinf F)) (hr : ∀ v, gv v r • iP = iP) (h : GA F 2) :
    φ.1 (h * TR.infGL F 2 r) * ∏ v, j1 (k v) (gv v r) iP = φ.1 h := by
  have hgv : ∀ v i j, (gv v r) i j = r i j v := fun v i j => rfl
  have hE : ∀ v, r 1 1 v = r 0 0 v ∧ r 1 0 v = -r 0 1 v := fun v => by
    have h1 := congrArg Subtype.val (hr v)
    rw [coe_smul, div_eq_iff (den_ne _ iP.2)] at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp [num, den, iP, hgv] at hre him
    constructor <;> linarith
  set w : InfinitePlace F → ℂ := fun v => ⟨r 0 0 v, r 0 1 v⟩ with hw
  have hw0 : ∀ v, w v ≠ 0 := fun v h0 => by
    have ha : r 0 0 v = 0 := congrArg Complex.re h0
    have hb : r 0 1 v = 0 := congrArg Complex.im h0
    apply (gv v r).det_ne_zero
    rw [det_eq]
    simp only [hgv, (hE v).1, (hE v).2, ha, hb]
    ring
  have hρ : ∀ v, 0 < ‖w v‖ := fun v => norm_pos_iff.2 (hw0 v)
  set θ : TR.Rinf F := fun v => Complex.arg (w v) with hθ
  set u := TR.expU (fun v => Real.log ‖w v‖) with hu0
  have hu : ∀ v, (u : TR.Rinf F) v = ‖w v‖ := fun v => by
    rw [hu0, TR.expU_val, Real.exp_log (hρ v)]
  have hc : ∀ v, Real.cos (θ v) = r 0 0 v / ‖w v‖ := fun v => Complex.cos_arg (hw0 v)
  have hs : ∀ v, Real.sin (θ v) = r 0 1 v / ‖w v‖ := fun v => Complex.sin_arg _
  have hdec : r = Matrix.GeneralLinearGroup.scalar (Fin 2) u * rotA θ := by
    ext i j v
    have h0 := (hρ v).ne'
    fin_cases i <;> fin_cases j <;>
      simp [rotA, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.GeneralLinearGroup.scalar, hu, hc, hs, (hE v).1, (hE v).2] <;>
      field_simp
  have hj : ∀ v, j1 (k v) (gv v r) iP = Complex.exp (-(Complex.I * k v * ((θ v : ℝ) : ℂ))) := fun v => by
    unfold j1
    have hden : den (gv v r) iP.1 = (‖w v‖ : ℂ) * Complex.exp (-((θ v : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
      have h0 := (hρ v).ne'
      apply Complex.ext <;> simp [den, hgv, (hE v).1, (hE v).2, iP] <;> field_simp
    have hdet : |(gv v r).val.det| = ‖w v‖ ^ 2 := by
      rw [det_eq, Complex.sq_norm, Complex.normSq_apply]
      simp only [hgv, (hE v).1, (hE v).2, hw]
      rw [abs_of_nonneg (by nlinarith [mul_self_nonneg (r 0 0 v), mul_self_nonneg (r 0 1 v)])]
      ring
    have hp : (‖w v‖ ^ 2) ^ (-(k v : ℝ) / 2) = (‖w v‖ ^ (k v))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast, ← Real.rpow_neg (norm_nonneg _)]
      congr 1
      push_cast
      ring
    rw [hden, hdet, hp, mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_inv, Complex.ofReal_pow, mul_right_comm,
      mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast (hρ v).ne')), one_mul]
    congr 1
    ring
  have hinf : h * TR.infGL F 2 r =
      (h * TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) * TR.infGL F 2 (rotA θ) := by
    rw [mul_assoc, ← map_mul, ← hdec]
  rw [Finset.prod_congr rfl fun v _ => hj v, ← Complex.exp_sum, Finset.sum_neg_distrib, hinf, rot_eq hφ.wt θ,
    hu0, scal hω hφ]

theorem key (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2}
    (hφ : IsHolV k c ω φ) (g g' : GL (Fin 2) (TR.Rinf F)) (x : GF F) (h : ∀ v, gv v g • iP = gv v g' • iP) :
    φ.1 (TR.infGL F 2 g' * finGL F 2 x) * ∏ v, j1 (k v) (gv v g') iP =
      φ.1 (TR.infGL F 2 g * finGL F 2 x) * ∏ v, j1 (k v) (gv v g) iP := by
  obtain ⟨r, rfl⟩ : ∃ r, g' = g * r := ⟨g⁻¹ * g', by group⟩
  have hs : ∀ v, gv v r • iP = iP := fun v => by
    have := h v
    rw [map_mul, mul_smul] at this
    exact ((smul_left_cancel_iff _).1 this).symm
  have hj : ∀ v, j1 (k v) (gv v (g * r)) iP = j1 (k v) (gv v g) iP * j1 (k v) (gv v r) iP := fun v => by
    rw [map_mul, hB.1, hs v]
  have hc : TR.infGL F 2 (g * r) * finGL F 2 x = (TR.infGL F 2 g * finGL F 2 x) * TR.infGL F 2 r := by
    rw [map_mul, mul_assoc, mul_assoc, inf_fin_comm]
  rw [Finset.prod_congr rfl fun v _ => hj v, Finset.prod_mul_distrib, hc,
    ← stab hω hφ r hs (TR.infGL F 2 g * finGL F 2 x)]
  ring

end UpperTheory.Esk.HyperbolicKernelAlgebraLemmas

theorem UpperTheory.Esk.hyperbolic_kernel_algebra_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.H1a := by
  intro hB _ F _ _ _ k c ω φ hω hφ
  classical
  refine ⟨fun p => if h : ∃ g : GL (Fin 2) (TR.Rinf F), (fun v => UpperTheory.Esk.gv v g • UpperTheory.Esk.iP) = p.1 then
      φ.1 (TR.infGL F 2 h.choose * finGL F 2 p.2) * ∏ v, UpperTheory.Esk.j1 (k v) (UpperTheory.Esk.gv v h.choose) UpperTheory.Esk.iP else 0,
    fun g x => ?_⟩
  have h : ∃ g' : GL (Fin 2) (TR.Rinf F), (fun v => UpperTheory.Esk.gv v g' • UpperTheory.Esk.iP) = fun v => UpperTheory.Esk.gv v g • UpperTheory.Esk.iP :=
    ⟨g, rfl⟩
  dsimp only
  rw [dite_eq_left h]
  exact UpperTheory.Esk.HyperbolicKernelAlgebraLemmas.key hB hω hφ h.choose g x fun v => congrFun h.choose_spec v
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicKernelContinuity
section
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.Esk.HyperbolicKernelContinuity

theorem norm_omega {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Ideles F) : ‖((ω.1 z : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  have e3 : ω.1 z ^ n = 1 := by
    have := DFunLike.congr_fun e2 z
    simpa using this
  have e4 : ((ω.1 z : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, e3, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one e4 hn.ne'

end UpperTheory.Esk.HyperbolicKernelContinuity

theorem UpperTheory.Esk.hyperbolic_kernel_continuity : UpperTheory.Esk.H1c := by
  intro F _ _ _ k c ω φ hω hφ hcusp
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cuspForms ((UpperTheory.V.Fb.isCuspForm_iff φ).1 hcusp)
  refine ⟨C, fun g => ?_⟩
  obtain ⟨s, y, hy, rfl⟩ := exists_centralSection_mul_mem_normOneGL g
  have hz : centralSection F 2 s = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (posIdeleHom F (rpowHom ((2 * Module.finrank ℚ F : ℝ))⁻¹ s)) := by
    refine Units.ext ?_
    ext i j
    simp [centralSection, scalarUnits_apply, coe_diagUnits, Matrix.diagonal_apply, Matrix.scalar_apply]
  rw [hz, hφ.cent, norm_mul, UpperTheory.Esk.HyperbolicKernelContinuity.norm_omega hω, one_mul]
  exact hC y hy
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicOrbitBoundProof
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped ContDiff

namespace UpperTheory.Esk.ImaginaryUnitActionLemmas

open UpperTheory.Esk


open Classical in
def Fx {I : Type} (f : X I → ℂ) (w : I → ℂ) : ℂ :=
  if h : ∀ v, (w v).im ≠ 0 then f (fun v => ⟨w v, h v⟩) else 0

theorem Fx_eq {I : Type} (f : X I → ℂ) {w : I → ℂ} (h : ∀ v, (w v).im ≠ 0) :
    Fx f w = f (fun v => ⟨w v, h v⟩) := by
  rw [Fx, dite_eq_left h]

theorem Fx_val {I : Type} (f : X I → ℂ) (z : X I) : Fx f (fun v => (z v).1) = f z :=
  Fx_eq f (fun v => (z v).2)

theorem isOpen_U (I : Type) [Finite I] : IsOpen {w : I → ℂ | ∀ v, (w v).im ≠ 0} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun v =>
    isOpen_ne_fun (Complex.continuous_im.comp (continuous_apply v)) continuous_const

theorem analytic_Fx (hO : Osg) {I : Type} [Fintype I] (f : X I → ℂ) (hf : SepHol f) :
    AnalyticOnNhd ℂ (Fx f) {w : I → ℂ | ∀ v, (w v).im ≠ 0} := by
  classical
  obtain ⟨hc, hh⟩ := hf
  refine hO I _ (isOpen_U I) (Fx f) ?_ ?_
  · rw [continuousOn_iff_continuous_domRestrict]
    have e : Set.domRestrict {w : I → ℂ | ∀ v, (w v).im ≠ 0} (Fx f) = fun w => f (fun v => ⟨w.1 v, w.2 v⟩) := by
      funext w
      exact Fx_eq f w.2
    rw [e]
    refine hc.comp (continuous_pi fun v => ?_)
    exact Continuous.subtype_mk ((continuous_apply v).comp continuous_subtype_val) _
  · intro w hw v
    have hw' : ∀ u, (w u).im ≠ 0 := hw
    let z : X I := fun u => ⟨w u, hw' u⟩
    have hd := hh z v
    have hopen : IsOpen {t : ℂ | t.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
    have hmem : {t : ℂ | t.im ≠ 0} ∈ nhds (w v) := hopen.mem_nhds (hw' v)
    refine (DifferentiableOn.differentiableAt hd hmem).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with t ht
    have ht' : t.im ≠ 0 := ht
    have hu : ∀ u, (Function.update w v t u).im ≠ 0 := by
      intro u
      by_cases huv : u = v
      · subst huv
        simpa using ht'
      · simpa [Function.update_of_ne huv] using hw' u
    rw [Fx_eq f hu]
    unfold ext1
    rw [dite_eq_left ht']
    congr 1
    funext u
    apply Subtype.ext
    exact (Function.apply_update (fun _ (p : P) => p.1) z v ⟨t, ht'⟩ u).symm

def dn (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ((M 1 0 : ℝ) : ℂ) * Complex.I + ((M 1 1 : ℝ) : ℂ)

def nm (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ((M 0 0 : ℝ) : ℂ) * Complex.I + ((M 0 1 : ℝ) : ℂ)

def dt (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := M 0 0 * M 1 1 - M 0 1 * M 1 0

def jj (k : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := dn M ^ k * ((|dt M| ^ (-(k : ℝ) / 2) : ℝ) : ℂ)

theorem smul_iP (g : GL (Fin 2) ℝ) : (g • iP).1 = nm g.val * (dn g.val)⁻¹ := by
  rw [coe_smul, div_eq_mul_inv]
  rfl

theorem automorphy_factor_at_i_eq (k : ℕ) (g : GL (Fin 2) ℝ) : j1 k g iP = jj k g.val := by
  unfold j1 jj dt
  rw [det_eq]
  rfl

theorem dn_ne {M : Matrix (Fin 2) (Fin 2) ℝ} (h : dt M ≠ 0) : dn M ≠ 0 := by
  intro e
  have h1 := congrArg Complex.re e
  have h2 := congrArg Complex.im e
  simp [dn] at h1 h2
  apply h
  simp [dt, h1, h2]

theorem cd_parts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (M : E → Matrix (Fin 2) (Fin 2) ℝ) (m0 : E)
    (hM : ∀ i j, ContDiffAt ℝ ∞ (fun m => M m i j) m0) (h0 : dt (M m0) ≠ 0) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun m => nm (M m) * (dn (M m))⁻¹) m0 ∧ ContDiffAt ℝ ∞ (fun m => jj k (M m)) m0 := by
  have hC : ∀ i j, ContDiffAt ℝ ∞ (fun m => ((M m i j : ℝ) : ℂ)) m0 := fun i j =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp m0 (hM i j)
  have hdn : ContDiffAt ℝ ∞ (fun m => dn (M m)) m0 := by
    unfold dn
    exact ((hC 1 0).mul contDiffAt_const).add (hC 1 1)
  have hnm : ContDiffAt ℝ ∞ (fun m => nm (M m)) m0 := by
    unfold nm
    exact ((hC 0 0).mul contDiffAt_const).add (hC 0 1)
  have hdt : ContDiffAt ℝ ∞ (fun m => dt (M m)) m0 := by
    unfold dt
    exact ((hM 0 0).mul (hM 1 1)).sub ((hM 0 1).mul (hM 1 0))
  refine ⟨hnm.mul (hdn.inv (dn_ne h0)), ?_⟩
  unfold jj
  exact (hdn.pow k).mul (Complex.ofRealCLM.contDiff.contDiffAt.comp m0
    ((hdt.abs h0).rpow_const_of_ne (p := -(k : ℝ) / 2) (abs_ne_zero.2 h0)))

theorem chart_smooth (hO : Osg) (hB : B1b) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (k : InfinitePlace F → ℕ) (f : X (InfinitePlace F) × GF F → ℂ) (φ : GA F 2 → ℂ)
    (hf : ∀ x, SepHol fun z => f (z, x)) (hR : Rel k f φ) (g0 : GA F 2) :
    ContDiffOn ℝ ∞ (TR.chart φ g0) (TR.invSet F 2) := by
  obtain ⟨-, hj1, -⟩ := hB
  obtain ⟨y0, x0, rfl⟩ : ∃ (y0 : GL (Fin 2) (TR.Rinf F)) (x0 : GF F), g0 = TR.infGL F 2 y0 * finGL F 2 x0 :=
    ⟨_, _, (TR.infGL_mul_finGL g0).symm⟩
  have hj : ∀ g : GL (Fin 2) (TR.Rinf F), ∏ v, j1 (k v) (gv v g) iP ≠ 0 :=
    fun g => Finset.prod_ne_zero_iff.2 fun v _ => hj1 _ _ _
  have key : ∀ y : GL (Fin 2) (TR.Rinf F), TR.chart φ (TR.infGL F 2 y0 * finGL F 2 x0) (TR.toL y.val) =
      f (fun v => gv v (y0 * y) • iP, x0) * (∏ v, j1 (k v) (gv v (y0 * y)) iP)⁻¹ := by
    intro y
    have e : TR.infGL F 2 y0 * finGL F 2 x0 * TR.infGL F 2 y = TR.infGL F 2 (y0 * y) * finGL F 2 x0 := by
      rw [mul_assoc, ← TR.infGL_comm, ← mul_assoc, ← map_mul]
    rw [TR.chart_val, e, eq_mul_inv_iff_mul_eq₀ (hj _)]
    exact hR (y0 * y) x0
  let A : Matrix (Fin 2) (Fin 2) (TR.Rinf F) := y0.val
  let M : InfinitePlace F → TR.Lie F 2 → Matrix (Fin 2) (Fin 2) ℝ := fun v m i j => ∑ l, A i l v * m l j v
  have hM : ∀ (y : GL (Fin 2) (TR.Rinf F)) v, M v (TR.toL y.val) = (gv v (y0 * y)).val := by
    intro y v
    ext i j
    simp only [M, A]
    change _ = ((y0 * y).val i j) v
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_apply]
    rfl
  let G : TR.Lie F 2 → ℂ := fun m => Fx (fun z => f (z, x0)) (fun v => nm (M v m) * (dn (M v m))⁻¹) *
    (∏ v, jj (k v) (M v m))⁻¹
  have hG : ∀ y : GL (Fin 2) (TR.Rinf F),
      TR.chart φ (TR.infGL F 2 y0 * finGL F 2 x0) (TR.toL y.val) = G (TR.toL y.val) := by
    intro y
    rw [key]
    simp only [G, hM, ← smul_iP, ← automorphy_factor_at_i_eq]
    rw [Fx_val]
  have hA := analytic_Fx hO (fun z => f (z, x0)) (hf x0)
  refine ContDiffOn.congr (f := G) (fun m hm => ?_) (fun m hm => ?_)
  · obtain ⟨y, rfl⟩ := id hm
    have hE : ∀ v i j, ContDiffAt ℝ ∞ (fun m : TR.Lie F 2 => M v m i j) (TR.toL y.val) := by
      intro v i j
      have hc : ∀ l, ContDiff ℝ ∞ (fun m : TR.Lie F 2 => m l j v) := fun l =>
        (contDiff_apply ℝ (fun _ => ℝ) v).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ l))
      exact (ContDiff.sum fun l _ => contDiff_const.mul (hc l)).contDiffAt
    have hdt : ∀ v, dt (M v (TR.toL y.val)) ≠ 0 := by
      intro v
      rw [hM]
      have h := (gv v (y0 * y)).det_ne_zero
      rw [det_eq] at h
      exact h
    have hP : ∀ v, ContDiffAt ℝ ∞ (fun m => nm (M v m) * (dn (M v m))⁻¹) (TR.toL y.val) ∧
        ContDiffAt ℝ ∞ (fun m => jj (k v) (M v m)) (TR.toL y.val) := fun v => cd_parts (M v) _ (hE v) (hdt v) (k v)
    have hw : ∀ v, (nm (M v (TR.toL y.val)) * (dn (M v (TR.toL y.val)))⁻¹).im ≠ 0 := by
      intro v
      rw [hM, ← smul_iP]
      exact (gv v (y0 * y) • iP).2
    have h1 : ContDiffAt ℝ ∞ (fun m => Fx (fun z => f (z, x0)) (fun v => nm (M v m) * (dn (M v m))⁻¹))
        (TR.toL y.val) :=
      ContDiffAt.comp (g := Fx (fun z => f (z, x0))) (TR.toL y.val)
        ((hA (fun v => nm (M v (TR.toL y.val)) * (dn (M v (TR.toL y.val)))⁻¹) hw).contDiffAt.restrict_scalars ℝ)
        ((contDiffAt_pi (Φ := fun m v => nm (M v m) * (dn (M v m))⁻¹)).2 fun v => (hP v).1)
    have h2 : ContDiffAt ℝ ∞ (fun m => ∏ v, jj (k v) (M v m)) (TR.toL y.val) :=
      contDiffAt_prod fun v _ => (hP v).2
    have h3 : (∏ v, jj (k v) (M v (TR.toL y.val))) ≠ 0 := by
      simp only [hM, ← automorphy_factor_at_i_eq]
      exact hj (y0 * y)
    exact (h1.mul (h2.inv h3)).contDiffWithinAt
  · obtain ⟨y, rfl⟩ := id hm
    exact hG y

end UpperTheory.Esk.ImaginaryUnitActionLemmas

theorem UpperTheory.Esk.hyperbolic_orbit_bound_proof : UpperTheory.Esk.Osg → UpperTheory.Esk.B1b → UpperTheory.Esk.H2b := by
  intro hO hB F _ _ _ k c _ om χ _ _ _ _ f φ hf hR g
  exact UpperTheory.Esk.ImaginaryUnitActionLemmas.chart_smooth hO hB F k f φ hf.hol hR g
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfGCh
section
noncomputable section

open scoped NNReal

namespace UpperTheory.Esk.CharacterExpansionLemmas

theorem key (ν : Valuation ℂ ℝ≥0) (τ δ : ℂ) (hτ : ν τ ≤ 1) (hδ : ν δ ≤ 1) :
    ∀ n, ν (ch τ δ n) ≤ 1 ∧ ν (ch τ δ (n + 1)) ≤ 1 ∧ ν (ch τ δ (n + 1) - τ ^ n) ≤ ν δ := by
  intro n
  induction n with
  | zero => simp [ch]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have e : ch τ δ (n + 2) = τ * ch τ δ (n + 1) - δ * ch τ δ n := rfl
    have e2 : ch τ δ (n + 2) - τ ^ (n + 1) = τ * (ch τ δ (n + 1) - τ ^ n) - δ * ch τ δ n := by
      rw [e]; ring
    refine ⟨h1, ?_, ?_⟩
    · rw [e]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [Valuation.map_mul]
      · calc ν τ * ν (ch τ δ (n + 1)) ≤ 1 * 1 := mul_le_mul' hτ h1
          _ = 1 := one_mul _
      · calc ν δ * ν (ch τ δ n) ≤ 1 * 1 := mul_le_mul' hδ h0
          _ = 1 := one_mul _
    · rw [e2]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [Valuation.map_mul]
      · calc ν τ * ν (ch τ δ (n + 1) - τ ^ n) ≤ 1 * ν δ := mul_le_mul' hτ h2
          _ = ν δ := one_mul _
      · calc ν δ * ν (ch τ δ n) ≤ ν δ * 1 := mul_le_mul' le_rfl h0
          _ = ν δ := mul_one _

end UpperTheory.Esk.CharacterExpansionLemmas

theorem UpperTheory.Esk.pf_GCh : UpperTheory.Esk.GCh := fun ν τ δ hτ hδ n =>
  ⟨(UpperTheory.Esk.CharacterExpansionLemmas.key ν τ δ hτ hδ n).2.1, (UpperTheory.Esk.CharacterExpansionLemmas.key ν τ δ hτ hδ n).2.2⟩
end
end

