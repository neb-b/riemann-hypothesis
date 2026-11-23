module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.AnnVac
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private noncomputable def kA (δ : F) : Fin 4 → A F := ![1, 1, 2, -2 * rt δ]

private noncomputable def qG (δ : F) (v : V4 F) : A F := v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)

private theorem kap_eq (δ : F) (w : InfinitePlace F) (i : Fin 4) :
    kap δ w i = ((TR.pInf F (kA δ i) w : ℝ) : ℂ) := by
  have h2 : TR.pInf F (2 : A F) w = 2 := by
    rw [map_ofNat]
    rfl
  fin_cases i <;> simp [kap, kA, cw, h2]

private theorem form_step (δ : F) (v : V4 F) (i : Fin 4) (s : A F) :
    qG δ (v + Pi.single i s) = qG δ v + kA δ i * (2 * v i * s + s * s) := by
  fin_cases i <;> simp [qG, kA, Pi.single_apply] <;> ring

private theorem sum_step (w : InfinitePlace F) (K b : InfinitePlace F → ℝ) (t : ℝ) :
    ∑ w', (K * (2 * b * Pi.single w t + Pi.single w t * Pi.single w t) : InfinitePlace F → ℝ) w' =
      K w * (2 * b w * t + t * t) := by
  rw [Finset.sum_eq_single w]
  · simp
  · intro b' _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ w) h

private theorem gauss_step (δ : F) (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    gauss δ (v + Pi.single i (at1 w t)) =
      gauss δ v * Complex.exp (-((Real.pi : ℂ) * kap δ w i * (2 * cw w (v i) * t + t * t))) := by
  have hp : TR.pInf F (at1 w t) = Pi.single w t := (atLaws F w).2.2.1 t
  have hs : (∑ w', TR.pInf F (qG δ (v + Pi.single i (at1 w t))) w' : ℝ) =
      (∑ w', TR.pInf F (qG δ v) w') +
        TR.pInf F (kA δ i) w * (2 * TR.pInf F (v i) w * t + t * t) := by
    rw [form_step, ← sum_step w (TR.pInf F (kA δ i)) (TR.pInf F (v i)) t,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w' _ => ?_
    have h2 : TR.pInf F (2 : A F) = 2 := by rw [map_ofNat]
    simp only [map_add (f := _), map_mul, hp, h2, Pi.add_apply]
  have hg : ∀ u : V4 F, gauss δ u =
      Complex.exp (-(Real.pi : ℂ) * ((∑ w', TR.pInf F (qG δ u) w' : ℝ) : ℂ)) := by
    intro u
    unfold gauss qG
    rfl
  rw [hg, hg, hs, ← Complex.exp_add, kap_eq]
  congr 1
  simp only [cw]
  push_cast
  ring

private theorem cw_step (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    cw w ((v + Pi.single i (at1 w t) : V4 F) i) = cw w (v i) + t := by
  have hp : TR.pInf F (at1 w t) = Pi.single w t := (atLaws F w).2.2.1 t
  simp [cw, hp]

private theorem line_step (δ : F) (O : Ops F) (φ : S4 F)
    (h : ∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ)
    (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    φ.1 (v + Pi.single i (at1 w t)) * gauss δ v = φ.1 v * gauss δ (v + Pi.single i (at1 w t)) := by
  set a : ℂ := cw w (v i) with ha
  set κ : ℂ := kap δ w i with hκ
  let f : ℝ → ℂ := fun t => φ.1 (v + Pi.single i (at1 w t))
  let X : ℝ → ℂ := fun t => (Real.pi : ℂ) * κ * (2 * a * t + t * t)
  have hf : ∀ t, HasDerivAt f (-2 * Real.pi * κ * (a + t) * f t) t := by
    intro t
    have h0 := O.d_spec w i φ (v + Pi.single i (at1 w t))
    have e : (fun s : ℝ => φ.1 (v + Pi.single i (at1 w t) + Pi.single i (at1 w s))) = fun s => f (t + s) := by
      funext s
      simp only [f]
      rw [(atLaws F w).2.2.2.1 t s, Pi.single_add, add_assoc]
    rw [e] at h0
    have h1 : HasDerivAt (fun s => f (t + s)) ((O.d w i φ).1 (v + Pi.single i (at1 w t))) (t - t) := by
      simpa using h0
    have h2 := h1.comp_sub_const t t
    have e2 : (fun x => f (t + (x - t))) = f := by
      funext x
      simp
    rw [e2] at h2
    have key : (O.d w i φ).1 (v + Pi.single i (at1 w t)) = -2 * Real.pi * κ * (a + t) * f t := by
      rw [h w i]
      change (-2 * Real.pi * kap δ w i) * (O.x w i φ).1 (v + Pi.single i (at1 w t)) = _
      rw [O.x_apply, cw_step]
      simp only [f]
      ring
    rw [key] at h2
    exact h2
  have hX : ∀ t : ℝ, HasDerivAt X ((Real.pi : ℂ) * κ * (2 * a + 2 * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h2 := ((h1.const_mul (2 * a)).add (h1.mul h1)).const_mul ((Real.pi : ℂ) * κ)
    exact h2.congr_deriv (by ring)
  have hE : ∀ t : ℝ, HasDerivAt (fun t => f t * Complex.exp (X t)) 0 t := by
    intro t
    have h2 := (hf t).mul (hX t).cexp
    exact h2.congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hE t).differentiableAt) (fun t => (hE t).deriv) t 0
  have h0 : f 0 = φ.1 v := by
    simp only [f]
    rw [(atLaws F w).2.2.2.2.1]
    simp
  have hX0 : X 0 = 0 := by simp [X]
  simp only [hX0, Complex.exp_zero, mul_one, h0] at hc
  rw [gauss_step, ← hc]
  have : Complex.exp (X t) * Complex.exp (-X t) = 1 := by
    rw [← Complex.exp_add]
    simp
  change f t * gauss δ v = f t * Complex.exp (X t) * (gauss δ v * Complex.exp (-X t))
  linear_combination (-(f t * gauss δ v)) * this

private theorem chain_step (δ : F) (O : Ops F) (φ : S4 F)
    (h : ∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ)
    (v : V4 F) (c : Fin 4 × InfinitePlace F → ℝ) (s : Finset (Fin 4 × InfinitePlace F)) :
    φ.1 (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) * gauss δ v =
      φ.1 v * gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.sum_insert hp, add_comm (Pi.single p.1 _), ← add_assoc]
    have hs := line_step δ O φ h (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) p.1 p.2 (c p)
    have hg : gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) ≠ 0 := Complex.exp_ne_zero _
    refine mul_right_cancel₀ hg ?_
    linear_combination (gauss δ v) * hs +
      (gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p)) + Pi.single p.1 (at1 p.2 (c p)))) * ih

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Fo.annVac :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F) (φ : S4 F), (∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ) → φ ∈ Vac δ := by
  intro F _ _ _ δ O φ h v v' e
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  let c : Fin 4 × InfinitePlace F → ℝ := fun p => TR.pInf F (v' p.1 - v p.1) p.2
  have hv : v' = v + ∑ p, Pi.single p.1 (at1 p.2 (c p)) := by
    funext j
    have h0 : (v' j - v j).2 = 0 := by
      have := congrFun e j
      change (v j).2 = (v' j).2 at this
      change (v' j).2 - (v j).2 = 0
      rw [this, sub_self]
    have h1 := (atLaws F w₀).2.2.2.2.2.2.1 (v' j - v j) h0
    have h2 : (∑ p : Fin 4 × InfinitePlace F, (Pi.single p.1 (at1 p.2 (c p)) : V4 F)) j = v' j - v j := by
      rw [h1, Fintype.sum_prod_type, Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp [c, ← h1]
      · intro b _ hb
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun w _ => Pi.single_eq_of_ne hb.symm _
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [Pi.add_apply, h2]
    abel
  have := chain_step δ O φ h v c Finset.univ
  rw [← hv] at this
  exact this.symm ▸ (by ring)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CwShift
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private lemma cw_shift {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (w w' : InfinitePlace F) (i j : Fin 4) (v : V4 F) (t : ℝ) :
    cw w' ((v + Pi.single i (at1 w t) : V4 F) j) = cw w' (v j) + if w = w' ∧ i = j then (t : ℂ) else 0 := by
  have hp := ((atLaws F w).2.2.1) t
  by_cases hij : i = j
  · subst hij
    have h1 : (v + Pi.single i (at1 w t) : V4 F) i = v i + at1 w t := by simp
    rw [h1]
    unfold cw
    rw [map_add (f := _), Pi.add_apply, hp]
    by_cases hw : w = w'
    · subst hw; simp
    · have : w' ≠ w := fun h => hw h.symm
      simp [hw, this]
  · have h1 : (v + Pi.single i (at1 w t) : V4 F) j = v j := by
      simp [Pi.single_apply, Ne.symm hij]
    rw [h1]
    simp [hij]

theorem UpperTheory.ConvolutionTheory.R2.Fo.weyl :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F) w w' i j, O.x w i * O.x w' j = O.x w' j * O.x w i ∧
    O.d w i * O.x w' j = O.x w' j * O.d w i + if w = w' ∧ i = j then 1 else 0 := by
  intro F _ _ _ O w w' i j
  refine ⟨?_, ?_⟩
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    change (O.x w i (O.x w' j φ)).1 v = (O.x w' j (O.x w i φ)).1 v
    rw [O.x_apply, O.x_apply, O.x_apply, O.x_apply, mul_left_comm]
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    have h0 : at1 w 0 = (0 : A F) := (atLaws F w).2.2.2.2.1
    have hv : (v + Pi.single i (at1 w 0) : V4 F) = v := by rw [h0]; simp
    set C : Prop := w = w' ∧ i = j with hC
    have hg := O.d_spec w i φ v
    have hh : HasDerivAt (fun t : ℝ => cw w' (v j) + if C then (t : ℂ) else 0) (if C then 1 else 0) 0 := by
      by_cases c : C
      · simp only [if_pos c]
        exact (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add _ |>.congr_deriv (by simp)
      · simp only [if_neg c]
        exact hasDerivAt_const _ _
    have hm := hh.mul hg
    have hd := O.d_spec w i (O.x w' j φ) v
    have he : (fun t : ℝ => (O.x w' j φ).1 (v + Pi.single i (at1 w t) : V4 F)) =
        (fun t : ℝ => cw w' (v j) + if C then (t : ℂ) else 0) * fun t : ℝ => φ.1 (v + Pi.single i (at1 w t) : V4 F) := by
      funext t
      rw [O.x_apply, cw_shift]
      rfl
    rw [he] at hd
    have hu := hd.unique hm
    change (O.d w i (O.x w' j φ)).1 v = (O.x w' j (O.d w i φ)).1 v + ((if C then (1 : Module.End ℂ (S4 F)) else 0) φ).1 v
    rw [hu, O.x_apply, hv]
    by_cases c : C
    · simp [c]; ring
    · simp [c]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FinPartMulVec
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem finPart_mulVec {F : Type} [Field F] [NumberField F] (M : Matrix (Fin 4) (Fin 4) (A F))
    {v v' : V4 F} (e : finPartPi v = finPartPi v') : finPartPi (M *ᵥ v) = finPartPi (M *ᵥ v') := by
  funext i
  have e' : ∀ j, (v j).2 = (v' j).2 := fun j => congrFun e j
  let s : A F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have e'' : ∀ j, s (v j) = s (v' j) := e'
  change s ((M *ᵥ v) i) = s ((M *ᵥ v') i)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, e'']

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (h : GL (Fin 2) (A E)), (Matrix.GeneralLinearGroup.map (pInf E) h).val ∈ Matrix.unitaryGroup (Fin 2) (Cinf E) →
    ∀ φ ∈ Vac D.δ, W.L h φ ∈ Vac D.δ := by
  intro F E _ _ _ _ _ _ _ D W h hu φ hφ v v' e
  have hinv : (Matrix.GeneralLinearGroup.map (pInf E) h⁻¹).val ∈ Matrix.unitaryGroup (Fin 2) (Cinf E) := by
    have hs := Unitary.star_mem hu
    have hm : (Matrix.GeneralLinearGroup.map (pInf E) h⁻¹).val = star (Matrix.GeneralLinearGroup.map (pInf E) h).val := by
      have h1 : (Matrix.GeneralLinearGroup.map (pInf E) h⁻¹).val * (Matrix.GeneralLinearGroup.map (pInf E) h).val = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      have h2 : (Matrix.GeneralLinearGroup.map (pInf E) h).val * star (Matrix.GeneralLinearGroup.map (pInf E) h).val = 1 :=
        Unitary.mul_star_self_of_mem hu
      exact left_inv_eq_right_inv h1 h2
    rw [hm]
    exact hs
  have hg := gaussAct F E D h⁻¹ hinv
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hfin : finPartPi (D.act h⁻¹ v) = finPartPi (D.act h⁻¹ v') := by
    rw [hρ, hρ]
    exact finPart_mulVec _ e
  have key := hφ _ _ hfin
  rw [hg, hg] at key
  rw [W.L_apply, W.L_apply, mul_assoc, mul_assoc, key]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.PsiShift
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section
variable {F : Type} [Field F] [NumberField F]

private theorem psi_add (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem norm_psi (a : A F) : ‖ψ a‖ = 1 := by
  exact Circle.norm_coe _

private theorem cont_psi : Continuous (ψ : A F → ℂ) :=
  continuous_subtype_val.comp continuous_adelicChar

private theorem B_add (δ : F) (y v v' : V4 F) : B4 δ y (v + v') = B4 δ y v + B4 δ y v' := by
  simp only [B4, Pi.add_apply]
  ring

private theorem B_single (δ : F) (y : V4 F) (i : Fin 4) (a : A F) :
    B4 δ y (Pi.single i a) = a * B4 δ y (Pi.single i 1) := by
  fin_cases i <;> simp [B4] <;> ring

private theorem cont_B (δ : F) (v : V4 F) : Continuous fun y : V4 F => B4 δ y v := by
  unfold B4
  exact ((continuous_const.mul (((continuous_apply 2).mul continuous_const).sub
    (continuous_const.mul ((continuous_apply 3).mul continuous_const)))).sub
    ((continuous_apply 1).mul continuous_const)).sub ((continuous_apply 0).mul continuous_const)

variable [IsTotallyReal F]

private theorem cw_add (w : InfinitePlace F) (a b : A F) : cw w (a + b) = cw w a + cw w b := by
  simp [cw]
private theorem cw_sub (w : InfinitePlace F) (a b : A F) : cw w (a - b) = cw w a - cw w b := by
  simp [cw]
private theorem cw_mul (w : InfinitePlace F) (a b : A F) : cw w (a * b) = cw w a * cw w b := by
  simp [cw]
private theorem cw_neg (w : InfinitePlace F) (a : A F) : cw w (-a) = -cw w a := by
  simp [cw]
private theorem cw_two (w : InfinitePlace F) : cw w (2 : A F) = 2 := by
  have h1 : cw w (1 : A F) = 1 := by simp [cw]
  rw [show (2 : A F) = 1 + 1 by norm_num, cw_add, h1]
  norm_num

private theorem p_apply (δ : F) (O : Ops F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (y : V4 F) :
    (O.p δ w i φ).1 y = cc * cw w (B4 δ y (Pi.single i 1)) * φ.1 y := by
  fin_cases i <;>
    simp [Ops.p, B4, O.x_apply, cw_add, cw_sub, cw_mul, cw_neg, cw_two] <;> ring

private theorem psi_shift (δ : F) (w : InfinitePlace F) (i : Fin 4) (y v : V4 F) (t : ℝ) :
    ψ (B4 δ y (v + Pi.single i (at1 w t))) =
      ψ (B4 δ y v) * Complex.exp (cc * cw w (B4 δ y (Pi.single i 1)) * t) := by
  obtain ⟨h1, -, -, -, -, h6, -, -⟩ := atLaws F w
  rw [B_add, psi_add, B_single, h6, h1]
  congr 2
  simp only [cw]
  push_cast
  ring

private theorem deriv_gen {X : Type} [MeasurableSpace X] (μ : Measure X) (f G : X → ℂ) (u : ℝ → X → ℂ) (c : X → ℂ)
    (hf : Integrable f μ) (hG : Integrable G μ) (hu : ∀ t, AEStronglyMeasurable (u t) μ)
    (hn : ∀ t y, ‖u t y‖ = 1) (hd : ∀ t y, HasDerivAt (fun s => u s y) (c y * u t y) t)
    (hc : ∀ y, G y = c y * f y) :
    HasDerivAt (fun t => ∫ y, f y * u t y ∂μ) (∫ y, G y * u 0 y ∂μ) 0 := by
  have hm : ∀ t, AEStronglyMeasurable (fun y => f y * u t y) μ := fun t => hf.1.mul (hu t)
  have hm' : ∀ t, AEStronglyMeasurable (fun y => G y * u t y) μ := fun t => hG.1.mul (hu t)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t y => f y * u t y) (F' := fun t y => G y * u t y)
    (x₀ := (0 : ℝ)) (s := Set.univ) (bound := fun y => ‖G y‖) univ_mem
    (Eventually.of_forall hm)
    (hf.mono (hm 0) (ae_of_all _ fun y => by rw [norm_mul, hn, mul_one]))
    (hm' 0)
    (ae_of_all _ fun y t _ => by rw [norm_mul, hn, mul_one])
    hG.norm
    (ae_of_all _ fun y t _ => ?_)).2
  refine ((hd t y).const_mul (f y)).congr_deriv ?_
  rw [hc]
  ring

private theorem psi_deriv (δ : F) (w : InfinitePlace F) (i : Fin 4) (y v : V4 F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ψ (B4 δ y (v + Pi.single i (at1 w s))))
      (cc * cw w (B4 δ y (Pi.single i 1)) * ψ (B4 δ y (v + Pi.single i (at1 w t)))) t := by
  have h1 : HasDerivAt (fun s : ℝ => cc * cw w (B4 δ y (Pi.single i 1)) * (s : ℂ))
      (cc * cw w (B4 δ y (Pi.single i 1))) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (cc * cw w (B4 δ y (Pi.single i 1)))
  have h2 := h1.cexp.const_mul (ψ (B4 δ y v))
  simp only [psi_shift]
  refine h2.congr_deriv ?_
  ring

private theorem deriv_ops (O : Ops F) (δ : F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (u : ℝ → V4 F → ℂ) (c : V4 F → ℂ)
    (hu : ∀ t, AEStronglyMeasurable (u t) (adeleMeasurePi F)) (hn : ∀ t y, ‖u t y‖ = 1)
    (hd : ∀ t y, HasDerivAt (fun s => u s y) (c y * u t y) t) (hc : ∀ y, (O.p δ w i φ).1 y = c y * φ.1 y) :
    HasDerivAt (fun t => ∫ y, φ.1 y * u t y ∂(adeleMeasurePi F)) (∫ y, (O.p δ w i φ).1 y * u 0 y ∂(adeleMeasurePi F)) 0 :=
  deriv_gen (adeleMeasurePi F) φ.1 (O.p δ w i φ).1 u c (integrable_of_mem_schwartzBruhatPi φ.2)
    (integrable_of_mem_schwartzBruhatPi (O.p δ w i φ).2) hu hn hd hc

private theorem key (δ : F) (O : Ops F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (v : V4 F) :
    HasDerivAt (fun t : ℝ => ft4 δ φ.1 (v + Pi.single i (at1 w t))) (ft4 δ (O.p δ w i φ).1 v) 0 := by
  obtain ⟨-, -, -, -, h0, -, -, -⟩ := atLaws F w
  obtain ⟨u, hu⟩ : ∃ u : ℝ → V4 F → ℂ, ∀ t y, u t y = ψ (B4 δ y (v + Pi.single i (at1 w t))) := ⟨_, fun _ _ => rfl⟩
  have hm : ∀ t, AEStronglyMeasurable (u t) (adeleMeasurePi F) := fun t => by
    rw [show u t = fun y => ψ (B4 δ y (v + Pi.single i (at1 w t))) from funext (hu t)]
    exact (cont_psi.comp (cont_B δ _)).aestronglyMeasurable
  have hn : ∀ t y, ‖u t y‖ = 1 := fun t y => by rw [hu]; exact norm_psi _
  have hd : ∀ t y, HasDerivAt (fun s => u s y) (cc * cw w (B4 δ y (Pi.single i 1)) * u t y) t := fun t y => by
    rw [show (fun s => u s y) = fun s => ψ (B4 δ y (v + Pi.single i (at1 w s))) from funext fun s => hu s y, hu]
    exact psi_deriv δ w i y v t
  have h := deriv_ops O δ w i φ u (fun y => cc * cw w (B4 δ y (Pi.single i 1))) hm hn hd (fun y => p_apply δ O w i φ y)
  have e1 : (fun t : ℝ => ft4 δ φ.1 (v + Pi.single i (at1 w t))) = fun t => ∫ y, φ.1 y * u t y ∂(adeleMeasurePi F) := by
    simp only [ft4, hu]
  have e2 : ft4 δ (O.p δ w i φ).1 v = ∫ y, (O.p δ w i φ).1 y * u 0 y ∂(adeleMeasurePi F) := by
    simp only [ft4, hu, h0, Pi.single_zero, add_zero]
  rw [e1, e2]
  exact h

end

theorem UpperTheory.ConvolutionTheory.R2.Fo.dW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w i, O.d w i * W.Om (wW F) = W.Om (wW F) * O.p D.δ w i := by
  intro F E _ _ _ _ _ _ _ D W O w i
  refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
  rw [Module.End.mul_apply, Module.End.mul_apply]
  rw [W.Om_w (O.p D.δ w i φ) v]
  have hd := O.d_spec w i (W.Om (wW F) φ) v
  simp only [W.Om_w] at hd
  exact hd.unique (key D.δ O w i φ v)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.QuaternaryFormEqOfFinitePart
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem mul_eq_of_inf_zero {F : Type} [Field F] [NumberField F] (x u u' : A F) (hx : x.1 = 0)
    (h : u.2 = u'.2) : x * u = x * u' := by
  apply Prod.ext
  · change x.1 * u.1 = x.1 * u'.1
    rw [hx, zero_mul, zero_mul]
  · change x.2 * u.2 = x.2 * u'.2
    rw [h]

private theorem quaternaryForm_eq_of_finitePart {F : Type} [Field F] [NumberField F] (δ : F) (a v v' : V4 F)
    (ha : ∀ i, (a i).1 = 0) (h : finPartPi v = finPartPi v') : B4 δ a v = B4 δ a v' := by
  have e : ∀ i j, a i * v j = a i * v' j := fun i j =>
    mul_eq_of_inf_zero _ _ _ (ha i) (congrFun h j)
  simp only [B4, e]

theorem UpperTheory.ConvolutionTheory.R2.Fo.lFix :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (y : GL (Fin 2) (Cinf E)) Λ, ∀ φ ∈ Fix D.δ Λ, W.L (infGL E 2 y) φ ∈ Fix D.δ Λ := by
  intro F E _ _ _ _ _ _ _ D W y Λ φ hφ
  have hφ' : ∀ a : V4 F, (∀ i, (a i).1 = 0 ∧ (a i).2 ∈ Λ) → ∀ v,
      φ.1 (v + a) = φ.1 v ∧ ψ (B4 D.δ a v) * φ.1 v = φ.1 v := hφ
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hinv : (infGL E 2 y)⁻¹ = infGL E 2 y⁻¹ := (map_inv (infGL E 2) y).symm
  have hfin := UpperTheory.ConvolutionTheory.R2.Fo.actFin F E D y⁻¹

  have key : ∀ a : V4 F, (∀ i, (a i).1 = 0) → D.act (infGL E 2 y⁻¹) a = a := by
    intro a ha
    let e : A F := (0, 1)
    have hea : e • a = a := by
      funext i
      apply Prod.ext
      · change (0 : _) * (a i).1 = (a i).1
        rw [ha i, mul_zero]
      · change (1 : _) * (a i).2 = (a i).2
        rw [one_mul]
    have hinf : D.act (infGL E 2 y⁻¹) a = e • D.act (infGL E 2 y⁻¹) a := by
      rw [hρ, ← Matrix.mulVec_smul, hea]
    funext i
    apply Prod.ext
    · rw [hinf, ha i]
      change (0 : _) * _ = 0
      rw [zero_mul]
    · exact congrFun (hfin a) i
  change ∀ a : V4 F, (∀ i, (a i).1 = 0 ∧ (a i).2 ∈ Λ) → ∀ v,
    (W.L (infGL E 2 y) φ).1 (v + a) = (W.L (infGL E 2 y) φ).1 v ∧
      ψ (B4 D.δ a v) * (W.L (infGL E 2 y) φ).1 v = (W.L (infGL E 2 y) φ).1 v
  intro a ha v
  have hfix := key a fun i => (ha i).1
  have hact : D.act (infGL E 2 y⁻¹) (v + a) = D.act (infGL E 2 y⁻¹) v + a := by
    rw [hρ, Matrix.mulVec_add, ← hρ, ← hρ, hfix]
  have hB : B4 D.δ a v = B4 D.δ a (D.act (infGL E 2 y⁻¹) v) :=
    quaternaryForm_eq_of_finitePart _ _ _ _ (fun i => (ha i).1) (hfin v).symm
  refine ⟨?_, ?_⟩
  · rw [W.L_apply, W.L_apply, hinv, hact, (hφ' a ha _).1]
  · rw [W.L_apply, hinv, mul_left_comm, hB, (hφ' a ha _).2]
end

