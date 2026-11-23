module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.QuadraticFormAddExpand
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem quadraticForm_add_expand (δ : F) (v : V4 F) (i : Fin 4) (a : A F) :
    q4 δ (v + Pi.single i a) = q4 δ v + a * (B4 δ v (Pi.single i 1) + a * q4 δ (Pi.single i 1)) := by
  fin_cases i <;> simp [q4, B4, Pi.single_apply] <;> ring

private theorem psi_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, (adelicChar F).map_add_eq_mul]

private theorem cw_mul (w : InfinitePlace F) (a b : A F) : cw w (a * b) = cw w a * cw w b := by
  simp [cw, map_mul]

private theorem psi_curve (w : InfinitePlace F) (b : A F) (δ : F) (i : Fin 4) (v : V4 F) :
    ∃ g : ℝ → ℂ, (∀ t, ψ (b * q4 δ (v + Pi.single i (at1 w t))) = ψ (b * q4 δ v) * g t) ∧ g 0 = 1 ∧
      HasDerivAt g (cc * (cw w b * cw w (B4 δ v (Pi.single i 1)))) 0 := by
  obtain ⟨hψ, -, hp, -, -, hm, -, -⟩ := atLaws F w
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = TR.pInf F b w * TR.pInf F (B4 δ v (Pi.single i 1)) w := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = TR.pInf F b w * TR.pInf F (q4 δ (Pi.single i 1)) w := ⟨_, rfl⟩
  refine ⟨fun t => Complex.exp (cc * ((t * (β + t * κ) : ℝ) : ℂ)), ?_, by simp, ?_⟩
  · intro t
    have h0 : at1 w t * (b * (B4 δ v (Pi.single i 1) + at1 w t * q4 δ (Pi.single i 1))) =
        at1 w (t * (β + t * κ)) := by
      rw [hm]
      congr 2
      have : TR.pInf F (at1 w t) w = t := by rw [hp]; simp
      simp only [map_mul, map_add (f := _), Pi.mul_apply, Pi.add_apply, this, hβ, hκ]
      ring
    have h1 : b * q4 δ (v + Pi.single i (at1 w t)) = b * q4 δ v + at1 w (t * (β + t * κ)) := by
      rw [quadraticForm_add_expand, ← h0]
      ring
    rw [h1, psi_add, hψ]
  · have hu : HasDerivAt (fun t : ℝ => t * (β + t * κ)) β 0 := by
      have := (hasDerivAt_id' (0 : ℝ)).fun_mul (((hasDerivAt_id' (0 : ℝ)).mul_const κ).const_add β)
      simpa using this
    have h2 := (hu.ofReal_comp.const_mul cc).cexp
    convert h2 using 1
    simp [hβ, cw]

private theorem p_apply (O : Ops F) (δ : F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (v : V4 F) :
    (O.p δ w i φ).1 v = cc * cw w (B4 δ v (Pi.single i 1)) * φ.1 v := by
  have hs : ∀ (c : ℂ) (T : Module.End ℂ (S4 F)), ((c • T) φ).1 v = c * (T φ).1 v := fun _ _ => rfl
  have hn : ∀ a : A F, cw w (-a) = -cw w a := fun a => by simp [cw]
  have h2 : cw w (2 : A F) = 2 := by
    have : TR.pInf F (2 : A F) = 2 := map_ofNat _ 2
    simp [cw, this]
  fin_cases i
  · have : B4 δ v (Pi.single 0 1) = -v 1 := by simp [B4, Pi.single_apply]
    simp only [Fin.zero_eta, this, hn, Ops.p]
    simp [hs, O.x_apply]
    ring
  · have : B4 δ v (Pi.single 1 1) = -v 0 := by simp [B4, Pi.single_apply]
    simp only [Fin.mk_one, this, hn, Ops.p]
    simp [hs, O.x_apply]
    ring
  · have : B4 δ v (Pi.single 2 1) = 2 * v 2 := by simp [B4, Pi.single_apply]
    simp only [Fin.reduceFinMk, this, cw_mul, h2, Ops.p]
    simp [hs, O.x_apply]
    ring
  · have : B4 δ v (Pi.single 3 1) = (-2 * rt δ) * v 3 := by simp [B4, Pi.single_apply]; ring
    simp only [Fin.reduceFinMk, this, cw_mul, hn, h2, Ops.p]
    simp [hs, O.x_apply]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Fo.dN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w i b, O.d w i * W.Om (nU b) = W.Om (nU b) * (O.d w i + cw w b • O.p D.δ w i) ∧
    O.x w i * W.Om (nU b) = W.Om (nU b) * O.x w i := by
  intro F E _ _ _ _ _ _ _ D W O w i b
  refine ⟨?_, ?_⟩
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    obtain ⟨g, hg, hg0, hgd⟩ := psi_curve w b D.δ i v
    have hφ := O.d_spec w i φ v
    have h1 := O.d_spec w i (W.Om (nU b) φ) v
    have hz : v + Pi.single i (at1 w 0) = v := by
      rw [(atLaws F w).2.2.2.2.1]; simp
    have hfun : (fun t : ℝ => (W.Om (nU b) φ).1 (v + Pi.single i (at1 w t))) =
        fun t => (ψ (b * q4 D.δ v) * g t) * φ.1 (v + Pi.single i (at1 w t)) := by
      funext t
      rw [W.Om_n, hg]
    rw [hfun] at h1
    have h2 := (hgd.const_mul (ψ (b * q4 D.δ v))).mul hφ
    have h3 := h1.unique h2
    change (O.d w i (W.Om (nU b) φ)).1 v = (W.Om (nU b) ((O.d w i + cw w b • O.p D.δ w i) φ)).1 v
    rw [h3, W.Om_n]
    change _ = _ * ((O.d w i φ).1 v + cw w b * (O.p D.δ w i φ).1 v)
    rw [p_apply, hg0, hz]
    ring
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    change (O.x w i (W.Om (nU b) φ)).1 v = (W.Om (nU b) (O.x w i φ)).1 v
    rw [O.x_apply, W.Om_n, W.Om_n, O.x_apply]
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacAnn
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem hasDerivAt_sumq {ι : Type} [Fintype ι] [DecidableEq ι] (K b r : ι → ℝ) (w : ι) :
    HasDerivAt (fun t : ℝ => ∑ w', (K w' * (b w' + (Pi.single w t : ι → ℝ) w') ^ 2 + r w')) (2 * K w * b w) 0 := by
  have h : ∀ w' ∈ (Finset.univ : Finset ι), HasDerivAt (fun t : ℝ => K w' * (b w' + (Pi.single w t : ι → ℝ) w') ^ 2 + r w')
      (if w' = w then 2 * K w * b w else 0) 0 := by
    intro w' _
    by_cases hw : w' = w
    · subst hw
      simp only [Pi.single_eq_same, if_true]
      have h0 : HasDerivAt (fun t : ℝ => b w' + t) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add (b w')
      refine (((h0.fun_pow 2).const_mul (K w')).add_const (r w')).congr_deriv ?_
      simp only [add_zero, Nat.add_one_sub_one, pow_one, mul_one, Nat.cast_ofNat]
      ring
    · simp only [Pi.single_eq_of_ne hw, if_neg hw]
      exact hasDerivAt_const _ _
  have := HasDerivAt.fun_sum h
  simpa using this

private theorem gauss_deriv {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (v : V4 F) (w : InfinitePlace F) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => gauss δ (v + Pi.single i (at1 w t)))
      (-2 * Real.pi * kap δ w i * cw w (v i) * gauss δ v) 0 := by
  obtain ⟨-, -, hp, -, h0, -, -, -⟩ := atLaws F w
  set p := TR.pInf F with hpdef
  let Kf : InfinitePlace F → ℝ := fun w' => ![1, 1, 2, -2 * p (rt δ) w'] i
  let bf : InfinitePlace F → ℝ := fun w' => p (v i) w'
  let Q : V4 F → A F := fun u => u 0 ^ 2 + u 1 ^ 2 + 2 * (u 2 ^ 2 - rt δ * u 3 ^ 2)
  let rf : InfinitePlace F → ℝ := fun w' => p (Q v) w' - Kf w' * bf w' ^ 2
  have hQ : ∀ (t : ℝ) w', p (Q (v + Pi.single i (at1 w t))) w' =
      Kf w' * (bf w' + (Pi.single w t : InfinitePlace F → ℝ) w') ^ 2 + rf w' := by
    intro t w'
    have h2 : p (2 : A F) w' = 2 := by
      rw [map_ofNat]
      rfl
    fin_cases i <;> simp [Q, Kf, bf, rf, hp, h2, map_add (f := _), map_mul, map_pow, map_sub, Pi.single_apply] <;> ring
  have hK : kap δ w i = ((Kf w : ℝ) : ℂ) := by
    fin_cases i <;> simp [kap, Kf, cw, hpdef]
  have hfun : (fun t : ℝ => gauss δ (v + Pi.single i (at1 w t))) = fun t : ℝ => Complex.exp (-(Real.pi : ℂ) *
      ((∑ w', (Kf w' * (bf w' + (Pi.single w t : InfinitePlace F → ℝ) w') ^ 2 + rf w') : ℝ) : ℂ)) := by
    funext t
    simp only [← hQ]
    rfl
  have hC : HasDerivAt (fun t : ℝ => ((∑ w', (Kf w' * (bf w' + (Pi.single w t : InfinitePlace F → ℝ) w') ^ 2 + rf w') : ℝ) : ℂ))
      ((2 * Kf w * bf w : ℝ) : ℂ) 0 := (hasDerivAt_sumq Kf bf rf w).ofReal_comp
  have hX := (hC.const_mul (-(Real.pi : ℂ))).cexp
  have e0 : v + Pi.single i (at1 w 0) = v := by
    rw [h0]
    simp
  have hval := (congrArg (gauss δ) e0).symm.trans (congrFun hfun 0)
  rw [hfun]
  refine hX.congr_deriv ?_
  beta_reduce at hval ⊢
  rw [← hval, hK]
  have hb : cw w (v i) = ((bf w : ℝ) : ℂ) := rfl
  rw [hb]
  push_cast
  ring

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacAnn :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F), ∀ φ ∈ Vac δ, ∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ := by
  intro F _ _ _ δ O φ hφ w i
  obtain ⟨-, -, -, -, -, -, -, hfin⟩ := atLaws F w
  apply Subtype.ext
  funext v
  have hg := gauss_deriv δ v w i
  have hne : gauss δ v ≠ 0 := Complex.exp_ne_zero _
  have hf : ∀ t : ℝ, finPartPi (v + Pi.single i (at1 w t)) = finPartPi v := by
    intro t
    have := hfin t i
    funext j
    have hj := congrFun this j
    simp only [finPartPi] at hj ⊢
    change (v j).2 + ((Pi.single i (at1 w t) : V4 F) j).2 = (v j).2
    rw [hj]
    exact add_zero _
  have h1 : (fun t : ℝ => φ.1 (v + Pi.single i (at1 w t))) = fun t : ℝ => (φ.1 v / gauss δ v) * gauss δ (v + Pi.single i (at1 w t)) := by
    funext t
    have := hφ (v + Pi.single i (at1 w t)) v (hf t)
    field_simp
    exact this
  have hd := O.d_spec w i φ v
  rw [h1] at hd
  have hu := hd.unique (hg.const_mul (φ.1 v / gauss δ v))
  change _ = (-2 * Real.pi * kap δ w i) * (O.x w i φ).1 v
  rw [hu, O.x_apply]
  field_simp
end

