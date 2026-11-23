module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAb
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg' {K : Type} [Field K] [NumberField K]
    (S : Set (Fin 4 → FiniteAdeleRing (𝓞 K) K)) (N : ℕ) (v : V4 K) : 0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem continuous_ab {K : Type} [Field K] [NumberField K] :
    Continuous (ab : (A K)ˣ → ℝ) :=
  continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule (K := K))

private theorem ab_pos {K : Type} [Field K] [NumberField K] (a : (A K)ˣ) : 0 < ab a :=
  (IdeleGroup.ideleModule K a).2

theorem UpperTheory.ConvolutionTheory.R2.Ff.lDom :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), LDom W := by
  intro F E _ _ _ _ _ _ _ D W ι s Φ hΦ C hC
  obtain ⟨K, hK, hΦ⟩ := hΦ
  obtain ⟨ρ, hρ, hact, hnu, -, -⟩ := actCont F E D

  let r : GL (Fin 2) (A E) → GL (Fin 4) (A F) := fun h => ρ h⁻¹
  have hr : Continuous r := hρ.comp continuous_inv
  obtain ⟨K', hK', hlin⟩ := wtLin F (r '' C) (hC.image hr) K hK

  let β : GL (Fin 2) (A E) → ℝ := fun h => (ab (nu F h))⁻¹
  have hβ : Continuous β :=
    (continuous_ab.comp hnu).inv₀ fun h => (ab_pos _).ne'
  obtain ⟨A₀, hA₀⟩ := (hC.image hβ).bddAbove
  refine ⟨K', hK', fun N => ?_⟩
  obtain ⟨B, hB⟩ := hΦ N
  obtain ⟨B', hB'⟩ := hlin N
  refine ⟨|A₀| * (|B| * B'), ?_⟩
  rintro ⟨h, i⟩ ⟨hh, hi⟩ v
  have hβ0 : 0 ≤ β h := (inv_pos.2 (ab_pos _)).le
  have hβA : β h ≤ |A₀| := (hA₀ ⟨h, hh, rfl⟩).trans (le_abs_self _)
  have hnorm : ‖(W.L h (Φ i)).1 v‖ = β h * ‖(Φ i).1 (D.act h⁻¹ v)‖ := by
    rw [W.L_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]
  have h1 : ‖(Φ i).1 (D.act h⁻¹ v)‖ ≤ |B| * (B' * wt K' N v) := by
    have h2 : wt K N ((r h).val *ᵥ v) ≤ B' * wt K' N v := hB' (r h) ⟨h, hh, rfl⟩ v
    have h3 := hB i hi (D.act h⁻¹ v)
    rw [hact h⁻¹ v] at h3 ⊢
    calc _ ≤ B * wt K N ((r h).val *ᵥ v) := h3
      _ ≤ |B| * wt K N ((r h).val *ᵥ v) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg' _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  calc ‖(W.L h (Φ i)).1 v‖ = β h * ‖(Φ i).1 (D.act h⁻¹ v)‖ := hnorm
    _ ≤ |A₀| * (|B| * (B' * wt K' N v)) :=
      mul_le_mul hβA h1 (norm_nonneg _) (abs_nonneg _)
    _ = |A₀| * (|B| * B') * wt K' N v := by ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveH
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Ff.OneParameterSubgroupCurves

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private def eR (w : InfinitePlace F) (t : ℝ) : TR.Rinf F := fun v => if v = w then Real.exp t else 1

private theorem eR_add (w : InfinitePlace F) (s t : ℝ) : eR w (s + t) = eR w s * eR w t := by
  funext v
  by_cases h : v = w <;> simp [eR, h, Real.exp_add]

private theorem eR_zero (w : InfinitePlace F) : eR w 0 = 1 := by
  funext v
  by_cases h : v = w <;> simp [eR, h]

private theorem hasDerivAt_eR (w : InfinitePlace F) : HasDerivAt (eR w) (Pi.single w 1 : TR.Rinf F) 0 := by
  refine hasDerivAt_pi.2 fun v => ?_
  by_cases h : v = w
  · subst h
    simpa [eR] using Real.hasDerivAt_exp 0
  · simpa [eR, h] using hasDerivAt_const (0 : ℝ) (1 : ℝ)

private def eU (w : InfinitePlace F) (t : ℝ) : (TR.Rinf F)ˣ :=
  ⟨eR w t, eR w (-t), by rw [← eR_add, add_neg_cancel, eR_zero], by rw [← eR_add, neg_add_cancel, eR_zero]⟩

private theorem eU_add (w : InfinitePlace F) (s t : ℝ) : eU w (s + t) = eU w s * eU w t :=
  Units.ext (eR_add w s t)

private def aI (w : InfinitePlace F) (t : ℝ) : (A F)ˣ := TR.infId F (eU w t)

private theorem aI_add (w : InfinitePlace F) (s t : ℝ) : aI w (s + t) = aI w s * aI w t := by
  rw [aI, eU_add, map_mul]; rfl

private theorem aI_zero (w : InfinitePlace F) : aI w 0 = 1 := by
  have h : eU w 0 = 1 := Units.ext (eR_zero w)
  rw [aI, h, map_one]

private theorem aI_neg (w : InfinitePlace F) (t : ℝ) : aI w (-t) = (aI w t)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← aI_add, neg_add_cancel, aI_zero])

private theorem aI_val (w : InfinitePlace F) (t : ℝ) :
    ((aI w t : (A F)ˣ) : A F) = 1 + TR.sInf F (eR w t - 1) := by
  change 1 - TR.sInf F 1 + TR.sInf F (eR w t) = _
  rw [map_sub]; abel

private theorem pInf_sInf (x : TR.Rinf F) : TR.pInf F (TR.sInf F x) = x := (TR.infEq F).symm_apply_apply x

private theorem pFin_sInf (x : TR.Rinf F) : pFin F (TR.sInf F x) = 0 := rfl

private theorem sInf_mul (x : TR.Rinf F) (a : A F) : TR.sInf F x * a = TR.sInf F (x * TR.pInf F a) := by
  refine TR.ad_ext ?_ ?_
  · rw [map_mul, pInf_sInf, pInf_sInf]
  · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]

private theorem pInf_aI (w : InfinitePlace F) (t : ℝ) : TR.pInf F (aI w t : (A F)ˣ) = eR w t := by
  rw [aI_val, map_add (f := _), pInf_sInf, map_one]; abel

private theorem pFin_aI (w : InfinitePlace F) (t : ℝ) : pFin F (aI w t : (A F)ˣ) = 1 := by
  rw [aI_val, map_add (f := _), pFin_sInf, map_one, add_zero]

private theorem ab_aI (w : InfinitePlace F) (t : ℝ) : ab (aI w t) = Real.exp t := by
  have h1 : ((aI w t : (A F)ˣ) : A F).1 = TR.infEq F (eR w t) := by
    change (1 : InfiniteAdeleRing F) - TR.infEq F 1 + TR.infEq F (eR w t) = _
    rw [map_one, sub_self, zero_add]
  have h2 : ((aI w t : (A F)ˣ) : A F).2 = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    rw [sub_zero, add_zero]
  have h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : Af F) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by exact norm_one
  have h4 : ∀ v : InfinitePlace F, ‖(TR.infEq F (eR w t)) v‖ = |eR w t v| := fun v => by
    have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.dist_eq (eR w t v) 0
    have h0 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm 0 : v.Completion) = 0 :=
      map_zero _
    rw [← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right, ← h0]
    exact h
  unfold ab
  rw [IdeleGroup.ideleModule_eq, h1, h2, h3, mul_one]
  rw [Finset.prod_eq_single w]
  · rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one, h4]
    simp [eR, abs_of_pos (Real.exp_pos t)]
  · intro v _ hv
    rw [(IsTotallyReal.isReal v).mult_eq_one, pow_one, h4]
    simp [eR, hv]
  · simp

private theorem h_apply (O : Fo.Ops F) (w : InfinitePlace F) (φ : S4 F) (v : V4 F) :
    (O.h w φ).1 v = (∑ i, Fo.cw w (v i) * (O.d w i φ).1 v) + 2 * φ.1 v := by
  have e : O.h w φ = (∑ i, O.x w i (O.d w i φ)) + (2 : ℂ) • φ := by
    simp [Fo.Ops.h, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, two_smul, two_mul]
  rw [e]
  change ((∑ i, O.x w i (O.d w i φ) : S4 F)).1 v + 2 * φ.1 v = _
  congr 1
  have : ((∑ i, O.x w i (O.d w i φ) : S4 F)).1 = ∑ i, (O.x w i (O.d w i φ)).1 :=
    AddSubmonoidClass.coe_finsetSum _ _
  rw [this, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => O.x_apply w i _ v

private theorem key (O : Fo.Ops F) (hS : SDiff O) (w : InfinitePlace F) (φ : S4 F) (v : V4 F) :
    HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ) * φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * v i)
      ((O.h w φ).1 v) 0 := by
  let x : ℝ → Fin 4 → TR.Rinf F := fun r i => (eR w r - 1) * TR.pInf F (v i)
  let x' : Fin 4 → TR.Rinf F := fun i => (Pi.single w 1 : TR.Rinf F) * TR.pInf F (v i)
  have hx0 : x 0 = 0 := by funext i; simp [x, eR_zero]
  have hx : HasDerivAt x x' 0 := by
    refine hasDerivAt_pi.2 fun i => ?_
    exact ((hasDerivAt_eR w).sub_const 1).mul_const _
  have h1 := hS φ v x x' hx0 hx
  have h2 : (fun r : ℝ => φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * v i) =
      fun r => φ.1 fun i => v i + TR.sInf F (x r i) := by
    funext r
    refine congrArg φ.1 (funext fun i => ?_)
    rw [aI_val, add_mul, one_mul, sInf_mul]
  rw [← h2] at h1
  have h3 : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ)) (2 : ℂ) 0 := by
    have h : HasDerivAt (fun r : ℝ => Real.exp (2 * r)) 2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).exp
    simpa using h.ofReal_comp
  have h4 : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ) * φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * v i) _ 0 :=
    h3.mul h1
  refine h4.congr_deriv ?_
  have h5 : (∑ i, ∑ u, ((x' i u : ℝ) : ℂ) * (O.d u i φ).1 v) = ∑ i, Fo.cw w (v i) * (O.d w i φ).1 v := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single w]
    · simp [x', Fo.cw]
    · intro u _ hu
      simp [x', hu]
    · simp
  rw [h5, h_apply, aI_zero]
  simp [add_comm]

private theorem eR_mul_neg (w : InfinitePlace F) (t : ℝ) : eR w t * eR w (-t) = 1 := by
  rw [← eR_add, add_neg_cancel, eR_zero]

private theorem eR_neg_mul (w : InfinitePlace F) (t : ℝ) : eR w (-t) * eR w t = 1 := by
  rw [← eR_add, neg_add_cancel, eR_zero]

private theorem hasDerivAt_eR_neg (w : InfinitePlace F) :
    HasDerivAt (fun t => eR w (-t)) (-(Pi.single w 1 : TR.Rinf F)) 0 := by
  refine hasDerivAt_pi.2 fun v => ?_
  by_cases h : v = w
  · subst h
    simpa [eR] using (hasDerivAt_neg (0 : ℝ)).exp
  · simpa [eR, h] using hasDerivAt_const (0 : ℝ) (1 : ℝ)

private def cT (w : InfinitePlace F) (t : ℝ) : GL (Fin 2) (TR.Rinf F) :=
  ⟨!![eR w t, 0; 0, eR w (-t)], !![eR w (-t), 0; 0, eR w t],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two, eR_mul_neg, eR_neg_mul],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two, eR_mul_neg, eR_neg_mul]⟩

private theorem cT_add (w : InfinitePlace F) (s t : ℝ) : cT w (s + t) = cT w s * cT w t := by
  refine Units.ext ?_
  change !![eR w (s + t), 0; 0, eR w (-(s + t))] = !![eR w s, 0; 0, eR w (-s)] * !![eR w t, 0; 0, eR w (-t)]
  rw [Matrix.mul_fin_two, neg_add, eR_add, eR_add]
  simp

private theorem hasDerivAt_cT (w : InfinitePlace F) : HasDerivAt (fun t => TR.toL (cT w t).val)
    (TR.toL (Matrix.single 0 0 (Pi.single w 1)) - TR.toL (Matrix.single 1 1 (Pi.single w 1))) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa [cT] using hasDerivAt_eR w
  · simpa [cT] using hasDerivAt_const (0 : ℝ) (0 : TR.Rinf F)
  · simpa [cT] using hasDerivAt_const (0 : ℝ) (0 : TR.Rinf F)
  · simpa [cT] using hasDerivAt_eR_neg w

private theorem gl_mD_aI (w : InfinitePlace F) (t : ℝ) : gl (mD (aI w t)) = TR.infGL F 2 (cT w t) := by
  have hn : ((aI w t)⁻¹ : (A F)ˣ) = aI w (-t) := (aI_neg w t).symm
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j
    · exact pInf_aI w t
    · exact map_zero (TR.pInf F)
    · exact map_zero (TR.pInf F)
    · change TR.pInf F (((aI w t)⁻¹ : (A F)ˣ) : A F) = eR w (-t)
      rw [hn]; exact pInf_aI w (-t)
  · rw [TR.pFin_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j
    · exact pFin_aI w t
    · exact map_zero (pFin F)
    · exact map_zero (pFin F)
    · change pFin F (((aI w t)⁻¹ : (A F)ˣ) : A F) = 1
      rw [hn]; exact pFin_aI w (-t)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E}

private theorem om_aI (W : Weil D) (w : InfinitePlace F) (t : ℝ) (φ : S4 F) (v : V4 F) :
    (W.Om (mD (aI w t)) φ).1 v =
      ((Real.exp (2 * t) : ℝ) : ℂ) * φ.1 fun i => ((aI w t : (A F)ˣ) : A F) * v i := by
  have hη : W.η.1 (aI w t) = 1 := by
    have h : aI w t = aI w (t / 2) ^ 2 := by
      rw [pow_two, ← aI_add]
      congr 1
      ring
    rw [h, map_pow]
    exact W.η_sq _
  have he : Real.exp t ^ 2 = Real.exp (2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [W.Om_m, hη, ab_aI, he]
  simp

end UpperTheory.ConvolutionTheory.R2.Ff.OneParameterSubgroupCurves

end

open UpperTheory.ConvolutionTheory.R2.Ff.OneParameterSubgroupCurves in
theorem UpperTheory.ConvolutionTheory.R2.Ff.curveH :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D), CurveH O W := by
  intro F E _ _ _ _ _ _ _ D O W w
  have hS := sDiff F O
  refine ⟨fun t => mD (aI w t), cT w, ⟨cT_add w, hasDerivAt_cT w⟩, gl_mD_aI w, fun φ t v => ?_⟩
  have hk := key O hS w φ (fun i => ((aI w t : (A F)ˣ) : A F) * v i)
  have hk' : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ) *
      φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * (((aI w t : (A F)ˣ) : A F) * v i))
      ((O.h w φ).1 fun i => ((aI w t : (A F)ˣ) : A F) * v i) (t - t) := by
    rwa [sub_self]
  have h := (hk'.comp_sub_const t t).const_mul ((Real.exp (2 * t) : ℝ) : ℂ)
  have e : (fun s => (W.Om (mD (aI w s)) φ).1 v) = fun s => ((Real.exp (2 * t) : ℝ) : ℂ) *
      (((Real.exp (2 * (s - t)) : ℝ) : ℂ) *
        φ.1 fun i => ((aI w (s - t) : (A F)ˣ) : A F) * (((aI w t : (A F)ˣ) : A F) * v i)) := by
    funext s
    rw [om_aI W w s φ v, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    have h1 : 2 * t + 2 * (s - t) = 2 * s := by ring
    rw [h1]
    refine congrArg _ (congrArg φ.1 (funext fun i => ?_))
    rw [← mul_assoc, ← Units.val_mul, ← aI_add, sub_add_cancel]
  change HasDerivAt (fun s => (W.Om (mD (aI w s)) φ).1 v) ((W.Om (mD (aI w t)) (O.h w φ)).1 v) t
  rw [e, om_aI W w t (O.h w φ) v]
  exact h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DLFock
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.dLFock :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (Y : Lie E 2), ∀ φ ∈ Fock D.δ, O.dL D Y φ ∈ Fock D.δ := by
  intro F E _ _ _ _ _ _ _ D O Y φ hφ
  let S : Subalgebra ℂ (Module.End ℂ (S4 F)) :=
    { carrier := {z | ∀ φ ∈ Fock D.δ, z φ ∈ Fock D.δ}
      mul_mem' := fun hx hy φ h => hx _ (hy φ h)
      add_mem' := fun hx hy φ h => add_mem (hx φ h) (hy φ h)
      algebraMap_mem' := fun c φ h => Submodule.smul_mem _ c h }
  have hx : ∀ w i, O.x w i ∈ S := fun w i ψ hψ => (opsFock F E D O w i ψ hψ).1
  have hd : ∀ w i, O.d w i ∈ S := fun w i ψ hψ => (opsFock F E D O w i ψ hψ).2
  have hX : ∀ τ a b, O.X D τ a b ∈ S := fun τ a b => by
    fin_cases a <;> fin_cases b
    · exact hx _ _
    · exact add_mem (hx _ _) (S.smul_mem (hx _ _) _)
    · exact sub_mem (hx _ _) (S.smul_mem (hx _ _) _)
    · exact hx _ _
  have hD : ∀ τ a b, O.DX D τ a b ∈ S := fun τ a b => by
    fin_cases a <;> fin_cases b
    · exact hd _ _
    · exact S.smul_mem (add_mem (hd _ _) (S.smul_mem (hd _ _) _)) _
    · exact S.smul_mem (sub_mem (hd _ _) (S.smul_mem (hd _ _) _)) _
    · exact hd _ _
  refine (?_ : O.dL D Y ∈ S) φ hφ
  refine sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ => S.smul_mem (sub_mem (neg_mem ?_) ?_) _
  · split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact sum_mem fun b _ => mul_mem (hX _ _ _) (hD _ _ _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.MovG
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.movG :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F), MovG W M := by
  intro F E _ _ _ _ _ _ _ D W M f hf φ g₀ h
  have hu : LInv (fun g : G1 F => f (gl g * dM (nu F h) * (gl g₀)⁻¹) * Th (W.Om g (W.L h φ)).1) := by
    intro γ g
    have h1 : gl (ratS F γ * g) * dM (nu F h) * (gl g₀)⁻¹ =
        ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) * (gl g * dM (nu F h) * (gl g₀)⁻¹) := by
      rw [gl_mul, gl_ratS]; group
    have h2 : W.Om (ratS F γ * g) (W.L h φ) = W.Om (ratS F γ) (W.Om g (W.L h φ)) := by
      rw [map_mul, Module.End.mul_apply]
    show f (gl (ratS F γ * g) * dM (nu F h) * (gl g₀)⁻¹) * Th (W.Om (ratS F γ * g) (W.L h φ)).1 = _
    rw [h1, hf, h2, W.th_Om]
  have key := rtInv F M _ hu (cD (nu F h) g₀)
  refine Eq.trans (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)) key
  have h1 : gl (g * cD (nu F h) g₀) * dM (nu F h) * (gl g₀)⁻¹ = gl g * dM (nu F h) := by
    rw [gl_mul, gl_cD]; group
  have h2 : W.L h (W.Om g₀ φ) = W.Om (cD (nu F h) g₀) (W.L h φ) := by
    have := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (W.comm h g₀)
    simpa only [Module.End.mul_apply] using this
  have h3 : W.Om (g * cD (nu F h) g₀) (W.L h φ) = W.Om g (W.L h (W.Om g₀ φ)) := by
    rw [h2, map_mul, Module.End.mul_apply]
  show f (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om g₀ φ))).1 =
    f (gl (g * cD (nu F h) g₀) * dM (nu F h) * (gl g₀)⁻¹) * Th (W.Om (g * cD (nu F h) g₀) (W.L h φ)).1
  rw [h1, h3]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.SummableRationalSchwartz
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem summable_rational_schwartz (F : Type) [Field F] [NumberField F] (φ : S4 F) :
    Summable (fun ξ : Fin 4 → F => φ.1 fun i => rt (ξ i)) := by
  obtain ⟨-, K, hK, hB⟩ := wtBound F φ
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨B, hB⟩ := hB N
  obtain ⟨C, hC⟩ := hN K hK 1 one_pos
  have hab : (1 : ℝ) ≤ ab (1 : (A F)ˣ) := by
    simp [ab]
  have hs := (hC 1 hab).1
  refine Summable.of_norm_bounded (g := fun ξ => B * wt K N (sc (1 : (A F)ˣ) ξ)) (hs.mul_left B) ?_
  intro ξ
  have := hB () (Set.mem_univ _) (fun i => rt (ξ i))
  have hsc : sc (1 : (A F)ˣ) ξ = fun i => rt (ξ i) := by
    funext i
    exact one_mul _
  rw [hsc]
  exact this

theorem UpperTheory.ConvolutionTheory.R2.Ff.thLin :
    ∀ (F : Type) [Field F] [NumberField F], ThLin F := by
  intro F _ _
  refine ⟨fun φ φ' => ?_, fun c φ => ?_⟩
  · have h : ∀ ξ : Fin 4 → F, (φ + φ').1 (fun i => rt (ξ i)) =
        φ.1 (fun i => rt (ξ i)) + φ'.1 (fun i => rt (ξ i)) := fun ξ => rfl
    simp only [Th, h]
    exact (summable_rational_schwartz F φ).tsum_add (summable_rational_schwartz F φ')
  · have h : ∀ ξ : Fin 4 → F, (c • φ).1 (fun i => rt (ξ i)) =
        c * φ.1 (fun i => rt (ξ i)) := fun ξ => rfl
    simp only [Th, h]
    exact tsum_mul_left
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThDer
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.thDer :
    ∀ (F : Type) [Field F] [NumberField F], ThDer F := by
  intro F _ _ Ψ Ψ' hD t hDom
  obtain ⟨K, hK, hB⟩ := hDom
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨C, hC⟩ := hN K hK 1 one_pos
  have hab : (1 : ℝ) ≤ ab (1 : (A F)ˣ) := by simp [ab]
  have hsum := (hC 1 hab).1
  obtain ⟨B, hB⟩ := hB N
  have hsc : ∀ ξ : Fin 4 → F, sc (1 : (A F)ˣ) ξ = fun i => rt (ξ i) := by
    intro ξ; funext i; simp [sc]
  obtain ⟨-, K', hK', hB'⟩ := wtBound F (Ψ t)
  have hs0 : Summable (fun ξ : Fin 4 → F => (Ψ t).1 fun i => rt (ξ i)) := by
    obtain ⟨B', hB'⟩ := hB' N
    obtain ⟨C', hC'⟩ := hN K' hK' 1 one_pos
    refine Summable.of_norm_bounded (g := fun ξ : Fin 4 → F => B' * wt K' N (sc (1 : (A F)ˣ) ξ)) ((hC' 1 hab).1.mul_left B') ?_
    intro ξ
    rw [hsc]
    exact hB' () (Set.mem_univ _) _
  have key := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℂ)
    (u := fun ξ : Fin 4 → F => B * wt K N (sc (1 : (A F)ˣ) ξ))
    (g := fun (ξ : Fin 4 → F) (s : ℝ) => (Ψ s).1 fun i => rt (ξ i))
    (g' := fun (ξ : Fin 4 → F) (s : ℝ) => (Ψ' s).1 fun i => rt (ξ i))
    (t := Metric.ball t 1) (y₀ := t) (y := t)
    (hsum.mul_left B) Metric.isOpen_ball (convex_ball t 1).isPreconnected
    (fun ξ y _ => hD y _)
    (fun ξ y hy => by rw [hsc]; exact hB y hy _)
    (Metric.mem_ball_self one_pos) hs0 (Metric.mem_ball_self one_pos)
  exact key
end

