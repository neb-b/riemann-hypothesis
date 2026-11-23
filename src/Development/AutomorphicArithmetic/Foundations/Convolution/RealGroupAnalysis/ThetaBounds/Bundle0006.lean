module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FderivOfExp
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem fre_of_rays {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : V → ℂ) (G : V → V →L[ℝ] ℂ) (hG : Continuous G)
    (h : ∀ (X : V) (s : ℝ), HasDerivAt (fun s : ℝ => u (s • X)) (G (s • X) X) s) :
    HasFDerivAt u (G 0) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.1 hG.continuousAt c hc
  filter_upwards [Metric.ball_mem_nhds (0 : V) hδ] with X hX
  have hX' : ‖X‖ < δ := by simpa using hX
  have hv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => u (s • X) - (s : ℂ) * G 0 X)
      (G (s • X) X - G 0 X) (Set.Icc (0 : ℝ) 1) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * G 0 X) (G 0 X) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (G 0 X)
    exact ((h X s).sub h1).hasDerivWithinAt
  have hbd : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖G (s • X) X - G 0 X‖ ≤ c * ‖X‖ := by
    intro s hs
    have hs' : ‖s • X‖ < δ := by
      rw [norm_smul, Real.norm_of_nonneg hs.1]
      calc s * ‖X‖ ≤ 1 * ‖X‖ := by gcongr; exact hs.2
        _ < δ := by simpa using hX'
    have h2 : ‖G (s • X) - G 0‖ < c := by
      simpa [dist_eq_norm] using hb (x := s • X) (by simpa [dist_eq_norm] using hs')
    calc ‖G (s • X) X - G 0 X‖ = ‖(G (s • X) - G 0) X‖ := by simp
      _ ≤ ‖G (s • X) - G 0‖ * ‖X‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖X‖ := by gcongr
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hv hbd (convex_Icc 0 1)
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  simp only [zero_smul, one_smul, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, sub_zero,
    norm_one, mul_one] at key
  have e : u (0 + X) - u 0 - G 0 X = u X - G 0 X - u 0 := by rw [zero_add]; ring
  rw [e]
  exact key

private theorem fderiv_of_exp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : V → ℂ) (ε : V → V) (L : V →L[ℝ] ℂ)
    (hε : HasStrictFDerivAt ε ((ContinuousLinearEquiv.refl ℝ V : V ≃L[ℝ] V) : V →L[ℝ] V) 0)
    (h : HasFDerivAt (f ∘ ε) L 0) : HasFDerivAt f L (ε 0) := by
  have hi := hε.to_localInverse
  have h0 := hε.localInverse_apply_image
  set l := HasStrictFDerivAt.localInverse ε _ 0 hε
  have h' : HasFDerivAt (f ∘ ε) L (l (ε 0)) := by rw [h0]; exact h
  have hc := h'.comp (ε 0) hi.hasFDerivAt
  have e : L.comp (((ContinuousLinearEquiv.refl ℝ V).symm : V ≃L[ℝ] V) : V →L[ℝ] V) = L := by
    ext x; simp
  rw [e] at hc
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hε.eventually_right_inverse] with y hy
  simp only [Function.comp_apply]
  rw [hy]

section
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem exp_eq (Y : Lie E 2) : toL (NormedSpace.exp (Matrix.of Y)) =
    (Cm.archEq E 2).symm (NormedSpace.exp (Cm.archEq E 2 Y)) := by
  letI : NormedRing (Matrix (Fin 2) (Fin 2) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin 2) (Fin 2) (Cinf E)) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (ArchMatrix E 2) := NormedAlgebra.restrictScalars ℚ ℝ _
  refine (Cm.archEq E 2).injective ?_
  rw [ContinuousLinearEquiv.apply_symm_apply, Cm.archEq_toL]
  have hc : Continuous (Cm.matEq E 2) := (Cm.archEq E 2).continuous
  exact NormedSpace.map_exp (Cm.matEq E 2) hc (Matrix.of Y)

private noncomputable def expL (Y : Lie E 2) : Lie E 2 := (Cm.archEq E 2).symm (NormedSpace.exp (Cm.archEq E 2 Y))

private theorem expL_strict : HasStrictFDerivAt (expL (E := E))
    ((ContinuousLinearEquiv.refl ℝ (Lie E 2) : Lie E 2 ≃L[ℝ] Lie E 2) : Lie E 2 →L[ℝ] Lie E 2) 0 := by
  have h1 : HasStrictFDerivAt (fun x : ArchMatrix E 2 => NormedSpace.exp x) (1 : ArchMatrix E 2 →L[ℝ] ArchMatrix E 2)
      (Cm.archEq E 2 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero
  have h2 := ((Cm.archEq E 2).symm.hasStrictFDerivAt.comp _ (h1.comp (0 : Lie E 2) (Cm.archEq E 2).hasStrictFDerivAt))
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  exact (Cm.archEq E 2).symm_apply_apply x

private theorem expL_cont : Continuous (expL (E := E)) := by
  letI : NormedAlgebra ℚ (ArchMatrix E 2) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact (Cm.archEq E 2).symm.continuous.comp (NormedSpace.exp_continuous.comp (Cm.archEq E 2).continuous)

private theorem toL_ex (Y : Lie E 2) : toL (ex Y 1).val = expL Y := by
  have : (ex Y 1).val = NormedSpace.exp (Matrix.of Y) := by
    rw [ex, IsUnit.unit_spec, one_smul]
  rw [this]
  exact exp_eq Y

private theorem ex_smul (X : Lie E 2) (s : ℝ) : ex (s • X) 1 = ex X s := by
  refine Units.ext ?_
  change NormedSpace.exp ((1 : ℝ) • Matrix.of (s • X)) = NormedSpace.exp (s • Matrix.of X)
  rw [one_smul]
  rfl

private theorem ex_zero (X : Lie E 2) : ex X 0 = 1 := by
  refine Units.ext ?_
  change NormedSpace.exp ((0 : ℝ) • Matrix.of X) = 1
  rw [zero_smul, NormedSpace.exp_zero]

private theorem ex_inv (X : Lie E 2) : (ex X 1)⁻¹ = ex (-X) 1 := by
  have h := (exPar E X).1 1 (-1)
  rw [add_neg_cancel, ex_zero] at h
  have e : ex (-X) 1 = ex X (-1) := by
    rw [← ex_smul X (-1), neg_one_smul]
  rw [e]
  exact inv_eq_of_mul_eq_one_right h.symm

private theorem ex_cont : Continuous fun Y : Lie E 2 => ex Y 1 := by
  have hv : Continuous fun Y : Lie E 2 => (ex Y 1).val := by
    have : (fun Y : Lie E 2 => (ex Y 1).val) = fun Y => Matrix.of (expL Y) := by
      funext Y; rw [← toL_ex]; rfl
    rw [this]
    exact expL_cont
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  have : (fun Y : Lie E 2 => ((ex Y 1)⁻¹).val) = fun Y => (ex (-Y) 1).val := by
    funext Y; rw [ex_inv]
  change Continuous (fun Y : Lie E 2 => ((ex Y 1)⁻¹).val)
  rw [this]
  exact hv.comp continuous_neg

end

theorem UpperTheory.ConvolutionTheory.R2.Ff.smFre :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], SmFre E := by
  intro E _ _ _ Φ T hc hd g
  let G : Lie E 2 → Lie E 2 →L[ℝ] ℂ := fun Y =>
    LinearMap.toContinuousLinearMap ((LinearMap.proj (g * infGL E 2 (ex Y 1))) ∘ₗ T)
  have hGa : ∀ Y X, G Y X = T X (g * infGL E 2 (ex Y 1)) := fun _ _ => rfl
  have hG : Continuous G := continuous_clm_apply.2 fun X => by
    simp only [hGa]
    exact (hc X g).comp ex_cont
  have hray : ∀ (X : Lie E 2) (s : ℝ), HasDerivAt (fun s : ℝ => Φ (g * infGL E 2 (ex (s • X) 1))) (G (s • X) X) s := by
    intro X s
    have h1 := hd X (g * infGL E 2 (ex X s))
    have h2 : HasDerivAt (fun r : ℝ => Φ (g * infGL E 2 (ex X s) * infGL E 2 (ex X (r - s))))
        (T X (g * infGL E 2 (ex X s))) s :=
      HasDerivAt.comp_sub_const s s (by simpa using h1)
    rw [hGa, ex_smul]
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    simp only [ex_smul]
    rw [mul_assoc, ← map_mul, ← (exPar E X).1, add_sub_cancel]
  have h1 := fre_of_rays (fun Y => Φ (g * infGL E 2 (ex Y 1))) G hG hray
  have h2 : HasFDerivAt (chart Φ g ∘ expL) (G 0) 0 := by
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun Y => ?_)
    simp only [Function.comp_apply]
    rw [← toL_ex, chart_val]
  have h3 := fderiv_of_exp (chart Φ g) expL (G 0) expL_strict h2
  have h0 : expL (0 : Lie E 2) = oneL E 2 := by
    rw [← toL_ex, ← zero_smul ℝ (0 : Lie E 2), ex_smul, ex_zero]
    rfl
  rw [h0] at h3
  refine ⟨h3.differentiableAt, fun X => ?_⟩
  rw [h3.fderiv, hGa, ← zero_smul ℝ (0 : Lie E 2), ex_smul, ex_zero, map_one, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.HmEntries
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open UpperTheory.ConvolutionTheory.R2.Fo (pl)
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldDerivatives

private theorem herm_der (P : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (P' H : Matrix (Fin 2) (Fin 2) ℂ) (h0 : P 0 = 1)
    (hP : ∀ i j, HasDerivAt (fun t => P t i j) (P' i j) 0) (i j : Fin 2) :
    HasDerivAt (fun t => (P t * H * (P t)ᴴ) i j) ((P' * H + H * P'ᴴ) i j) 0 := by
  have hval : ∀ i j : Fin 2,
      P' i 0 * H 0 0 * star ((1 : Matrix (Fin 2) (Fin 2) ℂ) j 0) + (1 : Matrix (Fin 2) (Fin 2) ℂ) i 0 * H 0 0 * star (P' j 0) +
        (P' i 1 * H 1 0 * star ((1 : Matrix (Fin 2) (Fin 2) ℂ) j 0) + (1 : Matrix (Fin 2) (Fin 2) ℂ) i 1 * H 1 0 * star (P' j 0)) +
      (P' i 0 * H 0 1 * star ((1 : Matrix (Fin 2) (Fin 2) ℂ) j 1) + (1 : Matrix (Fin 2) (Fin 2) ℂ) i 0 * H 0 1 * star (P' j 1) +
        (P' i 1 * H 1 1 * star ((1 : Matrix (Fin 2) (Fin 2) ℂ) j 1) + (1 : Matrix (Fin 2) (Fin 2) ℂ) i 1 * H 1 1 * star (P' j 1))) =
      (P' * H + H * P'ᴴ) i j := by
    simp only [Fin.forall_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring
  have hc : ∀ a b, HasDerivAt (fun t => star (P t a b)) (star (P' a b)) 0 := fun a b => (hP a b).star
  have hh : ∀ a b, HasDerivAt (fun t => P t i a * H a b * star (P t j b))
      (P' i a * H a b * star (P 0 j b) + P 0 i a * H a b * star (P' j b)) 0 :=
    fun a b => ((hP i a).mul_const (H a b)).mul (hc j b)
  have hs := (((hh 0 0).add (hh 1 0)).add ((hh 0 1).add (hh 1 1)))
  refine (hs.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  · rw [h0]
    exact hval i j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    ring

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem hm_entries {s : ℂ} {w : InfinitePlace F} (u : Fin 4 → TR.Rinf F) :
    Hm s w u 0 0 = (u 1 w : ℝ) ∧ Hm s w u 1 1 = (u 0 w : ℝ) ∧ Hm s w u 0 1 = (u 2 w : ℝ) + s * (u 3 w : ℝ) ∧
      Hm s w u 1 0 = (u 2 w : ℝ) - s * (u 3 w : ℝ) := by
  simp [Hm]

private theorem coord_der {s : ℂ} (hs : s ≠ 0) (w : InfinitePlace F) (a : ℝ → Fin 4 → TR.Rinf F)
    (Q : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : ∀ t, Hm s w (a t) = Q t)
    (hq : ∀ i j, HasDerivAt (fun t => Q t i j) (q i j) 0) (i : Fin 4) :
    ∃ d : ℝ, HasDerivAt (fun t => a t i w) d 0 := by
  have e00 : ∀ t, Q t 0 0 = (a t 1 w : ℝ) := fun t => by rw [← hQ]; exact (hm_entries _).1
  have e11 : ∀ t, Q t 1 1 = (a t 0 w : ℝ) := fun t => by rw [← hQ]; exact (hm_entries _).2.1
  have e01 : ∀ t, Q t 0 1 = (a t 2 w : ℝ) + s * (a t 3 w : ℝ) := fun t => by rw [← hQ]; exact (hm_entries _).2.2.1
  have e10 : ∀ t, Q t 1 0 = (a t 2 w : ℝ) - s * (a t 3 w : ℝ) := fun t => by rw [← hQ]; exact (hm_entries _).2.2.2
  suffices h : ∃ c : ℂ, HasDerivAt (fun t => ((a t i w : ℝ) : ℂ)) c 0 by
    obtain ⟨c, hc⟩ := h
    refine ⟨c.re, ?_⟩
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => by simp)
  fin_cases i
  · exact ⟨_, (hq 1 1).congr_of_eventuallyEq (Eventually.of_forall fun t => (e11 t).symm)⟩
  · exact ⟨_, (hq 0 0).congr_of_eventuallyEq (Eventually.of_forall fun t => (e00 t).symm)⟩
  · refine ⟨_, (((hq 0 1).add (hq 1 0)).const_mul (2⁻¹ : ℂ)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)⟩
    simp only [Pi.add_apply, e01, e10]
    change ((a t 2 w : ℝ) : ℂ) = _
    ring
  · refine ⟨_, (((hq 0 1).sub (hq 1 0)).const_mul ((2 * s)⁻¹ : ℂ)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)⟩
    simp only [Pi.sub_apply, e01, e10]
    change ((a t 3 w : ℝ) : ℂ) = _
    field_simp
    ring

private theorem hm_der {s : ℂ} (w : InfinitePlace F) (a : ℝ → Fin 4 → TR.Rinf F) (d : Fin 4 → TR.Rinf F)
    (Q : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : ∀ t, Hm s w (a t) = Q t)
    (hq : ∀ i j, HasDerivAt (fun t => Q t i j) (q i j) 0)
    (hd : ∀ i, HasDerivAt (fun t => a t i w) (d i w) 0) : Hm s w d = q := by
  have hc : ∀ i, HasDerivAt (fun t => ((a t i w : ℝ) : ℂ)) ((d i w : ℝ) : ℂ) 0 := fun i => (hd i).ofReal_comp
  have e00 : (fun t => Q t 0 0) = fun t => ((a t 1 w : ℝ) : ℂ) :=
    funext fun t => by rw [← hQ]; exact (hm_entries _).1
  have e11 : (fun t => Q t 1 1) = fun t => ((a t 0 w : ℝ) : ℂ) :=
    funext fun t => by rw [← hQ]; exact (hm_entries _).2.1
  have e01 : (fun t => Q t 0 1) = (fun t => ((a t 2 w : ℝ) : ℂ)) + fun t => s * ((a t 3 w : ℝ) : ℂ) :=
    funext fun t => by rw [← hQ]; exact (hm_entries _).2.2.1
  have e10 : (fun t => Q t 1 0) = (fun t => ((a t 2 w : ℝ) : ℂ)) - fun t => s * ((a t 3 w : ℝ) : ℂ) :=
    funext fun t => by rw [← hQ]; exact (hm_entries _).2.2.2
  have h00 := hq 0 0
  have h11 := hq 1 1
  have h01 := hq 0 1
  have h10 := hq 1 0
  rw [e00] at h00
  rw [e11] at h11
  rw [e01] at h01
  rw [e10] at h10
  obtain ⟨f00, f11, f01, f10⟩ := hm_entries (s := s) (w := w) d
  ext i j
  revert i j
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [f00]; exact (hc 1).unique h00
  · rw [f01]; exact ((hc 2).add ((hc 3).const_mul s)).unique h01
  · rw [f10]; exact ((hc 2).sub ((hc 3).const_mul s)).unique h10
  · rw [f11]; exact (hc 0).unique h11

end UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldDerivatives

open UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldDerivatives in
theorem UpperTheory.ConvolutionTheory.R2.Ff.vfDer :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E), VfDer D := by
  intro F E _ _ _ _ _ _ _ D Y v
  obtain ⟨hadd, -, hder, -, -⟩ := exPar E Y
  have hA := actInf F E D
  have hex0 : ex Y 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hinv : ∀ t, (ex Y t)⁻¹ = ex Y (-t) := fun t => by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hadd, add_neg_cancel, hex0]
  let a : ℝ → Fin 4 → TR.Rinf F := fun t i => TR.pInf F (D.act (infGL E 2 (ex Y t))⁻¹ v i)
  let a0 : Fin 4 → TR.Rinf F := fun i => TR.pInf F (v i)
  let P : (E →+* ℂ) → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun τ t => (ex Y (-t)).val.map (coord τ)
  have hHm : ∀ τ t, Hm (τ D.θ) (pl F τ) (a t) = P τ t * Hm (τ D.θ) (pl F τ) a0 * (P τ t)ᴴ := fun τ t => by
    have h := (hA (ex Y (-t)) v).2 τ
    simp only [a, P]
    rw [← map_inv, hinv]
    exact h
  have hP0 : ∀ τ, P τ 0 = 1 := fun τ => by
    simp only [P, neg_zero, hex0]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hPd : ∀ τ i j, HasDerivAt (fun t => P τ t i j) ((-(Matrix.of Y).map (coord τ)) i j) 0 := fun τ i j => by
    let c : Cinf E →L[ℝ] ℂ := LinearMap.mkContinuous
      { toFun := coord τ, map_add' := map_add _, map_smul' := UpperTheory.V.FieldIso.coord_smul τ } 1
      (fun x => by simpa using UpperTheory.V.FieldIso.norm_coord_le τ x)
    have h1 : HasDerivAt (fun t => (ex Y t).val i j) (Y i j) 0 := hasDerivAt_pi.1 (hasDerivAt_pi.1 hder i) j
    have h2 : HasDerivAt (fun t => c ((ex Y t).val i j)) (c (Y i j)) (-(0 : ℝ)) := by
      rw [neg_zero]
      exact c.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    have h3 := HasDerivAt.scomp (0 : ℝ) h2 (hasDerivAt_neg (0 : ℝ))
    refine (h3.congr_deriv ?_)
    simp [c]
  have hQ := fun τ => herm_der (P τ) (-(Matrix.of Y).map (coord τ)) (Hm (τ D.θ) (pl F τ) a0) (hP0 τ) (hPd τ)
  have hs : ∀ τ : E →+* ℂ, τ D.θ ≠ 0 := fun τ => (map_ne_zero τ).2 D.θ_ne_zero
  have hex : ∀ (w : InfinitePlace F) i, ∃ d : ℝ, HasDerivAt (fun t => a t i w) d 0 := by
    intro w i
    have : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
    obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w
    have hw : pl F W.embedding = W.comap (algebraMap F E) := by
      rw [pl, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    beta_reduce
    rw [← hw]
    exact coord_der (hs _) _ a _ _ (hHm _) (hQ _) i
  choose d hd using hex
  have hact1 : D.act 1 v = v := by
    have hc (u : A F) : D.co (am E u) 0 = u := by
      rw [← D.mkE_base, D.co_mkE]
      rfl
    funext i
    fin_cases i <;> simp [Dat.act, Dat.unherm, Dat.herm, D.co_mkE, hc]
  refine ⟨fun t i => a t i - a0 i, fun i w => d w i, ?_, ?_, ?_, ?_⟩
  · funext i
    simp only [a, a0, hex0, map_one, inv_one, hact1, sub_self]
    rfl
  · rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro w
    exact (hd w i).sub_const _
  · intro t
    have hf := (hA (ex Y t)⁻¹ v).1
    rw [map_inv] at hf
    funext i
    have hi := congrFun hf i
    refine TR.ad_ext ?_ ?_
    · have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
      rw [map_add (f := _), h]
      simp [a, a0]
    · have h0 : ∀ x, pFin F (TR.sInf F x) = 0 := fun _ => rfl
      rw [map_add (f := _), h0, add_zero]
      exact hi
  · intro τ
    rw [hm_der (pl F τ) a (fun i w => d w i) _ _ (hHm τ) (hQ τ) (fun i => hd _ i)]
    simp only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_add]
    rfl
end

