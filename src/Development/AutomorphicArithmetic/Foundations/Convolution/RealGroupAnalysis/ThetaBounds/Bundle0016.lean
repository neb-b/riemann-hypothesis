module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Vol
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.HatMaj
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ZpowLeAbs
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private theorem top_GL (E : Type) [Field E] [NumberField E] :
    LocallyCompactSpace (GL (Fin 2) (Cinf E)) ∧ FirstCountableTopology (GL (Fin 2) (Cinf E)) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (Cinf E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → Cinf E))
  haveI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) (Cinf E)) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → Cinf E))
  haveI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) (Cinf E))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) (Cinf E))).symm.isInducing.firstCountableTopology
  have h := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin 2) (Fin 2) (Cinf E))
  exact ⟨h.locallyCompactSpace, h.isEmbedding.isInducing.firstCountableTopology⟩

private theorem om_L {D : Dat F E} (W : Weil D) (g : G1 F) (h : GL (Fin 2) (A E))
    (hh : nu F h = 1) (φ : S4 F) : W.Om g (W.L h φ) = W.L h (W.Om g φ) := by
  have e := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (W.comm h g)
  simp only [Module.End.mul_apply, hh] at e
  rw [e, UpperTheory.ConvolutionTheory.R2.M.cD_one]

private theorem term_cont (D : Dat F E) (W : Weil D) (Ψ : S4 F) (v : V4 F) :
    Continuous fun y : GL (Fin 2) (Cinf E) => (W.L (infGL E 2 y) Ψ).1 v := by
  obtain ⟨ρ, hρ, hact, hnu, hinf, -⟩ := actCont F E D
  have hΨ := (wtBound F Ψ).1
  have e : (fun y : GL (Fin 2) (Cinf E) => (W.L (infGL E 2 y) Ψ).1 v) = fun y =>
      (((ab (nu F (infGL E 2 y)))⁻¹ : ℝ) : ℂ) * Ψ.1 ((ρ (infGL E 2 y)⁻¹).val *ᵥ v) := by
    funext y
    rw [W.L_apply, hact]
  rw [e]
  refine Continuous.mul ?_ ?_
  · exact Complex.continuous_ofReal.comp
      ((continuous_ab.comp (hnu.comp hinf)).inv₀ fun _ => (ab_pos _).ne')
  · refine hΨ.comp ?_
    have h1 : Continuous fun y : GL (Fin 2) (Cinf E) => ρ (infGL E 2 y)⁻¹ :=
      hρ.comp (continuous_inv.comp hinf)
    exact (Units.continuous_val.comp h1).matrix_mulVec continuous_const

private theorem th_cont (D : Dat F E) (W : Weil D) (Ψ : S4 F) (S : Set (GL (Fin 2) (Cinf E)))
    (hS : IsCompact S) : ContinuousOn (fun y => Th (W.L (infGL E 2 y) Ψ).1) S := by
  obtain ⟨n, hn⟩ := wtSum F
  obtain ⟨ρ, -, -, -, hinf, -⟩ := actCont F E D
  obtain ⟨K, hK, hb⟩ := lDom F E D W Unit Set.univ (fun _ => Ψ) (wtBound F Ψ).2
    (infGL E 2 '' S) (hS.image hinf)
  obtain ⟨B, hB⟩ := hb n
  obtain ⟨C, hC⟩ := hn K hK 1 one_pos
  obtain ⟨hs, -⟩ := hC 1 (by rw [ab_one])
  have e : (fun ξ : Fin 4 → F => wt K n (sc (1 : (A F)ˣ) ξ)) = fun ξ => wt K n fun i => rt (ξ i) := by
    funext ξ
    congr 1
    funext i
    change ((1 : (A F)ˣ) : A F) * rt (ξ i) = rt (ξ i)
    rw [Units.val_one, one_mul]
  rw [e] at hs
  unfold Th
  refine continuousOn_tsum (fun ξ => (term_cont D W Ψ _).continuousOn) (hs.mul_left B) ?_
  intro ξ y hy
  exact hB (infGL E 2 y, ()) ⟨⟨y, hy, rfl⟩, trivial⟩ _

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.contOne :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ContOne W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ y₀ hy₀
  obtain ⟨ρ, -, -, hnu, hinf, -⟩ := actCont F E D
  obtain ⟨hlc, hfc⟩ := top_GL E
  have hfcont : Continuous f.1 := (decay F π f hf).1
  obtain ⟨S, hS, hSmem⟩ := exists_compact_mem_nhds y₀
  have hcl : IsClosed {y : GL (Fin 2) (Cinf E) | UpperTheory.ConvolutionTheory.R2.Ff.One F y} :=
    isClosed_eq (hnu.comp hinf) continuous_const
  have hC' := hS.inter_right hcl
  obtain ⟨B, hB⟩ := thBoundH F E D W π f hf φ hφ 1 {1} isCompact_singleton _ hC' (fun y hy => hy.2)
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using vol F M⟩
  have key : ContinuousWithinAt (fun y : GL (Fin 2) (Cinf E) =>
      ∫ g, f.1 (gl g) * Th (W.Om g (W.L (infGL E 2 y) φ)).1 ∂(M.μ.restrict M.D))
      {y | UpperTheory.ConvolutionTheory.R2.Ff.One F y} y₀ := by
    refine continuousWithinAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const _) ?_
    · filter_upwards with y
      exact ((hfcont.comp continuous_gl).measurable.mul
        (thMeas F E D W (W.L (infGL E 2 y) φ)).1).aestronglyMeasurable
    · have hev : ∀ᶠ y in 𝓝[{y | UpperTheory.ConvolutionTheory.R2.Ff.One F y}] y₀,
          y ∈ S ∩ {y | UpperTheory.ConvolutionTheory.R2.Ff.One F y} :=
        inter_mem (mem_nhdsWithin_of_mem_nhds hSmem) self_mem_nhdsWithin
      filter_upwards [hev] with y hy
      refine ae_of_all _ fun g => ?_
      simpa using hB g 1 rfl y hy
    · refine ae_of_all _ fun g => ?_
      have h1 : ContinuousAt (fun y => Th (W.L (infGL E 2 y) (W.Om g φ)).1) y₀ :=
        (th_cont D W (W.Om g φ) S hS).continuousAt hSmem
      have h2 : ContinuousWithinAt (fun y => Th (W.Om g (W.L (infGL E 2 y) φ)).1)
          {y | UpperTheory.ConvolutionTheory.R2.Ff.One F y} y₀ :=
        h1.continuousWithinAt.congr (fun y hy => by rw [om_L W g _ hy]) (by rw [om_L W g _ hy₀])
      exact continuousWithinAt_const.mul h2
  refine key.congr (fun y hy => ?_) ?_
  · have hy' : nu F (infGL E 2 y) = 1 := hy
    simp only [lift, hy', dM_one, mul_one]
  · have hy' : nu F (infGL E 2 y₀) = 1 := hy₀
    simp only [lift, hy', dM_one, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveAt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem curve_at {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (f : TR.Sm F 2) (x : GL (Fin 2) (A F)) {c : ℝ → GL (Fin 2) (TR.Rinf F)} {Y : TR.Lie F 2}
    (hc : Par c Y) (c0 : c 0 = 1) (t : ℝ) :
    HasDerivAt (fun s => f.1 (x * TR.infGL F 2 (c s))) ((TR.lie F 2 Y f).1 (x * TR.infGL F 2 (c t))) t := by
  have h1 := TR.hasDerivAt_curve f (x * TR.infGL F 2 (c t)) c Y c0 hc.2
  have h2 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h1' : HasDerivAt (fun u => f.1 (x * TR.infGL F 2 (c t) * TR.infGL F 2 (c u)))
      (TR.lieD Y f.1 (x * TR.infGL F 2 (c t))) ((fun s : ℝ => s - t) t) := by simpa using h1
  have h3 : HasDerivAt ((fun u => f.1 (x * TR.infGL F 2 (c t) * TR.infGL F 2 (c u))) ∘ (fun s : ℝ => s - t))
      ((1 : ℝ) • TR.lieD Y f.1 (x * TR.infGL F 2 (c t))) t := HasDerivAt.scomp t h1' h2
  have e : (fun s => f.1 (x * TR.infGL F 2 (c s))) =
      (fun u => f.1 (x * TR.infGL F 2 (c t) * TR.infGL F 2 (c u))) ∘ (fun s : ℝ => s - t) := by
    funext s
    simp only [Function.comp_apply]
    rw [mul_assoc, ← map_mul, ← hc.1, add_sub_cancel]
  rw [e]
  simpa using h3

theorem UpperTheory.ConvolutionTheory.R2.Ff.derF :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), DerF W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ c Y hc h
  obtain ⟨hinf, hcc⟩ := parCont F
  obtain ⟨c0, ccont, -⟩ := hcc c Y hc
  have hf' : TR.lie F 2 Y f ∈ π.V := π.stable (.lie Y) f hf
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using vol F M⟩
  obtain ⟨m1, -⟩ := thMeas F E D W (W.L h φ)
  set T : G1 F → ℂ := fun g => Th (W.Om g (W.L h φ)).1 with hT
  set x₀ := dM (nu F h) with hx₀
  have cf : ∀ (u : TR.Sm F 2), u ∈ π.V → ∀ a : GL (Fin 2) (A F), Continuous fun g : G1 F => u.1 (gl g * a) :=
    fun u hu a => (decay F π u hu).1.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)
  have hone : ∀ y ∈ ({1} : Set (GL (Fin 2) (Cinf E))), One F y := by
    rintro _ rfl; simp [Ff.One, nu]
  set C : Set (GL (Fin 2) (A F)) :=
    (fun t => x₀ * TR.infGL F 2 (c t)) '' Metric.closedBall (0 : ℝ) 1 with hC
  have Cc : IsCompact C := (isCompact_closedBall (0 : ℝ) 1).image
    (continuous_const.mul (hinf.comp ccont))
  obtain ⟨B, hB⟩ := thBoundH F E D W π _ hf' φ hφ h C Cc {1} isCompact_singleton hone
  obtain ⟨B₀, hB₀⟩ := thBoundH F E D W π f hf φ hφ h C Cc {1} isCompact_singleton hone
  have bd : ∀ (u : TR.Sm F 2) (B : ℝ), (∀ g, ∀ x ∈ C, ∀ y ∈ ({1} : Set (GL (Fin 2) (Cinf E))),
      ‖u.1 (gl g * x) * Th (W.Om g (W.L (h * infGL E 2 y) φ)).1‖ ≤ B) →
      ∀ t ∈ Metric.closedBall (0 : ℝ) 1, ∀ g, ‖u.1 (gl g * x₀ * TR.infGL F 2 (c t)) * T g‖ ≤ B := by
    intro u B hb t ht g
    have := hb g _ ⟨t, ht, rfl⟩ 1 rfl
    simpa [hT, mul_assoc] using this
  have ms : ∀ u ∈ π.V, ∀ a : GL (Fin 2) (A F),
      AEStronglyMeasurable (fun g => u.1 (gl g * x₀ * a) * T g) (M.μ.restrict M.D) := by
    intro u hu a
    have e : (fun g => u.1 (gl g * x₀ * a) * T g) = (fun g => u.1 (gl g * (x₀ * a))) * T := by
      funext g
      simp only [Pi.mul_apply, mul_assoc]
    rw [e]
    exact ((cf u hu (x₀ * a)).measurable.mul m1).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := M.μ.restrict M.D)
    (F := fun t g => f.1 (gl g * x₀ * TR.infGL F 2 (c t)) * T g)
    (F' := fun t g => (TR.lie F 2 Y f).1 (gl g * x₀ * TR.infGL F 2 (c t)) * T g)
    (x₀ := (0 : ℝ)) (s := Metric.closedBall (0 : ℝ) 1) (bound := fun _ => B)
    (Metric.closedBall_mem_nhds _ one_pos)
    (Eventually.of_forall fun t => ?_) ?_ ?_ (ae_of_all _ fun g t ht => bd _ B hB t ht g)
    (integrable_const _) (ae_of_all _ fun g t _ => ?_)
  · simpa [lift, Function.comp_def, c0, mul_assoc] using key.2
  · exact ms f hf _
  · have h0 : ∀ g, ‖f.1 (gl g * x₀ * TR.infGL F 2 (c 0)) * T g‖ ≤ B₀ := bd _ B₀ hB₀ 0 (by simp)
    exact Integrable.of_bound (ms f hf _) B₀ (ae_of_all _ h0)
  · exact ms _ hf' _
  · exact (curve_at f _ hc c0 t).mul_const _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DerOm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.derOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), DerOm W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ φ' hφ' G hG hG0 hD h
  have hc : Continuous fun g : G1 F => f.1 (gl g * dM (nu F h)) :=
    (decay F π f hf).1.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using vol F M⟩
  have hm : ∀ ψ₀ : S4 F, AEStronglyMeasurable
      (fun g => f.1 (gl g * dM (nu F h)) * Th (W.Om g ψ₀).1) (M.μ.restrict M.D) := fun ψ₀ =>
    (hc.measurable.mul (thMeas F E D W ψ₀).1).aestronglyMeasurable
  have hP : Continuous fun s : ℝ => (gl (cD (nu F h) (G s)))⁻¹ * dM (nu F h) :=
    (continuous_gl.comp (continuous_cD.comp (continuous_const.prodMk hG))).inv.mul continuous_const
  have key : ∀ φ₀ ∈ Fock D.δ, ∃ B : ℝ, ∀ s ∈ Metric.closedBall (0 : ℝ) 1, ∀ g,
      ‖f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G s) φ₀))).1‖ ≤ B := by
    intro φ₀ hφ₀
    obtain ⟨B, hB⟩ := thBoundH F E D W π f hf φ₀ hφ₀ h _
      ((isCompact_closedBall (0 : ℝ) 1).image hP) {1} isCompact_singleton
      (by rintro _ rfl; simp [Ff.One, nu])
    refine ⟨B, fun s hs g => ?_⟩
    have e1 : W.L h (W.Om (G s) φ₀) = W.Om (cD (nu F h) (G s)) (W.L h φ₀) :=
      LinearMap.congr_fun (W.comm h (G s)) φ₀
    have e2 : W.Om g (W.Om (cD (nu F h) (G s)) (W.L h φ₀)) = W.Om (g * cD (nu F h) (G s)) (W.L h φ₀) := by
      rw [map_mul]; rfl
    have e3 : gl g * dM (nu F h) =
        gl (g * cD (nu F h) (G s)) * ((gl (cD (nu F h) (G s)))⁻¹ * dM (nu F h)) := by
      rw [gl_mul, mul_assoc, mul_inv_cancel_left]
    have h1 := hB (g * cD (nu F h) (G s)) _ ⟨s, hs, rfl⟩ 1 rfl
    rw [← e3] at h1
    rw [e1, e2]
    simpa using h1
  obtain ⟨B, hB⟩ := key φ' hφ'
  obtain ⟨B₀, hB₀⟩ := key φ hφ
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := M.μ.restrict M.D)
    (F := fun s g => f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G s) φ))).1)
    (F' := fun s g => f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G s) φ'))).1)
    (x₀ := (0 : ℝ)) (s := Metric.closedBall 0 1) (bound := fun _ => B)
    (Metric.closedBall_mem_nhds 0 one_pos)
    (Eventually.of_forall fun s => hm _)
    (Integrable.of_bound (hm _) B₀ (ae_of_all _ fun g => hB₀ 0 (by simp) g))
    (hm _)
    (ae_of_all _ fun g s hs => hB s hs g)
    (integrable_const B)
    (ae_of_all _ fun g s _ => (thDerOm F E D W φ φ' hφ' G hG hD g h s).const_mul _)
  have e : (∫ g in M.D, f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G 0) φ'))).1 ∂M.μ) =
      lift W M f.1 φ' h := by
    simp [lift, hG0]
  have := hmain.2
  rw [e] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WeilLiftOneCuspidal
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.weilLift_one_cuspidal :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), UnfoldedThetaIntegralConvergesSimilitudeOne W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ x
  have hL := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1
  have hW := UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 hL
  have hWc : Continuous fun g : G1 F => Wf f.1 (gl g * x) :=
    hW.1.comp (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const)
  have hm : ∀ φ : S4 F, Measurable fun g => Wf f.1 (gl g * x) * hat (W.Om g φ).1 ![0, 1, 1, 0] := fun φ =>
    hWc.measurable.mul ((thMeas F E D W φ).2.2.2.2 _)
  refine ⟨hm φ, ?_, ?_⟩
  · intro b g
    have h1 : Wf f.1 (gl (nU b * g) * x) = ψ (-b) * Wf f.1 (gl g * x) := by
      rw [UpperTheory.ConvolutionTheory.R2.gl_mul, mul_assoc]
      exact hW.2.1 b _
    have h2 : hat (W.Om (nU b * g) φ).1 ![0, 1, 1, 0] = ψ b * hat (W.Om g φ).1 ![0, 1, 1, 0] := by
      rw [map_mul, Module.End.mul_apply, (hatSt F E D W).n b (W.Om g φ) ![0, 1, 1, 0]]
      have e : Function.update ![(0 : A F), 1, 1, 0] 1 (![(0 : A F), 1, 1, 0] 1 + b * ![(0 : A F), 1, 1, 0] 0) = ![0, 1, 1, 0] := by
        ext i; fin_cases i <;> simp
      rw [e]
      simp
    rw [h1, h2]
    have h3 : ψ (-b) * ψ b = 1 := by
      rw [UpperTheory.ConvolutionTheory.R2.ψ_neg]; exact inv_mul_cancel₀ (UpperTheory.ConvolutionTheory.R2.ψ_ne_zero b)
    calc _ = (ψ (-b) * ψ b) * (Wf f.1 (gl g * x) * hat (W.Om g φ).1 ![0, 1, 1, 0]) := by ring
      _ = _ := by rw [h3, one_mul]
  · intro hφ y hy
    obtain ⟨N, hN⟩ := wtId F
    obtain ⟨K, hK, hB'⟩ := hatMaj F E D W φ hφ y hy
    obtain ⟨B', hB'⟩ := hB' N
    obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.R2.Pp.bdd F π f hf {x} isCompact_singleton
    have := M.prob
    have hI := (hN K hK).comp_fst M.κ
    have hmaj : Integrable (fun p : IdeleGroup F × G1 F => (B * B') * ((ab p.1)⁻¹ * wt K N ![0, ((p.1⁻¹ : (A F)ˣ) : A F), (p.1 : A F), 0])) M.ν :=
      hI.const_mul _
    refine hmaj.mono' ?_ ?_
    · have hc : Continuous fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
        (UpperTheory.ConvolutionTheory.R2.continuous_mD.comp continuous_fst).mul continuous_snd
      have hab : Continuous fun p : IdeleGroup F × G1 F => ab p.1 :=
        UpperTheory.ConvolutionTheory.R2.continuous_ab.comp continuous_fst
      have hmm : Measurable (iw fun g => Wf f.1 (gl g * x) * hat (W.Om g (W.L (infGL E 2 y) φ)).1 ![0, 1, 1, 0]) :=
        (Complex.continuous_ofReal.comp ((hab.inv₀ fun p => UpperTheory.ConvolutionTheory.R2.ab_ne_zero _).pow 2)).measurable.mul
          ((hm (W.L (infGL E 2 y) φ)).comp hc.measurable)
      exact hmm.aestronglyMeasurable
    · have hk : ∀ᵐ p ∂M.ν, p.2 ∈ KK F := Measure.quasiMeasurePreserving_snd.ae (by
        have := M.supp
        exact measure_eq_zero_iff_ae_notMem.1 (by simpa using this) |>.mono (fun k hk => by simpa using hk))
      filter_upwards [hk] with p hp
      obtain ⟨a, k⟩ := p
      have hk' : k ∈ KK F := hp
      have h1 := (hB (mD a * k) x rfl).2
      have h2 := hB' 0 a k hk' 1 1 0
      rw [UpperTheory.ConvolutionTheory.R2.nU_zero, one_mul, mul_one, mul_one, mul_zero] at h2
      have hpos : 0 < ab a := UpperTheory.ConvolutionTheory.R2.ab_pos a
      have hB0 : 0 ≤ B := (norm_nonneg _).trans h1
      simp only [iw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      calc ((ab a)⁻¹ ^ 2) * (‖Wf f.1 (gl (mD a * k) * x)‖ * ‖hat (W.Om (mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 1, 1, 0]‖)
          ≤ ((ab a)⁻¹ ^ 2) * (B * (B' * ab a * wt K N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0])) := by
            gcongr
        _ = _ := by field_simp
end

