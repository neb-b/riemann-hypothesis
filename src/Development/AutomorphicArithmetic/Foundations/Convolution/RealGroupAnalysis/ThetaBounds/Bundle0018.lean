module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0016
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DerX
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.derX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), DerX O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ Y s hY h
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨z, c, hc, hz⟩ := UpperTheory.ConvolutionTheory.R2.Ff.cenExp F E D s
  have hc0 : c 0 = 1 := ((UpperTheory.ConvolutionTheory.R2.Ff.parCont F).2 c _ hc).1
  let χ : ℝ → ℂ := fun t => ((ω (ideleNorm F E (z t)) : ℂˣ) : ℂ)
  have hfx : ∀ t x, f.1 (x * TR.infGL F 2 (c t)) = χ t * f.1 x := by
    intro t x
    rw [← (hz t).2, ← UpperTheory.ConvolutionTheory.R2.scalar_comm, hω f hf]
  have hfun : ∀ t, lift W M f.1 φ (h * infGL E 2 (ex (Y + zE s) t)) =
      χ t * lift W M f.1 φ (h * infGL E 2 (ex Y t)) := by
    intro t
    rw [(UpperTheory.ConvolutionTheory.R2.Ff.exPar E Y).2.2.2.2 s t, map_mul, (hz t).1, ← mul_assoc,
      ← UpperTheory.ConvolutionTheory.R2.scalar_comm, mul_assoc]
    exact (UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).2 ω (hω f hf) (z t) _
  have hlin := (UpperTheory.ConvolutionTheory.R2.Ff.lin F E D W M π).2.2.2
  have hG := UpperTheory.ConvolutionTheory.R2.Ff.derL F E D O W M π f hf φ hφ Y hY h
  have hD : HasDerivAt (fun t => χ t * lift W M f.1 φ h)
      (lift W M (TR.lie F 2 (zF (trI F s)) f).1 φ h) 0 := by
    have h0 := UpperTheory.ConvolutionTheory.R2.Ff.derF F E D W M π f hf φ hφ c _ hc h
    refine h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have e : (fun x => f.1 (x * TR.infGL F 2 (c t))) = χ t • f.1 := by
      funext x
      exact hfx t x
    simp only [e]
    rw [hlin]
    rfl
  by_cases h0 : f.1 = 0
  · have hz0 : ∀ (φ₁ : S4 F) h₁, lift W M f.1 φ₁ h₁ = 0 := by
      intro φ₁ h₁
      have := congrFun (hlin f.1 0 φ₁) h₁
      rw [zero_smul] at this
      rw [h0] at this ⊢
      simpa using this
    have hl : lift W M (TR.lie F 2 (zF (trI F s)) f).1 φ h = 0 := by
      have hc' : HasDerivAt (fun t => χ t * lift W M f.1 φ h) 0 0 := by
        simp only [hz0, mul_zero]
        exact hasDerivAt_const _ _
      exact hD.unique hc'
    rw [hl, hz0, add_zero]
    simp only [hz0]
    exact hasDerivAt_const _ _
  · obtain ⟨g, hg⟩ : ∃ g, f.1 g ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h0 (funext hn)
    have hcv := TR.hasDerivAt_curve f g c _ hc0 hc.2
    have hχ : HasDerivAt χ (TR.lieD (zF (trI F s)) f.1 g / f.1 g) 0 := by
      refine (hcv.div_const (f.1 g)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      show χ t = f.1 (g * TR.infGL F 2 (c t)) / f.1 g
      rw [hfx, mul_div_assoc, div_self hg, mul_one]
    have hχ0 : χ 0 = 1 := by
      have := hfx 0 g
      rw [hc0, map_one, mul_one] at this
      exact (mul_right_cancel₀ hg (by rw [one_mul]; exact this.symm))
    have hex0 : ex Y 0 = 1 := by
      have := (UpperTheory.ConvolutionTheory.R2.Ff.exPar E Y).1 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    have hl := hD.unique (hχ.mul_const (lift W M f.1 φ h))
    have hp := hχ.mul hG
    rw [hex0, map_one, mul_one, hχ0, one_mul, ← hl, add_comm] at hp
    exact hp.congr_of_eventuallyEq (Filter.Eventually.of_forall hfun)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieL
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), LieL O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ Y hY Φ hΦ
  funext g
  have hE := (exPar E Y)
  have h0 : ex Y 0 = 1 := by
    refine Units.ext ?_
    show NormedSpace.exp ((0 : ℝ) • Matrix.of Y) = 1
    rw [zero_smul, NormedSpace.exp_zero]
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve Φ g (ex Y) Y h0 hE.2.2.1
  have h2 := derL F E D O W M π f hf φ hφ Y hY g
  rw [hΦ] at h1
  rw [GlobalTheory.CuspRep.lie_apply, hΦ]
  exact h1.unique h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieZ
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieZ :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), LieZ W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ s Φ hΦ
  funext h
  obtain ⟨hadd, -, hder, -, -⟩ := UpperTheory.ConvolutionTheory.R2.Ff.exPar E (zE s)
  have h0 : ex (zE s) 0 = 1 := by
    have h00 := hadd 0 0
    rw [add_zero] at h00
    exact left_eq_mul.mp h00
  obtain ⟨z, c, hc, hz⟩ := UpperTheory.ConvolutionTheory.R2.Ff.cenExp F E D s
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  have hE := (UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).2 ω (hω f hf)
  have hlin := (UpperTheory.ConvolutionTheory.R2.Ff.lin F E D W M π).2.2.2
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve Φ h (ex (zE s)) (zE s) h0 hder
  have h2 := UpperTheory.ConvolutionTheory.R2.Ff.derF F E D W M π f hf φ hφ c _ hc h
  have key : ∀ t, lift W M (fun x => f.1 (x * TR.infGL F 2 (c t))) φ h =
      Φ.1 (h * infGL E 2 (ex (zE s) t)) := by
    intro t
    obtain ⟨e1, e2⟩ := hz t
    have e3 : (fun x => f.1 (x * TR.infGL F 2 (c t))) = ((ω (ideleNorm F E (z t)) : ℂˣ) : ℂ) • f.1 := by
      funext x
      rw [← e2, ← UpperTheory.ConvolutionTheory.R2.scalar_comm, hω f hf]
      rfl
    rw [hΦ, e1, e3, hlin, ← UpperTheory.ConvolutionTheory.R2.scalar_comm (z t) h, hE]
    rfl
  have h3 : HasDerivAt (fun t => Φ.1 (h * infGL E 2 (ex (zE s) t)))
      (lift W M (TR.lie F 2 (zF (trI F s)) f).1 φ h) 0 := by
    simpa only [key] using h2
  exact h1.unique h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Mov
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.mov :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Mov W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ φ' hφ' G c Y hP hG hD
  obtain ⟨hinf, hPc⟩ := UpperTheory.ConvolutionTheory.R2.Ff.parCont F
  obtain ⟨hc0, hcc, hPn⟩ := hPc c Y hP
  have hGc : Continuous G := continuous_adelicSL2_of_continuous_entries fun i j => by
    have e : (fun t => G t i j) = fun t => (TR.infGL F 2 (c t)).val i j := by
      funext t
      rw [← hG t]
      rfl
    rw [e]
    have hv : Continuous fun t => (TR.infGL F 2 (c t)).val :=
      Units.continuous_val.comp (hinf.comp hcc)
    exact hv.matrix_elem i j
  have hG0 : G 0 = 1 := gl_injective (by rw [hG, hc0, map_one, gl_one])
  have hL : LRat f.1 := (π.cusp f hf).1.left
  have hinv : ∀ t, (gl (G t))⁻¹ = TR.infGL F 2 (c (-t)) := fun t => by
    have h1 : c (-t) = (c t)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← hP.1, neg_add_cancel, hc0])
    rw [hG, h1, map_inv]
  funext h
  have d1 := UpperTheory.ConvolutionTheory.R2.Ff.derOm F E D W M π f hf φ hφ φ' hφ' G hGc hG0 hD h
  have d2 := UpperTheory.ConvolutionTheory.R2.Ff.derF F E D W M π f hf φ hφ (fun t => c (-t)) (-Y) hPn h
  have e : (fun t => lift W M (fun x => f.1 (x * TR.infGL F 2 (c (-t)))) φ h) =
      fun t => lift W M f.1 (W.Om (G t) φ) h := by
    funext t
    rw [UpperTheory.ConvolutionTheory.R2.Ff.movG F E D W M f.1 hL φ (G t) h, hinv]
  rw [e] at d2
  have hu := d1.unique d2
  have hl : (TR.lie F 2 (-Y) f).1 = (-1 : ℂ) • (TR.lie F 2 Y f).1 := by
    rw [map_neg]
    funext x
    simp
  have h4 := (UpperTheory.ConvolutionTheory.R2.Ff.lin F E D W M π).2.2.2 (TR.lie F 2 Y f).1 (-1) φ
  rw [hu, hl, h4]
  simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormDetKinf
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem norm_det_kinf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : Kinf E 2)
    (w : InfinitePlace E) : ‖(Unitary.toUnits k).val.det w‖ = 1 := by
  have h : star k.1 * k.1 = 1 := by simp
  have hd : star (k.1.det) * k.1.det = 1 := by
    have := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at this
  have hw : star (k.1.det w) * k.1.det w = 1 := congrFun hd w
  have hn : ‖k.1.det w‖ * ‖k.1.det w‖ = 1 := by
    have := congrArg norm hw
    rwa [norm_mul, norm_star, norm_one] at this
  have h0 : 0 ≤ ‖k.1.det w‖ := norm_nonneg _
  change ‖k.1.det w‖ = 1
  nlinarith

private theorem dM_one' {F : Type} [Field F] [NumberField F] : dM (1 : (A F)ˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM]

theorem UpperTheory.ConvolutionTheory.R2.Ff.kFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), KFin W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ Φ hΦ
  have hl := lin F E D W M π
  obtain ⟨U, hUF, hfd, hU⟩ := (fockSt F E D W).cpt φ hφ
  have key : ∀ k : Kinf E 2, (cptRep E 2 k Φ).1 = lift W M f.1 (W.L (infGL E 2 (Unitary.toUnits k)) φ) := by
    intro k
    funext h
    have h1 : nu F (infGL E 2 (Unitary.toUnits k)) = 1 :=
      oneOf F E D (Unitary.toUnits k) (norm_det_kinf k)
    have h2 := transl F E D W M f.1 φ h (infGL E 2 (Unitary.toUnits k))
    rw [h1, dM_one'] at h2
    simp only [mul_one] at h2
    change Φ.1 (h * infGL E 2 (Unitary.toUnits k)) = _
    rw [hΦ]
    exact h2
  refine ⟨fun k => Submodule.subset_span ⟨f, hf, _, hUF (hU k), key k⟩, ?_⟩
  haveI := hfd
  let T : U →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ) :=
    { toFun := fun u => lift W M f.1 u.1
      map_add' := fun u u' => hl.1 f hf u.1 (hUF u.2) u'.1 (hUF u'.2)
      map_smul' := fun c u => hl.2.1 f.1 c u.1 }
  have hle : (Submodule.span ℂ (Set.range fun k => cptRep E 2 k Φ)).map (Sm E 2).subtype ≤ LinearMap.range T := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨⟨_, hU k⟩, (key k).symm⟩
  haveI : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range fun k => cptRep E 2 k Φ)).map (Sm E 2).subtype) :=
    Submodule.finiteDimensional_of_le hle
  exact (Submodule.equivMapOfInjective (Sm E 2).subtype (Submodule.injective_subtype _) _).symm.finiteDimensional
end

