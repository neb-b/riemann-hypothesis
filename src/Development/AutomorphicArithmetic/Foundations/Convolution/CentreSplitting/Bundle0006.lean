module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.ExpGen
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfIff
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V
open scoped TensorProduct

private theorem UpperTheory.ConvolutionTheory.Dp.sInfIff_uC {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}
    (p q : UEnv E n) (ψ : cuspForms E n) :
    Cm.uC E n ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) (Cm.ofCusp E n ψ) =
      Cm.ofCusp E n (uActionCusp E n p ψ + Complex.I • uActionCusp E n q ψ) := by
  rw [map_add (f := _), map_add (f := _), map_smul, Cm.ofCusp_uAction, Cm.ofCusp_uAction, Cm.uC_tmul, Cm.uC_tmul, one_smul]
  rfl

theorem UpperTheory.ConvolutionTheory.Dp.sInfIff :
    UpperTheory.ConvolutionTheory.Dp.SInfIff := by
  intro E _ _ _ n μ _ π V h τ m
  rw [UpperTheory.ConvolutionTheory.Dp.infZc E n π τ m]
  have hcen := (UpperTheory.ConvolutionTheory.Dp.capZc E n τ).1
  have hform := (UpperTheory.ConvolutionTheory.Dp.formsIrr E n μ V h.summand).2.2.2
  have hcls := (UpperTheory.ConvolutionTheory.Dp.clsBasic E n μ).1
  unfold SInf
  refine and_congr_right fun _ => ⟨fun H i φ hφ => ?_, fun H ν _ β hβ i v hv => ?_⟩
  · obtain ⟨p, hp, q, hq, hzc⟩ := Cm.exists_re_im_center (hcen i)
    rw [← Cm.map_carrier π] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    have hψ' : ψ ∈ formsIn μ V := h.carrier_eq ▸ hψ
    obtain ⟨hψc, hψV⟩ := hψ'
    have hz : clsL μ ((uActionCusp E n p ψ + Complex.I • uActionCusp E n q ψ) - m.esymm (i + 1) • ψ) = 0 := by
      refine UpperTheory.ConvolutionTheory.Dp.diracSep E n μ (Measure.haar : Measure (archGroup E n)) _ fun β hβ => ?_
      have h1 := H Measure.haar β hβ i _ hψV
      rw [hzc, UpperTheory.ConvolutionTheory.Dp.lactCen_of_gen E n (UpperTheory.ConvolutionTheory.Tf.expGen E n) μ Measure.haar β hβ p hp q hq ψ hψc] at h1
      rw [map_sub, map_smul, map_sub, map_smul, h1, sub_self]
    have hz0 := hcls _ (sub_mem (add_mem (uActionCusp_mem_centralCuspForms p hψc)
      (Submodule.smul_mem _ _ (uActionCusp_mem_centralCuspForms q hψc))) (Submodule.smul_mem _ _ hψc)) hz
    rw [hzc, sInfIff_uC, sub_eq_zero.1 hz0, map_smul]
  · obtain ⟨p, hp, q, hq, hzc⟩ := Cm.exists_re_im_center (hcen i)
    rw [hzc]
    have hclosed : IsClosed {v : LL μ | Oinf μ ν (lact ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β) v =
        m.esymm (i + 1) • Oinf μ ν β v} :=
      isClosed_eq (ContinuousLinearMap.continuous _) ((continuous_const_smul (m.esymm (i + 1))).comp (Oinf μ ν β).continuous)
    have hsub : (((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) ⊆
        {v : LL μ | Oinf μ ν (lact ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β) v =
          m.esymm (i + 1) • Oinf μ ν β v} := by
      rintro _ ⟨ψ, hψ, rfl⟩
      have hφ : Cm.ofCusp E n ψ ∈ π.V := Cm.mem_carrier.1 (h.carrier_eq.symm ▸ hψ)
      have e := H i _ hφ
      rw [hzc, sInfIff_uC] at e
      have e' := Cm.ofCusp_injective (e.trans (map_smul (Cm.ofCusp E n) _ ψ).symm)
      change Oinf μ ν _ (clsL μ ψ) = _
      rw [UpperTheory.ConvolutionTheory.Dp.lactCen_of_gen E n (UpperTheory.ConvolutionTheory.Tf.expGen E n) μ ν β hβ p hp q hq ψ hψ.1, e', map_smul, map_smul]
    have hv' : v ∈ ((formsIn μ V).map (clsL μ)).topologicalClosure := by rw [hform]; exact hv
    exact closure_minimal hsub hclosed hv'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatEx
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.sSatEx :
    UpperTheory.ConvolutionTheory.Dp.SSatEx := by
  intro E _ _ _ n μ _ V hV w hne
  have hex : ∃! π : CuspSub E n, Carries μ π V := exCusp E n μ V hV
  obtain ⟨π, h, -⟩ := hex
  obtain ⟨J, hi, hd, -, hJ'⟩ := UpperTheory.ConvolutionTheory.Dp.locEmb E n μ π V h
  have hρ : ∀ g v, ‖locOn h.summand w g v‖ = ‖v‖ := fun g v => by
    change ‖RG μ (finGL E n (locGL E n w g)) (v : LL μ)‖ = ‖(v : LL μ)‖
    exact UnitaryRep.norm_map _ _ _
  have hK := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  have hdense := UpperTheory.ConvolutionTheory.Dp.fixedDense _ _ _ (locOn h.summand w) (π.locRep w) J (GlobalTheory.LFun.KGL w (n := n)) hK hρ
    (π.isSmooth_locRep w) (hJ' w) hd
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hfix : ∀ u ∈ GlobalTheory.LFun.KGL w (n := n), locOn h.summand w u ⟨v, hv.1⟩ = ⟨v, hv.1⟩ := fun u hu => by
    refine Subtype.ext ?_
    change localRepresentationL2 μ w u v = v
    rw [← rhoLoc E n μ w u v]
    have h2 := hv.2
    simp only [UpperTheory.ConvolutionTheory.fixL, UpperTheory.ConvolutionTheory.fixF, SetLike.mem_coe, Submodule.mem_iInf] at h2
    exact h2 _ ⟨u, by exact (PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.KGL_eq w n).le hu, rfl⟩
  have hs : GlobalTheory.LGrp.IsSpherical (π.locRep w) (GlobalTheory.LFun.KGL w (n := n)) := by
    refine (Submodule.ne_bot_iff _).2 ?_
    by_contra hno
    push_neg at hno
    have hsub : J '' {x | ∀ u ∈ GlobalTheory.LFun.KGL w (n := n), π.locRep w u x = x} ⊆ {0} := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hno x (GlobalTheory.LGrp.mem_fixed.2 hx), map_zero]
      rfl
    exact h0 (congrArg Subtype.val (closure_minimal hsub isClosed_singleton (hdense _ hfix)))
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_locRep π w hs
  exact ⟨_, (tsphVec E n μ w V hV B).1 ((satIff E n μ π V h w B).1 hB)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.sSatIff :
    UpperTheory.ConvolutionTheory.Dp.SSatIff := by
  intro E _ _ _ n μ _ π V h w B
  constructor
  · intro hB
    obtain ⟨B', rfl⟩ := (sSatUnit E n μ w V B hB).1
    exact ⟨B', rfl, (satIff E n μ π V h w B').2 ((tsphVec E n μ w V h.summand B').2 hB)⟩
  · rintro ⟨B', rfl, hB⟩
    exact (tsphVec E n μ w V h.summand B').1 ((satIff E n μ π V h w B').1 hB)
end

