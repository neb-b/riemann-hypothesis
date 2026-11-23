module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm in
theorem UpperTheory.ConvolutionTheory.R2.Pp.cuspZero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.CuspZero F := by
  intro F _ _ _ π f hf
  have hc : Continuous f.1 := by
    have hp : Continuous (TR.pInf F) := by
      have hc : Continuous (TR.infEq F).symm :=
        continuous_pi fun w =>
          (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
      exact hc.comp continuous_fst
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hm : Continuous fun x : GA F 2 => g⁻¹ * x := continuous_const.mul continuous_id
    have hI : Continuous (Matrix.GeneralLinearGroup.map (TR.pInf F) : GA F 2 → GL (Fin 2) (TR.Rinf F)) :=
      Continuous.units_map _ (continuous_id.matrix_map hp)
    have hFn : Continuous (Matrix.GeneralLinearGroup.map (pFin F) : GA F 2 → GL (Fin 2) (Af F)) :=
      Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
    have h1 : Continuous fun x : GA F 2 => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val :=
      (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (TR.Rinf F))).comp (hI.comp hm)
    have h2 : ContinuousAt (fun x : GA F 2 => TR.chart f.1 g (TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)) g :=
      ContinuousAt.comp (f := fun x : GA F 2 => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)
        (TR.contDiffAt_chart f.2 g (TR.val_mem_invSet _)).continuousAt h1.continuousAt
    refine h2.congr ?_
    have h3 : {x : GA F 2 | TR.finRep F 2 (Matrix.GeneralLinearGroup.map (pFin F) (g⁻¹ * x)) f = f} ∈ 𝓝 g :=
      ((π.cusp f hf).1.level.preimage (hFn.comp hm)).mem_nhds (by simp)
    filter_upwards [h3] with x hx
    rw [TR.chart_val]
    conv_lhs => rw [← hx]
    change f.1 (g * TR.infGL F 2 _ * finGL F 2 _) = _
    rw [mul_assoc, TR.infGL_mul_finGL, mul_inv_cancel_left]
  refine ⟨⟨hc, (π.cusp f hf).1.left⟩, fun g => ?_⟩
  letI : Unique (BlockIx 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  rw [← int_one (ι := BlockIx 2 1)]
  have hz := (π.cusp f hf).2 1 one_pos one_lt_two (FourierWhittaker.vecMeasure F (BlockIx 2 1)) (FourierWhittaker.vecDomain F (BlockIx 2 1)) inferInstance (by exact FourierWhittaker.isAddFundamentalDomain_vecDomain) g
  rw [← hz]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have : gl (nU (x default)) = unip x := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vn, unip, nilM]
    rfl
  simp only [this]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfBasic
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfBasic :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfBasic F := by
  intro F _ _ f hf
  have hc : ∀ {f : GL (Fin 2) (A F) → ℂ}, Lf f → ∀ g, IntegrableOn (fun b => f (gl (nU b) * g) * ψ b) (fundamentalSet F)
      (adeleMeasure F) := fun hf g => intOn ((hf.1.comp (cont_n.mul continuous_const)).mul cont_ψ)
  refine ⟨?_, fun b g => ?_, hc hf, fun c g => ?_, fun f' hf' g => ?_⟩
  · obtain ⟨C, hC, hs⟩ := exists_cpt (F := F)
    have e : Wf f = fun g => ∫ b in C, f (gl (nU b) * g) * ψ b ∂((adeleMeasure F).restrict (fundamentalSet F)) := by
      funext g
      rw [Measure.restrict_restrict hC.measurableSet, Set.inter_eq_right.2 hs]; rfl
    rw [e]
    haveI : IsFiniteMeasure ((adeleMeasure F).restrict (fundamentalSet F)) :=
      isFiniteMeasure_restrict.2 (by rw [adeleMeasure_fundamentalSet]; exact ENNReal.one_ne_top)
    set_option synthInstance.maxHeartbeats 200000 in
    exact continuous_parametric_integral_of_continuous
      ((hf.1.comp ((cont_n.comp continuous_snd).mul continuous_fst)).mul (cont_ψ.comp continuous_snd)) hC
  · unfold Wf
    rw [← integral_const_mul, ← int_add (h := fun x => ψ (-b) * (f (gl (nU x) * g) * ψ x))
      (fun k x => by rw [hf.per, ψ_add, ψ_rt, one_mul]) b]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : ψ (-b) * ψ (x + b) = ψ x := by rw [← ψ_add]; congr 1; ring
    simp only [n_add, mul_assoc]
    rw [mul_left_comm, this]
  · unfold Wf
    rw [← integral_const_mul]
    simp [mul_assoc]
  · unfold Wf
    rw [← integral_add (hc hf g) (hc hf' g)]
    simp [add_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfEig
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open UpperTheory.V.Af.Smo (Eig)

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfEig :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfEig F := by
  intro F _ _ f hf v B h g
  let W (b : A F) (y : GL (Fin 2) (v.adicCompletion F)) :=
    f (gl (nU b) * (g * finGL F 2 (locGL F 2 v y)))
  have hW (b : A F) : Eig v B (W b) := by
    simpa only [W, mul_assoc] using h (gl (nU b) * g)
  have hi (y : GL (Fin 2) (v.adicCompletion F)) :
      IntegrableOn (fun b => W b y * ψ b) (fundamentalSet F) (adeleMeasure F) :=
    intOn ((hf.1.comp (cont_n.mul continuous_const)).mul cont_ψ)
  change Eig v B (fun y => ∫ b in fundamentalSet F, W b y * ψ b ∂(adeleMeasure F))
  refine ⟨(h 1).card, fun y k hk => by simp only [fun b => (hW b).inv y k hk],
    fun ϖ hϖ j hj y => ?_⟩
  have hsupp := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm F v 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  have hsum (G : GL (Fin 2) (v.adicCompletion F) ⧸ GlobalTheory.LFun.KGL v (n := 2) → ℂ) :
      ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov F v) ϖ j c.out * G c =
        ∑ c ∈ hsupp.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov F v) ϖ j c.out * G c := by
    refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
    rw [Set.Finite.coe_toFinset]
    exact left_ne_zero_of_mul hc
  rw [hsum]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have hb := (hW b).eig ϖ hϖ j hj y
  rw [hsum] at hb
  simp only [← mul_assoc, ← hb, Finset.sum_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfT
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfT :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfT F := by
  intro F _ _ f hf t g
  unfold Wf
  rw [← int_mul (h := fun x => f (gl (nU x) * (aE (IdeleGroup.diagonal F t) * g)) * ψ x)
    (fun k x => by rw [hf.per, ψ_add, ψ_rt, one_mul]) t]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  obtain ⟨γ, hγ⟩ := rat_a t
  have := a_n (IdeleGroup.diagonal F t) x
  simp only
  rw [← hf.2 γ (gl (nU x) * g), hγ, ← mul_assoc, ← mul_assoc, this]
  rfl
end

