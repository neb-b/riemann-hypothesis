module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.StabFin

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.CmpEquiv
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem cmpEquiv_holds : CmpEquiv := by
  intro E _ _ _ a μ _ _ μ₁ _ hp g v
  have hquot (q : Quot (latticeGL E a)) :
      quotMap E a (rmul (latticeGL E a) g q) =
        RightCosetSpace.rightMul (Γ1 E a) (retractOne g) (quotMap E a q) := by
    refine Quotient.inductionOn q fun x => ?_
    simp only [rmul_mk, quotMk_holds E a, RightCosetSpace.rightMul_mk, retractOne_mul]
  have hcmp (w : CuspL2 μ₁) :
      (cmp hp w : Quot (latticeGL E a) → ℂ) =ᵐ[quotMeasure (latticeGL E a) μ]
        (toLp μ₁ w : RightCosetSpace (Γ1 E a) → ℂ) ∘ quotMap E a :=
    Lp.coeFn_compMeasurePreserving (toLp μ₁ w) hp
  have hpres := measurePreserving_rmul (Γ := latticeGL E a) (μ := μ) g
  have htranslated := hpres.quasiMeasurePreserving.ae (hcmp v)
  have hrep :
      (toLp μ₁ (cuspRepT μ₁ (retractOne g) v) : RightCosetSpace (Γ1 E a) → ℂ)
        =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] fun x =>
          (toLp μ₁ v : RightCosetSpace (Γ1 E a) → ℂ)
            (RightCosetSpace.rightMul (Γ1 E a) (retractOne g) x) := by
    rw [toLp_cuspRepT]
    exact RightCosetSpace.coeFn_rightTranslate _ μ₁ (retractOne g) (toLp μ₁ v)
  apply Lp.ext
  filter_upwards [coeFn_R g (cmp hp v), htranslated, hcmp (cuspRepT μ₁ (retractOne g) v),
    hp.quasiMeasurePreserving.ae hrep] with q hR hleft hright hrepq
  simp only [Function.comp_apply] at hleft hright
  rw [hR, hleft, hright, hrepq, hquot]

end UpperTheory.V.KernelIndexFullLattice
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.CmpForm
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.KernelIndexFullLattice

theorem cmpForm_holds : CmpForm := by
  intro E _ _ _ a μ _ μ₁ _ hp φ hφ
  have hRep : (toLp μ₁ (cuspVecL μ₁ φ) : RightCosetSpace (Γ1 E a) → ℂ)
      =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] cuspQuot φ.2.1.isLeftInvariant := by
    rw [toLp_cuspVecL]
    exact coeFn_cuspToL2 μ₁ φ
  have hQuot : (cmp hp (cuspVecL μ₁ φ) : Quot (latticeGL E a) → ℂ)
      =ᵐ[quotMeasure (latticeGL E a) μ] cuspQuot φ.2.1.isLeftInvariant ∘ quotMap E a :=
    (Lp.coeFn_compMeasurePreserving _ hp).trans (hp.quasiMeasurePreserving.ae_eq_comp hRep)
  filter_upwards [ae_quotMeasure_iff.1 hQuot] with g hg
  calc
    lift (latticeGL E a) (cmp hp (cuspVecL μ₁ φ)) g =
        cuspQuot φ.2.1.isLeftInvariant (quotMap E a (mk (latticeGL E a) g)) := hg
    _ = φ.1 g := by
      rw [quotMk_holds E a g, cuspQuot_mk, coe_retractOne, ← (Reduction.centralSection E a).map_inv]
      exact apply_mul_centralSection_of_mem hφ _ _

end UpperTheory.V.KernelIndexFullLattice
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.KFinMem
section
open NumberField MeasureTheory
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem kFinMem_holds : KFinMem := by
  intro K _ _ n μ₁ _ π v hv hop hfin
  have h1 : retractOne (1 : AdelicGLn.AdelicGL K n) = 1 := retractOne_coe (1 : G1 K n)
  let r : AdelicGLn.FiniteAdelicGL K n →* G1 K n :=
    { toFun := fun h => retractOne (finEmb K n h)
      map_one' := by rw [map_one (finEmb K n), h1]
      map_mul' := fun a b => by rw [map_mul (finEmb K n), retractOne_mul] }
  let S : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    { carrier := {h | cuspRepT μ₁ (r h) v = v}
      one_mem' := by
        show cuspRepT μ₁ (r 1) v = v
        rw [map_one r]
        simp
      mul_mem' := fun {a b} ha hb => by
        have ha' : cuspRepT μ₁ (r a) v = v := ha
        have hb' : cuspRepT μ₁ (r b) v = v := hb
        show cuspRepT μ₁ (r (a * b)) v = v
        rw [map_mul r, UnitaryRep.map_mul_apply, hb', ha']
      inv_mem' := fun {a} ha => by
        have ha' : cuspRepT μ₁ (r a) v = v := ha
        show cuspRepT μ₁ (r a⁻¹) v = v
        have h := (cuspRepT μ₁).map_mul_apply (r a⁻¹) (r a) v
        rw [ha', ← map_mul r, inv_mul_cancel, map_one r] at h
        rw [← h]
        simp }
  have hSo : IsOpen (S : Set (AdelicGLn.FiniteAdelicGL K n)) := hop
  let U : Subgroup (AdelicGLn.FiniteAdelicGL K n) := S ⊓ AdelicGLn.integralFiniteGL K n
  have hUo : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) := hSo.inter (AdelicGLn.isOpen_integralFiniteGL K n)
  have hUc : IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (U.isClosed_of_isOpen hUo) fun _ h => h.2
  obtain ⟨N, hN, hN'⟩ := pvFin_holds K n μ₁ π U hUc hUo v (fun u hu => hu.1) hfin
  let A : archCompact K n ⊕ U → CuspL2 μ₁ →L[ℂ] CuspL2 μ₁ :=
    Sum.elim (fun k => cuspRepT μ₁ (archP K n k)) fun u => cuspRepT μ₁ (r u)
  refine absApprox_holds (archCompact K n ⊕ U) (CuspL2 μ₁) A ?_ _ N hN ?_ v hv
    fun P hP hPW => hN' P (fun k x => hP (.inl k) x) (fun u hu x => hP (.inr ⟨u, hu⟩) x) hPW
  · rintro (k | u)
    · refine ⟨.inl k⁻¹, ?_⟩
      show ContinuousLinearMap.adjoint (cuspRepT μ₁ (archP K n k)) = cuspRepT μ₁ (archP K n (k : archGroup K n)⁻¹)
      rw [UnitaryRep.adjoint_map, map_inv (archP K n)]
    · refine ⟨.inr u⁻¹, ?_⟩
      show ContinuousLinearMap.adjoint (cuspRepT μ₁ (r u)) =
        cuspRepT μ₁ (r (u : AdelicGLn.FiniteAdelicGL K n)⁻¹)
      rw [UnitaryRep.adjoint_map, map_inv r]
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨Y, hY, hφY, hk, hu⟩ :=
      stabFin_holds K n π.carrier π.toModule π.isAdmissible.1 U hUc ⟨φ, hφ⟩
    let j : π.carrier →ₗ[ℂ] CuspL2 μ₁ := cuspVecL μ₁ ∘ₗ π.carrier.subtype
    refine ⟨Y.map j, ?_, inferInstance, ⟨_, hφY, rfl⟩, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro (k | u) _ ⟨y, hy, rfl⟩
      · exact ⟨_, hk k y hy, cuspToL2_sigma μ₁ k (π.le_central y.2)⟩
      · exact ⟨_, hu u u.2 y hy, cuspToL2_finRepCusp μ₁ u (π.le_central y.2)⟩

end UpperTheory.V.KernelIndexFullLattice
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotPres
section
open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.KernelIndexFullLattice

private theorem measurableSet_band' (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    MeasurableSet (band E a) := by
  have hc : Continuous fun g : GA E a => (detModule E a g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  have h := hc.measurable (measurableSet_Ico (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ)))
  exact (MeasurableSet.const (a = 0)).union h

theorem UpperTheory.V.KernelIndexFullLattice.quotPres_holds :
    UpperTheory.V.KernelIndexFullLattice.QuotPres := by
  intro E _ _ _ a μ _
  have hr : Measurable (retractOne : GA E a → G1 E a) := continuous_retractOne.measurable
  have hD := RightCosetSpace.measurableSet_fundamentalDomain (Γ1 E a)
  have hmk : Measurable (RightCosetSpace.mk (Γ1 E a)) := RightCosetSpace.measurable_mk _
  have hcomp : quotMap E a ∘ mk (latticeGL E a) = RightCosetSpace.mk (Γ1 E a) ∘ retractOne :=
    funext fun g => quotMk_holds E a g
  have hq : Measurable (quotMap E a) := by
    refine measurable_from_quotient.2 ?_
    change Measurable (quotMap E a ∘ mk (latticeGL E a))
    rw [hcomp]
    exact hmk.comp hr
  have hF : IsFundamentalDomain (latticeGL E a)
      (retractOne ⁻¹' RightCosetSpace.fundamentalDomain (Γ1 E a) ∩ band E a) μ :=
    IsFundamentalDomain.mk' ((hr hD).inter (measurableSet_band' E a)).nullMeasurableSet
      (bandDom_holds E a _ (RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (Γ1 E a)))
  refine ⟨hq, ?_⟩
  rw [quotMeasure_eq hF, Measure.map_map hq measurable_mk, hcomp, RightCosetSpace.quotientMeasure, muOne,
    Measure.restrict_map hr hD, Measure.restrict_restrict (hr hD), Measure.map_map hmk hr]
end

