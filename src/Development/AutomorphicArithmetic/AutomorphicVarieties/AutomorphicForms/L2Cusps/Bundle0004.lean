module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0002
public import GroundTheory.AutomorphicForms.L2LocalComponents

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.KFinTr
section
open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem kFinTr_holds : KFinTr := by
  intro E _ _ _ a μ _ _ μ₁ _ hp v h
  have hi : Function.Injective (cmp hp) := (cmp hp).injective
  refine ⟨?_, ?_⟩
  · convert h.1 using 1
    ext k
    have e := cmpEquiv_holds E a μ μ₁ hp (finGL E a k) v
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, e, hi.eq_iff, Fb.finEmb_eq]
  · have := h.2
    have hle : (Submodule.span ℂ (Set.range fun k : archCompact E a => archRepT μ₁ (k : archGroup E a) v)).map
        (cmp hp).toLinearMap ≤ Submodule.span ℂ
        (Set.range fun k : Kinf E a => R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (cmp hp v)) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨y, hy⟩ := (Cm.grpEq E a).surjective (k : archGroup E a)
      have hu : y.val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := (Cm.grpEq_mem_archCompact y).1 (hy ▸ k.2)
      refine Submodule.subset_span ⟨⟨y.val, hu⟩, ?_⟩
      have ey : Unitary.toUnits (⟨y.val, hu⟩ : Kinf E a) = y := Units.ext rfl
      change R (latticeGL E a) μ (infGL E a (Unitary.toUnits (⟨y.val, hu⟩ : Kinf E a)))
        (cmp hp v) = cmp hp (archRepT μ₁ (k : archGroup E a) v)
      rw [ey, cmpEquiv_holds E a μ μ₁ hp (infGL E a y) v, ← Cm.infEmb_grpEq, hy, archRepT_apply,
        retract_infEmb]
    have := Submodule.finiteDimensional_of_le hle
    exact (Submodule.equivMapOfInjective (cmp hp).toLinearMap hi _).symm.finiteDimensional

end UpperTheory.V.KernelIndexFullLattice
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.RangeLe
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem rangeLe_holds : RangeLe := by
  intro E _ _ _ a μ _ μ₁ _ hp v
  have hv : v ∈ ((centralCuspForms E a).map (cuspVecL μ₁)).topologicalClosure := by
    rw [topologicalClosure_map_centralCuspForms μ₁]
    exact Submodule.mem_top
  have hmap : Set.MapsTo (cmp hp) (↑((centralCuspForms E a).map (cuspVecL μ₁)) : Set (CuspL2 μ₁))
      (L2cusp μ : Set (L2 (latticeGL E a) μ)) := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hc : Continuous φ.1 := φ.2.1.continuous
    have hl : IsLeftInvariant φ.1 := φ.2.1.isLeftInvariant
    have hcont : φ.1 ∈ cuspCont E a := by
      refine mem_cuspCont.2 ⟨hc, fun γ g => hl γ g, ?_,
        UpperTheory.isCuspidal_of_constantTerm_eq_zero E a φ.1 hl hc φ.2.2⟩
      intro t g
      rw [splitCentre_comm, splitEq_holds E a t]
      exact apply_mul_centralSection_of_mem hφ _ _
    apply mem_L2cusp_of_ae_eq hcont
    have hrep :
        (toLp μ₁ (cuspVecL μ₁ φ) : RightCosetSpace (Γ1 E a) → ℂ)
          =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] cuspQuot hl := by
      rw [toLp_cuspVecL]
      exact coeFn_cuspToL2 μ₁ φ
    have hquot :
        (cmp hp (cuspVecL μ₁ φ) : Quot (latticeGL E a) → ℂ)
          =ᵐ[quotMeasure (latticeGL E a) μ] cuspQuot hl ∘ quotMap E a :=
      (Lp.coeFn_compMeasurePreserving _ hp).trans (hp.quasiMeasurePreserving.ae_eq_comp hrep)
    filter_upwards [ae_quotMeasure_iff.1 hquot] with g hg
    calc
      lift (latticeGL E a) (cmp hp (cuspVecL μ₁ φ)) g =
          cuspQuot hl (quotMap E a (mk (latticeGL E a) g)) := hg
      _ = φ.1 g := by
        rw [quotMk_holds E a g, cuspQuot_mk, coe_retractOne, ← (Reduction.centralSection E a).map_inv]
        exact apply_mul_centralSection_of_mem hφ _ _
  exact hmap.closure_left (cmp hp).continuous (isClosed_L2cusp μ) hv

end UpperTheory.V.KernelIndexFullLattice
end

