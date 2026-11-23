module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0036

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseSmul
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem hasseSmul_holds : HasseSmul := by
  intro D B P j X ka wL wF G la k o x hx β hβ h h'
  classical
  have hmem : ∀ q : Idx D j G.N →₀ ℕ, hasse X la G.w q (x : Lw X la G.w) ∈ HK X la G.w wF := fun q =>
    (mem_HK X la G.w).2 (hasse_presentation X la G.w wF q _ ((mem_HK X la G.w).1 x.2))
  have key : (⟨_, h⟩ : ↥(HK X la G.w wF)) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β,
      (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (hasseOp X la G.N q.1 o)) •
        (⟨_, hmem q.2⟩ : ↥(HK X la G.w wF)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    show hasse X la G.w β ((o • x : ↥(HK X la G.w wF)) : Lw X la G.w) = _
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (Op X la G.N) (Rp X la G.N) (Lw X la G.w)]
    erw [hasse_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    erw [hasse_algebraMap_Op]
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def]
    congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum, Finset.sum_eq_single (0, β)]
  · rw [LinearMap.map_smul_of_tower, hasseOp_zero, algebraMap_smul]
  · intro q hq hne
    rw [LinearMap.map_smul_of_tower]
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have h1 : q.1 ≠ 0 := fun h0 => hne (Prod.ext h0 (by rw [← hq, h0, zero_add]))
    have h2 : (q.2.sum fun _ n => n) < k := by
      rw [sumN_eq] at hβ ⊢
      rw [← hq, map_add (f := _)] at hβ
      have : Finsupp.degree q.1 ≠ 0 := fun h0 => h1 ((Finsupp.degree_eq_zero_iff _).1 h0)
      omega
    rw [hasseVan_holds G la k x hx q.2 h2 (hmem q.2), smul_zero]
  · intro h0
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add β)) h0

end PoleLengthBounds
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.UInjOfColumn
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem uInj_of_column (hCol : Column) : UInj := by
  unfold UInj
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw α b hb
  have hC : Q.InCurve := hOk.2.1
  have hU := isUnif_of_curve Q hC
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := fun ζ => isDVRAt_of_curve Q hC ζ
  have hco : (coord Q.e b : OsK X la G.w) = 0 := by
    refine eq_zero_of_ord_top hU fun ζ => ?_
    obtain ⟨jj, hjj⟩ := (hCol G la Q S CRm T c hOk hw ζ).2
    have h1 := congrArg (ordV (unifO X la G.N) ζ Q.e Q.c) (hb jj)
    rw [ordV_smul Q.c ζ hU hC.2.2, ord_uC_eq_zero Q hC ζ jj α hjj, zero_add,
      ordV_zero Q.c ζ hU hC.2.2, ordV, WithTop.add_eq_top] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 WithTop.coe_ne_top
  rw [← coord_smul_self hC.2.2 b, hco, zero_smul]

end PoleLengthBounds
end
end

