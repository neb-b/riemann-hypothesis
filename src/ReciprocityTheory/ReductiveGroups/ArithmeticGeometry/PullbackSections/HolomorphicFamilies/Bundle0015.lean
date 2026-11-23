module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
public import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NegLogEpStar
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma neg_log_epStar (M f w k0 : ℝ) (hM : 0 < M) (hfw : 0 < f * w + 2) (hk0 : 0 < k0) (hk0' : k0 ≤ 2) :
    -Real.log (epStar M f w k0) ≤ max 0 (Real.log M + Real.log (f * w + 2) + Real.log 2) := by
  unfold epStar
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < M * (f * w + 2) * k0 * Real.log 2 := by positivity
  rcases le_total 1 (Real.pi / (M * (f * w + 2) * k0 * Real.log 2)) with hq | hq
  · rw [min_eq_left hq, Real.log_one]; simp
  · rw [min_eq_right hq, Real.log_div Real.pi_pos.ne' hden.ne', Real.log_mul (by positivity) hl2.ne',
      Real.log_mul (by positivity) hk0.ne', Real.log_mul hM.ne' hfw.ne']
    have h1 : Real.log k0 ≤ Real.log 2 := Real.log_le_log hk0 hk0'
    have h2 : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos hl2.le (by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith)
    have h3 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have h4 := le_max_right 0 (Real.log M + Real.log (f * w + 2) + Real.log 2)
    linarith

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NonzeroDivisorOfConnected
section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem nonzero_divisor_of_connected : ReciprocityTheory.ChartRestriction.G.PullbackSections.NZDOfCompSt :=
  nzdOfComp_of_conn fun _ _ _ _ r X => (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RamifiedEigenLiftsGeneral
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB Pf.ERam

theorem dual_int {E : Type} [Field E] [NumberField E] (δ : 𝓞 E) (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) :
    ∀ i : Fin (nI E), IsIntegral ℤ ((δ : E) * omDF (E := E) i) := by
  set ω := RingOfIntegers.basis E
  set bq := integralBasis E
  have hbqω : ∀ i, bq i = algebraMap (𝓞 E) E (ω i) := fun i => integralBasis_apply E i
  have h := _root_.dual_difference E _ bq (fun i => by rw [hbqω]; exact RingOfIntegers.isIntegral_coe _) (fun x => by
      refine ⟨fun i => ω.repr x i, ?_⟩
      have h1 := congrArg (algebraMap (𝓞 E) E) (ω.sum_repr x)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h1
      show algebraMap (𝓞 E) E x = _
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbqω, map_zsmul, Int.cast_smul_eq_zsmul]) _ hδ
  intro i
  exact h _

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ThetaNuPf
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

theorem cast_cancel {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (k : ℕ) {L1 L2 : RigLB G}
    (e : L1 = L2) (θ : LB.Sec (LB.LinComb L2.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) :
    (e ▸ (e.symm ▸ θ : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))) = θ := by
  subst e; rfl

theorem thetaNu : ThetaNuSt := by
  intro E _ _ _ H V _ _ _ _ _ t P _ ϖ hϖ Q hQ vK hvK tK m w _ θ θK htie
  haveI := t.semi.smooth
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  let σ' : LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))) :=
    P.bundle.symm ▸ θ
  let s : P.U.SecK 1 := TG.secK P.U.toUnifPre σ'
  have hs := TG.secK_rel P.U.toUnifPre σ'
  obtain ⟨Ex, hEx, -⟩ := (P.U.expand 1 le_rfl).1 s
  have hnu := expansion_nonneg_regular V ϖ hϖ P.D Q hQ vK hvK P.A t.G P.U 1 rfl σ' s hs Ex hEx
  refine ⟨s, Ex, fun Z r zp hzp z J J' hJ hJ' => ?_, hEx, hnu⟩
  have hsc := secScal_cast (pullback.fst t.G.hom (Out.jK V)) 1 P.bundle s σ' hs
  have e1 := ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_sval hsc (r ≫ iotaK m) z hJ
  rw [Category.assoc, iotaK, pullback.lift_fst, cast_cancel 1 P.bundle θ] at e1
  exact e1.symm.trans (htie Z r zp hzp z J J' hJ hJ')

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TorusFrame
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma finrank_eq (D : Formalism.BasicNotions.D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f]
  have hn : D.R.n = D.R.ord := rfl
  rw [hn]
  ring


end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame
end
end

