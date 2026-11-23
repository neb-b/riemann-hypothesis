module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingIdentity.FoldUnfoldMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ExistsDenomBackward
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.MinkowskiBoundOfSteps
public import Formalism.PeriodIntegrals.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiLowerBoundHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.Bundle0002
public import Formalism.PeriodIntegrals.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TraceDualLocal.Imports
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.TwNormLatMain
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.EqZeroOfMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.VanishInvertible
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
section
theorem lintegralTransversalSum : PI.FoldUnfold.FoldUnfold :=
  PI.FoldUnfold.UnitaryGroupMassFormula.foldUnfold_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.JetsPhW
section
theorem jets_high_generation : PI.JetsPhW.HighG :=
  PI.JetsPhW.W.highG_of PI.JetsPhW.W.derivative_chain_rule PI.JetsPhW.W.derivative_self
    PI.JetsPhW.W.pderiv_subst_ne PI.JetsPhW.W.pderiv_subst_self PI.JetsPhW.W.evaluation_at_zero
    PI.JetsPhW.W.jet_derivative_integrality PI.JetsPhW.W.log_derivative_integral_jet_integrality PI.JetsPhW.W.derivative_integral

theorem jets_phase_weights : PI.JetsPhW.Target :=
  PI.JetsPhW.W.glue_holds_var PI.JetsPhW.Inv.inverse_omega_holds jets_high_generation
    PI.JetsPhW.Low.firstJetIntegralGeneral_holds PI.JetsPhW.Low.secondJetIntegralGeneral_holds

theorem jets_high : PI.JetsPhW.High :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).1

theorem jets_one : PI.JetsPhW.One :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.1

theorem jets_two : PI.JetsPhW.Two :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.2
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerDetFin
section
theorem ordRelativeDet_finite : PI.KerIso.DetOrdFin := PI.KerDetFinW.detOrdFin
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LowSmooth
section
theorem low_smooth_of_k_finite : PI.KFinSmooth → PI.LowSmooth := PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski
section
theorem card_dvd_minkowskiNumber : PI.MinkowskiBound :=
  PI.Mk.minkowskiBound_of_steps PI.Mk.traceStep PI.Mk.powerSumStep
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeCount
section
theorem prime_count_bound : PI.PrimeCountBound :=
  PI.PC.primeCountBound_of 131072 (PI.PC.pcLarge_of PI.PC.psiUpperBound_holds) PI.PC.pcSmall
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
section
theorem ssAscent : PI.SSAscent :=
  PI.SSAscent.UnitaryGroupMassFormula.ssAscent_of
    (PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent)
    PI.SSAscent.UnitaryGroupMassFormula.traceFormNondegenerate_baseChange
    PI.SSAscent.UnitaryGroupMassFormula.semisimpleOfTraceFormNondegenerate
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TrDualLoc
section
theorem trace_dual_local : PI.TrDualLoc.Stmt := by
  intro K _ _ p _ Fp _ _ _ _ _ hc hfin ι hd _ t ht c hcO
  haveI : CharZero Fp :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp).injective
  exact PI.TrDualLocW.main hc hfin ι (PI.CntNotIntW.tensorLiftSurjective K _ Fp hc hfin ι hd) t ht c hcO
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwNormLat
section
theorem TwNormLat : PI.TwNormLat.TwNormLat := PI.TwNormLat.W.twNormLat_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitKron
section
theorem unit_kronecker : PI.UnitKron :=
  PI.UnitKronW.unitKron_of PI.UnitKronW.stepA PI.UnitKronW.stepB PI.UnitKronW.stepC
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDense
section
theorem productFramesDense_holds : PI.FramesDense := PI.UD.framesDense_of PI.UD.svdStep PI.UD.gramStep

theorem unitaryGroupDense_holds : PI.UnitaryDense := unitaryDense_of productFramesDense_holds
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfRing
section
private theorem exists_pow_mul_add_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a + b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a + b) = q ^ j * (q ^ i * a) + q ^ i * (q ^ j * b) := by ring
  rw [e]
  exact S.add_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)

private theorem exists_pow_mul_sub_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a - b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a - b) = q ^ j * (q ^ i * a) - q ^ i * (q ^ j * b) := by ring
  rw [e]
  exact S.sub_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)

private theorem exists_pow_mul_mul_mem_subring {R : Type*} [CommRing R] (S : Subring R) {q a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a * b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a * b) = (q ^ i * a) * (q ^ j * b) := by ring
  rw [e]
  exact S.mul_mem hi hj

private theorem exists_pow_mul_finset_sum_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {ι : Type*}
    (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, ∃ k : ℕ, q ^ k * f i ∈ S) :
    ∃ k : ℕ, q ^ k * ∑ i ∈ s, f i ∈ S := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => ⟨0, by simp⟩) ?_
  intro a s ha ih h
  rw [Finset.sum_insert ha]
  exact exists_pow_mul_add_mem_subring S q hq (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem witt_ring_structure : PI.WfRing := by
  classical
  intro p _ σ f g hf hg
  delta PI.CoefWf PI.InWf at hf hg ⊢
  have hq : (p : ℂ_[p]) ∈ PI.Wp p := natCast_mem (PI.Wp p) p
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_, fun c hc n => ?_⟩
  · rw [map_add (f := _)]
    exact exists_pow_mul_add_mem_subring _ _ hq (hf n) (hg n)
  · rw [map_sub]
    exact exists_pow_mul_sub_mem_subring _ _ hq (hf n) (hg n)
  · rw [MvPowerSeries.coeff_mul]
    exact exists_pow_mul_finset_sum_mem_subring _ _ hq _ _ fun x _ => exists_pow_mul_mul_mem_subring _ (hf x.1) (hg x.2)
  · rw [MvPowerSeries.coeff_C_mul]
    exact exists_pow_mul_mul_mem_subring _ hc (hf n)
end

