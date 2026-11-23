module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstantTermAlongFlagEqZeroOfCuspidalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantTermAlongFlag_eq_zero_of_cuspidal : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), φ ∈ cuspCont V → ∀ 𝔉 : IsoFlag V, 𝔉.Proper → constTerm 𝔉 φ = 0 := by
  first | exact @GlobalTheory.Cusp.constTerm_eq_zero_of_mem_cuspCont | exact GlobalTheory.Cusp.constTerm_eq_zero_of_mem_cuspCont | (intros; apply GlobalTheory.Cusp.constTerm_eq_zero_of_mem_cuspCont <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DecompositionGroupMulEquivLocalGaloisCyclotomicStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decompositionGroup_mulEquiv_localGalois_cyclotomic : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] K) (e : Dec (F := F) A ≃* GK l K), Continuous e ∧ Continuous e.symm ∧ ∀ (r : ℕ) (g : Dec (F := F) A), cycK l K r (e g) = cycMod F Ω l r (g : G F Ω) := by
  first | exact @GlobalTheory.DecLocal.exists_mulEquiv_cyc | exact GlobalTheory.DecLocal.exists_mulEquiv_cyc | (intros; apply GlobalTheory.DecLocal.exists_mulEquiv_cyc <;> assumption)
end

