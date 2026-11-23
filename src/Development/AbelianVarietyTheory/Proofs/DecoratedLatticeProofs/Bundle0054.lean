module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
public import Formalism.HarderNarasimhan.Statement
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCongruenceIffFlagConditions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChebotarevDegreeOneValuationSubrings
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem chebOmSt_holds : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  intro E Ω _ _ _ _ _ S hS H hn ho _ σ
  obtain ⟨v, hv, hd, -, B, hB, -, φ, hφ, hφσ⟩ := GlobalTheory.Published.cheb_holds E Ω H ho hn σ hS.toFinset
  refine ⟨B, v, φ, ?_, by simpa using hv, ?_, ?_, ?_⟩
  · intro x
    rw [ValuationSubring.mem_nonunits_iff]
    exact hB x
  · have := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  · refine ⟨hφ.1, fun x hx => ?_⟩
    rw [ValuationSubring.mem_nonunits_iff]
    exact hφ.2 x ((B.valuation_le_one_iff x).2 hx)
  · have := hn.conj_mem _ hφσ σ⁻¹
    simpa [mul_assoc] using this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem exists_isConjAt_of_embedding (K : Type) [Field K] [NumberField K] [StarRing K]
    (h : ∃ σ : K →+* ℂ, ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) :
    ∃ v0 : InfinitePlace K, IsConjAt v0 := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨InfinitePlace.mk σ, fun a => ?_⟩
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e]; exact hσ a
  · rw [e]
    simp only [ComplexEmbedding.conjugate_coe_eq]
    rw [hσ a]

theorem isConjAt_exists_main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    (∃ σ : K →+* ℂ, ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) →
      ∃ v0 : InfinitePlace K, IsConjAt v0 :=
  fun K _ _ _ h => exists_isConjAt_of_embedding K h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagBasisLiftGramSignedPermutationStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftFrame_gram_congr_flagGram : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → ZMod' I g (1 - ew - sigA I ew) ∧ (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) := by
  first | exact @GlobalTheory.FlagBasis.GramLift.gramIn_lift | exact GlobalTheory.FlagBasis.GramLift.gramIn_lift | (intros; apply GlobalTheory.FlagBasis.GramLift.gramIn_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCongruenceIffFlagConditionsStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCongruence_iff_flag_conditions : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → ∀ x : I.Gf, (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β → (K2cong I g e0 z0 bw x ↔ FlagCond (ZMod' I g) ρ k ew (matIn I β x)) := by
  first | exact @GlobalTheory.FlagBasis.Cong.k2cong_iff_flagCond | exact GlobalTheory.FlagBasis.Cong.k2cong_iff_flagCond | (intros; apply GlobalTheory.FlagBasis.Cong.k2cong_iff_flagCond <;> assumption)
end

