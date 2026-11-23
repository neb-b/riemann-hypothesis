module

public import Formalism.GaussJetBounds.StatementP
public import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound
public import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
public import Formalism.GaussJetBounds.GaussJetProofs.Bundle0002
public import Formalism.GaussJetBounds.GaussJetProofs.Bundle0001
public import Formalism.GaussJetBounds.GaussJetProofs.PureCrossTermWeight
public import Formalism.GaussJetBounds.GaussJetProofs.Bundle0003
public import Formalism.GaussJetBounds.GaussJetProofs.SwappedParitySeriesBinomialForm
public import Formalism.GaussJetBounds.GaussJetProofs.ExistsNeZeroOfFinsumNeZero
public import Formalism.GaussJetBounds.GaussJetProofs.AsmOne

@[expose] public section

-- bundled from Formalism.GaussJetBounds.FrameJetEval
section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def TransferB : Prop :=
  ∀ (F K : Type) [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K),
    (∀ z, ‖φ z‖ = ‖z‖) →
    ∀ (l d N0 N1 : ℕ) [NeZero d] (K0 : Subfield F) (ζ : F) (be : MvPowerSeries (ZMod d) F),
      (Unram l K0 → Unram l (K0.map φ)) ∧
      (BHyp l d K0 ζ be → BHyp l d (K0.map φ) (φ ζ) (MvPowerSeries.map φ be)) ∧
      (∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) F,
        (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
        (∀ y, MvPowerSeries.subst g (entLog (K := F) l y) = MvPowerSeries.X y) →
        (∀ y, MvPowerSeries.constantCoeff (MvPowerSeries.map φ (g y)) = 0) ∧
        ∀ y, MvPowerSeries.subst (fun y' => MvPowerSeries.map φ (g y')) (entLog (K := K) l y) =
          MvPowerSeries.X y) ∧
      (∀ U : MvPowerSeries (ZV d N0 N1) F, Integral U → Integral (MvPowerSeries.map φ U))

def FrameJetEval : Prop :=
  ∀ (F K : Type) [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
    (d N0 N1 : ℕ) [NeZero d] (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) F)
    (U : MvPowerSeries (ZV d N0 N1) F) (ε : F) (be : MvPowerSeries (ZMod d) F),
    (∀ y, MvPowerSeries.constantCoeff (g y) = 0) → MvPowerSeries.constantCoeff be = 0 →
    ∀ (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0)
      (I : ∀ s c, Fin (p s c) → Fin N1) (x : ZMod d × Fin N0 × Fin N0 → K),
      MvPolynomial.eval₂ φ x (frameJet colN p hp I (thetaZ g U ε be)) =
        jetPair (∏ s : ZMod d, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K))
            (p s) (hp s) (I s))
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) x))
              (MvPowerSeries.subst (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U)) *
            mvExp (φ ε • bSum (frameM (N1 := N1) x) (MvPowerSeries.map φ be)))

def LabelsExist : Prop :=
  ∀ (l d N0 : ℕ) [NeZero d], 2 ≤ l → ∀ (TT : Finset (ZMod d)) (nu1 size : ZMod d → ℕ) (a : ℕ),
    1 ≤ a → (∀ s, nu1 s ≤ a) → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∃ (J : ZMod d → ℕ) (lab : ∀ s, Fin (J s) → ZMod d × ℤ) (m : ℕ),
      (∀ s, Function.Injective (lab s)) ∧
      (∀ (s s0 : ZMod d) (j : ℤ), (∃ i, lab s i = (s0, j)) ↔
        (s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
          (j < 0 → l ^ (-j).toNat ≤ size s))) ∧
      (∀ s, J s + (if s ∈ TT then 1 else 0) ≤ N0) ∧ (∀ s i, (-(lab s i).2).toNat ≤ m)

def GaussPow : Prop :=
  ∀ (F K : Type) [NormedField F] [NormedField K] (φ : F →+* K) (σ : Type) (Y : σ → K),
    (∀ P : MvPolynomial σ F, ‖MvPolynomial.eval₂ φ Y P‖ = ⨆ n : σ →₀ ℕ, ‖AddMonoidAlgebra.coeff P n‖) →
    ∀ (k : σ → ℕ), (∀ y, k y ≠ 0) → ∀ (P : MvPolynomial σ F) (n : σ →₀ ℕ),
      ‖AddMonoidAlgebra.coeff P n‖ ≤ ‖MvPolynomial.eval₂ φ (fun y => Y y ^ k y) P‖

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.OneLetterRadius
section
universe u v

namespace Formalism.DworkPowerSeriesWeights

theorem lemmaS : LemmaS.{u} :=
  lemmaS_of generalized_log_weight generalized_log_inverse logarithm_weight_comparison substitution_weight_bound exponential_derivative_inverse
    weightQuantization logarithm_weight_induction binomial_coefficient_extraction

theorem oneLetterR : OneLetterR.{u, v} :=
  oneLetterR_of lemmaS generalized_log_weight logarithm_weight_comparison substitution_weight_bound substitution_weight_bound radical_weight_monotone
    multiplicative_weight_le exponential_weight_le factorial_valuation_bound oneLetterRadiusIdentity

end Formalism.DworkPowerSeriesWeights
end

-- bundled from Formalism.GaussJetBounds.StatementS
section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def unitBall (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

def xMinors {K : Type} [Field K] {d N0 : ℕ} [NeZero d] (colN : ZMod d → ℕ)
    (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) :
    Set (MvPolynomial (ZMod d × Fin N0 × Fin N0) K) :=
  {P | ∃ A : ∀ s c, Fin (p s c) → Fin N0, P = ∏ s : ZMod d, minorProd
    (fun (i a : Fin N0) => (MvPolynomial.X (s, i, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) K))
    (p s) (hp s) (A s)}

def nablaO {K : Type} [NormedField K] [IsUltrametricDist K] {d N0 : ℕ} [NeZero d]
    (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) :
    Submodule (unitBall K) (MvPolynomial (ZMod d × Fin N0 × Fin N0) K) :=
  Submodule.span (unitBall K) (xMinors colN p hp)

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.StatementU
section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def thetaOne {K : Type} [NormedField K] [CharZero K] {N0 N1 : ℕ}
    (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K)
    (U : MvPowerSeries (Fin N0 × Fin N1) K) (sgn ep : K) (be : MvPowerSeries (ZMod 2) K) :
    MvPowerSeries (Fin N0 × Fin N1) K :=
  MvPowerSeries.subst g U * mvExp ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
    (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
      (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) K)) be)

def frameJetOne {K : Type} [Field K] {N0 N1 C : ℕ} (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) (Th : MvPowerSeries (Fin N0 × Fin N1) K) :
    MvPolynomial (Fin N0 × Fin N0) K :=
  jetPairPoly (minorProd
    (fun (i : Fin N0) (b : Fin N1) =>
      (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (i, a)) * MvPolynomial.X (a, b) :
        MvPolynomial (Fin N0 × Fin N1) (MvPolynomial (Fin N0 × Fin N0) K))) p hp I) Th

def OneLetterGauss : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N0 N1 C : ℕ), 3 ≤ l →
    ∀ (K0 : Subfield ℂ_[l]), Unram l K0 → ∀ ζ : ℂ_[l], IsPrimitiveRoot ζ (l ^ 2 - 1) →
    ∀ be : MvPowerSeries (ZMod 2) ℂ_[l], BHyp l 2 K0 ζ be → ∀ ep : ℂ_[l], ‖ep‖ = 1 →
    ∀ g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) ℂ_[l],
      (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
      (∀ y, MvPowerSeries.subst g (oneLog (K := ℂ_[l]) l y) = MvPowerSeries.X y) →
    ∀ U : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l], Integral U →
    ∀ (sgn : ℂ_[l]), (sgn = 1 ∨ sgn = -1) →
    ∀ (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) (a : ℕ), 1 ≤ a →
      (∑ c, p c) ≤ a → ∀ n : (Fin N0 × Fin N0) →₀ ℕ,
      ‖AddMonoidAlgebra.coeff (frameJetOne p hp I (thetaOne g U sgn ep be)) n‖ ≤
        ‖(l : ℂ_[l])‖ ^ (rho l * ((∑ c, p c : ℕ) : ℝ) -
          ((N0 : ℝ) * N1) * (Real.logb l (a : ℝ) + 1))

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.StatementW
section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

def serAlong {K : Type} [Field K] {ι κ : Type} (e : ι → κ) (f : MvPowerSeries ι K) :
    MvPowerSeries κ K :=
  MvPowerSeries.subst (fun i => (MvPowerSeries.X (e i) : MvPowerSeries κ K)) f

def opAlong {K : Type} [Field K] {ι κ σ τ : Type} (e : ι → κ) (e' : σ → τ)
    (P : MvPolynomial ι (MvPolynomial σ K)) : MvPolynomial κ (MvPolynomial τ K) :=
  MvPolynomial.rename e (MvPolynomial.map (MvPolynomial.rename e' : MvPolynomial σ K →ₐ[K]
    MvPolynomial τ K).toRingHom P)

end Formalism.DworkPowerSeriesWeights
end
end

