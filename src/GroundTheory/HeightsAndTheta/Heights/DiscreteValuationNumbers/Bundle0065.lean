module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutLiesOver
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxPointCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocMaxCentre.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ (𝔫 : Ideal (blowUpOverLoc P W u)) (h𝔫 : 𝔫.IsMaximal),
        ∃ W' : Ideal (MRing (extIdx ι J) O),
          W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W ∧
          ∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u W',
            letI := (Subring.inclusion h).toAlgebra
            haveI := h𝔫.isPrime
            IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫

def BlowUpOverLocFibreMinimal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
    ∀ W' : Ideal (MRing (extIdx ι J) O), W'.IsPrime → IsMultiHomogIdeal W' → IsRelevant W' →
      blowUpOf P u ≤ W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes

def BlowUpOverLocPointDeg.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔫 : Ideal (blowUpOverLoc P W u))
          (h𝔫 : 𝔫.IsMaximal),
          (letI := (Subring.inclusion h).toAlgebra
           haveI := h𝔫.isPrime
           IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫) ∧
          𝔫.inertiaDeg (homLocRing P W) = specialRelDeg W'

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChartSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutChartSection.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N) (c : ∀ k, ι k), segreVec y c ≠ 0 →
      (∃ (dl dm : Option (Option K) → ℕ) (l μ : MRing (bundleIdx (bundleIdx ι M) M') O) (m : K → ℕ),
        μ = ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ^ m j ∧
        IsMultiHomog l dl ∧ IsMultiHomog μ dm ∧
        (fun o => (dl o : ℤ) - dm o) = zetaFirst a₀ + liftPairDeg (x ⟨k, hk⟩) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) l =
          flagLineCoord w w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) μ ∧
        ∀ q ∈ pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k), ∃ n : ℕ,
          (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ n *
              rename (FieldNumbers.blockIncl Function.Embedding.some (bundleIdx (bundleIdx ι M) M')) q ∈
            pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l}) ∧
      (∃ (dl dm : Option (Option K) → ℕ) (l μ : MRing (bundleIdx (bundleIdx ι M) M') O) (m : K → ℕ),
        μ = ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ^ m j ∧
        IsMultiHomog l dl ∧ IsMultiHomog μ dm ∧
        (fun o => (dl o : ℤ) - dm o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) l =
          flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) μ ∧
        ∀ q ∈ pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k), ∃ n : ℕ,
          (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ n *
              rename (FieldNumbers.blockIncl secondFactorBlocks (bundleIdx (bundleIdx ι M) M')) q ∈
            pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l})

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagProjSpecialDimSteps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PrimeDimLeTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    P.IsPrime → P.comap (C : O →+* MRing ι O) = ⊥ →
      ringKrullDim (MRing ι O ⧸ P) ≤ (((Algebra.trdeg O (MRing ι O ⧸ P)).toENat + 1 : ℕ∞) : WithBot ℕ∞)

def FlagProjTrdegLe.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, k < N →
      Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (Function.Embedding.some o)) O ⧸
          pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k)) ≤
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal) ∧
      Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (secondFactorBlocks o)) O ⧸
          pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k)) ≤
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

