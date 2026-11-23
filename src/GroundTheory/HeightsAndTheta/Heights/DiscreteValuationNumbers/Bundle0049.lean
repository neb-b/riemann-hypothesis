module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

def homLocRing (P W : Ideal (MRing ι R)) [P.IsPrime] : Subring (FractionRing (MRing ι R ⧸ P)) :=
  Subring.closure {z | ∃ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧
    z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g)}

end Objects

section Lemmas

def HomLocRingLocal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (hP : IsMultiProjPrime P) (c : K → ℕ) (x : MRing ι O),
    IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.isPrime
      IsLocalRing (homLocRing P W) ∧ IsNoetherianRing (homLocRing P W) ∧
        ringKrullDim (homLocRing P W) = 1

def DivCycleHomLoc.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (hP : IsMultiProjPrime P) (c : K → ℕ) (x : MRing ι O),
    IsMultiHomog x c → x ∉ P →
    ∀ (W : Ideal (MRing ι O)) (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes), IsRelevant W →
    ∀ g : MRing ι O, IsMultiHomog g c → g ∉ W →
      haveI := hP.isPrime
      ∀ hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
            homLocRing P W,
      haveI : W.IsPrime := hW.1.1
      multAt (P ⊔ Ideal.span {x}) W =
        Module.length (homLocRing P W) (homLocRing P W ⧸ Ideal.span {(⟨_, hz⟩ : homLocRing P W)})

def FiniteBirationalLength.Statement : Prop :=
  ∀ (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [Module.Finite A B], ringKrullDim A = 1 →
    Function.Injective (algebraMap A B) → Module.finrank A B = 1 → ∀ z : A, z ≠ 0 →
      Finite {𝔫 : Ideal B // 𝔫.IsMaximal} ∧
      Module.length A (A ⧸ Ideal.span {z}) =
        ∑ᶠ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
          (haveI := 𝔫.2.isPrime
           Module.length (Localization.AtPrime 𝔫.1)
             (Localization.AtPrime 𝔫.1 ⧸
               Ideal.span {algebraMap B (Localization.AtPrime 𝔫.1) (algebraMap A B z)})) *
            (𝔫.1.inertiaDeg A : ℕ∞)

def BlowUpFibreSemilocal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
    ∀ g : MRing ι O, IsMultiHomog g c → g ∉ W →
      haveI := hP.multiProj.isPrime
      ∀ hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
            homLocRing P W,
      ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (homLocRing P W) B),
        Module.Finite (homLocRing P W) B ∧ Function.Injective (algebraMap (homLocRing P W) B) ∧
        Module.finrank (homLocRing P W) B = 1 ∧
        ∃ e : {𝔫 : Ideal B // 𝔫.IsMaximal} ≃ {W' : Ideal (MRing (extIdx ι J) O) //
            W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
              W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W},
          ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
            (haveI := 𝔫.2.isPrime
             Module.length (Localization.AtPrime 𝔫.1)
               (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {(algebraMap B (Localization.AtPrime 𝔫.1)
                 (algebraMap (homLocRing P W) B ⟨_, hz⟩))})) =
              ((divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1).toNat : ℕ∞) ∧
            𝔫.1.inertiaDeg (homLocRing P W) = specialRelDeg (e 𝔫).1

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {Ω : Type*} [Field Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
  [Algebra Ω Φ]

def flagLineCoord (b w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (k : ℕ) (i : Fin N) : Φ :=
  ∑ j, flagCoord w e t k j * algebraMap Ω Φ (b.repr (w j) i)

end Objects


open Classical in
def SegreFlagCutSection.Statement : Prop :=
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
    ∀ (k : ℕ) (hk : k < N) (r : ℕ) (a : Fin r → MRing ι O), (∀ j, a j ∉ pointIdeal O y) →
      ∃ (cs ch : Option (Option K) → ℕ) (s h f₃ g₃ : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs ∧ IsMultiHomog h ch ∧
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) ∧
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ∧ h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h ∧
        (∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W →
          ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W =
            if 0 < k ∧ W = pointIdeal O (flagClosurePt y w e φ φ' t k) then 1 else 0) ∧
        IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) ϖ (zetaFirst a₀ - zetaSecond a₀') f₃ g₃ ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) f₃ = aeval (flagClosurePt y w e φ φ' t (k + 1)) g₃ ∧
        (0 < k → f₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧
          g₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧
          aeval (flagClosurePt y w e φ φ' t k) f₃ = aeval (flagClosurePt y w e φ φ' t k) g₃) ∧
        ∀ H, (divCycle (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s H ≠ 0 ∨ divCycle (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) h H ≠ 0) →
          (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ H →
          f₃ ∉ H ∧ g₃ ∉ H ∧ ∀ j, liftPairForm M M' (a j) ∉ H

def SegreFlagCutContraction.Statement : Prop :=
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
    ∀ (k : ℕ) (hk : k < N),
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaFirst a₀ + liftPairDeg (x ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        ∀ l : List (Option (Option K) → ℤ), l.length = d + k → (∀ b ∈ l, b none = 0) → vNumL W l = 0) ∧
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        ∀ l : List (Option (Option K) → ℤ), l.length = d + k → (∀ b ∈ l, b (some none) = 0) → vNumL W l = 0)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

