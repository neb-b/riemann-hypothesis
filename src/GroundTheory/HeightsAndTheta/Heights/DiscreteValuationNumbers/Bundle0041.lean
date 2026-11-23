module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0032

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOrderLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def LocalizedQuotLength.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (P : Ideal S) (W₀ : Ideal (S ⧸ P)) [W₀.IsPrime] (z : S),
    Module.length (Localization.AtPrime (W₀.comap (Ideal.Quotient.mk P)))
        (LocalizedModule (W₀.comap (Ideal.Quotient.mk P)).primeCompl (S ⧸ (P ⊔ Ideal.span {z}))) =
      Module.length (Localization.AtPrime W₀)
        (Localization.AtPrime W₀ ⧸
          Ideal.span {algebraMap (S ⧸ P) (Localization.AtPrime W₀) (Ideal.Quotient.mk P z)})

def LengthMapIdealLe.Statement : Prop :=
  ∀ (C D : Type u) [CommRing C] [CommRing D] [IsLocalRing D] (φ : C →+* D),
    (∀ m : Ideal C, m.IsMaximal → m.map φ = ⊤ ∨ IsLocalRing.maximalIdeal D ≤ m.map φ) →
    ∀ I : Ideal C, Module.length D (D ⧸ I.map φ) ≤ Module.length C (C ⧸ I)

def IntermediateRingQuotLength.Statement : Prop :=
  ∀ (A C : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing C] [IsDomain C]
    [Algebra A C], ringKrullDim A = 1 → Function.Injective (algebraMap A C) →
    (∀ c : C, ∃ a : A, a ≠ 0 ∧ a • c ∈ Set.range (algebraMap A C)) →
    ∀ a : A, a ≠ 0 →
      Module.length A (C ⧸ Ideal.span {algebraMap A C a}) ≤ Module.length A (A ⧸ Ideal.span {a})

def BlowUpLocalChart.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (P : Ideal (MRing ι R)), P.IsPrime →
    ∀ (u : J → MRing ι R) (G' : Ideal (MRing (extIdx ι J) R)) (y : MRing (extIdx ι J) R),
      y ∉ blowUpOf P u → G' ∈ (blowUpOf P u ⊔ Ideal.span {y}).minimalPrimes → IsRelevant G' →
    ∀ x : MRing ι R, x ∉ P → G'.comap (liftForm (J := J)) ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
    ∀ (G₀ : Ideal (MRing ι R ⧸ P)) [G₀.IsPrime],
      G₀.comap (Ideal.Quotient.mk P) = G'.comap (liftForm (J := J)) →
    ∀ (W₀ : Ideal (MRing (extIdx ι J) R ⧸ blowUpOf P u)) [W₀.IsPrime],
      W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = G' →
    ∃ (C : Subring (Localization.AtPrime W₀)) (f : Localization.AtPrime G₀ →+* C),
      Function.Injective f ∧ (∀ c : C, ∃ a, a ≠ 0 ∧ f a * c ∈ Set.range f) ∧
      (∀ s : MRing ι R,
        (f (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀) (Ideal.Quotient.mk P s)) :
            Localization.AtPrime W₀) =
          algebraMap (MRing (extIdx ι J) R ⧸ blowUpOf P u) (Localization.AtPrime W₀)
            (Ideal.Quotient.mk (blowUpOf P u) (liftForm s))) ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime W₀) ≤
        ((IsLocalRing.maximalIdeal (Localization.AtPrime W₀)).comap C.subtype).map C.subtype

end Lemmas

section Examples

theorem BlowUpLocalChart.exists_quotient_primes {R : Type*} [CommRing R] {K : Type*} {ι : K → Type}
    {J : Type} {P : Ideal (MRing ι R)} {u : J → MRing ι R} {G' : Ideal (MRing (extIdx ι J) R)}
    (hG' : G'.IsPrime) (hQ : blowUpOf P u ≤ G') (hP : P ≤ G'.comap (liftForm (J := J))) :
    ∃ (G₀ : Ideal (MRing ι R ⧸ P)) (W₀ : Ideal (MRing (extIdx ι J) R ⧸ blowUpOf P u)),
      G₀.IsPrime ∧ W₀.IsPrime ∧ G₀.comap (Ideal.Quotient.mk P) = G'.comap (liftForm (J := J)) ∧
        W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = G' := by
  refine ⟨(G'.comap (liftForm (J := J))).map (Ideal.Quotient.mk P), G'.map (Ideal.Quotient.mk _),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]),
    Ideal.comap_map_mk hP, Ideal.comap_map_mk hQ⟩

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

universe u

section Lemmas

def LocCycleSpanMul.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (x y : A), x ≠ 0 → y ≠ 0 →
    ∀ W : Ideal A, locCycle (Ideal.span {x * y}) W =
      locCycle (Ideal.span {x}) W + locCycle (Ideal.span {y}) W

def LocCyclePos.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (J W : Ideal R), W ∈ J.minimalPrimes →
    0 < locCycle J W

def MinimalPrimesSpanSingleton.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (x : A), x ≠ 0 →
    ∀ W : Ideal A, W ∈ (Ideal.span {x}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ x ∈ W

def LocalDomainDimTwo.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    (∀ Q₁ Q₂ : Ideal A, Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ → Q₂ < IsLocalRing.maximalIdeal A →
      False) →
    (∃ Q : Ideal A, Q.IsPrime ∧ ⊥ < Q ∧ Q < IsLocalRing.maximalIdeal A) →
    ringKrullDim A = 2 ∧ (IsLocalRing.maximalIdeal A).height = 2 ∧
      ∀ Q : Ideal A, Q.IsPrime → ⊥ < Q → Q < IsLocalRing.maximalIdeal A → Q.height = 1

def DimTwoSumReading.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    ringKrullDim A = 2 → ∀ a b : A, a ≠ 0 →
    (∀ p : Ideal A, p.IsPrime → p.height = 1 → a ∈ p → b ∉ p) →
    ∃ n : ℕ, ∑ᶠ W : Ideal A, locCycle (Ideal.span {a}) W *
        locCycle (W ⊔ Ideal.span {b}) (IsLocalRing.maximalIdeal A) = n ∧
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal), ordLoc p a * ordMod p b = n

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def flagCoord (w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (k : ℕ) : Fin N → Φ :=
  fun j => if (j : ℕ) < k then ∑ i, t i * algebraMap Ω Φ (w.repr (e i) j) else 0

def flagClosurePt (y : (Σ k, ι k) → Ω) (w e : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (k : ℕ) :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ :=
  pairProjCoord y w φ φ' (flagCoord w e t k)

end Objects

def closureDeg {K : Type*} {m : ℕ} (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    Fin (1 + m) → Option (Option K) → ℤ :=
  Fin.append (fun _ : Fin 1 => ζ) (fun j => liftPairDeg (L j))

def closureForm {K : Type*} {ι : K → Type} {R : Type*} [CommRing R] {m : ℕ} (M M' : ℕ)
    (h : MRing (bundleIdx (bundleIdx ι M) M') R) (F : Fin m → MRing ι R) :
    Fin (1 + m) → MRing (bundleIdx (bundleIdx ι M) M') R :=
  Fin.append (fun _ : Fin 1 => h) (fun j => liftPairForm M M' (F j))

def SegreFlagClosureModel.Statement : Prop :=
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
    ∀ k : ℕ, 1 ≤ k → k ≤ N →
      IsModelOver (pointIdeal O (flagClosurePt y w e φ φ' t k)) (d + (k - 1)) ∧
      ∃ f₀ g₀ : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t k)) ϖ
          (zetaFirst a₀ - zetaSecond a₀') f₀ g₀ ∧
        aeval (flagClosurePt y w e φ φ' t k) f₀ = aeval (flagClosurePt y w e φ φ' t k) g₀

def SegreFlagClosureCut.Statement : Prop :=
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
    ∀ (k : ℕ) (hk : k < N) (f₁ g₁ f₂ g₂ : MRing (bundleIdx (bundleIdx ι M) M') O),
      IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) ϖ
        (zetaFirst a₀ - zetaSecond a₀') f₁ g₁ →
      aeval (flagClosurePt y w e φ φ' t (k + 1)) f₁ = aeval (flagClosurePt y w e φ φ' t (k + 1)) g₁ →
      (0 < k → IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t k)) ϖ
          (zetaFirst a₀ - zetaSecond a₀') f₂ g₂ ∧
        aeval (flagClosurePt y w e φ φ' t k) f₂ = aeval (flagClosurePt y w e φ φ' t k) g₂) →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (fz gz : Fin n → MRing ι O),
      (∀ j, IsVerticalDivisor (pointIdeal O y) ϖ (z j - z' j) (fz j) (gz j)) →
    ∀ (m : ℕ) (A : MvPolynomial (Fin (1 + (N + n))) ℤ), A.IsHomogeneous m →
    ∀ As Bs : Fin (1 + (N + n)) → MvPolynomial (Fin (1 + (N + n)) ⊕ Fin (1 + (N + n))) ℤ,
      IsPairExpansion (m + 1)
        ((X (Fin.castAdd (N + n) (0 : Fin 1)) + X (Fin.natAdd 1 (Fin.castAdd n ⟨k, hk⟩))) * A) As →
      IsPairExpansion m A Bs →
    ∀ Q : List (K → ℤ), Q.length + (m + 1) = d + k + 1 →
      pairNum (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)))
          (closureDeg (zetaFirst a₀) (Fin.append x z)) (closureDeg (zetaSecond a₀') (Fin.append x' z'))
          (closureForm M M' f₁ (Fin.append f fz)) (closureForm M M' g₁ (Fin.append g gz)) As
          (Q.map liftPairDeg) =
        if k = 0 then 0 else
          pairNum (pointIdeal O (flagClosurePt y w e φ φ' t k))
            (closureDeg (zetaFirst a₀) (Fin.append x z)) (closureDeg (zetaSecond a₀') (Fin.append x' z'))
            (closureForm M M' f₂ (Fin.append f fz)) (closureForm M M' g₂ (Fin.append g gz)) Bs
            (Q.map liftPairDeg)

def SegreFlagClosurePullback.Statement : Prop :=
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
    ∀ (k : ℕ), 1 ≤ k → k ≤ N → ∀ f₁ g₁ : MRing (bundleIdx (bundleIdx ι M) M') O,
      IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t k)) ϖ
        (zetaFirst a₀ - zetaSecond a₀') f₁ g₁ →
      aeval (flagClosurePt y w e φ φ' t k) f₁ = aeval (flagClosurePt y w e φ φ' t k) g₁ →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (fz gz : Fin n → MRing ι O),
      (∀ j, IsVerticalDivisor (pointIdeal O y) ϖ (z j - z' j) (fz j) (gz j)) →
    ∀ (r : ℕ) (Bf : MvPolynomial (Fin (N + n)) ℤ), Bf.IsHomogeneous r →
    ∀ (As : Fin (1 + (N + n)) → MvPolynomial (Fin (1 + (N + n)) ⊕ Fin (1 + (N + n))) ℤ)
      (Bs : Fin (N + n) → MvPolynomial (Fin (N + n) ⊕ Fin (N + n)) ℤ),
      IsPairExpansion r (rename (Fin.natAdd 1) Bf) As → IsPairExpansion r Bf Bs →
    ∀ Q : List (K → ℤ), Q.length + r = d + k →
      pairNum (pointIdeal O (flagClosurePt y w e φ φ' t k))
          (closureDeg (zetaFirst a₀) (Fin.append x z)) (closureDeg (zetaSecond a₀') (Fin.append x' z'))
          (closureForm M M' f₁ (Fin.append f fz)) (closureForm M M' g₁ (Fin.append g gz)) As
          (Q.map liftPairDeg) =
        if k = 1 then
          pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
            (Fin.append g gz) Bs Q
        else 0

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTwistedDualGensExpress
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensExpress.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (ϖ : R) (Ω : Type) [Field Ω] [Algebra R Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle R (segreVec y) N E),
    SameGenericFibre ϖ B B' →
    ∀ (a a' : K → ℤ) (M M' : ℕ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a φ → IsTwistedDualGens y B' a' φ' →
    ∀ c, segreVec y c ≠ 0 → ∀ m, ∃ (n : ℕ) (r : Fin M → Ω),
      (∀ l, r l ∈ chartRing R (segreVec y) c) ∧
      algebraMap R Ω ϖ ^ n • φ' m = ∑ l, (r l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k)) • φ l

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

