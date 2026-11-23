module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPlace
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0016

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveResidueDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def CurveResidueDegree.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation I q),
        Module.length (curveLocalRing I q) (curveNormalisation I q ⧸ P.asIdeal) = 1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermProjectionFunctionForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def GermProjectionFunctionForm.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    (∀ i, AnalyticAt ℂ (p i) w) → IsFiniteGermProjection w (holGermIdeal w p) A →
      (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → IsGermCombination w p (fun z => h (A z)) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) ∧
      (∀ i : σ, ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        IsGermCombination w p (fun z => z i ^ n + ∑ j, b j (A z) * z i ^ (j : ℕ))) ∧
      (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
        ∃ (s : Finset (σ → ℕ)) (a : (σ → ℕ) → (Fin d → ℂ) → ℂ), (∀ m ∈ s, AnalyticAt ℂ (a m) (A w)) ∧
          IsGermCombination w p (fun z => g z - ∑ m ∈ s, a m (A z) * ∏ i, z i ^ m i))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StJacobianRankOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def JacobianRankOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ)) (d r : ℕ) (q : Fin r → MvPolynomial σ ℂ)
    (t : MvPolynomial σ ℂ), Q.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (d : ℕ) →
    (∀ j, q j ∈ Q) → t ∉ Q → (∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q)) →
      ∃ μ : MvPolynomial σ ℂ, μ ∉ Q ∧ ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q, eval w μ ≠ 0 →
        Module.finrank ℂ (Submodule.span ℂ (Set.range fun j s ↦ eval w (pderiv s (q j)))) + d =
          Fintype.card σ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthTransverseSlice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def LengthTransverseSlice.Statement : Prop :=
  ∀ (n d : ℕ) (I W : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (L : Matrix (Fin d) (Fin n) ℂ),
    W ∈ I.minimalPrimes → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → q ∈ zeroSet W →
    (∀ W' ∈ I.minimalPrimes, q ∈ zeroSet W' → W' = W) → IsCohenMacaulayAt I q →
    IsTransverseSliceAt W L q →
      localMult I W = localMult (sliceIdeal I L q) (RingHom.ker (eval q))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def LocalDimDomain.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (e : ℕ) → ∀ q ∈ zeroSet J,
      ringKrullDim (localRingAt J q) = (e : ℕ)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMinimalPrimePlace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def MinimalPrimePlace.Statement : Prop :=
  ∀ (n : ℕ) (I J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → J ∈ I.minimalPrimes → J ≤ RingHom.ker (eval q) →
    ∀ P' : MaximalSpectrum (curveNormalisation J q), ∃ P : MaximalSpectrum (curveNormalisation I q),
      ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
        Ring.ord (Localization.AtPrime P'.asIdeal)
          (algebraMap (curveNormalisation J q) (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveLocalRing J q) (curveNormalisation J q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCodimOneUniformiser
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCodimOneUniformiser.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P Q : Ideal (MvPolynomial σ ℂ)) (e : ℕ) (x : MvPolynomial σ ℂ),
    P.IsPrime → Q.IsPrime → P ≤ Q → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ P) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ P) = (e + 1 : ℕ) → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (e : ℕ) →
    x ∈ Q → x ∉ P →
      ∃ (g a b t : MvPolynomial σ ℂ) (k : ℕ), g ∈ Q ∧ 0 < k ∧ a ∉ Q ∧ b ∉ Q ∧ t ∉ Q ∧
        b * x - a * g ^ k ∈ P ∧ ∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ P ⊔ Ideal.span {g}

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveBranchOrder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCurveBranchOrder.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ) (r : ℝ) (φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → 0 < r →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) → φ 0 = w →
      ∀ g : MvPolynomial (Fin n ⊕ Fin M.m) ℂ,
        Ring.ord (pointLocalRing M.ideal w)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) g) =
          analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurvePointDVR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCurvePointDVR.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
      ∃ _ : IsDomain (pointLocalRing I w), IsDiscreteValuationRing (pointLocalRing I w)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelOpenMapping
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

def NormalModelOpenMapping.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : NormalModel J) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) →
    IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn M.ideal) →
    ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ φ '' U = zeroSetIn M.ideal ∩ O

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalisationModelLocalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (q : Fin n → ℂ) : Submonoid (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :=
  (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl.map
    ((Ideal.Quotient.mk M.ideal).comp
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom)

theorem mk_rename_mem_normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (hf : eval q f ≠ 0) :
    Ideal.Quotient.mk M.ideal (rename Sum.inl f) ∈ normalModelSubmonoid M q :=
  Submonoid.mem_map_of_mem _ (show f ∈ (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl from
    fun h ↦ hf (RingHom.mem_ker.1 h))

theorem zero_not_mem_normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (q : Fin n → ℂ) (hq : q ∈ zeroSet J) :
    (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∉ normalModelSubmonoid M q := by
  rintro ⟨f, hf, h0⟩
  apply hf
  refine RingHom.mem_ker.2 (hq f ?_)
  rw [← M.comap_eq, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  exact h0

def NormalisationModelLocalization.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime →
      ∃ e : curveNormalisation J q ≃+* Localization (normalModelSubmonoid M q),
        ∀ f : MvPolynomial (Fin n) ℂ,
          e (algebraMap (curveLocalRing J q) (curveNormalisation J q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)) =
            algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))
              (Ideal.Quotient.mk M.ideal (rename Sum.inl f))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeBranchPlace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def PrimeBranchPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch J 1 q),
    J.IsPrime → ringKrullDim (curveLocalRing J q) ≤ 1 →
      ∃ P : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) = branchOrder c f

end

end GroundTheory.Heights₂.Heights
end

