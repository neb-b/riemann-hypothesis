module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalMaximumPrinciple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalMaximumPrinciple.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ))
    (g : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    HolomorphicOnSubset g (zeroSetIn I ∩ U) → (∀ z ∈ zeroSetIn I ∩ U, ‖g z‖ ≤ ‖g w‖) →
    ∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → g z = g w

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelProper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def NormalModelProper.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : NormalModel J) (K : Set (Fin n → ℂ)),
    Bornology.IsBounded K →
      Bornology.IsBounded {w : Fin n ⊕ Fin M.m → ℂ | w ∈ zeroSetIn M.ideal ∧ firstCoords w ∈ K}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalRiemannExtension
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def NormalRiemannExtension.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (U : Set (σ → ℂ))
    (f : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → IsOpen U →
    HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0})) →
    ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ U) ∧
      Set.EqOn g f ((zeroSetIn I ∩ U) \ {z | eval z h = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalRiemannExtensionLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalRiemannExtensionLocal.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (U : Set (σ → ℂ)) (f : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0})) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧ ∃ F : (σ → ℂ) → ℂ, DifferentiableOn ℂ F V ∧
      Set.EqOn F f ((zeroSetIn I ∩ V) \ {z | eval z h = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalZerosNowhereDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalZerosNowhereDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (G : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ G N → ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    ∃ U : Set (σ → ℂ), IsOpen U ∧ w ∈ U ∧ U ⊆ N ∧
      ∀ z ∈ zeroSetIn I ∩ U, ∀ V ∈ 𝓝 z, ∃ x ∈ zeroSetIn I ∩ V, G x ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOpenProjectionDominantComponents
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def OpenProjectionDominantComponents.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ w ∈ X ∩ B,
    ∃ (n : ℕ) (Y : Fin n → Set (σ → ℂ)),
      (∀ i, IsAnalyticNear (Y i) w ∧ GermIrreducibleAt (Y i) w ∧
        ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0) ∧
      (∀ i j, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j) ∧
      ∃ W ∈ 𝓝 w, X ∩ B ∩ W = (⋃ i, Y i) ∩ W

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveElementFibres
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def PrimitiveElementFibres.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ (c : Fin n → ℂ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Δ : MvPolynomial (Fin d) ℂ)
        (Q : Fin n → Polynomial (MvPolynomial (Fin d) ℂ)),
        m.Monic ∧ m.natDegree = projDegree J A ∧ Δ ≠ 0 ∧
          ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
            (m.map (eval y)).Separable ∧
            (∀ x ∈ fibre J A y, (m.map (eval y)).IsRoot (∑ j, c j * x j) ∧
              ∀ j, eval y Δ * x j = ((Q j).map (eval y)).eval (∑ j, c j * x j)) ∧
            ∀ τ : ℂ, (m.map (eval y)).IsRoot τ → ∃ x ∈ fibre J A y, ∑ j, c j * x j = τ

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusIdentity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def RegularLocusIdentity.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)), I.IsPrime →
    ∃ h : MvPolynomial σ ℂ, h ∉ I ∧ ∀ z ∈ zeroSetIn I, eval z h ≠ 0 → ∀ W ∈ 𝓝 z,
      ∃ V : Set (σ → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
        ∀ F : (σ → ℂ) → ℂ, AnalyticOnNhd ℂ F V →
          (∃ y ∈ zeroSetIn I ∩ V, ∀ᶠ u in 𝓝 y, u ∈ zeroSetIn I → F u = 0) →
            ∀ u ∈ zeroSetIn I ∩ V, F u = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeaklyHolomorphicIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def WeaklyHolomorphicIntegral.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (G f : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ G N → ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    HolomorphicOnSubset f ((zeroSetIn I ∩ N) \ {z | G z = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ N) \ {z | G z = 0})) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ V ⊆ N ∧ ∃ (d : ℕ) (a : Fin d → (σ → ℂ) → ℂ),
      (∀ j, DifferentiableOn ℂ (a j) V) ∧
      ∀ z ∈ (zeroSetIn I ∩ V) \ {z | G z = 0}, f z ^ d + ∑ j, a j z * f z ^ (j : ℕ) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiAnalyticNormality
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

def holGerms {σ : Type} [Fintype σ] (w : σ → ℂ) : Subring (Germ (𝓝 w) ℂ) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ (f : Germ (𝓝 w) ℂ) = φ}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

theorem analyticAt_eval_polynomial {σ : Type} [Fintype σ] (w : σ → ℂ) (q : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun z : σ → ℂ => eval z q) w := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : σ → ℂ => a) w)
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    have hi : AnalyticAt ℂ (fun z : σ → ℂ => z i) w :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w
    simp only [map_mul, eval_X]
    exact hp.mul hi

def polyGerm {σ : Type} [Fintype σ] (w : σ → ℂ) : MvPolynomial σ ℂ →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (RingHom.pi fun z : σ → ℂ => (MvPolynomial.eval z))).codRestrict
    (holGerms w) fun q => ⟨fun z => eval z q, analyticAt_eval_polynomial w q, rfl⟩

def ZariskiAnalyticNormality.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I →
      (I.map (polyGerm w)).IsPrime ∧ IsIntegrallyClosed (holGerms w ⧸ I.map (polyGerm w))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal

noncomputable section

def AreaLinear.Statement : Prop :=
  ∀ (k m : ℕ) (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
    Function.Injective L → ∀ A : Set (EuclideanSpace ℝ (Fin k)),
      μH[(k : ℝ)] (L '' A) =
        ENNReal.ofReal (√(LinearMap.det (LinearMap.adjoint L ∘ₗ L))) * μH[(k : ℝ)] A


def realGraphPt {k m : ℕ} (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (fun i => F x i))

def AreaGraph.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (EuclideanSpace ℝ (Fin k)))
    (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    IsOpen U → ContDiffOn ℝ 1 F U → ∀ A ⊆ U, MeasurableSet A →
      μH[(k : ℝ)] (realGraphPt F '' A) =
        ∫⁻ x in A, ENNReal.ofReal (√(LinearMap.det
          ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
            LinearMap.adjoint (fderiv ℝ F x : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∘ₗ
              (fderiv ℝ F x : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))))) ∂(μH[(k : ℝ)])

def graphPt {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) (x : EuclideanSpace ℂ (Fin d)) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun j => Sum.elim (fun i => x i) (fun i => F x i) (e j)

def frameProj {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) : I → ℂ :=
  fun i => inner ℂ (b i) z

def frameFibreCount {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (S : Set (EuclideanSpace ℂ (Fin n))) (x : I → ℂ) : ℝ≥0∞ :=
  (({z ∈ S | frameProj b I z = x}.encard : ℕ∞) : ℝ≥0∞)

def ProjectionFormula.Statement : Prop :=
  ∀ (d m n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
    IsOpen Ω → DifferentiableOn ℂ F Ω →
    ∀ (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
      (B : Set (EuclideanSpace ℂ (Fin n))), MeasurableSet B →
      μH[((2 * d : ℕ) : ℝ)] (graphPt e F '' Ω ∩ B) =
        ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount b I (graphPt e F '' Ω ∩ B) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)])

def zeroSetEuc {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (EuclideanSpace ℂ (Fin n)) :=
  {z | ∀ q ∈ J, eval (fun i => z i) q = 0}

def NullSmaller.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < d →
      μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J) = 0

def MassFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ∀ R : ℝ,
      μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball 0 R) < ⊤

def PolySublevel.Statement : Prop :=
  ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ), Q ≠ 0 → ∀ R : ℝ, 0 < R →
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      volume {x : Fin d → ℂ | x ∈ Metric.ball 0 R ∧ ‖eval x Q‖ ≤ η} ≤ ENNReal.ofReal (C * η ^ α)

def linProjHom {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ J :=
  (Ideal.Quotient.mkₐ ℂ J).comp (aeval fun i => ∑ j, C (A i j) * X j)

structure IsFiniteLinProj {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) : Prop where

  injective : Function.Injective (linProjHom J A)

  finite : (linProjHom J A : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J).Finite

def SlabBound.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (u : Fin n → ℂ),
    J.IsPrime → IsFiniteLinProj J A → linForm u ∉ J →
      ∃ Q : MvPolynomial (Fin d) ℂ, Q ≠ 0 ∧ ∀ R : ℝ, ∃ C : ℝ, ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R →
        ‖eval (A *ᵥ fun j => z j) Q‖ ≤ C * ‖∑ j, u j * z j‖

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsConeAvoid
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n d : ℕ}

def leadForm (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  homogeneousComponent f.totalDegree f

def leadIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (leadForm '' (J : Set (MvPolynomial (Fin n) ℂ)))

def originIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range X)

def linIdeal (A : Matrix (Fin d) (Fin n) ℂ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range (linPoly A))

def ConeAvoids (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (N : ℕ) : Prop :=
  originIdeal n ^ N ≤ leadIdeal J ⊔ linIdeal A

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

