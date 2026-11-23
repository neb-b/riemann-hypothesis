module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsClosedPointConeCoord
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ClosedPointConeCoord.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (i : Fin n),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((1 : ℕ) : WithBot ℕ∞) → X i ∉ I →
      ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (y : Fin n → Ω), y ≠ 0 → (∀ g ∈ I, aeval y g = 0) → y i ≠ 0

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMapArea
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

def ConeMapArea.Statement : Prop :=
  ∀ (n e : ℕ) (ι : Type) [Countable ι] (U D : ι → Set (Fin e → ℂ))
    (v : ι → (Fin e → ℂ) → (Fin n → ℂ)) (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    (∀ i, IsOpen (U i) ∧ MeasurableSet (D i) ∧ D i ⊆ U i ∧ DifferentiableOn ℂ (v i) (U i)) →
    Set.InjOn (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1))
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0} →
    Measurable F →
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
              {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0}, F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∑' i, ∫⁻ x in D i, ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i x)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) x)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMapAreaOne
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

def ConeMapAreaOne.Statement : Prop :=
  ∀ (n e : ℕ) (U D : Set (Fin e → ℂ)) (v : (Fin e → ℂ) → (Fin n → ℂ))
    (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    IsOpen U → MeasurableSet D → D ⊆ U → DifferentiableOn ℂ v U →
    Set.InjOn (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) {q | q.1 ∈ D ∧ q.2 ≠ 0} →
    Measurable F →
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) ''
              {q | q.1 ∈ D ∧ q.2 ≠ 0}, F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∫⁻ x in D, ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeMassOfFibre.Statement : Prop :=
  ∀ (n m δ : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    IsProjPrime J →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = δ) →
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} =
        (δ : ENNReal) * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0}

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMeetNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeMeetNull.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W W' : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime → W'.IsPrime →
    W ≠ W' → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W') ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W ∩ coneBall h W') = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSlab
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeSlabBound.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      ∃ C α : ℝ, 0 < α ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            (coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖}) ≤
          ENNReal.ofReal (C * ε ^ α)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsHolomorphicImplicitGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

def HolomorphicImplicitGraph.Statement : Prop :=
  ∀ (n m : ℕ) (f : Fin (n - m) → EuclideanSpace ℂ (Fin n) → ℂ) (y : EuclideanSpace ℂ (Fin n))
    (V : Set (EuclideanSpace ℂ (Fin n))),
    (∀ i, ContDiff ℂ 1 (f i)) → IsOpen V → y ∈ V → (∀ i, f i y = 0) →
    finrank ℂ ↥(⨅ i, LinearMap.ker (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin n))) = m →
      ∃ (e : Fin n ≃ Fin m ⊕ Fin (n - m)) (Ω : Set (EuclideanSpace ℂ (Fin m)))
        (Φ : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m)))
        (U : Set (EuclideanSpace ℂ (Fin n))),
        IsOpen U ∧ y ∈ U ∧ U ⊆ V ∧ IsOpen Ω ∧ DifferentiableOn ℂ Φ Ω ∧
        graphPt e Φ '' Ω = {z | z ∈ U ∧ ∀ i, f i z = 0} ∧
        ∀ x ∈ Ω, LinearMap.range (fderiv ℂ (graphPt e Φ) x :
            EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) =
          ⨅ i, LinearMap.ker (fderiv ℂ (f i) (graphPt e Φ x) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncIdealSeparate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncIdealSeparate.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P Q : Ideal (MvPolynomial (Fin n) F)),
    IsProjPrime P → IsProjPrime Q → incIdeal Q k ≠ ⊥ → incIdeal Q k ≤ incIdeal P k → Q ≤ P

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPolyLocalGenerators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

def polyTangent {n : ℕ} (S : Set (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    Submodule ℂ (Fin n → ℂ) where
  carrier := {v | ∀ q ∈ S, ∑ j, eval p (pderiv j q) * v j = 0}
  add_mem' {v w} hv hw q hq := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hv hw ⊢
    rw [hv q hq, hw q hq, add_zero]
  zero_mem' q _ := by simp
  smul_mem' c v hv q hq := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum] at hv ⊢
    rw [hv q hq, mul_zero]

def PolyLocalGenerators.Statement : Prop :=
  ∀ (n m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = m →
    ∀ p : Fin n → ℂ, (∀ q ∈ J, eval p q = 0) →
      finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p) = m →
      ∃ (q : Fin (n - m) → MvPolynomial (Fin n) ℂ) (g : MvPolynomial (Fin n) ℂ),
        (∀ i, q i ∈ J) ∧ eval p g ≠ 0 ∧ finrank ℂ (polyTangent (Set.range q) p) = m ∧
        ∀ r ∈ J, g * r ∈ Ideal.span (Set.range q)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def projVar (e : ℕ) (i : Fin (e + 1)) : FractionRing (MvPolynomial (Fin (e + 1)) ℂ) :=
  algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (X i)

def projPar {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) :
    Vertical.Par e n → FractionRing (MvPolynomial (Fin (e + 1)) ℂ)
  | .inl (i, j) =>
      projVar e i.succ * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) -
        projVar e 0 * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A i.succ j)
  | .inr j => algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) / projVar e 0

def ProjSecDegree.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    ComplexSets.projDegree J A =
      Module.finrank (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
        (Vertical.SecAlg
          (J.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecDegreeGe.Statement : Prop :=
  ∀ (k E : Type) [Field k] [PerfectField k] [Field E] [Algebra k E] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → E),
    IsProjPrime Q → IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      eval (fun j => y (.inr j)) (Vertical.specRest (algebraMap k E) g y) ≠ 0 →
        Module.Finite E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) ∧
          δ ≤ Module.finrank E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecDegreeLe.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → E),
    IsProjPrime Q → IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      Module.Finite E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      IsDomain (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      Algebra.IsSeparable E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      Vertical.specRest (algebraMap k E) g y ≠ 0 →
        Module.finrank E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) ≤ δ

namespace SecDegreeLe

end SecDegreeLe

end

end GroundTheory.Heights₂.Heights
end

