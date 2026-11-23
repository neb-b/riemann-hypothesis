module

public import Mathlib
public import Formalism.LogFactorialIndices.Bundle0001
public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.Bundle0001
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0004
public import Formalism.QuotientMetricDivisors.StatementK
public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.FockJet
public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.GaussCoord
public import Formalism.ThetaSupremumBounds.StatementE
public import Formalism.QuotientMetricDivisors.Bundle0002
public import Formalism.ThetaSupremumBounds.DivIneqExplicit6

@[expose] public section

-- bundled from Formalism.ThetaSupremumBounds.LiftOperatorBoundOfFockJet
section
namespace Formalism.DimensionVariation

theorem blockBound : BlockBound := blockBound_of_fockJet gaussianCoeffIntegral

end Formalism.DimensionVariation
end

-- bundled from Formalism.ThetaSupremumBounds.StatementCB
section
open Finset NumberField
open scoped Real

noncomputable section

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)

def cbSq (n n' h h' t : ℝ) : ℝ := n * n' * (h * h') * t

def blockMap {AA AA' : Type} [Fintype AA] {H : AA → Type} {H' : AA' → Type}
    [∀ a, AddCommMonoid (H a)] [∀ b, AddCommMonoid (H' b)]
    (E : ∀ a b, H a →+ H' b) (G : ∀ a, H a) : ∀ b, H' b :=
  fun b => ∑ a, E a b (G a)

def PathSum : Prop :=
  ∀ (m : ℕ) (AA : Fin (m + 1) → Type) [∀ i, Fintype (AA i)] [∀ i, DecidableEq (AA i)]
    (H : ∀ i, AA i → Type) [∀ i a, AddCommMonoid (H i a)]
    (E : ∀ (j : Fin m) (a : AA j.castSucc) (b : AA j.succ), H j.castSucc a →+ H j.succ b)
    (G : ∀ a, H 0 a),
    chainFun (C := fun i => ∀ a, H i a) (fun j => blockMap (E j)) (Fin.last m) G =
      ∑ al : (∀ i, AA i), Pi.single (al (Fin.last m))
        (chainFun (C := fun i => H i (al i)) (fun j => E j (al j.castSucc) (al j.succ)) (Fin.last m)
          (G (al 0)))

def SharpNorm : Prop :=
  ∀ (AA AA' : Type) [Fintype AA] [Fintype AA'] (Cl : AA → Type) (Cl' : AA' → Type)
    [∀ a, Fintype (Cl a)] [∀ b, Fintype (Cl' b)] (A B : Type)
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    (γ : (Σ a, Cl a) → ℝ) (γ' : (Σ b, Cl' b) → ℝ) (ε : (Σ a, Cl a) → (Σ b, Cl' b) → ℂ)
    (T : (Σ a, Cl a) → (Σ b, Cl' b) → A →L[ℂ] B) (h h' tmax : ℝ),
    (∀ p, 0 < γ p ∧ γ p ≤ 1) → (∀ q, 0 < γ' q ∧ γ' q ≤ 1) → (∀ p q, ‖ε p q‖ = 1) →
    (∀ p q, ‖T p q‖ ^ 2 ≤ tmax) → 0 ≤ tmax →
    (∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) → (∀ b, (Fintype.card (Cl' b) : ℝ) ≤ h') →
    (∀ G : (Σ a, Cl a) → A, (∑ q, γ' q * ‖liftOp γ ε T G q‖ ^ 2) ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax * ∑ p, γ p * ‖G p‖ ^ 2) ∧
    liftNormSq γ γ' ε T ≤ cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax

def CBHyp {K : Type} [Field K] [NumberField K] {m : ℕ} {c : Fin (m + 1) → ℕ}
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ)
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    {AA : Fin (m + 1) → Type} (Cl : ∀ i, AA i → Type) [∀ i, Fintype (AA i)] [∀ i a, Fintype (Cl i a)]
    (W : Fin (m + 1) → InfinitePlace K → Type) [∀ i v, NormedAddCommGroup (W i v)]
    [∀ i v, NormedSpace ℂ (W i v)]
    (γ : ∀ i, (Σ a, Cl i a) → ℝ)
    (Φ : ∀ i v, (Fin (c i) → ℂ) → (Σ a, Cl i a) → W i v)
    (ε : ∀ (j : Fin m) (_ : InfinitePlace K), (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) → ℂ)
    (T : ∀ (j : Fin m) (v : InfinitePlace K), (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) →
      W j.castSucc v →L[ℂ] W j.succ v)
    (hcl : Fin (m + 1) → ℝ) (tmax : Fin m → InfinitePlace K → ℝ) : Prop :=
  (∀ i v, IsUnit (Xc i v).det) ∧
  (∀ i p, 0 < γ i p ∧ γ i p ≤ 1) ∧
  (∀ i v x, (∑ p, γ i p * ‖Φ i v x p‖ ^ 2) = fnorm (Xc i v) x ^ 2) ∧
  (∀ j v x, Φ j.succ v (((Kj j).map v.embedding).mulVec x) =
    liftOp (γ j.castSucc) (ε j v) (T j v) (Φ j.castSucc v x)) ∧
  (∀ j v p q, ‖ε j v p q‖ = 1) ∧
  (∀ j v p q, ‖T j v p q‖ ^ 2 ≤ tmax j v) ∧ (∀ j v, 0 ≤ tmax j v) ∧
  (∀ i a, (Fintype.card (Cl i a) : ℝ) ≤ hcl i)

def ChainCB : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ)
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    (AA : Fin (m + 1) → Type) (Cl : ∀ i, AA i → Type) [∀ i, Fintype (AA i)] [∀ i a, Fintype (Cl i a)]
    (W : Fin (m + 1) → InfinitePlace K → Type) [∀ i v, NormedAddCommGroup (W i v)]
    [∀ i v, NormedSpace ℂ (W i v)]
    (γ : ∀ i, (Σ a, Cl i a) → ℝ)
    (Φ : ∀ i v, (Fin (c i) → ℂ) → (Σ a, Cl i a) → W i v)
    (ε : ∀ (j : Fin m) (_ : InfinitePlace K), (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) → ℂ)
    (T : ∀ (j : Fin m) (v : InfinitePlace K), (Σ a, Cl j.castSucc a) → (Σ b, Cl j.succ b) →
      W j.castSucc v →L[ℂ] W j.succ v)
    (hcl : Fin (m + 1) → ℝ) (tmax : Fin m → InfinitePlace K → ℝ),
    CBHyp Xc Kj Cl W γ Φ ε T hcl tmax →
    ∀ kU : Fin m → InfinitePlace K → ℝ,
    (∀ j v, kU j v = Real.sqrt (cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
      (hcl j.castSucc) (hcl j.succ) (tmax j v))) →
    (∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v) ∧
    (∀ j v, kU j v ^ 2 = cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
      (hcl j.castSucc) (hcl j.succ) (tmax j v)) ∧
    (chainMat Kj (Fin.last m) ≠ 0 →
      (∀ j v, 0 < (Fintype.card (AA j.castSucc) : ℝ) ∧ 0 < (Fintype.card (AA j.succ) : ℝ) ∧
        0 < hcl j.castSucc ∧ 0 < hcl j.succ ∧ 0 < tmax j v) ∧
      (∀ j v, Real.log (kU j v ^ 2) =
        Real.log (tmax j v) + (Real.log (hcl j.castSucc) + Real.log (hcl j.succ)) +
          (Real.log (Fintype.card (AA j.castSucc)) + Real.log (Fintype.card (AA j.succ)))) ∧
      (∀ v, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
          (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
          (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ^ 2) ≤
        ∑ j : Fin m, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ^ 2)) ∧
      (∀ v, (∑ j : Fin m, Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
          (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ^ 2)) ≤
        ∑ j : Fin m, Real.log (kU j v ^ 2)) ∧
      Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin (c (Fin.last m))))
                (Xc (Fin.last m)) (Matrix.mulVecLin (chainMat Kj (Fin.last m))) ≤
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, ∑ j : Fin m, Real.log (kU j v ^ 2))

end Formalism.DimensionVariation
end
end

