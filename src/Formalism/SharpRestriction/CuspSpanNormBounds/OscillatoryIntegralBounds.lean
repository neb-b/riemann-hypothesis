module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
public import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateTheorem
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Formalism.YangianSpanCharacter.YangianRelationFirst
public import Formalism.FormalDegreeBessel.Bundle0001
public import Formalism.HermitianCurvature.Bundle0001
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0007
public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AffineChangeOfVariables
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousInvUpper
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Markov
public import Formalism.HermitianCurvature.Bundle0003
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Formalism.GelfandTransference.Bundle0001
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeRigidity.StatementC

@[expose] public section

section PartA3c

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

namespace Formalism.MainNotions.InterlacingSignCuts

section Cut

variable {k0 : ℕ}

end Cut

end Formalism.MainNotions.InterlacingSignCuts

end PartA3c

section PartA4

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.QuantumDeterminants Formalism.YangianSpanCharacter.T

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

section PlaneWaves

open Formalism.QuantumDeterminants.WirtingerDerivatives

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

end PlaneWaves

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA4

section PartA9

open Formalism.QuantumDeterminants Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA9

section PartA14

open Polynomial Finset

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA14

section PartA14v

open Polynomial Finset

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA14v

section PartA15

open MeasureTheory Filter Topology
open scoped ComplexConjugate BoundedContinuousFunction NNReal ENNReal

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

namespace Hz

end Hz

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA15

section PartA16

open Complex Real MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

section Std

variable (d : ℕ)

variable {d}


end Std

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA16

section PartA17m

open MeasureTheory Complex Filter
open scoped FourierTransform ContDiff SchwartzMap Real

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.SP

end Formalism.MainNotions.InterlacingSignCuts.SP

end

end PartA17m

section PartA17d

open MeasureTheory Filter Topology Set
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.SP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end Formalism.MainNotions.InterlacingSignCuts.SP

end

end PartA17d

section PartA17a

open MeasureTheory Complex Filter Set
open scoped ContDiff Real

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.SP

end Formalism.MainNotions.InterlacingSignCuts.SP

end

end PartA17a

section PartA17p

open MeasureTheory Complex Filter Set Topology
open scoped ContDiff Real

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.SP

end Formalism.MainNotions.InterlacingSignCuts.SP

end

end PartA17p

section PartA17s

open MeasureTheory Complex Filter Set Topology
open scoped ContDiff Real

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open SP

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA17s

section PartAOm

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LevR

namespace Formalism.MainNotions.InterlacingSignCuts

theorem herm_Hb (k : ℕ) (x y : Fin (k + 1) → ℂ) :
    herm (Hb k) x y = ∑ j, star (y j) * ((if j = Fin.last k then (-1 : ℂ) else 1) * x j) := by
  unfold herm Hb
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]

theorem wI_inj (k r : ℕ) : Function.Injective (wI k r) := by
  intro a b h
  unfold wI at h
  rw [Fin.mk.injEq] at h
  exact Fin.ext (by omega)

theorem not_range_wI (k r : ℕ) (i : Fin (2 * r + k + 1)) (hi : i ∉ Set.range (wI k r)) :
    i.val < r ∨ r + k < i.val := by
  by_contra hc
  push_neg at hc
  apply hi
  refine ⟨⟨i.val - r, by omega⟩, ?_⟩
  unfold wI
  ext
  show r + (i.val - r) = i.val
  omega

theorem Hpk_wI (k r : ℕ) (j : Fin (k + 1)) (q : Fin (2 * r + k + 1)) :
    Hpk k r (wI k r j) q = if q = wI k r j then (if j = Fin.last k then (-1 : ℂ) else 1) else 0 := by
  have hj := j.isLt
  have hv : (wI k r j).val = r + j.val := rfl
  unfold Hpk
  rw [if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega)]
  by_cases hq : q = wI k r j
  · rw [if_pos hq, if_pos ⟨by rw [hv]; omega, by rw [hv]; omega, hq.symm⟩]
    by_cases hl : j = Fin.last k
    · rw [if_pos hl, if_pos (by rw [hv, hl]; rfl)]
    · rw [if_neg hl, if_neg (by
        rw [hv]
        intro h
        exact hl (Fin.ext (by rw [Fin.val_last]; omega)))]
  · rw [if_neg hq, if_neg (by rintro ⟨_, _, h⟩; exact hq h.symm)]

theorem herm_Hpk_wb (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) (hw : inWb k r w) :
    herm (Hpk k r) v w = herm (Hb k) (wbPart k r v) (wbPart k r w) := by
  rw [herm_Hb]
  unfold herm
  simp only [dotProduct, Pi.star_apply]
  symm
  apply Fintype.sum_of_injective (wI k r) (wI_inj k r)
  · intro i hi
    rw [hw i (not_range_wI k r i hi)]
    simp
  · intro j
    have : (Hpk k r *ᵥ v) (wI k r j) = (if j = Fin.last k then (-1 : ℂ) else 1) * v (wI k r j) := by
      simp only [Matrix.mulVec, dotProduct, Hpk_wI]
      simp
    rw [this]
    rfl

theorem wbPart_bigCell (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') :
    wbPart k r (bigCell k r c μ *ᵥ z') = μ *ᵥ wbPart k r z' := by
  funext j
  simp only [wbPart, Matrix.mulVec, dotProduct]
  symm
  apply Fintype.sum_of_injective (wI k r) (wI_inj k r)
  · intro q hq
    rw [hz' q (not_range_wI k r q hq)]
    simp
  · intro j'
    have hj := j.isLt
    have hj' := j'.isLt
    have h1 : ¬ (wI k r j').val < r := by show ¬ (r + j'.val < r); omega
    have h2 : (wI k r j').val ≤ r + k := by show r + j'.val ≤ r + k; omega
    have h3 : r ≤ (wI k r j).val ∧ (wI k r j).val ≤ r + k := by
      constructor
      · show r ≤ r + j.val; omega
      · show r + j.val ≤ r + k; omega
    have : bigCell k r c μ (wI k r j) (wI k r j') = μ j j' := by
      unfold bigCell
      rw [dif_neg h1, dif_pos h2, dif_pos h3]
      congr 1 <;> exact Fin.ext (by show r + _ - r = _; omega)
    rw [this]

theorem bigCell_D (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ ≠ 0 ∧
    Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1)) =
      Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ * herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  obtain ⟨m1, -, m3⟩ := Formalism.QuantumDeterminants.bigCellMinors k r z z' c μ hz hz'
  have hDr : Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ ≠ 0 := by
    have h := m1 (Fin.last r)
    simp only [Fin.val_last] at h
    rw [h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  refine ⟨hDr, ?_⟩
  have h := m3 hc
  unfold zeta at h
  rw [herm_Hpk_wb k r _ z hz, wbPart_bigCell k r c μ z' hz', div_eq_iff hDr] at h
  rw [h, mul_comm]

def IsPolyG {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, ∀ g, evG g P = a g

namespace IsPolyG

variable {n : ℕ}

end IsPolyG

end Formalism.MainNotions.InterlacingSignCuts

end PartAOm

section PartAImg

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Topology Filter
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

end PartAImg

section PartAGb

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGb

section PartAGw

open MeasureTheory

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

section Abstract

variable {X Y K Q : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace K] [MeasurableSpace Q]

variable {M ν : Measure X} {Sm : Measure Y} {act : X → Y → X} {LUs : Set X}
  {μK : Measure K} {μQ : Measure Q} [SFinite μK] [SFinite μQ] {κ : K → Y} {Ψ : K × Q → X} {kc : X → K} {γ : K → ℝ}

end Abstract

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGw

section PartAGj

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGj

section PartAGo1

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

def LUs (s : ℕ) : Set (Msq s × Msq s) := {p | IsLowerUni (Matrix.of p.1) ∧ IsUpperUni (Matrix.of p.2)}

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGo1

section PartAGo2

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGo2

section PartAGo3

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGo3

section PartAGo4

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGo4

section PartAGo

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGo

section PartAGk

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.MainNotions.S

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGk

section PartAGs1

open Matrix MeasureTheory

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGs1

section PartAGs2

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S

variable {s : ℕ} {ι : Type} [Fintype ι]

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGs2

section PartAGs3

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

section ExpCont

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

end ExpCont

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGs3

section PartAGs

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.FourierDecayAlt.G Formalism.MainNotions.S.UnitaryLevelOperators

end Formalism.MainNotions.InterlacingSignCuts.Gm

end PartAGs

section PartAPk

open Polynomial

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

end PartAPk

section PartALev

open Matrix MeasureTheory TensorProduct
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

end PartALev

section PartAOpen

open Polynomial

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

end PartAOpen

section PartALat

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.FrobeniusOrbits

variable (D : D7)

theorem host_totallyComplex : NumberField.IsTotallyComplex D.host.E := by
  have := D.host.isCMField_hostE
  infer_instance

def plOf (v : D.what₂.Tau) : InfinitePlace D.host.E := InfinitePlace.mk (plEmb D v)

theorem plOf_apply (v : D.what₂.Tau) (l : D.host.E) : plOf D v l = ‖plEmb D v l‖ := rfl

theorem plEmb_mem (v : D.what₂.Tau) : plEmb D v ∈ D.host.cmType :=
  ((factEmb D.R D.host).2 _).2 (D.eTau v).2

theorem plEmb_injective : Function.Injective (plEmb D) := by
  intro v w h
  have h1 := (factEmb D.R D.host).1.1 h
  exact D.eTau.injective (Subtype.ext h1)

theorem plOf_bijective : Function.Bijective (plOf D) := by
  have hcm := D.host.der.cmType.1
  constructor
  · intro v w h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact plEmb_injective D h
    · exfalso
      have h1 := (hcm (plEmb D v)).1 (plEmb_mem D v)
      apply h1
      have : (starRingEnd ℂ).comp (plEmb D v) = plEmb D w := h
      rw [this]
      exact plEmb_mem D w
  · intro w
    by_cases hw : w.embedding ∈ D.host.cmType
    · obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 w.embedding
      have hgP : g ∈ D.R.Psi := ((factEmb D.R D.host).2 g).1 (hg ▸ hw)
      refine ⟨D.eTau.symm ⟨g, hgP⟩, ?_⟩
      have : plEmb D (D.eTau.symm ⟨g, hgP⟩) = w.embedding := by
        unfold plEmb
        rw [Equiv.apply_symm_apply]
        exact hg
      unfold plOf
      rw [this, InfinitePlace.mk_embedding]
    · have hw' : (starRingEnd ℂ).comp w.embedding ∈ D.host.cmType := by
        by_contra hc
        exact hw ((hcm w.embedding).2 hc)
      obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ((starRingEnd ℂ).comp w.embedding)
      have hgP : g ∈ D.R.Psi := ((factEmb D.R D.host).2 g).1 (hg ▸ hw')
      refine ⟨D.eTau.symm ⟨g, hgP⟩, ?_⟩
      have : plEmb D (D.eTau.symm ⟨g, hgP⟩) = ComplexEmbedding.conjugate w.embedding := by
        unfold plEmb
        rw [Equiv.apply_symm_apply]
        exact hg
      unfold plOf
      rw [this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem card_places : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [← D.what₂.card_Tau]
  exact (Fintype.card_of_bijective (plOf_bijective D)).symm

theorem f_pos : 0 < D.R.f := by
  rw [← card_places D]
  exact Fintype.card_pos

theorem prod_places (F : InfinitePlace D.host.E → ℝ) : ∏ w, F w = ∏ v, F (plOf D v) := by
  exact (Fintype.prod_bijective (plOf D) (plOf_bijective D) (fun v => F (plOf D v)) F (fun v => rfl)).symm

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S

end Formalism.MainNotions.InterlacingSignCuts

end

end PartALat

section PartALat2

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S

section Theta

variable (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D)

end Theta

end Formalism.MainNotions.InterlacingSignCuts

end

end PartALat2

section PartAAx

open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt.TA

attribute [local instance] Classical.propDecidable

section Points

variable {E : Type} [Field E]

end Points

section Data

variable (D : D7) (L : LatticeDataWithDual D) (Kd : KernelData D) (Lv : ℕ → AddSubgroup D.host.E)

variable {D L Kd}

end Data

end Formalism.MainNotions.InterlacingSignCuts

end

end PartAAx

section PartASz

open NumberField Finset
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt.TA

attribute [local instance] Classical.propDecidable

section Sizes

variable (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (K : ℕ)

variable {D C1 C2 N T T' δ x L}

end Sizes

end Formalism.MainNotions.InterlacingSignCuts

end

end PartASz

section PartAKol

open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.MainNotions.S

end Formalism.MainNotions.InterlacingSignCuts

end

end PartAKol

section PartAPsd

open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.MainNotions.S

attribute [local instance] Classical.propDecidable

end Formalism.MainNotions.InterlacingSignCuts

end

end PartAPsd

section PartARow

open scoped ComplexConjugate ComplexOrder InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.MainNotions.S

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Formalism.MainNotions.InterlacingSignCuts

end

end PartARow

section PartATop

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt.TA

attribute [local instance] Classical.propDecidable

section Points

variable {E : Type} [Field E]

end Points

end Formalism.MainNotions.InterlacingSignCuts

end

end PartATop
