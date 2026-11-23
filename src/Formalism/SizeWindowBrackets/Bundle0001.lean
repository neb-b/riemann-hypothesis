module

public import Mathlib
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

-- bundled from Formalism.SizeWindowBrackets.ClaimGaFree
section
namespace Formalism.LFunctionChainParameters.UnitWeightPartition

open Finset

noncomputable section

variable {ι κ : Type*} [DecidableEq ι]

def sgw (J : Finset κ) (gain F E : κ → ι → ℝ) (w : ι) : ℝ :=
  ∑ j ∈ J, (gain j w + F j w - E j w)

def Ga (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain : κ → ι → ℝ) (tau : ι → ℝ) : ℝ :=
  2 * ∑ w ∈ W, l w * ((∑ j ∈ J, gain j w) - tau w)

def Fo (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (F : κ → ι → ℝ) : ℝ :=
  2 * ∑ j ∈ J, ∑ w ∈ W, l w * F j w

def Ee (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (E : κ → ι → ℝ) : ℝ :=
  2 * ∑ j ∈ J, ∑ w ∈ W, l w * E j w

def Sg (W : Finset ι) (l s tau : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * (s w - tau w)

def Ta (W : Finset ι) (l tau : ι → ℝ) : ℝ :=
  2 * ∑ w ∈ W, l w * tau w

def IO (W : Finset ι) (l io : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * io w

def be (du : ℝ) (len tau : ι → ℝ) (w : ι) : ℝ :=
  (len w - du * tau w) / du

def BeSum (W : Finset ι) (l : ι → ℝ) (du : ℝ) (len tau : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * be du len tau w

def ClaimSg (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau : ι → ℝ) : Prop :=
  Sg W l (sgw J gain F E) tau = Ga W J l gain tau + Fo W J l F - Ee W J l E

def ClaimDe (f : ℕ) (T dM du : ℝ) : Prop :=
  0 < dM → 2 < T → du = dM * (1 - 1 / (T - 1)) ^ f →
  du = (1 - (1 - du / dM)) * dM ∧ 0 ≤ 1 - du / dM ∧ 1 - du / dM < 1 ∧
    1 - du / dM ≤ 2 * (f : ℝ) / T

def ClaimT (WT : Finset ι) (l len : ι → ℝ) (dM du de lam T : ℝ) : Prop :=
  (∀ w ∈ WT, 0 ≤ l w) → 0 < dM → 0 ≤ de → de ≤ 1 / 2 → du = (1 - de) * dM → 0 ≤ lam →
  (∀ w ∈ WT, len w ≤ dM * lam) → ∑ w ∈ WT, l w = Real.log T →
  ∑ w ∈ WT, 2 * l w * len w / du ≤ 4 * lam * Real.log T

def HypLow (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ) : Prop :=
  (∀ w ∈ W, 0 ≤ l w) ∧ 0 < dM ∧ 0 ≤ de ∧ de < 1 ∧ du = (1 - de) * dM ∧ WT ⊆ W ∧
  (∀ w ∈ WT, tau w = 0) ∧ (∀ w ∈ W, 0 ≤ io w) ∧
  (∀ w ∈ W \ WT, len w ≤ dM * (tau w + io w)) ∧
  ∑ w ∈ WT, 2 * l w * len w / du ≤ PT ∧
  ∑ w ∈ W, 2 * l w * (sgw J gain F E w - sg' w) ≤ Rd ∧
  muN = muMu + Sg W l sg' tau - BeSum W l du len tau

def HypLow2 (W : Finset ι) (l tau io : ι → ℝ) (f T de b muM muMu IOp PT LT Rd RX : ℝ) :
    Prop :=
  muMu = muM - f * Real.log (T - 1) / (T - 2) ∧ de ≤ 2 * f / T ∧ 2 * f / T ≤ 1 / 2 ∧
  (∀ w ∈ W, 0 ≤ tau w) ∧ Ta W l tau ≤ b ^ 2 ∧
  4 * f / T * b ^ 2 + f * Real.log (T - 1) / (T - 2) ≤ 1 ∧
  IO W l io = 2 * IOp ∧ PT ≤ LT ∧ Rd ≤ RX

def ClaimLow2 (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ)
    (f T b muM IOp LT RX : ℝ) : Prop :=
  HypLow W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd →
  HypLow2 W l tau io f T de b muM muMu IOp PT LT Rd RX →
  muM + Ga W J l gain tau + Fo W J l F - Ee W J l E - (4 * IOp + LT + RX + 1) ≤ muN

def HypHigh (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau sg' : ι → ℝ) (muMaxM muMaxMu muMaxN : ℝ) : Prop :=
  (∀ w ∈ W, 0 ≤ l w) ∧ (∀ w ∈ W, sg' w ≤ sgw J gain F E w) ∧
  muMaxN ≤ muMaxMu + Sg W l sg' tau ∧ muMaxMu ≤ muMaxM

def ClaimHigh (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau sg' : ι → ℝ) (muMaxM muMaxMu muMaxN : ℝ) : Prop :=
  HypHigh W J l gain F E tau sg' muMaxM muMaxMu muMaxN →
  muMaxN ≤ muMaxM + Ga W J l gain tau + Fo W J l F - Ee W J l E

end

end Formalism.LFunctionChainParameters.UnitWeightPartition
end

-- bundled from Formalism.SizeWindowBrackets.RealSlopeBoundsSplit
section
namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas

open Finset

noncomputable section

def wmean {ι : Type*} [Fintype ι] (d X : ι → ℝ) : ℝ :=
  (∑ u, d u * X u) / ∑ u, d u

def sF {ι : Type*} [Fintype ι] (d muN h : ι → ℝ) : ℝ :=
  wmean d (fun u => muN u - h u)

end

end Formalism.LFunctionChainParameters.WeightedMeanLemmas
end

-- bundled from Formalism.SizeWindowBrackets.TraceSquareAndDiagBounds
section
open Matrix
open scoped ComplexOrder

namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

noncomputable section

def hsSq {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖ ^ 2

def hsNorm {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  Real.sqrt (hsSq M)

section Family

variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}

def Kp (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (u u' : ι) :
    Matrix (Fin (d u)) (Fin (d u')) ℂ :=
  ((Real.sqrt (ga u * ga u') : ℝ) : ℂ) • ((B u)ᴴ * B u')

def Kd (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (u : ι) :
    Matrix (Fin (d u)) (Fin (d u)) ℂ :=
  Kp B ga u u

def Qm (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ u, ((ga u : ℝ) : ℂ) • (B u * (B u)ᴴ)

def Rs (d : ι → ℕ) : ℝ := ∑ u, (d u : ℝ)

def F1 (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (η : ℝ) : Prop :=
  (Qm B ga * Qm B ga).trace.re ≤ (1 + η) * (Qm B ga).trace.re ^ 2 / (D : ℝ)

def F2 (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (e : ℝ) : Prop :=
  ∑ u, hsSq (Kd B ga u - 1) ≤ e * Rs d

def InputS (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (Dstar η0 η1 e0 : ℝ) : Prop :=
  (∀ u u', u ≠ u' → hsSq (Kp B ga u u') ≤ (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar) ∧
  (∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) ∧
  (D : ℝ) ≤ (1 + η1) * Dstar

def Isom {r : ι → ℕ} (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) : Prop :=
  ∀ u, (V u)ᴴ * V u = 1

def Bram {r : ι → ℕ} (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) : ∀ u, Matrix (Fin D) (Fin (r u)) ℂ :=
  fun u => B u * V u

end Family

def TraceLower : Prop :=
  ∀ (n : ℕ) (K : Matrix (Fin n) (Fin n) ℂ),
    (n : ℝ) - Real.sqrt n * hsNorm (K - 1) ≤ K.trace.re

def TraceSquareAndDiagBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (Dstar sg η0 η1 e0 : ℝ),
    (∀ u, 0 ≤ ga u) → 0 < Dstar → 0 < sg → sg ≤ 1 / 4 → Dstar / sg ≤ Rs d →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    InputS B ga Dstar η0 η1 e0 →
    F1 B ga (5 * sg) ∧ F2 B ga e0 ∧ e0 ≤ 1 / 4

def RamTrace : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (de e0 : ℝ),
    Isom V → (∀ u, 0 ≤ ga u) → 0 ≤ de → 0 ≤ e0 →
    (∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) →
    ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * Rs d →
    (Qm B ga).trace.re - (de + Real.sqrt (de * e0)) * Rs d ≤ (Qm (Bram B V) ga).trace.re

def CompressDiagDefectBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (de e0 : ℝ),
    Isom V → de ≤ 1 / 2 → 0 ≤ e0 →
    (∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) →
    ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * Rs d →
    (1 - de) * Rs d ≤ Rs r ∧ F2 (Bram B V) ga (2 * e0)

def CompressTraceSquareBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (Dstar sg η0 η1 e0 de : ℝ),
    Isom V → (∀ u, 0 ≤ ga u) → 0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ Rs d →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 → ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * Rs d →
    InputS B ga Dstar η0 η1 e0 →
    F1 (Bram B V) ga (5 * sg + 3 * Real.sqrt de)

end

end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
end

