module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0015
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermGeneralCoordinates
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def GeneralLinearCoordinates.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (f : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → ¬ (∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0) →
    ∃ (A : (Option σ → ℂ) ≃L[ℂ] (Option σ → ℂ)) (d : ℕ),
      analyticOrderAt (fun t => f (A (pointWithLast 0 t))) 0 = d

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassPreparation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def weierstrassPolynomial {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ) (x : Option σ → ℂ) : ℂ :=
  x none ^ d + ∑ j : Fin d, c j (fun i => x (some i)) * x none ^ (j : ℕ)

theorem weierstrassPolynomial_pointWithLast_zero {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, c j 0 = 0) (t : ℂ) : weierstrassPolynomial c (pointWithLast 0 t) = t ^ d := by
  have h : (fun i => pointWithLast (0 : σ → ℂ) t (some i)) = 0 := rfl
  simp only [weierstrassPolynomial, h, hc, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

def WeierstrassPreparation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (f : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 →
    analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = d →
    ∃ (e : (Option σ → ℂ) → ℂ) (c : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ e 0 ∧ e 0 ≠ 0 ∧ (∀ j, AnalyticAt ℂ (c j) 0) ∧ (∀ j, c j 0 = 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = e x * weierstrassPolynomial c x

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHessCCompPluri
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

def HessCCompPluri.Statement : Prop :=
  ∀ (D : ℕ) (F : ℝ → ℝ) (L : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ),
    ContDiffAt ℝ 2 F (L z) → ContDiffAt ℝ 2 L z → hessC L z = 0 →
      hessC (fun w => F (L w)) z = ((deriv (deriv F) (L z) : ℝ) : ℂ) • hessC (fun w => L w ^ 2 / 2) z

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicFibreSumInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.AnForm.A

noncomputable section

def HolomorphicFibreSumInt.Statement : Prop :=
  ∀ (d : ℕ) (Ω : Set (Fin d → ℂ)) (τ : (Fin d → ℂ) → Fin d → ℂ) (H : (Fin d → ℂ) → ℝ),
    IsOpen Ω → DifferentiableOn ℂ τ Ω → (∀ y, {t | t ∈ Ω ∧ τ t = y}.Finite) →
    IntegrableOn (fun t => Complex.normSq (jacC τ t).det * H t) Ω →
      Integrable (fun y => ∑ᶠ t ∈ {t | t ∈ Ω ∧ τ t = y}, H t) ∧
        ∫ y, (∑ᶠ t ∈ {t | t ∈ Ω ∧ τ t = y}, H t) =
          ∫ t in Ω, Complex.normSq (jacC τ t).det * H t

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

def IsolatedFibreOpen.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin k) (Fin n) ℂ) (x : Fin n → ℂ),
    IsAffVariety J k → x ∈ zeroLocus J →
    (∃ W ∈ 𝓝 x, ∀ z ∈ W, z ∈ zeroLocus J → A *ᵥ z = A *ᵥ x → z = x) →
    ∀ W' ∈ 𝓝 x, (fun z => A *ᵥ z) '' (zeroLocus J ∩ W') ∈ 𝓝 (A *ᵥ x)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

variable {n : ℕ}

def logReg (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) : ℝ :=
  Real.log (‖linEval u x‖ ^ 2 + ε) / 2

theorem contDiff_linEval (u : Fin n → ℂ) : ContDiff ℝ ∞ (fun x : Fin n → ℂ => linEval u x) := by
  unfold linEval
  exact ContDiff.sum fun j _ => contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℂ) j).restrict_scalars ℝ)

theorem contDiff_logReg (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (logReg u ε) := by
  unfold logReg
  refine ContDiff.div_const (ContDiff.log (((contDiff_norm_sq ℝ).comp (contDiff_linEval u)).add
    contDiff_const) fun x => ?_) _
  have : 0 ≤ ‖linEval u x‖ ^ 2 := sq_nonneg _
  simp only [Function.comp_apply]
  linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGeneratorsClearDenominators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem LocalGeneratorsClearDenominators.polyOriginIdeal_isPrime : polyOriginIdeal.IsPrime :=
  polyOriginIdeal_isMaximal.isPrime

attribute [local instance] LocalGeneratorsClearDenominators.polyOriginIdeal_isPrime

def LocalGeneratorsClearDenominators.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (f : Fin h → T),
    (∀ i, f i ∈ P) →
    maximalIdeal (Localization.AtPrime P) ≤
        Ideal.span (Set.range fun i => algebraMap T (Localization.AtPrime P) (f i)) ⊔
          maximalIdeal (Localization.AtPrime P) ^ 2 →
      ∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range f)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff

noncomputable section

def cutStep (t : ℝ) : ℝ := Real.smoothTransition (2 - 2 * t)

def cutLevel (k : ℕ) : ℝ := Real.exp (-Real.exp ((k : ℝ) + 1))

def logAbsSq {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : ℝ :=
  Real.log (‖eval y Q‖ ^ 2)

def logLogCut {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ) : ℝ :=
  if ‖eval y Q‖ ^ 2 = 0 then 0
  else if 1 ≤ ‖eval y Q‖ ^ 2 then 1
  else cutStep (Real.log (-logAbsSq Q y) / ((k : ℝ) + 1))

def logLogCutAlong {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (Q : MvPolynomial (Fin m) ℂ) (k : ℕ)
    (x : Fin n → ℂ) : ℝ :=
  logLogCut Q k (A *ᵥ x)

def tubeWeight {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : ℝ :=
  if logAbsSq Q y ≤ -1 then (logAbsSq Q y ^ 2)⁻¹ else 0

def tubeDens {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Fin (d + 1) → ℂ) → ℝ :=
  chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => tubeWeight P (A *ᵥ x))
    (vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) φ)

def CutOffShape.Statement : Prop :=
  ∀ (m : ℕ) (Q : MvPolynomial (Fin m) ℂ),
    (∀ k, ContDiff ℝ ∞ (logLogCut Q k) ∧ (∀ y, logLogCut Q k y ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ y, ‖eval y Q‖ ^ 2 < cutLevel k → logLogCut Q k y = 0) ∧
    ∀ y, eval y Q ≠ 0 → Tendsto (fun k => logLogCut Q k y) atTop (𝓝 1)

theorem cutLevel_mem (k : ℕ) : 0 < cutLevel k ∧ cutLevel k < 1 := by
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _))⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaDensChain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

def MaDensChain.Statement : Prop :=
  ∀ (D : ℕ) (φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (F : ℝ → ℝ) (g : (Fin (D + 1) → ℂ) → ℝ)
    (z : Fin (D + 1) → ℂ),
    ContDiff ℝ 2 F → ContDiffAt ℝ 2 g z →
      maDens (Fin.cons (F ∘ g) φ) z =
          deriv F (g z) * maDens (Fin.cons g φ) z + deriv (deriv F) (g z) * gradDens φ g g z ∧
        gradDens φ (F ∘ g) (F ∘ g) z = deriv F (g z) ^ 2 * gradDens φ g g z

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaDensLogPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ComplexSets

noncomputable section

def MaDensLogPow.Statement : Prop :=
  ∀ (e : ℕ) (φ₀ p : (Fin (e + 1 + 1) → ℂ) → ℝ) (y : Fin (e + 1 + 1) → ℂ),
    ContDiffAt ℝ 2 p y → 0 < p y →
      maDens (Fin.cons φ₀ fun _ : Fin (e + 1) => Real.log ∘ p) y =
        maDens (Fin.cons φ₀ fun _ : Fin (e + 1) => p) y / p y ^ (e + 1) -
          ((e + 1 : ℕ) : ℝ) * gradDens (Fin.cons φ₀ fun _ : Fin e => p) p p y / p y ^ (e + 2)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamChartInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamChartInt.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r r' : ℝ) (N : Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    DifferentiableOn ℂ σ (Metric.ball 0 r) → Set.InjOn σ (Metric.ball 0 r) →
    IsOpen N → r' < r →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r') →
    zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
      ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
      (∀ i, SmoothNear (zeroSet W) (φ i)) →
        chartInt W A f φ =
          ∫ w in Metric.ball (0 : Fin d → ℂ) r, f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolydiscLelongLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff

noncomputable section

def PolydiscLelongLimit.Statement : Prop :=
  ∀ (d m : ℕ) (r ρ : ℝ) (F : (Fin (d + 1) → ℂ) → ℂ) (χ : (Fin (d + 1) → ℂ) → ℝ)
    (ψ : Fin d → (Fin (d + 1) → ℂ) → ℝ),
    ρ < r → VanishesToOrder F r m → ContDiffOn ℝ ∞ χ (Metric.ball 0 r) →
    (∀ τ ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) →
    (∀ k, ContDiffOn ℝ ∞ (ψ k) (Metric.ball 0 r)) →
      Tendsto (fun ε : ℝ =>
          ReciprocityTheory.AnForm.maInt (vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ (Metric.ball 0 r))
        (𝓝[>] 0)
        (𝓝 ((m : ℝ) * ∫ w in Metric.ball (0 : Fin d → ℂ) r,
          χ (ReciprocityTheory.AnForm.A.hypIncl w) * ReciprocityTheory.AnForm.A.densHyp ψ w))

end

end GroundTheory.Heights₂.Heights
end

