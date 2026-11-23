module

public import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedMirrorLevelOperator
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0014
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
section
noncomputable section

namespace Formalism.MainNotions.S.UnitaryLevelOperators

section Gauge

open Matrix MeasureTheory TensorProduct
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA

end Gauge

section LevelR

open Matrix MeasureTheory TensorProduct
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Parts

variable {B : Base E} {r : ℕ} (C : Ctx B r) (Γ : GCtx E r)

def lenI (B : Base E) : ℝ := sSup B.I - sInf B.I

def mid3 (B : Base E) : Set ℝ := Set.Icc (sInf B.I + lenI B / 3) (sSup B.I - lenI B / 3)

def wnormSq {n : ℕ} (wt : (Fin n → Fin 2) → B.Rho → ℂ) (x : Fin (r + 1) → ℂ) (v : (Fin n → Fin 2) → E) : ℝ :=
  ∑ s, ∑ᶠ ρ, ‖wt s ρ‖ * (B.hs (C.P ρ x (v s)) (C.P ρ x (v s))).re

end Parts

end LevelR

section Further

open Matrix MeasureTheory Filter Topology Polynomial
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

def IsKFinCoefT {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ a ∈ UH (Hpk k r), ∃ b ∈ UH (Hpk k r), IsKFinCoefH σ (fun g => f (a * g * b))

section Lists

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

end Lists

def headEl (k j r' : ℕ) (h : Matrix (Fin j) (Fin j) ℂ)
    (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ := fun p q =>
  if hq : q.val < j then
    (if hp : 2 * (j + r') + k + 1 - j ≤ p.val then h ⟨2 * (j + r') + k - p.val, by omega⟩ ⟨q.val, hq⟩ else 0)
  else if hq2 : q.val < 2 * r' + k + 1 + j then
    (if hp : j ≤ p.val ∧ p.val < 2 * r' + k + 1 + j then g ⟨p.val - j, by omega⟩ ⟨q.val - j, by omega⟩ else 0)
  else
    (if hp : p.val < j then (hᴴ)⁻¹ ⟨p.val, hp⟩ ⟨2 * (j + r') + k - q.val, by omega⟩ else 0)

def levOf {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) : Lev where
  k0 := k0
  r := r
  z := L.z
  z' := L.z'
  Wp := L.Wp
  Wq := L.Wq
  π := L.π
  π' := L.π'
  μsec := μsec

def cutF {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (z z' : Fin (2 * r + k + 1) → ℂ)
    (χ : ℝ → ℝ) (ε : ℝ) (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V :=
  fun g => ((χ (Gf k r z z' g / ε) : ℝ) : ℂ) • F g

def Std (D : Formalism.BasicNotions.D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS)
    (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) (I : Set ℝ) : Prop :=
  (∀ i, L.ε i = epsSH D.R (Fin.cast (by rw [hk]) i)) ∧ L.c = cStd ∧
    IsSection (k0 + 1) D.R.rS L.z L.z' μsec ∧ IsCutS L.u L.u' I ∧
    ∃ ρ : Fin k0 → ℝ, Interlace L.u ρ ∧ Interlace L.u' ρ

abbrev Msq (s : ℕ) := Fin s → Fin s → ℂ

end Further

end Formalism.MainNotions.S.UnitaryLevelOperators
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.IsGramNorm
section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.QuantumDeterminants Formalism.MainNotions.S.LevR

section Val

variable {k r : ℕ}

def wbEmb (k r : ℕ) (x : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun p =>
  if h : r ≤ p.val ∧ p.val ≤ r + k then x ⟨p.val - r, by omega⟩ else 0

def PtRepC (B : LocBessel k r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (B.c.re = 0 → IsPtRep B γ g) ∧ (B.c.re ≠ 0 → IsPtRepO B γ g)

def HasRep (B : LocBessel k r) (γ : Point ℂ (r + 1)) : Prop :=
  PtLastOk r (Tz k r B.z) (Tz k r B.z') γ ∧ ∃ g, PtRepC B γ g

def IsGramRef (B : LocBessel k r) (n n' : Fin (k + 1) → ℂ) (ι : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  herm (Hb k) n (wbPart k r B.z) = 0 ∧ herm (Hb k) n n = 1 ∧
  herm (Hb k) n' (wbPart k r B.z') = 0 ∧ herm (Hb k) n' n' = 1 ∧
  ∀ x y : Fin (k + 1) → ℂ, herm (Hb k) x (wbPart k r B.z') = 0 → herm (Hb k) x n' = 0 →
    herm (Hb k) y (wbPart k r B.z') = 0 → herm (Hb k) y n' = 0 →
    herm (Hb k) (ι *ᵥ x) (wbPart k r B.z) = 0 ∧ herm (Hb k) (ι *ᵥ x) n = 0 ∧
      herm (Hb k) (ι *ᵥ x) (ι *ᵥ y) = herm (Hb k) x y

def IsGramNorm (B : LocBessel k r)
    (n n' : Fin (k + 1) → ℂ) (ι : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∃ t : ℝ, 0 < t ∧ omG k r B.z B.z' g = ((t : ℂ) * Dmin k r B.z B.z' g (Fin.last (r + 1))) • n) ∧
  (∃ t : ℝ, 0 < t ∧ omG' k r B.z B.z' g = ((t : ℂ) * star (Dmin k r B.z B.z' g (Fin.last (r + 1)))) • n') ∧
  ∀ x : Fin (k + 1) → ℂ, herm (Hb k) x (wbPart k r B.z') = 0 → herm (Hb k) x n' = 0 →
    g *ᵥ wbEmb k r x = wbEmb k r (ι *ᵥ x)

end Val

structure ValMap (k r : ℕ) where

  V : ∀ (B : LocBessel k r),
    (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp)) → List (ℂ × ℕ) → (B.Wq →L[ℂ] B.Wp)

  rep : LocBessel k r → List (ℂ × ℕ) → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

  n : LocBessel k r → Fin (k + 1) → ℂ
  n' : LocBessel k r → Fin (k + 1) → ℂ
  ι : LocBessel k r → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ

  ref_ok : ∀ B : LocBessel k r, 0 < k → IsGramRef B (n B) (n' B) (ι B)

  rep_ok : ∀ (B : LocBessel k r) (γ : Point ℂ (r + 1)), HasRep B γ →
    PtRepC B γ (rep B γ.1) ∧ IsGramNorm B (n B) (n' B) (ι B) (rep B γ.1)

  val : ∀ (B : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp)) (γ : Point ℂ (r + 1))
    (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)),
    B.c ≠ 0 → (B.c.re = 0 ∨ B.c.im = 0) → SmoothOnH (Hpk k r) F → HasRep B γ →
    IsRootMeas B γ (rep B γ.1) μR → IsOrbQuot B (rep B γ.1) μR ν → V B F γ.1 = OrbInt B F (rep B γ.1) ν

  val0 : ∀ (B : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp)) (γ : Point ℂ (r + 1)),
    ¬ HasRep B γ → V B F γ.1 = 0

end Formalism.MainNotions.S
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.SLemOm
section
namespace Formalism.MainNotions.S.Lem

theorem orbRStabBig : Formalism.MainNotions.S.OrbRStabBig := stabilizer_large

end Formalism.MainNotions.S.Lem
end

