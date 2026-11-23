module

public import Formalism.HermitianCurvature.StatementU
public import Mathlib
public import Formalism.HermitianCurvature.StatementLE
public import Formalism.HermitianCurvature.StatementG
public import Formalism.HermitianCurvature.Bundle0001
public import Formalism.HermitianCurvature.StatementQ

@[expose] public section

-- bundled from Formalism.HermitianCurvature.BigCellVanishingOfCommute
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.C6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def sq2 {m : ℕ} (v : Fin m → ℂ) : ℝ := ∑ a, Complex.normSq (v a)

def unitOf {m : ℕ} (T Gv : ℝ) (v : Fin m → ℂ) : Fin m → ℂ := ((Real.sqrt (T / Gv) : ℝ) : ℂ) • v

def UnitWords (k r : ℕ) (u v : List (B.Mat k r)) (i : ℕ) : Prop :=
  (∀ X ∈ u, B.unitLie k r X) ∧ (∀ X ∈ v, B.unitLie k r X) ∧ u.length + v.length = i

def FibUnit : Prop :=
  ∀ (k r m : ℕ) (om : B.Mat k r → Fin m → ℂ) (Gp : B.Mat k r → ℝ) (T : ℝ),
    (∀ a, U.IsPolyDeg (r + 1) (fun g => om g a)) → U.IsPolyDeg (2 * r + 2) (fun g => (Gp g : ℂ)) → 0 < T →
    (∀ g ∈ B.GV k r, sq2 (om g) = Gp g / T) →
    ∀ ε : ℝ, 0 < ε → ∀ i : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), UnitWords k r u v i →
      ∀ g ∈ B.GV k r, ε ≤ Gp g →
        ‖B.dLR u v (fun g' => unitOf T (Gp g') (om g')) g‖ ≤ C * B.gN g ^ ((r + 1) * (2 * i + 1))

def FibCost : Prop :=
  ∀ (k r m m' : ℕ) (om : B.Mat k r → Fin m → ℂ) (om' : B.Mat k r → Fin m' → ℂ) (Gp : B.Mat k r → ℝ) (T T' : ℝ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Pi : (Fin m → ℂ) × (Fin m' → ℂ) → E)
    (O : Set ((Fin m → ℂ) × (Fin m' → ℂ))),
    (∀ a, U.IsPolyDeg (r + 1) (fun g => om g a)) → (∀ a, U.IsPolyDeg (r + 1) (fun g => om' g a)) →
    U.IsPolyDeg (2 * r + 2) (fun g => (Gp g : ℂ)) → 0 < T → 0 < T' →
    (∀ g ∈ B.GV k r, sq2 (om g) = Gp g / T) → (∀ g ∈ B.GV k r, sq2 (om' g) = Gp g / T') →
    IsOpen O → {w | sq2 w.1 = 1 ∧ sq2 w.2 = 1} ⊆ O → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pi O →
    ∀ ε : ℝ, 0 < ε → ∀ i : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), UnitWords k r u v i →
      ∀ g ∈ B.GV k r, ε ≤ Gp g →
        ‖B.dLR u v (fun g' => Pi (unitOf T (Gp g') (om g'), unitOf T' (Gp g') (om' g'))) g‖ ≤
          C * B.gN g ^ (3 * (r + 1) * i)

def FibCostOfParts : Prop := FibUnit → FibCost

def DminPoly : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)), U.IsPolyDeg l.val (fun g => Dmin k r z z' g l)

def GfPoly : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), U.IsPolyDeg (2 * r + 2) (fun g => ((Gf k r z z' g : ℝ) : ℂ))

def GfDlast : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 0 ≤ Tz k r z → 0 ≤ Tz k r z' →
    ∀ (g : B.Mat k r) (ε : ℝ), ε ≤ Gf k r z z' g → ε ≤ Complex.normSq (Dmin k r z z' g (Fin.last (r + 1)))

abbrev EndH (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] := (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)

section ddplus

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def domL (D : B.RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ 0 < Gf k r D.z D.z' g ∧ ∀ l ∈ L, Dmin k r D.z D.z' g l ≠ 0}

def bigPos (D : B.RealPlaceData k r Wp Wq) : Set (B.Mat k r) := domL D Finset.univ

def monoM (D : B.RealPlaceData k r Wp Wq) (a b : Fin (r + 2) → ℕ) (c : ℕ) (g : B.Mat k r) : ℂ :=
  (∏ l, (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) *
    ((Gf k r D.z D.z' g : ℝ) : ℂ)⁻¹ ^ c

def Epart {nf : ℕ} (fib : Fin nf → B.Mat k r → EndH Wp Wq) (es : List (Fin nf × List (B.Mat k r)))
    (g : B.Mat k r) : EndH Wp Wq :=
  (es.map fun e => B.Rw e.2 (fib e.1) g).prod

def FibBound (D : B.RealPlaceData k r Wp Wq) (E : B.Mat k r → EndH Wp Wq) : Prop :=
  B.CkOn ⊤ (B.GPos D) E ∧ ∀ ε : ℝ, 0 < ε → ∀ i : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), UnitWords k r u v i →
    ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → ‖B.dLR u v E g‖ ≤ C * B.gN g ^ (3 * (r + 1) * i)

def InDDPlus (D : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → EndH Wp Wq)
    (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq) : Prop :=
  B.SmoothCoef (domL D L) Θ ∧ B.Commutes D (domL D L) Θ ∧
  ∀ T ∈ Θ, ∃ (P : B.Mat k r → ℂ) (a b : Fin (r + 2) → ℕ) (c : ℕ)
      (es : List (Fin nf × List (B.Mat k r))), U.IsPolyDeg κ P ∧
      (∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) ∧
      T.word.length + (es.map fun e => e.2.length).sum ≤ o ∧ (∀ e ∈ es, ∀ X ∈ e.2, B.inLie k r X) ∧
      ∀ g ∈ domL D L, T.coef g = (P g * monoM D a b c g) • Epart fib es g

def IsCut0 (χ₀ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ₀ ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ x, x < δ → χ₀ x = 0) ∧ ∀ x, 1 ≤ x → χ₀ x = 1

end ddplus

def ComposeDDPlus : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (nf : ℕ)
    (fib : Fin nf → B.Mat k r → EndH Wp Wq) (L : Finset (Fin (r + 2))) (o₁ κ₁ o₂ κ₂ : ℕ)
    (Θ₁ Θ₂ : B.DiffOp k r Wp Wq),
    (∀ j, FibBound D (fib j)) → InDDPlus D fib L o₁ κ₁ Θ₁ → InDDPlus D fib L o₂ κ₂ Θ₂ →
    ∃ Θ : B.DiffOp k r Wp Wq, InDDPlus D fib L (o₁ + o₂) (κ₁ + κ₂ + (2 * r + 2) * o₁) Θ ∧
      ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (B.GV k r) F →
        ∀ g ∈ domL D L, B.opApply Θ F g = B.opApply Θ₁ (B.opApply Θ₂ F) g

def AV (CV r n : ℕ) : ℝ := (CV : ℝ) * ((r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4)

def mmV (CV r : ℕ) : ℕ := CV * (r ^ 2 + 1)

section radial

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end radial

def AveragingZero : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (p : Seminorm ℂ V) (s : ℕ) (w : Fin s → ℂ)
    (a : Fin s → V) (C' x₁ : ℝ), Function.Injective w →
    (∀ x : ℂ, x₁ ≤ ‖x‖ → p (∑ j, G.psi β (w j * x) • a j) ≤ C' / ‖x‖) → ∀ j, p (a j) = 0

section orbit

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def Rset (γ : B.Mat k r) : Set (B.Mat k r) := {ρ | ρ ∈ Nset k r ∧ γ⁻¹ * ρ * γ ∈ Nset k r}

def IsRelevant (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : Prop :=
  γ ∈ B.GV k r ∧ ∀ ρ ∈ Rset γ, psi k r D.z cStd ρ = psi k r D.z' cStd (γ⁻¹ * ρ * γ)

def actR (γ ρ : B.Mat k r) (p : B.SS k r) : B.SS k r :=
  ((p.1.1, Matrix.of.symm (ρ * Matrix.of p.1.2)), (p.2.1, Matrix.of.symm (γ⁻¹ * ρ * γ * Matrix.of p.2.2)))

structure OrbData (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) where
  μR : Measure (Mt k r)
  haarR : B.IsHaarOn (Rset γ) μR
  J : (B.Mat k r → (Wq →L[ℂ] Wp)) → (Wq →L[ℂ] Wp)
  weil : ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (θ : B.SS k r → ℝ), Measurable θ → (∀ p, 0 ≤ θ p) →
    (∀ p, D.inSS p → ∫ x, θ (actR γ (Matrix.of x) p) ∂μR = 1) →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F γ)) D.μSS →
    ∫ p, θ p • (B.xiTau D (1, 1) p • B.rho D p F γ) ∂D.μSS = J F

end orbit

end Formalism.FourierDecayAlt.C6
end
end

-- bundled from Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
section
namespace Formalism.FourierDecayAlt.C7

open Finset Matrix

open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

def LamInterlaces (k r : ℕ) (u : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ i : Fin (k + 2 * r + 1),
    (i.val + 1 ≤ k → lam i < u (i.val + 1)) ∧ (i.val + 2 ≤ k → u (i.val + 2) < lam i)

def Between (u u' : ℕ → ℝ) (l : ℕ) (Y : ℝ) : Prop :=
  min (u l) (u' l) < -Y ∧ -Y < max (u l) (u' l)

def LamSide : Prop :=
  ∀ (k r : ℕ) (u u' : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k →
    LamInterlaces k r u lam → LamInterlaces k r u' lam → Between u u' l Y →
    ∀ i : Fin (k + 2 * r + 1), (l ≤ i.val + 1 → lam i < min (u l) (u' l)) ∧
      (i.val + 1 < l → max (u l) (u' l) < lam i)

def RhoSide : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k → I.Interlaces k u u' ρ → Between u u' l Y →
    ∀ i ∈ Icc 1 (k - 1), (l ≤ i → ρ i < -Y) ∧ (i < l → -Y < ρ i)

def PSign : Prop :=
  ∀ (k r : ℕ) (u u' ρ : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k →
    LamInterlaces k r u lam → LamInterlaces k r u' lam → I.Interlaces k u u' ρ → Between u u' l Y →
    0 < (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s) ∧ 0 < (-1 : ℝ) ^ (k - l) * I.xpoly k ρ Y ∧
      |∏ s, (Y + lam s)| = (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s)

def principalHermitianLattice {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  B.beta D (w.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F) F

def RootsOutJoint : Prop :=
  ∀ (S : LE.Sys) (u u' : ℕ → ℝ) (l : ℕ), 1 ≤ l → l ≤ S.k →
    LamInterlaces S.k S.r u S.lam → LamInterlaces S.k S.r u' S.lam →
    (∀ Y ∈ Set.Icc S.α S.β, Between u u' l Y) → S.RootsOut

end

end Formalism.FourierDecayAlt.C7
end

-- bundled from Formalism.HermitianCurvature.OperatorsCommuteTranslations
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.C3

open Formalism.REAL Formalism.QuantumDeterminants

def InNp (k r : ℕ) (p q : Fin (2 * r + k + 1)) : Prop :=
  p.val < q.val ∧ ¬ (r ≤ p.val ∧ p.val ≤ r + k ∧ r ≤ q.val ∧ q.val ≤ r + k)

def dpsiP (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) : ℂ :=
  if p.val < r ∧ q.val < r then (if q.val = p.val + 1 then 1 else 0)
  else if p.val < r ∧ r ≤ q.val ∧ q.val ≤ r + k then (if p.val + 1 = r then z' q else 0)
  else if r ≤ p.val ∧ p.val ≤ r + k ∧ r + k < q.val then
    (if q.val = r + k + 1 then herm (Hpk k r) (bvec p) z' else 0)
  else if r + k < p.val ∧ r + k < q.val then (if q.val = p.val + 1 then 1 else 0)
  else 0

def rgen {A : Type*} [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) : Set A :=
  {x | ∃ p q, InNp k r p q ∧ x = E p q - algebraMap ℂ A (dpsiP k r z' p q)}

def RightRuleFn {A M : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (z' : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) : Prop :=
  ∀ (x : A) (p q : Fin (2 * r + k + 1)), InNp k r p q → La (x * E p q) = dpsiP k r z' p q • La x

def xR (k r m : ℕ) (h : m ≤ r) (l : Fin m) : Fin (2 * r + k + 1) := eI k r (Fin.castLE h l)

def sR (k r m : ℕ) (h : m ≤ r) (l : Fin m) : Fin (2 * r + k + 1) := esI k r (Fin.castLE h l)

def PeelingOmittedColumn : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (m : ℕ) (hm : m + 1 ≤ r) (i : Fin (m + 1)) (u : ℂ),
    qminor E (xR k r m (by omega)) (fun l : Fin m => xR k r (m + 1) hm (i.succAbove l)) u -
      qminor E (xR k r i.val (by have := i.isLt; omega)) (xR k r i.val (by have := i.isLt; omega)) u ∈
      Ideal.span (rgen k r z' E)

def PeelingCovector : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k m : ℕ) (z' yb : Fin (2 * (m + 1) + k + 1) → ℂ)
    (E : Fin (2 * (m + 1) + k + 1) → Fin (2 * (m + 1) + k + 1) → A) (i : Fin (m + 1)) (u : ℂ),
    inWb k (m + 1) z' →
    (∑ w : Fin (k + 1), herm (Hpk k (m + 1)) (bvec (wI k (m + 1) w)) yb •
        qminor E (xR k (m + 1) (m + 1) le_rfl)
          (Fin.snoc (α := fun _ => Fin (2 * (m + 1) + k + 1))
            (fun l : Fin m => xR k (m + 1) (m + 1) le_rfl (i.succAbove l)) (wI k (m + 1) w)) u) -
      herm (Hpk k (m + 1)) z' yb •
        qminor E (xR k (m + 1) i.val (by have := i.isLt; omega)) (xR k (m + 1) i.val (by have := i.isLt; omega)) u ∈
      Ideal.span (rgen k (m + 1) z' E)

def PeelingDualColumn : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A), GlRel E →
    ∀ (m : ℕ) (hm : m + 1 ≤ r) (i : Fin (m + 1)) (ell : ℂ),
    qminor E (fun l : Fin m => sR k r (m + 1) hm (i.succAbove l)) (sR k r m (by omega)) (ell + (m : ℂ) - 1) -
      qminor E (sR k r i.val (by have := i.isLt; omega)) (sR k r i.val (by have := i.isLt; omega))
        (ell + ((i.val : ℕ) : ℂ) - 1) ∈
      Ideal.span (rgen k r z' E)

def Zb (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (a b : ℕ) : ℂ :=
  if ha : a < i0 then (if hb : b < i0 then h ⟨a, ha⟩ ⟨b, hb⟩ else 0)
  else if i0 ≤ b ∧ a < i0 + s ∧ b < i0 + s ∧ (a - i0) + (b - i0) + 1 = s then t else 0

def Dlead (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (n : ℕ) : ℂ :=
  (Matrix.of fun a b : Fin n => Zb i0 s h t a.val b.val).det

def sgnW (m : ℕ) : ℂ := (-1) ^ (m * (m - 1) / 2)

def DleadZb : Prop :=
  ∀ (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ),
    Dlead i0 s h t i0 = h.det ∧ Dlead i0 s h t (i0 + s) = h.det * t ^ s * sgnW s

def MinorsFirstCase : Prop :=
  ∀ (i0 s' : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (c : Fin (i0 + s' + 1)),
    (Matrix.of fun a l : Fin (i0 + s') => Zb i0 (s' + 1) h t a.val (c.succAbove l).val).det =
      if c.val = i0 then h.det * t ^ s' * sgnW s' else 0

def MinorsThirdCase : Prop :=
  ∀ (i0 s'' : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ),
    (Matrix.of fun a b : Fin (i0 + s'') =>
        Zb i0 (s'' + 2) h t ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val
          ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val).det =
      h.det * t ^ s'' * sgnW s''

def SignE : Prop :=
  ∀ s : ℕ, sgnW s * sgnW (s + 1) = (-1) ^ s ∧ sgnW s * sgnW (s + 2) = -1

def keyS (k r : ℕ) (p : Fin (2 * r + k + 1)) : ℕ := if r + k < p.val then 2 * r + k - p.val else p.val + r


open scoped Classical in
def AAx {A : Type*} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (u : ℂ) : A :=
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then (Matrix.of fun a l : Fin m => xi (Fin.castLE hm a) (c l)).det • qminor E (xR k r m hm) c u
    else 0


open scoped Classical in
def AAv {A : Type*} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (ell : ℂ) : A :=
  ∑ B : Fin m → Fin (2 * r + k + 1),
    if StrictMono (fun l => keyS k r (B l)) then
      (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) (B l)).det • qminor E B (sR k r m hm) (ell + (m : ℂ) - 1)
    else 0

def ExpansionOmittedColumn : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (z' : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t u : ℂ)
    (hs : 1 ≤ s) (hj : i0 + s ≤ r),
    RightRuleFn k r z' E La → h.det ≠ 0 → t ≠ 0 →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi a p = if p.val < i0 + s then Zb i0 s h t a.val p.val else 0) →
    (Dlead i0 s h t (i0 + s))⁻¹ • La (AAx k r E xi (i0 + s - 1) (by omega) u) =
      ((-1 : ℂ) ^ (s - 1) * t⁻¹) • ((Dlead i0 s h t i0)⁻¹ • La (AAx k r E xi i0 (by omega) u))

def ExpansionDualColumn : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (z' : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t ell : ℂ)
    (hs : 1 ≤ s) (hj : i0 + s ≤ r),
    GlRel E → RightRuleFn k r z' E La → h.det ≠ 0 → t ≠ 0 →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      y a p = if r + k < p.val ∧ 2 * r + k - p.val < i0 + s then star (Zb i0 s h t a.val (2 * r + k - p.val))
        else 0) →
    (star (Dlead i0 s h t (i0 + s)))⁻¹ • La (AAv k r E y (i0 + s - 1) (by omega) ell) =
      ((-1 : ℂ) ^ (s - 1) * (star t)⁻¹) • ((star (Dlead i0 s h t i0))⁻¹ • La (AAv k r E y i0 (by omega) ell))

def ExpansionCovector : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (z' yb : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t u : ℂ)
    (hs : 2 ≤ s) (hj : i0 + s = r + 1),
    RightRuleFn k r z' E La → h.det ≠ 0 → t ≠ 0 → inWb k r z' → inWb k r yb → herm (Hpk k r) z' yb = t →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val ≠ i0 →
      xi a p = if p.val < r ∧ p.val ≠ i0 then Zb i0 s h t a.val p.val else 0) →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val = i0 → xi a p = herm (Hpk k r) (bvec p) yb) →
    (Dlead i0 s h t (r + 1))⁻¹ • La (AAx k r E xi r le_rfl u) =
      ((-1 : ℂ) ^ (s - 1) * t⁻¹) • ((Dlead i0 s h t i0)⁻¹ • La (AAx k r E xi i0 (by omega) u))

def LeftRuleBig {A M : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (k r : ℕ) (c : Fin r → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) : Prop :=
  ∀ (x : A) (a b : Fin r), b.val < a.val →
    La (E (eI k r a) (eI k r b) * x) = (if a.val = b.val + 1 then c a / c b else 0) • La x

def LastColumnChain : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (La : A →ₗ[ℂ] M), GlRel E → (∀ l, c l ≠ 0) → RightRuleFn k r z' E La → LeftRuleBig k r c E La →
    ∀ (m : ℕ) (hm : m + 2 ≤ r) (u : ℂ),
      La (qminor E (xR k r (m + 2) hm) (xR k r (m + 2) hm) u) =
        La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
            Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) -
          (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u)

def dEll (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hr : 1 ≤ r) : ℂ :=
  (∑ a : Fin r, if h : a.val + 1 < r then X (eI k r a) (eI k r ⟨a.val + 1, h⟩) else 0) +
    (X *ᵥ z') (eI k r ⟨r - 1, by omega⟩)

def DpsiDerivation : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hr : 1 ≤ r), inWb k r z' → Xᴴ * Hpk k r + Hpk k r * X = 0 → (∀ p q, ¬ InNp k r p q → X p q = 0) →
    ∑ p, ∑ q, X p q * dpsiP k r z' p q = dEll k r z' X hr - star (dEll k r z' X hr)

def LeadAA : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r), ∃ B : Fin m → A, ∀ u : ℂ,
      AAx k r E xi m hm u =
        algebraMap ℂ A (u ^ m * (Matrix.of fun a b : Fin m => xi (Fin.castLE hm a) (xR k r m hm b)).det) +
          ∑ l : Fin m, algebraMap ℂ A (u ^ (l : ℕ)) * B l

def LeadAAv : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r), ∃ B : Fin m → A, ∀ ell : ℂ,
      AAv k r E y m hm ell =
        algebraMap ℂ A (ell ^ m * (Matrix.of fun a b : Fin m => y (Fin.castLE hm a) (sR k r m hm b)).det) +
          ∑ l : Fin m, algebraMap ℂ A (ell ^ (l : ℕ)) * B l

def XiYZhat : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a b : Fin r), g ∈ UH (Hpk k r) →
    herm (Hpk k r) (g *ᵥ bvec (eI k r b)) (bvec (eI k r a)) = Zhat k r z z' g a.castSucc b.castSucc ∧
    (g⁻¹ *ᵥ bvec (eI k r a)) (esI k r b) = star (Zhat k r z z' g a.castSucc b.castSucc)


open scoped Classical in
def AAop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r m : ℕ) (hm : m ≤ r) (u : ℂ)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E := fun g =>
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then
      (Matrix.of fun a l : Fin m => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))).det •
        qminorOp (EabH (Hpk k r)) (xR k r m hm) c u f g
    else 0


open scoped Classical in
def AAvop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r m : ℕ) (hm : m ≤ r) (ell : ℂ)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E := fun g =>
  ∑ B : Fin m → Fin (2 * r + k + 1),
    if StrictMono (fun l => keyS k r (B l)) then
      (Matrix.of fun a l : Fin m => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)).det •
        qminorOp (EabH (Hpk k r)) B (sR k r m hm) (ell + (m : ℂ) - 1) f g
    else 0

def OperatorsCommuteTranslations : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (m : ℕ)
    (hm : m ≤ r) (u ell : ℂ) (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E),
    inWb k r z → inWb k r z' → SmoothOnH (Hpk k r) f →
    ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', ∀ g, inUH (Hpk k r) g →
      AAop k r m hm u (fun x => f (s * x * s')) g = AAop k r m hm u f (s * g * s') ∧
      AAvop k r m hm ell (fun x => f (s * x * s')) g = AAvop k r m hm ell f (s * g * s')

def N0set (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧ (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a)) ∧ g *ᵥ z' = z' ∧
    (∀ p q : Fin (2 * r + k + 1), r ≤ q.val → q.val ≤ r + k → r ≤ p.val → g p q = if p = q then 1 else 0) ∧
    (∀ p q : Fin (2 * r + k + 1), r + k < q.val → r + k < p.val → g p q = if p = q then 1 else 0)}

def IsotropicNormalFormFull : Prop :=
  ∀ (k m : ℕ) (z' : Fin (2 * (m + 1) + k + 1) → ℂ) (i : Fin (m + 1)) (y : Fin (m + 1) → Fin (2 * (m + 1) + k + 1) → ℂ)
    (t : ℂ), inWb k (m + 1) z' → herm (Hpk k (m + 1)) z' z' ≠ 0 → t ≠ 0 →
    (∀ a, a ≠ i → y a (esI k (m + 1) i) = 0) →
    (∀ p : Fin (2 * (m + 1) + k + 1), m + 1 + k < p.val → y i p = 0) →
    (Matrix.of fun a b : Fin m => y (i.succAbove a) (esI k (m + 1) (i.succAbove b))).det ≠ 0 →
    (∀ a, a ≠ i → herm (Hpk k (m + 1)) z' (y a) = 0) → herm (Hpk k (m + 1)) z' (y i) = t →
    (∀ a a', herm (Hpk k (m + 1)) (y a) (y a') = 0) →
    ∃ n0 ∈ N0set k (m + 1) z', ∃ y' : Fin (m + 1) → Fin (2 * (m + 1) + k + 1) → ℂ, ∀ a,
      n0 *ᵥ y' a = y a ∧
      (a ≠ i → (∀ p : Fin (2 * (m + 1) + k + 1), p.val ≤ m + 1 + k → y' a p = 0) ∧
        (∀ p : Fin (2 * (m + 1) + k + 1), m + 1 + k < p.val → y' a p = y a p)) ∧
      (a = i → inWb k (m + 1) (y' a) ∧ herm (Hpk k (m + 1)) z' (y' a) = t)

end Formalism.FourierDecayAlt.C3
end
end

