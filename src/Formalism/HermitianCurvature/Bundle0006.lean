module

public import Formalism.HermitianCurvature.StatementNF
public import Formalism.HermitianCurvature.StatementM
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0024
public import Formalism.HermitianCurvature.StatementWd
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0018
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0016
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QEFirstMulSecondEqSwap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0022
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EntryCommuteTransposedRMatrix
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMatrixTransferConjTransposeCommute
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteOfEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialFlipCommuteDiagScalarOfFree
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0021
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelNablaStarRelations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferRtt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0023
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero

@[expose] public section

-- bundled from Formalism.HermitianCurvature.ActualZetaSmooth
section
open Matrix Finset
open scoped ContDiff

namespace Formalism.FourierDecayAlt.NF

open Formalism.REAL Formalism.QuantumDeterminants

def IsMulZ {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
    (W : Module.End ℂ (Q.RadSp k r z z' π π')) (f : ℂ → ℂ) : Prop :=
  ∀ Φ : Q.RadSp k r z z' π π', (W Φ : Q.Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' f (Φ : Q.Fn k r (Wq →L[ℂ] Wp))

def MulZExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∃ W : Module.End ℂ (Q.RadSp P.k P.r z z' π π'), IsMulZ W f

def ActualZetaSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → ∀ (X : Q.ActualOps P.k P.r z z' π π') (f : ℂ → ℂ),
      ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W W₁ W₂ : Module.End ℂ (Q.RadSp P.k P.r z z' π π'), IsMulZ W f → IsMulZ W₁ (dZ f) → IsMulZ W₂ (dZb f) → ∀ Y : ℂ,
        X.t Y 1 0 * W = W * X.t Y 1 0 - W₁ * X.t Y 1 1 ∧ X.t Y 1 1 * W = W * X.t Y 1 1 ∧
        X.t Y 0 1 * W = W * X.t Y 0 1 + W₂ * X.t Y 1 1

def NFOrder0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → ∀ (X : Q.ActualOps P.k P.r z z' π π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r z z' π π'))),
      Q.IsActualLevel X d.L → Fr.IsStarLevel d.L → d.Rel → (∀ Y, X.QQ Y = d.QQ Y) →
      ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W W₁ W₂ : Module.End ℂ (Q.RadSp P.k P.r z z' π π'), IsMulZ W f → IsMulZ W₁ (dZ f) → IsMulZ W₂ (dZb f) →
        (∀ g, Commute (d.κ g).1 W) ∧
        (∀ l ∈ Finset.Icc 1 (P.k - 1), Commute (d.SS l).1 W ∧ Commute (star (d.SS l)).1 W) ∧
        d.L.nab.1 * W = W * d.L.nab.1 + W₁ ∧ d.L.nabs.1 * W = W * d.L.nabs.1 - W₂

def NFOrder0OfParts : Prop := MulZExists → ActualZetaSmooth → NFOrder0

def RelExtra {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) : Prop :=
  d.L.nabs * d.L.nab - d.L.nab * d.L.nabs = (d.κ fun ρ => ((2 * M.aC P ρ * P.TT : ℝ) : ℂ)) * d.L.GGi * d.L.GGi ∧
  ∀ l ∈ Finset.Icc 1 (P.k - 1), (d.SS l * star (d.SS l) = d.κ fun ρ => ((M.NrmDown P l ρ : ℝ) : ℂ)) ∧
    ∀ j ∈ Finset.Icc 1 (P.k - 1), j ≠ l →
      d.SS j * d.SS l * (d.κ fun ρ => ((M.rho P ρ j - M.rho P ρ l - 1 : ℝ) : ℂ)) =
        d.SS l * d.SS j * (d.κ fun ρ => ((M.rho P ρ j - M.rho P ρ l + 1 : ℝ) : ℂ)) ∧
      star (d.SS l) * d.SS j = d.SS j * star (d.SS l)

def SExtra : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), P.OK → Fr.IsStarLevel d.L → d.Rel →
    Wd.IsStart d.QQ (M.qC P) → RelExtra d

end Formalism.FourierDecayAlt.NF
end

-- bundled from Formalism.HermitianCurvature.TopDensNonnegOfKappa
section
open MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section Her

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable (S : Type) [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
  (D : B.RealPlaceData P.k P.r Wp Wq)

def JFOK (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ B.GV P.k P.r, F g ≠ 0 → ε ≤ Gf P.k P.r z z' g

def IsRadJF (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (Φ : RadSp P.k P.r z z' π π') : Prop :=
  ∀ x ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (B.JF D F) x.1 x.2

inductive HerGen : Fin (P.r + 1) → RadSp P.k P.r z z' π π' → Prop
  | jf (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (Φ : RadSp P.k P.r z z' π π') :
      JFOK P z z' F → IsRadJF P z z' π π' D F Φ → HerGen 0 Φ
  | slice (l : Fin P.r) (w : List (Letter ℂ S)) (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → HerGen l.castSucc Φ → HerGen l.succ ((bTl L l w a b).1 Φ)
  | waveC (l : Fin P.r) (w : List (Letter ℂ S)) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
      (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → multiplicationOperator Wv (fun c' _ => fsv s (c' l)) → multiplicationOperator Wv' (fun c' _ => fsv (-s) (c' l)) →
      HerGen l.castSucc Φ → HerGen l.castSucc ((Vw (mkP Wv Wv') s w a b).1 Φ)
  | waveZ (w : List (Letter ℂ S)) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
      (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)) →
      multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g)) →
      HerGen (Fin.last P.r) Φ → HerGen (Fin.last P.r) ((Vw (mkP Wv Wv') s w a b).1 Φ)

def herK (i : Fin (P.r + 1)) : Submodule ℂ (RadSp P.k P.r z z' π π') :=
  Submodule.span ℂ {Φ | HerGen S P z z' π π' L st l0 D i Φ}

variable (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π'))

def TopTwistDens : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w →
  ∀ (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
    multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)) → multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g)) →
    ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K (Fin.last P.r)) x → InK (K (Fin.last P.r)) y → ∀ c ∈ OmX P.r,
      ∀ g, topDens L st w (act (Vw (mkP Wv Wv') s w) x) y c g = fsv s (zeta P.k P.r z z' g) * topDens L st w x y c g

def FormInt : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), c ∈ OmX P.r →
  ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → InK (K i) y →
    (∀ (c' : Cf P.r i) (a : Ix S), Integrable (fun g : Mt P.k P.r =>
        B.hsInner ((act (RRi L st i w) x a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
          ((y a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ) ∧
    Integrable (fun c' : Cf P.r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ a, pairAt μ (act (RRi L st i w) x a) (y a) (glue i c c'))

end Her

def FormSesqOfInt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')),
    FormInt S P z z' π π' μ L st l0 K → FormSesq (S := S) P z z' π π' μ L st K l0

def RadJFExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (F : Mx P.k P.r → (Wq →L[ℂ] Wp)),
    IsPlace P z z' π π' → D.z = z → D.z' = z' → D.π = π → D.π' = π' → JFOK P z z' F →
    ∃ Φ : RadSp P.k P.r z z' π π', IsRadJF P z z' π π' D F Φ

def XKappa {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) : Prop :=
  ∃ κ : (M.Ty P → ℂ) →ₐ[ℂ] Pr (RadSp P.k P.r z z' π π'),
    (∀ Y, st.x Y = κ fun ρ => M.x0 P l0 ρ Y) ∧ (∀ Y ∈ st.inv, st.xi Y = κ fun ρ => (M.x0 P l0 ρ Y)⁻¹) ∧
    ∀ f : M.Ty P → ℂ, (∀ ρ, 0 < f ρ) → ∀ (Φ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r),
      0 ≤ B.hsInner (((κ f).1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g)

def TopDensNonnegOfKappa : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → XKappa P z z' π π' st l0 →
    TopDensNonneg (S := S) P z z' π π' L st K l0

def KappaFibrePos : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)), IsPlace P z z' π π' →
    ∀ (X : ActualOps P.k P.r z z' π π') (d : NFData P (Pr (RadSp P.k P.r z z' π π'))),
      IsActualLevel X d.L → Fr.IsStarLevel d.L → d.Rel → (∀ Y, X.QQ Y = d.QQ Y) →
      ∀ f : M.Ty P → ℂ, (∀ ρ, 0 < f ρ) → ∀ (Φ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r),
        0 ≤ B.hsInner (((d.κ f).1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g)

def XKappaOfNF : Prop :=
  Q.NormalFormActual → KappaFibrePos →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ),
    IsData P z z' π π' X μ L st l0 → XKappa P z z' π π' st l0

end Formalism.FourierDecayAlt.P5
end
end

