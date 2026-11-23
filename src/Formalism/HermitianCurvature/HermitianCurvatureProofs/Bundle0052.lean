module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.HermitianCurvature.Bundle0009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def CSec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μ0 : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  IsSection k r z z' μ0 ∧ ∀ ζ ζ' : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ → Tz k r z * Tz k r z' < Complex.normSq ζ' →
    NF.Stab k r z z' μ0 ζ = NF.Stab k r z z' μ0 ζ'

def GCoreSec : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
      ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

def SecExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∃ μ0, CSec P.k P.r Bs.z Bs.z' μ0

def SecMove : Prop := SecExists → GCoreSec → GCore

def trR {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)

def FamLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r))
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
    ∀ q : MA.Qp P.r P.TT, ∃ Φt : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∃ V ∈ nhds q.1.2,
      ∀ ζ' ∈ V, (Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') = Φ q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') ∧
        ∀ (Y : ℂ) (a b : Fin 2), (X.t Y a b Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') =
          Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b Φ q.1.1 (NF.muZ P.k P.r Bs.μsec ζ')

def GenTransfer : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
      Q.IsActualLevel X d.L → Fr.IsStarLevel d.L → d.Rel → (∀ Y : ℂ, X.QQ Y = d.QQ Y) →
      ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
        ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
          trR P Bs e (d.L.ζ.1 Φ) = MA.actA P (MA.zA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.ζi.1 Φ) = MA.actA P (MA.ziA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.ζb.1 Φ) = MA.actA P (MA.zbA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.ζbi.1 Φ) = MA.actA P (MA.zbiA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.GG.1 Φ) = MA.actA P (MA.ggA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.GGi.1 Φ) = MA.actA P (MA.ggiA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.nab.1 Φ) = MA.actA P (MA.nabA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.nabs.1 Φ) = MA.actA P (MA.nabsA P (MA.DQ P)) (trR P Bs e Φ) ∧
          (∀ f : M.Ty P → ℂ, trR P Bs e ((d.κ f).1 Φ) = MA.actA P (MA.kap P (MA.DQ P) f) (trR P Bs e Φ)) ∧
          (∀ l ∈ Finset.Icc 1 (P.k - 1),
            trR P Bs e ((d.SS l).1 Φ) = MA.actA P (MA.SS P (MA.DQ P) l) (trR P Bs e Φ)) ∧
          ∀ l ∈ Finset.Icc 1 (P.k - 1),
            trR P Bs e ((star (d.SS l)).1 Φ) = MA.actA P (star (MA.SS P (MA.DQ P) l)) (trR P Bs e Φ)

def GenTransferQQ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∀ X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
        ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (Y : ℂ) (a b : Fin 2),
          trR P Bs e (X.t Y a b Φ) = MA.actA P (MA.QQr P (MA.DQ P) Y a b) (trR P Bs e Φ)

def ModelLocal : Prop :=
  ∀ (P : M.Par) (f g : M.Ty P → MA.SmQ P.r P.TT) (c : Fin P.r → ℂ) (V : Set ℂ), IsOpen V →
    (∀ ρ (q : MA.Qp P.r P.TT), q.1.1 = c → q.1.2 ∈ V → (f ρ : MA.Qp P.r P.TT → ℂ) q = (g ρ : MA.Qp P.r P.TT → ℂ) q) →
    ∀ (Y : ℂ) (a b : Fin 2) ρ (q : MA.Qp P.r P.TT), q.1.1 = c → q.1.2 ∈ V →
      (MA.actA P (MA.QQr P (MA.DQ P) Y a b) f ρ : MA.Qp P.r P.TT → ℂ) q =
        (MA.actA P (MA.QQr P (MA.DQ P) Y a b) g ρ : MA.Qp P.r P.TT → ℂ) q

def RadSpSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT

def GenToQQ : Prop := RadSpSmooth → GenTransfer → GenTransferQQ

def AsmSec : Prop := FamLocal → GenTransferQQ → ModelLocal → RadSpSmooth → GRawSmooth → GQLFam → GCoreSec

def GCoreOfCut : Prop :=
  SecExists → SecMove → FamLocal → GenTransfer → GenToQQ → ModelLocal → RadSpSmooth → GRawSmooth → GQLFam → AsmSec → GCore

theorem gauge_construction_of_truncation : GCoreOfCut := fun hSE hSM hFL hGT hGQ hML hRS hRaw hQL hA =>
  hSM hSE (hA hFL (hGQ hRS hGT) hML hRS hRaw hQL)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

abbrev GFn (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Type := B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))

def smoothFormsPositiveCone (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) : Set (GFn S v) :=
  Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

def GfP (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (g : B.Mat S.G.k S.G.r) : ℝ :=
  Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g

def mulG (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (ψ : ℝ → ℝ) (J : GFn S v) : GFn S v :=
  fun g => ((ψ (GfP S T v g) : ℝ) : ℂ) • J g

def CCg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (A Bg : ℝ) (F : GFn S v) : Prop :=
  ∀ m : ℕ, B.InCC (A - Bg * m) m F

def CutCoef (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg : ℝ) : Prop :=
  ∀ Tm ∈ Θ, ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat S.G.k S.G.r),
    (∀ X ∈ u, B.unitLie S.G.k S.G.r X) → (∀ X ∈ w, B.unitLie S.G.k S.G.r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV S.G.k S.G.r, ε ≤ GfP S T v g →
      ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ (d + Bg * m) ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ (d + Bg * m)

def IsAAOp (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) : Prop :=
  B.SmoothCoef (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θ

def LocCC (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (A Bg : ℝ) (J : GFn S v) : Prop :=
  J ∈ smoothFormsPositiveCone S T v ∧ ∀ δ : ℝ, 0 < δ → ∃ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ CCg S v A Bg F ∧
    ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, δ ≤ GfP S T v (B.gq (T v).base x) →
      J (B.gq (T v).base x) = B.JF (T v).base F (B.gq (T v).base x)

def applyL (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (J : GFn S v) : GFn S v :=
  Θs.foldr (fun Θ J' => B.opApply Θ J') J

def adjL (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (J : GFn S v) : GFn S v :=
  Θs.foldl (fun J' Θ => B.opAdj Θ J') J

end defs

def JABddStar : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), star b ∈ Submonoid.closure (MA.bddSet P L) ∧
      ∀ (ε : ℝ) (U V : M.Ty P → MA.SmQ P.r P.TT), 0 < ε →
        (∀ π q, MA.Gq P q < ε → MA.evQ P (U π) q = 0) →
        (∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ P (U π) q‖ ^ 2) {q | ε ≤ MA.Gq P q} (MA.mu0 P.r P.TT)) →
        (∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ P (V π) q‖ ^ 2) {q | ε ≤ MA.Gq P q} (MA.mu0 P.r P.TT)) →
        MA.ipA P U (MA.actA P b V) = MA.ipA P (MA.actA P (star b) U) V

def JAIsAdj : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ a ∈ Submonoid.closure (MA.hatSet P L ∪ MA.bddSet P L), MA.IsAdjA P a

def JAPhiOp : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → ∀ φ : ℝ → ℝ, LE.SmoothLog φ →
      ∀ J ∈ smoothFormsPositiveCone S T v, mulG S T v φ J ∈ smoothFormsPositiveCone S T v ∧
        trJ S T v e (mulG S T v φ J) =
          fun π => MA.toSm (D.parOf S v) (fun q => (φ (MA.Gq (D.parOf S v) q) : ℂ)) * trJ S T v e J π

def JAStarOp : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ a ∈ Submonoid.closure (MA.hatSet (D.parOf S v) L ∪ MA.bddSet (D.parOf S v) L), ∀ ts : List (ℂ × List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))), (∀ t ∈ ts, ∀ Θ ∈ t.2, IsAAOp S T v Θ) →
        (∀ J ∈ smoothFormsPositiveCone S T v, (∀ t ∈ ts, applyL S v t.2 J ∈ smoothFormsPositiveCone S T v ∧ adjL S v t.2 J ∈ smoothFormsPositiveCone S T v) ∧
          MA.actA (D.parOf S v) a (trJ S T v e J) = (ts.map fun t => t.1 • trJ S T v e (applyL S v t.2 J)).sum) →
        ∀ J ∈ smoothFormsPositiveCone S T v,
          MA.actA (D.parOf S v) (star a) (trJ S T v e J) = (ts.map fun t => (starRingEnd ℂ t.1) • trJ S T v e (adjL S v t.2 J)).sum

def JAGroupAdj : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg : ℝ), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ → CutCoef S T v Θ d Bg →
      ∀ ε : ℝ, 0 < ε → ∀ J₁ J₂ : GFn S v,
        LocCC S T v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg J₁ →
        LocCC S T v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg J₂ →
        (∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, GfP S T v (B.gq (T v).base x) < ε → J₁ (B.gq (T v).base x) = 0) →
        B.opApply Θ J₁ ∈ smoothFormsPositiveCone S T v → B.opAdj Θ J₂ ∈ smoothFormsPositiveCone S T v →
        MA.ipA (D.parOf S v) (trJ S T v e (B.opApply Θ J₁)) (trJ S T v e J₂) =
          MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e (B.opAdj Θ J₂))

def JALocCC : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v,
      (∀ (F : GFn S v) (A Bg : ℝ), B.CkOn ⊤ (B.GV S.G.k S.G.r) F → (∀ m : ℕ, B.InCC A m F) →
        B.JF (T v).base F ∈ smoothFormsPositiveCone S T v → 0 ≤ Bg → LocCC S T v A Bg (B.JF (T v).base F)) ∧
      (∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opApply Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opApply Θ J)) ∧
      (∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opAdj Θ J)) ∧
      (∀ (φ : ℝ → ℝ) (Bg A : ℝ) (J : GFn S v), LE.SmoothLog φ → (∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) →
        Cg * ((S.G.r : ℝ) + 1) ≤ Bg → LocCC S T v A Bg J → mulG S T v φ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v A Bg (mulG S T v φ J)) ∧
      (∀ (Bg A : ℝ) (J J' : GFn S v), 0 ≤ Bg → Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 ≤ A →
        LocCC S T v A Bg J → LocCC S T v A Bg J' → LocCC S T v A Bg (J + J')) ∧
      (∀ (Bg A : ℝ) (c : ℂ) (J : GFn S v), LocCC S T v A Bg J → LocCC S T v A Bg (c • J)) ∧
      (∀ (Bg A A' : ℝ) (J : GFn S v), A' ≤ A → LocCC S T v A Bg J → LocCC S T v A' Bg J) ∧
      (∀ (Bg A ε : ℝ) (J : GFn S v) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → 0 ≤ Bg → 0 < ε →
        Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r + 5 * Bg ≤ A → LocCC S T v A Bg J →
        ∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          {q | ε ≤ MA.Gq (D.parOf S v) q} (MA.mu0 (D.parOf S v).r (D.parOf S v).TT))

def JAFFStable : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))), IsAAOp S T v Θ → ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatBdd
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem hat_bounded_decay_holds : JDHatBdd := by
  intro P L hTT hL X hX b hb
  have hLaw : (MA.DQ P).Laws P.TT := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT
  have hS := Formalism.FourierDecayAlt.P.MAx3.H.hyp_model hL hLaw
  have hV := Formalism.FourierDecayAlt.P.MAx3.K.hypV_model hL hLaw
  have gen : ∀ b' ∈ Submonoid.closure (MA.bddSet P L), ∀ X' ∈ MA.hatSet P L,
      b' * X' ∈ Submodule.span ℂ (bddHat P L) := fun b' hb' X' hX' =>
    Submodule.subset_span ⟨b', hb', X', hX', rfl⟩
  have mA : ∀ y, L.Ahat y ∈ MA.hatSet P L := fun y => Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
  have mR : ∀ y, L.R0 y ∈ MA.hatSet P L := fun y => Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))
  have mAv : ∀ y, L.Ahatv y ∈ MA.hatSet P L := fun y => Or.inl (Or.inr ⟨y, rfl⟩)
  have mRv : ∀ y, L.R0v y ∈ MA.hatSet P L := fun y => Or.inr ⟨y, rfl⟩
  have sumA : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahat x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L) := by
    intro ts hts
    refine list_sum_mem fun u hu => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mA _))
  have sumAv : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahatv x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L) := by
    intro ts hts
    refine list_sum_mem fun u hu => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mAv _))
  rcases hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
  · obtain ⟨t, ht⟩ := hS.ahat b hb
    rw [ht y]; exact gen _ hb _ (mA _)
  · obtain ⟨t, ts, hts, he⟩ := hS.r0 b hb y
    rw [he]; exact Submodule.add_mem _ (gen _ hb _ (mR _)) (sumA ts hts)
  · obtain ⟨t, ht⟩ := hV.ahatv b hb
    rw [ht y]; exact gen _ hb _ (mAv _)
  · obtain ⟨t, ts, hts, he⟩ := hV.r0v b hb y
    rw [he]; exact Submodule.add_mem _ (gen _ hb _ (mRv _)) (sumAv ts hts)

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExtension
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.FrameExtension

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frame_weaken {k r m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, e] Bs) : IsFrameOf k r [z] Bs := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun a v hv => h3 a v (by rw [List.mem_singleton] at hv; subst hv; simp)⟩

private theorem hpk_apply_comm (k r : ℕ) (t u : Fin (2 * r + k + 1)) : Hpk k r u t = Hpk k r t u := by
  have := t.isLt
  have := u.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

private theorem star_hpk_apply (k r : ℕ) (t u : Fin (2 * r + k + 1)) : star (Hpk k r t u) = Hpk k r t u := by
  simp only [Hpk]
  split_ifs <;> simp

private theorem herm_hpk_eq_star_herm_swap (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, star_hpk_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
  rw [hpk_apply_comm]
  ring

theorem frame_snoc {k r m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, e] Bs) (he : inWb k r e) (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) :
    IsFrameOf k r [z] (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
  · induction a using Fin.lastCases with
    | last => simpa using he
    | cast i => simpa using h1 i
  · induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simpa using hee
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last j).ne', herm_hpk_eq_star_herm_swap, h3 j e (by simp), star_zero]
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last i).ne, h3 i e (by simp)]
      | cast j =>
        simp only [Fin.snoc_castSucc]
        rw [h2 i j]
        simp [Fin.castSucc_inj]
  · rw [List.mem_singleton] at hv
    subst hv
    induction a using Fin.lastCases with
    | last => simpa using hez
    | cast i => simpa using h3 i v (by simp)

theorem subA_EB {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {k r m : ℕ} (π : Mx k r → (W →L[ℂ] W))
    (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (e : Fin (2 * r + k + 1) → ℂ) :
    subA (EB π (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e)) = EB π Bs := by
  funext a b
  simp [subA, EB, unitB, Fin.snoc_castSucc]

theorem prod_Icc_fin (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Finset.Icc 1 (n + 1), f i = ∏ j : Fin (n + 1), f ((j : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n + 1)]
    simp

end Formalism.FourierDecayAlt.P.FrameExtension

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qr_branchingK_of : Qr.BranchingAlg → Qr.FrameGl → Qr.LieStab → Qr.StabLie → Qr.FrameChange →
    Qr.FrameExists2 → Qr.BranchingK := by
  intro hBA hFG hLS hSL hFC hFE Wp _ _ _ n r z e π u β L hz hT hty hL hu he hez hee
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨Bs₀, hB₀⟩ := hFE n r z e hz hT he hez hee
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  have hsub : subA (EB π Bs₁) = EB π Bs₀ := FrameExtension.subA_EB π Bs₀ e
  obtain ⟨hgl, hq⟩ := hFG Wp (n + 1) r (n + 1) z π Bs₁ hR hB₁
  have hH : Hyp (EB π Bs₁) β L := by
    refine ⟨hgl, ⟨hnt, fun S hS => hirr S (hLS Wp (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
    intro w v
    rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [← hu j]
    ring
  obtain ⟨hint, hS⟩ := hBA Wp n (EB π Bs₁) β L hH
  rw [hsub] at hint hS
  refine ⟨fun M => CapSp (EB π Bs₀) (shf β M.1), hint, fun M => ⟨(hS M).1, fun S' hle hst => ?_⟩, ?_⟩
  · exact (hS M).2 S' hle (hSL Wp (n + 1) r n z e π Bs₀ hR hB₀ S' hst)
  · intro Bs hBs M w v hv
    rw [(hFG Wp (n + 1) r n z π Bs hR (FrameExtension.frame_weaken hBs)).2 w v,
      hFC Wp n r z e π Bs Bs₀ hz hT he hez hee hR hBs hB₀ w]
    exact Qr.mem_CapSp.1 hv w

end Formalism.FourierDecayAlt.P
end
end

