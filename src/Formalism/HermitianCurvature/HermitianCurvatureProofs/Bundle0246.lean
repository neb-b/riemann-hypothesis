module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsCompactCutoffCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0206
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCoefficientHasCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0242
public import Formalism.DoubleCosetMeasures.Statement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0239
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0244
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0240
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0241
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmLongContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0220
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensityOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
section
noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def xT (k r : ℕ) (Z : Matrix (Fin r) (Fin r) ℂ) (μ : B.Mat k (r - r)) : B.Mat k r :=
  D.castM (by omega) (U.mMap k r (r - r) Z μ)

def pbTop {P : M.Par} (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Z : Matrix (Fin P.r) (Fin P.r) ℂ)
    (μ : B.Mat P.k (P.r - P.r)) : Wq →L[ℂ] Wp :=
  PBQ.pbT p P.r le_rfl G (xT P.k P.r Z μ)

def TopCls {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  KB.CptCoef Bs G ∧ ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧
    ∀ g ∈ B.GV k r, G g ≠ 0 → Dmin k r Bs.z Bs.z' g ⟨r, by omega⟩ ∈ K

def UT (k r : ℕ) (z z' : Fin (2 * (r - r) + k + 1) → ℂ) : Set ((Fin r → Fin r → ℂ) × Mt k (r - r)) :=
  {q | (Matrix.of q.1).det ≠ 0 ∧ 0 < Q.GGl k (r - r) z z' (Matrix.of q.2)}

def psiU {P : M.Par} (p : KB.Pl P Wp Wq) (u : Matrix (Fin P.r) (Fin P.r) ℂ) : ℂ :=
  psi P.k P.r p.T.base.z' cStd (D.castM (by omega) (U.muP P.k P.r (P.r - P.r) u))

def F2 {k r : ℕ} (b b' : U.RC k r (r - r) → ℝ) (Φ : (Fin r → Fin r → ℂ) → Mt k (r - r) → (Wq →L[ℂ] Wp)) :
    B.Mat k r → (Wq →L[ℂ] Wp) :=
  D.castF (by omega : r = r + (r - r)) (PBI.chartCoefficient b b' Φ)

end defs

def UwTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base F →
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      TopCls p.T.base (D.uwG P.k P.r p.T.base.z p.T.base.z' F P.r le_rfl w e)

def SliceTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
      Integrable (fun v : PBQ.XH h => PBQ.ellH h v (pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (pbTop p G (PBQ.zxH h P.r hh.2 v) γ)

def PbSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z')
      (fun q => pbTop p G (Matrix.of q.1) (Matrix.of q.2))

def PbRight : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (Z u : Matrix (Fin P.r) (Fin P.r) ℂ) (μ : B.Mat P.k (P.r - P.r)), Formalism.DoubleCosetMeasures.IsUpUni u →
      pbTop p G (Z * u) μ = psiU p u • pbTop p G Z μ

def PbSupp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∃ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K ∧
      K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ∧
      ∀ q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r), (Matrix.of q.1).det ≠ 0 →
        Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → pbTop p G (Matrix.of q.1) (Matrix.of q.2) ≠ 0 →
        ∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K

def PbEquiv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (Z : Matrix (Fin P.r) (Fin P.r) ℂ), Z.det ≠ 0 →
    ∀ μ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _), ∀ h ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z,
    ∀ h' ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z',
      pbTop p G Z (h * μ * h') = ((p.T.bs P.r).π h).comp ((pbTop p G Z μ).comp ((p.T.bs P.r).π' h'))

def MkTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    ∃ (b b' : U.RC P.k P.r (P.r - P.r) → ℝ) (β : (Fin P.r → Fin P.r → ℂ) → ℝ) (κ : ℂ),
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ ContDiff ℝ ∞ b' ∧ HasCompactSupport b' ∧ κ ≠ 0 ∧
      ContDiffOn ℝ ∞ β {Z | (Matrix.of Z).det ≠ 0} ∧
      (∀ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K →
        K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
        ∃ K' : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K' ∧
          K' ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ∧
          ∀ q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r), (Matrix.of q.1).det ≠ 0 → β q.1 ≠ 0 →
            (∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K) →
            q ∈ K') ∧
      ∀ Φ : (Fin P.r → Fin P.r → ℂ) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp),
        (∀ Z y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → ∀ h ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z,
          ∀ h' ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z',
            Φ Z (Matrix.of.symm (h * Matrix.of y * h')) = ((p.T.bs P.r).π h).comp ((Φ Z y).comp ((p.T.bs P.r).π' h'))) →
        (∀ Z y (u : Matrix (Fin P.r) (Fin P.r) ℂ), (Matrix.of Z).det ≠ 0 →
          Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Formalism.DoubleCosetMeasures.IsUpUni u →
            Φ (Matrix.of.symm (Matrix.of Z * u)) y = psiU p u • Φ Z y) →
        ∀ Z y, (Matrix.of Z).det ≠ 0 → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
          pbTop p (F2 b b' (fun Z' y' => ((β Z' : ℝ) : ℂ) • Φ Z' y')) (Matrix.of Z) (Matrix.of y) = κ • Φ Z y

def MkCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (b b' : U.RC P.k P.r (P.r - P.r) → ℝ), ContDiff ℝ ∞ b → HasCompactSupport b → ContDiff ℝ ∞ b' →
    HasCompactSupport b' → ∀ Φ : (Fin P.r → Fin P.r → ℂ) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp),
    PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') (fun q => Φ q.1 q.2) →
    ∀ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K →
      K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
      (∀ q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ K → Φ q.1 q.2 = 0) →
      TopCls p.T.base (F2 b b' Φ)

def TopPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    (∀ x ∈ Q.DomR P.k P.r p.T.base.z p.T.base.z', ∃ g : B.Mat P.k (P.r - P.r),
      g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) ∧ 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g ∧
      x.2 = D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) ∧
    ∀ γ : B.Mat P.k (P.r - P.r), γ ∈ B.GV P.k (P.r - P.r) ↔ γ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _)

def ZxDet : Prop :=
  ∀ (r : ℕ) (h : C.LPt) (hh : D.IsLocPt h r) (v : PBQ.XH h), (PBQ.zxH h r hh.2 v).det ≠ 0

def HeadFam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (f : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp)),
    PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') f →
    ∀ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K →
      K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
      (∀ q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → f q ≠ 0 →
        ∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K) →
      PBI.ParFam P.k (P.r - P.r)
        (Set.univ ×ˢ {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)})
        (fun q : PBQ.XH h × Mt P.k (P.r - P.r) => PBQ.ellH h q.1 (f (PBQ.zxH h P.r hh.2 q.1, q.2))) ∧
      ∃ Kp : Set (PBQ.XH h), IsCompact Kp ∧ ∀ v ∉ Kp, ∀ y : Mt P.k (P.r - P.r),
        Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → f (PBQ.zxH h P.r hh.2 v, y) = 0

def RadSliceTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
          (p.T.bs P.r).π',
        Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) Ψ
          (D.castF (by rw [hh.2]; rfl) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h))

section mx

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def RadOfFun : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Q.Mx k ρ → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)) (f : Q.Mx k ρ → (Wq →L[ℂ] Wp)),
    (∀ g₀, g₀ ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' g₀ → ∃ (U : Set (Q.Mx k ρ)) (F : Q.Mx k ρ → (Wq →L[ℂ] Wp)),
      IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ Q.Glev k ρ (Fin.last ρ) → f g = F g) →
    (∀ g, g ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' g → ∀ h ∈ UWset k ρ z, ∀ h' ∈ UWset k ρ z',
      f (h * g * h') = (π h).comp ((f g).comp (π' h'))) →
    ∃ Ψ : Q.RadSp k ρ z z' π π', ∀ x ∈ Q.DomR k ρ z z', (Ψ : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2 = f x.2

end mx

def RadExt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Q.Mx k ρ → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)) (Ψ Ψ' : Q.RadSp k ρ z z' π π'),
    (∀ x ∈ Q.DomR k ρ z z', (Ψ : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2 = (Ψ' : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2) → Ψ = Ψ'

def ResTop : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k ρ : ℕ), ρ = 0 →
    ∀ (J : Q.Mx k ρ → E) (c : Fin ρ → ℂ) (g : Q.Mx k ρ), Q.resG k ρ (Fin.last ρ) J c g = J g

def Asm : Prop :=
  UwTop → SliceTop → PbSmooth → PbRight → PbSupp → PbEquiv → MkTop → MkCpt → TopPt → ZxDet → HeadFam → RadSliceTop →
    RadOfFun → RadExt → ResTop → PBI.FrameParam → PBI.RadWordSlice → PBI.PicSlice → PBI.ExhPic

theorem exhPic_of_leaves (hA : Asm) (h1 : UwTop) (h2 : SliceTop) (h3 : PbSmooth) (h3' : PbRight) (h4 : PbSupp) (h5 : PbEquiv)
    (h6 : MkTop) (h7 : MkCpt) (h8 : TopPt) (h9 : ZxDet) (h10 : HeadFam) (h11 : RadSliceTop) (h12 : RadOfFun)
    (h13 : RadExt) (h14 : ResTop) (hFP : PBI.FrameParam) (hRW : PBI.RadWordSlice) (hPS : PBI.PicSlice) :
    PBI.ExhPic :=
  hA h1 h2 h3 h3' h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hFP hRW hPS

end Formalism.FourierDecayAlt.P.CutEX
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHL2
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

section defs

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Hyp (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) : Prop :=
  inWb k r z ∧ inWb k r z' ∧ IsOpen Dm ∧ Dm ⊆ domJ k r j hj z z' ∧ RulesOn k r j hj z z' Dm Φ ∧
    Z.det ≠ 0 ∧ τ ≠ 0 ∧ γ ∈ B.GV k (r - (j + 1)) ∧ x0 k r j hj Z τ γ ∈ Dm

def Eq1 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (true, Y) 0 Φ (x0 k r j hj Z τ γ) =
    ((Y : ℂ) + levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ) +
      τ • PBP.dz (fun τ' => D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
      τ • D.vLet k r z z' j (by omega) (true, Y) 1 Φ (x0 k r j hj Z τ γ)

def Eq2 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (true, Y) 1 Φ (x0 k r j hj Z τ γ) =
    τ⁻¹ • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ)

def Eq3 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (false, Y) 0 Φ (x0 k r j hj Z τ γ) =
    ((Y : ℂ) - levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ) -
      conj τ • PBP.dzb (fun τ' => D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
      conj τ • D.vLet k r z z' j (by omega) (false, Y) 1 Φ (x0 k r j hj Z τ γ)

def Eq4 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (false, Y) 1 Φ (x0 k r j hj Z τ γ) =
    (conj τ)⁻¹ • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ)

end defs

def Comp1 : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq2 k r j hj z z' Φ Z γ τ Y ∧ Eq4 k r j hj z z' Φ Z γ τ Y

def PlusPos : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), 1 ≤ j → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq1 k r j hj z z' Φ Z γ τ Y

def PlusZero : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), j = 0 → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq1 k r j hj z z' Φ Z γ τ Y

def MinusPos : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), 1 ≤ j → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq3 k r j hj z z' Φ Z γ τ Y

def MinusZero : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), j = 0 → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq3 k r j hj z z' Φ Z γ τ Y

theorem headLetter_of (h1 : Comp1) (hPP : PlusPos) (hPZ : PlusZero) (hMP : MinusPos) (hMZ : MinusZero) :
    LevelPointCoordinates.HeadLetter := by
  intro k r j hj z z' E _ _ Dm Φ hz hz' hD hDs hR Z γ τ hZ hτ hγ hx Y
  have hH : Hyp k r j hj z z' Dm Φ Z γ τ := ⟨hz, hz', hD, hDs, hR, hZ, hτ, hγ, hx⟩
  obtain ⟨c2, c4⟩ := h1 k r j hj z z' E Dm Φ Z γ τ hH Y
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · exact ⟨hPZ k r j hj z z' E Dm Φ Z γ τ h0 hH Y, c2, hMZ k r j hj z z' E Dm Φ Z γ τ h0 hH Y, c4⟩
  · exact ⟨hPP k r j hj z z' E Dm Φ Z γ τ hpos hH Y, c2, hMP k r j hj z z' E Dm Φ Z γ τ hpos hH Y, c4⟩

def NormalFormsAtBasePoint : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1))),
    Z.det ≠ 0 → τ ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < j + 1 →
      PBG.xi0 (x0 k r j hj Z τ γ) a p = if p.val < j + 1 then C3.Zb j 1 Z τ a.val p.val else 0) ∧
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < j + 1 →
      PBG.y0 (x0 k r j hj Z τ γ) a p =
        if r + k < p.val ∧ 2 * r + k - p.val < j + 1 then star (C3.Zb j 1 Z τ a.val (2 * r + k - p.val)) else 0)

def LeadingMinorsAtBasePoint : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    Dmin k r z z' (x0 k r j hj Z τ γ) ⟨j, by omega⟩ = Z.det ∧
      Dmin k r z z' (x0 k r j hj Z τ γ) ⟨j + 1, by omega⟩ = Z.det * τ

def LeftActionRuleAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), 1 ≤ j → inWb k r z → IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    (∀ a : Fin j → ℂ, Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ)) →
    ∀ b : Fin j, Q.EH k r (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      (τ * Z⁻¹ b ⟨j - 1, by have := b.isLt; omega⟩) • Ψ (x0 k r j hj Z τ γ)

def TorusDirectionAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    Q.EH k r (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      τ • PBP.dz (fun τ' => Ψ (x0 k r j hj Z τ' γ)) τ

def ConjugateActionRuleAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), 1 ≤ j → inWb k r z → IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    (∀ a : Fin j → ℂ, Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ)) →
    ∀ b : Fin j, Q.EH k r (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      (conj τ * conj (Z⁻¹ b ⟨j - 1, by have := b.isLt; omega⟩)) • Ψ (x0 k r j hj Z τ γ)

def ConjugateTorusDirectionAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    Q.EH k r (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      -(conj τ • PBP.dzb (fun τ' => Ψ (x0 k r j hj Z τ' γ)) τ)

def FrozenX : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (Z : Matrix (Fin j) (Fin j) ℂ) (τ τ' u : ℂ)
    (γ : B.Mat k (r - (j + 1))), GlRel Eu → Z.det ≠ 0 → τ ≠ 0 → τ' ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ' γ)) j (by omega) u =
        C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u ∧
      Eu (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩) * C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u =
        C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u * Eu (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩)

def FrozenV : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (Z : Matrix (Fin j) (Fin j) ℂ) (τ τ' ℓ : ℂ)
    (γ : B.Mat k (r - (j + 1))), GlRel Eu → Z.det ≠ 0 → τ ≠ 0 → τ' ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ' γ)) j (by omega) ℓ =
        C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ ∧
      Eu (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩) * C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ =
        C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ * Eu (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩)

def Comp1OfParts : Prop := NormalFormsAtBasePoint → Comp1

def PlusPosOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → LeftActionRuleAtBasePoint → TorusDirectionAtBasePoint → FrozenX → PlusPos

def PlusZeroOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → TorusDirectionAtBasePoint → PlusZero

def MinusPosOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → ConjugateActionRuleAtBasePoint → ConjugateTorusDirectionAtBasePoint → FrozenV → MinusPos

def MinusZeroOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → ConjugateTorusDirectionAtBasePoint → MinusZero

theorem headLetter_of_leaves (hNf : NormalFormsAtBasePoint) (hDm : LeadingMinorsAtBasePoint) (hL : LeftActionRuleAtBasePoint) (hT : TorusDirectionAtBasePoint) (hSL : ConjugateActionRuleAtBasePoint)
    (hST : ConjugateTorusDirectionAtBasePoint) (hFX : FrozenX) (hFV : FrozenV) (h1 : Comp1OfParts) (hPP : PlusPosOfParts)
    (hPZ : PlusZeroOfParts) (hMP : MinusPosOfParts) (hMZ : MinusZeroOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of (h1 hNf) (hPP hNf hDm hL hT hFX) (hPZ hNf hDm hT) (hMP hNf hDm hSL hST hFV) (hMZ hNf hDm hST)

end Formalism.FourierDecayAlt.P.CutHL
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrpAll
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem tVGrp_of (hRR : RightRuleEv) (hLR : LeftRuleCellv) (hTC : TorusCellv) (hCh : MirrorChainExpansion) : TVGrp := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  have hGG := JDAToda.gg_pos Bs hc hg hcg
  have hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, hGG⟩
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  rw [JDAToda.omB_eq] at hf hLf hRf
  set D := OmPlus P.k P.r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  have h1N : (1 : Mx P.k P.r) ∈ Nlev P.k P.r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds P.k P.r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev P.k P.r 0 ∩ D, ∀ n ∈ Nlev P.k P.r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := P.k) (r := P.r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS P.k P.r 0 D (Wq →L[ℂ] Wp) := ⟨cut P.k P.r 0 D J, cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c * g ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs (c, g) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c * g ∈ Glev P.k P.r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hcl := claimV hRR hLR hTC hCh hD v₀ g (kvTop P.k P.r y) Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hg
    hcell P.r le_rfl 1 (Subalgebra.one_mem _) c hc
  rw [mul_one] at hcl
  have eR : kvC P.r (kvTop P.k P.r y) P.r (fun c' => J (wCell P.k P.r (Fin.last P.r) c' * g)) c =
      kvC P.r (kvTop P.k P.r y) P.r (fun c' => La hD v₀ (wCell P.k P.r (Fin.last P.r) c' * g) 1) c :=
    kvC_loc _ _ _ _ (fun c' hc' => (cut_of_mem _ (hcell c' hc')).symm) hc
  rw [eR, ← hcl, La_apply]
  have hγ := hcell c hc
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (colsVm P.k P.r P.r) (colsVm P.k P.r P.r) (kvTop P.k P.r y) :
      SA (Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS P.k P.r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ colsVm P.k P.r P.r) (cI ∘ colsVm P.k P.r P.r)
        (kvTop P.k P.r y) := by
    have := map_qminor (SA (Wq →L[ℂ] Wp) hD).val (EA hD) (colsVm P.k P.r P.r) (colsVm P.k P.r P.r) (kvTop P.k P.r y)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL P.k P.r 0 ∘ (cI ∘ colsVm P.k P.r P.r) = colsVm P.k P.r P.r := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ colsVm P.k P.r P.r) (cI ∘ colsVm P.k P.r P.r)
    (kvTop P.k P.r y)).loc (cut P.k P.r 0 D J) J (fun x' hx' => cut_of_mem _ hx') _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

theorem toda_group_action_holds : TVGrp :=
  tVGrp_of mirror_right_rule_holds mirror_left_rule_cell_holds mirror_torus_cell_holds mirror_chain_expansion_holds

end Formalism.FourierDecayAlt.P.CutMP.TVG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Lam1
section
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

def qU : ℝ := ((Real.toNNReal (‖U.betaU‖ / (2 * Real.pi)) : NNReal) : ℝ)

section pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lam1 (S : C.HidaSetting E Wp Wq) (s : ℕ) : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ s : ℝ) : ℂ) * Complex.I ^ (s - 2)

def lam2 (S : C.HidaSetting E Wp Wq) (s : ℕ) : ℂ :=
  ((((S.g : ℝ) / (2 * Real.pi)) ^ (s - 1) : ℝ) : ℂ) * Complex.I ^ (s - 1)

def omN (S : C.HidaSetting E Wp Wq) (N : ℕ) (P : C.LPt) : ℝ :=
  √(PBL.nnS S P) / PBL.bS S P * √(Top.wPt (S.T * S.T') S.G.r (PBL.stdS S P) ^ N)

end pts

end

end Formalism.FourierDecayAlt.P.GermRateSplit
end

