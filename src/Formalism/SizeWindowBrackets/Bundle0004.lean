module

public import Formalism.SizeWindowBrackets.Bundle0002
public import Formalism.SizeWindowBrackets.Bundle0003
public import Formalism.HarderNarasimhan.Bundle0001
public import Formalism.SizeWindowBrackets.Bundle0001
public import Mathlib

@[expose] public section

-- bundled from Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
section
open Real

namespace Formalism.LFunctionChainParameters.LErr

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds

noncomputable section

section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}

def ErrText (D : Data U0 W Top m f) : ℝ :=
  D.nT * D.a * (1 + (m : ℝ) ^ 2 / D.k) + (m : ℝ) * (D.B0 + D.Nc)

def CErr (C : Consts) : ℝ := C.eDiv + C.eLoss + 3

def KBig (K cHH eK : ℝ) : ℝ := 200 * (1 + K) ^ 2 * (1 + cHH) * (1 + eK)

def ConstsBound (C : Consts) (K : ℝ) : Prop :=
  0 ≤ C.cDiv ∧ C.cDiv ≤ K ∧ 0 ≤ C.cE ∧ C.cE ≤ K ∧ 0 ≤ C.cH ∧ C.cH ≤ K ∧
  0 ≤ C.cCount ∧ C.cCount ≤ K ∧ 0 ≤ C.cSlope ∧ C.cSlope ≤ K ∧ 0 ≤ C.cSl1 ∧ C.cSl1 ≤ K ∧
  0 ≤ C.cLoss ∧ C.cLoss ≤ K ∧ 0 ≤ C.eDiv ∧ 0 ≤ C.eLoss ∧ 0 ≤ C.cHH

def ErrWindows0 (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ) : Prop :=
  1 ≤ D.x ∧ 0 < D.ε ∧ D.ε ≤ 1 ∧
  1 ≤ D.b ∧ D.x * D.b ≤ D.a ∧
  1 ≤ D.nT ∧
  (m : ℝ) ≤ D.x ^ ((1 : ℝ) / 2 + D.ε / 2) ∧ D.x * m ≤ D.k ∧
  0 ≤ eK ∧ 1 ≤ D.k ∧ D.k ≤ D.x ^ eK ∧ D.k ≤ D.a ∧
  0 ≤ D.L ∧ D.L ≤ 2 * D.x ^ D.ε ∧ 0 ≤ D.La ∧ D.La ≤ 2 * D.x ^ D.ε ∧
  0 ≤ D.b' ∧ D.k * D.b' ≤ D.a ∧
  0 ≤ Xpp ∧ Xpp ≤ D.a ∧
  (∀ t, 0 ≤ D.aT t ∧ D.aT t ≤ 2 * D.a) ∧
  0 ≤ D.B0 ∧ 0 ≤ D.Nc ∧
  (∀ u0, Real.log (Fintype.card (W u0) : ℝ) ≤ (D.k - 3) * Real.log 2) ∧
  D.delBar ≤ 1 / 2 ∧ 0 ≤ D.etaBar ∧ 0 ≤ D.eBar ∧
  ConstsBound C K

def ErrWindows (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ) : Prop :=
  ErrWindows0 D C Xpp eK K ∧
  (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) ≤ K * D.x ^ D.ε * (D.nT * D.a)

end

def LargeX (x ε K cHH eK : ℝ) : Prop := Real.log x ≤ x ^ ε ∧ KBig K cHH eK ≤ x ^ ε

def LargeXEv : Prop :=
  ∀ ε K cHH eK : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → LargeX x ε K cHH eK

def bTx (x ε : ℝ) : ℝ := Real.exp (x ^ ε)

def aTx (x ε : ℝ) : ℝ := x * bTx x ε

def XpTx (x ε : ℝ) : ℝ := Real.exp (x ^ (ε / 3))

def bpTx (x ε : ℝ) : ℝ := aTx x ε / XpTx x ε

def wppTx (x ε n : ℝ) : ℝ := bpTx x ε / (x * n)

def XppTx (x ε n : ℝ) : ℝ := aTx x ε / wppTx x ε n

section
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def errorBracketSizeWindows (x ε : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : ℝ :=
  (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
    + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))

end

end

end Formalism.LFunctionChainParameters.LErr
end

-- bundled from Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv
section
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates

open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)

def KpG {I α : Type} [Fintype α] {ι : I → Type} (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i j : I) :
    Matrix (ι i) (ι j) ℂ :=
  ((Real.sqrt (ga i * ga j) : ℝ) : ℂ) • ((B i)ᴴ * B j)

def KdG {I α : Type} [Fintype α] {ι : I → Type} (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i : I) :
    Matrix (ι i) (ι i) ℂ :=
  KpG B ga i i

def QmG {I α : Type} [Fintype I] {ι : I → Type} [∀ i, Fintype (ι i)] (B : ∀ i, Matrix α (ι i) ℂ)
    (ga : I → ℝ) : Matrix α α ℂ :=
  ∑ i, ((ga i : ℝ) : ℂ) • (B i * (B i)ᴴ)

def RsG {I : Type} [Fintype I] (ι : I → Type) [∀ i, Fintype (ι i)] : ℝ :=
  ∑ i, (Fintype.card (ι i) : ℝ)

def InputSG {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (Dstar η0 η1 e0 : ℝ) : Prop :=
  (∀ i j, i ≠ j → hsSq (KpG B ga i j)
      ≤ (1 + η0) * (Fintype.card (ι i) : ℝ) * (Fintype.card (ι j) : ℝ) / Dstar) ∧
  (∀ i, hsSq (KdG B ga i - 1) ≤ e0 * (Fintype.card (ι i) : ℝ)) ∧
  (Fintype.card α : ℝ) ≤ (1 + η1) * Dstar

def toFin {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) :
    ∀ i, Matrix (Fin (Fintype.card α)) (Fin (Fintype.card (ι i))) ℂ :=
  fun i => Matrix.reindex (Fintype.equivFin α) (Fintype.equivFin (ι i)) (B i)

def toFinV {I : Type} {ιf ι : I → Type} [∀ i, Fintype (ιf i)] [∀ i, Fintype (ι i)]
    (V : ∀ i, Matrix (ιf i) (ι i) ℂ) :
    ∀ i, Matrix (Fin (Fintype.card (ιf i))) (Fin (Fintype.card (ι i))) ℂ :=
  fun i => Matrix.reindex (Fintype.equivFin (ιf i)) (Fintype.equivFin (ι i)) (V i)

def FrameDeviationLinear {I α : Type} [Fintype I] [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (e : ℝ) : Prop :=
  (∑ i, hs2 (frK (ga i) (Matrix.toEuclideanLin (B i)) - LinearMap.id)) ≤
    e * ∑ i, (Fintype.card (ι i) : ℝ)

def FrameTraceRatioLinear {I α : Type} [Fintype I] [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (η : ℝ) : Prop :=
  (LinearMap.trace ℂ (EuclideanSpace ℂ α)
      (frQ ga (fun i => Matrix.toEuclideanLin (B i)) ∘ₗ
       frQ ga (fun i => Matrix.toEuclideanLin (B i)))).re ≤
    (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ α)
      (frQ ga (fun i => Matrix.toEuclideanLin (B i)))).re ^ 2 / (Fintype.card α : ℝ)

def LatGeom {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (δ : ℝ) : Prop :=
  (∀ w, IsUnit (X' w).det) ∧ (∀ i w, IsUnit (X i w).det) ∧ (∀ i, IsUnit (Y i).det) ∧
  IsUnit Y'.det ∧
  cc.FG ∧ Submodule.span K (cc : Set W) = ⊤ ∧
  (∀ i, (N i).FG) ∧ (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) ∧
  0 < ∑ i, Fintype.card (ι i) ∧ (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) ∧
  (∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i) ∧
  0 ≤ δ ∧ δ < 1 ∧ (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ) ∧
  (∀ i (k : κ) (j : ι i),
    Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j)

def LatNum {K W κ I : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (h : I → ℝ) (s u HH : ℝ) : Prop :=
  s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
    ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i) ∧
  0 ≤ u ∧ (∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ s + u) ∧
  s - muMinDef b' X' cc ≤ HH ∧ 0 ≤ HH

def BridgeHS : Prop :=
  ∀ (I α : Type) [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i : I), 0 ≤ ga i →
    hs2 (frK (ga i) (Matrix.toEuclideanLin (B i)) - LinearMap.id) = hsSq (KdG B ga i - 1)

def BridgeQ : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] [DecidableEq α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ),
    LinearMap.trace ℂ (EuclideanSpace ℂ α) (frQ ga (fun i => Matrix.toEuclideanLin (B i)))
      = (QmG B ga).trace ∧
    LinearMap.trace ℂ (EuclideanSpace ℂ α)
      (frQ ga (fun i => Matrix.toEuclideanLin (B i)) ∘ₗ
       frQ ga (fun i => Matrix.toEuclideanLin (B i))) = (QmG B ga * QmG B ga).trace

def BridgeFin : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ),
    (∀ i j, hsSq (HilbertSchmidtNormSquare.Kp (toFin B) ga i j) = hsSq (KpG B ga i j)) ∧
    (∀ i, hsSq (HilbertSchmidtNormSquare.Kd (toFin B) ga i - 1) = hsSq (KdG B ga i - 1)) ∧
    (HilbertSchmidtNormSquare.Qm (toFin B) ga).trace = (QmG B ga).trace ∧
    (HilbertSchmidtNormSquare.Qm (toFin B) ga * HilbertSchmidtNormSquare.Qm (toFin B) ga).trace = (QmG B ga * QmG B ga).trace ∧
    HilbertSchmidtNormSquare.Rs (fun i => Fintype.card (ι i)) = RsG ι

def BridgeInputS : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (Dstar η0 η1 e0 : ℝ),
    HilbertSchmidtNormSquare.InputS (toFin B) ga Dstar η0 η1 e0 ↔ InputSG B ga Dstar η0 η1 e0

def BridgeRam : Prop :=
  ∀ (I α : Type) [Fintype α] (ιf ι : I → Type) [∀ i, Fintype (ιf i)] [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (Bf : ∀ i, Matrix α (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ),
    toFin (fun i => Bf i * Vr i) = HilbertSchmidtNormSquare.Bram (toFin Bf) (toFinV Vr) ∧
    (HilbertSchmidtNormSquare.Isom (toFinV Vr) ↔ ∀ i, (Vr i)ᴴ * Vr i = 1)

def FrameTraceRatioFinEquiv : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (η : ℝ),
    HilbertSchmidtNormSquare.F1 (toFin B) ga η ↔ FrameTraceRatioLinear B ga η

def FrameDeviationFinEquiv : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (e : ℝ), (∀ i, 0 ≤ ga i) →
    (HilbertSchmidtNormSquare.F2 (toFin B) ga e ↔ FrameDeviationLinear B ga e)

def BridgeConcl : Prop :=
  ∀ s mu logI δ u HH η e : ℝ,
    (s - logI - (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) ≤ mu) ↔
      PhiMonotonicityLemmas.ConclF s mu logI δ u HH η e

def CorLin : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ι : I → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (Dstar sg η0 η1 e0 : ℝ),
    (∀ i, 0 ≤ ga i) → 0 < Dstar → 0 < sg → sg ≤ 1 / 4 → Dstar / sg ≤ RsG ι →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    InputSG B ga Dstar η0 η1 e0 →
    FrameTraceRatioLinear B ga (5 * sg) ∧ FrameDeviationLinear B ga e0 ∧ e0 ≤ 1 / 4 ∧ 0 < ∑ i, Fintype.card (ι i)

def RamLin : Prop :=
  ∀ (I α : Type) [Fintype I] [Fintype α] (ιf ι : I → Type) [∀ i, Fintype (ιf i)]
    [∀ i, DecidableEq (ιf i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (Bf : ∀ i, Matrix α (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ) (ga : I → ℝ)
    (Dstar sg η0 η1 e0 de : ℝ),
    (∀ i, (Vr i)ᴴ * Vr i = 1) → (∀ i, 0 ≤ ga i) → 0 < Dstar → 0 < sg → sg ≤ 1 / 20 →
    Dstar / sg ≤ RsG ιf → -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf ga Dstar η0 η1 e0 →
    FrameTraceRatioLinear (fun i => Bf i * Vr i) ga (5 * sg + 3 * Real.sqrt de) ∧
    FrameDeviationLinear (fun i => Bf i * Vr i) ga (2 * e0) ∧ 2 * e0 ≤ 1 / 4 ∧ 0 < ∑ i, Fintype.card (ι i)

def TheoremFLat : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH e η δ : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → FrameDeviationLinear Ball γ e → 0 ≤ e → e ≤ 1 / 4 → FrameTraceRatioLinear Ball γ η → 0 ≤ η →
    s - Real.log (Fintype.card I : ℝ) -
        (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) ≤ muDef b' X' cc

def JointARam : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u HH δ Dstar sg η0 η1 e0 de : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    s - Real.log (Fintype.card I : ℝ) -
        (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u)
          + ((5 * sg + 3 * Real.sqrt de) + 4 * Real.sqrt (2 * e0)) * HH)
      ≤ muDef b' X' cc

def WordsR : Prop :=
  ∀ (I : Type) [Fintype I] (ιf : I → Type) [∀ i, Fintype (ιf i)] (Dstar sg C0 Gam : ℝ),
    0 < Dstar → 0 < sg → 0 < C0 → 0 < Gam → C0 * Gam ^ 2 / sg ≤ (Fintype.card I : ℝ) →
    (∀ i, Dstar * (Gam ^ 2)⁻¹ / C0 ≤ (Fintype.card (ιf i) : ℝ)) → Dstar / sg ≤ RsG ιf

end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
end
end

-- bundled from Formalism.SizeWindowBrackets.LcvBaseChange
section
open Module NumberField

noncomputable section

namespace Formalism.LFunctionChainParameters.LLcv

open Formalism.HN

section Defs

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

def lcvInf (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) {j : ℕ} (e : Fin j → V) : ℝ :=
  (1 / (nPl K : ℝ)) * ∑ v, Real.log (gramPl b X v e).det.re

def lcvFin {j : ℕ} (e : Fin j → V) (M : Submodule (𝓞 K) V) : ℝ :=
  2 * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
    (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) *
      (haveI := p.2.isPrime; (Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ))

def lcv (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) {j : ℕ} (e : Fin j → V)
    (M : Submodule (𝓞 K) V) : ℝ :=
  lcvInf b X e + lcvFin e M

end Defs

def LcvMu : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V) (M : Submodule (𝓞 K) V), LinearIndependent K e → M.FG → M ≠ ⊥ →
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e) →
      rkK M = j ∧ 0 < j ∧
      (∀ v, 0 < (gramPl b X v e).det.re ∧ (gramPl b X v e).det.im = 0) ∧
      (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; Formalism.HermitianLatticesTheory.lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M)).Finite ∧
      muDef b X M = -lcv b X e M / (rkK M : ℝ)

def LcvExists : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V),
    ∃ (j : ℕ) (e : Fin j → V), LinearIndependent K e ∧ (∀ a, e a ∈ M) ∧
      Submodule.span K (M : Set V) = Submodule.span K (Set.range e)

def LcvFree : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (j : ℕ) (e : Fin j → V), LinearIndependent K e → 0 < j →
      lcvFin e (Submodule.span (𝓞 K) (Set.range e)) = 0 ∧
      muDef b X (Submodule.span (𝓞 K) (Set.range e)) = -lcvInf b X e / (j : ℝ)

def LcvIdeal : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (_b : Basis ι K V) (j : ℕ) (e : Fin j → V)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), LinearIndependent K e → 0 < j → I ≠ 0 →
      lcvFin e (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K)
        (Submodule.span (𝓞 K) (Set.range e))) =
        2 * (j : ℝ) * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)

def IndexLocLen : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V), B ≤ A → B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 →
      (∀ p : {p : Ideal (𝓞 K) // p.IsMaximal}, (haveI := p.2.isPrime;
        Module.length (𝓞 K) ((Formalism.HermitianLatticesTheory.localization₂ p.1 A) ⧸
          (Formalism.HermitianLatticesTheory.localization₂ p.1 B).comap (Formalism.HermitianLatticesTheory.localization₂ p.1 A).subtype)) ≠ ⊤) ∧
      (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; Formalism.HermitianLatticesTheory.locLen p.1 A B)).Finite ∧
      Real.log (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
        ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, Real.log (Ideal.absNorm p.1 : ℝ) *
          (haveI := p.2.isPrime; (Formalism.HermitianLatticesTheory.locLen p.1 A B : ℝ))

end Formalism.LFunctionChainParameters.LLcv
end
end

