module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.Bundle0008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0027
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0015
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0016

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeC
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

private theorem contDiffOn_ann_of_wirt_fnZ_eq (P : M.Par) {u : ℂ → ℂ} (w : M.Var P.r) (F : ℂ → ℂ)
    (hF : ∀ q : MA.Qp P.r P.TT,
      MA.wirt w (MA.ext ((fnZ P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = F q.1.2) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Ann P) := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (MA.wirt w (MA.ext ((fnZ P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ))) (MA.Qset P.r P.TT) :=
    MA.wirt_smooth (fnZ P u).2 w
  let ι : ℂ → MA.E P.r := fun ζ => ((fun _ => (1 : ℂ)), ζ)
  have hι : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ι := contDiff_const.prodMk contDiff_id
  have hmap : Set.MapsTo ι (Ann P) (MA.Qset P.r P.TT) := fun ζ hζ => ⟨fun _ => one_ne_zero, hζ⟩
  refine (hs.comp hι.contDiffOn hmap).congr fun ζ hζ => ?_
  exact (hF ⟨ι ζ, hmap hζ⟩).symm

theorem dZ_smooth (P : M.Par) {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (Ann P)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZ u) (Ann P) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZb u) (Ann P) :=
  ⟨contDiffOn_ann_of_wirt_fnZ_eq P M.vz _ fun q => wirtinger_derivative_fibre_function P hu q, contDiffOn_ann_of_wirt_fnZ_eq P M.vzb _ fun q => wirt_fnZ_zb P hu q⟩

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem connF_phase (P : M.Par) (hTT : 0 ≤ P.TT) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A B u : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hC : ConnF P Bs d e A B)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) :
    SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ) (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) ∧
      ConnF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
        (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := by
  have hSm : SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
      (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := fun ρ =>
    ⟨(hAB ρ).1.add ((conj_smooth (hu ρ).1).mul (dZ_smooth P (hu ρ).1).1),
      (hAB ρ).2.sub ((conj_smooth (hu ρ).1).mul (dZ_smooth P (hu ρ).1).2)⟩
  refine ⟨hSm, ?_⟩
  intro Φ ρ
  have hc := conj_smooth (hu ρ).1
  rw [trR_phase P Bs e u hu, trR_phase P Bs e u hu, trR_phase P Bs e u hu, (hC Φ ρ).1, (hC Φ ρ).2]
  set g := trR P Bs e Φ ρ
  constructor
  · apply Subtype.ext
    funext q
    have hq : q.1.2 ∈ Ann P := q.2.2
    have e1 : ((dzQ P (fnZ P (fun ζ => star (u ρ ζ)) * g) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        NF.dZ (fun ζ => star (u ρ ζ)) q.1.2 * (g : MA.Qp P.r P.TT → ℂ) q +
          star (u ρ q.1.2) * MA.wirt M.vz (MA.ext (g : MA.Qp P.r P.TT → ℂ)) q.1 := by
      rw [dzQ_apply P hTT, wirtQ_mul, wirtinger_derivative_fibre_function P hc, fnZ_val P hc]
    simp only [MulMemClass.coe_mul, AddMemClass.coe_add, Pi.mul_apply, Pi.add_apply]
    rw [e1, dzQ_apply P hTT, fnZ_val P hc, fnZ_val P (hAB ρ).1, fnZ_val P (hSm ρ).1,
      (dZ_conj_unit P (hu ρ).1 (hu ρ).2 hq).1]
    ring
  · apply Subtype.ext
    funext q
    have hq : q.1.2 ∈ Ann P := q.2.2
    have e1 : ((dzbQ P (fnZ P (fun ζ => star (u ρ ζ)) * g) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        NF.dZb (fun ζ => star (u ρ ζ)) q.1.2 * (g : MA.Qp P.r P.TT → ℂ) q +
          star (u ρ q.1.2) * MA.wirt M.vzb (MA.ext (g : MA.Qp P.r P.TT → ℂ)) q.1 := by
      rw [dzbQ_apply P hTT, wirtQ_mul, wirt_fnZ_zb P hc, fnZ_val P hc]
    simp only [MulMemClass.coe_mul, AddMemClass.coe_add, NegMemClass.coe_neg, Pi.mul_apply,
      Pi.add_apply, Pi.neg_apply]
    rw [e1, dzbQ_apply P hTT, fnZ_val P hc, fnZ_val P (hAB ρ).2, fnZ_val P (hSm ρ).2,
      (dZ_conj_unit P (hu ρ).1 (hu ρ).2 hq).2]
    ring


end main

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

section K

variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]

def Kset (k r : ℕ) (z b : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (f : ℂ → ℂ) : Set Wp :=
  {x | ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, b] Fr → ∀ w : ℂ, capRep k r π Fr w x = f w • x}

def K (k r : ℕ) (z b : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (f : ℂ → ℂ) : Submodule ℂ Wp :=
  Submodule.span ℂ (Kset k r z b π f)

end K

def FrameLoc : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 2 ≤ k → inWb k r z → 0 < Tz k r z →
    ∀ a₀ : Fin (2 * r + k + 1) → ℂ, 0 < PRho.nrmW k r z a₀ →
      ∃ Fr : (Fin (2 * r + k + 1) → ℂ) → Fin (k - 1) → Fin (2 * r + k + 1) → ℂ,
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fr a₀ ∧ ∀ᶠ a in 𝓝 a₀, IsFrameOf k r [z, SSn.prWv k r z a] (Fr a)

def CapSmooth : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (k r m : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)), Qr.IsRepW k r z π → ∀ w : ℂ,
    ∃ C : (Fin m → Fin (2 * r + k + 1) → ℂ) → (Wp →L[ℂ] Wp), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C ∧
      ∀ Bs, IsFrameOf k r [z] Bs → ∀ v, C Bs v = capRep k r π Bs w v

def EigOrth : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (k r : ℕ)
    (z e : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Qr.IsRepW k r z π →
    (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) →
    (∃ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, e] Fr) →
    ∀ (f g : ℂ → ℂ) (x y : Wp), x ∈ Kset k r z e π f → y ∈ Kset k r z e π g → (∃ w, f w ≠ g w) → inner ℂ x y = 0

def Lagrange : Prop :=
  EigOrth → ∀ (P : M.Par), P.OK → 2 ≤ P.k → ∃ (w : ℂ) (p : M.Ty P → Polynomial ℂ),
    ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      (z e : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)),
      inWb P.k P.r z → 0 < Tz P.k P.r z → IsType P.k P.r z π P.u →
      inWb P.k P.r e → herm (Hpk P.k P.r) e z = 0 → herm (Hpk P.k P.r) e e = 1 →
      ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, IsFrameOf P.k P.r [z, e] Fr →
      ∀ C : Wp →L[ℂ] Wp, (∀ v, C v = capRep P.k P.r π Fr w v) →
      ∀ ρ : M.Ty P, Polynomial.aeval C (p ρ) =
        (K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2))).starProjection

def Assembly : Prop := FrameLoc → CapSmooth → EigOrth → Lagrange → PRho.PRhoExists

theorem pRhoExists_of_cut (hA : Assembly) (hF : FrameLoc) (hC : CapSmooth) (hO : EigOrth) (hL : Lagrange) :
    PRho.PRhoExists :=
  hA hF hC hO hL

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCore
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def ActHyp (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) : Prop :=
  Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' ∧ Q.IsActualLevel X d.L ∧ Fr.IsStarLevel d.L ∧ d.Rel ∧ ∀ Y : ℂ, X.QQ Y = d.QQ Y

def GQQ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
    Gauge.FamR P Bs Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ

def IsSSPt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (l : ℕ) (S : ℂ → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) : Prop :=
  ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r → ∀ ζ ∈ Gauge.GC.Ann P,
    ((d.SS l).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      S ζ ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))

end preds

def GQQSSF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e → GQQ P Bs e → Gauge.GC.SSF P Bs d e

def SSPointwise : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∃ S, IsSSPt P Bs d l S

def ThConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∃ θ : M.Ty P → ℂ, ∀ ζ ∈ Gauge.GC.Ann P, ∀ π ρ : M.Ty P, M.Up P l π ρ →
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          θ π • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def SSEntry : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e → Gauge.GC.SSF P Bs d e →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S → ∀ ζ ∈ Gauge.GC.Ann P, ∀ π ρ : M.Ty P,
      inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (S ζ (e π ζ))) =
        if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0

def ThtGaugeConstOfCore : Prop :=
  GQQSSF → SSPointwise → ThConst → SSEntry → PRho.PRhoExists → PRho.GaugeLines → DatumUnit → ThtGaugeConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

namespace DU

variable {k r : ℕ}

theorem hadd_l {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (x y w : Fin m → ℂ) :
    herm H (x + y) w = herm H x w + herm H y w := by
  simp [herm, Matrix.mulVec_add]

theorem hadd_r {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (x w w' : Fin m → ℂ) :
    herm H x (w + w') = herm H x w + herm H x w' := by
  simp [herm, add_dotProduct]

theorem hsmul_l {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (x w : Fin m → ℂ) :
    herm H (c • x) w = c * herm H x w := by
  simp [herm, Matrix.mulVec_smul]

theorem hsmul_r {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (x w : Fin m → ℂ) :
    herm H x (c • w) = conj c * herm H x w := by
  simp [herm, smul_dotProduct, Complex.star_def]

private theorem herm_swap_eq_zero_of_eq_zero {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : ∀ i j, H i j = star (H j i))
    (v w : Fin m → ℂ) : herm H w v = conj (herm H v w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hH b a]
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_conj]
  ring

private theorem Hpk_apply_eq_star_apply_swap : ∀ i j : Fin (2 * r + k + 1), Hpk k r i j = star (Hpk k r j i) := by
  intro i j
  simp only [Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | (exfalso; omega)

theorem hswap (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) w v = conj (herm (Hpk k r) v w) := by
  exact herm_swap_eq_zero_of_eq_zero _ Hpk_apply_eq_star_apply_swap v w

theorem blockProjection_of_mem_block {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : SSn.wbP k r v = v := by
  funext i
  simp only [SSn.wbP]
  split_ifs with h
  · rfl
  · exact (hv i (by omega)).symm

theorem prWv_of {z v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    SSn.prWv k r z v = v + (herm (Hpk k r) v z / (Tz k r z : ℂ)) • z := by
  simp only [SSn.prWv, blockProjection_of_mem_block hv]

theorem prWv_fix {z x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (h0 : herm (Hpk k r) x z = 0) :
    SSn.prWv k r z x = x := by
  rw [prWv_of hx, h0]
  simp

private theorem herm_Hpk_self_eq_neg_Tz (z : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := hswap (k := k) (r := r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.conj_im] at h2
    simp
    linarith

theorem prWv_perp {z y : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hy : inWb k r y) :
    herm (Hpk k r) (SSn.prWv k r z y) z = 0 := by
  have hT0 : (Tz k r z : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [prWv_of hy, hadd_l, hsmul_l, herm_Hpk_self_eq_neg_Tz]
  have h1 : herm (Hpk k r) y z / (Tz k r z : ℂ) * -(Tz k r z : ℂ) = -herm (Hpk k r) y z := by
    rw [div_mul_eq_mul_div, mul_neg, neg_div, mul_div_assoc, div_self hT0, mul_one]
  rw [h1]
  ring

theorem prWv_inWb {z y : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hy : inWb k r y) :
    inWb k r (SSn.prWv k r z y) := by
  intro i hi
  have h1 : SSn.wbP k r y i = 0 := by
    simp only [SSn.wbP]
    rw [if_neg]
    omega
  simp only [SSn.prWv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz i hi, h1, mul_zero, add_zero]

private theorem herm_Hpk_self_self_eq_neg_ofReal_Tz (z : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := hswap (k := k) (r := r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.conj_im] at h2
    simp
    linarith

theorem prWv_norm {z y : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hy : inWb k r y) {ζ : ℂ} {T' : ℝ}
    (hyy : herm (Hpk k r) y y = -(T' : ℂ)) (hyz : herm (Hpk k r) y z = ζ) :
    herm (Hpk k r) (SSn.prWv k r z y) (SSn.prWv k r z y) =
      ((Complex.normSq ζ / Tz k r z - T' : ℝ) : ℂ) := by
  have hT0 : (Tz k r z : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [prWv_of hy]
  simp only [hadd_l, hadd_r, hsmul_l, hsmul_r, herm_Hpk_self_self_eq_neg_ofReal_Tz, hyy, hyz]
  rw [hswap y z, hyz, map_div₀, Complex.conj_ofReal]
  push_cast
  rw [← Complex.mul_conj]
  field_simp
  ring

theorem unitH_facts {z x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (h0 : herm (Hpk k r) x z = 0) {s : ℝ}
    (hs : 0 < s) (hxx : herm (Hpk k r) x x = (s : ℂ)) :
    SSn.prWv k r z (SSn.unitH k r x) = SSn.unitH k r x ∧ herm (Hpk k r) (SSn.unitH k r x) (SSn.unitH k r x) = 1 := by
  have hu : SSn.unitH k r x = (((Real.sqrt s)⁻¹ : ℝ) : ℂ) • x := by
    simp only [SSn.unitH, hxx, Complex.ofReal_re]
  have hin : inWb k r (SSn.unitH k r x) := by
    intro i hi
    rw [hu]
    simp [hx i hi]
  refine ⟨prWv_fix hin ?_, ?_⟩
  · rw [hu, hsmul_l, h0, mul_zero]
  · rw [hu, hsmul_l, hsmul_r, hxx, Complex.conj_ofReal]
    have key : (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * s) = 1 := by
      rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hs.le, inv_mul_cancel₀ hs.ne']
    exact_mod_cast key

theorem base {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    SSn.prWv k r z (SSn.nu0 k r z z' μsec ζ) = SSn.nu0 k r z z' μsec ζ ∧
      herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) (SSn.nu0 k r z z' μsec ζ) = 1 ∧
      SSn.prWv k r z' (SSn.nu0' k r z z' μsec ζ) = SSn.nu0' k r z z' μsec ζ ∧
      herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) (SSn.nu0' k r z z' μsec ζ) = 1 := by
  have hm := NFRadRedA.muZ_uwb hsec hζ
  have hG := NFRadRedA.uwb_glev hm
  have hU : NF.muZ k r μsec ζ ∈ UH (Hpk k r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hUi : (NF.muZ k r μsec ζ)⁻¹ ∈ UH (Hpk k r) := hGi.1
  have hyz : herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') z = ζ := by
    rw [← NFRadRedA.zeta_eq]; exact NFRadRedA.zeta_muZ hz hz' hsec hζ
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hyy : herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') (NF.muZ k r μsec ζ *ᵥ z') = -((Tz k r z' : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hU, FrameEntries.herm_self]
  have hyyi : herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) =
      -((Tz k r z : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hUi, FrameEntries.herm_self]
  have hyzi : herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) z' = conj ζ := by
    rw [hswap, ← FrameEntries.herm_inv hU, hyz]
  have hpos : 0 < Complex.normSq ζ / Tz k r z - Tz k r z' := by
    rw [sub_pos, lt_div_iff₀ hT]; linarith
  have hposi : 0 < Complex.normSq (conj ζ) / Tz k r z' - Tz k r z := by
    rw [Complex.normSq_conj, sub_pos, lt_div_iff₀ hT']; linarith
  obtain ⟨h1, h2⟩ := unitH_facts (prWv_inWb hz hy) (prWv_perp hT hy) hpos (prWv_norm hT hy hyy hyz)
  obtain ⟨h3, h4⟩ := unitH_facts (prWv_inWb hz' hyi) (prWv_perp hT' hyi) hposi (prWv_norm hT' hyi hyyi hyzi)
  exact ⟨h1, h2, h3, h4⟩

end DU

theorem datum_unit_norm_holds : DatumUnit := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v ζ hζ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hζ' : Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' < Complex.normSq ζ := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; exact hζ
  exact DU.base hPl.2.1 hPl.2.2.1 (T v).base.T_pos (T v).base.T'_pos (T v).base.sec hζ'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RealInputsBuiltClosedForm
section
open Finset NumberField MeasureTheory Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

noncomputable section

theorem jct_rd_pos (E : Type) [Field E] [NumberField E] : 0 < S6.rd E := by
  unfold S6.rd
  apply Real.rpow_pos_of_pos
  exact Int.cast_pos.mpr (abs_pos.mpr (NumberField.discr_ne_zero E))

theorem jct_isBuiltPlace_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {A₀ Cc c : ℝ} (hc : c ≤ Cc) (h : JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀) :
    JCT.IsBuiltPlace c S T f χ ν' m₀ top A₀ := by
  unfold JCT.IsBuiltPlace at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, le_trans hc h9, h10, h11, ?_, h13⟩
  · unfold JCT.LongCut at h8 ⊢
    intro v
    exact le_trans (mul_le_mul_of_nonneg_right hc (by positivity)) (h8 v)
  · exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)) h12

theorem energy_of_built_setting : JCT.EnergyOfLemmaE := by
  intro hBC
  obtain ⟨Cc, hBC⟩ := hBC
  refine ⟨Cc, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ jv hBP hL v
  obtain ⟨-, -, -, hB, -, -, -, -, -, hsm, -, -, -⟩ := id hBP
  have hpd := (hB.2 v).1
  set Γ := D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0 with hΓ
  obtain ⟨-, hlim⟩ := hBC E Wp Wq S T f χ ν' m₀ top A₀ hBP v
  have hemp : S.empW.1 v = [] := rfl
  have h1 := hL S.empW v
  have h2 : Filter.Tendsto (fun ε => (S.pd v).RR ε 0 (S.empW.1 v) [] []) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((((1 / Γ : ℝ)) : ℂ) * (((B.normSq (T v).base (f v)).toReal : ℝ) : ℂ))) := by
    refine (hlim.const_mul _).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hsm' := cutoff_smooth _ _ _ _ (T v).base χ (f v) ε hB.1 (hsm v) hε
    rw [hpd]
    simp only [D.componentFamilySetting_ofSetting, D.bSt, D.toStd, List.map_nil, List.prod_nil]
    rw [level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hsm' (good_of_admissible _ _ _ S S.empW v)]
    rw [hemp]
    simp only [C7.principalHermitianLattice, List.foldr_nil]
    push_cast
    ring
  have h3 := tendsto_nhds_unique h1 h2
  rw [hemp] at h3
  have hsz : S.sizeAt v [] = 1 := by simp [C.HidaSetting.sizeAt]
  rw [hsz, one_mul] at h3
  have h4 : jv v = 1 / Γ * (B.normSq (T v).base (f v)).toReal := by exact_mod_cast h3
  rw [h4]
  ring

end

end Formalism.FourierDecayAlt.P
end

