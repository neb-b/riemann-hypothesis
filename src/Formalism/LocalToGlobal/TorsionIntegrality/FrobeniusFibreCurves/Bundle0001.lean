module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LawDifferenceThree
section
noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7 (at1 cob d1 in3 swap2 DivAB)

section Alg

variable {K : Type} [Field K] [CharZero K]

def wp3 (P : PowerSeries K) (j k : Fin 3) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.X j ^ 2 - MvPowerSeries.X k ^ 2 +
    MvPowerSeries.X j ^ 2 * MvPowerSeries.X k ^ 2 * (at1 k P - at1 j P)

def det3 (P : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  Matrix.det (Matrix.of fun j : Fin 3 =>
    ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K) ^ 3,
      MvPowerSeries.X j * (1 + MvPowerSeries.X j ^ 2 * at1 j P),
      -2 + MvPowerSeries.X j ^ 3 * at1 j (dz P)])

def vand3 (K : Type) [Field K] : MvPowerSeries (Fin 3) K :=
  (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
    (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) *
    (MvPowerSeries.X 1 - MvPowerSeries.X 2)

def evalSumThree (f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  PowerSeries.subst
    (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f

def evalDiffThree (j k : Fin 3) (f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  PowerSeries.subst (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K) f

def fsE (f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  evalSumThree f + evalDiffThree 0 1 f + evalDiffThree 0 2 f + evalDiffThree 1 2 f - 3 * at1 0 f - 3 * at1 1 f - 3 * at1 2 f

def ev3 (h : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1, 0] h

def F3 (F : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] F

def lawDifferenceThree (F : MvPowerSeries (Fin 2) K) (i : PowerSeries K) (j k : Fin 3) :
    MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), at1 k i] F

def par3 (F : MvPowerSeries (Fin 2) K) (i f : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  PowerSeries.subst (F3 F) f + PowerSeries.subst (lawDifferenceThree F i 0 1) f +
    PowerSeries.subst (lawDifferenceThree F i 0 2) f + PowerSeries.subst (lawDifferenceThree F i 1 2) f -
    3 * at1 0 f - 3 * at1 1 f - 3 * at1 2 f

end Alg

section Norm

open Formalism.DworkPowerSeriesWeights (Integral)

variable {K : Type} [NormedField K]

def CurveHyp3 (F : MvPowerSeries (Fin 2) K) (l P ep : PowerSeries K) (a1 a3 : K) : Prop :=
  PowerSeries.X ^ 3 * (-2 + l ^ 3 * PowerSeries.subst l (PowerSeries.derivative (R := K) P)) =
      l ^ 3 * (-2 * ep + PowerSeries.C a1 * PowerSeries.X * ep +
        PowerSeries.C a3 * PowerSeries.X ^ 3) ∧
    ∃ e : MvPowerSeries (Fin 3) K, Integral e ∧ MvPowerSeries.constantCoeff e = -1 ∧
      Matrix.det (Matrix.of fun j : Fin 3 =>
        ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K) ^ 3, MvPowerSeries.X j * at1 j ep,
          -at1 j ep]) =
        e * F3 F * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
          (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2)

end Norm

end Formalism.L2.Th1.B
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementA
section
noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7 (at1)

def ExpLogRules : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type),
    (∀ f g : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff g = 0 → fExp (f + g) = fExp f * fExp g) ∧
    (∀ f : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (fExp f) = 1 ∧ fLog (fExp f) = f) ∧
    (∀ g : MvPowerSeries ι K, MvPowerSeries.constantCoeff g = 1 →
      MvPowerSeries.constantCoeff (fLog g) = 0 ∧ fExp (fLog g) = g)

def ExpLogDeriv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Finite ι] (i : ι),
    (∀ f : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      pd i (fExp f) = fExp f * pd i f) ∧
    (∀ g : MvPowerSeries ι K, MvPowerSeries.constantCoeff g = 1 → g * pd i (fLog g) = pd i g)

def ExpLogSubst : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι κ : Type) [Finite ι] (φ : ι → MvPowerSeries κ K),
    (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
    (∀ f : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.subst φ (fExp f) = fExp (MvPowerSeries.subst φ f)) ∧
    (∀ g : MvPowerSeries ι K, MvPowerSeries.constantCoeff g = 1 →
      MvPowerSeries.subst φ (fLog g) = fLog (MvPowerSeries.subst φ g))

def PrimRules : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : PowerSeries K),
    dz (prim f) = f ∧ PowerSeries.constantCoeff (prim f) = 0

def WaveUnique : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (h : MvPowerSeries (Fin 2) K),
    pd 0 (pd 0 h) = pd 1 (pd 1 h) → ev0 h = 0 → ev0 (pd 1 h) = 0 → h = 0

def WaveKills : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : PowerSeries K),
    pd 0 (pd 0 (par0 f)) - pd 1 (pd 1 (par0 f)) = -2 * at1 0 (dz (dz f)) + 2 * at1 1 (dz (dz f))

def ParCauchy : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : PowerSeries K),
    PowerSeries.constantCoeff f = 0 → PowerSeries.coeff 1 f = 0 →
    ev0 (par0 f) = 0 ∧ ev0 (pd 1 (par0 f)) = 0

def WpReduced : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    PowerSeries.X ^ 4 * dz P ^ 2 - 4 * PowerSeries.X * dz P =
        12 * P + 12 * PowerSeries.X ^ 2 * P ^ 2 + 4 * PowerSeries.X ^ 4 * P ^ 3 -
          PowerSeries.C g2 * PowerSeries.X ^ 2 * (1 + PowerSeries.X ^ 2 * P) -
          PowerSeries.C g3 * PowerSeries.X ^ 4 ∧
      PowerSeries.X ^ 2 * dz (dz P) =
        12 * P + 6 * PowerSeries.X ^ 2 * P ^ 2 - PowerSeries.C (g2 / 2) * PowerSeries.X ^ 2

def WSecond : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A kap : K) (w : PowerSeries K), IsW A kap w →
    PowerSeries.coeff 1 w = 0 ∧
      dz (dz w) = 2 + 4 * PowerSeries.C A * w + 6 * PowerSeries.C kap * w ^ 2

def WOfWp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 e1 : K) (P : PowerSeries K), IsWp g2 g3 P →
    4 * e1 ^ 3 - g2 * e1 - g3 = 0 → IsW (3 * e1) (3 * e1 ^ 2 - g2 / 4) (wOf e1 P)

def DqRule : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (P : PowerSeries K),
    (∀ n, Odd n → PowerSeries.coeff n P = 0) →
    at1 0 P - at1 1 P = (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) * dq P

def AddSigmaLog : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    par0 (sigS P) = fLog (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P)

def AddSigma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P : PowerSeries K), IsWp g2 g3 P →
    MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * (atS (sigma P) * atD (sigma P)) =
      at1 0 (sigma P) ^ 2 * at1 1 (sigma P) ^ 2 * wpDiff P

def AddSgStar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 s2 : K) (P : PowerSeries K), IsWp g2 g3 P →
    MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * (atS (sgStar s2 P) * atD (sgStar s2 P)) =
      at1 0 (sgStar s2 P) ^ 2 * at1 1 (sgStar s2 P) ^ 2 * wpDiff P

def Sigma1Sq : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 e1 : K) (P : PowerSeries K), IsWp g2 g3 P →
    4 * e1 ^ 3 - g2 * e1 - g3 = 0 →
    PowerSeries.X ^ 2 * sigma1 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) ^ 2 =
      sigma P ^ 2 * (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2)

end Formalism.L2.Th1.B
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementB
section
noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)

def HalfExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l : PowerSeries K), LawLog F l → ‖(2 : K)‖ = 1 → ∃ h, IsHalf l h

def SimeqInt : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (f g f' g' : MvPowerSeries ι K),
    Simeq f g → Simeq f' g' →
    Simeq (f - f') (g - g') ∧ Simeq (-f) (-g) ∧ ∀ n : ℤ, Simeq ((n : MvPowerSeries ι K) * f) (n * g)

def SimeqLog : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g : MvPowerSeries ι K),
    MvPowerSeries.constantCoeff g = 1 → Integral g → Simeq (fLog g) 0 ∧ Simeq (-fLog g) 0

def PhODef : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (s2 : K) (P l : PowerSeries K),
    PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 →
    PowerSeries.constantCoeff (phO s2 P l) = 0 ∧
      PowerSeries.subst l (sgStar s2 P) = PowerSeries.X * fExp (-phO s2 P l)

def PhEDef : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (s2 e1 kap : K) (w l : PowerSeries K),
    PowerSeries.constantCoeff l = 0 →
    PowerSeries.constantCoeff (phE s2 e1 kap w l) = 0 ∧
      PowerSeries.subst l
          (sigma1 e1 kap w * fExp (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2))) =
        fExp (-phE s2 e1 kap w l)

def ParE : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (A kap e1 s2 : K)
    (w l i : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsW A kap w → LawLog F l → IsInv l i → ‖kap‖ ≤ 1 →
    Integral (ι := Unit) (PowerSeries.subst l w) →
    Simeq (par F i (phE s2 e1 kap w l)) 0

def ParO : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 →
    Simeq (par F i (phO s2 P l)) 0

def WIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (c0 e1 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    LawLog F l → CurveHyp F i l P ep c0 → ‖c0 - e1‖ ≤ 1 →
    PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) =
        PowerSeries.X ^ 2 ∧
      Integral (ι := Unit) (PowerSeries.subst l (wOf e1 P))

def DiffPh : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 e1 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → 4 * e1 ^ 3 - g2 * e1 - g3 = 0 → LawLog F l → CurveHyp F i l P ep c0 →
    2 * (phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l - phO s2 P l) =
        -fLog (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) ∧
      (‖c0 - e1‖ ≤ 1 →
        Simeq (ι := Unit) (2 * phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l) (2 * phO s2 P l))

def CobRules : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l f : PowerSeries K), LawLog F l → PowerSeries.constantCoeff f = 0 →
    DivAB (cob F f) ∧ swap2 (cob F f) = cob F f

def Cube : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l i f : PowerSeries K), LawLog F l → IsInv l i → ‖(2 : K)‖ = 1 →
    Simeq (par F i f) 0 → Simeq (d1 F (cob F f)) 0

def LogSigmaPullbackCocycle : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → ‖(2 : K)‖ = 1 →
    DivAB (cob F (phO s2 P l)) ∧ swap2 (cob F (phO s2 P l)) = cob F (phO s2 P l) ∧
      Simeq (d1 F (cob F (phO s2 P l))) 0 ∧ Simeq (d1 F (swap2 (cob F (phO s2 P l)))) 0

def JetsThree : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l f : PowerSeries K), LawLog F l → Simeq (d1 F (cob F f)) 0 →
    ∀ n : ℕ, 3 ≤ n → ‖PowerSeries.constantCoeff ((Dinv l)^[n] f)‖ ≤ 1

end Formalism.L2.Th1.B
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementC
section
noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)

def BaseChange : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
    (s2 e1 kap : K) (P w l : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 →
    MvPowerSeries.constantCoeff F = 0 →
    PowerSeries.map j (sigma P) = sigma (PowerSeries.map j P) ∧
    PowerSeries.map j (sgStar s2 P) = sgStar (j s2) (PowerSeries.map j P) ∧
    PowerSeries.map j (sigma1 e1 kap w) = sigma1 (j e1) (j kap) (PowerSeries.map j w) ∧
    PowerSeries.map j (wOf e1 P) = wOf (j e1) (PowerSeries.map j P) ∧
    PowerSeries.map j (phO s2 P l) = phO (j s2) (PowerSeries.map j P) (PowerSeries.map j l) ∧
    PowerSeries.map j (phE s2 e1 kap w l) =
      phE (j s2) (j e1) (j kap) (PowerSeries.map j w) (PowerSeries.map j l) ∧
    ∀ f : PowerSeries K, MvPowerSeries.map j (cob F f) =
      cob (MvPowerSeries.map j F) (PowerSeries.map j f)

end Formalism.L2.Th1.B
end
end

