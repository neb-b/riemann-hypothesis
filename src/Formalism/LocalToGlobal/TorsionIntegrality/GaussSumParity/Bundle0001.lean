module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.LetterShift
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.GaussJetBounds.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionPointsIntegral
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)

def TilInvariantL : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ u : K, u ^ (l ^ d - 1) = 1 →
    ∀ (τ : Type) [Finite τ] (L : ZMod d → MvPowerSeries τ K), ShiftType l σ L →
      Simeq (MvPowerSeries.subst L (MvPowerSeries.subst (torus l u) (beTil (d := d) l σ be0 om oms)))
        (MvPowerSeries.subst L (beTil (d := d) l σ be0 om oms))

def MeanSimeqL : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ (τ : Type) [Finite τ] (L : ZMod d → MvPowerSeries τ K), ShiftType l σ L →
      Simeq (MvPowerSeries.subst L (beMean (d := d) l σ be0 om oms ζ))
        (MvPowerSeries.subst L (beTil (d := d) l σ be0 om oms))

def BiextensionPointsIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
      ∃ Xt : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K,
        (∀ x, MvPowerSeries.constantCoeff (Xt x) = 0 ∧ Integral (Xt x)) ∧
        (∀ x, PowerSeries.subst (Xt x) (lgF K l) =
          if x.1 = false then
            linEL σ (oms x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))
          else linOL σ (om x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))) ∧
        Simeq (∑ ab : Fin N0 × Fin N1, MvPowerSeries.subst
            (fun s => entLog (K := K) l (s, ab.1, ab.2)) (beMean (d := d) l σ be0 om oms ζ))
          (MvPowerSeries.subst Xt (sumE be0))

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementC
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 cob UnrOK IsLawOfLog)

section Defs

variable {K : Type} [Field K]

def IsHom (F FE : MvPowerSeries (Fin 2) K) (θ : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff θ = 0 ∧
  PowerSeries.subst F θ = MvPowerSeries.subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] FE

def mulS (K : Type) [Field K] (l : ℕ) (c : K) : PowerSeries K :=
  PowerSeries.subst (PowerSeries.C c * lgF K l) (expF K l)

end Defs

def NormRel {K : Type} [NormedField K] [CharZero K] (l : ℕ) (σ : K →+* K) (ph : PowerSeries K)
    (α : K) : Prop :=
  Simeq (PowerSeries.subst (mulS K l α) ph : MvPowerSeries Unit K)
    (MvPowerSeries.C (α * σ α) * ph)

def SigmaIsom : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ a : K, ‖σ a‖ = ‖a‖

def FixedIsLimit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ x : K, ‖x‖ ≤ 1 → σ x = x → ∀ k : ℕ, ∃ n : ℕ, ‖x - n‖ ≤ ((l : ℝ) ^ k)⁻¹

def SimeqClosed : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (τ : Type) [Finite τ] (f : ℕ → MvPowerSeries τ K) (g : MvPowerSeries τ K),
    (∀ n, Filter.Tendsto (fun k => MvPowerSeries.coeff n (f k)) Filter.atTop
      (nhds (MvPowerSeries.coeff n g))) →
    (∀ k, Simeq (f k) 0) → Simeq g 0

def SimeqFixed : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (τ : Type) [Finite τ] (f : MvPowerSeries τ K) (c : K), ‖c‖ ≤ 1 → σ c = c →
    Simeq f 0 → Simeq (MvPowerSeries.C c * f) 0

def CoboundaryCocycleTransportAlongHom : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ = (l : ℝ)⁻¹ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ (FE : MvPowerSeries (Fin 2) K) (θ phE ph : PowerSeries K),
      MvPowerSeries.constantCoeff FE = 0 → (∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) → IsHom F FE θ →
      F1 FE (cob FE phE) → Simeq (ph : MvPowerSeries Unit K) (PowerSeries.subst θ phE) →
      F1 F (cob F ph)

def TransportNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (θ phE ph eE : PowerSeries K) (α : K),
      PowerSeries.constantCoeff θ = 0 → (∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) →
      PowerSeries.constantCoeff eE = 0 →
      ‖α‖ ≤ 1 → σ (σ α) = α →
      PowerSeries.subst (mulS K l α) θ = PowerSeries.subst θ eE →
      Simeq (PowerSeries.subst eE phE : MvPowerSeries Unit K) (MvPowerSeries.C (α * σ α) * phE) →
      Simeq (ph : MvPowerSeries Unit K) (PowerSeries.subst θ phE) →
      NormRel l σ ph α

def NormUnits : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (ph : PowerSeries K), PowerSeries.constantCoeff ph = 0 →
    ∀ S : Set K, (∀ α ∈ S, NormRel l σ ph α) →
      ∀ α : K, (∀ ε : ℝ, 0 < ε → ∃ a ∈ S, ‖a - α‖ < ε) → NormRel l σ ph α

def SecondLevelOfNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ ph : PowerSeries K, PowerSeries.constantCoeff ph = 0 → F1 F (cob F ph) →
    (∀ α : K, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ ph α) →
      F2 l σ (cob F ph) ∧
      (∀ α : K, ‖α‖ ≤ 1 → σ (σ α) = α → NormRel l σ ph α) ∧
      Simeq (MvPowerSeries.C (2 : K) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K)) (cob F ph))

def FOfBetaHyp : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → (∃ ζ : K, IsPrimitiveRoot ζ (l ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ be0 : MvPowerSeries (Fin 2) K, Formalism.InvariantFactorPaths.G7.BetaHyp l F be0 → F1 F be0 ∧ F2 l σ be0

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def muPrime (l : ℕ) [Fact l.Prime] : Set ℂ_[l] := {ζ | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}

def ringA (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] := Subring.closure (muPrime l)

def ringB (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] := (ringA l).topologicalClosure

def KurUnram : Prop := ∀ (l : ℕ) [Fact l.Prime], Unram l (MaximalUnramifiedExtension l)

def KurIntegers : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    (∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) ∧
    (∀ x ∈ ringB l, ‖x‖ < 1 → ∃ y ∈ ringB l, x = (l : ℂ_[l]) * y) ∧
    (∀ x ∈ ringB l, ‖x‖ = 1 → x⁻¹ ∈ ringB l)

def KurRoots : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ¬ l ∣ n → ∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ n

def KurComplete : Prop := ∀ (l : ℕ) [Fact l.Prime], CompleteSpace (MaximalUnramifiedExtension l)

def KurFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 2 < l →
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ ∧
      ∀ ζ : MaximalUnramifiedExtension l, (ζ : ℂ_[l]) ∈ muPrime l → σ ζ = ζ ^ l

def TrDualExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → Even d → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∃ om oms : Fin (d / 2) → K, OwOK d σ om oms ∧ TrDual d σ om oms

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.ThetaInZIsThetaLog
section
noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog OmOK lamF thetaLog EV alG capG lsG deLoss dSet oddT
  InClass hhS uS sSub)

def ThetaInZIsThetaLog : Prop :=
  ∀ (K0 K : Type) [Field K0] [Field K] (l ν r0 r1 : ℕ) [NeZero ν] (σ : K0 →+* K0) (j : K0 →+* K)
    (om oms : Fin ν → K0) (ϖ : K) (μ : PowerSeries K), 2 ≤ l → ϖ ≠ 0 →
    PowerSeries.constantCoeff μ = 0 →
    (PowerSeries.subst μ (lamF l ϖ) : PowerSeries K) = PowerSeries.X →
    ∀ Tht : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) K,
      thetaInZ (d := 2 * ν) l j σ om oms Tht = thetaLog (conjJ j σ om) (conjJ j σ oms) ϖ μ Tht

def KernelOfF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0]
    [CompleteSpace K0] (σ : K0 →+* K0), UnrOK K0 p σ → (∃ ζ : K0, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K0, F1 F be → F2 p σ be →
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (j : K0 →+* K) (ν r0 r1 : ℕ)
      [NeZero ν], (∀ a, ‖j a‖ = ‖a‖) → (∃ ϖ : K, ϖ ^ (p ^ 2 - 1) = (p : K)) →
    ∀ (om oms : Fin ν → K0), OwOK (2 * ν) σ om oms → TrDual (2 * ν) σ om oms →
    ∀ (U0 Φ : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) K), Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 → Simeq Φ (sumE (MvPowerSeries.map j be)) →
    ∀ (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1) n,
      ‖AddMonoidAlgebra.coeff (frameJet colN hts hp I (thetaInZ (d := 2 * ν) p j σ om oms (mvExp (-Φ) * U0))) n‖ ≤
          (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)))) ∧
      ‖AddMonoidAlgebra.coeff (frameJet colN hts hp I (thetaInZ (d := 2 * ν) p j σ om oms (mvExp (-Φ) * U0))) n‖ ≤
          (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
            ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ))) ∧
      ∀ i : ℕ, 1 ≤ i →
        ‖(p : K) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
            (if s.val % 2 = 0 then
              min (hts s c) i -
                ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
            else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
          AddMonoidAlgebra.coeff (frameJet colN hts hp I (thetaInZ (d := 2 * ν) p j σ om oms (mvExp (-Φ) * U0)))
            n‖ ≤
          (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TwoPlaces
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog bSum idM ZV serAlong)
open Formalism.InvariantFactorPaths.G7 (Simeq UnrOK IsLawOfLog)
open MvPowerSeries

abbrev PV (ι : Type) (N0 N1 : ℕ) := Bool × ι × Fin N0 × Fin N1

end Formalism.L2.Th1.D
end
end

