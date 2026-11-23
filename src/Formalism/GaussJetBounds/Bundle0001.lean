module

public import Formalism.GaussJetBounds.Statement

@[expose] public section

-- bundled from Formalism.GaussJetBounds.GenLogInverse
section
noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def genLog {K : Type u} [Field K] {τ : Type v} [DecidableEq τ] (l : ℕ) (p : τ → τ) (x : τ) :
    MvPowerSeries τ K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0

def WtGeLe {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (κ : ι →₀ ℕ)
    (f : MvPowerSeries ι K) : Prop :=
  ∀ n : ι →₀ ℕ, n ≤ κ → MonoWtGe pi r w n (MvPowerSeries.coeff n f)

def GenLogWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (τ : Type v) [Finite τ] [DecidableEq τ] (p : τ → τ)
    (g : τ → MvPowerSeries τ K), (∀ x, MvPowerSeries.constantCoeff (g x) = 0) →
      (∀ x, MvPowerSeries.subst g (genLog (K := K) l p x) = MvPowerSeries.X x) →
      ∀ x, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (g x)

def LogBridges : Prop :=
  ∀ (K : Type u) [Field K] (l d N0 N1 : ℕ),
    (∀ x : V2 d, letterLog (K := K) l x = genLog l (fun y : V2 d => (y.1, y.2 - 2)) x) ∧
    (∀ x : ZV d N0 N1, entLog (K := K) l x =
      genLog l (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2)) x) ∧
    (∀ x : Fin N0 × Fin N1, oneLog (K := K) l x = genLog l id x)

def GenLogInverse : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (l : ℕ), l.Prime → ∀ (τ : Type v) [Finite τ]
    [DecidableEq τ] (p : τ → τ),
    ∃ g : τ → MvPowerSeries τ K, (∀ x, MvPowerSeries.constantCoeff (g x) = 0) ∧
      (∀ x, MvPowerSeries.subst g (genLog (K := K) l p x) = MvPowerSeries.X x) ∧
      (∀ x, MvPowerSeries.subst (genLog (K := K) l p) (g x) = MvPowerSeries.X x)

def SubstWt : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (pi : ℝ), 0 < pi → pi < 1 →
    ∀ (σ : Type v) (τ : Type w) [Finite σ] (a : σ → MvPowerSeries τ K) (r : σ → ℝ) (r' : τ → ℝ)
      (wt : ℝ) (f : MvPowerSeries σ K),
      (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, WtGe pi r' (r i) (a i)) →
      WtGe pi r wt f → WtGe pi r' wt (MvPowerSeries.subst a f)

def RadMono : Prop :=
  ∀ (K : Type u) [NormedField K] (pi : ℝ), 0 < pi → pi < 1 → ∀ (ι : Type v) (r r' : ι → ℝ)
    (wt : ℝ), (∀ i, r i ≤ r' i) →
    (∀ f : MvPowerSeries ι K, WtGe pi r wt f → WtGe pi r' wt f) ∧
    (∀ (κ : ι →₀ ℕ) (f : MvPowerSeries ι K), WtGeLe pi r wt κ f → WtGeLe pi r' wt κ f)

def MulWtLe : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (pi : ℝ), 0 < pi →
    ∀ (ι : Type v) (r : ι → ℝ) (w1 w2 : ℝ) (κ : ι →₀ ℕ) (f g : MvPowerSeries ι K),
      WtGeLe pi r w1 κ f → WtGeLe pi r w2 κ g → WtGeLe pi r (w1 + w2) κ (f * g)

def ExpWtLe : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) (r : ι → ℝ) (κ : ι →₀ ℕ) (B : MvPowerSeries ι K),
      MvPowerSeries.constantCoeff B = 0 →
      WtGeLe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) κ B → WtGeLe ‖(l : K)‖ r 0 κ (mvExp B)

def FactVal : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) [Fintype ι] (κ : ι →₀ ℕ),
      ‖((mfact κ : ℕ) : K)‖ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
        (Fintype.card ι : ℝ) * (Real.logb l (κ.degree : ℝ) + 1))

def PureCross : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → ‖(l : K)‖ < 1 →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ZV d N0 N1 → ι → K), (∀ x i, ‖M x i‖ ≤ 1) →
    ∀ be : MvPowerSeries (ZMod d) K, MvPowerSeries.constantCoeff be = 0 →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) be →
      (∀ n, ¬ IsBiPower l n →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n (MvPowerSeries.coeff n be)) →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) (bSum M be) ∧
      ∀ n : ι →₀ ℕ, (¬ ∃ (i j : ι) (α β : ℕ), n = pureMon l i j α β) →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n
          (MvPowerSeries.coeff n (bSum M be))

def LogStep : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ι : Type v) (r : ι → ℝ) (D : MvPowerSeries ι K),
      MvPowerSeries.constantCoeff D = 0 →
      WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) (mvExp D - 1) → WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) D

def ExpDeInv : Prop :=
  ∀ (K : Type u) [NormedField K] [CharZero K] (l d : ℕ) [NeZero d], l.Prime → 2 ≤ d → Even d →
    ∀ (K0 : Subfield K) (ζ : K), IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ be : MvPowerSeries (ZMod d) K, (∀ n, MvPowerSeries.coeff n be ∈ K0) →
      MvPowerSeries.subst (torus l ζ) be = be → MvPowerSeries.constantCoeff be = 0 →
      ∀ D ∈ ({de1 be, de2 be} : Set (MvPowerSeries (V2 d) K)),
        (∀ n, MvPowerSeries.coeff n (mvExp D) ∈ K0) ∧
        ∀ n : V2 d →₀ ℕ, MvPowerSeries.coeff n (mvExp D) ≠ 0 →
          ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2

def Quant : Prop :=
  ∀ (K : Type u) [NormedField K] (l d : ℕ) [NeZero d], l.Prime → 2 ≤ d → Even d →
    ‖(l : K)‖ < 1 → 0 < ‖(l : K)‖ → ∀ (K0 : Subfield K), Unram l K0 →
    ∀ (c : K), c ∈ K0 → ∀ n : V2 d →₀ ℕ,
      ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2 →
      MonoWtGe ‖(l : K)‖ (fun _ => rho l) (rho l) n c →
      MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n c

def BinomExtract : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d],
    l.Prime → Odd l → 2 ≤ d → Even d → ‖(l : K)‖ < 1 →
    ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) → ∀ be : MvPowerSeries (ZMod d) K,
      MvPowerSeries.subst (torus l ζ) be = be → NoLowBidegree be →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (de1 be) →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (de2 be) →
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) be ∧
      ∀ n, ¬ IsBiPower l n →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) n (MvPowerSeries.coeff n be)

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.StatementA
section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def rowRad {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d) (isTop : ι → Bool)
    (spec : ι → Option (ZMod d × ℤ)) (i : ι) : ℝ :=
  if isTop i then eps (lt i) else
    match spec i with
    | some (s, j) =>
        if 0 < j then max (sig (lt i)) (1 - (l : ℝ) ^ j.toNat * eps s)
        else max (sig (lt i)) ((l : ℝ) ^ (-j).toNat)⁻¹
    | none => sig (lt i)

def ThmAAssembly : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
  ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu2 s ≤ nu1 s) →
    (∀ s, nu1 s ≤ size s) →
  ∀ sig : ZMod d → ℝ, IsOptDual l d (fun s => (Dl d TT nu1 size s : ℝ)) sig →
  ∀ (ι : Type) [Fintype ι] (lt : ι → ZMod d) (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ))
    (κ : ι → ℕ),
    (∀ i, isTop i = true → lt i ∈ TT ∧ spec i = none) →
    (∀ s ∈ TT, (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = true), (κ i : ℝ)) =
      (nu1 s : ℝ)) →
    (∀ s, (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = false), (κ i : ℝ)) =
      (Dl d TT nu1 size s : ℝ)) →
    (∀ i s j, spec i = some (s, j) → s ∈ TT ∧ Odd j ∧ lt i = s + (j : ZMod d) ∧
      (0 < j → l ^ j.toNat ≤ nu1 s) ∧ (j < 0 → l ^ (-j).toNat ≤ size (lt i))) →
    (∀ (s : ZMod d) (j : ℤ), (∑ i ∈ Finset.univ.filter (fun i => spec i = some (s, j)), (κ i : ℝ)) ≤
      (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ)) →
    ∃ eps : ZMod d → ℝ, (∀ s, 0 ≤ eps s) ∧
      (∀ s ∈ TT, ∀ e : ℕ, dTop d TT s = (e : ℕ∞) → ((l : ℝ) ^ e)⁻¹ ≤ eps s) ∧
      (∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) ≤
        ∑ i, (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i)

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.StatementC
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def frameM {K : Type u} [Field K] {d N0 N1 : ℕ} (x : ZMod d × Fin N0 × Fin N0 → K) :
    ZV d N0 N1 → ZV d N0 N1 → K :=
  fun z y => if y.1 = z.1 ∧ y.2.2 = z.2.2 then x (z.1, y.2.1, z.2.1) else 0

def FramePure : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0) (x : ZMod d × Fin N0 × Fin N0 → K), (∀ y, ‖x y‖ ≤ 1) →
    ∀ be : MvPowerSeries (ZMod d) K,
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) be →
    ∀ (s s' : ZMod d), s ≠ s' → ∀ (k : Fin N0) (b b' : Fin N1) (α β : ℕ),
      (b ≠ b' → MvPowerSeries.coeff (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b') α β)
          (bSum (frameM (N1 := N1) x) be) = 0) ∧
      ((if β ≤ α then ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ (α - β)) * x (s', k, a)‖
          else ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) * x (s', k, a) ^ (l ^ (β - α))‖) ≤ ‖(l : K)‖ →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1))
          (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b) α β)
          (MvPowerSeries.coeff (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b) α β)
            (bSum (frameM (N1 := N1) x) be)))

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.StatementD
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

def JCount : Prop :=
  ∀ l a : ℕ, 2 ≤ l → 1 ≤ a →
    (((Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a)).card : ℝ) ≤
      2 * Real.logb l a + 1

end Formalism.DworkPowerSeriesWeights
end
end

