module

public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

@[expose] public section

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.PrimeSupply
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField

def dlogQ (d : ℕ) (hd : d.Prime) : ℝ :=
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : NeZero d := ⟨hd.ne_zero⟩
  (deriv (DirichletCharacter.LFunction
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d)) 1 /
    DirichletCharacter.LFunction
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d) 1).re

structure QDGood (x eps : ℝ) (q d : ℕ) : Prop where
  hyp : HostHyp q d
  q_lo : Real.exp (x ^ (eps / 5) / 2) < q
  q_hi : (q : ℝ) ≤ Real.exp (x ^ (eps / 5))
  d_lo : Real.exp (x ^ (eps / 5) * Real.log x ^ 2 / 2) < d
  d_hi : (d : ℝ) ≤ Real.exp (x ^ (eps / 5) * Real.log x ^ 2)
  split : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ x ^ (eps / 5) → jacobiSym (-(d : ℤ)) p = 1
  dlog : |dlogQ d hyp.2.1| ≤ x ^ eps

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.TiesCore
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.Inhab.GC

structure GHost (R : Ranks) where
  TT : Finset (R.A)
  T2 : Finset ℕ
  u0 : R.A
  cls : ℕ → PrimeClass

structure GD where
  R : Ranks
  host : GHost R
  hPf : ℕ → R.A

structure GParameters (D : GD) where
  sc : Scale
  Sc : ℝ
  etaSz : ℝ

abbrev HH (D : GD) : Type := D.R.A

def cG {D : GD} (L : GParameters D) : ℝ := 4 * L.Sc

def L1 (D : GD) (s : Scale) (p : ℕ) : ℕ := ⌈Real.logb p (((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4)⌉₊

def L2 (D : GD) (s : Scale) : ℕ :=
  2 * sSup {l | ∃ p : ℕ, p.Prime ∧ D.host.cls p = PrimeClass.inertClass ∧ l = L1 D s p}

def Nstar (D : GD) (s : Scale) : ℝ := 2 * (D.R.n : ℝ) * s.delta1

def rhoB (D : GD) (K : Consts) (s : Scale) : ℝ :=
  4 * Nstar D s * s.x ^ s.eps * La K s / D.R.k + K.rho * K.CN * Real.log s.x * La K s / D.R.k

def InBand (D : GD) (K : Consts) (s : Scale) (p : ℕ) : Prop :=
  s.p0 D.R.k ≤ (p : ℝ) ∧ (p : ℝ) < s.X' ∧ ∃ d : ℕ, 1 ≤ d ∧
    s.X' * (1 - rhoB D K s) ≤ (p : ℝ) ^ d ∧ (p : ℝ) ^ d ≤ s.X' * (1 + rhoB D K s)

def hP (D : GD) (p : ℕ) : HH D := D.hPf p

abbrev IsResidueClassZero (D : GD) (p : ℕ) : Prop := D.host.cls p = PrimeClass.inertClass

abbrev IsSg (D : GD) (p : ℕ) : Prop := D.host.cls p = PrimeClass.signal

def IsTopPl (D : GD) (z : Bool × HH D) : Prop := z.1 = false ∧ z.2 ∈ D.host.TT

def IsThickPl (D : GD) (z : Bool × HH D) : Prop :=
  z.1 = true ∧ z.2 ∈ D.host.T2.image (fun s : ℕ => D.R.dig s + D.host.u0)

def IsThinPl (D : GD) (z : Bool × HH D) : Prop := ¬ IsTopPl D z ∧ ¬ IsThickPl D z

structure Inst (D : GD) (L : GParameters D) where
  bs : HH D → HH D → HH D
  bs_orb : ∀ h t, ∃ i : ℕ, bs h t + i • h = t
  bs_step : ∀ h t, bs h (t + h) = bs h t
  off : ℕ → Bool × HH D → ℝ
  off_top : ∀ j z, IsTopPl D z → L.sc.b' / L.sc.x ≤ off j z ∧ off j z ≤ L.sc.b' / L.sc.x + L.etaSz
  off_thin : ∀ j z, IsThinPl D z → L.sc.w'' D.R.n ≤ off j z ∧ off j z ≤ L.sc.w'' D.R.n + L.etaSz
  off_thick : ∀ j z, IsThickPl D z → L.sc.b ≤ off j z ∧ off j z ≤ L.sc.b + L.etaSz + 1
  kapI : ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ
  ep : ℕ → ℕ

variable {D : GD} {L : GParameters D}

def stepP (D : GD) (p : ℕ) : HH D := if IsSg D p then 2 • hP D p else hP D p

def topsPos (D : GD) (p : ℕ) (t0 : HH D) : Finset (Fin (addOrderOf (hP D p))) :=
  Finset.univ.filter (fun i => t0 + (i : ℕ) • hP D p ∈ D.host.TT)

def Good (_X : Inst D L) (p : ℕ) (t0 : HH D) : Prop :=
  IsGoodOrbit (addOrderOf (hP D p)) (topsPos D p t0) (L2 D L.sc) (KG L.sc) (rG L.sc) L.sc.delta1
    (hG L.sc) L.sc.x





def Cand (D : GD) (L : GParameters D) (K : Consts) (p : ℕ) : Prop :=
  p.Prime ∧ (p : ℝ) < L.sc.X' ∧ IsResidueClassZero D p ∧ L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ) ∧
    (L.sc.p0 D.R.k ≤ (p : ℝ) → ¬ InBand D K L.sc p)







end Formalism.MainNotions.Inhab.GC

end
end

