module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.TableDegreeElevenProduct

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

open Formalism.BasicNotions Formalism.MainNotions Finset

def cOne : ℝ := 8

def cThree : ℝ := 94

def cSix : ℝ := 32

def ceilEight (n : ℕ) : ℕ := 8 * ((n + 7) / 8)

section Numbers

variable (D : D7) (L : SizeData₂ D)

def lrd : ℝ := Real.log D.host.rdE

def pp (j : ℕ) : ℕ := (D.R.sigW j).1

def qq (j : ℕ) : ℕ := (D.R.sigW j).2

def dY : ℝ := (placeRankTwoOne.dimY D : ℝ)

def dX (j : ℕ) : ℕ := D.R.f * pp D j * qq D j

def cTw (j : ℕ) : ℕ := ceilEight (max (D.R.r + (dX D j + 1).choose 2 + 2) (8 * D.R.f * D.R.r + 4))

def nCol (j : ℕ) : ℕ :=
  ceilEight (max (D.R.f * (pp D j * (pp D j + 1) + qq D j * (qq D j + 1))) (8 * D.R.f * D.R.r + 4))

def eZero (j : ℕ) : ℝ := (D.R.f : ℝ) * D.R.r * ((cTw D j : ℝ) + 4 * D.R.r)

def bigR : ℝ := D.host.rdE ^ 7

def degStar : ℝ := 7 * (D.R.f : ℝ) * D.R.k * L.sc.b

def expQ : ℕ := sInf {c : ℕ | bigR D ^ 7 * degStar D L ^ 2 ≤ (3 : ℝ) ^ (2 * c)}

def levQ : ℕ := 3 ^ (2 * expQ D L)

def expC : ℕ := sInf {c : ℕ | bigR D ^ 8 * degStar D L ^ 2 ≤ (3 : ℝ) ^ c ∧ max 4 (2 * expQ D L) ≤ c}

def levDeep : ℕ := D.host.g 0 * D.host.g 1 * (3 ^ expC D L * 5 ^ expC D L)

def shareW (g : ℕ) : ℝ :=
  3 * (D.R.f : ℝ) / g + 23 * D.R.f * Real.log g * (g : ℝ) ^ (-(1 : ℝ) / 2) +
    2 * D.R.f * D.R.m * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log D.R.r) / ((g : ℝ) - 1)) +
    (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log D.R.r))

def del : ℝ := shareW D (D.host.g 0) + shareW D (D.host.g 1)

def kap (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := if h : i < D.R.r then DV.kapW D j τ ⟨i, h⟩ else 0

def wAn (j : ℕ) (τ : D.what₂.Tau) : ℤ := kap D j τ (D.R.k - 2)

def uAn (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := kap D j τ i - wAn D j τ

def nrm (v : ℕ → ℤ) : ℝ := ∑ i ∈ range D.R.r, |(v i : ℝ)|

def nKap (j : ℕ) : ℝ := ∑ τ, nrm D (kap D j τ)

def deW (j i : ℕ) : ℤ := if i < pp D j then 0 else -1

def canW (j i : ℕ) : ℤ :=
  if i < pp D j then (qq D j : ℤ) - pp D j + 1 + 2 * i else -(pp D j : ℤ) - qq D j + 1 + 2 * ((i : ℤ) - pp D j)

def aW (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uAn D j τ i - (cTw D j : ℤ) * deW D j i - canW D j i

def degW (v : D.what₂.Tau → ℕ → ℤ) : ℝ :=
  ∏ τ, ∏ l ∈ range D.R.r, ∏ i ∈ range l, ((v τ i : ℝ) - v τ l)

def shift : ℝ := (D.R.nV : ℝ) / 2 * D.R.f * D.R.r * (Real.log (2 * Real.pi) / 2 + lrd D)

end Numbers

section Run

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

def ppTsq : ℝ :=
  max (1.2e9 * (D.R.r : ℝ) ^ 2)
    (max (448 * cOne * Q.PP * D.R.f * D.R.m) (32 * cThree * cSix * Q.PP * D.R.f * D.R.m))

def tN : ℕ := ⌈ppTsq Q * dY D ^ 2 * D.R.k / D.R.m⌉₊

def tR : ℝ := (tN Q : ℝ)

def gapOne (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ :=
  (aW D j τ i - aW D j τ (i + 1)) / ((tN Q + placeRankTwoOne.dimY D + 1 : ℕ) : ℤ)

def uOne (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ :=
  (∑ l ∈ Ico i (D.R.k - 2), gapOne Q j τ l) - ∑ l ∈ Ico (D.R.k - 2) i, gapOne Q j τ l

def uPr (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uOne Q j τ i - 3 * (D.R.r : ℤ) * deW D j i

def rhoB (j : ℕ) : ℝ := 1 - degW D (uPr Q j) / degW D (uOne Q j)

def zed (j : ℕ) : ℝ := 7 * (dY D ^ 2 / tR Q + dY D * rhoB Q j)

def numBase (j : ℕ) : OT.Num where
  D := placeRankTwoOne.dimY D
  DX := dX D j
  f := D.R.f
  r := D.R.r
  m := D.R.m
  L := L.sc.L
  j := qq D j
  nW := Q.nWn
  Np := nCol D j
  lrd := lrd D
  LL := |L.logDerivativeAtOne|
  lM := Real.log (levDeep D L)
  lg := Real.log ((D.host.g 0 : ℝ) * D.host.g 1)
  lg1 := max (Real.log (D.host.g 0)) (Real.log (D.host.g 1))
  lp := max (Real.log D.host.pde) (Real.log D.host.pde')
  ld := Real.log D.host.d
  l4 := Real.log (max (4 * (D.R.n : ℝ) ^ 2) ((D.host.QS : ℝ) ^ 2 / 4) * D.host.q * D.host.d)
  l2q := Real.log ((D.host.QS : ℝ) * D.host.q * D.host.d)
  lx := Real.log L.sc.x
  llx := Real.log (Real.log L.sc.x)
  n := D.R.nV
  w := L.sc.b ^ 2
  a := nKap D j - (D.R.f : ℝ) * D.R.r * D.R.nV / 2
  ka := nKap D j
  u1 := ∑ τ, nrm D (uOne Q j τ)
  DF := degStar D L
  DFs := degStar D L
  RTc := bigR D * tR Q * (bigR D * Q.PP * degStar D L ^ 2 / levQ D L)
  lh := 0
  lNc := 0
  lpi := 0
  lmu := 0
  lmu1 := 0
  V := 0
  hb := 0
  logGenusConstant := 0
  dS := 0
  rS := 0
  dP := 0
  rP := 0
  lNA := 0
  Om := 0
  nu := 0
  lc := 0
  leE := 0
  ln0 := 0
  c1 := 0
  sc1 := 0
  G1 := 0
  CL := 0
  lR := 0
  rho := 0
  dp := 0
  gC := 0

def numAt (j : ℕ) : OT.Num := (numBase Q j).hat

end Run

end GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

end
