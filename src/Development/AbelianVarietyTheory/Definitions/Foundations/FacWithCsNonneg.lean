module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HalfLatticeTypes
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants Formalism.HN
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
open Formalism.L2.Pj hiding kap
open GlobalTheory.CompHt hiding rhoB

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P) {T : Par D} {j : ℕ} {l : Level T.H}
  {Xo : Moduli (T.Dw j) l} {c : Coeff l} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
  (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r)

abbrev gKap (T : Par D) (j : ℕ) : WTZ D.host.E := thetaExp D (T.Dw j) (kap D j)

abbrev gKapMinus (T : Par D) (j : ℕ) : WTZ D.host.E := thetaExp D (T.Dw j) (kapMinus D j)

abbrev gTw (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (twW D j)

abbrev gMinus (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uMinus D j)

abbrev gOne (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uOne Q j)

abbrev gTop (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uTop Q j)

abbrev nrmAt (G : WTZ D.host.E) : (c.F →+* ℂ) → cuspW Xo c U G → ℝ := normW U (xiR D) (fun _ => D.sp.W j) dict G

def refConst : ℝ := 1 / 2500

def ccOf : ℝ := (refSum U refConst (gOne Q T j)).toReal + aSum Q j + cInf Q j

theorem comp_nonempty (h : T.Pins) (hj : InR D j) : Nonempty (Comp Xo c) :=
  (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Xo c (by
    rw [(sig_eq h hj).2.2]
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega)).1

set_option synthInstance.maxHeartbeats 100000

variable [StarRing c.F] (h : T.Pins) (hj : InR D j) (CI C2 : ℝ) (Vs : ValFam Xo c) (Hb : Type) [Fintype Hb]
  (NN : Submodule (𝓞 c.F) (cuspW Xo c U (gKap T j)))
  (Ph : cuspW Xo c U (gKapMinus T j) →ₗ[c.F] (Hb → cuspW Xo c U (gKap T j)))
  (e : cuspW Xo c U (gKap T j) →ₗ[c.F] cuspW Xo c U (gKap T j)) (g : ℕ)

def facWith : SlopeBoundLiftData c.F (pageOf Q) where
  w τ := wAn D j τ
  w0 τ := wj D j τ
  c1 τ := GlobalTheory.FlatLine.c1 U (xiR D) (psiOf h.1 τ)
  ua τ := nrm D (uAn D j τ)
  kap := nKap D j
  q' := qq D j
  pq := (pp D j : ℝ) - qq D j
  ι := Comp Xo c
  fι := haveI := CompFin.finite_comp Xo c; Fintype.ofFinite _
  nι := comp_nonempty h hj
  DY := dY D
  A := cA Q j
  cs := cStarInf U (xiR D) (fun _ => D.sp.W j) dict (gOne Q T j)
  X := CI * placeRankTwoOne.LL0 D L * nPrW Q j
  cc := ccOf Q U
  E0 := eZero D j
  Qcc := (numAt Q j).Qc
  ρ := rhoB Q j
  R1 := rOne Q C2 j
  R2 := rTwo Q j
  Bn := ((tN Q - 1).choose (placeRankTwoOne.dimY D) : ℕ)
  δ' := compMean fun Z => delPrime U Z (toWt (T.Dw j) (uOne Q j))
  h Z := compHeight U (xiR D) (fun _ => D.sp.W j) dict Z (gOne Q T j)
  sl Z := (compVolSlope U (xiR D) 8 Vs Z (toWt (T.Dw j) (uPr Q j))).toReal
  δc Z := compDeg U Z (gOne Q T j)
  dc Z := rankOn U Z (gTop Q T j)
  degc Z := degOn U (xiR D) (fun _ => D.sp.W j) dict Z (gTop Q T j)
  PPf := (numAt Q j).Pfl
  mv := shift D
  muU := slopeW_sq U (xiR D) (fun _ => D.sp.W j) dict (gMinus T j)
  nA := cDim (nrmAt U dict (gKapMinus T j))
  nB := cDim (piNorm Hb (nrmAt U dict (gKap T j)))
  nN := cDim (nrmAt U dict (gKap T j))
  XA := frameCo _
  XB := frameCo _
  XN := frameCo _
  LA := latCo _ (latW U (gKapMinus T j))
  LB := latCo _ (piLat Hb NN)
  NN := latCo _ NN
  Mk := latCo _ (latW U (gKap T j))
  φ := mapCo _ _ Ph
  e := mapCo _ _ e
  g := g
  PPh := 3 / 2 * Real.log (Fintype.card Hb) + (numAt Q j).U0
  abelian₂ := lamKap Q j + Real.log (Fintype.card Hb)
  δ := del D
  o' := GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.ringCost c.F
  n2 := measureMove D L

variable {U dict}

end GlobalTheory.SlopeRec
