module

public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataForced
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.DataIdx
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.DefsInst
public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalRingCardinality.DataNChoice
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.LocalRingCardinality.Bundle0006

@[expose] public section

-- bundled from Formalism.LocalRingCardinality.DataExtra
section
namespace Formalism.BasicNotions

open Formalism.MainNotions

def EpTie {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : Prop :=
  ∀ u w hg, (D.gat u w hg).e = X.ep (D.what₂.places.resChar w)

def NuUnserved {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) : Prop :=
  ∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    G.VV X K (G.aL L) (G.bL L) (D.what₂.places.resChar w) = ∅ →
    DV.LocEq (D.plEq w) (L.NuLat u) (DV.MramL D u)

def FillsAll {D : D7} (hT : GatTies D) (Y : G.LatInst D) : Prop :=
  ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)), ∀ j ∈ SizeData₂.lifts D,
    ((Y.Fl u w hg).w v j s : ℝ) = wj D j (hT.gat_pos u w hg ⟨v, s⟩) - G.kaJ D j

structure ExtraC where
  Ce : ℝ
  err : ErrC

structure Extra (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
    (K : G.Consts) (X : DivX D) (cX : ExtraC) where

  lev : LevelData D

  th : ThetaX D

  th_io : th.TieIo

  cmp : LatCmp D

  lat : LatDefs D L Gi Gl K cmp

  tw : TwForms D

  ker : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    LocalToGlobal₂ D hT cmp tw u w h (Gl.Ch u w h)

  ep_def : G.EpDef Gi cX.Ce
  ep_tie : EpTie Gi
  kapI_def : G.KapIDef Gi K
  fills_all : FillsAll hT Gl
  nu_unserved : NuUnserved Gi K

  idx : IdxDefs D X
  kap_def : DV.KapDef D
  lam_def : DV.LamDef D

  kapR_def : DV.KapRBase X

  errX : ErrX D
  err : ErrDefs D L errX lev K cX.err

  nch : NChoice D

  nch_tie : NChTie D nch

  xd : ThData D

  p0 : BaseLevelRowSide D

  rationalRoots_def : p0.s.RRDef

  amb : AmbForm D (RowSide.sharp D)
  amb0 : AmbForm D p0.s

  fdef : L.FDef

  duStar_def : ∀ u, ((D.mem u).A.duStar : ℝ) = StandardLattice.duStarU D u

  Dstar_def : D.what₂.Dstar = StandardLattice.DstarD D

  gauge : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig
  gauge_def : letI := D.host.cmStar; gauge.IsGauge

end Formalism.BasicNotions
end

-- bundled from Formalism.LocalRingCardinality.FourthPowerRankLeNF
section
namespace Formalism.BasicNotions

open Formalism.MainNotions

theorem m_pow_four_le_n {D : D7} (L : SizeData₂ D) (hN : SizeN L) (hM : SizeM L) : D.R.m ^ 4 ≤ D.R.n := by
  obtain ⟨hNl, -⟩ := hN
  obtain ⟨-, hMu⟩ := hM
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he : 0 < L.sc.eps := L.sc.eps_pos
  have hd0 : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg hx0.le _
  have hsq : Real.sqrt (L.sc.x * L.sc.delta1) ^ 2 = L.sc.x * L.sc.delta1 :=
    Real.sq_sqrt (mul_nonneg hx0.le hd0)
  have hth : szTh L = L.sc.eps / 100 := rfl
  have e1 : (L.sc.x ^ szTh L) ^ 4 = L.sc.x ^ (szTh L * 4) := by
    rw [Real.rpow_mul hx0.le]
    first
      | (norm_num; done)
      | exact_mod_cast (Real.rpow_natCast (L.sc.x ^ szTh L) 4).symm
  have e2 : Real.sqrt (L.sc.x * L.sc.delta1) ^ 4 = L.sc.x ^ (2 - L.sc.eps / 4) := by
    have h4 : Real.sqrt (L.sc.x * L.sc.delta1) ^ 4 = (L.sc.x * L.sc.delta1) ^ 2 := by
      calc Real.sqrt (L.sc.x * L.sc.delta1) ^ 4
          = (Real.sqrt (L.sc.x * L.sc.delta1) ^ 2) ^ 2 := by ring
        _ = (L.sc.x * L.sc.delta1) ^ 2 := by rw [hsq]
    have h5 : L.sc.x ^ (2 - L.sc.eps / 4)
        = L.sc.x ^ (2 : ℝ) * L.sc.x ^ (-(L.sc.eps / 8) * 2) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [h4, h5, Real.rpow_mul hx0.le, mul_pow]
    unfold Scale.delta1
    rw [Real.rpow_two, Real.rpow_two]
  have h1 : (D.R.m : ℝ) ^ 4 ≤ (L.sc.x ^ szTh L * Real.sqrt (L.sc.x * L.sc.delta1)) ^ 4 :=
    by
      first
        | exact pow_le_pow_left₀ (Nat.cast_nonneg _) hMu 4
        | gcongr
  have h2 : (L.sc.x ^ szTh L * Real.sqrt (L.sc.x * L.sc.delta1)) ^ 4
      = L.sc.x ^ (szTh L * 4 + (2 - L.sc.eps / 4)) := by
    rw [mul_pow, e1, e2, ← Real.rpow_add hx0]
  have h3 : L.sc.x ^ (szTh L * 4 + (2 - L.sc.eps / 4)) ≤ L.sc.x ^ (2 + 8 * L.sc.eps - szTh L) := by
    apply Real.rpow_le_rpow_of_exponent_le hx.le
    rw [hth]
    linarith
  have h6 : ((D.R.m ^ 4 : ℕ) : ℝ) ≤ ((D.R.n : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h6

theorem m_pow_four_le_f {D : D7} (L : SizeData₂ D) (h : SizesAt L) : D.R.m ^ 4 ≤ D.R.f := by
  obtain ⟨hN, hM, -⟩ := h
  have h4 := m_pow_four_le_n L hN hM
  show D.R.m ^ 4 ≤ 2 * D.R.n
  first
    | omega
    | linarith

end Formalism.BasicNotions
end

