module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHRed
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.HermitianLattices.StatementLat
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0008
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsCnt
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def Gbd (b C β : ℝ) (Z : GramM D) : ℝ := (2 * β ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f * sizeZ D b C Z ^ 2

theorem embS_star (τ : D.what₂.Tau) (x : D.host.E) : embS D τ (star x) = starRingEnd ℂ (embS D τ x) := by
  unfold embS
  first
  | exact NumberField.IsCMField.complexEmbedding_complexConj _ _
  | exact NumberField.IsCMField.embedding_complexConj _ _
  | exact NumberField.IsCMField.map_complexConj _ _
  | exact (NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (D.host.emb _) x : _)

theorem frameExp_succ : frameExp D.R.rS (D.R.rS + 1) = frameExp D.R.rS D.R.rS := by
  unfold frameExp
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp

def wG : ℝ := D.host.rdE ^ (-(2 * (frameExp D.R.rS D.R.rS : ℝ)))

private theorem one_le_host_rdE : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow _ (by positivity)
  have h := NumberField.discr_ne_zero D.host.E
  have h' : (1 : ℤ) ≤ |discr D.host.E| := Int.one_le_abs h
  have h'' : ((1 : ℤ) : ℝ) ≤ ((|discr D.host.E| : ℤ) : ℝ) := by exact_mod_cast h'
  simpa [Int.cast_abs] using h''

theorem wG_pos : 0 < wG D := by
  unfold wG
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_host_rdE D)) _

theorem absGz_eq {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : FlagU D u')
    (τ : D.what₂.Tau) :
    |Cnt.Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ| = ‖embS D τ (Gval (lf D F0) F')‖ * wG D ^ 2 := by
  have e1 : ∀ x : D.host.E, embS D τ (x * star x) = ((Complex.normSq (embS D τ x) : ℝ) : ℂ) := by
    intro x; rw [map_mul, embS_star, Complex.mul_conj]
  have hG : embS D τ (Gval (lf D F0) F') =
      (((Complex.normSq (embS D τ (leadMinorE (ZhatL (lf D F0) F') (D.R.rS + 1)))) -
        ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) *
          Complex.normSq (embS D τ (leadMinorE (ZhatL (lf D F0) F') D.R.rS)) : ℝ) : ℂ) := by
    show embS D τ (Gflag (lf D F0).fl F'.fl) = _
    unfold Gflag Dl
    rw [map_sub, e1, map_mul, e1, map_mul, map_natCast, map_natCast]
    push_cast
    ring
  rw [hG, Complex.norm_real, Real.norm_eq_abs]
  unfold Cnt.Gz absDl absReal
  rw [frameExp_succ]
  simp only [Complex.normSq_eq_norm_sq]
  rw [← abs_of_pos (pow_pos (wG_pos D) 2), ← abs_mul]
  congr 1
  unfold wG
  ring

end Formalism.MainNotions.S.Pv.HH

end
