module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussM
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousEvXI

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CruxSt
section
noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def DomZ (n : ℕ) : Set (M2 n) := {x | x ∈ Dom n ∧ (u1 x).det * (ub1 x).det ∈ Complex.slitPlane}

def KappaC : Prop :=
  ∀ (N : ℕ) (t : ℂ), detD (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det ^ t) = ∏ i ∈ Finset.range N, (t + i)

def DjZ : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (j : ℕ) (z : ℂ) (x : M2 n), j ≤ n → x ∈ DomZ n →
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
    (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z)) *
      fz m e z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹

def FzHol : Prop :=
  ∀ (n m : ℕ) (e : ℤ), IsOpen (DomZ n) ∧ GSet n ⊆ DomZ n ∧
    AnalyticOnNhd ℂ (fun p : ℂ × M2 n => fz m e p.1 p.2) (Set.univ ×ˢ DomZ n)

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.TraceTransposeMul
section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR.G

variable {m n : ℕ}

theorem det_gram_eq_zero (hmn : m < n) (x : Fin m → Fin n → ℂ) : (gramX (fun _ : Fin m => true) x).det = 0 := by
  have hg : gramX (fun _ : Fin m => true) x = (Matrix.of x)ᴴ * Matrix.of x := by
    ext i j
    simp [gramX, evX, Qp, Qb, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hg]
  by_contra hne
  have hu : IsUnit ((Matrix.of x)ᴴ * Matrix.of x) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := Matrix.rank_mul_le_right (Matrix.of x)ᴴ (Matrix.of x)
  have h3 := Matrix.rank_le_height (Matrix.of x)
  simp only [Fintype.card_fin] at h1 h3
  omega

theorem trace_transpose_mul' (X Y : Matrix (Fin n) (Fin n) ℂ) : (Xᵀ * Y).trace = (Yᵀ * X).trace := by
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]

end PositivityTheory.Rg.Sw.HSt.L3
end
end

