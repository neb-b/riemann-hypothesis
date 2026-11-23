module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.DegreeFormula.FlagDegFormula
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.DoubleCosetMeasures.StatementV

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.LatticeTransfer
section
noncomputable section

open NumberField MvPolynomial Finset
open scoped BigOperators

namespace Formalism.MainNotions.LatticeTransfer

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

def wt (Tau : Type) [Fintype Tau] (N : ℕ) : Vm Tau N → ℕ
  | Sum.inl _ => 1
  | Sum.inr (_, k) => k

structure Loc (D : D7) (XD : DivX D) where

  rt : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev) (p : ℕ) [Fact p.Prime]
    (la : XD.PlP p) (z : XD.Mp S κ p la), Bool × Rt D.what₂.Tau (XD.shv S κ).N → (XD.md S κ p la z).Z.LB

  rt_lie : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ)) (i' : Fin (XD.shv S κ).N),
      (i' : ℕ) = i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).lie τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).lie τ).x' i

  rt_om : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
      (i' : Fin (XD.shv S κ).N), (i' : ℕ) = (XD.shv S κ).j + i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).om τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).om τ).x' i

  lieW_gen : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la), ∃ (e : Fin (D.R.f * (XD.shv S κ).N) ≃ Rt D.what₂.Tau (XD.shv S κ).N)
      (V : Fin (D.R.f * (XD.shv S κ).N) → (XD.md S κ p la z).Z.VDiv), ∀ l,
      (XD.md S κ p la z).Z.c1 ((XD.md S κ p la z).lieW.x l) =
        (if ((e l).2 : ℕ) < (XD.shv S κ).j then (1 : ℚ) else -1) •
            (XD.md S κ p la z).Z.c1 (rt S κ p la z (false, e l)) +
          (XD.md S κ p la z).Z.cD (V l)

section One
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

def adm1 : Prop :=
  ∀ p : ℕ, p.Prime → ∀ c : (XD.shv S κ).FibComp p, ¬ (XD.shv S κ).fibInBd p c

end One

def PointsLemma (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ (XD.shv S κ).lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
    (XD.shv S κ).arMix Sx R p
        ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            collapse D _ Q)) -
        (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (Sum.inl τ) * collapse D _ Q) /
          ((p : ℝ) - 1))

section One1
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

end One1

end Formalism.MainNotions.LatticeTransfer

end
end

-- bundled from Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
section
noncomputable section

namespace Formalism.MainNotions.DIV.Align

open Formalism.BasicNotions Formalism.MainNotions

def SmallFirstModulusBelowScale {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ((AbsolutelyIrreducibleSpan.q0 (Fm.D x i) : ℕ) : ℝ) < (Fm.L x i).sc.X'

end Formalism.MainNotions.DIV.Align

end
end

-- bundled from Formalism.SharpRestriction.Divisibility.ZetaProductPairs
section
noncomputable section

namespace Formalism.MainNotions.ZetaProductPairs

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Loc (D : D7) (T : ThetaX D) where

  gl1 : D.what₂.Word → T.Gf (D.sp.Y 0)

  glSym : D.what₂.Word → T.Gf (D.sp.Y 0)

  ArchDat : D.what₂.Word → Type
  ArchDat_ne : ∀ u, Nonempty (ArchDat u)

  ellT : ∀ u, ArchDat u → ℂ

  Au : ∀ u, ArchDat u → ℂ

  B0 : ∀ u, D.what₂.Mu u →ₗ[ℂ] D.what₂.EE →ₗ[ℂ] ℂ

  zeX : D.what₂.Word → D.what₂.Tup → ℂ

  zeta_at_base_tuple : ∀ u, zeX u D.what₂.mu0 = 1

  zeX_fin : ∀ u μ, ∃ n : ℕ, 0 < n ∧ zeX u μ ^ n = 1

variable {D : D7}

variable {T : ThetaX D}

section Local

open MeasureTheory Matrix ComplexConjugate Finset

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

def zetaProd (q : ℝ) (n : ℕ) : ℝ := (qE q 1 n)⁻¹

def idxPar (q : ℝ) (r s : ℕ) : ℝ := TH.parIdx q r s

def Lpair (q : ℝ) (t : ℕ) (x : ℂ) : ℂ :=
  (∏ s ∈ Icc 1 t, ((1 - x * ((q : ℂ) ^ (-(s : ℤ)))) * (1 - x⁻¹ * ((q : ℂ) ^ (-(s : ℤ))))))⁻¹


end Local

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA)
  (GF : ∀ x (i : Fm.Ix x), Formalism.MainNotions.product_first_zeroth_parts.Th22 (Fm.D x i))
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).th)

end Family

end Formalism.MainNotions.ZetaProductPairs

end
end

