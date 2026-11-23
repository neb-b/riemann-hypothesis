module

public import Formalism.LocalToGlobal.Divisibility.NumbersLink
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementStep
public import Formalism.LocalToGlobal.Divisibility.JetBounds.Bundle0001
public import Formalism.GaussJetBounds.FinalB
public import Formalism.LocalToGlobal.Divisibility.JetBounds.JetBoundsProofs.NormEqOneOfNotMem
public import Mathlib
public import Formalism.LocalToGlobal.ExponentGrids.IntegerShiftClosedExponent
public import Formalism.QuotientMetricDivisors.Bundle0002
public import Formalism.TranslateCocycles.StatementHC
public import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
public import Formalism.SizeWindowBrackets.SBrDiv
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AtG.EntryG

open Formalism.L2.Col (Fields Sp HomE homAt divLat IsSdLat)
open Formalism.L2.Ker (Amb DVar)
open Formalism.L2.AlgTh (KerStd SplitS JetAtSplit IsQInt GAt)
open Formalism.DivisionValues (vw PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols)
open Formalism.L2.DIV (PathData EmbAt IsExpansion ColsInt RowsInt LastInt UnitsInt StabDvd)
open Formalism.AtG (PerBd colRhs)

section Terms

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ}

structure Term (X : Fields) (p : ℕ) [Fact p.Prime] (a b : ℕ) where

  coef : ℂ_[p]

  scal : X.K

  xi : X.K

  S : Finset (HeightOneSpectrum (𝓞 X.E))

  N : Submodule (𝓞 X.E) (Sp X.E a)

  N' : Submodule (𝓞 X.E) (Sp X.E b)

  c' : ℕ

  x : HomE X.E a b

  m : DVar X.Tau a b →₀ ℕ

def Term.val (A : Amb X) (ι : ℂ ≃+* ℂ_[p]) (T : Term X p a b) : ℂ_[p] :=
  T.coef * ι (A.σ₀ T.scal) * ι (A.σ₀ T.xi) * ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))

def Term.Ok (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (T : Term X p a b) : Prop :=
  ‖T.coef‖ ≤ 1 ∧ ‖ι (A.σ₀ T.scal)‖ ≤ 1 ∧ ‖ι (A.σ₀ T.xi)‖ ≤ ‖(p : ℂ_[p])‖ ^ e ∧
  KerStd A T.N T.N' a₀ b₀ c₀ ha hd lam hlam p ι ∧ IsSdLat T.N ∧ IsSdLat T.N' ∧ A.LaHyp a b T.S ∧ SplitS A T.S p ϖ pE ∧
  0 < T.c' ∧ ¬ p ∣ T.c' ∧ T.x ∈ divLat T.c' (homAt T.S T.N T.N') ∧ T.m.degree = D

def IsEntryG (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (a b : ℕ) (y : ℂ_[p]) : Prop :=
  ∃ (n : ℕ) (T : Fin n → Term X p a b), y = ∑ k, (T k).val A ι ∧ ∀ k, (T k).Ok A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e

theorem isEntryG_zero (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (a b : ℕ) : IsEntryG A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e a b 0 :=
  ⟨0, Fin.elim0, by simp, fun k => k.elim0⟩

end Terms

section Place

variable {X : Fields}

end Place

section Record

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Indef

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

end Record

end Formalism.L2.AtG.EntryG
