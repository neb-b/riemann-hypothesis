module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0012
public import Formalism.PeriodIntegrals.Bundle0003
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh

@[expose] public section

-- bundled from Formalism.LocalToGlobal.KernelLattices.BaseEx
section
noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker

open Formalism.MainNotions

section HostFacts

variable (D : D7)

def thetaC : ℂ := (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2

def KQuad : Prop := Module.finrank ℚ D.host.K = 2

def ConjOnK : Prop := PI.KerIso.IsConj D.host.K D.host.conj

def TrPos : Prop := ∀ x : D.host.E, x ≠ 0 → 0 < Algebra.trace ℚ D.host.E (x * D.host.conj x)

def CardTau : Prop := Fintype.card D.what₂.Tau = Module.finrank D.host.K D.host.E

def EmbInj : Prop := Function.Injective (TaylorLogMetric.embT D)

def EmbOnK : Prop :=
  ∀ (τ : D.what₂.Tau) (k : D.host.K), TaylorLogMetric.embT D τ (algebraMap D.host.K D.host.E k) = D.host.φ₀ (k : D.host.E)

def PhiNonReal : Prop := ∃ k : D.host.K, (D.host.φ₀ (k : D.host.E)).im ≠ 0

def DMod8 : Prop := D.host.d % 8 = 7

def SqrtInK : Prop :=
  ∃ s : D.host.K, s * s = -(D.host.d : D.host.K) ∧
    D.host.conj (algebraMap D.host.K D.host.E s) = -algebraMap D.host.K D.host.E s

def LatStable : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), ∀ w ∈ TaylorLogMetric.lamOf D cc δ, thetaC D * w ∈ TaylorLogMetric.lamOf D cc δ

def ConjIdeal : Prop :=
  ∀ x : 𝓞 D.host.E, x ∈ D.host.conj • D.host.𝔟 ↔ ∃ y ∈ D.host.𝔟, D.host.conj (y : D.host.E) = (x : D.host.E)

def HostFacts : Prop :=
  KQuad D ∧ ConjOnK D ∧ TrPos D ∧ CardTau D ∧ EmbInj D ∧ EmbOnK D ∧ PhiNonReal D ∧ DMod8 D ∧ SqrtInK D ∧ LatStable D ∧ ConjIdeal D

def MMSelfDual : Prop := PI.KerIso.SelfDualI D.host.K D.host.conj D.host.AA0

def SplitKSplits : Prop := ∀ p : ℕ, p.Prime → SplitK D p → PI.KerIso.SplitsAt D.host.K D.host.conj p

def PeriodExists : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∃ L : PeriodPair, L.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ

end HostFacts

end Formalism.L2.Ker
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.InterlaceAll
section
open MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section Io

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)

def upperParabolic : Pol K ι n →ₐ[K] Pol K ι N := rename (upVar hN)

def zExp (b : ι → Fin n → ℕ) : ι × Fin N × Fin N →₀ ℕ :=
  ∑ τ, ∑ s, Finsupp.single (τ, iL hN, iC hN s) (b τ s)

def bFac (b : ι → Fin n → ℕ) : ℕ := ∏ τ, ∏ s, (b τ s).factorial

def raise (b : ι → Fin n → ℕ) : Pol K ι n →ₗ[K] Pol K ι N :=
  LinearMap.mulLeft K (monomial (zExp hN b) (1 : K)) ∘ₗ (upperParabolic hN).toLinearMap

variable (lam : ι → DomWeight N) (sg : ι → DomWeight n)

def ioConst (K : Type) [Field K] (lam : ι → DomWeight N) (sg : ι → DomWeight n) : K :=
  ∏ τ, ((cBr hN (lam τ) (sg τ) : ℤ) : K) * fockB (xiBr K hN (lam τ) (sg τ)) (xiBr K hN (lam τ) (sg τ)) /
    (fockB (extremal K n (sg τ)) (extremal K n (sg τ)) * ((∏ s, (bExp hN lam sg τ s).factorial : ℕ) : K))

def ioStd : VV K sg →ₗ[K] VV K lam :=
  ioConst hN K lam sg • (projVV lam ∘ₗ raise hN (bExp hN lam sg) ∘ₗ (VV K sg).subtype)

def hTen (K : Type) [Field K] {n : ℕ} (sg : ι → DomWeight n) : Pol K ι n := ten fun τ => extremal K n (sg τ)

def xiTen (K : Type) [Field K] (lam : ι → DomWeight N) (sg : ι → DomWeight n) : Pol K ι N :=
  ten fun τ => xiBr K hN (lam τ) (sg τ)

def SameShiftAll : Prop := ∀ τ, SameShift (lam τ) (sg τ)

def InterlaceAll : Prop := ∀ τ, Interlace hN (lam τ) (sg τ)

def BrTranspose (K : Type) [Field K] : Prop :=
  ∀ (f : VV K lam) (g : VV K sg), pairBK sg (brStd hN lam sg f) g = pairBK lam f (ioStd hN lam sg g)

def IoHw (K : Type) [Field K] [CharZero K] : Prop :=
  InterlaceAll hN lam sg → SameShiftAll lam sg → ∀ h : hTen K sg ∈ VV K sg, (ioStd hN lam sg ⟨hTen K sg, h⟩ : Pol K ι N) = ((∏ τ, (cBr hN (lam τ) (sg τ) : ℤ) : ℤ) : K) • xiTen hN K lam sg

def IoEquiv (K : Type) [Field K] [CharZero K] : Prop :=
  SameShiftAll lam sg → ∀ (g : ι → GL (Fin n) K) (x : VV K sg) (hx : actP sg g x.1 ∈ VV K sg),
    (ioStd hN lam sg ⟨actP sg g x.1, hx⟩ : Pol K ι N) =
      actP lam (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm (g τ)) (ioStd hN lam sg x : Pol K ι N)

def CoefXi (K : Type) [Field K] : Prop :=
  coefLast hN (bExp hN lam sg) (xiTen hN K lam sg) = hTen K sg

end Io

section Fn

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
  (lam : ι → DomWeight N) (sg : ι → DomWeight n)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Fn

section BC

variable {K K' : Type} [Field K] [Field K'] (j : K →+* K') {ι : Type} [Fintype ι] {n : ℕ}

end BC

section One

variable (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)

def toUnit (N : ℕ) : MvPolynomial (Fin N × Fin N) K ≃ₐ[K] Pol K Unit N :=
  renameEquiv K (Equiv.punitProd (Fin N × Fin N)).symm

def brOne : MvPolynomial (Fin N × Fin N) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
  (toUnit K n).symm.toLinearMap ∘ₗ (VV K (fun _ : Unit => sg)).subtype ∘ₗ brStdP hN (fun _ : Unit => lam) (fun _ : Unit => sg) ∘ₗ
    (toUnit K N).toLinearMap

def beOnVal : ℝ := |((cBr hN lam sg : ℤ) : ℝ)| * Real.sqrt (kapBr ℝ hN lam sg)

end One

section Record

open Formalism.MainNotions.product_first_zeroth_parts

def BrOneIsBr (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : Prop :=
  ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) →
    Formalism.MainNotions.PrimeDegreeVariant.IsBr (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ))

def BeOnTie (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : Prop :=
  ∀ τ, (D.fm u).beOn τ = opNorm D u τ (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ))

def BeOnEq (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : Prop :=
  ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) →
    opNorm D u τ (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) =
    beOnVal (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)

def brTen (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ :=
  blk fun τ => brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)

end Record

section Chi

variable {G : Type} [CommGroup G]

end Chi

end Formalism.L2.Ker
end
end

