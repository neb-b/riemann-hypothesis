module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.CoefModB

@[expose] public section

open MvPolynomial NumberField
open Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators

section Numbers

variable {n : ℕ}

def Interlace (lam : DomWeight (n + 1)) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, lam.w i.succ ≤ sg.w i ∧ sg.w i ≤ lam.w i.castSucc

def EqualLast (lam : DomWeight (n + 1)) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, i.val + 1 = n → sg.w i = lam.w (Fin.last n)

def aNum (lam : DomWeight (n + 1)) (sg : DomWeight n) (i : Fin n) : ℕ := (sg.w i - lam.w i.succ).toNat

def bNum (lam : DomWeight (n + 1)) (sg : DomWeight n) (i : Fin n) : ℕ := (lam.w i.castSucc - sg.w i).toNat

def dZero (lam : DomWeight (n + 1)) (sg : DomWeight n) : ℤ := ∑ i : Fin n, (sg.w i - lam.w i.succ)

def rangeSet (lam : DomWeight (n + 1)) (sg : DomWeight n) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam.w i.succ) (min (lam.w i.castSucc) (lam.w i.succ + dZero lam sg))

def degDiff (lam : DomWeight (n + 1)) (sg : DomWeight n) : ℤ := ∑ i, lam.w i - ∑ i, sg.w i

end Numbers

section Capelli

variable (K : Type) [Field K] (n : ℕ)

def eOp (i j : Fin (n + 1)) : Module.End K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :=
  ∑ s : Fin (n + 1), (LinearMap.mulLeft K (X (i, s) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) K)) ∘ₗ
    (pderiv (j, s) : Derivation K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) _).toLinearMap

def fOp (u : ℤ) (i j : Fin n) : Module.End K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :=
  (if i = j then (u + ((j.val : ℤ) + 1)) • (1 : Module.End K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K)) else 0) -
    eOp K n i.castSucc j.castSucc

def capelli (u : ℤ) : Module.End K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :=
  ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => fOp K n u (p j) j).prod

variable {n}

def zOp (lam : DomWeight (n + 1)) (sg : DomWeight n) : Module.End K (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :=
  (List.ofFn fun i : Fin n =>
    ((((rangeSet lam sg i).erase (sg.w i)).toList).map fun v =>
      capelli K n (v - lam.w (Fin.last n) - ((i.val : ℤ) + 1))).prod).prod

end Capelli

section Tensors

variable (K : Type) [Field K] {n : ℕ}

abbrev Gen (lam : DomWeight (n + 1)) (sg : DomWeight n) : Type :=
  (∀ i : Fin n, Fin (aNum lam sg i) → Fin (i.val + 1) → Fin n) ×
    (∀ i : Fin n, Fin (bNum lam sg i) → Fin i.val → Fin n)

def piGen (lam : DomWeight (n + 1)) (sg : DomWeight n) (t : Gen lam sg) : MvPolynomial (Fin n × Fin n) K :=
  (∏ i : Fin n, ∏ k : Fin (aNum lam sg i), Formalism.GradedWeylDivisibility.initMinor K (t.1 i k) (Nat.succ_le_of_lt i.isLt)) *
    ∏ i : Fin n, ∏ k : Fin (bNum lam sg i), Formalism.GradedWeylDivisibility.initMinor K (t.2 i k) i.isLt.le

def phiGen (lam : DomWeight (n + 1)) (sg : DomWeight n) (t : Gen lam sg) :
    MvPolynomial (Fin (n + 1) × Fin (n + 1)) K :=
  (∏ i : Fin n, ∏ k : Fin (aNum lam sg i),
      Formalism.GradedWeylDivisibility.initMinor K (fun r => (t.1 i k r).castSucc) (Nat.succ_le_succ i.isLt.le)) *
    ∏ i : Fin n, ∏ k : Fin (bNum lam sg i),
      Formalism.GradedWeylDivisibility.initMinor K (s := i.val + 1)
        (Fin.snoc (α := fun _ => Fin (n + 1)) (fun r : Fin i.val => (t.2 i k r).castSucc) (Fin.last n))
        (Nat.succ_le_succ i.isLt.le)

variable {ι : Type} [Fintype ι]

def piAll (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n) :
    ((∀ τ, Gen (lam τ) (sg τ)) →₀ K) →ₗ[K] Pol K ι n :=
  Finsupp.linearCombination K fun t => ten fun τ => piGen K (lam τ) (sg τ) (t τ)

def zPhiAll (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n) :
    ((∀ τ, Gen (lam τ) (sg τ)) →₀ K) →ₗ[K] Pol K ι (n + 1) :=
  Finsupp.linearCombination K fun t => ten fun τ => zOp K (lam τ) (sg τ) (phiGen K (lam τ) (sg τ) (t τ))

end Tensors

section Maps

variable (K : Type) [Field K] {n : ℕ} {ι : Type} [Fintype ι]

instance finiteVV (lam : ι → DomWeight n) : Module.Finite K (VV K lam) := Module.Finite.of_basis (bVV K lam)

variable [CharZero K]

variable {K}

end Maps

section Statement

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators
