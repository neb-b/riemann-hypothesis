module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import ReciprocityTheory.DualLattices.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

structure CycPerfd (p : ℕ) [Fact p.Prime] : Type 1 where
  R : Type
  [ring : CommRing R]
  [nonunit : Fact ¬IsUnit (p : R)]
  [complete : IsAdicComplete (span {(p : R)}) R]
  reg : IsSMulRegular R (p : R)
  ε : PreTilt R p
  zeta_zero : zeta ε 0 = 1
  surj : Function.Surjective (fontaineTheta R p)
  ker_eq : RingHom.ker (fontaineTheta R p) = span {xi ε}

attribute [instance] CycPerfd.ring CycPerfd.nonunit CycPerfd.complete

def CycPerfd.Over {p : ℕ} [Fact p.Prime] (S S' : CycPerfd p) [Algebra S.R S'.R] (α : Ainf p S.R →+* Ainf p S'.R) : Prop :=
  (∀ a, fontaineTheta S'.R p (α a) = algebraMap S.R S'.R (fontaineTheta S.R p a)) ∧
    (∀ a, α (frobenius a) = frobenius (α a)) ∧ α (teichmuller p S.ε) = teichmuller p S'.ε

def CycPerfd.ofIntegers (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) : CycPerfd p where
  R := O
  reg := fun a b h => sub_eq_zero.1 (ReciprocityTheory.PGsh.Ainf.torsion_free p O hv 1 _ (by
    have h' : (p : O) * a = (p : O) * b := h
    rw [pow_one, sub_mul, mul_comm a, mul_comm b, h', sub_self]))
  ε := ε
  zeta_zero := (zeta_succ_pow ε 0).symm.trans hε.pow_eq_one
  surj := ReciprocityTheory.PGsh.Ainf.theta_surj p O hv
  ker_eq := ReciprocityTheory.PGsh.Ainf.ker_theta p O hv ε hε


end GlobalTheory.Published
