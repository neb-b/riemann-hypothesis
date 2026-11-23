module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0032
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0036

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DepthBoundTest

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

variable {D : D7}

theorem choose_two_add (p q : ℕ) : (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]
    simp only [Nat.choose_one_right]
    ring

theorem dimY_eq_flag {j : ℕ} (hj : InR D j) : WeightFamilies.dimY D j = D.R.f * D.R.r.choose 2 := by
  have h : D.R.r = (D.R.sigW j).1 + (D.R.sigW j).2 := by
    have := hj.1; have := hj.2
    unfold Ranks.r Ranks.sigW; simp only; omega
  unfold WeightFamilies.dimY
  rw [h, choose_two_add, Nat.choose_two_right, Nat.choose_two_right]

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

section Record

variable {B : WeightFamilies.Prov D} {Q : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B Q j)

end Record

end GlobalTheory.DepthBoundTest
