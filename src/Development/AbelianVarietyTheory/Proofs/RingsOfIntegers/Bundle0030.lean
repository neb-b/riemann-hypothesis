module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionPullbackSourceLevelOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionPullbackSourceLevelOneStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_pullback_sourceLevelOne : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (s : P.U.SecK 1) (F : Fam P.D.toPre (FractionRing V) 1), P.U.Expands 1 s F → ∀ s' : P.U.SecK (1 * N), IsPullByEnd P.U (t.act.act a) 1 N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (1 * N), P.U.Expands (1 * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a 1 N F F' := by
  first | exact @GlobalTheory.PullLevelOne.expands_pull_level_one | exact GlobalTheory.PullLevelOne.expands_pull_level_one | (intros; apply GlobalTheory.PullLevelOne.expands_pull_level_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LevelDvdBadN
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrivLevel

theorem level_dvd_badN (D : D7) {p : ℕ} (hp : p ∈ D.host.levelPrimes) : p ∣ badN D :=
  dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) _

theorem badN_pos_iff (D : D7) : 0 < badN D ↔ 0 ∉ D.host.levelPrimes := by
  have h := D.host.qd_big
  constructor
  · intro hb h0
    exact hb.ne' (Nat.eq_zero_of_zero_dvd (level_dvd_badN D h0))
  · intro h0
    unfold badN
    refine Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega)) (Finset.prod_pos fun p hp => ?_)
    exact Nat.pos_of_ne_zero fun e => h0 (e ▸ hp)

end GlobalTheory.TrivLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LevelNeQ
section
noncomputable section

namespace GlobalTheory.ShortOwnCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

variable {D : D7}

theorem level_ne_q (D : D7) (i : Fin 2) : D.host.g i ≠ D.host.q := by
  intro e
  have hc := D.ntypes.g_cond i
  have hq := D.host.hyp.1
  have h1 : D.host.g i % D.host.q = 1 % D.host.q := by
    rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.d, by ring⟩), hc]
  rw [e, Nat.mod_self, Nat.mod_eq_of_lt hq.one_lt] at h1
  exact zero_ne_one h1

end GlobalTheory.ShortOwnCompare
end
end

