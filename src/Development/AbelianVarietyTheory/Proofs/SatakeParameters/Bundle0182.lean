module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EsymmInvMulProd
section
namespace GlobalTheory.ElementarySymmetricInverse

theorem esymm_deg_zero (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

theorem esymm_cons_succ (x : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add (f := _), Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

theorem esymm_top (s : Multiset ℂ) (k : ℕ) (hk : Multiset.card s = k) : s.esymm k = s.prod := by
  subst hk
  simp [Multiset.esymm]

theorem esymm_inv_mul_prod (s : Multiset ℂ) (hs : ∀ x ∈ s, x ≠ 0) :
    ∀ i j : ℕ, i + j = Multiset.card s →
      (s.map fun x => x⁻¹).esymm i * s.prod = s.esymm j := by
  induction s using Multiset.induction_on with
  | empty =>
    intro i j h
    have hi : i = 0 := by simp at h; exact h.1
    have hj : j = 0 := by simp at h; exact h.2
    subst hi hj
    simp [esymm_deg_zero]
  | cons x s ih =>
    intro i j h
    have hx : x ≠ 0 := hs x (Multiset.mem_cons_self x s)
    have ih' := ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy))
    rcases i with _ | i
    · rw [esymm_deg_zero, one_mul, esymm_top _ j (by omega)]
    rcases j with _ | j
    · rw [esymm_deg_zero, esymm_top _ (i + 1) (by rw [Multiset.card_map]; omega),
        Multiset.prod_map_inv']
      exact inv_mul_cancel₀ (Multiset.prod_ne_zero (fun h0 => hs 0 h0 rfl))
    rw [Multiset.card_cons] at h
    rw [Multiset.map_cons, Multiset.prod_cons, esymm_cons_succ, esymm_cons_succ,
      ← ih' (i + 1) j (by omega), ← ih' i (j + 1) (by omega)]
    field_simp
    ring

theorem half_pow (q a : ℕ) :
    (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) ^ a = (q : ℂ) ^ Nat.choose a 2 := by
  have h : ((q : ℝ) ^ (((a : ℝ) - 1) / 2)) ^ a = (q : ℝ) ^ Nat.choose a 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q), ← Real.rpow_natCast,
      Nat.cast_choose_two]
    congr 1
    ring
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h

theorem algSat_eq (a q : ℕ) (B : Multiset ℂˣ) :
    UpperTheory.V.Af.algSat a q B =
      B.map fun b : ℂˣ => (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (b : ℂ) := by
  unfold UpperTheory.V.Af.algSat
  simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_def]

theorem esymm_inv_algSat : ∀ {q : ℕ}, q ≠ (0 : ℕ) → ∀ {a : ℕ} {B : Multiset ℂˣ},
    Multiset.card B = a → ∀ {j : ℕ}, j ≤ a → GlobalTheory.LFun.satEig q a B a ≠ (0 : ℂ) →
    Multiset.esymm (Multiset.map (fun (x : ℂ) ↦ x⁻¹) (UpperTheory.V.Af.algSat a q B)) j =
      Multiset.esymm (UpperTheory.V.Af.algSat a q B) (a - j) *
        (((↑q : ℂ) ^ Nat.choose a (2 : ℕ))⁻¹ * (GlobalTheory.LFun.satEig q a B a)⁻¹) := by
  intro q hq a B hB j hj hne
  have hsat : GlobalTheory.LFun.satEig q a B a = (B.map fun b : ℂˣ => (b : ℂ)).prod := by
    unfold GlobalTheory.LFun.satEig
    rw [esymm_top _ a (by rw [Multiset.card_map, hB])]
    simp
  have hcard : Multiset.card (UpperTheory.V.Af.algSat a q B) = a := by
    rw [algSat_eq, Multiset.card_map, hB]
  have hprod : (UpperTheory.V.Af.algSat a q B).prod =
      (q : ℂ) ^ Nat.choose a 2 * GlobalTheory.LFun.satEig q a B a := by
    rw [hsat, ← half_pow, algSat_eq, Multiset.prod_map_mul,
      Multiset.map_const', Multiset.prod_replicate, hB]
  have hq' : (q : ℂ) ^ Nat.choose a 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hq)
  have hP : (UpperTheory.V.Af.algSat a q B).prod ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero hq' hne
  have hall : ∀ x ∈ UpperTheory.V.Af.algSat a q B, x ≠ 0 := by
    rintro x hx rfl
    exact hP (Multiset.prod_eq_zero hx)
  rw [← esymm_inv_mul_prod _ hall j (a - j) (by omega), hprod]
  field_simp

end GlobalTheory.ElementarySymmetricInverse
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryLiftOperatorIsLabelOperatorWithPartner
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDictionary

set_option maxHeartbeats 4000000

variable {D : D7} {G : Type} [Group G] [Fintype G] {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

section Zero

variable {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks)

theorem hk_zero (V : HSp D) (P : Pl D.host.E) : hk V P 0 = 0 := Finsupp.sum_zero_index

theorem postOn_zero (V : HSp D) {S} (M : DSModel V S) (T : MMap M) : postOn M 0 T = 0 := by
  ext v
  simp [postOn]

theorem hkF_zero (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (F : Bridge.Gf V → W) : hkF V P 0 F = 0 := by
  funext g
  exact Finsupp.sum_zero_index

theorem ops_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H) (hh : IsOpsV R j t h) (y : (R.HV j t).H) : h P 0 y = 0 := by
  refine (hM.HV j t).1 ?_
  rw [hh P hP 0 y, map_zero]
  exact hkF_zero _ _ _

theorem match_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) : MatchW R j t P 0 0 := by
  intro y y' hy
  have h0 : y' = 0 := by
    refine (hM.HV j t).1 ?_
    rw [hy, map_zero]
    exact hkF_zero _ _ _
  have e1 : (R.thG j t) y' = 0 := by rw [h0]; exact (R.thG j t).map_zero
  have e2 : (R.HW j (sg0 D A)).e ((R.thG j t) y') = 0 := by rw [e1]; exact (R.HW j (sg0 D A)).e.map_zero
  refine e2.trans ?_
  rw [hk_zero]
  exact (postOn_zero _ _ _).symm

theorem op_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (o : Module.End D.what₂.LL (A.MtCSD j t).Forms) (ho : o = 0)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H) (hh : IsOpsV R j t h) (x : (A.MtCSD j t).Forms) :
    R.jV j t (o x) = h P 0 (R.jV j t x) := by
  rw [ops_zero R hM j t P hP h hh, ho, LinearMap.zero_apply]
  exact (R.jV j t).map_zero

end Zero

section Cases

variable {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks)

theorem split_good (F : Face D A) (core : Core R F) (t : T) (P : A.ok t) : Good R t (R.pl P) :=
  ((GlobalTheory.GoodPrimes.good_primes R F core.lev).2.2.2 core.fam t P P.2).1

theorem split_low (F : Face D A) (core : Core R F) (hS : SchurAll R) (j : Fin D.R.m) (t : T) (P : A.ok t) (k : ℕ)
    (hk : k ≤ (Vc D j).rank) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R t pl ∧
      (∀ h, IsOpsV R j t h → ∀ x, R.jV j t (A.heckeL j t (P, k) x) = h pl cV (R.jV j t x)) ∧ MatchW R j t pl cV cW := by
  obtain ⟨z, hz, -⟩ := GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime R F core hS j t P
  exact ⟨R.pl P, Finsupp.single (splitLab (Vc D j).rank k) 1, splitC (Wc D j).rank (z k), split_good R F core t P,
    fun h hh x => (GlobalTheory.SplitHeckeLabel.split_ops R F core.lev core.fam core.models).2 j t h hh P k hk x, hz k hk⟩

theorem split_high (F : Face D A) (core : Core R F) (j : Fin D.R.m) (t : T) (P : A.ok t) (k : ℕ)
    (hk : ¬ k ≤ (Vc D j).rank) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R t pl ∧
      (∀ h, IsOpsV R j t h → ∀ x, R.jV j t (A.heckeL j t (P, k) x) = h pl cV (R.jV j t x)) ∧ MatchW R j t pl cV cW := by
  have h0 : A.heckeL j t (P, k) = 0 := (core.fam.degL j t P).2 k (not_le.1 hk)
  have hg := split_good R F core t P
  refine ⟨R.pl P, 0, 0, hg, fun h hh x => ?_, match_zero R core.models j t _⟩
  exact op_zero R core.models j t (R.pl P) hg (A.heckeL j t (P, k)) h0 h hh x

end Cases

section Inert

variable {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (R : RealDat3 D A3 Ks) (F : Face3 D A3)

theorem inert_valid (hH : HoweUnram) (hI : GlobalTheory.Chain.LiftInteg D) (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt)
    (hS : SchurAll R.toRealDat) (j : Fin D.R.m) (t : T) (Q : A3.okI t) (s : List ℕ)
    (hs : Formalism.L2.Col.InertTypeOk (Vc D j).rank s) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t (A3.heckeLI j t (Q, s) x) = h pl cV (R.jV j t x)) ∧
        MatchW R.toRealDat j t pl cV cW := by
  obtain ⟨hCore, -, hGoodI, -, -, -, -⟩ := _root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have core := hCore hEx
  obtain ⟨hg, hconj⟩ := hGoodI t Q Q.2
  have two := _root_.GlobalTheory.Hk3.TwoSidedInert.twoSided_of_inert hH R.toRealDat F.lv2 hI core hS t (R.plI Q) hg hconj (_root_.GlobalTheory.VacFixInert.fixAll_inert R F hC t _ hg hconj)
  obtain ⟨cW, hW⟩ := (two.2 j).1 (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s) 1)
  refine ⟨R.plI Q, Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s) 1, cW, hg, fun h hh x => ?_, hW⟩
  have hty : ∀ i : A3.okI t × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2 →
      Good R.toRealDat t (R.plI i.1) ∧ conjPl (R.plI i.1) = R.plI i.1 ∧
        (GlobalTheory.Hk3.labIn (Vc D j).rank i.2).Pairwise (fun a b => b ≤ a) := by
    intro i hi
    obtain ⟨g1, g2⟩ := hGoodI t i.1 i.1.2
    exact ⟨g1, g2, ((_root_.GlobalTheory.Hk3.labIn_selfDual_iff (Vc D j).rank _).2 ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩
  exact (_root_.GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 core.lev core.fam core.models j t (A3.okI t × List ℕ) (fun i => R.plI i.1)
    (fun i => GlobalTheory.Hk3.labIn (Vc D j).rank i.2) (A3.heckeLI j t) (fun i => Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2) hty
    (hC.inert.hL j t).some (Q, s) hs).2.2.2 h hh x

theorem inert_vanish (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (j : Fin D.R.m) (t : T) (Q : A3.okI t) (s : List ℕ)
    (h0 : A3.heckeLI j t (Q, s) = 0) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t (A3.heckeLI j t (Q, s) x) = h pl cV (R.jV j t x)) ∧
        MatchW R.toRealDat j t pl cV cW := by
  obtain ⟨hCore, -, hGoodI, -, -, -, -⟩ := _root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have core := hCore hEx
  obtain ⟨hg, -⟩ := hGoodI t Q Q.2
  refine ⟨R.plI Q, 0, 0, hg, fun h hh x => ?_, match_zero R.toRealDat core.models j t _⟩
  exact op_zero R.toRealDat core.models j t (R.plI Q) hg (A3.heckeLI j t (Q, s)) h0 h hh x

end Inert

theorem every_op_label : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ j t, ∃ pl cV cW, LiftDict R j t pl cV cW := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hI hC hEx hS hJ j t
  have core := (_root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC).1 hEx
  have key : ∀ i : (A3.liftI j t).OpIx, ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t ((A3.liftI j t).opAll i x) = h pl cV (R.jV j t x)) ∧
      MatchW R.toRealDat j t pl cV cW := by
    rintro (⟨P, k⟩ | ⟨Q, s⟩)
    · by_cases hk : k ≤ (Vc D j).rank
      · exact split_low R.toRealDat F.lv2 core hS j t P k hk
      · exact split_high R.toRealDat F.lv2 core j t P k hk
    · rcases hJ.L j t Q s with h0 | ⟨s', hs', he⟩
      · exact inert_vanish R F hC hEx j t Q s h0
      · have hrank : A3.A.r + A3.A.t = (Vc D j).rank := (R.B.rankL j).symm
        rw [hrank] at hs'
        obtain ⟨pl, cV, cW, g, o, m⟩ := inert_valid R F hH hI hC hEx hS j t Q s' hs'
        refine ⟨pl, cV, cW, g, fun h hh x => ?_, m⟩
        have e : (A3.liftI j t).opAll (Sum.inr (Q, s)) = A3.heckeLI j t (Q, s') := he
        rw [e]
        exact o h hh x
  choose pl cV cW h1 h2 h3 using key
  exact ⟨pl, cV, cW, ⟨h1, fun h hh i x => h2 i h hh x, h3⟩⟩

end GlobalTheory.LiftDictionary

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryRowOperatorIsLabelOperatorWithPartner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowDictR

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hk_zero (V : HSp D) (P : Pl D.host.E) : hk V P 0 = 0 := by
  unfold hk; exact Finsupp.sum_zero_index

theorem hkF_zero (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (F : Bridge.Gf V → W) :
    hkF V P 0 F = 0 := by
  funext h; unfold hkF; exact Finsupp.sum_zero_index

theorem postOn_hk_zero {V : HSp D} {S : _} (M : DSModel V S) (P : Pl D.host.E) (z : MMap M) : postOn M (hk V P 0) z = 0 := by
  rw [hk_zero]
  rfl


set_option maxHeartbeats 1000000 in
theorem entry_zero (R : RealDat3 D A3 Ks) (hM : R.toRealDat.IsModels) (t : T) (i : (A3.rowI t).OpIx) (p : Pl D.host.E)
    (hp : Good R.toRealDat t p) (h0 : ∀ x, (A3.rowI t).opAll i x = 0) :
    ∃ cX c0 : List ℤ →₀ ℂ, (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll i x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
  refine ⟨0, 0, fun h hh x => ?_, fun y y' hy => ?_⟩
  · have hx : (A3.rowI t).opAll i x = 0 := h0 x
    refine (congrArg (R.jX t) hx).trans ((R.jX t).map_zero.trans ?_)
    refine ((hM.HX t).1 ?_).symm
    refine (hh p hp 0 (R.jX t x)).trans ?_
    rw [hkF_zero, LinearMap.map_zero]
  · have hy0 : y' = 0 := (hM.HX t).1 (by rw [hy, LinearMap.map_zero, hkF_zero])
    subst hy0
    have e1 : R.HE.e (R.Th t 0) = 0 := by simp
    exact e1.trans (postOn_hk_zero _ _ _).symm


set_option maxHeartbeats 1000000 in
theorem entry_split (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hL : GlobalTheory.Chain.LiftInteg D) (hW : R.WeakCharacterisation F)
    (hE : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (t : T) (P0 : A3.A.ok t) (k : ℕ) :
    ∃ (p : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ), Good R.toRealDat t p ∧
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll (Sum.inl (P0, k)) x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  have hg : Good R.toRealDat t (R.pl P0.1) :=
    ((_root_.GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hcore.lev).2.2.2 hcore.fam t P0.1 P0.2).1
  by_cases hk : k ≤ D.sp.X'.rank
  · have hz := _root_.GlobalTheory.Hk3.SplitChain.exists_transfer R.toRealDat F.lv2 hL hcore hS t P0
    have hop := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models).1 t
    have hm : MatchE R.toRealDat t (R.pl P0.1) (Finsupp.single (splitLab D.sp.X'.rank k) 1)
        (splitC (Yc D 0).rank (hz.choose k)) := hz.choose_spec.1 k hk
    refine ⟨R.pl P0.1, Finsupp.single (splitLab D.sp.X'.rank k) 1, splitC (Yc D 0).rank (hz.choose k), hg,
      fun h hh x => ?_, hm⟩
    have ex : (A3.rowI t).opAll (Sum.inl (P0, k)) x = A3.A.heckeR t (P0, k) x := rfl
    exact (congrArg (R.jX t) ex).trans (hop h hh P0 k hk x)
  · have hd := (hcore.fam.degR t P0).2 k (not_le.1 hk)
    have h0 : ∀ x, (A3.rowI t).opAll (Sum.inl (P0, k)) x = 0 := fun x =>
      (LinearMap.congr_fun hd x).trans (LinearMap.zero_apply x)
    have hz := entry_zero R hcore.models t (Sum.inl (P0, k)) (R.pl P0.1) hg h0
    exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩


set_option maxHeartbeats 1000000 in
theorem entry_valid (hH : HoweUnram) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hL : GlobalTheory.Chain.LiftInteg D) (hW : R.WeakCharacterisation F)
    (hE : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (t : T) (Q : A3.okI t) (s s' : List ℕ)
    (hs' : Formalism.L2.Col.InertTypeOk D.sp.X'.rank s') (he : A3.heckeRI t (Q, s) = A3.heckeRI t (Q, s')) :
    ∃ (cX c0 : List ℤ →₀ ℂ),
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll (Sum.inr (Q, s)) x) = h (R.plI Q.1) cX (R.jX t x)) ∧
      MatchE R.toRealDat t (R.plI Q.1) cX c0 := by
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  have hQ := (_root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hW).2.2.1
  have hg := (hQ t Q.1 Q.2).1
  have hc := (hQ t Q.1 Q.2).2
  have hTwo := _root_.GlobalTheory.Hk3.TwoSidedInert.twoSided_of_inert hH R.toRealDat F.lv2 hL hcore hS t _ hg hc (_root_.GlobalTheory.VacFixInert.fixAll_inert R F hW t _ hg hc)
  have hpre : ∀ j : A3.okI t × List ℕ, Formalism.L2.Col.InertTypeOk D.sp.X'.rank j.2 →
      Good R.toRealDat t (R.plI j.1.1) ∧ conjPl (R.plI j.1.1) = R.plI j.1.1 ∧
        (GlobalTheory.Hk3.labIn D.sp.X'.rank j.2).Pairwise (fun a b => b ≤ a) := fun j hj =>
    ⟨(hQ t j.1.1 j.1.2).1, (hQ t j.1.1 j.1.2).2, ((_root_.GlobalTheory.Hk3.labIn_selfDual_iff D.sp.X'.rank (GlobalTheory.Hk3.labIn D.sp.X'.rank j.2)).2
      ⟨j.2, hj.2.2, hj.1, hj.2.1, rfl⟩).2.1⟩
  have hR := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models t (A3.okI t × List ℕ)
    (fun j => R.plI j.1.1) (fun j => GlobalTheory.Hk3.labIn D.sp.X'.rank j.2) (A3.heckeRI t)
    (fun j => Formalism.L2.Col.InertTypeOk D.sp.X'.rank j.2) hpre (hW.inert.hR t).some (Q, s') hs'
  have hop := hR.2.2.2
  have hc0 := hTwo.1.1 (Finsupp.single (GlobalTheory.Hk3.labIn D.sp.X'.rank s') 1)
  refine ⟨_, hc0.choose, fun h hh x => ?_, hc0.choose_spec⟩
  have ex : (A3.rowI t).opAll (Sum.inr (Q, s)) x = A3.heckeRI t (Q, s') x := LinearMap.congr_fun he x
  exact (congrArg (R.jX t) ex).trans (hop h hh x)


set_option maxHeartbeats 4000000 in
theorem entry_inert (hH : HoweUnram) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hL : GlobalTheory.Chain.LiftInteg D) (hW : R.WeakCharacterisation F)
    (hE : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (hJ : InertJunk A3) (t : T) (Q : A3.okI t) (s : List ℕ) :
    ∃ (p : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ), Good R.toRealDat t p ∧
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll (Sum.inr (Q, s)) x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  have hg := ((_root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hW).2.2.1 t Q.1 Q.2).1
  by_cases hv : Formalism.L2.Col.InertTypeOk D.sp.X'.rank s
  · have hz := entry_valid hH R F hL hW hE hS t Q s s hv rfl
    exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩
  · have hj := hJ.R t Q s
    rcases hj with h0 | hs
    · have h0' : ∀ x, (A3.rowI t).opAll (Sum.inr (Q, s)) x = 0 := fun x =>
        (LinearMap.congr_fun h0 x).trans (LinearMap.zero_apply x)
      have hz := entry_zero R hcore.models t (Sum.inr (Q, s)) (R.plI Q.1) hg h0'
      exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩
    · have hok : Formalism.L2.Col.InertTypeOk D.sp.X'.rank hs.choose := by
        rw [R.B.rankR]; exact hs.choose_spec.1
      have hz := entry_valid hH R F hL hW hE hS t Q s hs.choose hok hs.choose_spec.2
      exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩


set_option maxHeartbeats 4000000 in
theorem rowDict_exists : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ t, ∃ pl cX c0, RowDict R t pl cX c0 := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hL hW hE hS hJ t
  have key : ∀ i : (A3.rowI t).OpIx, ∃ (p : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ), Good R.toRealDat t p ∧
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll i x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
    rintro (⟨P, k⟩ | ⟨Q, s⟩)
    · exact entry_split R F hL hW hE hS t P k
    · exact entry_inert hH R F hL hW hE hS hJ t Q s
  choose pl cX c0 hg hop hm using key
  exact ⟨pl, cX, c0, ⟨hg, fun h hh i x => hop i h hh x, hm⟩⟩

end GlobalTheory.RowDictR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : (E →+* ℂ) → DomWeight n) (K : Subgroup (UA E n)) (U : Submodule ℂ (UA E n → ℂ)), K ≤ finU (E := E) (n := n) → OfType lam K U → ∀ w₀ : HeightOneSpectrum (𝓞 E), ∃ (W : Wt E n) (f : algForms W), (∀ τ, W.at τ = lam τ) ∧ f ≠ 0 ∧ (∀ v, f.1 v ∈ U) ∧ (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) ∧ ∃ N ∈ nhds (1 : GL (Fin n) (w₀.adicCompletion E)), ∀ x ∈ locU n w₀, cLoc w₀ x ∈ N → ∀ v g, f.1 v (g * x) = f.1 v g := by
  first | (exact @GlobalTheory.Cong.exists_algForm_ofType) | (exact GlobalTheory.Cong.exists_algForm_ofType) | (intros; apply GlobalTheory.Cong.exists_algForm_ofType  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicModularFormMulArchInvariantStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (f : algForms W) (e : UA E n → ℂ), IsAutFormU e → (∀ g, ∀ x ∈ infU E n, e (g * x) = e g) → ∃ f' : algForms W, ∀ v g, f'.1 v g = e g * f.1 v g := by
  first | (exact @GlobalTheory.AlgMul.exists_mul_algForms) | (exact GlobalTheory.AlgMul.exists_mul_algForms) | (intros; apply GlobalTheory.AlgMul.exists_mul_algForms  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_eigenvector_splitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ w, IsSplitAt w → ∀ (J : Subgroup (GL (Fin n) (w.adicCompletion E))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion E))) → ∀ (χ : J →* ℂˣ) (φ : UA E n → ℂ), φ ∈ U → φ ≠ 0 → (∀ x ∈ locU n w, ∀ hx : cLoc w x ∈ J, RU E n x φ = (χ ⟨_, hx⟩ : ℂ) • φ) → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ ∃ v : σ.V, v ≠ 0 ∧ ∀ g : J, σ.ρ g v = (χ g : ℂ) • v := by
  first | (exact @GlobalTheory.SplitEigen.exists_locComp_eigen) | (exact GlobalTheory.SplitEigen.exists_locComp_eigen) | (intros; apply GlobalTheory.SplitEigen.exists_locComp_eigen  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartFormStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAutomorphicOfWeight_of_nonzero_fixed_finPart_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n) (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) → OfType (fun τ => W.at τ) K π.V := by
  first | (exact @GlobalTheory.Cong.ofType_of_finPart_fixed) | (exact GlobalTheory.Cong.ofType_of_finPart_fixed) | (intros; apply GlobalTheory.Cong.ofType_of_finPart_fixed  <;> assumption)
end

