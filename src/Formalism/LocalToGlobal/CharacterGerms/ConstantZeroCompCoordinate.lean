module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0026
public import Formalism.LocalToGlobal.CharacterGerms.PderivDoubleMultiplicationJacobian
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0018

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def zl {C : Type} [Field C] {dd : ℕ} (v : Fin dd → C) (F : PS C 2 dd) : PS C 1 dd :=
  ∑ j, MvPowerSeries.C (v j) * ev (n := 1) ![pt C dd 0, 0] (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), j) F)

namespace SelfAdjointLinearTerm

open PartialDerivEval FirstUnitSeriesIntegrality MulLFrob LiftedCoordinateEvaluation MvPowerSeries

variable {C : Type} [Field C] {dd : ℕ}

theorem snd_map (ν : Fin 1 × Fin dd →₀ ℕ) :
    (ν.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) = ν := by
  rw [← Finsupp.mapDomain_comp]
  have e : ((fun x : Fin dd => ((0 : Fin 1), x)) ∘ Prod.snd) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [e, Finsupp.mapDomain_id]

theorem snd_mapDomain_mapDomain (ν : Fin 1 × Fin dd →₀ ℕ) :
    (ν.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) =
      ν.mapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) := by
  rw [← Finsupp.mapDomain_comp]
  rfl

end SelfAdjointLinearTerm

open SelfAdjointLinearTerm in
theorem coeff_zl {C : Type} [Field C] {dd : ℕ} (v : Fin dd → C) (F : PS C 2 dd) (ν : Fin 1 × Fin dd →₀ ℕ) :
    MvPowerSeries.coeff ν (zl v F) = ∑ j, v j * MvPowerSeries.coeff
      (ν.mapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) + Finsupp.single ((1 : Fin 2), j) 1) F := by
  unfold zl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coeff_C_mul]
  conv_lhs => rw [← snd_map ν]
  rw [coeff_eval_second_zero, MvPowerSeries.coeff_pderiv, snd_mapDomain_mapDomain]
  have h0 : (ν.mapDomain fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) ((1 : Fin 2), j) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨x, hx⟩
    have h01 : (0 : Fin 2) = 1 := congrArg Prod.fst hx
    exact absurd h01 (by decide)
  rw [h0]
  simp

namespace SelfAdjointLinearTerm

open PartialDerivEval FirstUnitSeriesIntegrality MulLFrob LiftedCoordinateEvaluation MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

theorem aux_statement_9 : Z0 (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) := by
  intro k i
  fin_cases k
  · simp [pt]
  · simp

theorem zl_sub (v : Fin dd → C) (F G : PS C 2 dd) : zl v (F - G) = zl v F - zl v G := by
  have hS : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => aux_statement_9 p.1 p.2)
  simp only [zl, ev, map_sub, MvPowerSeries.subst_sub hS, mul_sub, Finset.sum_sub_distrib]

theorem zl_smul (v : Fin dd → C) (c : C) (F : PS C 2 dd) : zl v (c • F) = c • zl v F := by
  have hS : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => aux_statement_9 p.1 p.2)
  simp only [zl, ev, Derivation.map_smul, LinearMap.map_smul, MvPowerSeries.subst_smul hS, Finset.smul_sum,
    mul_smul_comm]

theorem zl_expS (v : Fin dd → C) {f : PS C 2 dd} (hf : constantCoeff f = 0)
    (hf0 : ev (n := 1) ![pt C dd 0, 0] f = 0) : zl v (FB.expS C f) = zl v f := by
  unfold zl
  refine Finset.sum_congr rfl fun j _ => ?_
  have hd : pderiv (R := C) ((1 : Fin 2), j) (FB.expS C f) =
      FB.expS C f * pderiv (R := C) ((1 : Fin 2), j) f := by
    unfold FB.expS
    rw [Formalism.G.LogCR.pderiv_psubst hf, PowerSeries.derivative_exp]
  rw [hd, Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_mul aux_statement_9,
    FirstUnitSeriesIntegrality.expS_eq, FirstUnitSeriesIntegrality.ev_ex aux_statement_9 f hf,
    hf0, ex_zero, one_mul]

def PAB (A B : Pt C 1 dd) : Fin 2 → Pt C 2 dd := ![comp1 A (pt C (n := 2) dd 0), comp1 B (pt C (n := 2) dd 1)]

theorem constant_zero_comp_coordinate {n : ℕ} {A : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0) (k : Fin n) (i : Fin dd) :
    constantCoeff (comp1 A (pt C (n := n) dd k) i) = 0 := by
  simp only [comp1, ev]
  have hc : ∀ p : Fin 1 × Fin dd, constantCoeff ((![pt C dd k] : Fin 1 → Pt C n dd) p.1 p.2) = 0 := by
    intro p
    simp only [Matrix.cons_val_fin_one, pt, MvPowerSeries.constantCoeff_X]
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  · exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  · exact hc
  · exact hA i

theorem zPAB {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0) (hB : ∀ i, constantCoeff (B i) = 0) :
    Z0 (PAB A B) := by
  intro k i
  fin_cases k
  · simpa [PAB] using constant_zero_comp_coordinate hA 0 i
  · simpa [PAB] using constant_zero_comp_coordinate hB 1 i

theorem product_points_at_zero {A B : Pt C 1 dd} (hB : ∀ i, constantCoeff (B i) = 0) :
    (fun k i => ev (n := 1) ![pt C dd 0, 0] (PAB A B k i)) = (![A, 0] : Fin 2 → Pt C 1 dd) := by
  funext k i
  fin_cases k
  · show ev (n := 1) ![pt C dd 0, 0] (ev ![pt C (n := 2) dd 0] (A i)) = A i
    rw [ev_ev (z0_1 _ fun j => z0_pt 0 j) aux_statement_9]
    have : (fun (k : Fin 1) (i : Fin dd) => ev (n := 1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 0] : Fin 1 → Pt C 2 dd) k i)) =
        ![pt C (n := 1) dd 0] := by
      funext k i
      fin_cases k
      exact ev_X aux_statement_9 0 i
    rw [this, germEval_oneStandardPoint_self]
  · show ev (n := 1) ![pt C dd 0, 0] (ev ![pt C (n := 2) dd 1] (B i)) = 0
    rw [ev_ev (z0_1 _ fun j => z0_pt 1 j) aux_statement_9]
    have : (fun (k : Fin 1) (i : Fin dd) => ev (n := 1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k i)) =
        ![(0 : Pt C 1 dd)] := by
      funext k i
      fin_cases k
      exact ev_X aux_statement_9 1 i
    rw [this, ev_zero_pt, hB i, map_zero]

theorem d_A (A : Pt C 1 dd) (j k : Fin dd) :
    pderiv (R := C) ((1 : Fin 2), j) (comp1 A (pt C (n := 2) dd 0) k) = 0 := by
  show pderiv (R := C) ((1 : Fin 2), j) (ev ![pt C (n := 2) dd 0] (A k)) = 0
  have hsingle {P : Pt C 2 dd} (hP : ∀ m, constantCoeff (P m) = 0) (g : PS C 1 dd)
      (q : Fin 2 × Fin dd) :
      pderiv (R := C) q (ev ![P] g) =
        ∑ m, ev ![P] (pderiv (R := C) ((0 : Fin 1), m) g) * pderiv (R := C) q (P m) := by
    unfold ev
    rw [Formalism.G.LogCR.pderiv_subst
      (a := fun p : Fin 1 × Fin dd => (![P] : Fin 1 → Pt C 2 dd) p.1 p.2)
      (fun p => by obtain ⟨t, m⟩ := p; fin_cases t; exact hP m) g q,
      Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  rw [hsingle (fun m => z0_pt 0 m) (A k) ((1 : Fin 2), j)]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [show pt C dd 0 m = X ((0 : Fin 2), m) from rfl,
    pderiv_X_of_ne (by
      intro h
      have h' := congrArg Prod.fst h
      exact (by decide : (0 : Fin 2) ≠ 1) h'), mul_zero]

theorem d_B (B : Pt C 1 dd) (j k : Fin dd) :
    pderiv (R := C) ((1 : Fin 2), j) (comp1 B (pt C (n := 2) dd 1) k) =
      ev ![pt C (n := 2) dd 1] (pderiv (R := C) ((0 : Fin 1), j) (B k)) := by
  show pderiv (R := C) ((1 : Fin 2), j) (ev ![pt C (n := 2) dd 1] (B k)) = _
  have hsingle {P : Pt C 2 dd} (hP : ∀ m, constantCoeff (P m) = 0) (g : PS C 1 dd)
      (q : Fin 2 × Fin dd) :
      pderiv (R := C) q (ev ![P] g) =
        ∑ m, ev ![P] (pderiv (R := C) ((0 : Fin 1), m) g) * pderiv (R := C) q (P m) := by
    unfold ev
    rw [Formalism.G.LogCR.pderiv_subst
      (a := fun p : Fin 1 × Fin dd => (![P] : Fin 1 → Pt C 2 dd) p.1 p.2)
      (fun p => by obtain ⟨t, m⟩ := p; fin_cases t; exact hP m) g q,
      Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  rw [hsingle (fun m => z0_pt 1 m) (B k) ((1 : Fin 2), j), Finset.sum_eq_single j]
  · rw [show pt C dd 1 j = X ((1 : Fin 2), j) from rfl, pderiv_X_self, mul_one]
  · intro m _ hm
    rw [show pt C dd 1 m = X ((1 : Fin 2), m) from rfl,
      pderiv_X_of_ne (fun h => hm (Prod.mk.inj h).2), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem eval_pderiv_constant_linear (B : Pt C 1 dd) (j k : Fin dd) :
    ev (n := 1) ![pt C dd 0, 0] (ev ![pt C (n := 2) dd 1] (pderiv (R := C) ((0 : Fin 1), j) (B k))) =
      MvPowerSeries.C (coeff (Finsupp.single ((0 : Fin 1), j) 1) (B k)) := by
  rw [ev_ev (z0_1 _ fun j => z0_pt 1 j) aux_statement_9]
  have : (fun (k : Fin 1) (i : Fin dd) => ev (n := 1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k i)) =
      ![(0 : Pt C 1 dd)] := by
    funext k i
    fin_cases k
    exact ev_X aux_statement_9 1 i
  rw [this, ev_zero_pt, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

variable {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem zl_hAB (Y : FBChart C V O dd) {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0)
    (hB : ∀ i, constantCoeff (B i) = 0) (v : Fin dd → C) :
    zl v (ev (PAB A B) Y.h) = -ev (n := 1) ![A] (Y.sgP (linAct B v)) := by
  have hsg : ev (n := 1) ![A] (Y.sgP (linAct B v)) =
      -∑ i, MvPowerSeries.C (linAct B v i) *
        ev (n := 1) ![A, 0] (pderiv (R := C) ((1 : Fin 2), i) Y.h) := by
    have hZ : Z0 (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) := aux_statement_9
    have hZA : Z0 (![A] : Fin 1 → Pt C 1 dd) := z0_1 A hA
    unfold FBChart.sgP
    rw [ev_neg hZA, ev_sum hZA]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_mul hZA, PartialDerivEval.ev_C, ev_ev hZ hZA]
    congr 2
    funext k j
    fin_cases k
    · exact ev_X hZA 0 j
    · exact ev_zero hZA
  rw [hsg, neg_neg]
  unfold zl
  have h1 : ∀ j, ev (n := 1) ![pt C dd 0, 0] (pderiv (R := C) ((1 : Fin 2), j) (ev (PAB A B) Y.h)) =
      ∑ k, ev (n := 1) ![A, 0] (pderiv (R := C) ((1 : Fin 2), k) Y.h) *
        MvPowerSeries.C (coeff (Finsupp.single ((0 : Fin 1), j) 1) (B k)) := by
    intro j
    have hpPair (g : PS C 2 dd) (q : Fin 2 × Fin dd) :
        pderiv (R := C) q (ev (PAB A B) g) =
          ∑ k, ev (PAB A B) (pderiv (R := C) ((0 : Fin 2), k) g) *
              pderiv (R := C) q (PAB A B 0 k) +
            ∑ k, ev (PAB A B) (pderiv (R := C) ((1 : Fin 2), k) g) *
              pderiv (R := C) q (PAB A B 1 k) := by
      unfold ev
      rw [Formalism.G.LogCR.pderiv_subst
        (a := fun p : Fin 2 × Fin dd => PAB A B p.1 p.2)
        (fun p => zPAB hA hB p.1 p.2) g q,
        Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [hpPair Y.h ((1 : Fin 2), j)]
    have e0 : ∑ k, ev (PAB A B) (pderiv (R := C) ((0 : Fin 2), k) Y.h) * pderiv (R := C) ((1 : Fin 2), j) (PAB A B 0 k) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        rw [show PAB A B 0 k = comp1 A (pt C (n := 2) dd 0) k from rfl, d_A, mul_zero]
    rw [e0, zero_add, ev_sum aux_statement_9]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show PAB A B 1 k = comp1 B (pt C (n := 2) dd 1) k from rfl, d_B, Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_mul aux_statement_9, eval_pderiv_constant_linear,
      ev_ev (zPAB hA hB) aux_statement_9, product_points_at_zero hB]
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold linAct
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

theorem height_at_zero_product (Y : FBChart C V O dd) {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0)
    (hB : ∀ i, constantCoeff (B i) = 0) : ev (n := 1) ![pt C dd 0, 0] (ev (PAB A B) Y.h) = 0 := by
  rw [ev_ev (zPAB hA hB) aux_statement_9, product_points_at_zero hB]
  have h := congrArg (ev (n := 1) ![A]) Y.gauge.ax1
  rw [ev_ev aux_statement_9 (z0_1 A hA), ev_zero (z0_1 A hA)] at h
  have : (fun (k : Fin 2) (i : Fin dd) => ev (n := 1) ![A] ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) k i)) =
      (![A, 0] : Fin 2 → Pt C 1 dd) := by
    funext k i
    fin_cases k
    · exact ev_X (z0_1 A hA) 0 i
    · exact ev_zero (z0_1 A hA)
  rw [this] at h
  exact h

theorem const_hAB (Y : FBChart C V O dd) {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0)
    (hB : ∀ i, constantCoeff (B i) = 0) : constantCoeff (ev (PAB A B) Y.h) = 0 :=
  const_ev (zPAB hA hB) (h_const Y)

theorem comp1_identity_left {n : ℕ} (k : Fin n) : comp1 (pt C (n := 1) dd 0) (pt C (n := n) dd k) = pt C dd k := by
  funext i
  simp only [comp1, ev, pt]
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
    simp only [Matrix.cons_val_fin_one, pt, MvPowerSeries.constantCoeff_X]))]
  rfl

theorem linAct_id (v : Fin dd → C) : linAct (pt C (n := 1) dd 0) v = v := by
  funext i
  unfold linAct
  rw [Finset.sum_eq_single i]
  · show coeff (Finsupp.single ((0 : Fin 1), i) 1) (X ((0 : Fin 1), i) : PS C 1 dd) * v i = v i
    rw [coeff_X, if_pos rfl, one_mul]
  · intro j _ hj
    show coeff (Finsupp.single ((0 : Fin 1), j) 1) (X ((0 : Fin 1), i) : PS C 1 dd) * v j = 0
    rw [coeff_X, if_neg, zero_mul]
    intro h
    apply hj
    have := (Finsupp.single_left_inj (one_ne_zero)).1 h
    exact (Prod.mk.inj this).2
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem zId : ∀ i, constantCoeff (pt C (n := 1) dd 0 i) = 0 := fun i => by simp [pt]

end SelfAdjointLinearTerm


open SelfAdjointLinearTerm PartialDerivEval FirstUnitSeriesIntegrality MulLFrob in
theorem linear_part_first_unit {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (v : Fin dd → C) :
    zl v Y.u1 = (V.l : C) • Y.sgP v - ev (n := 1) ![mulL Y.B.G.F V.l] (Y.sgP v) := by
  have hM : ∀ i, MvPowerSeries.constantCoeff (mulL Y.B.G.F V.l i) = 0 :=
    FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l
  have e1 : (![comp1 (mulL Y.B.G.F V.l) (pt C (n := 2) dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) =
      SelfAdjointLinearTerm.PAB (mulL Y.B.G.F V.l) (pt C (n := 1) dd 0) := by
    unfold SelfAdjointLinearTerm.PAB
    rw [SelfAdjointLinearTerm.comp1_identity_left]
  have e2 : ev (SelfAdjointLinearTerm.PAB (pt C (n := 1) dd 0) (pt C (n := 1) dd 0)) Y.h = Y.h := by
    unfold SelfAdjointLinearTerm.PAB
    rw [SelfAdjointLinearTerm.comp1_identity_left, SelfAdjointLinearTerm.comp1_identity_left,
      PartialDerivEval.eval_points_two]
  have e3 : ev (n := 2) ![comp1 (mulL Y.B.G.F V.l) (pt C (n := 2) dd 0), pt C dd 1] Y.h - (V.l : C) • Y.h =
      ev (SelfAdjointLinearTerm.PAB (mulL Y.B.G.F V.l) (pt C (n := 1) dd 0)) Y.h -
        (V.l : C) • ev (SelfAdjointLinearTerm.PAB (pt C (n := 1) dd 0) (pt C (n := 1) dd 0)) Y.h := by
    rw [e1, e2]
  unfold FBChart.u1
  rw [e3, SelfAdjointLinearTerm.zl_expS v
      (by rw [map_sub, SelfAdjointLinearTerm.const_hAB Y hM SelfAdjointLinearTerm.zId, MvPowerSeries.smul_eq_C_mul, map_mul, SelfAdjointLinearTerm.const_hAB Y SelfAdjointLinearTerm.zId SelfAdjointLinearTerm.zId, mul_zero,
        sub_zero])
      (by rw [PartialDerivEval.ev_sub SelfAdjointLinearTerm.aux_statement_9, SelfAdjointLinearTerm.height_at_zero_product Y hM SelfAdjointLinearTerm.zId, MvPowerSeries.smul_eq_C_mul, PartialDerivEval.ev_mul SelfAdjointLinearTerm.aux_statement_9, SelfAdjointLinearTerm.height_at_zero_product Y SelfAdjointLinearTerm.zId SelfAdjointLinearTerm.zId, mul_zero,
        sub_zero]),
    SelfAdjointLinearTerm.zl_sub, SelfAdjointLinearTerm.zl_smul, SelfAdjointLinearTerm.zl_hAB Y hM SelfAdjointLinearTerm.zId, SelfAdjointLinearTerm.zl_hAB Y SelfAdjointLinearTerm.zId SelfAdjointLinearTerm.zId, SelfAdjointLinearTerm.linAct_id, MulLFrob.germEval_oneStandardPoint_self, smul_neg]
  ring


open SelfAdjointLinearTerm PartialDerivEval FirstUnitSeriesIntegrality MulLFrob in
theorem constant_zero_first_zero_self {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (e eb : Pt C 1 dd) (he0 : ∀ i, MvPowerSeries.constantCoeff (e i) = 0)
    (heb0 : ∀ i, MvPowerSeries.constantCoeff (eb i) = 0) (v : Fin dd → C) :
    zl v (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h)) =
      Y.sgP (linAct eb v) - ev (n := 1) ![e] (Y.sgP v) := by
  have e1 : (![comp1 e (pt C (n := 2) dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) = SelfAdjointLinearTerm.PAB e (pt C (n := 1) dd 0) := by
    unfold SelfAdjointLinearTerm.PAB
    rw [SelfAdjointLinearTerm.comp1_identity_left]
  have e2 : (![pt C (n := 2) dd 0, comp1 eb (pt C dd 1)] : Fin 2 → Pt C 2 dd) = SelfAdjointLinearTerm.PAB (pt C (n := 1) dd 0) eb := by
    unfold SelfAdjointLinearTerm.PAB
    rw [SelfAdjointLinearTerm.comp1_identity_left]
  rw [e1, e2, SelfAdjointLinearTerm.zl_expS v
      (by rw [map_sub, SelfAdjointLinearTerm.const_hAB Y he0 SelfAdjointLinearTerm.zId, SelfAdjointLinearTerm.const_hAB Y SelfAdjointLinearTerm.zId heb0, sub_zero])
      (by rw [PartialDerivEval.ev_sub SelfAdjointLinearTerm.aux_statement_9, SelfAdjointLinearTerm.height_at_zero_product Y he0 SelfAdjointLinearTerm.zId, SelfAdjointLinearTerm.height_at_zero_product Y SelfAdjointLinearTerm.zId heb0, sub_zero]),
    SelfAdjointLinearTerm.zl_sub, SelfAdjointLinearTerm.zl_hAB Y he0 SelfAdjointLinearTerm.zId, SelfAdjointLinearTerm.zl_hAB Y SelfAdjointLinearTerm.zId heb0, SelfAdjointLinearTerm.linAct_id, MulLFrob.germEval_oneStandardPoint_self]
  ring

end Formalism.L2.FormalSeriesBounds
