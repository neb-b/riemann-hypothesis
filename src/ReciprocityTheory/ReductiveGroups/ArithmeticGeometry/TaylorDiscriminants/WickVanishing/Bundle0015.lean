module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofComm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0014

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CanonB
section
noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.TB.Canon

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {d n l : ℕ}

def ac (A : Q k d 1) (u : Q k d n) : Q k d n := sq ![u] A

private theorem sq_sq_lemma {m : ℕ} (b : Fin n → Q k d l) (a : Fin m → Q k d n) (p : Q k d m) :
    sq b (sq a p) = sq (fun j => sq b (a j)) p :=
  Subtype.ext (funext fun i => sb_sb b a (p.1 i))

@[simp] theorem sq_ac (b : Fin n → Q k d l) (A : Q k d 1) (u : Q k d n) : sq b (ac A u) = ac A (sq b u) := by
  show sq b (sq ![u] A) = sq ![sq b u] A
  have h : (fun j => sq b (![u] j)) = ![sq b u] := by
    funext j; fin_cases j; rfl
  rw [sq_sq_lemma, h]

variable [Algebra ℚ k]




section Transfer

omit [Algebra ℚ k]

theorem formalSeriesValueAtTwoPoints_eq_ev (f : PS k 2 d) (u v : Q k d n) : E2 f u v = ev ![u.1, v.1] f := by
  show sb ![u, v] f = _
  rw [sb_apply]
  congr 1
  funext j; fin_cases j <;> rfl

theorem formalSeriesValueAtThreePoints_eq_ev (f : PS k 3 d) (u v w : Q k d n) : E3 f u v w = ev ![u.1, v.1, w.1] f := by
  show sb ![u, v, w] f = _
  rw [sb_apply]
  congr 1
  funext j; fin_cases j <;> rfl

theorem ac_val (A : Q k d 1) (u : Q k d n) : (ac A u).1 = comp1 A.1 u.1 := by
  funext i
  show sb ![u] (A.1 i) = ev ![u.1] (A.1 i)
  rw [sb_apply]
  congr 1
  funext j; fin_cases j; rfl

def op (F : Q k d 2) (u v : Q k d n) : Q k d n := sq ![u, v] F

theorem op_val (F : Q k d 2) (u v : Q k d n) : (op F u v).1 = addOf F.1 u.1 v.1 := by
  funext i
  show sb ![u, v] (F.1 i) = ev ![u.1, v.1] (F.1 i)
  rw [sb_apply]
  congr 1
  funext j; fin_cases j <;> rfl

theorem sq_op (b : Fin n → Q k d l) (F : Q k d 2) (u v : Q k d n) : sq b (op F u v) = op F (sq b u) (sq b v) := by
  show sq b (sq ![u, v] F) = sq ![sq b u, sq b v] F
  have h : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext j; fin_cases j <;> rfl
  rw [sq_sq_lemma, h]

theorem gen_val (j : Fin n) : (gen j : Q k d n).1 = pt k d j := rfl

variable {R : Type} [CommRing R] (φ : R →+* k)

end Transfer


end ReciprocityTheory.ChartRestriction.G.TB.Canon
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffAddFirstSecond
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section Gen

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_pderiv' {n : ℕ} (f : PS k n d) (v : Fin n × Fin d) :
    constantCoeff (pderiv (R := k) v f) = coeff (Finsupp.single v 1) f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

theorem zero_constant_first_point : CZ (![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) := fun j i => by simp [pt]

theorem zp (h : PS k 2 d) (i : Fin d) (p : Pt k 3 d) (hp : ∀ c, constantCoeff (p c) = 0)
    (hpz : ∀ c, pderiv (R := k) ((2 : Fin 3), i) (p c) = 0) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv (R := k) ((2 : Fin 3), i) (ev (n := 3) ![p, pt k d 2] h)) =
      -ev (n := 2) ![fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (p c)]
        (-ev (n := 1) ![pt k d 0, 0] (pderiv (R := k) ((1 : Fin 2), i) h)) := by
  have hq : CZ (![p, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons hp (CZ.cons (_root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_pt 2) CZ.nil)
  have hp' : CZ (![fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (p c)] : Fin 1 → Pt k 2 d) :=
    CZ.cons (fun c => constantCoeff_ev czZ (hp c)) CZ.nil
  rw [pderiv_ev hq, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hpz, mul_zero, Finset.sum_const_zero,
    zero_add, pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [ev_neg hp', neg_neg, _root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_ev czZ hq, _root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_ev hp' cz1]
  congr 1
  funext j c
  fin_cases j
  · simp [pt_apply, _root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_X hp']
  · simp [pt_apply, _root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_X czZ, ev_zero' hp']

end Gen

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem lawK_F (B : FB R d O) : (lawK k B).F = B.FK k := rfl

theorem cc_h {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have h0 := congrArg constantCoeff hc.ax0
  rw [cc_ev' (by intro j i; fin_cases j <;> simp [pt]), map_zero] at h0
  exact h0

theorem constantCoeff_first_factor (B : FB R d O) : constantCoeff B.ph1 = 1 := by
  have h := congrArg constantCoeff B.cocycleLeft_zero_fst
  rw [cc_ev' (by intro j i; fin_cases j <;> simp [pt]), map_one] at h
  exact h

theorem constantCoeff_add_first_second (B : FB R d O) (l : Fin d) :
    constantCoeff (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) l) = 0 := by
  unfold addOf
  rw [cc_ev' (by intro j i; fin_cases j <;> simp [pt])]
  show constantCoeff (MvPowerSeries.map (algebraMap R k) (B.G.F l)) = 0
  rw [MvPowerSeries.constantCoeff_map, B.G.const l, map_zero]

theorem sig_add {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (i : Fin d) :
    ev (n := 2) ![(lawK k B).F] (sgOf k h i) - ev (n := 2) ![pt k d 0] (sgOf k h i) -
      ev (n := 2) ![pt k d 1] (sgOf k h i) ∈ Ig R k (Fin 2 × Fin d) := by
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (_root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_pt 0) (CZ.cons (_root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_pt 2) CZ.nil)
  have c12 : CZ (![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (_root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_pt 1) (CZ.cons (_root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_pt 2) CZ.nil)
  have cA : CZ (![addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1), pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (constantCoeff_add_first_second B) (CZ.cons (_root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_pt 2) CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h) = 0 := by
    rw [map_sub, map_add (f := _), cc_ev' c02, cc_ev' c12, cc_ev' cA, cc_h hc]
    simp
  have hH := ig_dlog B.ph1 (constantCoeff_first_factor B) _ hH0 hc.ph1 ((2 : Fin 3), i)
  have h2 := ig_ev czZ integral_family_pair_zero hH
  have z0 : ∀ c, pderiv (R := k) ((2 : Fin 3), i) (pt k (n := 3) d 0 c) = 0 := fun c => by simp [pderiv_pt]
  have z1 : ∀ c, pderiv (R := k) ((2 : Fin 3), i) (pt k (n := 3) d 1 c) = 0 := fun c => by simp [pderiv_pt]
  have zA : ∀ c, pderiv (R := k) ((2 : Fin 3), i) (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) c) = 0 := fun c =>
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  rw [map_sub, map_add (f := _), ev_sub czZ, ev_add czZ, zp h i _ (_root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_pt 0) z0, zp h i _ (_root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_pt 1) z1,
    zp h i _ (constantCoeff_add_first_second B) zA] at h2
  have f0 : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pt k (n := 3) d 0 c)) = pt k (n := 2) d 0 := by
    funext c; simp [pt_apply, _root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_X czZ]
  have f1 : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pt k (n := 3) d 1 c)) = pt k (n := 2) d 1 := by
    funext c; simp [pt_apply, _root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_X czZ]
  have fA : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) c)) =
      (lawK k B).F := by
    funext c
    show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k c)) = B.FK k c
    rw [_root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_ev czZ cz01]
    have : (fun j c => ev (n := 2) ![pt k d 0, pt k d 1, 0] ((![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) j c)) =
        fun j => pt k (n := 2) d j := by
      funext j c; fin_cases j <;> simp [pt_apply, _root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_X czZ]
    rw [this, _root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_pt]
  have es : -ev (n := 1) ![pt k d 0, 0] (pderiv (R := k) ((1 : Fin 2), i) h) = sgOf k h i := rfl
  rw [f0, f1, fA, es] at h2
  have e : ev (n := 2) ![(lawK k B).F] (sgOf k h i) - ev (n := 2) ![pt k d 0] (sgOf k h i) -
      ev (n := 2) ![pt k d 1] (sgOf k h i) =
      -ev (n := 2) ![pt k d 0] (sgOf k h i) + -ev (n := 2) ![pt k d 1] (sgOf k h i) -
        -ev (n := 2) ![(lawK k B).F] (sgOf k h i) := by ring
  rw [e]
  exact h2

theorem sig_lin {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (i b : Fin d) :
    ∑ c, pderiv (R := k) ((0 : Fin 1), c) (sgOf k h i) * Jac (lawK k B) c b - C (sg1 k h i b) ∈ Ig R k (Fin 1 × Fin d) := by
  have h3 := ig_ev cz1 integral_family_point_zero (ig_pderiv (sig_add hc i) ((1 : Fin 2), b))
  have d0 : pderiv (R := k) ((1 : Fin 2), b) (ev (n := 2) ![pt k d 0] (sgOf k h i)) = 0 :=
    pderiv_ev_zero zero_constant_first_point _ _ (fun j l => by fin_cases j; simp [pderiv_pt])
  rw [map_sub, map_sub, d0, sub_zero, ev_sub cz1, d_F, d_y, ez_y, ev_sum cz1] at h3
  simp only [ev_mul cz1, ezF, ez_dF, cc_pderiv'] at h3
  exact h3

theorem dof_sig {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (u : Fin d → R) (i : Fin d) :
    Dof (B.FK k) (fun j => algebraMap R k (u j)) (sgOf k h i) -
      C (∑ j, sg1 k h i j * algebraMap R k (u j)) ∈ Ig R k (Fin 1 × Fin d) := by
  have e1 : Dof (B.FK k) (fun j => algebraMap R k (u j)) (sgOf k h i) =
      ∑ b, C (algebraMap R k (u b)) * ∑ c, pderiv (R := k) ((0 : Fin 1), c) (sgOf k h i) * Jac (lawK k B) c b := by
    simp only [Dof, Jac, lawK_F, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have e2 : (C (∑ j, sg1 k h i j * algebraMap R k (u j)) : PS k 1 d) =
      ∑ b, C (algebraMap R k (u b)) * C (sg1 k h i b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine sum_mem fun b _ => ?_
  rw [← mul_sub]
  exact mul_mem (ig_C _) (sig_lin hc i b)

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
end
end

