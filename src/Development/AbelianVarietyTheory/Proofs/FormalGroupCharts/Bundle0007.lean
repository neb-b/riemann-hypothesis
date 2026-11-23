module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGaugeOfSymmetry
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.SymGauge

variable {k : Type} [CommRing k] {d : ℕ}

theorem ev_C_mul {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (c : k) (f : PS k m d) :
    ev V (C c * f) = C c * ev V f := by
  rw [gt_ev_mul V hV]
  congr 1
  unfold ev
  rw [MvPowerSeries.subst_C]

theorem expS_inj [Algebra ℚ k] {n : ℕ} {f g : PS k n d} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) (h : FB.expS k f = FB.expS k g) : f = g := exp_inj hf hg h

theorem expS_zero [Algebra ℚ k] {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := exp_zero

theorem exists_gauge_of_symmetry :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → (∀ a, B.ad a = 1) → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ (∀ a : O, (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) = 0) ∧ B.sy = FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h) := by
  intro k _ _ d O _ _ B h1 h2 had
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hF : ∀ i, constantCoeff (B.G.F i) = 0 := B.G.const
  have hsy1 : constantCoeff B.sy = 1 := by
    have := congrArg constantCoeff B.symmetry_zero_fst
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_one] at this
  obtain ⟨s, hs0, hs⟩ : ∃ s : PS k 2 d, constantCoeff s = 0 ∧ FB.expS k s = B.sy :=
    ⟨_, constantCoeff_logS hsy1, exp_log hsy1⟩
  have E : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ev ![a, b] B.sy = FB.expS k (ev ![a, b] s) := by
    intro n a b ha hb
    rw [← hs, gt_ev_expS _ (pair_points_zero_constant ha hb) _ hs0]
  have c0 : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → constantCoeff (ev ![a, b] s) = 0 :=
    fun a b ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) _ hs0

  have anti0 : s + ev (n := 2) ![pt k d 1, pt k d 0] s = 0 := by
    have e := B.sy_inv
    rw [E _ _ (hp 1) (hp 0)] at e
    refine expS_inj (by rw [map_add (f := _), hs0, c0 _ _ (hp 1) (hp 0), add_zero]) (map_zero _) ?_
    rw [gt_expS_add _ _ hs0 (c0 _ _ (hp 1) (hp 0)), hs, e, expS_zero]
  have anti : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ev ![b, a] s = - ev ![a, b] s := by
    intro n a b ha hb
    have hV := pair_points_zero_constant ha hb
    have e := congrArg (ev ![a, b]) anti0
    rw [gt_ev_add _ hV, gt_ev_zero _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 0)), eval_pair_points,
      evP_pt _ hV, evP_pt _ hV] at e
    exact eq_neg_of_add_eq_zero_right e

  have add0 : ev (n := 3) ![pt k d 0, pt k d 1] s + ev (n := 3) ![pt k d 0, pt k d 2] s =
      ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] s := by
    have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    have e := B.sy_law
    rw [h1, h2, ev_one, one_mul, mul_one, E _ _ (hp 0) (hp 1), E _ _ (hp 0) (hp 2), E _ _ (hp 0) hA] at e
    refine expS_inj (by rw [map_add (f := _), c0 _ _ (hp 0) (hp 1), c0 _ _ (hp 0) (hp 2), add_zero])
      (c0 _ _ (hp 0) hA) ?_
    rw [gt_expS_add _ _ (c0 _ _ (hp 0) (hp 1)) (c0 _ _ (hp 0) (hp 2)), e]
  have add2 : ∀ {n : ℕ} (x y z : Pt k n d), GP x → GP y → GP z →
      ev ![x, y] s + ev ![x, z] s = ev ![x, addOf B.G.F y z] s := by
    intro n x y z hx hy hz'
    have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    have hV := triple_points_zero_constant hx hy hz'
    have e := congrArg (ev ![x, y, z]) add0
    rw [gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 1)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) hA), eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 1) (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at e
    exact e
  obtain ⟨c, hc⟩ : ∃ c : k, (C c : PS k 2 d) * 2 = -1 := by
    refine ⟨algebraMap ℚ k (-1 / 2), ?_⟩
    have e : algebraMap ℚ k (-1 / 2) * 2 = -1 := by
      rw [← map_ofNat (algebraMap ℚ k) 2, ← map_mul]
      norm_num
    have := congrArg (C (σ := Fin 2 × Fin d) (R := k)) e
    rwa [map_mul, map_neg, map_one, map_ofNat] at this
  refine ⟨C c * s, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have e := B.symmetry_zero_fst
    rw [E _ _ hz (hp 0), ← expS_zero] at e
    rw [ev_C_mul _ (pair_points_zero_constant hz (hp 0)), expS_inj (c0 _ _ hz (hp 0)) (map_zero _) e, mul_zero]
  · have e := B.symmetry_zero_snd
    rw [E _ _ (hp 0) hz, ← expS_zero] at e
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) hz), expS_inj (c0 _ _ (hp 0) hz) (map_zero _) e, mul_zero]
  · have hA := gp_addOf _ hF _ _ (hp (n := 3) 0) (hp (n := 3) 1)
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 2)), ev_C_mul _ (pair_points_zero_constant (hp 1) (hp 2)), ev_C_mul _ (pair_points_zero_constant hA (hp 2)),
      anti _ _ (hp 2) (hp 0), anti _ _ (hp 2) (hp 1), anti _ _ (hp 2) hA,
      ← add2 _ _ _ (hp 2) (hp 0) (hp 1)]
    ring
  · have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 1)), ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 2)), ev_C_mul _ (pair_points_zero_constant (hp 0) hA),
      ← add0]
    ring
  · intro a
    have hx := gp_comp1 _ _ (B.A.const a) (hp (n := 2) 0)
    have hy := gp_comp1 _ _ (B.A.const (star a)) (hp (n := 2) 1)
    have e := B.ad_sy a
    rw [had, had, ev_one, one_mul, one_mul, E _ _ hx (hp 1), E _ _ (hp 0) hy] at e
    rw [ev_C_mul _ (pair_points_zero_constant hx (hp 1)), ev_C_mul _ (pair_points_zero_constant (hp 0) hy),
      expS_inj (c0 _ _ hx (hp 1)) (c0 _ _ (hp 0) hy) e, sub_self]
  · rw [ev_C_mul _ (pair_points_zero_constant (hp 1) (hp 0)), ← hs]
    congr 1
    linear_combination (-C c) * anti0 + s * hc

end GlobalTheory.SymGauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalCompApplyEqMvPowerSeriesSubst
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ChartInv

variable {k : Type} [CommRing k] {d : ℕ}

theorem formalComp_apply_eq_mvPowerSeries_subst (φ ψ : Pt k 1 d) (i : Fin d) :
    comp1 φ ψ i = (φ i).subst (fun p : Fin 1 × Fin d => ψ p.2) := by
  unfold comp1 ev
  congr 1
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases a
  rfl

theorem linearPart_eq_submatrix (φ : Pt k 1 d) :
    GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2) =
      (dLin φ).submatrix (Equiv.uniqueProd (Fin d) (Fin 1)) (Equiv.uniqueProd (Fin d) (Fin 1)) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  obtain rfl : b = 0 := Subsingleton.elim _ _
  rfl

theorem exists_isInvPair :
    ∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) →
      IsUnit (dLin φ).det → ∃ φi : Pt k 1 d, IsInvPair φ φi := by
  intro k _ d φ h0 hdet
  have hu : ∀ p : Fin 1 × Fin d, constantCoeff ((fun p : Fin 1 × Fin d => φ p.2) p) = 0 :=
    fun p => h0 p.2
  have hA : IsUnit (GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2)) := by
    rw [Matrix.isUnit_iff_isUnit_det, linearPart_eq_submatrix, Matrix.det_submatrix_equiv_self]
    exact hdet
  obtain ⟨v, hv, h1, h2⟩ := (GlobalTheory.FormalInv.exists_substInv_iff hu).2 hA
  have hvv : (fun p : Fin 1 × Fin d => v (0, p.2)) = v := by
    funext ⟨a, j⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  refine ⟨fun i => v (0, i), h0, fun i => hv _, ?_, ?_⟩
  · funext i
    rw [formalComp_apply_eq_mvPowerSeries_subst, hvv]
    exact h1 (0, i)
  · funext i
    rw [formalComp_apply_eq_mvPowerSeries_subst]
    exact h2 (0, i)

end GlobalTheory.ChartInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvGermEvThreePoints
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.SecondLawGauge

variable {k : Type} [CommRing k] {d : ℕ}

theorem gp4 {n : ℕ} {a b c e : Pt k n d} (ha : GP a) (hb : GP b) (hc : GP c) (he : GP e) :
    ∀ j, GP (![a, b, c, e] j) := by
  intro j; fin_cases j; exacts [ha, hb, hc, he]

theorem gp_add (G : FGLaw k d) {n : ℕ} {a b : Pt k n d} (ha : GP a) (hb : GP b) : GP (addOf G.F a b) :=
  gp_addOf _ G.const _ _ ha hb

theorem germEv_germEv_two_points {m n : ℕ} (V : Fin m → Pt k n d) (a b : Pt k m d) (hV : ∀ j, GP (V j)) (ha : GP a)
    (hb : GP b) (f : PS k 2 d) : ev V (ev ![a, b] f) = ev ![evP V a, evP V b] f := by
  rw [gt_ev_ev' V _ hV (pair_points_zero_constant ha hb), eval_pair_points]

theorem germEv_germEv_three_points {m n : ℕ} (V : Fin m → Pt k n d) (a b c : Pt k m d) (hV : ∀ j, GP (V j)) (ha : GP a)
    (hb : GP b) (hc : GP c) (f : PS k 3 d) :
    ev V (ev ![a, b, c] f) = ev ![evP V a, evP V b, evP V c] f := by
  rw [gt_ev_ev' V _ hV (triple_points_zero_constant ha hb hc)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem ev_self3 (f : PS k 3 d) : ev (n := 3) ![pt k d 0, pt k d 1, pt k d 2] f = f := by
  change MvPowerSeries.subst (fun p : Fin 3 × Fin d => (![pt k (n := 3) d 0, pt k d 1, pt k d 2] p.1) p.2) f = f
  have e : (fun p : Fin 3 × Fin d => (![pt k (n := 3) d 0, pt k d 1, pt k d 2] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [e, MvPowerSeries.subst_self]
  rfl

theorem pderiv_ev {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (f : PS k m d)
    (v : Fin n × Fin d) :
    pderiv (R := k) v (ev V f) = ∑ j : Fin m, ∑ l : Fin d, ev V (pderiv (R := k) (j, l) f) * pderiv (R := k) v (V j l) := by
  unfold ev
  rw [GlobalTheory.FormalCalc.pderiv_subst (gt_hasSubst V hV), Fintype.sum_prod_type]

theorem pderiv_pt_ne {n : ℕ} {a b : Fin n} (h : b ≠ a) (i l : Fin d) :
    pderiv (R := k) (a, i) (pt k d b l) = 0 := by
  unfold pt
  rw [pderiv_X_of_ne]
  intro e
  exact h (congrArg Prod.fst e)

theorem pderiv_addOf_zero {n : ℕ} (F : Fin d → PS k 2 d) (a b : Pt k n d) (ha : GP a) (hb : GP b)
    (v : Fin n × Fin d) (h1 : ∀ l, pderiv (R := k) v (a l) = 0) (h2 : ∀ l, pderiv (R := k) v (b l) = 0) (l : Fin d) :
    pderiv (R := k) v (addOf F a b l) = 0 := by
  unfold addOf
  rw [pderiv_ev _ (pair_points_zero_constant ha hb), Fin.sum_univ_two]
  simp [h1, h2]

theorem pderiv_ev_fst {n : ℕ} (a : Fin n) (y : Pt k n d) (hy : GP y) (i : Fin d)
    (h : ∀ l, pderiv (R := k) (a, i) (y l) = 0) (f : PS k 2 d) :
    pderiv (R := k) (a, i) (ev ![pt k d a, y] f) = ev ![pt k d a, y] (pderiv (R := k) ((0 : Fin 2), i) f) := by
  rw [pderiv_ev _ (pair_points_zero_constant (gp_pt a) hy), Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single i]
  · simp [pt]
  · intro l _ hl
    unfold pt
    rw [pderiv_X_of_ne, mul_zero]
    intro e
    exact hl (congrArg Prod.snd e)
  · simp

theorem addOf_zero_left (G : FGLaw k d) {n : ℕ} (b : Pt k n d) (hb : GP b) : addOf G.F 0 b = b := by
  funext i
  have := congrArg (ev ![b]) (G.unit i)
  rw [germEv_germEv_two_points _ _ _ (single_point_zero_constant hb) gp_zero₂ (gp_pt _), evP_zero _ (single_point_zero_constant hb),
    evP_pt _ (single_point_zero_constant hb), gt_ev_X _ (single_point_zero_constant hb)] at this
  exact this

local macro "gp" : tactic =>
  `(tactic| (
    repeat' first
      | assumption
      | apply gp_pt
      | apply gp_zero₂
      | apply gp_addOf
      | apply single_point_zero_constant
      | apply pair_points_zero_constant
      | apply triple_points_zero_constant
      | apply gp4
    done))

private theorem ev_one_for_germ_points {m n : ℕ} (V : Fin m → Pt k n d)
    (hV : ∀ j, GP (V j)) : ev V (1 : PS k m d) = 1 :=
  GlobalTheory.FormalCalc.subst_one' (gt_hasSubst V hV)

local macro "push_ev" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (discharger := gp) only [FGLaw.add, gt_ev_add, gt_ev_sub, gt_ev_mul,
    gt_ev_zero, ev_one_for_germ_points, germEv_germEv_two_points, germEv_germEv_three_points,
    evP_pt, evP_zero, evP_addOf, Matrix.cons_val, one_mul, mul_one] $[$loc]?)

theorem exists_gauge_second_law : (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (c : PS k 3 d), ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 → ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c → ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c + ev (n := 4) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c = ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c + ev (n := 4) ![pt k d 0, addOf G.F (pt k d 1) (pt k d 2), pt k d 3] c → ∃ h : PS k 2 d, ev (n := 1) ![0, pt k d 0] h = 0 ∧ (∀ i, ev (n := 1) ![0, pt k d 0] (pderiv (R := k) ((0 : Fin 2), i) h) = 0) ∧ c = (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (q : ℕ) (g : PS k (q + 1) d), ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1)) (fun j : Fin q => pt k d j.succ.succ)) g = ev (n := q + 2) (Fin.cons (pt k d 0) (fun j : Fin q => pt k d j.succ.succ)) g + ev (n := q + 2) (Fin.cons (pt k d 1) (fun j : Fin q => pt k d j.succ.succ)) g → (∀ i, ev (n := q) (Fin.cons 0 (fun j : Fin q => pt k d j)) (pderiv (R := k) ((0 : Fin (q + 1)), i) g) = 0) → g = 0) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) := by
  intro H1 H2 k _ _ d O _ _ B hB
  have hF := B.G.const
  have c1 : constantCoeff B.ph2 = 1 := by
    have := congrArg constantCoeff B.cocycleRight_zero_fst
    rwa [gt_const_ev_eq _ (by gp), map_one] at this
  obtain ⟨L, hL0, hL⟩ : ∃ L : PS k 3 d, constantCoeff L = 0 ∧ FB.expS k L = B.ph2 :=
    ⟨_, constantCoeff_logS c1, exp_log c1⟩
  have cL : ∀ {n : ℕ} {a b c : Pt k n d}, GP a → GP b → GP c → constantCoeff (ev ![a, b, c] L) = 0 :=
    fun ha hb hc => gt_const_ev _ (triple_points_zero_constant ha hb hc) _ hL0
  have eL : ∀ {n : ℕ} {a b c : Pt k n d}, GP a → GP b → GP c →
      ev ![a, b, c] B.ph2 = FB.expS k (ev ![a, b, c] L) := by
    intro n a b c ha hb hc
    rw [← hL, gt_ev_expS _ (triple_points_zero_constant ha hb hc) _ hL0]
  have inj : ∀ {n : ℕ} {f g : PS k n d}, constantCoeff f = 0 → constantCoeff g = 0 →
      FB.expS k f = FB.expS k g → f = g := fun hf hg h => exp_inj hf hg h
  have inj2 : ∀ {n : ℕ} {f g f' g' : PS k n d}, constantCoeff f = 0 → constantCoeff g = 0 →
      constantCoeff f' = 0 → constantCoeff g' = 0 →
      FB.expS k f * FB.expS k g = FB.expS k f' * FB.expS k g' → f + g = f' + g' := by
    intro n f g f' g' hf hg hf' hg' h
    refine inj (by simp [hf, hg]) (by simp [hf', hg']) ?_
    rw [gt_expS_add _ _ hf hg, gt_expS_add _ _ hf' hg', h]
  have e0 : ∀ {n : ℕ}, FB.expS k (0 : PS k n d) = 1 := exp_zero
  have Lax : ev (n := 2) ![pt k d 1, 0, pt k d 0] L = 0 := by
    have := congrArg (ev (n := 2) ![pt k d 1, pt k d 0]) B.cocycleRight_zero_snd
    push_ev at this
    refine inj (cL (by gp) (by gp) (by gp)) (map_zero _) ?_
    rw [← eL (by gp) (by gp) (by gp), this, e0]
  have Lcomm : ev (n := 3) ![pt k d 2, pt k d 1, pt k d 0] L =
      ev (n := 3) ![pt k d 2, pt k d 0, pt k d 1] L := by
    have := congrArg (ev (n := 3) ![pt k d 2, pt k d 0, pt k d 1]) B.cocycleRight_comm
    push_ev at this
    refine inj (cL (by gp) (by gp) (by gp)) (cL (by gp) (by gp) (by gp)) ?_
    rw [← eL (by gp) (by gp) (by gp), ← eL (by gp) (by gp) (by gp), this]
  have Lassoc : ev (n := 4) ![pt k d 3, pt k d 0, pt k d 1] L +
      ev (n := 4) ![pt k d 3, addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] L =
      ev (n := 4) ![pt k d 3, pt k d 1, pt k d 2] L +
      ev (n := 4) ![pt k d 3, pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] L := by
    have := congrArg (ev (n := 4) ![pt k d 3, pt k d 0, pt k d 1, pt k d 2]) B.cocycleRight_assoc
    push_ev at this
    refine inj2 (cL (by gp) (by gp) (by gp)) (cL (by gp) (by gp) (by gp))
      (cL (by gp) (by gp) (by gp)) (cL (by gp) (by gp) (by gp)) ?_
    rw [← eL (by gp) (by gp) (by gp), ← eL (by gp) (by gp) (by gp), ← eL (by gp) (by gp) (by gp),
      ← eL (by gp) (by gp) (by gp), this]
  have Lint : ev (n := 4) ![addOf B.G.F (pt k d 2) (pt k d 3), pt k d 0, pt k d 1] L =
      ev (n := 4) ![pt k d 2, pt k d 0, pt k d 1] L + ev (n := 4) ![pt k d 3, pt k d 0, pt k d 1] L := by
    have := congrArg (ev (n := 4) ![pt k d 2, pt k d 3, pt k d 0, pt k d 1]) B.interchange
    rw [hB] at this
    push_ev at this
    rw [← zero_add (ev _ L)]
    refine inj2 (map_zero _) (cL (by gp) (by gp) (by gp))
      (cL (by gp) (by gp) (by gp)) (cL (by gp) (by gp) (by gp)) ?_
    rw [← eL (by gp) (by gp) (by gp), ← eL (by gp) (by gp) (by gp), ← eL (by gp) (by gp) (by gp), e0]
    simpa using this
  obtain ⟨g, g0, g1, hg⟩ := H1 k d B.G (ev (n := 3) ![pt k d 2, pt k d 0, pt k d 1] L)
    (by push_ev; exact Lax) (by push_ev; exact Lcomm) (by push_ev; exact Lassoc)
  have hg' : ∀ {n : ℕ} {x a b : Pt k n d}, GP x → GP a → GP b →
      ev ![x, a, b] L = ev ![a, x] g + ev ![b, x] g - ev ![addOf B.G.F a b, x] g := by
    intro n x a b hx ha hb
    have := congrArg (ev ![a, b, x]) hg
    push_ev at this
    exact this
  have g1' : ∀ {n : ℕ} {x : Pt k n d}, GP x → ∀ i, ev ![0, x] (pderiv (R := k) ((0 : Fin 2), i) g) = 0 := by
    intro n x hx i
    have := congrArg (ev ![x]) (g1 i)
    push_ev at this
    exact this
  have hu : ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g -
      ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] g = 0 := by
    refine H2 k d B.G 2 _ ?_ ?_
    · have v : ∀ y : Pt k 4 d, (Fin.cons y (fun j : Fin 2 => pt k d j.succ.succ) : Fin 3 → Pt k 4 d) =
          ![y, pt k d 2, pt k d 3] := by
        intro y; funext j; fin_cases j <;> rfl
      rw [v, v, v]
      push_ev
      rw [hg' (by gp) (by gp) (by gp), hg' (by gp) (by gp) (by gp), hg' (by gp) (by gp) (by gp)] at Lint
      linear_combination Lint
    · intro i
      have v : (Fin.cons 0 (fun j : Fin 2 => pt k d j) : Fin 3 → Pt k 2 d) =
          ![0, pt k d 0, pt k d 1] := by
        funext j; fin_cases j <;> rfl
      rw [v, map_sub, map_add (f := _), pderiv_ev_fst _ _ (by gp) _ (pderiv_pt_ne (by decide) i),
        pderiv_ev_fst _ _ (by gp) _ (pderiv_pt_ne (by decide) i),
        pderiv_ev_fst _ _ (by gp) _ (pderiv_addOf_zero _ _ _ (by gp) (by gp) _
          (pderiv_pt_ne (by decide) i) (pderiv_pt_ne (by decide) i))]
      push_ev
      rw [g1' (by gp), g1' (by gp), g1' (by gp)]
      simp
  refine ⟨ev (n := 2) ![pt k d 1, pt k d 0] g, ⟨?_, ?_⟩, ?_, ?_⟩
  · have := congrArg (ev (n := 1) ![pt k d 0, 0, 0]) hu
    push_ev at this
    rw [addOf_zero_left _ _ (by gp), add_sub_cancel_right] at this
    push_ev
    exact this
  · push_ev
    exact g0
  · have := congrArg (ev (n := 3) ![pt k d 2, pt k d 0, pt k d 1]) hu
    push_ev at this
    push_ev
    exact this
  · push_ev
    rw [← hg' (by gp) (by gp) (by gp), ev_self3, hL]

end GlobalTheory.SecondLawGauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MapMaximalIdealEqKerMapResidue
section
open IsLocalRing TensorProduct

namespace GlobalTheory.FiniteColength

theorem map_maximalIdeal_eq_ker_map_residue (T : Type) [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] (σ : Type) :
    (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T)) =
      RingHom.ker (MvPowerSeries.map (σ := σ) (residue T)) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change MvPowerSeries.map (residue T) (MvPowerSeries.C r) = 0
    rw [MvPowerSeries.map_C, (residue_eq_zero_iff r).2 hr, map_zero]
  · intro g hg
    refine GlobalTheory.FormalIsogeny.mem_map_C_of_coeff_mem (IsNoetherian.noetherian _) fun d => ?_
    rw [← residue_eq_zero_iff, ← MvPowerSeries.coeff_map, RingHom.mem_ker.1 hg, map_zero]

theorem free_finite_quotient : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsAdicComplete (maximalIdeal T) T → ∀ (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : Fin n → MvPowerSeries σ T), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField T))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (f j))) → Module.Free T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) ∧ Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) := by
  intro T _ _ _ hc σ _ n e f h0 hM
  have hfin : Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) :=
    (GlobalTheory.FormalIsogeny.finiteReduction_iff.2 hM).finite_quotient
  refine ⟨?_, hfin⟩
  haveI : Module.Flat T (MvPowerSeries σ T) := _root_.GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing T σ
  haveI : IsLocalHom (algebraMap T (MvPowerSeries σ T)) := ⟨fun r hr => by
    have := MvPowerSeries.isUnit_iff_constantCoeff.1 hr
    exact this⟩
  have hreg := _root_.GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le (ResidueField T) σ n e
    (fun s => MvPowerSeries.map (residue T) (f (e.symm s)))
    (fun s => by rw [MvPowerSeries.constantCoeff_map, h0, map_zero])
    (by
      have : (Set.range fun s => MvPowerSeries.map (σ := σ) (residue T) (f (e.symm s))) =
          Set.range fun j => MvPowerSeries.map (σ := σ) (residue T) (f j) :=
        e.symm.surjective.range_comp fun j => MvPowerSeries.map (σ := σ) (residue T) (f j)
      rw [this]; exact hM)
  simp only [Equiv.symm_apply_apply] at hreg
  let φ : (MvPowerSeries σ T ⧸ (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T))) ≃+*
      MvPowerSeries σ (ResidueField T) :=
    (Ideal.quotEquivOfEq (map_maximalIdeal_eq_ker_map_residue T σ)).trans
      (RingHom.quotientKerEquivOfSurjective
        (GlobalTheory.FormalIsogeny.map_surjective_of_surjective (σ := σ) (residue_surjective (R := T))))
  have hφ : ∀ g, φ (Ideal.Quotient.mk _ g) = MvPowerSeries.map (residue T) g := fun g => rfl
  have hreg' : RingTheory.Sequence.IsWeaklyRegular
      (MvPowerSeries σ T ⧸ (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T)))
      (List.ofFn f) := by
    refine (AddEquiv.isWeaklyRegular_congr (e := φ.toAddEquiv) ?_).2 hreg
    have : (List.ofFn fun i => MvPowerSeries.map (σ := σ) (residue T) (f i)) =
        (List.ofFn f).map (MvPowerSeries.map (σ := σ) (residue T)) := by
      rw [List.map_ofFn]; rfl
    rw [this, List.forall₂_map_right_iff, List.forall₂_same]
    intro r _ x
    change φ (Ideal.Quotient.mk _ r * x) = _ * φ x
    rw [map_mul, hφ]
  have hflat := _root_.GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre T (MvPowerSeries σ T) (List.ofFn f) (fun r hr => by
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hr
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, h0]
    exact not_isUnit_zero) hreg'
  have hI : Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
    unfold Ideal.ofList
    congr 1
    ext r
    exact List.mem_ofFn' _ _
  rw [hI] at hflat
  exact Module.free_of_flat_of_isLocalRing

end GlobalTheory.FiniteColength
end

