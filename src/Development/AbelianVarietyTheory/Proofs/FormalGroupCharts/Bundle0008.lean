module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeNabValBaseChange
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.GaugeBaseChange

open GlobalTheory.QuadDeriv

section

variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {d : ℕ}

theorem map_ev_two {n : ℕ} (a b : Pt k n d) (ha : GP a) (hb : GP b) (f : PS k 2 d) :
    MvPowerSeries.map φ (ev ![a, b] f) = ev ![mapP φ a, mapP φ b] (MvPowerSeries.map φ f) := by
  rw [map_ev φ _ (pair_points_zero_constant ha hb)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem baseChange_zero₂ {n : ℕ} : mapP φ (0 : Pt k n d) = 0 := funext fun _ => map_zero _

theorem map_expS [Algebra ℚ k] [Algebra ℚ k'] {n : ℕ} (f : PS k n d) (hf : constantCoeff f = 0) :
    MvPowerSeries.map φ (FB.expS k f) = FB.expS k' (MvPowerSeries.map φ f) := by
  unfold FB.expS
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf), PowerSeries.map_exp]

theorem map_dpolyOf (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (f : PS k 1 d) :
    MvPowerSeries.map φ (DpolyOf F u P f) =
      DpolyOf (mapP φ F) (fun l i => φ (u l i)) (MvPolynomial.map φ P) (MvPowerSeries.map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GE.dpolyOf_eq_sum_of_subset _ _ (MvPolynomial.map φ P) P.support
    (MvPolynomial.support_map_subset _ _), DpolyOf, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_C, GlobalTheory.map_dmonOf, MvPolynomial.coeff_map]
  rfl

end

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
  {k k' : Type} [CommRing k] [Algebra R k] [CommRing k'] [Algebra R k'] (β : k →ₐ[R] k')

theorem map_map_alg {σ : Type} (f : MvPowerSeries σ R) :
    MvPowerSeries.map (β : k →+* k') (MvPowerSeries.map (algebraMap R k) f) =
      MvPowerSeries.map (algebraMap R k') f := by
  ext m
  simp [coeff_map]

theorem mapP_FK : mapP (β : k →+* k') (B.FK k) = B.FK k' :=
  funext fun i => map_map_alg β (B.G.F i)

theorem baseChange_actK (a : O) : mapP (β : k →+* k') (B.actK k a) = B.actK k' a :=
  funext fun i => map_map_alg β (B.A.act a i)

theorem gp_FK : GP (B.FK k) := constantCoeff_mapP_eq_zero (algebraMap R k) _ B.G.const

theorem gp_actK (a : O) : GP (B.actK k a) := constantCoeff_mapP_eq_zero (algebraMap R k) _ (B.A.const a)

theorem const_of_axis {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) : constantCoeff h = 0 := by
  have := gt_const_ev_eq (n := 1) ![0, pt k d 0] (pair_points_zero_constant gp_zero₂ (gp_pt 0)) h
  rw [← this, h0, map_zero]

variable [Algebra ℚ k] [Algebra ℚ k']

theorem isCanonGauge_map {h : PS k 2 d} (H : B.IsCanonGauge k h) :
    B.IsCanonGauge k' (MvPowerSeries.map (β : k →+* k') h) := by
  have hc := const_of_axis H.ax0
  have c2 : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → constantCoeff (ev ![a, b] h) = 0 :=
    fun a b ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) h hc
  have gA : ∀ {n : ℕ} (i j : Fin n), GP (addOf (B.FK k) (pt k d i) (pt k d j)) :=
    fun i j => gp_addOf _ (gp_FK B) _ _ (gp_pt i) (gp_pt j)
  have gC : ∀ {n : ℕ} (a : O) (i : Fin n), GP (comp1 (B.actK k a) (pt k d i)) :=
    fun a i => gp_comp1 _ _ (gp_actK B a) (gp_pt i)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ax0
    rwa [map_ev_two _ _ _ gp_zero₂ (gp_pt 0), baseChange_zero₂, baseChange_pt, map_zero] at this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ax1
    rwa [map_ev_two _ _ _ (gp_pt 0) gp_zero₂, baseChange_zero₂, baseChange_pt, map_zero] at this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ph1
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, map_add (f := _), c2 _ _ (gp_pt _) (gp_pt _), c2 _ _ (gp_pt _) (gp_pt _),
        c2 _ _ (gA _ _) (gp_pt _), add_zero, sub_zero]), map_sub, map_add,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gp_pt _),
      map_ev_two _ _ _ (gA _ _) (gp_pt _), baseChange_addOf _ _ _ _ (gp_pt _) (gp_pt _), mapP_FK] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ph2
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, map_add (f := _), c2 _ _ (gp_pt _) (gp_pt _), c2 _ _ (gp_pt _) (gp_pt _),
        c2 _ _ (gp_pt _) (gA _ _), add_zero, sub_zero]), map_sub, map_add,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gp_pt _),
      map_ev_two _ _ _ (gp_pt _) (gA _ _), baseChange_addOf _ _ _ _ (gp_pt _) (gp_pt _), mapP_FK] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.sy
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, c2 _ _ (gp_pt _) (gp_pt _), hc, sub_zero]), map_sub,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _)] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) (H.ad a)
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, c2 _ _ (gC _ _) (gp_pt _), c2 _ _ (gp_pt _) (gC _ _), sub_zero]), map_sub,
      map_ev_two _ _ _ (gC _ _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gC _ _),
      baseChange_comp1 _ _ _ (gp_pt _), baseChange_comp1 _ _ _ (gp_pt _), baseChange_actK, baseChange_actK] at this
    simpa only [baseChange_pt] using this

theorem nabVal_map {h : PS k 2 d} (hc : constantCoeff h = 0) (w0 : O) (m : ℕ) (f : PS k 1 d) {Λ : Type}
    [Fintype Λ] (u : Λ → Fin d → k) (Q : MvPolynomial Λ k) :
    B.nabVal k' (MvPowerSeries.map (β : k →+* k') h) w0 m (MvPowerSeries.map (β : k →+* k') f)
      (fun l i => β (u l i)) (MvPolynomial.map (β : k →+* k') Q) = β (B.nabVal k h w0 m f u Q) := by
  have gC : GP (comp1 (B.actK k w0) (pt k (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL k h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map (β : k →+* k') (B.hL k h w0) =
      B.hL k' (MvPowerSeries.map (β : k →+* k') h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), baseChange_actK, baseChange_pt]
  unfold FB.nabVal
  change _ = (β : k →+* k') _
  rw [← MvPowerSeries.constantCoeff_map, map_dpolyOf, mapP_FK, map_mul,
    map_expS _ _ (by rw [MvPowerSeries.smul_eq_C_mul, map_mul, cL, mul_zero]),
    MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast (β : k →+* k'), eL]
  rfl

end GlobalTheory.GaugeBaseChange

namespace GlobalTheory

theorem canonGauge_nabVal_baseChange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k k' : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] [CommRing k'] [Algebra ℚ k'] [Algebra R k'] (β : k →ₐ[R] k') (h : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k' (MvPowerSeries.map (β : k →+* k') h) ∧ ∀ (w0 : O) (m : ℕ) (f : PS k 1 d) (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (Q : MvPolynomial Λ k), B.nabVal k' (MvPowerSeries.map (β : k →+* k') h) w0 m (MvPowerSeries.map (β : k →+* k') f) (fun l i => β (u l i)) (MvPolynomial.map (β : k →+* k') Q) = β (B.nabVal k h w0 m f u Q) := by
  intro R _ d O _ _ B k k' _ _ _ _ _ _ β h H
  exact ⟨GaugeBaseChange.isCanonGauge_map B β H, fun w0 m f _ _ u Q =>
    GaugeBaseChange.nabVal_map B β (GaugeBaseChange.const_of_axis H.ax0) w0 m f u Q⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGaugeFirstLaw
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.GaugeFirstLaw

variable {k : Type} [CommRing k] {d : ℕ}

theorem expS_inj [Algebra ℚ k] {n : ℕ} {a b : PS k n d} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (h : FB.expS k a = FB.expS k b) : a = b := exp_inj ha hb h

theorem expS_zero [Algebra ℚ k] {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := exp_zero

theorem ev_axis {n : ℕ} (a : Pt k n d) (ha : GP a) (h : PS k 2 d) :
    ev ![a] (ev (n := 1) ![pt k d 0, 0] h) = ev ![a, 0] h := by
  rw [gt_ev_ev' _ _ (single_point_zero_constant ha) (pair_points_zero_constant (gp_pt 0) gp_zero₂), eval_pair_points, evP_zero _ (single_point_zero_constant ha),
    evP_pt _ (single_point_zero_constant ha)]
  rfl

theorem pderiv_axis (h : PS k 2 d) (i : Fin d) :
    pderiv ((0 : Fin 1), i) (ev (n := 1) ![pt k d 0, 0] h) =
      ev (n := 1) ![pt k d 0, 0] (pderiv ((0 : Fin 2), i) h) := by
  rw [GlobalTheory.ChartTrans.pderiv_ev _ (pair_points_zero_constant (gp_pt 0) gp_zero₂), Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, map_zero, mul_zero,
    Finset.sum_const_zero, add_zero, pt]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [pderiv_X_of_ne (by simpa using hj), mul_zero]
  · simp

theorem exists_gauge_first_law :
    (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (c : PS k 3 d), ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 → ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c → ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c + ev (n := 4) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c = ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c + ev (n := 4) ![pt k d 0, addOf G.F (pt k d 1) (pt k d 2), pt k d 3] c → ∃ h : PS k 2 d, ev (n := 1) ![0, pt k d 0] h = 0 ∧ (∀ i, ev (n := 1) ![0, pt k d 0] (pderiv ((0 : Fin 2), i) h) = 0) ∧ c = (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (q : ℕ) (g : PS k (q + 1) d), ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1)) (fun j : Fin q => pt k d j.succ.succ)) g = ev (n := q + 2) (Fin.cons (pt k d 0) (fun j : Fin q => pt k d j.succ.succ)) g + ev (n := q + 2) (Fin.cons (pt k d 1) (fun j : Fin q => pt k d j.succ.succ)) g → (∀ i, ev (n := q) (Fin.cons 0 (fun j : Fin q => pt k d j)) (pderiv ((0 : Fin (q + 1)), i) g) = 0) → g = 0) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) := by
  intro H1 H2 k _ _ d O _ _ B
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hA : ∀ {n : ℕ} (i j : Fin n), GP (addOf B.G.F (pt k (n := n) d i) (pt k d j)) :=
    fun i j => gp_addOf _ B.G.const _ _ (hp i) (hp j)
  have h1 : constantCoeff B.ph1 = 1 := by
    have := congrArg constantCoeff B.cocycleLeft_zero_fst
    rwa [gt_const_ev_eq _ (triple_points_zero_constant hz (hp 0) (hp 1)), map_one] at this
  obtain ⟨c, hc0, hc⟩ : ∃ c : PS k 3 d, constantCoeff c = 0 ∧ B.ph1 = FB.expS k c :=
    ⟨_, constantCoeff_logS h1, (exp_log h1).symm⟩
  have E : ∀ {n : ℕ} (V : Fin 3 → Pt k n d), (∀ j, GP (V j)) →
      ev V B.ph1 = FB.expS k (ev V c) ∧ constantCoeff (ev V c) = 0 := by
    intro n V hV
    exact ⟨by rw [hc, gt_ev_expS V hV c hc0], gt_const_ev V hV c hc0⟩
  have a0 : ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 := by
    obtain ⟨e, e0⟩ := E (n := 2) _ (triple_points_zero_constant hz (hp 0) (hp 1))
    refine expS_inj e0 (map_zero _) ?_
    rw [← e, B.cocycleLeft_zero_fst, expS_zero]
  have a2 : ev (n := 2) ![pt k d 0, pt k d 1, 0] c = 0 := by
    obtain ⟨e, e0⟩ := E (n := 2) _ (triple_points_zero_constant (hp 0) (hp 1) hz)
    refine expS_inj e0 (map_zero _) ?_
    rw [← e, B.cocycleLeft_zero_thd, expS_zero]
  have cm : ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c := by
    obtain ⟨e, e0⟩ := E (n := 3) _ (triple_points_zero_constant (hp 1) (hp 0) (hp 2))
    refine expS_inj e0 hc0 ?_
    rw [← e, B.cocycleLeft_comm, hc]
  have as : ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c +
      ev (n := 4) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c =
      ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c +
      ev (n := 4) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2), pt k d 3] c := by
    obtain ⟨e1, f1⟩ := E (n := 4) _ (triple_points_zero_constant (hp 0) (hp 1) (hp 3))
    obtain ⟨e2, f2⟩ := E (n := 4) _ (triple_points_zero_constant (hA 0 1) (hp 2) (hp 3))
    obtain ⟨e3, f3⟩ := E (n := 4) _ (triple_points_zero_constant (hp 1) (hp 2) (hp 3))
    obtain ⟨e4, f4⟩ := E (n := 4) _ (triple_points_zero_constant (hp 0) (hA 1 2) (hp 3))
    refine expS_inj (by rw [map_add (f := _), f1, f2, add_zero]) (by rw [map_add (f := _), f3, f4, add_zero]) ?_
    rw [gt_expS_add _ _ f1 f2, gt_expS_add _ _ f3 f4, ← e1, ← e2, ← e3, ← e4]
    exact B.cocycleLeft_assoc
  obtain ⟨h, hx0, hd, hch⟩ := H1 k d B.G c a0 cm as
  refine ⟨h, ⟨hx0, ?_⟩, by rw [hc, hch]⟩
  have hV : ∀ j, GP ((![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) j) := triple_points_zero_constant (hp 0) (hp 1) hz
  rw [hch, gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hA 0 1) (hp 2)),
    eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ (hp 0) (hp 1),
    evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at a2
  have cons1 : ∀ {n : ℕ} (a : Pt k n d) (r : Fin 0 → Pt k n d),
      (Fin.cons a r : Fin (0 + 1) → Pt k n d) = ![a] := by
    intro n a r
    funext j
    fin_cases j
    rfl
  refine H2 k d B.G 0 (ev (n := 1) ![pt k d 0, 0] h) ?_ ?_
  · rw [cons1, cons1, cons1]
    have t0 := ev_axis (pt k (n := 2) d 0) (hp 0) h
    have t1 := ev_axis (pt k (n := 2) d 1) (hp 1) h
    have t2 := ev_axis _ (hA (n := 2) 0 1) h
    refine t2.trans (Eq.trans ?_ (congrArg₂ (· + ·) t0 t1).symm)
    exact (sub_eq_zero.1 a2).symm
  · intro i
    rw [cons1]
    have hZ : ∀ j, GP ((![0] : Fin 1 → Pt k 0 d) j) := single_point_zero_constant hz
    have e := congrArg (ev (n := 0) ![0]) (hd i)
    rw [gt_ev_ev' _ _ hZ (pair_points_zero_constant hz (hp 0)), eval_pair_points, evP_zero _ hZ, evP_pt _ hZ,
      gt_ev_zero _ hZ] at e
    refine (congrArg (ev (n := 0) ![0]) (pderiv_axis h i)).trans ?_
    rw [ev_axis _ hz]
    exact e

end GlobalTheory.GaugeFirstLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LawRightUnit
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.ChartTrans

namespace GlobalTheory.HomChain

variable {k : Type} [CommRing k] {d : ℕ}

theorem law_right_unit (G : FGLaw k d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  have hs : ∀ j, GP ((![pt k (n := 2) d 1, pt k (n := 2) d 0] : Fin 2 → Pt k 2 d) j) :=
    pair_points_zero_constant (gp_pt 1) (gp_pt 0)
  rw [← G.comm i, gt_ev_ev' _ _ axis_GP hs, eval_pair_points, evP_pt _ axis_GP, evP_pt _ axis_GP]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact G.unit i

theorem dof_hom (G G' : FGLaw k d) (α : Pt k 1 d) (hα : ∀ i, constantCoeff (α i) = 0)
    (hom : comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      G'.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof G.F u (ev (n := 1) ![α] g) = ev (n := 1) ![α] (Dof G'.F ((dLin α).mulVec u) g) := by
  have hφ : GP α := hα
  have h0 : GP (comp1 α (pt k (n := 2) d 0)) := gp_comp1 α _ hφ (gp_pt 0)
  have h1 : GP (comp1 α (pt k (n := 2) d 1)) := gp_comp1 α _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have hF : GP G.F := G.const
  have hF' : GP G'.F := G'.const
  have eF : G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1) = G.F := by
    funext i
    have e : (![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) = pt k d := by
      funext j; fin_cases j <;> rfl
    change ev ![pt k (n := 2) d 0, pt k (n := 2) d 1] (G.F i) = _
    rw [e]
    exact congrFun (MvPowerSeries.subst_self (R := k) (σ := Fin 2 × Fin d)) (G.F i)
  have key : ev (n := 2) ![G.F] (ev (n := 1) ![α] g) =
      ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] (ev (n := 2) ![G'.F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF'), vec1]
    have : evP ![G.F] α = evP ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] G'.F := by
      rw [eF] at hom
      exact hom
    rw [this]
  have pderiv_ev {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j))
      (f : PS k m d) (v : Fin n × Fin d) :
      pderiv (R := k) v (ev V f) =
        ∑ j : Fin m, ∑ l : Fin d, ev V (pderiv (R := k) (j, l) f) * pderiv (R := k) v (V j l) := by
    unfold ev
    rw [GlobalTheory.FormalCalc.pderiv_subst (gt_hasSubst V hV), Fintype.sum_prod_type]
  have dof_eq (L : FGLaw k d) (v : Fin d → k) (f : PS k 1 d) :
      Dof L.F v f = ∑ i, C (v i) *
        ev ![pt k (n := 1) d 0, 0] (pderiv (R := k) ((1 : Fin 2), i) (ev ![L.F] f)) := by
    have hL := single_point_zero_constant L.const
    have eval_axis (h : PS k 1 d) : ev ![pt k (n := 1) d 0, 0] (ev ![L.F] h) = h := by
      rw [gt_ev_ev' _ _ axis_GP hL, vec1,
        show evP ![pt k (n := 1) d 0, 0] L.F = pt k d 0 from funext (law_right_unit L),
        gt_ev_pt_self]
    unfold Dof
    simp only [pderiv_ev _ hL, Fin.sum_univ_one, ev_sum _ axis_GP, gt_ev_mul _ axis_GP,
      eval_axis, Finset.mul_sum, Finset.sum_mul, Matrix.cons_val_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have axis_pderiv_comp (H : PS k 2 d) (i : Fin d) :
      ev ![pt k (n := 1) d 0, 0] (pderiv (R := k) ((1 : Fin 2), i)
        (ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] H)) =
      ∑ l, C (dLin α l i) *
        ev ![α] (ev ![pt k (n := 1) d 0, 0] (pderiv (R := k) ((1 : Fin 2), l) H)) := by
    have eval_comp (K : PS k 2 d) :
        ev ![pt k (n := 1) d 0, 0]
          (ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] K) =
        ev ![α] (ev ![pt k (n := 1) d 0, 0] K) := by
      rw [gt_ev_ev' _ _ axis_GP hΦ, eval_pair_points, evP_comp1 _ axis_GP α _ (gp_pt 0),
        evP_comp1 _ axis_GP α _ (gp_pt 1), evP_pt _ axis_GP, evP_pt _ axis_GP,
        gt_ev_ev' _ _ (single_point_zero_constant hφ) axis_GP, eval_pair_points,
        evP_pt _ (single_point_zero_constant hφ), evP_zero _ (single_point_zero_constant hφ)]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [gt_comp1_pt_right, gt_comp1_zero α hφ]
    have pderiv_comp_pt (b : Fin 2) (l : Fin d) :
        pderiv (R := k) ((1 : Fin 2), i) (comp1 α (pt k (n := 2) d b) l) =
          if (1 : Fin 2) = b then
            ev ![pt k (n := 2) d b] (pderiv (R := k) ((0 : Fin 1), i) (α l)) else 0 := by
      change pderiv (R := k) ((1 : Fin 2), i) (ev ![pt k (n := 2) d b] (α l)) = _
      rw [pderiv_ev _ (single_point_zero_constant (gp_pt b)), Fin.sum_univ_one]
      simp only [Matrix.cons_val_zero, pt]
      split_ifs with h
      · subst b
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          rw [pderiv_X_of_ne (by simpa using hj), mul_zero]
        · simp
      · refine Finset.sum_eq_zero fun j _ => ?_
        rw [pderiv_X_of_ne (fun h' => h (congrArg Prod.fst h').symm), mul_zero]
    have eval_linear (l : Fin d) : ev ![pt k (n := 1) d 0, 0]
        (ev ![pt k (n := 2) d 1] (pderiv (R := k) ((0 : Fin 1), i) (α l))) = C (dLin α l i) := by
      rw [gt_ev_ev' _ _ axis_GP (single_point_zero_constant (gp_pt 1)), vec1, evP_pt _ axis_GP]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [ev_at_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
      simp [dLin]
    rw [pderiv_ev _ hΦ, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_comp_pt,
      one_ne_zero, if_false, if_true, mul_zero, Finset.sum_const_zero, zero_add]
    rw [ev_sum _ axis_GP]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [gt_ev_mul _ axis_GP, eval_comp, eval_linear, mul_comm]
  rw [dof_eq G, dof_eq G', key,
    ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp, ev_C_mul _ (single_point_zero_constant hφ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.HomChain
end
end

