module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ChartTrans

variable {k : Type} [CommRing k] {d : ℕ}

theorem pderiv_ev {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (f : PS k m d)
    (v : Fin n × Fin d) :
    pderiv v (ev V f) = ∑ j : Fin m, ∑ l : Fin d, ev V (pderiv (j, l) f) * pderiv v (V j l) := by
  unfold ev
  rw [GlobalTheory.FormalCalc.pderiv_subst (gt_hasSubst V hV), Fintype.sum_prod_type]

theorem ev_sum {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) {α : Type} (s : Finset α)
    (f : α → PS k m d) : ev V (∑ a ∈ s, f a) = ∑ a ∈ s, ev V (f a) :=
  GlobalTheory.FormalCalc.subst_sum' (gt_hasSubst V hV) s f

theorem ev_C {m n : ℕ} (V : Fin m → Pt k n d) (r : k) : ev V (C r : PS k m d) = C r := by
  unfold ev
  rw [MvPowerSeries.subst_C]

theorem ev_C_mul {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (r : k) (f : PS k m d) :
    ev V (C r * f) = C r * ev V f := by
  rw [gt_ev_mul V hV, ev_C]

theorem vec1 {m n : ℕ} (V : Fin m → Pt k n d) (a : Pt k m d) :
    (fun j => evP V (![a] j)) = ![evP V a] := by
  funext j; fin_cases j; rfl

theorem ev_at_zero {n : ℕ} (f : PS k 1 d) : ev ![(0 : Pt k n d)] f = C (constantCoeff f) := by
  have e : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  conv_lhs => rw [e]
  rw [gt_ev_add _ (single_point_zero_constant gp_zero₂), ev_C]
  have h2 : ev ![(0 : Pt k n d)] (f - C (constantCoeff f)) = 0 := by
    change MvPowerSeries.subst (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) _ = 0
    have e : (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) = 0 := by
      funext p; simp
    rw [e]
    exact MvPowerSeries.subst_zero_of_constantCoeff_zero h0
  rw [h2, add_zero]

theorem axis_GP : ∀ j, GP ((![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) j) :=
  pair_points_zero_constant (gp_pt 0) gp_zero₂

theorem dof_eq (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof F u g = ∑ i, C (u i) *
      ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv ((1 : Fin 2), i) (ev (n := 2) ![F] g)) := by
  have hF1 : ∀ j, GP ((![F] : Fin 1 → Pt k 2 d) j) := single_point_zero_constant hF
  have hS : ∀ h : PS k 1 d, ev (n := 1) ![pt k (n := 1) d 0, 0] (ev (n := 2) ![F] h) = h := by
    intro h
    rw [gt_ev_ev' _ _ axis_GP hF1, vec1]
    have : evP ![pt k (n := 1) d 0, 0] F = pt k (n := 1) d 0 := funext hu
    rw [this, gt_ev_pt_self]
  unfold Dof
  simp only [pderiv_ev _ hF1, Fin.sum_univ_one, ev_sum _ axis_GP, gt_ev_mul _ axis_GP, hS,
    Finset.mul_sum, Finset.sum_mul, Matrix.cons_val_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pderiv_comp_pt (φ : Pt k 1 d) (a b : Fin 2) (i l : Fin d) :
    pderiv (a, i) (comp1 φ (pt k (n := 2) d b) l) =
      if a = b then ev ![pt k (n := 2) d b] (pderiv ((0 : Fin 1), i) (φ l)) else 0 := by
  change pderiv (a, i) (ev ![pt k (n := 2) d b] (φ l)) = _
  rw [pderiv_ev _ (single_point_zero_constant (gp_pt b)), Fin.sum_univ_one]
  simp only [Matrix.cons_val_zero, pt]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [pderiv_X_of_ne (by simpa using hj), mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [pderiv_X_of_ne (fun h' => h (congrArg Prod.fst h').symm), mul_zero]

theorem axis_pderiv_comp (φ : Pt k 1 d) (hφ : GP φ) (H : PS k 2 d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv ((1 : Fin 2), i)
      (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] H)) =
    ∑ l, C (dLin φ l i) *
      ev ![φ] (ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv ((1 : Fin 2), l) H)) := by
  have hΦ : ∀ j, GP (![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] j) :=
    pair_points_zero_constant (gp_comp1 φ _ hφ (gp_pt 0)) (gp_comp1 φ _ hφ (gp_pt 1))
  have hK : ∀ K : PS k 2 d, ev (n := 1) ![pt k (n := 1) d 0, 0]
      (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] K) =
      ev ![φ] (ev (n := 1) ![pt k (n := 1) d 0, 0] K) := by
    intro K
    rw [gt_ev_ev' _ _ axis_GP hΦ, eval_pair_points, evP_comp1 _ axis_GP φ _ (gp_pt 0),
      evP_comp1 _ axis_GP φ _ (gp_pt 1), evP_pt _ axis_GP, evP_pt _ axis_GP,
      gt_ev_ev' _ _ (single_point_zero_constant hφ) axis_GP, eval_pair_points, evP_pt _ (single_point_zero_constant hφ), evP_zero _ (single_point_zero_constant hφ)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [gt_comp1_pt_right, gt_comp1_zero φ hφ]
  have hL : ∀ l, ev (n := 1) ![pt k (n := 1) d 0, 0]
      (ev ![pt k (n := 2) d 1] (pderiv ((0 : Fin 1), i) (φ l))) = C (dLin φ l i) := by
    intro l
    rw [gt_ev_ev' _ _ axis_GP (single_point_zero_constant (gp_pt 1)), vec1, evP_pt _ axis_GP]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ev_at_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
    simp [dLin]
  rw [pderiv_ev _ hΦ, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_comp_pt]
  simp only [one_ne_zero, ite_false, ite_true, mul_zero, Finset.sum_const_zero, zero_add]
  rw [ev_sum _ axis_GP]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [gt_ev_mul _ axis_GP, hK, hL, mul_comm]

theorem dof_transF (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (φ φi : Pt k 1 d) (hinv : IsInvPair φ φi) (u : Fin d → k) (g : PS k 1 d) :
    Dof (transF F φ φi) u (ev (n := 1) ![φ] g) =
      ev (n := 1) ![φ] (Dof F ((dLin φ).mulVec u) g) := by
  have hφ : GP φ := hinv.1
  have hφi : GP φi := hinv.2.1
  have h0 : GP (comp1 φ (pt k (n := 2) d 0)) := gp_comp1 φ _ hφ (gp_pt 0)
  have h1 : GP (comp1 φ (pt k (n := 2) d 1)) := gp_comp1 φ _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have hA := gp_addOf F hF _ _ h0 h1
  have eF : transF F φ φi =
      comp1 φi (addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) := rfl
  have hF' : GP (transF F φ φi) := eF ▸ gp_comp1 φi _ hφi hA
  have hax : addOf F φ 0 = φ := by
    have e1 : addOf F (pt k (n := 1) d 0) 0 = pt k (n := 1) d 0 := funext hu
    have e2 := congrArg (evP ![φ]) e1
    rwa [evP_addOf _ (single_point_zero_constant hφ) _ _ _ (gp_pt 0) gp_zero₂, evP_pt _ (single_point_zero_constant hφ),
      evP_zero _ (single_point_zero_constant hφ)] at e2
  have hu' : evP ![pt k (n := 1) d 0, 0] (transF F φ φi) = pt k (n := 1) d 0 := by
    rw [eF, evP_comp1 _ axis_GP _ _ hA, evP_addOf _ axis_GP _ _ _ h0 h1,
      evP_comp1 _ axis_GP φ _ (gp_pt 0), evP_comp1 _ axis_GP φ _ (gp_pt 1),
      evP_pt _ axis_GP, evP_pt _ axis_GP]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [gt_comp1_pt_right, gt_comp1_zero φ hφ, hax, hinv.2.2.2]
  have key : ev (n := 2) ![transF F φ φi] (ev (n := 1) ![φ] g) =
      ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (ev (n := 2) ![F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF') (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF), vec1]
    have : evP ![transF F φ φi] φ = evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] F :=
      gt_comp_inv hinv _ hA
    rw [this]
  rw [dof_eq _ hF' (congrFun hu'), dof_eq F hF hu, key, ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp φ hφ, ev_C_mul _ (single_point_zero_constant hφ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem transPolySt : TransPolySt := by
  intro k _ d F hF hu φ φi hinv ι _ u P g
  have hφ : GP φ := hinv.1
  have hit : ∀ (v : Fin d → k) (n : ℕ) (g : PS k 1 d),
      (Dof (transF F φ φi) v)^[n] (ev (n := 1) ![φ] g) =
        ev (n := 1) ![φ] ((Dof F ((dLin φ).mulVec v))^[n] g) := by
    intro v n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dof_transF F hF hu φ φi hinv, ih]
  have hmon : ∀ m : ι →₀ ℕ, DmonOf (transF F φ φi) u m (ev (n := 1) ![φ] g) =
      ev (n := 1) ![φ] (DmonOf F (fun l => (dLin φ).mulVec (u l)) m g) := by
    intro m
    unfold DmonOf
    induction (Finset.univ : Finset ι).toList with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]
  unfold DpolyOf
  rw [ev_sum _ (single_point_zero_constant hφ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_C_mul _ (single_point_zero_constant hφ), hmon]

end GlobalTheory.ChartTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeOfSteps
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.CanonGaugeAssembly

variable {k : Type} [CommRing k] {d : ℕ}

theorem const_of_ax {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) :
    constantCoeff h = 0 := by
  have := congrArg constantCoeff h0
  rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this

theorem cancel_expS [Algebra ℚ k] {n : ℕ} {p c : PS k n d} (hc : constantCoeff c = 0)
    (e : FB.expS k c = p * FB.expS k c) : p = 1 := by
  have u : FB.expS k c * FB.expS k (-c) = 1 := by
    rw [← gt_expS_add _ _ hc (by rw [map_neg, hc, neg_zero]), add_neg_cancel, nt_expS_zero]
  calc p = p * FB.expS k c * FB.expS k (-c) := by rw [mul_assoc, u, mul_one]
    _ = 1 := by rw [← e, u]

structure Cob {n : ℕ} (c : PS k 2 d → PS k n d) : Prop where
  add : ∀ f g, c (f + g) = c f + c g
  const : ∀ f, constantCoeff f = 0 → constantCoeff (c f) = 0

theorem cob_three {n : ℕ} (U V W : Fin 2 → Pt k n d) (hU : ∀ j, GP (U j)) (hV : ∀ j, GP (V j))
    (hW : ∀ j, GP (W j)) : Cob (fun h : PS k 2 d => ev U h + ev V h - ev W h) := by
  constructor
  · intro f g
    rw [gt_ev_add U hU, gt_ev_add V hV, gt_ev_add W hW]; ring
  · intro f hf
    rw [map_sub, map_add constantCoeff, gt_const_ev U hU f hf, gt_const_ev V hV f hf,
      gt_const_ev W hW f hf]; simp

theorem cob_two {n : ℕ} (U V : Fin 2 → Pt k n d) (hU : ∀ j, GP (U j)) (hV : ∀ j, GP (V j)) :
    Cob (fun h : PS k 2 d => ev U h - ev V h) := by
  constructor
  · intro f g
    rw [gt_ev_add U hU, gt_ev_add V hV]; ring
  · intro f hf
    rw [map_sub, gt_const_ev U hU f hf, gt_const_ev V hV f hf]; simp

theorem cob_swap (U : Fin 2 → Pt k 2 d) (hU : ∀ j, GP (U j)) :
    Cob (fun h : PS k 2 d => ev U h - h) := by
  constructor
  · intro f g
    rw [gt_ev_add U hU]; ring
  · intro f hf
    rw [map_sub, gt_const_ev U hU f hf, hf]; simp

theorem Cob.chain [Algebra ℚ k] {n : ℕ} {c : PS k 2 d → PS k n d} (hc : Cob c)
    {h₁ h₂ h₃ h₄ : PS k 2 d} (c₁ : constantCoeff h₁ = 0) (c₂ : constantCoeff h₂ = 0)
    (c₃ : constantCoeff h₃ = 0) (c₄ : constantCoeff h₄ = 0) {p₀ p₁ p₂ p₃ : PS k n d}
    (e₁ : p₀ = p₁ * FB.expS k (c h₁)) (e₂ : p₁ = p₂ * FB.expS k (c h₂))
    (e₃ : p₂ = p₃ * FB.expS k (c h₃)) (e₄ : p₃ = FB.expS k (c h₄)) :
    p₀ = FB.expS k (c (h₁ + h₂ + h₃ + h₄)) := by
  have k₁ := hc.const _ c₁
  have k₂ := hc.const _ c₂
  have k₃ := hc.const _ c₃
  have k₄ := hc.const _ c₄
  rw [hc.add, hc.add, hc.add, gt_expS_add _ _ (by simp [k₁, k₂, k₃]) k₄,
    gt_expS_add _ _ (by simp [k₁, k₂]) k₃, gt_expS_add _ _ k₁ k₂, e₁, e₂, e₃, e₄]
  ring

end GlobalTheory.CanonGaugeAssembly


open GlobalTheory.CanonGaugeAssembly in
theorem GlobalTheory.canonGauge_of_steps :
    (∀ (R k : Type) [CommRing R] [CommRing k] (f : R →+* k) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ B' : FB k d O, (∀ i, B'.G.F i = MvPowerSeries.map f (B.G.F i)) ∧ (∀ a i, B'.A.act a i = MvPowerSeries.map f (B.A.act a i)) ∧ B'.ph1 = MvPowerSeries.map f B.ph1 ∧ B'.ph2 = MvPowerSeries.map f B.ph2 ∧ B'.sy = MvPowerSeries.map f B.sy ∧ ∀ a, B'.ad a = MvPowerSeries.map f (B.ad a)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O) (h : PS k 2 d), (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) → ∃ B' : FB k d O, B'.G.F = B.G.F ∧ B'.A.act = B.A.act ∧ B.ph1 = B'.ph1 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) ∧ B.ph2 = B'.ph2 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) ∧ B.sy = B'.sy * FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h) ∧ ∀ a : O, B.ad a = B'.ad a * FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ ∀ a : O, B.ad a = FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → (∀ a, B.ad a = 1) → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ (∀ a : O, (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) = 0) ∧ B.sy = FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h)) → CanonGaugeSt := by
  intro hbc hrg s1 s2 s3 s4 R _ d O _ _ _ _ _ k _ _ _ B
  obtain ⟨B0, hF0, hA0, hp10, hp20, hsy0, had0⟩ := hbc R k (algebraMap R k) d O B
  have eF : B.FK k = B0.G.F := funext fun i => (hF0 i).symm
  have eA : ∀ a, B.actK k a = B0.A.act a := fun a => funext fun i => (hA0 a i).symm
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have C1 := cob_three (n := 3) ![pt k d 0, pt k d 2] ![pt k d 1, pt k d 2]
    ![addOf B0.G.F (pt k d 0) (pt k d 1), pt k d 2] (pair_points_zero_constant (hp _) (hp _)) (pair_points_zero_constant (hp _) (hp _))
    (pair_points_zero_constant (gp_addOf _ B0.G.const _ _ (hp _) (hp _)) (hp _))
  have C2 := cob_three (n := 3) ![pt k d 0, pt k d 1] ![pt k d 0, pt k d 2]
    ![pt k d 0, addOf B0.G.F (pt k d 1) (pt k d 2)] (pair_points_zero_constant (hp _) (hp _)) (pair_points_zero_constant (hp _) (hp _))
    (pair_points_zero_constant (hp _) (gp_addOf _ B0.G.const _ _ (hp _) (hp _)))
  have CS := cob_swap ![pt k d 1, pt k d 0] (pair_points_zero_constant (hp _) (hp _))
  have CA := fun a : O => cob_two (n := 2) ![comp1 (B0.A.act a) (pt k d 0), pt k d 1]
    ![pt k d 0, comp1 (B0.A.act (star a)) (pt k d 1)]
    (pair_points_zero_constant (gp_comp1 _ _ (B0.A.const a) (hp _)) (hp _))
    (pair_points_zero_constant (hp _) (gp_comp1 _ _ (B0.A.const (star a)) (hp _)))

  obtain ⟨h1, ax1, t1⟩ := s1 k d O B0
  have c1 := const_of_ax ax1.1
  obtain ⟨B1, F1, A1, p11, p21, sy1, ad1⟩ := hrg k d O B0 h1 ax1
  have q11 : B1.ph1 = 1 := cancel_expS (C1.const _ c1) (t1.symm.trans p11)

  obtain ⟨h2, ax2, z12, t2⟩ := s2 k d O B1 q11
  have c2 := const_of_ax ax2.1
  obtain ⟨B2, F2, A2, p12, p22, sy2, ad2⟩ := hrg k d O B1 h2 ax2
  have q12 : B2.ph1 = 1 := by
    rw [z12, nt_expS_zero, mul_one, q11] at p12; exact p12.symm
  rw [F1] at t2 p12 p22
  rw [A1] at ad2
  have q22 : B2.ph2 = 1 := cancel_expS (C2.const _ c2) (t2.symm.trans p22)

  obtain ⟨h3, ax3, z13, z23, t3⟩ := s3 k d O B2 q12 q22
  have c3 := const_of_ax ax3.1
  obtain ⟨B3, F3, A3, p13, p23, sy3, ad3⟩ := hrg k d O B2 h3 ax3
  have q13 : B3.ph1 = 1 := by
    rw [z13, nt_expS_zero, mul_one, q12] at p13; exact p13.symm
  have q23 : B3.ph2 = 1 := by
    rw [z23, nt_expS_zero, mul_one, q22] at p23; exact p23.symm
  rw [F2, F1] at p13 p23
  rw [A2, A1] at ad3 t3
  have qa3 : ∀ a, B3.ad a = 1 := fun a =>
    cancel_expS ((CA a).const _ c3) ((t3 a).symm.trans (ad3 a))

  obtain ⟨h4, ax4, z14, z24, za4, t4⟩ := s4 k d O B3 q13 q23 qa3
  have c4 := const_of_ax ax4.1
  rw [F3, F2, F1] at z14 z24
  rw [A3, A2, A1] at za4
  have g0 : ∀ j, GP ((![0, pt k d 0] : Fin 2 → Pt k 1 d) j) := pair_points_zero_constant gp_zero₂ (hp _)
  have g1 : ∀ j, GP ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j) := pair_points_zero_constant (hp _) gp_zero₂
  refine ⟨h1 + h2 + h3 + h4, ?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_add _ g0, gt_ev_add _ g0, gt_ev_add _ g0, ax1.1, ax2.1, ax3.1, ax4.1]; simp
  · rw [gt_ev_add _ g1, gt_ev_add _ g1, gt_ev_add _ g1, ax1.2, ax2.2, ax3.2, ax4.2]; simp
  · rw [eF]
    exact hp10.symm.trans (C1.chain c1 c2 c3 c4 p11 p12 p13 (by
      rw [q13, z14, nt_expS_zero]))
  · rw [eF]
    exact hp20.symm.trans (C2.chain c1 c2 c3 c4 p21 p22 p23 (by
      rw [q23, z24, nt_expS_zero]))
  · exact hsy0.symm.trans (CS.chain c1 c2 c3 c4 sy1 sy2 sy3 t4)
  · rw [eA, eA]
    exact (had0 a).symm.trans ((CA a).chain c1 c2 c3 c4 (ad1 a) (ad2 a) (ad3 a) (by
      rw [qa3 a, za4 a, nt_expS_zero]))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeSubIsBiadd
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory

theorem canonGauge_sub_isBiadd : G2.CanonicalGaugeDiffBiadditive := by
  intro R _ d O _ _ k _ _ _ B h h' hh hh'
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hF : ∀ i, constantCoeff (B.FK k i) = 0 := fun i => by
    simp only [FB.FK, FGLaw.mapF, MvPowerSeries.constantCoeff_map, B.G.const i, map_zero]
  have hA : ∀ a, GP (B.actK k a) := fun a i => by
    simp only [FB.actK, MvPowerSeries.constantCoeff_map, B.A.const a i, map_zero]
  have h0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero] at this
  have h0' : constantCoeff h' = 0 := by
    have := congrArg constantCoeff hh'.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero] at this
  have inj : ∀ {n : ℕ} {a b : PS k n d}, constantCoeff a = 0 → constantCoeff b = 0 →
      FB.expS k a = FB.expS k b → a = b := fun ha hb e => exp_inj ha hb e
  refine ⟨?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_sub _ (pair_points_zero_constant hz (hp 0)), hh.ax0, hh'.ax0, sub_zero]
  · rw [gt_ev_sub _ (pair_points_zero_constant (hp 0) hz), hh.ax1, hh'.ax1, sub_zero]
  · have a1 := pair_points_zero_constant (hp (n := 3) 0) (hp 2)
    have a2 := pair_points_zero_constant (hp (n := 3) 1) (hp 2)
    have a3 := pair_points_zero_constant (gp_addOf _ hF _ _ (hp (n := 3) 0) (hp 1)) (hp 2)
    have e := inj
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp)
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp)
      (hh.ph1.symm.trans hh'.ph1)
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]
    linear_combination -e
  · have a1 := pair_points_zero_constant (hp (n := 3) 0) (hp 1)
    have a2 := pair_points_zero_constant (hp (n := 3) 0) (hp 2)
    have a3 := pair_points_zero_constant (hp (n := 3) 0) (gp_addOf _ hF _ _ (hp (n := 3) 1) (hp 2))
    have e := inj
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp)
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp)
      (hh.ph2.symm.trans hh'.ph2)
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]
    linear_combination -e
  · have a1 := pair_points_zero_constant (gp_comp1 _ _ (hA a) (hp (n := 2) 0)) (hp 1)
    have a2 := pair_points_zero_constant (hp (n := 2) 0) (gp_comp1 _ _ (hA (star a)) (hp (n := 2) 1))
    have e := inj
      (by rw [map_sub, gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, sub_zero])
      (by rw [map_sub, gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', sub_zero])
      ((hh.ad a).symm.trans (hh'.ad a))
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2]
    linear_combination -e

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.DerivationInnerOfSeparabilityElement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem derivation_inner_of_separability_element (O : Type) [CommRing O] (N : ℕ)
    (e : TensorProduct ℤ O O) (hN : 0 < N) (he : Algebra.TensorProduct.lmul' ℤ e = (N : O))
    (hc : ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0)
    (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V)
    (hlr : ∀ a b, Commute (l a) (r b)) (δ : O →+ V)
    (hδ : ∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) :
    ∃ v : V, ∀ a, δ a = l a v - r a v := by
  let Φ : TensorProduct ℤ O O →ₗ[ℤ] V := TensorProduct.lift
    (LinearMap.mk₂ ℤ (fun a b => l a (δ b))
      (fun a a' b => by simp) (fun n a b => by simp)
      (fun a b b' => by simp) (fun n a b => by rw [map_zsmul, map_zsmul]))
  have hΦ : ∀ a b, Φ (TensorProduct.tmul ℤ a b) = l a (δ b) := fun a b => TensorProduct.lift.tmul a b
  have h1 : ∀ (c : O) (t : TensorProduct ℤ O O),
      Φ (TensorProduct.tmul ℤ c (1 : O) * t) = l c (Φ t) := by
    intro c t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, hΦ]
    | add x y hx hy => simp [mul_add, hx, hy]
  have h2 : ∀ (c : O) (t : TensorProduct ℤ O O),
      Φ (TensorProduct.tmul ℤ (1 : O) c * t)
        = l (Algebra.TensorProduct.lmul' ℤ t) (δ c) + r c (Φ t) := by
    intro c t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have h := LinearMap.congr_fun (hlr a c).eq (δ b)
      simp only [Module.End.mul_apply] at h
      simp [Algebra.TensorProduct.tmul_mul_tmul, hΦ, hδ, h]
    | add x y hx hy =>
      simp only [mul_add, map_add (f := _), hx, hy, LinearMap.add_apply]
      abel
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨(N : ℚ)⁻¹ • Φ e, fun c => ?_⟩
  have h := congrArg Φ (hc c)
  rw [sub_mul, map_sub, h1, h2, he, map_zero, map_natCast, Module.End.natCast_apply] at h
  have h' : l c (Φ e) - r c (Φ e) = (N : ℚ) • δ c := by
    rw [Nat.cast_smul_eq_nsmul]
    rw [sub_eq_zero] at h
    rw [h]; abel
  rw [map_smul, map_smul, ← smul_sub, h', smul_smul, inv_mul_cancel₀ hN', one_smul]

theorem derivation_inner_of_reduced_order :
    (∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O], ∃ (N : ℕ) (e : TensorProduct ℤ O O), 0 < N ∧ Algebra.TensorProduct.lmul' ℤ e = (N : O) ∧ ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0) → ∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V), (∀ a b, Commute (l a) (r b)) → ∀ δ : O →+ V, (∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) → ∃ v : V, ∀ a, δ a = l a v - r a v := by
  intro H O _ _ _ _ V _ _ l r hlr δ hδ
  obtain ⟨N, e, hN, he, hc⟩ := H O
  exact derivation_inner_of_separability_element O N e hN he hc V l r hlr δ hδ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermExpAddAndEvConst
section
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem germ_expS_add : G2.ExpAddZeroConstant :=
  fun _ _ _ _ _ f g hf hg => WickVanishing.gt_expS_add f g hf hg

theorem germ_constantCoeff_ev : G2.ConstantCoeffSubstitution :=
  fun _ _ _ _ _ a f ha => WickVanishing.gt_const_ev_eq a ha f

theorem germ_expAdd_and_evConst : G2.ExpAddZeroConstant ∧ G2.ConstantCoeffSubstitution :=
  ⟨germ_expS_add, germ_constantCoeff_ev⟩

end GlobalTheory
end

