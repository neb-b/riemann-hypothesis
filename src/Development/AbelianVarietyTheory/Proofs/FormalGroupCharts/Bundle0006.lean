module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalLogEqSumOfMultiplicativeParam

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.EqZeroOfAdditiveOfPderiv
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.AdditiveSeries

variable {k : Type} [CommRing k] {d : ℕ}

theorem gp_cons {m n : ℕ} {x : Pt k n d} {y : Fin m → Pt k n d} (hx : GP x) (hy : ∀ j, GP (y j)) :
    ∀ j, GP ((Fin.cons x y : Fin (m + 1) → Pt k n d) j) :=
  Fin.cases (by simpa using hx) (by simpa using hy)

theorem gp_pair {n : ℕ} {x y : Pt k n d} (hx : GP x) (hy : GP y) :
    ∀ j, GP ((![x, y] : Fin 2 → Pt k n d) j) := by
  intro j; fin_cases j; exacts [hx, hy]

theorem gp_single {n : ℕ} {x : Pt k n d} (hx : GP x) :
    ∀ j, GP ((![x] : Fin 1 → Pt k n d) j) := by
  intro j; fin_cases j; exact hx

theorem ev_pt {n : ℕ} (f : PS k n d) : ev (fun j => pt k d j) f = f :=
  congrFun subst_self f

theorem pderiv_ev_cons {m n : ℕ} {x : Pt k n d} {y : Fin m → Pt k n d} (hx : GP x)
    (hy : ∀ j, GP (y j)) (v : Fin n × Fin d) (hv : ∀ j i, pderiv (R := k) v (y j i) = 0)
    (g : PS k (m + 1) d) :
    pderiv (R := k) v (ev (Fin.cons x y) g) =
      ∑ l, ev (Fin.cons x y) (pderiv (R := k) ((0 : Fin (m + 1)), l) g) * pderiv (R := k) v (x l) := by
  unfold ev
  rw [FormalCalc.pderiv_subst'
    (fun p : Fin (m + 1) × Fin d => gp_cons hx hy p.1 p.2), Fintype.sum_prod_type,
    Fin.sum_univ_succ]
  simp [hv]

theorem ev_ev_cons {l m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, GP (V j)) {x : Pt k m d}
    {y : Fin l → Pt k m d} (hx : GP x) (hy : ∀ j, GP (y j)) (g : PS k (l + 1) d) :
    ev V (ev (Fin.cons x y) g) =
      ev (Fin.cons (fun i => ev V (x i)) fun j i => ev V (y j i)) g := by
  rw [gt_ev_ev V _ hV (gp_cons hx hy)]
  congr 1
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem ev_pt_apply {m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, GP (V j)) (j : Fin m)
    (i : Fin d) : ev V (pt k d j i) = V j i := gt_ev_X V hV j i

theorem ev_addOf {m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, GP (V j)) (F : Fin d → PS k 2 d)
    (a b : Fin m) (i : Fin d) :
    ev V (addOf F (pt k d a) (pt k d b) i) = addOf F (V a) (V b) i := by
  unfold addOf
  rw [gt_ev_ev V _ hV (gp_pair (gp_pt a) (gp_pt b))]
  congr 1
  funext j i
  fin_cases j <;> simp [ev_pt_apply hV]

theorem zero_addOf {n : ℕ} (G : FGLaw k d) {x : Pt k n d} (hx : GP x) : addOf G.F 0 x = x := by
  funext i
  have h := congrArg (ev ![x]) (G.unit i)
  rw [gt_ev_ev _ _ (gp_single hx) (gp_pair gp_zero₂ (gp_pt 0)),
    gt_ev_X _ (gp_single hx)] at h
  refine Eq.trans ?_ h
  unfold addOf
  congr 1
  funext j i
  fin_cases j <;> simp [ev_pt_apply (gp_single hx), gt_ev_zero _ (gp_single hx)]

theorem addOf_zero {n : ℕ} (G : FGLaw k d) {x : Pt k n d} (hx : GP x) : addOf G.F x 0 = x := by
  funext i
  have hz : GP (0 : Pt k n d) := gp_zero₂
  have h := congrArg (ev ![x, 0]) (G.comm i)
  rw [gt_ev_ev _ _ (gp_pair hx hz) (gp_pair (gp_pt 1) (gp_pt 0))] at h
  refine Eq.trans h.symm (Eq.trans ?_ (congrFun (zero_addOf G hx) i))
  unfold addOf
  congr 1
  funext j i
  fin_cases j <;> simp [ev_pt_apply (gp_pair hx hz)]

theorem pderiv_pt {n : ℕ} (a b : Fin n) (i l : Fin d) :
    pderiv (R := k) (a, i) (pt k d b l) = if b = a ∧ l = i then 1 else 0 := by
  simp [pt, FormalCalc.pderiv_X_ite]

theorem constantCoeff_pderiv_addOf {q : ℕ} (G : FGLaw k d) (i l : Fin d) :
    constantCoeff (pderiv (R := k) ((0 : Fin (q + 2)), i)
      (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1) l)) = if l = i then 1 else 0 := by
  have hx : GP (pt k d (0 : Fin 1)) := gp_pt 0
  have hy : ∀ j, GP ((fun _ => 0 : Fin (q + 1) → Pt k 1 d) j) := fun _ => gp_zero₂
  have h := pderiv_ev_cons hx hy ((0 : Fin 1), i) (by simp)
    (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1) l)
  rw [ev_addOf (gp_cons hx hy)] at h
  have e1 : (Fin.cons (pt k d (0 : Fin 1)) (fun _ => 0) : Fin (q + 2) → Pt k 1 d) 1 = 0 := rfl
  rw [e1, Fin.cons_zero, addOf_zero G hx] at h
  simp only [pderiv_pt, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  rw [← gt_const_ev_eq _ (gp_cons hx hy), ← h]
  split_ifs <;> simp

theorem eq_zero_of_additive_of_pderiv (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ)
    (G : FGLaw k d) (q : ℕ) (g : PS k (q + 1) d)
    (hadd : ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1))
        (fun j : Fin q => pt k d j.succ.succ)) g =
      ev (n := q + 2) (Fin.cons (pt k d 0) (fun j : Fin q => pt k d j.succ.succ)) g +
      ev (n := q + 2) (Fin.cons (pt k d 1) (fun j : Fin q => pt k d j.succ.succ)) g)
    (hlin : ∀ i, ev (n := q) (Fin.cons 0 (fun j : Fin q => pt k d j))
      (pderiv (R := k) ((0 : Fin (q + 1)), i) g) = 0) : g = 0 := by
  have : HasUniqueDiv k := HasUniqueDiv.of_module_rat k
  have hS : GP (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1)) :=
    gp_addOf _ G.const _ _ (gp_pt _) (gp_pt _)
  have hw : ∀ j : Fin q, GP (pt k d j.succ.succ) := fun _ => gp_pt _
  set V : Fin (q + 2) → Pt k (q + 1) d := Fin.cons 0 fun j => pt k d j with hVdef
  have hV : ∀ j, GP (V j) := gp_cons gp_zero₂ fun _ => gp_pt _
  have hV0 : V 0 = 0 := rfl
  have hV1 : V 1 = pt k d 0 := rfl
  have hVs : ∀ j : Fin q, V j.succ.succ = pt k d j.succ := fun _ => rfl
  have hid : (Fin.cons (pt k d 0) fun j : Fin q => pt k d j.succ :
      Fin (q + 1) → Pt k (q + 1) d) = fun j => pt k d j := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp

  have eS (f : PS k (q + 1) d) : ev V (ev (n := q + 2) (Fin.cons (addOf G.F (pt k d 0) (pt k d 1))
      (fun j : Fin q => pt k d j.succ.succ)) f) = f := by
    rw [ev_ev_cons hV hS hw]
    simp only [ev_addOf hV, ev_pt_apply hV, hV0, hV1, hVs, zero_addOf G (gp_pt _)]
    exact (congrArg (ev · f) hid).trans (ev_pt f)
  have e0 (f : PS k (q + 1) d) : ev V (ev (n := q + 2) (Fin.cons (pt k d 0)
      (fun j : Fin q => pt k d j.succ.succ)) f) =
      ev (Fin.cons 0 fun j : Fin q => pt k d j.succ) f := by
    rw [ev_ev_cons hV (gp_pt _) hw]
    simp only [ev_pt_apply hV, hV0, hVs]
  have e1 (f : PS k (q + 1) d) : ev V (ev (n := q + 2) (Fin.cons (pt k d 1)
      (fun j : Fin q => pt k d j.succ.succ)) f) = f := by
    rw [ev_ev_cons hV (gp_pt _) hw]
    simp only [ev_pt_apply hV, hV1, hVs]
    exact (congrArg (ev · f) hid).trans (ev_pt f)
  have hlin' (i : Fin d) : ev (Fin.cons 0 fun j : Fin q => pt k d j.succ)
      (pderiv (R := k) ((0 : Fin (q + 1)), i) g) = 0 := by
    have hU : ∀ j : Fin q, GP (pt k d j.succ) := fun _ => gp_pt _
    have h := congrArg (ev fun j : Fin q => pt k d j.succ) (hlin i)
    rw [ev_ev_cons hU gp_zero₂ (fun _ => gp_pt _), gt_ev_zero _ hU] at h
    simp only [ev_pt_apply hU, Pi.zero_apply, gt_ev_zero _ hU] at h
    exact h
  have hax : ev (Fin.cons 0 fun j : Fin q => pt k d j.succ) g = 0 := by
    have h := congrArg (ev V) hadd
    rw [gt_ev_add V hV, eS, e0, e1] at h
    simpa using h
  let J : Matrix (Fin d) (Fin d) (PS k (q + 1) d) := Matrix.of fun l i =>
    ev V (pderiv (R := k) ((0 : Fin (q + 2)), i) (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1) l))
  have hJ : IsUnit J := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_constantCoeff, RingHom.map_det]
    have : (constantCoeff : PS k (q + 1) d →+* k).mapMatrix J = 1 := by
      ext l i
      simp [J, gt_const_ev_eq V hV, constantCoeff_pderiv_addOf, Matrix.one_apply]
    rw [this, Matrix.det_one]
    exact isUnit_one
  have hD : Matrix.vecMul (fun l => pderiv (R := k) ((0 : Fin (q + 1)), l) g) J = 0 := by
    funext i
    have hv : ∀ (j : Fin q) (l : Fin d),
        pderiv (R := k) ((0 : Fin (q + 2)), i) (pt k d j.succ.succ l) = 0 := by
      intro j l
      rw [pderiv_pt, ite_eq_right fun h => Fin.succ_ne_zero _ h.1]
    have h := congrArg (pderiv (R := k) ((0 : Fin (q + 2)), i)) hadd
    rw [map_add (f := _), pderiv_ev_cons hS hw _ hv, pderiv_ev_cons (gp_pt _) hw _ hv,
      pderiv_ev_cons (gp_pt _) hw _ hv] at h
    simp only [pderiv_pt, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, one_ne_zero, false_and, ite_false, Finset.sum_const_zero,
      add_zero] at h
    have h2 := congrArg (ev V) h
    rw [e0, hlin'] at h2
    have hs : ∀ f : Fin d → PS k (q + 2) d, ev V (∑ l, f l) = ∑ l, ev V (f l) := fun f => by
      unfold ev
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← coe_substAlgHom (gt_hasSubst V hV), map_sum]
    simp only [hs, gt_ev_mul V hV, eS] at h2
    exact h2
  have hD0 : (fun l => pderiv (R := k) ((0 : Fin (q + 1)), l) g) = 0 := by
    obtain ⟨u, hu⟩ := hJ.exists_right_inv
    have h := congrArg (fun v => Matrix.vecMul v u) hD
    simpa [Matrix.vecMul_vecMul, hu] using h
  refine FormalCalc.ext_of_pderiv_of_subst (fun i : Fin d => ((0 : Fin (q + 1)), i))
    (b := fun p : Fin (q + 1) × Fin d =>
      (Fin.cons 0 fun j : Fin q => pt k d j.succ : Fin (q + 1) → Pt k (q + 1) d) p.1 p.2)
    (fun _ => rfl) ?_ (fun i => ?_) ?_
  · rintro ⟨j, i⟩ hj
    revert hj
    refine Fin.cases (fun hj => ?_) (fun j _ => rfl) j
    exact absurd ⟨i, rfl⟩ hj
  · simpa using congrFun hD0 i
  · exact hax.trans (gt_ev_zero _ (gp_cons gp_zero₂ fun _ => gp_pt _)).symm

end GlobalTheory.AdditiveSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FBMap

variable {R k : Type} [CommRing R] [CommRing k] (f : R →+* k) {d : ℕ}

def NoConst {n : ℕ} (a : Pt R n d) : Prop := ∀ i, constantCoeff (a i) = 0

def mapPt {n : ℕ} (a : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map f (a i)

theorem hasSubst_of {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, NoConst (a j)) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2

theorem map_ev {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, NoConst (a j)) (g : PS R m d) :
    MvPowerSeries.map f (ev a g) = ev (fun j => mapPt f (a j)) (MvPowerSeries.map f g) := by
  unfold ev mapPt
  rw [MvPowerSeries.map_subst (hasSubst_of ha)]

theorem cc_ev {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, NoConst (a j)) {g : PS R m d}
    (hg : constantCoeff g = 0) : constantCoeff (ev a g) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of ha) (fun p => ha p.1 p.2) hg

theorem map_ev1 {n : ℕ} {a : Pt R n d} (ha : NoConst a) (g : PS R 1 d) :
    MvPowerSeries.map f (ev ![a] g) = ev ![mapPt f a] (MvPowerSeries.map f g) := by
  rw [map_ev f (fun j => by fin_cases j; exact ha)]
  congr 1
  funext j
  fin_cases j; rfl

theorem map_ev2 {n : ℕ} {a b : Pt R n d} (ha : NoConst a) (hb : NoConst b) (g : PS R 2 d) :
    MvPowerSeries.map f (ev ![a, b] g) = ev ![mapPt f a, mapPt f b] (MvPowerSeries.map f g) := by
  rw [map_ev f (fun j => by fin_cases j; exacts [ha, hb])]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem map_ev3 {n : ℕ} {a b c : Pt R n d} (ha : NoConst a) (hb : NoConst b) (hc : NoConst c)
    (g : PS R 3 d) :
    MvPowerSeries.map f (ev ![a, b, c] g) =
      ev ![mapPt f a, mapPt f b, mapPt f c] (MvPowerSeries.map f g) := by
  rw [map_ev f (fun j => by fin_cases j; exacts [ha, hb, hc])]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem nc_zero {n : ℕ} : NoConst (0 : Pt R n d) := fun _ => by simp

theorem nc_pt {n : ℕ} (j : Fin n) : NoConst (pt R d j) := fun _ => by simp [pt]

theorem nc_comp1 {n : ℕ} {φ : Pt R 1 d} {a : Pt R n d} (hφ : NoConst φ) (ha : NoConst a) :
    NoConst (comp1 φ a) := fun i =>
  cc_ev (fun j => by fin_cases j; exact ha) (hφ i)

theorem nc_addOf {n : ℕ} {F : Pt R 2 d} {a b : Pt R n d} (hF : NoConst F) (ha : NoConst a)
    (hb : NoConst b) : NoConst (addOf F a b) := fun i =>
  cc_ev (fun j => by fin_cases j; exacts [ha, hb]) (hF i)

theorem mapPt_zero {n : ℕ} : mapPt f (0 : Pt R n d) = 0 := by
  funext i; simp [mapPt]

theorem mapPt_pt {n : ℕ} (j : Fin n) : mapPt f (pt R d j) = pt k d j := by
  funext i; simp [mapPt, pt]

theorem mapPt_comp1 {n : ℕ} (φ : Pt R 1 d) {a : Pt R n d} (ha : NoConst a) :
    mapPt f (comp1 φ a) = comp1 (mapPt f φ) (mapPt f a) := by
  funext i; exact map_ev1 f ha (φ i)

theorem mapPt_addOf {n : ℕ} (F : Pt R 2 d) {a b : Pt R n d} (ha : NoConst a) (hb : NoConst b) :
    mapPt f (addOf F a b) = addOf (mapPt f F) (mapPt f a) (mapPt f b) := by
  funext i; exact map_ev2 f ha hb (F i)

theorem nc_law (G : FGLaw R d) : NoConst G.F := G.const

theorem nc_act {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) (a : O) :
    NoConst (A.act a) := A.const a

local macro "map_formal_series" h:ident : tactic =>
  `(tactic|
    simp (disch := solve | apply_rules [nc_zero, nc_pt, nc_comp1, nc_addOf, nc_law, nc_act])
      only [FGLaw.add, map_ev1, map_ev2, map_ev3, mapPt_zero, mapPt_pt, mapPt_comp1,
        mapPt_addOf, map_X, map_one, map_mul] at $h:ident)

def mapLaw (G : FGLaw R d) : FGLaw k d where
  F := mapPt f G.F
  const i := by simp [mapPt, G.const i]
  unit i := by
    have h := congrArg (MvPowerSeries.map f) (G.unit i)
    map_formal_series h
    exact h
  comm i := by
    have h := congrArg (MvPowerSeries.map f) (G.comm i)
    map_formal_series h
    exact h
  assoc i := by
    have h0 : ev (n := 3) ![addOf G.F (pt R d 0) (pt R d 1), pt R d 2] (G.F i) =
        ev (n := 3) ![pt R d 0, addOf G.F (pt R d 1) (pt R d 2)] (G.F i) := G.assoc i
    have h := congrArg (MvPowerSeries.map f) h0
    map_formal_series h
    exact h

def mapAct {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : OAct O (mapLaw f G) where
  act a := mapPt f (A.act a)
  const a i := by simp [mapPt, A.const a i]
  hom a := by
    have h := congrArg (mapPt f) (A.hom a)
    map_formal_series h
    exact h
  add_act a b := by
    have h := congrArg (mapPt f) (A.add_act a b)
    map_formal_series h
    exact h
  mul_act a b := by
    have h := congrArg (mapPt f) (A.mul_act a b)
    map_formal_series h
    exact h
  one_act := by
    have h := congrArg (mapPt f) A.one_act
    map_formal_series h
    exact h

def mapFB {O : Type} [CommRing O] [StarRing O] (B : FB R d O) : FB k d O where
  G := mapLaw f B.G
  A := mapAct f B.A
  ph1 := MvPowerSeries.map f B.ph1
  ph2 := MvPowerSeries.map f B.ph2
  sy := MvPowerSeries.map f B.sy
  ad a := MvPowerSeries.map f (B.ad a)
  cocycleLeft_zero_fst := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleLeft_zero_fst)
    map_formal_series h
    exact h
  cocycleLeft_zero_snd := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleLeft_zero_snd)
    map_formal_series h
    exact h
  cocycleLeft_zero_thd := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleLeft_zero_thd)
    map_formal_series h
    exact h
  cocycleRight_zero_fst := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleRight_zero_fst)
    map_formal_series h
    exact h
  cocycleRight_zero_snd := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleRight_zero_snd)
    map_formal_series h
    exact h
  cocycleRight_zero_thd := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleRight_zero_thd)
    map_formal_series h
    exact h
  symmetry_zero_fst := by
    have h := congrArg (MvPowerSeries.map f) (B.symmetry_zero_fst)
    map_formal_series h
    exact h
  symmetry_zero_snd := by
    have h := congrArg (MvPowerSeries.map f) (B.symmetry_zero_snd)
    map_formal_series h
    exact h
  adjoint_zero_fst a := by
    have h := congrArg (MvPowerSeries.map f) (B.adjoint_zero_fst a)
    map_formal_series h
    exact h
  adjoint_zero_snd a := by
    have h := congrArg (MvPowerSeries.map f) (B.adjoint_zero_snd a)
    map_formal_series h
    exact h
  cocycleLeft_assoc := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleLeft_assoc)
    map_formal_series h
    exact h
  cocycleLeft_comm := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleLeft_comm)
    map_formal_series h
    exact h
  cocycleRight_assoc := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleRight_assoc)
    map_formal_series h
    exact h
  cocycleRight_comm := by
    have h := congrArg (MvPowerSeries.map f) (B.cocycleRight_comm)
    map_formal_series h
    exact h
  interchange := by
    have h := congrArg (MvPowerSeries.map f) (B.interchange)
    map_formal_series h
    exact h
  sy_inv := by
    have h := congrArg (MvPowerSeries.map f) (B.sy_inv)
    map_formal_series h
    exact h
  sy_law := by
    have h := congrArg (MvPowerSeries.map f) (B.sy_law)
    map_formal_series h
    exact h
  adjoint_compat_left a := by
    have h := congrArg (MvPowerSeries.map f) (B.adjoint_compat_left a)
    map_formal_series h
    exact h
  adjoint_compat_right a := by
    have h := congrArg (MvPowerSeries.map f) (B.adjoint_compat_right a)
    map_formal_series h
    exact h
  ad_one := by
    have h := congrArg (MvPowerSeries.map f) (B.ad_one)
    map_formal_series h
    exact h
  ad_mul a b := by
    have h := congrArg (MvPowerSeries.map f) (B.ad_mul a b)
    map_formal_series h
    exact h
  ad_add a b := by
    have h := congrArg (MvPowerSeries.map f) (B.ad_add a b)
    map_formal_series h
    exact h
  ad_sy a := by
    have h := congrArg (MvPowerSeries.map f) (B.ad_sy a)
    map_formal_series h
    exact h

end GlobalTheory.FBMap

namespace GlobalTheory

theorem exists_formalBiext_map :
    ∀ (R k : Type) [CommRing R] [CommRing k] (f : R →+* k) (d : ℕ) (O : Type) [CommRing O]
      [StarRing O] (B : FB R d O), ∃ B' : FB k d O,
      (∀ i, B'.G.F i = MvPowerSeries.map f (B.G.F i)) ∧
      (∀ a i, B'.A.act a i = MvPowerSeries.map f (B.A.act a i)) ∧
      B'.ph1 = MvPowerSeries.map f B.ph1 ∧ B'.ph2 = MvPowerSeries.map f B.ph2 ∧
      B'.sy = MvPowerSeries.map f B.sy ∧ ∀ a, B'.ad a = MvPowerSeries.map f (B.ad a) :=
  fun _ _ _ _ f _ _ _ _ B =>
    ⟨FBMap.mapFB f B, fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.WickVanishOfHalf
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem wickVanish_of_half : GE.HalfSt → G2.WickOperatorVanishing := by
  intro hH k _ _ d F ι _ u c P q hc hq0 hq1 hq2 hP m G
  obtain ⟨Y, hY⟩ := GE.exp_cut m q hq0 0
  have hY' : FB.expS k (m • q) = 1 + q * Y := by
    rw [hY]
    simp
  rw [hY', mul_add, mul_one, GE.dpolyOf_add_f, map_add (f := _),
    show G * (q * Y) = (G * Y) * q by ring, hH k d F ι u c q hc hq0 hq1 hq2 P (G * Y), hP,
    GE.dpolyOf_zero_P, map_zero, mul_zero, add_zero]

end GlobalTheory
end
end

