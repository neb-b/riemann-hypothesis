module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexTotalRepresentsVanishingCoch
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem map_res' {E E' : Spc} (j : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (z : Sx E p U) :
    (z.map j).res g = (z.res g).map j := by
  exact (ConcreteCategory.congr_hom ((j.app _).naturality g.op) z).symm

private theorem map_face' {E E' : Spc} (j : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (z : Sx E (p + 1) U) (i : Fin (p + 2)) :
    (z.map j).face i = (z.face i).map j :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (j.naturality (SimplexCategory.δ i).op) (op U)) z).symm

private theorem ev_delta_zero {R : Type} [CommRing R] {E : Spc} {I : Cx R} {N M s t : ℤ} (hm : N + 1 = M)
    (α : Cochain ((chains R).obj E) I N) (U : Scheme.{0}) (x : Sx E 0 U)
    (ht : -((0 : ℕ) : ℤ) + M = t) (hs : -((0 : ℕ) : ℤ) + N = s) :
    ev (R := R) (δ N M α) 0 t ht U x = Sec.map (I.d s t) (ev (R := R) α 0 s hs U x) := by
  obtain rfl : t = M := by omega
  obtain rfl : s = N := by omega
  exact (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R hm α U).1 x

private theorem fam_smul_apply {R : Type} [CommRing R] {E : Spc} {Z : Sub E} {p : ℕ} {M : Shv R} (u : ℤˣ) (a : Fam Z p M)
    (U : Scheme.{0}) (z : Sx E p U) : (u • a).1 U z = u • a.1 U z := by
  rfl

theorem UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain :
    ∀ (R : Type) [CommRing R] {E E' : Spc} (j : E ⟶ E') (Z : Sub E) (K : Cx R) (m n N : ℤ), n + m = N →
    (∀ γ : Cochain ((chains R).obj E') K N, (∀ (p : ℕ) (s : ℤ) h (U : Scheme.{0}) (z : Sx E p U), Z.mem p U z → ev (R := R) γ p s h U (z.map j) = 0) → ∃ x : (famDC Z K m).Tot, (famDC Z K m).Deg n x ∧ Comp j γ x) ∧
    (∀ (γ : Cochain ((chains R).obj E') K N) (x x' : (famDC Z K m).Tot), (famDC Z K m).Deg n x → (famDC Z K m).Deg n x' → Comp j γ x → Comp j γ x' → x = x') ∧
    (∀ (γ : Cochain ((chains R).obj E') K N) (x : (famDC Z K m).Tot), Comp j γ x → Comp j (δ N (N + 1) γ) ((famDC Z K m).D n x)) ∧
    (∀ (γ γ' : Cochain ((chains R).obj E') K N) (x x' : (famDC Z K m).Tot), Comp j γ x → Comp j γ' x' → Comp j (γ - γ') (x - x')) ∧
    ∀ x : (famDC Z K m).Tot, (famDC Z K m).Deg n x → (famDC Z K m).Deg (n + 1) ((famDC Z K m).D n x) := by
  intro R _ E E' j Z K m n N hN
  have ev_nat := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E') (I := K) (n := N)).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    let x : (famDC Z K m).Tot := fun p s =>
      if h : -(p : ℤ) + N = s + m then
        (⟨fun U z => ev (R := R) γ p (s + m) h U (z.map j),
          ⟨fun V U g z => (ev_nat γ p (s + m) h V U g (z.map j)).trans (by rw [map_res']),
           fun U z hz => hγ p (s + m) h U z hz⟩⟩ : Fam Z p (K.X (s + m)))
      else 0
    refine ⟨x, fun p s hps => ?_, fun p s h U z => ?_⟩
    · have h : ¬ (-(p : ℤ) + N = s + m) := by omega
      exact dif_neg h
    · exact congrArg (fun a : Fam Z p (K.X (s + m)) =>
        (a : (U : Scheme.{0}) → Sx E p U → Sec (K.X (s + m)) U) U z) (dif_pos h)
  · intro γ x x' hx hx' cx cx'
    funext p s
    by_cases hps : (p : ℤ) + s = n
    · have h : -(p : ℤ) + N = s + m := by omega
      change (x p s : Fam Z p (K.X (s + m))) = x' p s
      apply Subtype.ext
      funext U z
      exact (cx p s h U z).trans (cx' p s h U z).symm
    · rw [hx p s hps, hx' p s hps]
  · intro γ x cx p s h U z
    rcases p with _ | p
    · have h0 : -((0 : ℕ) : ℤ) + N = (s - 1) + m := by omega
      rw [ev_delta_zero (s := s - 1 + m) rfl γ U (z.map j) h h0, ← cx 0 (s - 1) h0 U z]
      rfl
    · have hs : -((p + 1 : ℕ) : ℤ) + N = (s - 1) + m := by omega
      have hp : -(p : ℤ) + N = s + m := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R (rfl : N + 1 = N + 1) γ U).2 p (s - 1 + m) (s + m) hs h (z.map j),
        ← cx (p + 1) (s - 1) hs U z]
      simp only [map_face']
      rw [Finset.sum_congr rfl (fun i _ => by rw [← cx p s hp U (z.face i)])]
      have eN : (N + 1).negOnePow = (n + 1).negOnePow * m.negOnePow := by
        rw [← Int.negOnePow_add]; congr 1; omega
      have e2 := fam_smul_apply (n + 1).negOnePow
        (Fam.δ Z p (K.X (s + m)) m.negOnePow (x p s : Fam Z p (K.X (s + m)))) U z
      rw [eN, mul_smul]
      show Sec.map (K.d (s - 1 + m) (s + m)) ((x (p + 1) (s - 1) : Fam Z (p + 1) (K.X (s - 1 + m))).1 U z) +
        ((n + 1).negOnePow • Fam.δ Z p (K.X (s + m)) m.negOnePow (x p s : Fam Z p (K.X (s + m)))).1 U z = _
      rw [e2]
      rfl
  · intro γ γ' x x' cx cx' p s h U z
    rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E') (I := K) (n := N)).1 γ γ' p (s + m) h U (z.map j)).2.1,
      ← cx p s h U z, ← cx' p s h U z]
    rfl
  · intro x hx p s hps
    rcases p with _ | p
    · have h1 : ((0 : ℕ) : ℤ) + (s - 1) ≠ n := by omega
      show (Fam.map Z 0 (K.d (s - 1 + m) (s + m))) (x 0 (s - 1)) = 0
      rw [hx 0 (s - 1) h1]
      exact map_zero _
    · have h1 : ((p + 1 : ℕ) : ℤ) + (s - 1) ≠ n := by omega
      have h2 : (p : ℤ) + s ≠ n := by omega
      show (Fam.map Z (p + 1) (K.d (s - 1 + m) (s + m))) (x (p + 1) (s - 1)) +
        (n + 1).negOnePow • (Fam.δ Z p (K.X (s + m)) m.negOnePow) (x p s) = 0
      rw [hx _ _ h1, hx _ _ h2]
      show (Fam.map Z (p + 1) (K.d (s - 1 + m) (s + m))) (0 : Fam Z (p + 1) (K.X (s - 1 + m))) +
        (n + 1).negOnePow • (Fam.δ Z p (K.X (s + m)) m.negOnePow) (0 : Fam Z p (K.X (s + m))) = 0
      rw [map_zero, map_zero, smul_zero, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TotalExactOfColumnExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem map_us {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (e : ℤˣ) (x : G) :
    f (e • x) = e • f x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

private theorem D_zero (C : DC) (n : ℤ) (x : C.Tot) (s t : ℤ) (h : s + 1 = t) :
    C.D n x 0 t = C.d 0 s t (x 0 s) := by
  obtain rfl : s = t - 1 := by omega
  rfl

private theorem D_succ (C : DC) (n : ℤ) (x : C.Tot) (p : ℕ) (s t : ℤ) (h : s + 1 = t) :
    C.D n x (p + 1) t = C.d (p + 1) s t (x (p + 1) s) + (n + 1).negOnePow • C.δ p t (x p t) := by
  obtain rfl : s = t - 1 := by omega
  rfl

private theorem col {C C' : DC} {Φ : C.Hom C'} {p : ℕ} (h : Φ.ColEx p) (r s t u : ℤ) (e1 : r + 1 = s)
    (e2 : s + 1 = t) (e3 : t + 1 = u) (a : C.A p t) (y : C'.A p s) (ha : C.d p t u a = 0)
    (hy : Φ p t a = C'.d p s t y) :
    ∃ (a' : C.A p s) (y' : C'.A p r), C.d p s t a' = a ∧ y = Φ p s a' + C'.d p r s y' := by
  subst e2
  subst e3
  obtain rfl : r = s - 1 := by omega
  exact h s a y ha hy

private structure Cl {C C' : DC} (Φ : C.Hom C') (n : ℤ) (p : ℕ) (b : ∀ s, C.A p s) (z : ∀ s, C'.A p s) : Prop where
  sb : ∀ s, (p : ℤ) + s ≠ n + 1 → b s = 0
  sz : ∀ s, (p : ℤ) + s ≠ n → z s = 0
  db : ∀ s t, s + 1 = t → C.d p s t (b s) = 0
  pz : ∀ s t, s + 1 = t → Φ p t (b t) = C'.d p s t (z s)

private structure Sv {C C' : DC} (Φ : C.Hom C') (n : ℤ) (p : ℕ) (b : ∀ s, C.A p s) (z : ∀ s, C'.A p s)
    (u : ∀ s, C.A p s) (v : ∀ s, C'.A p s) : Prop where
  su : ∀ s, (p : ℤ) + s ≠ n → u s = 0
  sv : ∀ s, (p : ℤ) + s ≠ n - 1 → v s = 0
  du : ∀ s t, s + 1 = t → C.d p s t (u s) = b t
  yv : ∀ r s, r + 1 = s → z s = Φ p s (u s) + C'.d p r s (v r)

private theorem solve {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {p : ℕ} (hcol : Φ.ColEx p)
    {b : ∀ s, C.A p s} {z : ∀ s, C'.A p s} (h : Cl Φ n p b z) : ∃ u v, Sv Φ n p b z u v := by
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℤ, s0 = n - p := ⟨_, rfl⟩
  obtain ⟨a', y', ha', hy'⟩ := col hcol (s0 - 1) s0 (s0 + 1) (s0 + 1 + 1) (by ring) rfl rfl
    (b (s0 + 1)) (z s0) (h.db _ _ rfl) (h.pz _ _ rfl)
  refine ⟨Function.update (fun _ => 0) s0 a', Function.update (fun _ => 0) (s0 - 1) y',
    ⟨?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    rw [Function.update_of_ne (by omega)]
  · intro s hs
    rw [Function.update_of_ne (by omega)]
  · intro s t hst
    by_cases hs : s = s0
    · subst hst
      subst hs
      rw [Function.update_self, ha']
    · simp [Function.update_of_ne hs, h.sb t (by omega)]
  · intro r s hrs
    by_cases hs : s = s0
    · have hr : r = s - 1 := by omega
      subst hr
      subst hs
      rw [Function.update_self, Function.update_self, hy']
    · have hr : r ≠ s0 - 1 := by omega
      simp [Function.update_of_ne hs, Function.update_of_ne hr, h.sz s (by omega)]

private structure St {C C' : DC} (Φ : C.Hom C') (n : ℤ) (a : C.Tot) (y : C'.Tot) (p : ℕ) where
  b : ∀ s, C.A p s
  z : ∀ s, C'.A p s
  u : ∀ s, C.A p s
  v : ∀ s, C'.A p s
  cl : Cl Φ n p b z
  sv : Sv Φ n p b z u v
  hb : ∀ s, C.δ p s (a p s) = C.δ p s (b s)
  hz : ∀ s, C'.δ p s (y p s) = C'.δ p s (z s)

private theorem cl_zero {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {a : C.Tot} {y : C'.Tot}
    (ha : C.Deg (n + 1) a) (hy : C'.Deg n y) (hD : C.D (n + 1) a = 0) (hP : Φ.tot a = C'.D n y) :
    Cl Φ n 0 (a 0) (y 0) := by
  refine ⟨fun s hs => ha 0 s hs, fun s hs => hy 0 s hs, ?_, ?_⟩
  · intro s t e
    have h1 := congrFun (congrFun hD 0) t
    rw [D_zero C (n + 1) a s t e] at h1
    exact h1
  · intro s t e
    have h1 := congrFun (congrFun hP 0) t
    rw [D_zero C' n y s t e] at h1
    exact h1

private theorem cl_next {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {a : C.Tot} {y : C'.Tot} {p : ℕ}
    (hC : C.Ok) (hC' : C'.Ok) (hΦ : Φ.Ok)
    (ha : C.Deg (n + 1) a) (hy : C'.Deg n y) (hD : C.D (n + 1) a = 0) (hP : Φ.tot a = C'.D n y)
    (x : St Φ n a y p) :
    Cl Φ n (p + 1) (fun s => a (p + 1) s - (n + 1).negOnePow • C.δ p s (x.u s))
      (fun s => y (p + 1) s + (n + 1).negOnePow • C'.δ p s (x.v s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [ha (p + 1) s hs, x.sv.su s (by omega), map_zero, smul_zero, sub_zero]
  · intro s hs
    simp only [hy (p + 1) s hs, x.sv.sv s (by omega), map_zero, smul_zero, add_zero]
  · intro s t e
    have h1 := congrFun (congrFun hD (p + 1)) t
    rw [D_succ C (n + 1) a p s t e, Int.negOnePow_succ, Units.neg_smul, x.hb t] at h1
    simp only [Pi.zero_apply] at h1
    have h2 : C.d (p + 1) s t (C.δ p s (x.u s)) = C.δ p t (x.b t) := by
      rw [hC.comm, x.sv.du s t e]
    simp only [map_sub, map_us, h2]
    rwa [← sub_eq_add_neg] at h1
  · intro s t e
    have h1 := congrFun (congrFun hP (p + 1)) t
    rw [D_succ C' n y p s t e] at h1
    change Φ (p + 1) t (a (p + 1) t) = _ at h1
    have h3 : C'.δ p t (y p t) =
        C'.δ p t (Φ p t (x.u t)) + C'.d (p + 1) s t (C'.δ p s (x.v s)) := by
      rw [x.hz t, x.sv.yv s t e, map_add (f := _), hC'.comm]
    have h4 : Φ (p + 1) t (C.δ p t (x.u t)) = C'.δ p t (Φ p t (x.u t)) := hΦ.2 p t (x.u t)
    simp only [map_sub, map_add (f := _), map_us, h4]
    rw [h1, h3, smul_add]
    abel

theorem UpperTheory.totalExact_of_columnExact :
    ∀ (C C' : DC) (Φ : C.Hom C'), C.Ok → C'.Ok → Φ.Ok → (∀ p, Φ.ColEx p) → Φ.TotEx := by
  intro C C' Φ hC hC' hΦ hcol n a y ha hy hD hP
  have hcl0 := cl_zero (Φ := Φ) ha hy hD hP
  have hs0 := solve (hcol 0) hcl0
  let S0 : St Φ n a y 0 := ⟨a 0, y 0, hs0.choose, hs0.choose_spec.choose, hcl0,
    hs0.choose_spec.choose_spec, fun _ => rfl, fun _ => rfl⟩
  let step : ∀ p, St Φ n a y p → St Φ n a y (p + 1) := fun p x =>
    { b := fun s => a (p + 1) s - (n + 1).negOnePow • C.δ p s (x.u s)
      z := fun s => y (p + 1) s + (n + 1).negOnePow • C'.δ p s (x.v s)
      u := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose
      v := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose_spec.choose
      cl := cl_next hC hC' hΦ ha hy hD hP x
      sv := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose_spec.choose_spec
      hb := fun s => by simp only [map_sub, map_us, hC.δδ, smul_zero, sub_zero]
      hz := fun s => by simp only [map_add (f := _), map_us, hC'.δδ, smul_zero, add_zero] }
  let S : ∀ p, St Φ n a y p := fun p => Nat.rec (motive := fun p => St Φ n a y p) S0 step p
  refine ⟨fun p s => (S p).u s, fun p s => (S p).v s, ?_, ?_, ?_, ?_⟩
  · intro p s hps
    exact (S p).sv.su s hps
  · intro p s hps
    exact (S p).sv.sv s hps
  · funext p t
    rcases p with _ | p
    · rw [D_zero C n _ (t - 1) t (by ring)]
      exact (S 0).sv.du (t - 1) t (by ring)
    · rw [D_succ C n _ p (t - 1) t (by ring)]
      have h1 := (S (p + 1)).sv.du (t - 1) t (by ring)
      change C.d (p + 1) (t - 1) t ((S (p + 1)).u (t - 1)) =
        a (p + 1) t - (n + 1).negOnePow • C.δ p t ((S p).u t) at h1
      beta_reduce
      rw [h1, sub_add_cancel]
  · funext p t
    rcases p with _ | p
    · show y 0 t = Φ 0 t ((S 0).u t) + C'.D (n - 1) (fun p s => (S p).v s) 0 t
      rw [D_zero C' (n - 1) _ (t - 1) t (by ring)]
      exact (S 0).sv.yv (t - 1) t (by ring)
    · show y (p + 1) t = Φ (p + 1) t ((S (p + 1)).u t) +
        C'.D (n - 1) (fun p s => (S p).v s) (p + 1) t
      rw [D_succ C' (n - 1) _ p (t - 1) t (by ring)]
      have h1 := (S (p + 1)).sv.yv (t - 1) t (by ring)
      change y (p + 1) t + (n + 1).negOnePow • C'.δ p t ((S p).v t) =
        Φ (p + 1) t ((S (p + 1)).u t) + C'.d (p + 1) (t - 1) t ((S (p + 1)).v (t - 1)) at h1
      have e : (n - 1 + 1).negOnePow = -(n + 1).negOnePow := by
        rw [sub_add_cancel, Int.negOnePow_succ, neg_neg]
      beta_reduce
      rw [e, Units.neg_smul, eq_sub_of_add_eq h1]
      abel
end

