module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ActionConvergesLadicCauchyAndStar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
section
noncomputable section
open scoped BigOperators
open Classical

namespace GlobalTheory.CharBlock

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries

variable {C : Type} [Field C]

def IsExp {σ : Type} (y : σ → C) (F : MvPowerSeries σ C) : Prop :=
  constantCoeff F = 1 ∧ ∀ w, pderiv w F = y w • F

theorem IsExp.one {σ : Type} : IsExp (fun _ : σ => (0 : C)) 1 := ⟨by simp, fun w => by simp⟩

theorem IsExp.mul {σ : Type} {y y' : σ → C} {F F' : MvPowerSeries σ C} (h : IsExp y F)
    (h' : IsExp y' F') : IsExp (fun w => y w + y' w) (F * F') := by
  refine ⟨by rw [map_mul, h.1, h'.1, one_mul], fun w => ?_⟩
  rw [Derivation.leibniz, h.2, h'.2]
  simp only [smul_eq_mul, add_smul, mul_smul_comm]
  rw [add_comm, mul_comm F' F]

theorem IsExp.prod {σ α : Type} (s : Finset α) {y : α → σ → C} {F : α → MvPowerSeries σ C}
    (h : ∀ i, IsExp (y i) (F i)) : IsExp (fun w => ∑ i ∈ s, y i w) (∏ i ∈ s, F i) := by
  induction s using Finset.induction_on with
  | empty => simpa using IsExp.one
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a).mul ih

theorem IsExp.subst {σ τ : Type} [Fintype σ] [Finite τ] {y : σ → C} {F : MvPowerSeries σ C}
    (h : IsExp y F) (e : σ → τ) :
    IsExp (fun t => ∑ j, if e j = t then y j else 0)
      (F.subst fun j => (X (e j) : MvPowerSeries τ C)) := by
  have hs : HasSubst (fun j => (X (e j) : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  constructor
  · have := rename_eq_subst (R := C) (f := e) (p := F)
    have h2 := constantCoeff_rename (R := C) (f := e) F
    rw [this, h.1] at h2
    exact h2
  · intro w
    rw [Formalism.G.LogCR.pderiv_subst (by simp), Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h.2, subst_smul hs]
    by_cases hj : e j = w
    · subst hj; simp
    · simp [hj, pderiv_X_of_ne hj]

theorem IsExp.coeff {σ : Type} {y : σ → C} {F : MvPowerSeries σ C} (h : IsExp y F) :
    ∀ (n : ℕ) (m : σ →₀ ℕ), m.degree = n →
      (mfact m : C) * coeff m F = m.prod fun s k => y s ^ k := by
  intro n
  induction n with
  | zero =>
    intro m hm
    rw [Finsupp.degree_eq_zero_iff] at hm
    subst hm
    simp [mfact, h.1]
  | succ n ih =>
    intro m hm
    have hne : m ≠ 0 := by rintro rfl; simp at hm
    obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hne
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
      refine ⟨m - Finsupp.single w 1, ?_⟩
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      simp at hw; omega
    have hd : m'.degree = n := by
      rw [map_add (f := _), Finsupp.degree_single] at hm; omega
    have h1 := congrArg (MvPowerSeries.coeff m') (h.2 w)
    rw [coeff_pderiv, coeff_smul] at h1
    have h2 : mfact (m' + Finsupp.single w 1) = (m' w + 1) * mfact m' := by
      unfold mfact
      have e1 := Finsupp.mul_prod_erase' (m' + Finsupp.single w 1) w (fun _ k => k.factorial) (by simp)
      have e2 := Finsupp.mul_prod_erase' m' w (fun _ k => k.factorial) (by simp)
      rw [← e1, ← e2, Finsupp.erase_add, Finsupp.erase_single, add_zero]
      simp [Nat.factorial_succ, mul_assoc]
    rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), ← ih m' hd, h2,
      Finsupp.prod_single_index (by simp)]
    push_cast
    linear_combination (mfact m' : C) * h1

theorem IsExp.jet {σ : Type} {y : σ → C} {F : MvPowerSeries σ C} (h : IsExp y F)
    (P : MvPolynomial σ C) : jetAt0 P F = MvPolynomial.eval y P := by
  unfold jetAt0
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_assoc, h.coeff _ m rfl]
  rfl

theorem coeff_mvExp {σ : Type} (h : MvPowerSeries σ C) (m : σ →₀ ℕ) :
    coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) := rfl

theorem mvExp_zero {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  rw [coeff_mvExp, Finset.sum_range_succ']
  simp

theorem isExp_mvExp [CharZero C] {σ : Type} [Fintype σ] (y : σ → C) :
    IsExp y (mvExp (∑ x, y x • (X x : MvPowerSeries σ C))) := by
  constructor
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mvExp]; simp
  · intro w
    ext m
    have hL : pderiv w (∑ x, y x • (X x : MvPowerSeries σ C)) = MvPowerSeries.C (y w) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single w]
      · simp [smul_eq_C_mul]
      · intro b _ hb; simp [pderiv_X_of_ne hb]
      · simp
    rw [coeff_pderiv, coeff_smul, coeff_mvExp, coeff_mvExp, map_add (f := _), Finsupp.degree_single,
      Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]
    have h0 : MvPowerSeries.coeff (m + Finsupp.single w 1)
        ((∑ x, y x • (X x : MvPowerSeries σ C)) ^ 0) = 0 := by
      rw [pow_zero, coeff_one, if_neg]
      intro h
      have := DFunLike.congr_fun h w
      simp at this
    rw [h0, zero_div, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := coeff_pderiv (i := w) ((∑ x, y x • (X x : MvPowerSeries σ C)) ^ (k + 1)) m
    rw [pderiv_pow, hL, Nat.add_sub_cancel, ← map_natCast (MvPowerSeries.C (σ := σ) (R := C)),
      coeff_mul_C, coeff_C_mul] at h1
    have hk : (k.factorial : C) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hk1 : ((k + 1 : ℕ) : C) ≠ 0 := by exact_mod_cast k.succ_ne_zero
    rw [div_mul_eq_mul_div, ← h1, Nat.factorial_succ]
    push_cast at hk1 ⊢
    field_simp

variable {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def stdSys {I J : Type} [Fintype I] [Fintype J] (X : Cart V d I J) : Sys X where
  tan := fun c => Pi.single c 1
  cur := fun c => X.std c
  curve := fun c => X.std_spec c
  unimod := by
    have : (Matrix.of fun c : I => (Pi.single c 1 : I → C)) = 1 := by
      ext a b
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this, Matrix.det_one, AddValuation.map_one]

theorem val_eq [CharZero C] (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (g : Fin 2)
    {n r : ℕ} (hn : n ≤ r) (en : Fin r → I g) (y : Fin n → I g → C) (u : ℕ) :
    ValOf hL (MvPolynomial.rename (fun x : Fin n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin n × WV I))
        (minorK C n r n) ^ u) (fun _ => none)
      (fun ρ => upG g (mvExp (∑ x : I g, y ρ x • (X x : MvPowerSeries (I g) C)))) =
    (Matrix.of fun ρ c : Fin n => y ρ (en (Fin.castLE hn c))).det ^ u := by
  unfold ValOf
  have h0 : ∀ ρ : Fin n, mvExp (rowCopy ρ (0 : MvPowerSeries (WV I) C)) = 1 := by
    intro ρ
    have : rowCopy ρ (0 : MvPowerSeries (WV I) C) = 0 := by
      unfold rowCopy
      have hs : HasSubst (fun w : WV I => (X (ρ, w) : MvPowerSeries (Fin n × WV I) C)) :=
        hasSubst_of_constantCoeff_zero (by simp)
      rw [← coe_substAlgHom hs, map_zero]
    rw [this, mvExp_zero]
  simp only [h0, mul_one]
  have h1 := IsExp.prod Finset.univ fun ρ : Fin n =>
    ((isExp_mvExp (y ρ)).subst fun x : I g => (⟨g, x⟩ : WV I)).subst
      fun w : WV I => ((ρ, w) : Fin n × WV I)
  refine (h1.jet _).trans ?_
  rw [map_pow, MvPolynomial.eval_rename, minorK, dite_eq_left ⟨le_rfl, hn⟩, RingHom.map_det]
  congr 2
  ext ρ c
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
    Function.comp_apply, Fin.castLE_refl, Prod.mk.injEq]
  rw [Finset.sum_eq_single ρ, Finset.sum_eq_single (⟨g, en (Fin.castLE hn c)⟩ : WV I),
    Finset.sum_eq_single (en (Fin.castLE hn c))]
  all_goals simp +contextual

theorem core (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (ha : X.big g a) {r : ℕ}
    (hn : X.n ≤ r) (en : Fin r → I g) (hinj : Function.Injective en)
    (hty : ∀ c, (X.G g).ty (Sum.inl (en c)) = a) (u : ℕ) :
    ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
      ∃ gr : Fin X.n → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        (X.Alt → V.v (ValOf X.hL (MvPolynomial.rename
          (fun x : Fin X.n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin X.n × WV I))
          (minorK C X.n r X.n) ^ u) (fun _ => none) gr) ≤
          (((u : ℝ) * (X.n * gam V.l + X.m / ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ)) ∧
        ((∀ a, X.big g a) → V.v (ValOf X.hL (MvPolynomial.rename
          (fun x : Fin X.n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin X.n × WV I))
          (minorK C X.n r X.n) ^ u) (fun _ => none) gr) ≤
          (((u : ℝ) * (X.m / ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ)) := by
  haveI := X.charZero
  choose t ht _ using fun g => tExistsUnique (X.G g) (stdSys (X.G g))
  have hint : ∀ (c x : I g), V.Ge 0 ((Pi.single c 1 : I g → C) x) := by
    intro c x
    rw [Pi.single_apply]
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  obtain ⟨y, -, hy, h1, h2⟩ := X.CH g a ha (fun c => Pi.single (en (Fin.castLE hn c)) 1)
    ⟨fun c x => hint _ _, fun x c => (Pi.single (en (Fin.castLE hn c)) 1 : I g → C) x,
      fun x c => hint _ _, fun c c' => by
        simp [Pi.single_apply, hinj.eq_iff, (Fin.castLE_injective hn).eq_iff, eq_comm]⟩
    (fun c x hx => Pi.single_eq_of_ne (fun h => hx (by rw [h]; exact hty _)) _)
  have key : ∀ b : ℝ, V.v (Matrix.of fun ρ c : Fin X.n =>
        ∑ x, y ρ x * (Pi.single (en (Fin.castLE hn c)) 1 : I g → C) x).det ≤ (b : WithTop ℝ) →
      V.v ((Matrix.of fun ρ c : Fin X.n => y ρ (en (Fin.castLE hn c))).det ^ u) ≤
        (((u : ℝ) * b : ℝ) : WithTop ℝ) := by
    intro b hb
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at hb
    rw [AddValuation.map_pow, ← nsmul_eq_mul, WithTop.coe_nsmul]
    exact nsmul_le_nsmul_right hb u
  refine ⟨fun g => stdSys (X.G g), t, ht, _, hy _ t ht, fun h => ?_, fun h => ?_⟩
  · rw [val_eq X.hL g hn en y u]
    simpa [RowData.m] using key _ (h1 h)
  · rw [val_eq X.hL g hn en y u]
    simpa [RowData.m] using key _ (h2 h)

theorem chSupply : CHSupply ∧ RF.CHSupply := by
  constructor
  · intro C _ V d _ I J _ _ X F g a ha u
    have hn : X.n ≤ X.rk g a := by
      unfold RowData.rk; rw [X.rk_big g a ha]; omega
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ := core X g a ha hn (F.en g a) (F.en_inj g a) (F.en_ty g a) u
    exact ⟨fun h => ⟨S, t, ht, gr, hgr, h1 h⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩
  · intro C _ V d _ I J _ _ X F g a ha u
    have hn : X.n ≤ X.rkF g a := by
      unfold RowData.rkF; rw [X.rk_big g a ha]; omega
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ := core X g a ha hn (F.en g a) (F.en_inj g a) (F.en_ty g a) u
    exact ⟨fun h => ⟨S, t, ht, gr, hgr, h1 h⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩

end GlobalTheory.CharBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAdjointIntegralEndOfLadicLimit
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ActionLimit

variable {C : Type} [Field C]

theorem eq_zero_of_forall_ge (V : VF C) (x : C) (h : ∀ N : ℕ, V.Ge N x) : x = 0 := by
  by_contra hx
  have ht : V.v x ≠ ⊤ := (AddValuation.ne_top_iff V.v).2 hx
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
  obtain ⟨N, hN⟩ := exists_nat_gt r
  have := h N
  rw [VF.Ge, ← hr, WithTop.coe_le_coe] at this
  exact absurd hN (not_lt.2 this)

theorem exists_nat_ge_neg (V : VF C) (x : C) : ∃ K : ℕ, V.Ge (-(K : ℝ)) x := by
  by_cases ht : V.v x = ⊤
  · exact ⟨0, by rw [VF.Ge, ht]; exact le_top⟩
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
  obtain ⟨N, hN⟩ := exists_nat_gt (-r)
  refine ⟨N, ?_⟩
  rw [VF.Ge, ← hr, WithTop.coe_le_coe]
  linarith

theorem limit_unique (V : VF C) (s : ℕ → C) (x y : C) (hx : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (x - s n))
    (hy : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (y - s n)) : x = y := by
  refine sub_eq_zero.1 (eq_zero_of_forall_ge V _ fun N => ?_)
  obtain ⟨a, ha⟩ := hx N
  obtain ⟨b, hb⟩ := hy N
  have := (ha _ (le_max_left a b)).sub (hb _ (le_max_right a b))
  rwa [sub_sub_sub_cancel_right] at this

theorem linear_limit (V : VF C) {dd : ℕ} (e : Pt C 1 dd) (s : ℕ → Pt C 1 dd)
    (h : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (s n i)))
    (N : ℕ) (v : Fin dd → C) (i : Fin dd) :
    ∃ n0, ∀ n ≥ n0, V.Ge N ((dLin e).mulVec v i - linAct (s n) v i) := by
  choose K hK using fun j => exists_nat_ge_neg V (v j)
  choose m hm using fun j => h (N + K j) i (Finsupp.single ((0 : Fin 1), j) 1)
  refine ⟨Finset.univ.sup m, fun n hn => ?_⟩
  have e1 : (dLin e).mulVec v i - linAct (s n) v i =
      ∑ j, (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (e i) -
        MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (s n i)) * v j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rfl
  rw [e1]
  refine VF.Ge.sum fun j _ => ?_
  have := (hm j n (le_trans (Finset.le_sup (f := m) (Finset.mem_univ j)) hn)).mul (hK j)
  refine this.mono ?_
  push_cast
  linarith

theorem subst_singlePointUncurry {dd : ℕ} {τ : Type} (a : Fin dd → MvPowerSeries τ C)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : PS C 1 dd) :
    MvPowerSeries.subst a (un1 f) = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  let ι : Fin dd ≃ Fin 1 × Fin dd :=
    { toFun := fun x => (0, x)
      invFun := fun p => p.2
      left_inv := fun _ => rfl
      right_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl }
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha),
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin dd => ha p.2),
    ← finsum_comp_equiv (Finsupp.equivCongrLeft ι)]
  refine finsum_congr fun e => ?_
  rw [Finsupp.equivCongrLeft_apply, Finsupp.prod_equivMapDomain, Finsupp.equivMapDomain_eq_mapDomain]
  rfl

theorem germComp1_eq_subst {dd n : ℕ} (e : Pt C 1 dd) (a : Pt C n dd) (i : Fin dd) :
    comp1 e a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (![a] : Fin 1 → Pt C n dd) q.1 q.2) (e i) = _
  congr 1
  funext ⟨s, x⟩
  obtain rfl : s = 0 := Subsingleton.elim _ _
  rfl

theorem subst_exp_eq_mvExp [CharZero C] {σ : Type} (f : MvPowerSeries σ C) (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.subst f (PowerSeries.exp C) = mvExp f := by
  ext m
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_inv_mul]
  · intro k hk
    by_contra hc
    apply hk
    have hlt : m.degree < k := by simpa using hc
    have : MvPowerSeries.coeff m (f ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hf)
      exact_mod_cast hlt
    simp [this]

section Chart

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)

theorem gp_lg : GP Y.lg := fun i => by
  have := Y.lg_lin i 0 (by simp)
  simpa using this

theorem dLin_lg : dLin Y.lg = 1 := by
  rw [← germLinearPart_coordinatePoint_zero]
  ext i j
  exact Y.lg_lin i _ (by simp)

theorem eq_exp_lin_log (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1))) :
    e = comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap (dLin e)) Y.lg) := by
  have h0 := gp_lg Y
  have hF := Y.B.G.const
  have hi : IsInvPair Y.lg Y.ex := ⟨h0, Y.ex_const, Y.lg_ex, Y.ex_lg⟩
  have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
  have hl : comp1 Y.lg (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      comp1 Y.lg (pt C (n := 2) dd 0) + comp1 Y.lg (pt C (n := 2) dd 1) := funext Y.lg_add
  have e1 := additive_eq_lin _ hF Y.lg Y.ex (comp1 Y.lg e) (dLin_lg Y) hl hi (gp_comp1 _ _ h0 he) (by
    rw [gt_comp1_comp1 _ _ he _ (gp_addOf _ hF _ _ p0 p1), hhom,
      additive_at _ hF _ hl _ _ (gp_comp1 _ _ he p0) (gp_comp1 _ _ he p1),
      gt_comp1_comp1 _ _ he _ p0, gt_comp1_comp1 _ _ he _ p1])
  rw [dLin_comp _ _ he, dLin_lg, one_mul] at e1
  rw [← e1, gt_comp_inv' hi _ he]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)

omit [CharZero C] in
theorem subst_linMap (M : Matrix (Fin dd) (Fin dd) C) (L : Pt C 1 dd) (h0 : GP L)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (x : Fin dd) :
    ∑ y, M x y • MvPowerSeries.subst a (un1 (L y)) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 (LogExpAdaptedGauge.linMap M) L x) := by
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [germComp_matrixLinearMap_apply _ _ h0, ← MvPowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [subst_singlePointUncurry a ha, ← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.coe_substAlgHom hs,
    MvPowerSeries.subst_smul hs]

theorem matrixEnd_linearMap (M : Matrix (Fin dd) (Fin dd) C)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP (Y.raw p) M a i =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) i) := by
  have h0 := gp_lg Y
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  have hL : GP (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) := gp_comp1 _ _ (gp_linMap _) h0
  have e0 : endP (Y.raw p) M a i =
    MvPowerSeries.subst (fun x => ∑ y, M x y • MvPowerSeries.subst a (un1 (Y.lg y))) (un1 (Y.ex i)) := rfl
  rw [e0, funext (subst_linMap M Y.lg h0 a ha)]
  generalize comp1 (LogExpAdaptedGauge.linMap M) Y.lg = L at hL ⊢
  have hz : ∀ x, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (L x)) = 0 :=
    fun x => Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (fun q : Fin 1 × Fin dd => ha q.2) (hL x)
  rw [subst_singlePointUncurry _ hz, germComp1_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => hL q.2) hs]

theorem matrixEnd_eq_subst (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP (Y.raw p) (dLin e) a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  rw [matrixEnd_linearMap Y p _ a ha, ← eq_exp_lin_log Y e he hhom]

theorem matrixEnd_eq_comp (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {n : ℕ} (a : Pt C n dd) (ha : GP a) : endP (Y.raw p) (dLin e) a = comp1 e a := by
  funext i
  rw [matrixEnd_eq_subst Y p e he hhom a ha, germComp1_eq_subst]

theorem hAt_eq_ev {n : ℕ} (a b : Pt C n dd) : hAt (Y.raw p) a b = ev ![a, b] Y.h := by
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s <;> rfl

theorem isEnd_of_hom (e e' : Pt C 1 dd) (he : GP e) (he' : GP e')
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    (hhom' : comp1 e' (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e' (pt C (n := 2) dd 0)) (comp1 e' (pt C (n := 2) dd 1)))
    (hi : ∀ i, IntS V (e i)) (hi' : ∀ i, IntS V (e' i))
    (hx : IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 e' (pt C dd 1)] Y.h))) :
    IsEnd (Y.raw p) V (dLin e) (dLin e') := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have hc : MvPowerSeries.constantCoeff Y.h = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt (0 : Fin 1))) Y.h, Y.gauge.ax0, map_zero]
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [matrixEnd_eq_subst Y p e he hhom _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi i _
  · rw [matrixEnd_eq_subst Y p e' he' hhom' _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi' i _
  · have g0 : gp C (Fin dd) (0 : Fin 2) = pt C dd 0 := rfl
    have g1 : gp C (Fin dd) (1 : Fin 2) = pt C dd 1 := rfl
    rw [g0, g1, matrixEnd_eq_comp Y p e he hhom _ (gp_pt 0), matrixEnd_eq_comp Y p e' he' hhom' _ (gp_pt 1),
      hAt_eq_ev, hAt_eq_ev, ← subst_exp_eq_mvExp]
    · exact hx
    · rw [map_sub, gt_const_ev _ (pair_points_zero_constant (gp_comp1 _ _ he (gp_pt 0)) (gp_pt 1)) _ hc,
        gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ he' (gp_pt 1))) _ hc, sub_zero]

end Chart

theorem exists_isEnd_of_limit : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd (Y.raw p) V M M' ∧ IsEnd (Y.raw p) V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  intro C _ _ V O _ _ dd Y d _ I _ p a ha
  obtain ⟨c1, c2⟩ := _root_.GlobalTheory.ActionLimit.main C V O dd Y a ha
  obtain ⟨e, eb, i1, i2, l1, l2, h1, x1⟩ := _root_.GlobalTheory.ActLimit.limit_endomorphisms C V O dd Y a c1 c2
  obtain ⟨f, fb, -, -, l3, l4, h2, x2⟩ := _root_.GlobalTheory.ActLimit.limit_endomorphisms C V O dd Y (fun n => star (a n)) c2
    (by simpa only [star_star] using c1)
  simp only [star_star] at l4
  obtain rfl : f = eb := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l3 N i μ) (fun N => l2 N i μ)
  obtain rfl : fb = e := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l4 N i μ) (fun N => l1 N i μ)
  have hz : ∀ (g : Pt C 1 dd) (s : ℕ → O), (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (g i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i))) → GP g := by
    intro g s hg i
    refine limit_unique V (fun n => MvPowerSeries.coeff 0 (Y.B.A.act (s n) i)) _ _ (fun N => hg N i 0)
      fun N => ⟨0, fun n _ => ?_⟩
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.B.A.const, sub_zero]
    exact VF.Ge.zero _
  have g1 := hz fb a l1
  have g2 := hz f (fun n => star (a n)) l2
  exact ⟨dLin fb, dLin f, isEnd_of_hom Y p fb f g1 g2 h1 h2 i1 i2 x1, isEnd_of_hom Y p f fb g2 g1 h2 h1 i2 i1 x2,
    linear_limit V fb _ l1, linear_limit V f _ l2⟩

end GlobalTheory.ActionLimit
end
end

