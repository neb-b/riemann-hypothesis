module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfGe
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndPairPlaces
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.TeichPair

theorem hasTeich : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ g, HasTeich (Y.raw p) V g := by
  intro C _ _ V O _ _ dd Y d _ I _ p g
  obtain ⟨s, N, ζ, hs, hN, h1, h2, h3, hζ⟩ := exists_seq V Y.cpl (p.em g) (p.em_int g) (p.em_frob g)
    (fun a a' h => p.em_sep (g, a) (g, a') fun h' => h (congrArg Prod.snd h')) (p.em_unr g)
  obtain ⟨M, M', hM, -, hl, hl'⟩ := _root_.GlobalTheory.ActionLimit.exists_isEnd_of_limit C V O dd Y d I p s hs
  have key : ∀ (a : ZMod d) (z w : C), V.Ge 0 w →
      (∀ N : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge N (z - p.em g a (s n) * w)) → z = ζ a * w := fun a z w hw h => by
    rw [← sub_eq_zero]
    refine eq_zero_of_ge (V := V) fun n => ?_
    obtain ⟨n0, hn⟩ := h n
    have e1 := hn (max n0 n) (le_max_left _ _)
    have e2 := (hw.mul_int (hζ a (max n0 n))).mono (w' := n) (by exact_mod_cast le_max_right _ _)
    have := e1.sub e2
    convert this using 1
    ring
  have hconj : ∀ a x, p.em (1 - g) a (star x) = p.em g a x := fun a x => by
    fin_cases g
    · show p.em 1 a (star x) = p.em 0 a x
      rw [p.em_conj, star_star]
    · show p.em 0 a (star x) = p.em 1 a x
      rw [p.em_conj]
  refine ⟨N, ζ, M, M', hN, h1, h2, h3, hM, fun c => funext fun i => ?_, fun q => funext fun i => ?_⟩
  · refine key _ _ _ (p.u_int g c i) fun n => ?_
    have := hl n (p.u g c) i
    simp only [p.u_eig] at this
    exact this
  · refine key _ _ _ (p.u_int (1 - g) q i) fun n => ?_
    have := hl' n (p.u (1 - g) q) i
    simp only [p.u_eig, hconj] at this
    exact this

end GlobalTheory.TeichPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivationsConstantInLogCoordinates
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InvDerivLog

open MvPowerSeries GlobalTheory.RowLawSquare ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {C : Type} [Field C] {dd : ℕ} {τ : Type}

open scoped MvPowerSeries.WithPiTopology in
private theorem pderiv_subst_of_zero_constantCoeff {σ : Type} [Fintype σ]
    {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ C) (t : τ) :
    pderiv t (subst a f) = ∑ s, subst a (pderiv s f) * pderiv t (a s) := by
  let : UniformSpace C := ⊥
  let : DiscreteUniformity C := ⟨rfl⟩
  have hsubst : Continuous (subst a : MvPowerSeries σ C → MvPowerSeries τ C) :=
    continuous_subst (hasSubst_of_constantCoeff_zero ha)
  have hderiv {ι : Type} (i : ι) :
      Continuous (pderiv (R := C) i : MvPowerSeries ι C → MvPowerSeries ι C) := by
    apply continuous_pi
    intro d
    change Continuous (fun g : MvPowerSeries ι C => coeff d (pderiv i g))
    simp only [coeff_pderiv]
    exact (WithPiTopology.continuous_coeff C _).mul continuous_const
  refine WithPiTopology.denseRange_toMvPowerSeries.induction_on f
    (isClosed_eq ((hderiv t).comp hsubst) (continuous_finsetSum _ fun s _ =>
      (hsubst.comp (hderiv s)).mul continuous_const)) ?_
  intro p
  simpa only [pderiv_coe, subst_coe] using Formalism.G.LogCR.pderiv_aeval p a t

theorem pderiv_substPointsPowerSeries_one {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (f : PS C 1 dd) (t : τ) :
    pderiv (R := C) t (sb ![a] f) = ∑ l, sb ![a] (pderiv (R := C) ((0 : Fin 1), l) f) * pderiv (R := C) t (a l) := by
  unfold sb
  rw [pderiv_subst_of_zero_constantCoeff (fun p : Fin 1 × Fin dd => zc1 ha p.1 p.2),
    Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem pderiv_substPointsPowerSeries_two {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (f : PS C 2 dd) (t : τ) :
    pderiv (R := C) t (sb ![a, b] f) = ∑ l, sb ![a, b] (pderiv (R := C) ((0 : Fin 2), l) f) * pderiv (R := C) t (a l) +
      ∑ l, sb ![a, b] (pderiv (R := C) ((1 : Fin 2), l) f) * pderiv (R := C) t (b l) := by
  unfold sb
  rw [pderiv_subst_of_zero_constantCoeff (fun p : Fin 2 × Fin dd => zc2 ha hb p.1 p.2),
    Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl

theorem sb_mul {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) (f g : PS C n dd) :
    sb a (f * g) = sb a f * sb a g := subst_mul (hasSubst_sb ha) f g

theorem sb_sum {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) {α : Type} (s : Finset α)
    (f : α → PS C n dd) : sb a (∑ x ∈ s, f x) = ∑ x ∈ s, sb a (f x) := by
  unfold sb
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← coe_substAlgHom (hasSubst_sb ha), map_sum]

theorem sb_zero {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) :
    sb a (0 : PS C n dd) = 0 := by
  unfold sb
  simp only [← coe_substAlgHom (hasSubst_sb ha), map_zero]

theorem sb_C {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (c : C) :
    sb a (MvPowerSeries.C c : PS C n dd) = MvPowerSeries.C c := by
  unfold sb
  rw [subst_C]

theorem zc_zero : Zc (0 : Fin dd → MvPowerSeries τ C) := fun _ => map_zero _

theorem sb_zeroPt (f : PS C 1 dd) :
    sb ![(0 : Fin dd → MvPowerSeries τ C)] f = MvPowerSeries.C (constantCoeff f) := by
  classical
  have hz := hasSubst_sb (zc1 (zc_zero (C := C) (dd := dd) (τ := τ)))
  ext e
  unfold sb
  rw [coeff_subst hz, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro x hx
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp), map_zero, smul_zero]
    obtain ⟨j, i⟩ := p
    fin_cases j
    exact zero_pow hp

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

theorem zc_ex {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) : Zc (fun x => sb ![a] (Y.ex x)) :=
  fun x => cc_sb (zc1 ha) (Y.ex_const x)

theorem law_ex {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (j : Fin dd) :
    sb ![fun x => sb ![a] (Y.ex x), fun x => sb ![b] (Y.ex x)] (Y.B.G.F j) = sb ![a + b] (Y.ex j) := by
  have h1 := ex_lg Y (zc_law Y (zc_ex Y ha) (zc_ex Y hb)) j
  simp only [← lg_law Y (zc_ex Y ha) (zc_ex Y hb), lg_ex Y ha, lg_ex Y hb] at h1
  exact h1.symm

theorem cc_pderiv_lg (i l : Fin dd) :
    constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (Y.lg l)) = if l = i then 1 else 0 := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, Y.lg_lin l _ (by simp), coeff_X]
  by_cases h : l = i
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right, zero_mul]
    intro h2
    rw [zero_add, Finsupp.single_left_inj one_ne_zero] at h2
    exact h (Prod.ext_iff.1 h2).2.symm

theorem cc_pderiv_ex (i l : Fin dd) :
    constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (Y.ex l)) = if l = i then 1 else 0 := by
  classical
  have e : sb ![Y.ex] (Y.lg l) = X ((0 : Fin 1), l) := congrFun Y.lg_ex l
  have e2 := congrArg (fun f => constantCoeff (pderiv (R := C) ((0 : Fin 1), i) f)) e
  have hz : Zc Y.ex := Y.ex_const
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pderiv_substPointsPowerSeries_one hz, map_sum, map_mul] at e2
  have h3 : ∀ x, constantCoeff (sb ![Y.ex] (pderiv (R := C) ((0 : Fin 1), x) (Y.lg l))) = if l = x then 1 else 0 :=
    fun x => by
      unfold sb
      rw [cc_subst (fun p : Fin 1 × Fin dd => zc1 hz p.1 p.2), cc_pderiv_lg]
  simp only [h3, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at e2
  rw [e2]
  by_cases h : l = i
  · subst h; simp
  · rw [ite_eq_right h, pderiv_X_of_ne (by simpa using h), map_zero]

theorem inv_field_ex {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (i j : Fin dd) :
    sb ![fun x => sb ![a] (Y.ex x), 0] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j)) =
      sb ![a] (pderiv (R := C) ((0 : Fin 1), i) (Y.ex j)) := by
  classical
  have z0 : Zc (pt C (n := 2) dd 0) := zc_pt 0
  have z1 : Zc (pt C (n := 2) dd 1) := zc_pt 1
  have zs : Zc (pt C (n := 2) dd 0 + pt C (n := 2) dd 1) := fun x => by
    rw [Pi.add_apply, map_add (f := _), z0 x, z1 x, add_zero]
  have d0 : ∀ l, pderiv (R := C) ((1 : Fin 2), i) (pt C (n := 2) dd 0 l) = 0 := fun l =>
    pderiv_X_of_ne (by simp)
  have d1 : ∀ l, pderiv (R := C) ((1 : Fin 2), i) (pt C (n := 2) dd 1 l) = if l = i then 1 else 0 := fun l => by
    by_cases h : l = i
    · subst h; rw [ite_eq_left rfl]; exact pderiv_X_self
    · rw [ite_eq_right h]; exact pderiv_X_of_ne (by simpa using h)
  have e := congrArg (pderiv (R := C) ((1 : Fin 2), i)) (law_ex Y z0 z1 j)
  rw [pderiv_substPointsPowerSeries_two (zc_ex Y z0) (zc_ex Y z1), pderiv_substPointsPowerSeries_one zs] at e
  simp only [pderiv_substPointsPowerSeries_one z0, pderiv_substPointsPowerSeries_one z1, Pi.add_apply, map_add (f := _), d0, d1, mul_zero, Finset.sum_const_zero,
    zero_add, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at e
  have h2 := zc2 ha (zc_zero (C := C) (dd := dd) (τ := τ))
  have s1 : ∀ {b : Pt C 2 dd} (_ : Zc b) (f : PS C 1 dd),
      sb ![a, 0] (sb ![b] f) = sb ![fun i => sb ![a, 0] (b i)] f := fun hb f => substPointsPowerSeries_eval_one h2 hb f
  have s2 : ∀ {b c : Pt C 2 dd} (_ : Zc b) (_ : Zc c) (f : PS C 2 dd),
      sb ![a, 0] (sb ![b, c] f) = sb ![fun i => sb ![a, 0] (b i), fun i => sb ![a, 0] (c i)] f :=
    fun hb hc f => substPointsPowerSeries_eval_two h2 hb hc f
  have e2 := congrArg (sb ![a, 0]) e
  have p0 : (fun i => sb ![a, 0] (pt C dd 0 i)) = a := sb_pt' h2 0
  have p1 : (fun i => sb ![a, 0] (pt C dd 1 i)) = 0 := sb_pt' h2 1
  have ps : (fun i => sb ![a, 0] ((pt C (n := 2) dd 0 + pt C (n := 2) dd 1) i)) = a := by
    funext x
    rw [Pi.add_apply, sb_add h2, congrFun p0 x, congrFun p1 x, Pi.zero_apply, add_zero]
  have c0 : (fun x => (MvPowerSeries.C (constantCoeff (Y.ex x)) : MvPowerSeries τ C)) = 0 := by
    funext x
    rw [Y.ex_const, map_zero, Pi.zero_apply]
  rw [sb_sum h2, s1 zs, ps] at e2
  simp only [sb_mul h2, s2 (zc_ex Y z0) (zc_ex Y z1), s1 z0, s1 z1, p0, p1, sb_zeroPt, c0, cc_pderiv_ex,
    apply_ite MvPowerSeries.C, map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at e2
  exact e2

theorem subst_ex_DofN : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (n : ℕ) (W : Type) [Fintype W] (Z : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (Z s) = 0) → ∀ (b : Fin n) (u : Fin dd → C) (co : W → C), (∀ (b' : Fin n) (j : Fin dd), ∑ w, co w • MvPowerSeries.pderiv (R := C) w (Z (b', j)) = if b' = b then MvPowerSeries.C (u j) else 0) → ∀ G : PS C n dd, MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) (DofN (Y.B.FK C) b u G) = ∑ w, co w • MvPowerSeries.pderiv (R := C) w (MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) G) := by
  classical
  intro C _ _ V O _ _ dd Y n W _ Z hZ b u co hco G
  have hz : ∀ b' : Fin n, Zc (fun j => Z (b', j)) := fun b' j => hZ _
  let E : Fin n → Fin dd → MvPowerSeries W C := fun b' x => sb ![fun j => Z (b', j)] (Y.ex x)
  have hE : ∀ b', Zc (E b') := fun b' => zc_ex Y (hz b')
  have eE : (fun s : Fin n × Fin dd => subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) =
      fun s => E s.1 s.2 := by
    funext s
    rw [GlobalTheory.RowLawSquare.subst_singlePointUncurry (hz s.1)]
    show _ = sb _ _
    unfold sb
    congr 1
    funext ⟨j, i⟩
    fin_cases j
    rfl
  rw [eE]
  show sb E _ = ∑ w, co w • pderiv (R := C) w (sb E G)
  have hD : ∀ (b' : Fin n) (j : Fin dd), ∑ w, co w • pderiv (R := C) w (E b' j) = if b' = b then
      ∑ i, MvPowerSeries.C (u i) * sb ![fun j => Z (b, j)] (pderiv (R := C) ((0 : Fin 1), i) (Y.ex j)) else 0 := by
    intro b' j
    simp only [E, pderiv_substPointsPowerSeries_one (hz b'), Finset.smul_sum, ← mul_smul_comm]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hco]
    split_ifs with h
    · subst h
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · simp
  have hR : ∑ w, co w • pderiv (R := C) w (sb E G) =
      ∑ p : Fin n × Fin dd, sb E (pderiv (R := C) p G) * ∑ w, co w • pderiv (R := C) w (E p.1 p.2) := by
    unfold sb
    simp only [pderiv_subst_of_zero_constantCoeff (a := fun p : Fin n × Fin dd => E p.1 p.2)
      (fun p => hE p.1 p.2), Finset.smul_sum, ← mul_smul_comm, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hR, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · unfold DofN
    rw [sb_sum hE]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hD, ite_eq_left rfl, sb_mul hE, mul_comm, sb_sum hE]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sb_mul hE, sb_C, substPointsPowerSeries_eval_two hE (zc_pt b) zc_zero, sb_pt' hE, FK_self, ← inv_field_ex Y (hz b)]
    have : (fun i : Fin dd => sb E ((0 : Pt C n dd) i)) = 0 := funext fun _ => sb_zero hE
    rw [this]
  · intro b' _ h
    simp [hD, h]
  · simp

end GlobalTheory.InvDerivLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsGaugeAdjointIntegralEndPairAdd
section
noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowVal MvPowerSeries

namespace GlobalTheory.RowLaw.EndSum

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {κ : Type} [Fintype κ]
  {X : RawChart C d I κ} {V : VF C}

theorem pair_cc {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) (p : Fin 2 × κ) :
    constantCoeff (if p.1 = 0 then a p.2 else b p.2) = 0 := by
  split_ifs
  · exact ha _
  · exact hb _

theorem gp_cc {n : ℕ} (j : Fin n) (x : κ) : constantCoeff (gp C κ j x) = 0 := constantCoeff_X _

theorem lg_cc (h : RLaw X V) (i : κ) : constantCoeff (X.lg i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, h.lin i 0 (by simp), coeff_zero_eq_constantCoeff_apply,
    constantCoeff_X]

theorem h_cc (h : RLaw X V) : constantCoeff X.h = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact h.axes 0 0 (by simp)

theorem sum_cc (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (x : κ) :
    constantCoeff (subst a (X.lg x) + subst b (X.lg x)) = 0 := by
  rw [map_add (f := _), cc_subst ha, cc_subst hb, lg_cc h, add_zero]

theorem lin_cc (h : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (x : κ) :
    constantCoeff (∑ y, M x y • subst a (X.lg y)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [smul_eq_C_mul, map_mul, cc_subst ha, lg_cc h, mul_zero]

theorem formalAdd_constantCoeff (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (x : κ) :
    constantCoeff (addP X a b x) = 0 := by
  unfold addP
  rw [cc_subst (sum_cc h ha hb), h.exc]

theorem constantCoeff_expMulLog (h : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (x : κ) : constantCoeff (endP X M a x) = 0 := by
  unfold endP
  rw [cc_subst (lin_cc h M ha), h.exc]

theorem hAt_cc (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) :
    constantCoeff (hAt X a b) = 0 := by
  unfold hAt
  rw [cc_subst (pair_cc ha hb), h_cc h]

theorem subst_addP (h : RLaw X V) {τ ρ : Type} [Finite τ] {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    {c : τ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) (x : κ) :
    subst c (addP X a b x) = addP X (fun y => subst c (a y)) (fun y => subst c (b y)) x := by
  have hS := hasSubst_of_constantCoeff_zero hc
  unfold addP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (sum_cc h ha hb)) hS]
  congr 1
  funext y
  rw [subst_add hS, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) hS,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hb) hS]

theorem subst_hAt {τ ρ : Type} [Finite τ] {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    {c : τ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) :
    subst c (hAt X a b) = hAt X (fun y => subst c (a y)) (fun y => subst c (b y)) := by
  have hS := hasSubst_of_constantCoeff_zero hc
  unfold hAt
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (pair_cc ha hb)) hS]
  congr 1
  funext p
  split_ifs <;> rfl

theorem subst_endP_X (h : RLaw X V) (M : Matrix κ κ C) {ρ : Type}
    {c : κ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) (x : κ) :
    subst c (endP X M (MvPowerSeries.X : κ → MvPowerSeries κ C) x) = endP X M c x := by
  have hS := hasSubst_of_constantCoeff_zero hc
  unfold endP
  rw [subst_comp_subst_apply
    (hasSubst_of_constantCoeff_zero (lin_cc h M (fun s => constantCoeff_X s))) hS]
  congr 1
  funext y
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom hS, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [coe_substAlgHom hS, subst_smul hS, subst_self]
  rfl

theorem lg_endP (h : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (i : κ) :
    subst (endP X M a) (X.lg i) = ∑ y, M i y • subst a (X.lg y) := by
  have hS := hasSubst_of_constantCoeff_zero (lin_cc h M ha)
  have := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h.exc) hS (X.lg i)
  rw [h.lgex, subst_X hS] at this
  exact this.symm

theorem matrixEnd_add (h : RLaw X V) (M N : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) : endP X (M + N) a = addP X (endP X M a) (endP X N a) := by
  funext i
  unfold addP
  simp only [lg_endP h _ ha]
  unfold endP
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem formalAdd_integral (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    (hai : ∀ s, IntS V (a s)) (hbi : ∀ s, IntS V (b s)) (x : κ) : IntS V (addP X a b x) := by
  have hc := pair_cc ha hb
  have hS := hasSubst_of_constantCoeff_zero hc
  have h1 := intS_subst hc (fun p => by split_ifs; exacts [hai _, hbi _]) (h.addInt x)
  rw [subst_addP h (gp_cc 0) (gp_cc 1) hc] at h1
  simpa [gp, subst_X hS] using h1

theorem defects [CharZero C] (h : RLaw X V) {τ : Type} {a b c : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (hc : ∀ s, constantCoeff (c s) = 0)
    (hai : ∀ s, IntS V (a s)) (hbi : ∀ s, IntS V (b s)) (hci : ∀ s, IntS V (c s)) :
    hAt X a c + hAt X b c - hAt X (addP X a b) c ∈ logInt V τ ∧
      hAt X a b + hAt X a c - hAt X a (addP X b c) ∈ logInt V τ := by
  let e : Fin 3 × κ → MvPowerSeries τ C := fun p => (![a, b, c] : Fin 3 → κ → MvPowerSeries τ C) p.1 p.2
  have he : ∀ p, constantCoeff (e p) = 0 := by
    rintro ⟨j, x⟩
    fin_cases j
    exacts [ha x, hb x, hc x]
  have hei : ∀ p, IntS V (e p) := by
    rintro ⟨j, x⟩
    fin_cases j
    exacts [hai x, hbi x, hci x]
  have hS := hasSubst_of_constantCoeff_zero he
  have s0 : (fun x => subst e (gp C κ (0 : Fin 3) x)) = a := funext fun x => subst_X hS _
  have s1 : (fun x => subst e (gp C κ (1 : Fin 3) x)) = b := funext fun x => subst_X hS _
  have s2 : (fun x => subst e (gp C κ (2 : Fin 3) x)) = c := funext fun x => subst_X hS _
  have g := fun j : Fin 3 => gp_cc (C := C) (κ := κ) j
  constructor
  · have h1 := logInt_subst he hei (mem_logInt.2 ⟨by
      rw [map_sub, map_add (f := _), hAt_cc h (g 0) (g 2), hAt_cc h (g 1) (g 2), hAt_cc h (formalAdd_constantCoeff h (g 0) (g 1)) (g 2)]
      simp, h.ph1⟩)
    rw [subst_sub hS, subst_add hS, subst_hAt (g 0) (g 2) he, subst_hAt (g 1) (g 2) he,
      subst_hAt (formalAdd_constantCoeff h (g 0) (g 1)) (g 2) he, funext (subst_addP h (g 0) (g 1) he), s0, s1, s2] at h1
    exact h1
  · have h1 := logInt_subst he hei (mem_logInt.2 ⟨by
      rw [map_sub, map_add (f := _), hAt_cc h (g 0) (g 1), hAt_cc h (g 0) (g 2), hAt_cc h (g 0) (formalAdd_constantCoeff h (g 1) (g 2))]
      simp, h.ph2⟩)
    rw [subst_sub hS, subst_add hS, subst_hAt (g 0) (g 1) he, subst_hAt (g 0) (g 2) he,
      subst_hAt (g 0) (formalAdd_constantCoeff h (g 1) (g 2)) he, funext (subst_addP h (g 1) (g 2) he), s0, s1, s2] at h1
    exact h1

theorem isEnd_add : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), RLaw X V → ∀ M M' N N' : Matrix κ κ C,
      IsEnd X V M M' → IsEnd X V N N' → IsEnd X V (M + N) (M' + N') := by
  intro C _ V d I κ _ X h M M' N N' hM hN
  haveI := h.charZero
  have hX : ∀ s : κ, constantCoeff (MvPowerSeries.X s : MvPowerSeries κ C) = 0 := fun s => constantCoeff_X s
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [matrixEnd_add h _ _ hX]
    exact formalAdd_integral h (constantCoeff_expMulLog h _ hX) (constantCoeff_expMulLog h _ hX) hM.1 hN.1 i
  · rw [matrixEnd_add h _ _ hX]
    exact formalAdd_integral h (constantCoeff_expMulLog h _ hX) (constantCoeff_expMulLog h _ hX) hM.2.1 hN.2.1 i
  have g := fun j : Fin 2 => gp_cc (C := C) (κ := κ) j
  have gi : ∀ (j : Fin 2) s, IntS V (gp C κ j s) := fun j s => intS_X _
  have ei : ∀ (A : Matrix κ κ C), (∀ i, IntS V (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i)) →
      ∀ (j : Fin 2) s, IntS V (endP X A (gp C κ j) s) := fun A hA j s => by
    rw [← subst_endP_X h A (g j)]
    exact intS_subst (g j) (gi j) (hA s)
  have ad : ∀ A A' : Matrix κ κ C, IsEnd X V A A' →
      hAt X (endP X A (gp C κ (0 : Fin 2))) (gp C κ 1) - hAt X (gp C κ 0) (endP X A' (gp C κ 1)) ∈
        logInt V (Fin 2 × κ) := fun A A' hA =>
    mem_logInt.2 ⟨by
      rw [map_sub, hAt_cc h (constantCoeff_expMulLog h _ (g 0)) (g 1), hAt_cc h (g 0) (constantCoeff_expMulLog h _ (g 1)), sub_zero], hA.2.2⟩
  have d1 := (defects h (constantCoeff_expMulLog h M (g 0)) (constantCoeff_expMulLog h N (g 0)) (g 1) (ei M hM.1 0) (ei N hN.1 0) (gi 1)).1
  have d2 := (defects h (g 0) (constantCoeff_expMulLog h M' (g 1)) (constantCoeff_expMulLog h N' (g 1)) (gi 0) (ei M' hM.2.1 1)
    (ei N' hN.2.1 1)).2
  have key := add_mem (sub_mem (add_mem (ad M M' hM) (ad N N' hN)) d1) d2
  rw [matrixEnd_add h M N (g 0), matrixEnd_add h M' N' (g 1)]
  convert (mem_logInt.1 key).2 using 2
  ring

end GlobalTheory.RowLaw.EndSum
end
end

