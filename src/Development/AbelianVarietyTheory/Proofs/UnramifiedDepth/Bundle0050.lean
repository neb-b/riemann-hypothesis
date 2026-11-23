module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeAdjointEndPairElementaryBlock
section
noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.EndBlock

open MvPowerSeries

variable {C : Type} [Field C]

theorem eq_zero_of_van {τ : Type} {f : MvPowerSeries τ C} (h : Van (∅ : Set τ) f) : f = 0 := by
  ext ν
  rw [h ν (fun _ _ => Set.notMem_empty _)]
  simp

theorem subst_zero' {σ τ : Type} [Finite σ] {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) :
    subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = 0 :=
  eq_zero_of_van (Van.subst Set.univ (fun _ => map_zero _) (fun _ _ ν _ => by simp) (van_univ hf))

section General

variable {d : ℕ} {I : Fin 2 → Type} {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem cc_lin (hlg : ∀ i, constantCoeff (X.lg i) = 0) (M : Matrix κ κ C) {τ : Type}
    {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (x : κ) :
    constantCoeff (∑ y, M x y • subst a (X.lg y)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [constantCoeff_smul, cc_subst ha, hlg, smul_zero]

theorem cc_endP (hlg : ∀ i, constantCoeff (X.lg i) = 0) (hex : ∀ i, constantCoeff (X.ex i) = 0)
    (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (i : κ) :
    constantCoeff (endP X M a i) = 0 := by
  unfold endP
  rw [cc_subst (cc_lin X hlg M ha), hex]

theorem subst_endP (hlg : ∀ i, constantCoeff (X.lg i) = 0) (M : Matrix κ κ C) {τ υ : Type} [Finite τ]
    {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    {b : τ → MvPowerSeries υ C} (hb : ∀ i, constantCoeff (b i) = 0) (i : κ) :
    subst b (endP X M a i) = endP X M (fun k => subst b (a k)) i := by
  have hA := hasSubst_of_constantCoeff_zero ha
  have hB := hasSubst_of_constantCoeff_zero hb
  unfold endP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cc_lin X hlg M ha)) hB]
  congr 1
  funext x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom hB, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_smul, coe_substAlgHom hB, subst_comp_subst_apply hA hB]

theorem cc_pair {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (p : Fin 2 × κ) :
    constantCoeff (if p.1 = 0 then a p.2 else b p.2) = 0 := by
  split_ifs
  exacts [ha _, hb _]

theorem subst_hAt {τ υ : Type} [Finite τ] {a a' : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (ha' : ∀ i, constantCoeff (a' i) = 0)
    {b : τ → MvPowerSeries υ C} (hb : ∀ i, constantCoeff (b i) = 0) :
    subst b (hAt X a a') = hAt X (fun k => subst b (a k)) (fun k => subst b (a' k)) := by
  unfold hAt
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cc_pair ha ha'))
    (hasSubst_of_constantCoeff_zero hb)]
  congr 1
  funext p
  split_ifs <;> rfl

theorem hAt_zero_left (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → coeff e X.h = 0) {τ : Type}
    {b : κ → MvPowerSeries τ C} (hb : ∀ i, constantCoeff (b i) = 0) : hAt X (fun _ => 0) b = 0 := by
  refine eq_zero_of_van (Van.subst {s : Fin 2 × κ | s.1 = 0} (cc_pair (fun _ => map_zero _) hb) ?_ hh)
  intro s hs ν _
  have h0 : s.1 = 0 := hs
  rw [if_pos h0, map_zero]

theorem hAt_zero_right (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → coeff e X.h = 0) {τ : Type}
    {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) : hAt X a (fun _ => 0) = 0 := by
  refine eq_zero_of_van (Van.subst {s : Fin 2 × κ | s.1 = 1} (cc_pair ha (fun _ => map_zero _)) ?_ hh)
  intro s hs ν _
  have h1 : s.1 = 1 := hs
  rw [if_neg (by rw [h1]; decide), map_zero]

theorem cc_hAt (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → coeff e X.h = 0) {τ : Type}
    {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    constantCoeff (hAt X a b) = 0 := by
  unfold hAt
  rw [cc_subst (cc_pair ha hb), ← coeff_zero_eq_constantCoeff_apply]
  exact hh 0 (by simp)

end General

section Square

variable {dd : ℕ}

theorem subst_inCol {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (col : Fin 2) (f : MvPowerSeries (Fin dd) C) :
    subst a (inCol col f) = subst (fun k => a (col, k)) f := by
  have hA := hasSubst_of_constantCoeff_zero ha
  unfold inCol
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hA]
  congr 1
  funext k
  rw [subst_X hA]

variable {d d' : ℕ} {I I' : Fin 2 → Type} (X : RawChart C d I (Fin dd)) (Z : RawChart C d' I' (Fin 2 × Fin dd))

theorem matrixEnd_block (hlg : ∀ x, Z.lg x = inCol x.1 (X.lg x.2)) (hex : ∀ x, Z.ex x = inCol x.1 (X.ex x.2))
    (hlg0 : ∀ i, constantCoeff (X.lg i) = 0) (hex0 : ∀ i, constantCoeff (X.ex i) = 0) (r s : Fin 2)
    (M : Matrix (Fin dd) (Fin dd) C) {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (col : Fin 2) (i : Fin dd) :
    endP Z (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0) a (col, i) =
      if col = r then endP X M (fun k => a (s, k)) i else 0 := by
  have hZ : ∀ x, constantCoeff (Z.lg x) = 0 := fun x => by
    rw [hlg, inCol, cc_subst (fun _ => constantCoeff_X _), hlg0]
  unfold endP
  rw [hex, subst_inCol (cc_lin Z hZ _ ha)]
  split_ifs with hc
  · congr 1
    funext k
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [hlg, subst_inCol ha]
      simp [hc]
    · intro t _ ht
      simp [ht]
    · simp
  · simp only [Matrix.of_apply, hc, false_and, if_false, zero_smul, Finset.sum_const_zero]
    exact subst_zero' (hex0 i)

theorem hAt_square (hh : Z.h = ∑ col, hCol col X.h) {τ : Type} {a b : Fin 2 × Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    hAt Z a b = ∑ col, hAt X (fun k => a (col, k)) (fun k => b (col, k)) := by
  have hA := hasSubst_of_constantCoeff_zero (cc_pair ha hb)
  unfold hAt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hh, ← coe_substAlgHom hA, map_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [coe_substAlgHom hA, hCol,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hA]
  congr 1
  funext q
  rw [subst_X hA]

theorem isEnd_block_raw [CharZero C] (V : VF C) (hlg : ∀ x, Z.lg x = inCol x.1 (X.lg x.2))
    (hex : ∀ x, Z.ex x = inCol x.1 (X.ex x.2)) (hh : Z.h = ∑ col, hCol col X.h)
    (hlg0 : ∀ i, constantCoeff (X.lg i) = 0) (hex0 : ∀ i, constantCoeff (X.ex i) = 0)
    (hax : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0)
    (r s : Fin 2) (M M' : Matrix (Fin dd) (Fin dd) C) (H : IsEnd X V M M') :
    IsEnd Z V (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0)
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = s ∧ y.1 = r then M' x.2 y.2 else 0) := by
  have hint : ∀ (r s : Fin 2) (M : Matrix (Fin dd) (Fin dd) C),
      (∀ i, IntS V (endP X M (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C) i)) →
      ∀ x, IntS V (endP Z (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0)
        (MvPowerSeries.X : Fin 2 × Fin dd → MvPowerSeries (Fin 2 × Fin dd) C) x) := by
    rintro r s M hM ⟨col, i⟩
    rw [matrixEnd_block X Z hlg hex hlg0 hex0 r s M (fun _ => constantCoeff_X _)]
    split_ifs
    · have hb : ∀ k : Fin dd, constantCoeff (MvPowerSeries.X (s, k) : MvPowerSeries (Fin 2 × Fin dd) C) = 0 :=
        fun _ => constantCoeff_X _
      have h1 := intS_subst hb (fun _ => intS_X _) (hM i)
      rw [subst_endP X hlg0 M (fun _ => constantCoeff_X _) hb] at h1
      simpa only [subst_X (hasSubst_of_constantCoeff_zero hb)] using h1
    · exact intS_zero
  refine ⟨hint r s M H.1, hint s r M' H.2.1, ?_⟩
  have hZ : ∀ x, constantCoeff (Z.lg x) = 0 := fun x => by
    rw [hlg, inCol, cc_subst (fun _ => constantCoeff_X _), hlg0]
  have hZ' : ∀ x, constantCoeff (Z.ex x) = 0 := fun x => by
    rw [hex, inCol, cc_subst (fun _ => constantCoeff_X _), hex0]
  have hg : ∀ (κ : Type) (j : Fin 2) (x : κ), constantCoeff (gp C κ j x) = 0 := fun _ _ _ => constantCoeff_X _
  have hb : ∀ q : Fin 2 × Fin dd, constantCoeff (MvPowerSeries.X (q.1, (if q.1 = 0 then s else r, q.2)) :
      MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C) = 0 := fun _ => constantCoeff_X _
  have hB := hasSubst_of_constantCoeff_zero hb
  have h1 := intS_subst hb (fun _ => intS_X _) H.2.2
  rw [GlobalTheory.RowVal.subst_mvExp hb (by
      rw [map_sub, cc_hAt X (hax 0) (cc_endP X hlg0 hex0 M (hg _ 0)) (hg _ 1),
        cc_hAt X (hax 0) (hg _ 0) (cc_endP X hlg0 hex0 M' (hg _ 1)), sub_zero]),
    subst_sub hB, subst_hAt X (cc_endP X hlg0 hex0 M (hg _ 0)) (hg _ 1) hb,
    subst_hAt X (hg _ 0) (cc_endP X hlg0 hex0 M' (hg _ 1)) hb] at h1
  simp only [subst_endP X hlg0 _ (hg _ _) hb] at h1
  simp only [gp, subst_X hB, if_true, one_ne_zero, if_false] at h1
  rw [hAt_square X Z hh (cc_endP Z hZ hZ' _ (hg _ 0)) (hg _ 1),
    hAt_square X Z hh (hg _ 0) (cc_endP Z hZ hZ' _ (hg _ 1)),
    Finset.sum_eq_single r, Finset.sum_eq_single s]
  · simp only [matrixEnd_block X Z hlg hex hlg0 hex0 _ _ _ (hg _ _), if_true]
    exact h1
  · intro t _ ht
    simp only [matrixEnd_block X Z hlg hex hlg0 hex0 _ _ _ (hg _ _), if_neg ht]
    exact hAt_zero_right X (hax 1) (fun _ => hg _ _ _)
  · simp
  · intro t _ ht
    simp only [matrixEnd_block X Z hlg hex hlg0 hex0 _ _ _ (hg _ _), if_neg ht]
    exact hAt_zero_left X (hax 0) (fun _ => hg _ _ _)
  · simp

end Square

theorem isEnd_block : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) (I0 : Type) [Fintype I0] (p : SelfData Y d I0) (d' : ℕ) (I : Fin 2 → Type)
    (X : RawChart C d' I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h →
    ∀ (r s : Fin 2) (M M' : Matrix (Fin dd) (Fin dd) C), IsEnd X V M M' →
    IsEnd (Y.rawSelf p) V
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0)
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = s ∧ y.1 = r then M' x.2 y.2 else 0) := by
  intro C _ _ V O _ _ dd Y d I0 _ p d' I X hlg hex hh r s M M' H
  refine isEnd_block_raw X (Y.rawSelf p) V (fun x => by rw [hlg]; rfl) (fun x => by rw [hex]; rfl)
    (by rw [hh]; rfl) (fun i => ?_) (fun i => ?_) (fun g => ?_) r s M M' H
  · rw [hlg]
    show constantCoeff (un1 (Y.lg i)) = 0
    rw [constantCoeff_uncurry, ← coeff_zero_eq_constantCoeff_apply, Y.lg_lin i 0 (by simp),
      coeff_zero_eq_constantCoeff_apply, constantCoeff_X]
  · rw [hex]
    show constantCoeff (un1 (Y.ex i)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const i
  · rw [hh]
    fin_cases g
    · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
      rfl
    · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
      rfl

end GlobalTheory.RowLaw.EndBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupCurveLogarithmsAddSubgroupResca
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

noncomputable section

namespace GlobalTheory.RowLaw.CvGroup

variable {C : Type} [Field C]

theorem alongCv_congr {σ : Type} [Finite σ] {a b : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, PowerSeries.constantCoeff (b i) = 0) {n : ℕ}
    (hab : ∀ i, ∀ m < n, PowerSeries.coeff m (a i) = PowerSeries.coeff m (b i)) (f : MvPowerSeries σ C)
    (m : ℕ) (hm : m < n) :
    PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv b f) := by
  unfold alongCv
  show MvPowerSeries.coeff (Finsupp.single () m) _ = MvPowerSeries.coeff (Finsupp.single () m) _
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha),
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hb)]
  refine finsum_congr fun e => ?_
  congr 1
  set J : Ideal (PowerSeries C) := Ideal.span {(PowerSeries.X : PowerSeries C) ^ n} with hJ
  have hq : ∀ i, Ideal.Quotient.mk J (a i) = Ideal.Quotient.mk J (b i) := by
    intro i
    rw [Ideal.Quotient.eq, hJ, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hab i k hk, sub_self]
  have hp : Ideal.Quotient.mk J (e.prod fun s k => a s ^ k) = Ideal.Quotient.mk J (e.prod fun s k => b s ^ k) := by
    unfold Finsupp.prod
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, map_pow, hq]
  rw [Ideal.Quotient.eq, hJ, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hp
  have := hp m hm
  rw [map_sub, sub_eq_zero] at this
  exact this

theorem alongCv_low {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) {n : ℕ}
    (hab : ∀ i, ∀ m < n, PowerSeries.coeff m (a i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) (m : ℕ) (hm : m < n) :
    PowerSeries.coeff m (alongCv a f) = 0 := by
  rw [alongCv_congr (b := fun _ => 0) ha (fun _ => map_zero _) (fun i k hk => by rw [hab i k hk, map_zero]) f m hm,
    alongCv_zero hf, map_zero]

theorem constantCoeff_alongCv {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) : PowerSeries.constantCoeff (alongCv a f) = 0 :=
  constantCoeff_subst_zero (τ := Unit) ha hf

theorem alongCv_comp {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) {p : σ → MvPowerSeries σ C}
    (hp : ∀ i, MvPowerSeries.constantCoeff (p i) = 0) (f : MvPowerSeries σ C) :
    alongCv (fun i => alongCv a (p i)) f = alongCv a (MvPowerSeries.subst p f) := by
  unfold alongCv
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hp)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]

theorem alongCv_X {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (i : σ) :
    alongCv a (MvPowerSeries.X i) = a i := by
  unfold alongCv
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) i

variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem lg_const (H : RLaw X V) (i : κ) : MvPowerSeries.constantCoeff (X.lg i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, H.lin i 0 (by simp),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]

theorem ex_lg (H : RLaw X V) {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : κ) :
    alongCv (fun j => alongCv γ (X.lg j)) (X.ex i) = γ i := by
  rw [alongCv_comp hγ (lg_const H), H.exlg, alongCv_X hγ]

theorem lg_ex (H : RLaw X V) {a : κ → PowerSeries C} (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (i : κ) :
    alongCv (fun j => alongCv a (X.ex j)) (X.lg i) = a i := by
  rw [alongCv_comp ha H.exc, H.lgex, alongCv_X ha]

theorem coeff_lg_low (H : RLaw X V) {γ : κ → PowerSeries C} {n : ℕ} (hn : 1 ≤ n)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) (i : κ) :
    PowerSeries.coeff n (alongCv γ (X.lg i)) = PowerSeries.coeff n (γ i) := by
  classical
  have hlg1 : ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun j => by
    rw [H.lin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  rw [coeff_alongCv_low hn hγ (lg_const H i)]
  simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem approx_neg (H : RLaw X V) (hA : X.AddCvSt V) {γ : κ → PowerSeries C} (hγ : IsCv V γ) (n : ℕ) :
    ∃ δ : κ → PowerSeries C, IsCv V δ ∧
      ∀ i, ∀ m < n + 1, PowerSeries.coeff m (alongCv γ (X.lg i) + alongCv δ (X.lg i)) = 0 := by
  induction n with
  | zero =>
    refine ⟨γ, hγ, fun i m hm => ?_⟩
    have : m = 0 := by omega
    rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_add (f := _),
      constantCoeff_alongCv (fun i => (hγ i).1) (lg_const H i), add_zero]
  | succ n ih =>
    obtain ⟨δ, hδ, hlow⟩ := ih
    obtain ⟨s, hs, hL, -⟩ := hA γ δ hγ hδ
    have hs0 : ∀ i, PowerSeries.constantCoeff (s i) = 0 := fun i => (hs i).1
    have hslow : ∀ i, ∀ m < n + 1, PowerSeries.coeff m (s i) = 0 := by
      intro i m hm
      rw [← ex_lg H hs0 i]
      exact alongCv_low (fun j => constantCoeff_alongCv hs0 (lg_const H j))
        (fun j k hk => by rw [hL j]; exact hlow j k hk) (H.exc i) m hm
    have hε : IsCv V fun i => -s i := fun i =>
      ⟨by rw [map_neg, hs0, neg_zero], fun k => by rw [map_neg]; exact ((hs i).2 k).neg⟩
    have hεlow : ∀ i, ∀ m < n + 1, PowerSeries.coeff m (-s i) = 0 := fun i m hm => by
      rw [map_neg, hslow i m hm, neg_zero]
    obtain ⟨δ', hδ', hL', -⟩ := hA δ _ hδ hε
    refine ⟨δ', hδ', fun i m hm => ?_⟩
    rw [hL' i, ← add_assoc, map_add (f := _)]
    by_cases hmn : m < n + 1
    · rw [hlow i m hmn, alongCv_low (fun j => (hε j).1) hεlow (lg_const H i) m hmn, add_zero]
    · have : m = n + 1 := by omega
      rw [this, ← hL i, coeff_lg_low H (by omega) hslow, coeff_lg_low H (by omega) hεlow, map_neg, add_neg_cancel]

theorem exists_neg (H : RLaw X V) (hA : X.AddCvSt V) {γ : κ → PowerSeries C} (hγ : IsCv V γ) :
    ∃ δ : κ → PowerSeries C, IsCv V δ ∧ ∀ i, alongCv δ (X.lg i) = -alongCv γ (X.lg i) := by
  have h0 : ∀ j, PowerSeries.constantCoeff (-alongCv γ (X.lg j)) = 0 := fun j => by
    rw [map_neg, constantCoeff_alongCv (fun i => (hγ i).1) (lg_const H j), neg_zero]
  refine ⟨fun i => alongCv (fun j => -alongCv γ (X.lg j)) (X.ex i), fun i => ⟨constantCoeff_alongCv h0 (H.exc i), fun n => ?_⟩,
    lg_ex H h0⟩
  obtain ⟨δ, hδ, hlow⟩ := approx_neg H hA hγ n
  have hδ0 : ∀ i, PowerSeries.constantCoeff (δ i) = 0 := fun i => (hδ i).1
  rw [alongCv_congr (b := fun j => alongCv δ (X.lg j)) h0 (fun j => constantCoeff_alongCv hδ0 (lg_const H j))
    (n := n + 1) (fun j m hm => by
      have := hlow j m hm
      rw [map_add (f := _)] at this
      rw [map_neg]
      exact neg_eq_of_add_eq_zero_right this) _ n (Nat.lt_succ_self n), ex_lg H hδ0]
  exact (hδ i).2 n

theorem sg_const (H : RLaw X V) (v : κ → C) : MvPowerSeries.constantCoeff (X.sg v) = 0 :=
  X.constantCoeff_sg (H.axes 0) v

theorem isCv_zero {σ : Type} : IsCv V fun _ : σ => (0 : PowerSeries C) := fun _ =>
  ⟨map_zero _, fun n => by rw [map_zero]; exact VF.Ge.zero 0⟩

theorem zero_mem (H : RLaw X V) (g : Fin 2) : 0 ∈ Cv X V g :=
  ⟨fun _ => 0, fun _ => 0, isCv_zero, isCv_zero, fun i => alongCv_zero (lg_const H i), fun q => by
    rw [alongCv_zero (sg_const H _), sub_zero]; rfl⟩

theorem add_mem (H : RLaw X V) (hA : X.AddCvSt V) (g : Fin 2) :
    ∀ a ∈ Cv X V g, ∀ b ∈ Cv X V g, a + b ∈ Cv X V g := by
  rintro a ⟨γ, lam, hγ, hlam, h1, h2⟩ b ⟨γ', lam', hγ', hlam', h1', h2'⟩
  obtain ⟨γ'', hγ'', hL, hS⟩ := hA γ γ' hγ hγ'
  refine ⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (H.uint (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_add (f := _), map_add (f := _), (hlam q).1, (hlam' q).1, c0]
      simp
    · rw [map_add (f := _), map_add (f := _)]
      exact (((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)
  · intro i
    rw [hL i, h1 i, h1' i]
    rfl
  · intro q
    show a.2 q + b.2 q = _
    rw [h2 q, h2' q]
    dsimp only
    abel

theorem neg_mem (H : RLaw X V) (hA : X.AddCvSt V) (g : Fin 2) : ∀ a ∈ Cv X V g, -a ∈ Cv X V g := by
  rintro a ⟨γ, lam, hγ, hlam, h1, h2⟩
  obtain ⟨δ, hδ, hneg⟩ := exists_neg H hA hγ
  obtain ⟨s, hs, hL, hS⟩ := hA γ δ hγ hδ
  have hs0 : s = fun _ => 0 := by
    funext i
    rw [← ex_lg H (fun j => (hs j).1) i]
    have : (fun j => alongCv s (X.lg j)) = fun _ => 0 := by
      funext j
      rw [hL j, hneg j, add_neg_cancel]
    rw [this, alongCv_zero (H.exc i)]
  refine ⟨δ, fun q => -lam q - (alongCv s (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv δ (X.sg (X.u (1 - g) q))), hδ, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (H.uint (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_sub, map_neg, (hlam q).1, c0]
      simp
    · rw [map_sub, map_neg]
      exact ((hlam q).2 n).neg.sub (cI n)
  · intro i
    rw [hneg i, h1 i]
    rfl
  · intro q
    show -a.2 q = _
    dsimp only
    rw [h2 q, hs0, alongCv_zero (sg_const H _)]
    abel

theorem rescale_mem (g : Fin 2) (s : C) (hs : V.Ge 0 s) : ∀ a ∈ Cv X V g,
    ((fun i => PowerSeries.rescale s (a.1 i), fun q => PowerSeries.rescale s (a.2 q)) :
      ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  rintro a ⟨γ, lam, hγ, hlam, h1, h2⟩
  have hτ : PowerSeries.constantCoeff (s • (PowerSeries.X : PowerSeries C)) = 0 := by simp
  have hcv : ∀ {σ : Type} (δ : σ → PowerSeries C), IsCv V δ → IsCv V fun i => PowerSeries.rescale s (δ i) := by
    intro σ δ hδ i
    refine ⟨?_, fun n => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ i).1, mul_zero]
    · rw [PowerSeries.coeff_rescale]
      exact (hs.pow n).mul_int ((hδ i).2 n)
  have hal : ∀ f, alongCv (fun i => PowerSeries.rescale s (γ i)) f = PowerSeries.rescale s (alongCv γ f) := by
    intro f
    simp only [PowerSeries.rescale_eq_subst]
    exact alongCv_repar (fun i => (hγ i).1) hτ f
  refine ⟨fun i => PowerSeries.rescale s (γ i), fun q => PowerSeries.rescale s (lam q), hcv γ hγ, hcv lam hlam, ?_, ?_⟩
  · intro i
    rw [hal, h1 i]
  · intro q
    show PowerSeries.rescale s (a.2 q) = _
    rw [hal, h2 q, map_sub]

end GlobalTheory.RowLaw.CvGroup

theorem GlobalTheory.RowLaw.cv_group : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, (0 ∈ Cv X V g) ∧ (∀ a ∈ Cv X V g, ∀ b ∈ Cv X V g, a + b ∈ Cv X V g) ∧ (∀ a ∈ Cv X V g, -a ∈ Cv X V g) ∧ (∀ s : C, V.Ge 0 s → ∀ a ∈ Cv X V g, ((fun i => PowerSeries.rescale s (a.1 i), fun q => PowerSeries.rescale s (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g) := by
  intro C _ V d _ I _ κ _ X H g
  have hA := GlobalTheory.T.addCurveStable_of_integralGaugedFormalGroupLaw C V d I κ X H
  exact ⟨CvGroup.zero_mem H g, CvGroup.add_mem H hA g, CvGroup.neg_mem H hA g, fun s hs => CvGroup.rescale_mem g s hs⟩
end
end

