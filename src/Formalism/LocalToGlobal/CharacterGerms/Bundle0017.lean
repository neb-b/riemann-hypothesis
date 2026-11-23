module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0014
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables
public import Formalism.DropLevelBounds.ThBounds
public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.Numbers

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePFBMapSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.MapFB

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}

def mpt {n : ℕ} (a : Pt R n d) : Pt S n d := fun i => MvPowerSeries.map φ (a i)

private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem map_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : MvPowerSeries.map φ (ev a f) = ev (fun j => mpt φ (a j)) (MvPowerSeries.map φ f) := by
  unfold ev
  exact MvPowerSeries.map_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2)) f

theorem map_ev1 {n : ℕ} (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (f : PS R 1 d) :
    MvPowerSeries.map φ (ev ![a] f) = ev ![mpt φ a] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a] (by intro j i; fin_cases j; simp [ha]) f]
  congr 1
  funext j
  fin_cases j
  rfl

theorem map_ev2 {n : ℕ} (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (f : PS R 2 d) :
    MvPowerSeries.map φ (ev ![a, b] f) = ev ![mpt φ a, mpt φ b] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) f]
  congr 1
  funext j
  fin_cases j <;> rfl

omit [CommRing S] in
theorem cc_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d)
    (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 := by
  unfold ev
  exact (cc_subst_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f).trans hf

omit [CommRing S] in
@[simp] theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp [pt]


omit [CommRing S] in
@[simp] theorem cc_comp1 {n : ℕ} (ψ : Pt R 1 d) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) :
    constantCoeff (comp1 ψ a i) = 0 := cc_ev ![a] (by intro j i; fin_cases j; simp [ha]) (ψ i) (hψ i)

omit [CommRing S] in
theorem zc_zero {n : ℕ} : ∀ i : Fin d, constantCoeff ((0 : Pt R n d) i) = 0 := fun i => by simp

@[simp] theorem mpt_pt {n : ℕ} (j : Fin n) : mpt φ (pt R d j) = pt S d j := by
  funext i
  simp [mpt, pt]

@[simp] theorem mpt_zero {n : ℕ} : mpt φ (0 : Pt R n d) = 0 := by
  funext i
  simp [mpt]

theorem mpt_comp1 {n : ℕ} (ψ : Pt R 1 d) (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) :
    mpt φ (comp1 ψ a) = comp1 (mpt φ ψ) (mpt φ a) := by
  funext i
  exact map_ev1 φ a ha (ψ i)

end Formalism.L2.FormalSeriesBounds.MapFB

namespace Formalism.L2.FormalSeriesBounds

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmall
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem lg_const (Y : FBChart C V O dd) (i : Fin dd) : constantCoeff (Y.lg i) = 0 := by
  have h := Y.lg_lin i 0 (by simp)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  simp [MvPowerSeries.coeff_X]
  exact (Finsupp.single_ne_zero.2 one_ne_zero).symm

theorem germEval_oneStandardPoint_self (f : PS C 1 dd) : ev (n := 1) ![pt C dd 0] f = f := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  have : (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) p.1 p.2) = X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k
    rfl
  rw [this, subst_self]
  rfl

theorem formalGroupLaw_ev_x_zero (Y : FBChart C V O dd) {n : ℕ} (A : Pt C n dd) (hA : ∀ j, constantCoeff (A j) = 0) (i : Fin dd) :
    ev (![A, 0] : Fin 2 → Pt C n dd) (Y.B.G.F i) = A i := by
  have hZ : Z0 (![A, 0] : Fin 2 → Pt C n dd) := z0_p0 A hA
  conv_lhs => rw [← Y.B.G.comm i]
  rw [ev_ev (z0_pp 1 0) hZ]
  have e1 : (fun k j => ev (![A, 0] : Fin 2 → Pt C n dd) ((![pt C dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) k j)) =
      ![0, A] := by
    funext k j; fin_cases k
    · exact ev_X hZ 1 j
    · exact ev_X hZ 0 j
  rw [e1]
  have hB : Z0 (![A] : Fin 1 → Pt C n dd) := z0_1 _ hA
  have hU : Z0 (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) := by
    intro k j; fin_cases k
    · simp
    · exact z0_pt 0 j
  have e2 : (![0, A] : Fin 2 → Pt C n dd) =
      fun k j => ev (![A] : Fin 1 → Pt C n dd) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) k j) := by
    funext k j; fin_cases k
    · exact (ev_zero hB).symm
    · exact (ev_X hB 0 j).symm
  rw [e2, ← ev_ev hU hB, Y.B.G.unit i, ev_X hB]
  rfl

theorem lg_addOf (Y : FBChart C V O dd) {n : ℕ} (P Q : Pt C n dd) (hP : ∀ j, constantCoeff (P j) = 0)
    (hQ : ∀ j, constantCoeff (Q j) = 0) (i : Fin dd) :
    ev ![addOf Y.B.G.F P Q] (Y.lg i) = ev ![P] (Y.lg i) + ev ![Q] (Y.lg i) := by
  have hPQ : Z0 (![P, Q] : Fin 2 → Pt C n dd) := constant_zero_two_points P Q hP hQ
  have h := congrArg (ev (![P, Q] : Fin 2 → Pt C n dd)) (Y.lg_add i)
  rw [ev_add hPQ] at h
  have hA : Z0 (![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)] : Fin 1 → Pt C 2 dd) :=
    z0_1 _ (fun j => const_addOf Y 0 1 j)
  rw [ev_ev hA hPQ, ev_ev (z0_1 _ (z0_pt 0)) hPQ, ev_ev (z0_1 _ (z0_pt 1)) hPQ] at h
  have e1 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd)
      ((![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)] : Fin 1 → Pt C 2 dd) k j)) =
      ![addOf Y.B.G.F P Q] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    show ev (![P, Q] : Fin 2 → Pt C n dd) (ev ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] (Y.B.G.F j)) =
      ev ![P, Q] (Y.B.G.F j)
    rw [ev_ev (z0_pp 0 1) hPQ]
    congr 1
    funext k' j'
    fin_cases k'
    · exact ev_X hPQ 0 j'
    · exact ev_X hPQ 1 j'
  have e2 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd) ((![pt C (n := 2) dd 0] : Fin 1 → Pt C 2 dd) k j)) = ![P] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    exact ev_X hPQ 0 j
  have e3 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd) ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k j)) = ![Q] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    exact ev_X hPQ 1 j
  rw [e1, e2, e3] at h
  exact h

theorem lg_act_nat (Y : FBChart C V O dd) (k : ℕ) (i : Fin dd) :
    ev ![Y.B.A.act (k : O)] (Y.lg i) = MvPowerSeries.C (k : C) * Y.lg i := by
  have act0 := Y.B.A.const
  induction k with
  | zero =>
    have h0 : Y.B.A.act ((0 : ℕ) : O) = addOf Y.B.G.F (Y.B.A.act ((0 : ℕ) : O)) (Y.B.A.act ((0 : ℕ) : O)) := by
      have := Y.B.A.add_act 0 0
      rw [add_zero] at this
      rw [Nat.cast_zero]; exact this
    have h := lg_addOf Y (Y.B.A.act ((0 : ℕ) : O)) (Y.B.A.act ((0 : ℕ) : O)) (act0 _) (act0 _) i
    rw [← h0] at h
    simp only [Nat.cast_zero, map_zero, zero_mul] at h ⊢
    linear_combination -h
  | succ k ih =>
    have h1 : Y.B.A.act ((k + 1 : ℕ) : O) = addOf Y.B.G.F (Y.B.A.act (k : O)) (pt C dd 0) := by
      rw [Nat.cast_succ, Y.B.A.add_act, Y.B.A.one_act]
    rw [h1, lg_addOf Y _ _ (act0 _) (z0_pt 0) i, ih, germEval_oneStandardPoint_self, Nat.cast_succ, map_add (f := _), map_one]
    ring

theorem ex_lg_comp (Y : FBChart C V O dd) {n : ℕ} (φ : Pt C n dd) (hφ : ∀ j, constantCoeff (φ j) = 0) (i : Fin dd) :
    ev ![fun j => ev ![φ] (Y.lg j)] (Y.ex i) = φ i := by
  have hφ1 : Z0 (![φ] : Fin 1 → Pt C n dd) := z0_1 φ hφ
  have hlg : Z0 (![Y.lg] : Fin 1 → Pt C 1 dd) := z0_1 _ (lg_const Y)
  have e1 : (![fun j => ev ![φ] (Y.lg j)] : Fin 1 → Pt C n dd) =
      fun k j => ev (![φ] : Fin 1 → Pt C n dd) ((![Y.lg] : Fin 1 → Pt C 1 dd) k j) := by
    funext k j; rw [Fin.fin_one_eq_zero k]; rfl
  rw [e1, ← ev_ev hlg hφ1]
  have e2 : ev (![Y.lg] : Fin 1 → Pt C 1 dd) (Y.ex i) = pt C dd 0 i := congrFun Y.ex_lg i
  rw [e2]
  exact ev_X hφ1 0 i

end Main

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}

structure LabS (E : Type) [Field E] (C : Type) (Orb : Type) (d : ℕ) where
  tau : Orb → ZMod d → (E →+* ℂ)
  hd : ZMod d
  gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C
  n : ℕ
  j : ℕ
  j' : ℕ
  big : Orb → Fin 2 → ZMod d → Prop

abbrev LabS.II {Orb : Type} {d : ℕ} (lab : LabS E C Orb d) (Dw : Datum H) (o : Orb) : Type :=
  Σ a : ZMod d, Fin (Dw.mult (lab.tau o a))

section Pairs

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

def selfLieBasisVector (C3 : IntChart T io y) (ι : T.Fr →+* C) (lab : LabS E C Orb d) (o : Orb) (x : lab.II Dw o) :
    Fin (chD C3.ch) → C := fun i => ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)

structure LabSArith (V : VF C) (io : c.F →+* T.Fr) (ι : T.Fr →+* C) (lab : LabS E C Orb d) : Prop where
  inj : Function.Injective fun x : Orb × ZMod d => lab.tau x.1 x.2
  hd_ne : lab.hd ≠ 0
  hd_two : lab.hd + lab.hd = 0
  conj : ∀ o a, ComplexEmbedding.conjugate (lab.tau o a) = lab.tau o (a + lab.hd)
  frob : ∀ o a x, V.MM (emA3 io ι (lab.tau o (a + 1)) x - emA3 io ι (lab.tau o a) x ^ V.l)
  sep : ∀ x x' : Orb × ZMod d, x ≠ x' →
    ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau x.1 x.2) a - emA3 io ι (lab.tau x'.1 x'.2) a) = 0
  unr : ∀ o, ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (lab.tau o a) ε - 1)) ∧
    ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (lab.tau o a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y
  gm_lim : ∀ o (N : ℕ), ∃ M : Matrix (Fin 2) (Fin 2) (𝓞 E), ∀ a r s,
    V.Ge N (lab.gm o a r s - emA3 io ι (lab.tau o a) (M r s))
  gm_hyp : ∀ o a (s s' : Fin 2), ∑ r, lab.gm o (a + lab.hd) r s * lab.gm o a r s' = if s = s' then 0 else 1

structure LabSGeo (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch)) (lab : LabS E C Orb d) :
    Prop where
  em_int : ∀ o a x, V.Ge 0 (emA3 io ι (lab.tau o a) x)
  em_conj : ∀ o a x, emA3 io ι (lab.tau o a) (star x) = emA3 io ι (lab.tau o (a + lab.hd)) x
  e_int : ∀ o x i, V.Ge 0 (selfLieBasisVector C3 ι lab o x i)
  e_eig : ∀ o (x : lab.II Dw o) a, linAct (Y.B.A.act a) (selfLieBasisVector C3 ι lab o x) =
    emA3 io ι (lab.tau o x.1) a • selfLieBasisVector C3 ι lab o x
  e_sat : ∀ o, ∃ w : Fin (chD C3.ch) → lab.II Dw o → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o, ∑ x, selfLieBasisVector C3 ι lab o q x * w x q' = if q = q' then 1 else 0
  e_full : ∀ o a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o a) x • v) →
    ∃ b : lab.II Dw o → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • selfLieBasisVector C3 ι lab o q

def selfOfLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (o : Orb) : SelfData Y d (lab.II Dw o) where
  em := fun a => emA3 io ι (lab.tau o a)
  em_int := hg.em_int o
  em_frob := ha.frob o
  em_sep := fun a a' h => ha.sep (o, a) (o, a') (fun e => h (Prod.mk.inj e).2)
  em_unr := ha.unr o
  hd := lab.hd
  hd_ne := ha.hd_ne
  hd_two := ha.hd_two
  em_conj := hg.em_conj o
  e := selfLieBasisVector C3 ι lab o
  ty0 := fun x => x.1
  e_int := hg.e_int o
  e_eig := hg.e_eig o
  e_sat := by
    obtain ⟨w, h1, h2⟩ := hg.e_sat o
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  e_full := hg.e_full o
  gm := lab.gm o
  gm_lim := ha.gm_lim o
  gm_hyp := ha.gm_hyp o
  n := lab.n
  j := lab.j
  j' := lab.j'
  big := lab.big o

theorem selfSep_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) : SelfSep Y (selfOfLab ha hg) := by
  intro x x' hne
  exact ha.sep x x' hne

def LabS.RankOK (lab : LabS E C Orb d) (Dw : Datum H) : Prop :=
  ∀ o, (∀ g a, lab.big o (1 - g) a ↔ ¬ lab.big o g a) ∧
    (∀ a, lab.big o 0 a → Dw.mult (lab.tau o a) = lab.n + lab.j) ∧
    (∀ a, ¬ lab.big o 0 a → Dw.mult (lab.tau o a) = lab.j') ∧
    (∀ a, lab.big o 1 a → Dw.mult (lab.tau o (a - lab.hd)) = lab.n + lab.j) ∧
    (∀ a, ¬ lab.big o 1 a → Dw.mult (lab.tau o (a - lab.hd)) = lab.j')

theorem card_sigma_shift (m : ZMod d → ℕ) (h a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 + h = a).card = m (a - h) := by
  have e1 : (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 + h = a) =
      (Finset.univ.filter fun b : ZMod d => b + h = a).sigma fun b => Finset.univ := by
    ext ⟨b, i⟩
    simp
  have e2 : (Finset.univ.filter fun b : ZMod d => b + h = a) = {a - h} := by
    ext b
    simp [eq_sub_iff_add_eq]
  rw [e1, Finset.card_sigma, e2, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin]

theorem rankHyp_ofLabS {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.rawSelf (selfOfLab ha hg o)).RankHyp := by
  refine { big_compl := (hr o).1, rk_big := ?_, rk_small := ?_ }
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab]
      convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.1 a hb) using 2
      exact Finset.filter_congr (fun _ _ => Iff.rfl)
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
      exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.1 a hb)
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab]
      convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.2.1 a hb) using 2
      exact Finset.filter_congr (fun _ _ => Iff.rfl)
    · intro a hb
      simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
      exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.2 a hb)

end Pairs

section Named

variable (Xo c)

def GmExSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → V.l ≠ 2 →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (tau : Orb → ZMod d → (E →+* ℂ)) (hd : ZMod d), hd ≠ 0 → hd + hd = 0 →
    (∀ o a, ComplexEmbedding.conjugate (tau o a) = tau o (a + hd)) →
    (∀ o a x, V.MM (emA3 io ι (tau o (a + 1)) x - emA3 io ι (tau o a) x ^ V.l)) →
    (∀ x x' : Orb × ZMod d, x ≠ x' → ∃ a : 𝓞 E, V.v (emA3 io ι (tau x.1 x.2) a - emA3 io ι (tau x'.1 x'.2) a) = 0) →
    ∃ gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C,
      (∀ o (N : ℕ), ∃ M : Matrix (Fin 2) (Fin 2) (𝓞 E), ∀ a r s, V.Ge N (gm o a r s - emA3 io ι (tau o a) (M r s))) ∧
      ∀ o a (s s' : Fin 2), ∑ r, gm o (a + hd) r s * gm o a r s' = if s = s' then 0 else 1

def AllSelfConjugateCharts (Φ : ∀ (C : Type) [Field C] (_V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (dd : ℕ),
    RawChart C d I (Fin 2 × Fin dd) → Prop) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, Φ C V d (fun _ => lab.II Dw o) (chD C3.ch) (Y.rawSelf (selfOfLab ha hg o))

def RankMaximalSelfCharts : Prop := AllSelfConjugateCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition Hc

end Named

section Top

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

end Top

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.BasicNotions

def i0 (k l : ℕ) : ℕ := sInf {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i}

def ThlEq : Prop := ∀ k l : ℕ, 1 ≤ k → 2 ≤ l →
  Odd (i0 k l) ∧ 3 ≤ i0 k l ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i0 k l ∧
    thl k l = ((l : ℝ) ^ i0 k l)⁻¹

def LevelBound : Prop := ∀ k l : ℕ, 1 ≤ k → 5 ≤ l → ((i0 k l : ℝ) - 1) ≤ 2 + 2 * Real.log k

structure Plan (l d : ℕ) [NeZero d] (W : ZMod d → ℕ) where
  y : ZMod d → ℕ → ℕ
  u : ZMod d → ℕ
  supp : ∀ a i, i ∉ oddLevels d → y a i = 0
  bal : ∀ a, W a = (∑ i ∈ oddLevels d, l ^ i * y a i) +
    (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) + u a

def Plan.triv (l d : ℕ) [NeZero d] (W : ZMod d → ℕ) : Plan l d W where
  y := fun _ _ => 0
  u := W
  supp := fun _ _ _ => rfl
  bal := fun a => by simp

def blockBd (l n m i y : ℕ) : ℝ :=
  if y = 0 then 0 else bdP l i n n y + ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)

def chBd (l n m u : ℕ) : ℝ := (u : ℝ) * (n * gam l + m / ((l : ℝ) - 1))

def Plan.bound {l d : ℕ} [NeZero d] {W : ZMod d → ℕ} (p : Plan l d W) (n m : ℕ) : ℝ :=
  (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (p.y a i)) + ∑ a, chBd l n m (p.u a)

def Windows (S : ℕ) (G : Set ℕ) : Prop := 0 ∈ G ∧ ∀ Y0 : ℕ, ∃ y ∈ G, Y0 ≤ y ∧ y < Y0 + S

def IsReps (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) : Prop :=
  ∀ z' : RPl N.R, ∃! p : RPl N.R × ZMod (N.ordP l), p.1 ∈ Z ∧ N.pos l p.1 p.2.val = z'

def alongOrb {X : Type} (N : NumDatum) (l : ℕ) (z : RPl N.R) (W : RPl N.R → X) : ZMod (N.ordP l) → X :=
  fun s => W (N.pos l z s.val)

def FInertReps : Prop :=
  ∀ (N : NumDatum) (j l : ℕ) (Z : Finset (RPl N.R)), IsReps N l Z →
    (N.cls l = PrimeClass.inertClass ∨ N.cls l = PrimeClass.signal) →
    ¬ (N.cls l = PrimeClass.inertClass ∧ N.hP l = 0) →
    N.FInert j l = ∑ z ∈ Z, Fnum l (N.ordP l)
        (fun s => ((N.R.k : ℝ) - 1) * alongOrb N l z (N.w j) s) ∧
      (l ≠ N.g 0 → l ≠ N.g 1 → (l : ℝ) ≤ N.sc.X'' N.R.n → N.FjP j l = N.FInert j l)

def LemmaFe : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → 2 ≤ d → Even d → ∀ D : ZMod d → ℝ, (∀ a, 0 ≤ D a) →
    (∀ a a', D a' ≤ l * D a) → Fnum l d D = rho l * ∑ a, D a

end Formalism.L2.FormalSeriesBounds
end
end

