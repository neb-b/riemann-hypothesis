module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0024
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0025
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0021

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.FirstVanishingAt
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Defs

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.FirstVanishingAt (Y : FBChart C V O dd) (u : Fin dd → C) : Prop :=
  ∀ k : Fin dd,
    V.MM (∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k) * u i ^ V.l)

def FBChart.aLin (Y : FBChart C V O dd) (u v : Fin dd → C) : C :=
  ∑ j, v j * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.aOf u)

def FBChart.LgLin (Y : FBChart C V O dd) (γ : Fin dd → PowerSeries C) (U : Fin dd → C) : Prop :=
  ∀ i, Agr (V.l ^ 2) (alongCv γ (un1 (Y.lg i))) (U i • (MvPowerSeries.X () : PowerSeries C))

end Defs

def FirstVanishingCore : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (γ : Fin dd → PowerSeries C) (U : Fin dd → C),
    IsCv V γ → Y.LgLin γ U → Y.FirstVanishingAt U

def FunEqCoreSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (u : Fin dd → C), (∀ i, V.Ge 0 (u i)) → Y.FirstVanishingAt u →
    ∀ μ, V.MM (MvPowerSeries.coeff μ (cobd Y.B.G.F (Y.aOf u) - frobTw V.l (Y.chartLinearTerm u)))

def CurveLinearTermCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (γ : Fin dd → PowerSeries C) (U : Fin dd → C),
    IsCv V γ → Y.LgLin γ U → ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (un1 (Y.sgP v))) - Y.aLin U v)

def ALinAdjSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (e eb : Pt C 1 dd),
    (∀ i, IntS V (e i)) → (∀ i, IntS V (eb i)) →
    (∀ i, MvPowerSeries.constantCoeff (e i) = 0) → (∀ i, MvPowerSeries.constantCoeff (eb i) = 0) →
    comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)) →
    IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h)) →
    ∀ u : Fin dd → C, (∀ i, V.Ge 0 (u i)) → Y.FirstVanishingAt u → ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    V.MM (Y.aLin (linAct e u) v - Y.aLin u (linAct eb v))

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.IntSProd
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

section Inv

variable {C : Type} [Field C] {V : VF C} {σ : Type}

theorem inv_int {c : C} (hc : V.v c = 0) : V.Ge 0 c⁻¹ := by
  simp [VF.Ge, AddValuation.map_inv, hc]

theorem intInv {U : MvPowerSeries σ C} (hU : IntS V U) (h0 : V.v (MvPowerSeries.constantCoeff U) = 0) :
    ∃ U' : MvPowerSeries σ C, IntS V U' ∧ U' * U = 1 := by
  have hc0 : MvPowerSeries.constantCoeff U ≠ 0 := by
    intro h
    simp [h] at h0
  refine ⟨U⁻¹, ?_, MvPowerSeries.inv_mul_cancel _ hc0⟩
  have hge0 : V.Ge 0 (0 : C) := by simp [VF.Ge]
  have hmul : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a * b) := by
    intro a b ha hb
    unfold VF.Ge at *
    rw [AddValuation.map_mul]
    simpa using add_le_add ha hb
  have hadd : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a + b) :=
    fun a b ha hb => le_trans (le_min ha hb) (V.v.map_add a b)
  have hneg : ∀ a : C, V.Ge 0 a → V.Ge 0 (-a) := by
    intro a ha
    unfold VF.Ge at *
    rwa [AddValuation.map_neg]
  intro μ
  induction μ using WellFoundedLT.induction with
  | _ μ ih =>
    rw [MvPowerSeries.coeff_inv]
    split_ifs with hμ
    · exact inv_int h0
    · refine hmul _ _ (hneg _ (inv_int h0)) ?_
      refine Finset.sum_induction _ (V.Ge 0) hadd hge0 (fun x _ => ?_)
      split_ifs with hlt
      · exact hmul _ _ (hU x.1) (ih x.2 hlt)
      · exact hge0

theorem IntS_prod {ι : Type} (s : Finset ι) {F : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS V (F i)) :
    IntS V (∏ i ∈ s, F i) := by
  classical
  have hge : ∀ c : C, (c = 0 ∨ c = 1) → V.Ge 0 c := by
    rintro c (rfl | rfl)
    · simp [VF.Ge]
    · simp [VF.Ge]
  have hone : IntS V (1 : MvPowerSeries σ C) := by
    intro μ
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · exact hge 1 (Or.inr rfl)
    · exact hge 0 (Or.inl rfl)
  have hmul : ∀ F G : MvPowerSeries σ C, IntS V F → IntS V G → IntS V (F * G) := by
    intro F G hF hG μ
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_induction _ (V.Ge 0) (fun a b ha hb => ?_) (hge 0 (Or.inl rfl)) (fun q _ => ?_)
    · exact le_trans (le_min ha hb) (V.v.map_add a b)
    · have h1 := add_le_add (hF q.1) (hG q.2)
      unfold VF.Ge
      rw [AddValuation.map_mul]
      simpa using h1
  induction s using Finset.induction_on with
  | empty => simpa using hone
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hmul _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IntS_X (s : σ) : IntS V (MvPowerSeries.X s : MvPowerSeries σ C) := by
  intro μ
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · simp [VF.Ge]
  · simp [VF.Ge]

end Inv

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

private theorem cc_ev_lemma {m n : ℕ} (a : Fin m → Pt C n dd)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS C m dd) :
    MvPowerSeries.constantCoeff (ev a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin dd => a p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => (a s.1 s.2) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (by rw [map_pow, ha, zero_pow hs'])
    rw [h0, smul_zero]

theorem cc_h (Y : FBChart C V O dd) : MvPowerSeries.constantCoeff Y.h = 0 := by
  have hax := Y.gauge.ax0
  have e : MvPowerSeries.constantCoeff (ev (n := 1) ![0, pt C dd 0] Y.h) = MvPowerSeries.constantCoeff Y.h :=
    cc_ev_lemma _ (fun j i => by fin_cases j <;> simp [pt]) _
  rw [← e, hax, map_zero]

theorem cc_hL (Y : FBChart C V O dd) : MvPowerSeries.constantCoeff (Y.B.hL C Y.h Y.w0) = 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.hL
  rw [cc_ev_lemma _ ?_ _]
  · exact cc_h Y
  · intro j i
    fin_cases j
    · simp [pt]
    · show MvPowerSeries.constantCoeff (comp1 (Y.B.actK C Y.w0) (pt C dd 0) i) = 0
      simp only [comp1]
      rw [cc_ev_lemma _ (fun j i => by rw [Fin.fin_one_eq_zero j]; simp [pt]) _]
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.actK, MvPowerSeries.constantCoeff_map, Y.B.A.const]

end VP

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieMemCDeg
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

theorem trueT_iff (g : Fin 2) (t' s : ZMod 2) : ((if g = 0 then t' else t' + 1) = s) ↔ t' = trueT g s := by
  unfold trueT
  revert g t' s
  decide

theorem trueT_one : ∀ t : ZMod 2, trueT 1 (t + 1) = t := by
  unfold trueT
  decide

theorem SelfConjugatePlaceSetting.rkF_eq {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
    {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
    {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}
    (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) :
    (X o).rkF g s = r (tau o (trueT g s)) := by
  unfold RowData.rkF
  have e : (Finset.univ.filter fun c : IIs r tau o => ((X o).G g).ty (Sum.inl c) = s) =
      Finset.univ.map (Function.Embedding.sigmaMk (β := fun t => Fin (r (tau o t))) (trueT g s)) := by
    ext ⟨t', c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.sigmaMk_apply, H.hty]
    rw [trueT_iff]
    constructor
    · rintro rfl
      exact ⟨c, rfl⟩
    · rintro ⟨c', h⟩
      exact (congrArg Sigma.fst h).symm
  rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]

open WeightHomogeneousMinors WeightHomogeneousLetters in
theorem isotropic_to_std_subst_degree : IsotropicToStdSubstLineDegree := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc m hm σ c0
  rw [← weight_wLet]
  suffices hWH : IsWeightedHomogeneous (wLet r n σ c0) (subG r tau gm plc (blkProd X F N L pl)) (a σ c0) from
    hWH (MvPolynomial.mem_support_iff.1 hm)
  unfold subG
  refine isWH_aeval (w' := fun x => if (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0) _
    (fun x => ?_) ?_
  · apply IsWeightedHomogeneous.sum
    intro col _
    have h := (isWeightedHomogeneous_C (wLet r n σ c0) (gm x.2.1 x.2.2.2.1 col x.2.2.1)).mul
      (isWeightedHomogeneous_X (R := C) (wLet r n σ c0)
        (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2, plc (x.1, col)⟩ : Letter T r n))
    rw [zero_add, wLet_mk] at h
    exact h
  · by_cases hσ : ∃ o t, tau o t = σ
    · obtain ⟨o0, t0, rfl⟩ := hσ
      have keyEq : ∀ o t (c : Fin (r (tau o t))),
          ((⟨tau o t, c⟩ : Σ σ, Fin (r σ)) = ⟨tau o0 t0, c0⟩) ↔ (o = o0 ∧ t = t0 ∧ (c : ℕ) = c0) := by
        intro o t c
        constructor
        · intro h
          have h1 : tau o t = tau o0 t0 := congrArg Sigma.fst h
          have h2 := H.inj (a₁ := (o, t)) (a₂ := (o0, t0)) h1
          simp only [Prod.mk.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          refine ⟨rfl, rfl, ?_⟩
          rw [eq_of_heq (Sigma.mk.inj h).2]
        · rintro ⟨rfl, rfl, hc⟩
          rw [Fin.ext hc]
      have hT1 : trueT 1 (t0 + 1) = t0 := trueT_one t0
      have hR0 : (X o0).rkF 0 t0 = r (tau o0 t0) := H.rkF_eq o0 0 t0
      have hR1 : (X o0).rkF 1 (t0 + 1) = r (tau o0 t0) := by rw [H.rkF_eq o0 1 (t0 + 1), hT1]
      have hD : a (tau o0 t0) c0 = ∑ o, (if o = o0 then ∑ i : Fin (L o).length,
          ((∑ k ∈ Finset.Icc ((c0 : ℕ) + 1) ((X o).rkF 0 t0), (blkAt L o i).wt (X o) 0 t0 k) +
            ∑ k ∈ Finset.Icc ((c0 : ℕ) + 1) ((X o).rkF 1 (t0 + 1)), (blkAt L o i).wt (X o) 1 (t0 + 1) k) else 0) := by
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hR0, hR1, H.tie.1 o0 t0 c0 c0.2]
        simp only [← Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← H.wt o0 t0 k, ← Fin.sum_univ_fun_getElem]
        rfl
      rw [hD]
      unfold blkProd
      refine IsWeightedHomogeneous.prod _ _ _ fun o _ => ?_
      by_cases ho : o = o0
      · subst ho
        rw [if_pos rfl]
        unfold toAll
        apply isWH_rename
        unfold prodAll
        refine IsWeightedHomogeneous.prod _ _ _ fun i _ => ?_
        apply isWH_rename
        refine isWH_congr ?_ (isWH_add
          (blockPoly_isWeightedHomogeneous' (X o) (F o) (fun _ x => x.2.val) (H.std o) (blkAt L o i) 0 t0 (c0 : ℕ))
          (blockPoly_isWeightedHomogeneous' (X o) (F o) (fun _ x => x.2.val) (H.std o) (blkAt L o i) 1 (t0 + 1) (c0 : ℕ)))
        rintro ⟨ρ, gg, tt, cc'⟩
        simp only [Function.comp_apply, keyEq, wRowG, true_and, H.hty]
        fin_cases gg <;> simp
      · rw [if_neg ho]
        unfold toAll
        apply isWH_rename
        refine isWH_of_zero (fun x => ?_) _
        obtain ⟨ρ, gg, tt, cc'⟩ := x
        simp only [Function.comp_apply, keyEq]
        rw [if_neg]
        exact fun hh => ho hh.1
    · push Not at hσ
      rw [H.tie.2 σ hσ c0 c0.2]
      refine isWH_of_zero (fun x => ?_) _
      obtain ⟨ρ, o, g, t, c⟩ := x
      show (if (⟨tau o t, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0) = 0
      rw [if_neg]
      exact fun hh => hσ o t (congrArg Sigma.fst hh)

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqSum2
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

namespace RowTiePCEqSum

theorem subst_zero_const {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = 0 := by
  ext e
  rw [MvPowerSeries.coeff_subst MvPowerSeries.HasSubst.zero, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hn
    have hs' : n s ≠ 0 := by simpa using hs
    have : (n.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 :=
      Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 hs') (zero_pow hs')
    rw [this, map_zero, smul_zero]

theorem hasSubst_unit {τ : Type} {T : MvPowerSeries τ C} (hT : MvPowerSeries.constantCoeff T = 0) :
    MvPowerSeries.HasSubst (fun _ : Unit => T) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hT)

theorem subst_lin {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : MvPowerSeries.HasSubst a) {ι : Type}
    (s : Finset ι) (r : ι → C) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∑ i ∈ s, r i • F i) = ∑ i ∈ s, r i • MvPowerSeries.subst a (F i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
  | exact map_smul _ _ _
  | exact AlgHom.map_smul_of_tower _ _ _

theorem coeff_subst_tyS {τ : Type} [Finite τ] {l : ℕ} (hl : 2 ≤ l) {T : MvPowerSeries τ C}
    (hT : MvPowerSeries.constantCoeff T = 0) (a : ℕ → C) (μ : τ →₀ ℕ) :
    MvPowerSeries.coeff μ (MvPowerSeries.subst (fun _ : Unit => T) (tyS l a)) =
      ∑ s ∈ Finset.range (μ.degree + 1), a s * MvPowerSeries.coeff μ (T ^ (l ^ s)) := by
  set N := μ.degree + 1 with hN
  set P : PowerSeries C := ∑ s ∈ Finset.range N, a s • PowerSeries.X ^ (l ^ s) with hP
  have hPc : ∀ m < l ^ N, PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m P := by
    intro m hm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_sum]
    simp only [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
    by_cases h : ∃ s', l ^ s' = m
    · obtain ⟨s', rfl⟩ := h
      rw [coeff_tyS_pow hl, Finset.sum_eq_single s']
      · simp
      · intro s _ hs
        rw [if_neg, smul_zero]
        intro h
        exact hs (Nat.pow_right_injective hl h).symm
      · intro h
        exfalso
        apply h
        rw [Finset.mem_range]
        exact (Nat.pow_lt_pow_iff_right (by omega)).1 hm
    · push Not at h
      rw [coeff_tyS_of_ne a m h]
      symm
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [if_neg (h s).symm, smul_zero]
  have hAg : Formalism.G.LogCR.Agree N (tyS l a : MvPowerSeries Unit C) (P : MvPowerSeries Unit C) := by
    intro e he
    have hes : e = Finsupp.single () (e ()) := Finsupp.unique_single e
    rw [hes] at he ⊢
    rw [Finsupp.degree_single] at he
    exact hPc _ (lt_of_lt_of_le he (Nat.lt_pow_self (by omega)).le)
  have h1 := Formalism.G.LogCR.Agree.subst (a := fun _ : Unit => T) (a' := fun _ : Unit => T) (fun _ => hT) (fun _ => hT) hAg
    (fun _ _ _ => rfl) μ (by omega)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, hP, ← MvPowerSeries.coe_substAlgHom (hasSubst_unit hT), map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, map_pow, MvPowerSeries.coe_substAlgHom]
  rw [show (PowerSeries.X : PowerSeries C) = (MvPowerSeries.X () : MvPowerSeries Unit C) from rfl,
    MvPowerSeries.subst_X (hasSubst_unit hT), MvPowerSeries.coeff_smul]

section Add

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

end Add

end RowTiePCEqSum


end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTeichDef
section
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

def TeichSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C),
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) →
    ∀ (n d : ℕ), d ≠ 0 → ∀ (A : Set (Matrix (Fin n) (Fin n) C)),
      (∀ a ∈ A, ∀ b ∈ A, a + b ∈ A) → (∀ a ∈ A, -a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, ∀ i j, V.Ge 0 (a i j)) →
      (∀ (s : ℕ → Matrix (Fin n) (Fin n) C) (b : Matrix (Fin n) (Fin n) C), (∀ k, s k ∈ A) →
        (∀ i j, RowTiePE0.Tends V (fun k => s k i j) (b i j)) → b ∈ A) →
      (∀ a ∈ A, ((V.l : C)⁻¹) • (a ^ V.l ^ d - a) ∈ A) →
      ∀ b ∈ A, ∃ τ ∈ A, τ ^ V.l ^ d = τ ∧ ((V.l : C)⁻¹) • (b - τ) ∈ A

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePPTAvg
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

def VLim (V : VF C) {N : Type} (m : ℕ → ℕ → N → C) (m' : ℕ → N → C) : Prop :=
  ∀ (K : ℝ) (s : ℕ) (n : N), ∃ k0 : ℕ, ∀ k ≥ k0, V.Ge K (m' s n - m k s n)

theorem VLim.mul_right {V : VF C} {N : Type} {m : ℕ → ℕ → N → C} {m' : ℕ → N → C} (h : VLim V m m')
    (y : ℕ → N → C) : VLim V (fun k => m k * y) (m' * y) := by
  intro K s n
  by_cases hy : y s n = 0
  · exact ⟨0, fun k _ => by simp [hy, VF.Ge.zero]⟩
  · have hne : V.v (y s n) ≠ ⊤ := by
      rw [Ne, AddValuation.top_iff]; exact hy
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    obtain ⟨k0, hk0⟩ := h (K - r) s n
    refine ⟨k0, fun k hk => ?_⟩
    have e : (m' * y) s n - (m k * y) s n = (m' s n - m k s n) * y s n := by
      simp only [Pi.mul_apply]; ring
    rw [e]
    have hyr : V.Ge r (y s n) := by unfold VF.Ge; rw [← hr]
    have := (hk0 k hk).mul hyr
    simpa using this

end Formalism.L2.FormalSeriesBounds
end
end

