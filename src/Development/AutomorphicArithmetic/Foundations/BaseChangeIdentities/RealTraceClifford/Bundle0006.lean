module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IsoFacts
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem dot_rt {n : ℕ} (x : Wt n) (a b : Fin n) : ∑ c, x c * rt a b c = x a - x b := by
  simp [rt, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

private theorem dot_add {n : ℕ} (x u v : Wt n) :
    ∑ c, x c * (u + v) c = ∑ c, x c * u c + ∑ c, x c * v c := by
  simp [mul_add, Finset.sum_add_distrib]

private theorem wt_shift {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hg : GlRel F) {μ : Wt n} {y : V}
    (hy : IsWeight F μ y) (a b : Fin n) : IsWeight F (μ + rt a b) (F a b y) := by
  intro c
  have h := LinearMap.congr_fun (hg c c a b) y
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hy c, map_smul, sub_eq_iff_eq_add] at h
  rw [h]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb
    simp [rt]
  · subst hca
    simp [rt, Pi.single_apply, hcb, Ne.symm hcb, add_smul]
    abel
  · subst hcb
    simp [rt, Pi.single_apply, hca, Ne.symm hca, add_smul, sub_smul]
    abel
  · simp [rt, Pi.single_apply, hca, hcb, Ne.symm hcb]

private theorem wt_word {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hg : GlRel F) {μ : Wt n} {x : V}
    (hx : IsWeight F μ x) (w : List (Fin n × Fin n)) :
    IsWeight F (μ + (w.map fun p => rt p.1 p.2).sum) (Formalism.REAL.ew F w x) := by
  induction w with
  | nil => simpa [Formalism.REAL.ew] using hx
  | cons p w ih =>
    have h := wt_shift hg ih p.1 p.2
    rw [Formalism.REAL.ew.eq_2]
    simp only [List.map_cons, List.sum_cons, Module.End.mul_apply]
    rwa [show ∀ u v : Wt n, μ + (u + v) = (μ + v) + u from fun u v => by abel]

private theorem maj_word {n : ℕ} (ν x : Wt n) (hx : Antitone x) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, p.2 < p.1) :
    ∑ a, x a * (ν + (w.map fun p => rt p.1 p.2).sum) a ≤ ∑ a, x a * ν a := by
  induction w with
  | nil => simp
  | cons p w ih =>
    have hp := hw p (by simp)
    have ih' := ih (fun q hq => hw q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons]
    rw [show ∀ u v : Wt n, ν + (u + v) = (ν + v) + u from fun u v => by abel, dot_add, dot_rt]
    have := hx hp.le
    linarith

private theorem rhoC_true (n : ℕ) : Formalism.REAL.rhoC (fun _ : Fin n => true) = rhoV n := by
  funext a
  simp only [Formalism.REAL.rhoC, rhoV]
  simp only [and_true, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  have ha := a.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

private theorem nsq_eq {n : ℕ} (u : Fin n → ℝ) : Formalism.REAL.nsq u = nsq u := by
  simp [Formalism.REAL.nsq, Formalism.REAL.dot, nsq, sq]

private theorem rhoV_anti (n : ℕ) : Antitone (rhoV n) := by
  intro a b hab
  have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [rhoV]
  linarith

theorem UpperTheory.RealTr.isoFacts :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ ν : Wt n, (∀ μ, μ ≠ ν → hw F μ ⊓ S = ⊥) →
      (∀ x ∈ S, Cas F x = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • x) ∧ (∀ μ, wsp F μ ⊓ S ≠ ⊥ → Maj μ ν) ∧ wsp F ν ⊓ S = hw F ν ⊓ S := by
  intro n V _ _ F hF S hS hst ν hν
  have hK : Formalism.REAL.KRel (fun _ : Fin n => true) F := Formalism.REAL.glRel_kRel _ F hF.gl
  have hU : Formalism.REAL.KUnit (fun _ : Fin n => true) F := fun a b _ x y => hF.unit a b x y
  have hSt : Formalism.REAL.KStable (fun _ : Fin n => true) F S := fun a b _ x hx => hst a b x hx
  obtain ⟨m, x, μ, hx, horth, hsup⟩ := Formalism.REAL.kDecomp V n (fun _ => true) F S hS hK hU hSt
  have hμ : ∀ i, μ i = ν := by
    intro i
    by_contra h
    have h0 := hν (μ i) h
    have hi : x i ∈ hw F (μ i) ⊓ S := Submodule.mem_inf.mpr ⟨(hx i).2.2, (hx i).1⟩
    rw [h0] at hi
    exact (hx i).2.1 ((Submodule.mem_bot ℂ).mp hi)
  have hC : ∀ y ∈ S, Cas F y = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • y := by
    have hCas : Formalism.REAL.CasK (fun _ : Fin n => true) F = Cas F := by
      simp [Formalism.REAL.CasK, Formalism.REAL.Cas]
    have hck : Formalism.REAL.ckv (fun _ : Fin n => true) ν = nsq (ν + rhoV n) - nsq (rhoV n) := by
      simp only [Formalism.REAL.ckv, rhoC_true, nsq_eq]
    intro y hy
    rw [← hsup] at hy
    refine Submodule.iSup_induction _ (motive := fun y => Cas F y = ((nsq (ν + rhoV n) - nsq (rhoV n) : ℝ) : ℂ) • y) hy ?_ ?_ ?_
    · intro i z hz
      have hz' := Formalism.REAL.kCasSpan V n _ F (μ i) (x i) hK (hx i).2.2 z hz
      rw [hCas, hμ i, hck] at hz'
      exact hz'
    · simp
    · intro a b ha hb
      rw [map_add (f := _), ha, hb, smul_add]
  have hM : ∀ μ', wsp F μ' ⊓ S ≠ ⊥ → Maj μ' ν := by
    intro μ' hne
    by_contra hnot
    apply hne
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
    rw [Submodule.mem_bot]
    have hle : S ≤ LinearMap.ker (innerₛₗ ℂ y) := by
      rw [← hsup]
      apply iSup_le
      intro i
      rw [(Formalism.REAL.kLow V n _ F (μ i) (x i) hK (hx i).2.2).1, Formalism.REAL.lowSpan, Submodule.span_le]
      rintro z ⟨w, hwl, rfl⟩
      have hwt := wt_word hF.gl (hx i).2.2.1 w
      rw [hμ i] at hwt
      have hne' : μ' ≠ ν + (w.map fun p => rt p.1 p.2).sum := by
        rintro rfl
        exact hnot (fun t ht => maj_word ν t ht w (fun p hp => (hwl p hp).2))
      simp only [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply]
      exact Formalism.REAL.kWtOrth V n _ F μ' _ y _ hU hyw hwt hne'
    have h0 := hle hyS
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero] at h0
    exact h0
  refine ⟨hC, hM, ?_⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
    have hk : KHighest (fun _ : Fin n => true) F ν y := by
      refine ⟨hyw, ?_⟩
      intro a b hab _
      by_contra hne
      have hmem : F a b y ∈ wsp F (ν + rt a b) ⊓ S :=
        Submodule.mem_inf.mpr ⟨wt_shift hF.gl hyw a b, hst a b y hyS⟩
      have hM' := hM (ν + rt a b) (by
        intro h
        rw [h] at hmem
        exact hne ((Submodule.mem_bot ℂ).mp hmem))
      have h1 := hM' (rhoV n) (rhoV_anti n)
      rw [dot_add, dot_rt] at h1
      have hlt : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
      have h2 : rhoV n b < rhoV n a := by
        simp only [rhoV]
        linarith
      linarith
    exact Submodule.mem_inf.mpr ⟨hk, hyS⟩
  · intro y hy
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hy
    exact Submodule.mem_inf.mpr ⟨(show KHighest (fun _ : Fin n => true) F ν y from h1).1, h2⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IsoSplit
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

section SlopeTestRemainingChoices

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem kSpan_self (F : Fin n → Fin n → Module.End ℂ V) (y : V) :
    y ∈ Formalism.REAL.kSpan (fun _ => true) F y := by
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf]
  exact fun S hS => hS.1

private theorem kSpan_stb (F : Fin n → Fin n → Module.End ℂ V) (y : V) (a b : Fin n) {z : V}
    (hz : z ∈ Formalism.REAL.kSpan (fun _ => true) F y) : F a b z ∈ Formalism.REAL.kSpan (fun _ => true) F y := by
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf] at hz ⊢
  exact fun S hS => hS.2 a b rfl z (hz S hS)

private theorem kSpan_le (F : Fin n → Fin n → Module.End ℂ V) {y : V} {Q : Submodule ℂ V}
    (hy : y ∈ Q) (hQ : Stb F Q) : Formalism.REAL.kSpan (fun _ => true) F y ≤ Q :=
  sInf_le ⟨hy, fun a b _ x hx => hQ a b x hx⟩

private theorem le_isoPart (F : Fin n → Fin n → Module.End ℂ V) {T : Set (Wt n)} {S : Submodule ℂ V}
    {y : V} {μ : Wt n} (hy : y ∈ S) (hμ : μ ∈ T) (h : KHighest (fun _ => true) F μ y) :
    Formalism.REAL.kSpan (fun _ => true) F y ≤ Formalism.REAL.isoPart (fun _ => true) F T S :=
  le_iSup₂_of_le (f := fun (y : V) (_ : y ∈ S ∧ ∃ μ ∈ T, KHighest (fun _ => true) F μ y) =>
    Formalism.REAL.kSpan (fun _ => true) F y) y ⟨hy, μ, hμ, h⟩ le_rfl

private theorem isoPart_map (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V)
    (f : Module.End ℂ V) (Q : Submodule ℂ V)
    (h : ∀ y, y ∈ S → ∀ μ ∈ T, KHighest (fun _ => true) F μ y →
      ∀ z ∈ Formalism.REAL.kSpan (fun _ => true) F y, f z ∈ Q) :
    ∀ z ∈ Formalism.REAL.isoPart (fun _ => true) F T S, f z ∈ Q := by
  have hle : Formalism.REAL.isoPart (fun _ => true) F T S ≤ Q.comap f := by
    unfold Formalism.REAL.isoPart
    refine iSup₂_le fun y hy => ?_
    obtain ⟨hyS, μ, hμ, hk⟩ := hy
    exact fun w hw => h y hyS μ hμ hk w hw
  exact fun z hz => hle hz

private theorem isoPart_stb (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V) :
    Stb F (Formalism.REAL.isoPart (fun _ => true) F T S) := fun a b =>
  isoPart_map F T S (F a b) _ fun y hy μ hμ hk z hz =>
    le_isoPart F hy hμ hk (kSpan_stb F y a b hz)

private theorem isoPart_cm (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V)
    (B : Module.End ℂ V) (hB : Cm F S B) :
    ∀ x ∈ Formalism.REAL.isoPart (fun _ => true) F T S, B x ∈ Formalism.REAL.isoPart (fun _ => true) F T S := by
  have hc : ∀ a b x, B (F a b x) = F a b (B x) := fun a b x => LinearMap.congr_fun (hB.1 a b) x
  refine isoPart_map F T S B _ fun y hy μ hμ hk z hz => ?_
  have hkB : KHighest (fun _ => true) F μ (B y) :=
    ⟨fun a => by rw [← hc, hk.1 a, map_smul], fun a b hab he => by rw [← hc, hk.2 a b hab he, map_zero]⟩
  have hle : Formalism.REAL.kSpan (fun _ => true) F y ≤ (Formalism.REAL.kSpan (fun _ => true) F (B y)).comap B :=
    kSpan_le F (kSpan_self F (B y)) fun a b x hx => by
      rw [Submodule.mem_comap, hc]
      exact kSpan_stb F (B y) a b hx
  exact le_isoPart F (hB.2 y hy) hμ hkB (hle hz)

private theorem parts_zero {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂) {u v : V} (hu : u ∈ S₁)
    (hv : v ∈ S₂) (h : u + v = 0) : u = 0 ∧ v = 0 := by
  have hv' : v = -u := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h
  have hv1 : v ∈ S₁ := hv' ▸ S₁.neg_mem hu
  have h0 : v = 0 := (Submodule.disjoint_def.mp hd) v hv1 hv
  refine ⟨?_, h0⟩
  rw [h0, add_zero] at h
  exact h

private theorem wt_comp (F : Fin n → Fin n → Module.End ℂ V) {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂)
    (s1 : Stb F S₁) (s2 : Stb F S₂) {μ : Wt n} {y₁ y₂ : V} (h₁ : y₁ ∈ S₁) (h₂ : y₂ ∈ S₂)
    (h : IsWeight F μ (y₁ + y₂)) : IsWeight F μ y₁ ∧ IsWeight F μ y₂ := by
  have key : ∀ a, F a a y₁ = ↑(μ a) • y₁ ∧ F a a y₂ = ↑(μ a) • y₂ := by
    intro a
    have e := h a
    rw [map_add (f := _), smul_add] at e
    have hz := parts_zero hd (S₁.sub_mem (s1 a a y₁ h₁) (S₁.smul_mem _ h₁))
      (S₂.sub_mem (s2 a a y₂ h₂) (S₂.smul_mem _ h₂)) (by rw [sub_add_sub_comm, e, sub_self])
    exact ⟨sub_eq_zero.mp hz.1, sub_eq_zero.mp hz.2⟩
  exact ⟨fun a => (key a).1, fun a => (key a).2⟩

set_option maxHeartbeats 200000 in
private theorem hw_comp (F : Fin n → Fin n → Module.End ℂ V) {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂)
    (s1 : Stb F S₁) (s2 : Stb F S₂) {μ : Wt n} {y₁ y₂ : V} (h₁ : y₁ ∈ S₁) (h₂ : y₂ ∈ S₂)
    (h : KHighest (fun _ => true) F μ (y₁ + y₂)) :
    KHighest (fun _ => true) F μ y₁ ∧ KHighest (fun _ => true) F μ y₂ := by
  obtain ⟨w1, w2⟩ := wt_comp F hd s1 s2 h₁ h₂ h.1
  refine ⟨⟨w1, fun a b hab e => ?_⟩, ⟨w2, fun a b hab e => ?_⟩⟩
  · have h0 := h.2 a b hab e
    rw [map_add (f := _)] at h0
    exact (parts_zero hd (s1 a b _ h₁) (s2 a b _ h₂) h0).1
  · have h0 := h.2 a b hab e
    rw [map_add (f := _)] at h0
    exact (parts_zero hd (s1 a b _ h₁) (s2 a b _ h₂) h0).2

end SlopeTestRemainingChoices

theorem UpperTheory.RealTr.isoSplit :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → S ≠ ⊥ → ∃ (ν : Wt n) (S₁ S₂ : Submodule ℂ V), S₁ ≠ ⊥ ∧ hw F ν ⊓ S₁ ≠ ⊥ ∧ S₁ ⊔ S₂ = S ∧ Disjoint S₁ S₂ ∧ Stb F S₁ ∧ Stb F S₂ ∧
      (∀ B, Cm F S B → Cm F S₁ B ∧ Cm F S₂ B) ∧ (∀ μ, μ ≠ ν → hw F μ ⊓ S₁ = ⊥) ∧
      ∀ μ, wsp F μ ⊓ S = (wsp F μ ⊓ S₁) ⊔ (wsp F μ ⊓ S₂) ∧ hw F μ ⊓ S = (hw F μ ⊓ S₁) ⊔ (hw F μ ⊓ S₂) := by
  intro n V _ _ F hF S hS hst hne
  have hK := Formalism.REAL.glRel_kRel (fun _ : Fin n => true) F hF.gl
  have hU : Formalism.REAL.KUnit (fun _ : Fin n => true) F := fun a b _ x y => hF.unit a b x y
  have hSt : Formalism.REAL.KStable (fun _ : Fin n => true) F S := fun a b _ x hx => hst a b x hx
  obtain ⟨x, hxS, hx0, ν, hxk⟩ := Formalism.REAL.kHiExist V n _ F S hS hK hU hSt hne
  obtain ⟨horth, hsup⟩ := Formalism.REAL.kIsoSplit V n _ F S {ν} hS hK hU hSt
  set S₁ := Formalism.REAL.isoPart (fun _ : Fin n => true) F {ν} S with hS₁
  set S₂ := Formalism.REAL.isoPart (fun _ : Fin n => true) F {ν}ᶜ S with hS₂
  have hd : Disjoint S₁ S₂ := by
    rw [Submodule.disjoint_def]
    intro v h1 h2
    have h0 := horth v h1 v h2
    rwa [inner_self_eq_zero] at h0
  have h1S : S₁ ≤ S := hsup ▸ le_sup_left
  have h2S : S₂ ≤ S := hsup ▸ le_sup_right
  have hst1 : Stb F S₁ := isoPart_stb F _ S
  have hst2 : Stb F S₂ := isoPart_stb F _ S
  have hx1 : x ∈ S₁ := le_isoPart (T := {ν}) F hxS (Set.mem_singleton ν) hxk (kSpan_self F x)
  refine ⟨ν, S₁, S₂, ?_, ?_, hsup, hd, hst1, hst2, ?_, ?_, ?_⟩
  · intro h
    rw [h] at hx1
    exact hx0 ((Submodule.mem_bot ℂ).mp hx1)
  · intro h
    have hm : x ∈ hw F ν ⊓ S₁ := Submodule.mem_inf.mpr ⟨hxk, hx1⟩
    rw [h] at hm
    exact hx0 ((Submodule.mem_bot ℂ).mp hm)
  · intro B hB
    exact ⟨⟨hB.1, isoPart_cm F _ S B hB⟩, ⟨hB.1, isoPart_cm F _ S B hB⟩⟩
  · intro μ hμ
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyk, hy1⟩ := Submodule.mem_inf.mp hy
    have hy2 : y ∈ S₂ := le_isoPart (T := {ν}ᶜ) F (h1S hy1) (show μ ∈ ({ν}ᶜ : Set (Wt n)) from hμ) hyk (kSpan_self F y)
    exact (Submodule.mem_bot ℂ).mpr (Submodule.disjoint_def.mp hd y hy1 hy2)
  · intro μ
    constructor
    · apply le_antisymm
      · intro y hy
        obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
        rw [← hsup] at hyS
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := Submodule.mem_sup.mp hyS
        obtain ⟨w1, w2⟩ := wt_comp F hd hst1 hst2 h₁ h₂ hyw
        exact Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨w1, h₁⟩) (Submodule.mem_inf.mpr ⟨w2, h₂⟩)
      · exact sup_le (inf_le_inf_left _ h1S) (inf_le_inf_left _ h2S)
    · apply le_antisymm
      · intro y hy
        obtain ⟨hyk, hyS⟩ := Submodule.mem_inf.mp hy
        rw [← hsup] at hyS
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := Submodule.mem_sup.mp hyS
        obtain ⟨k1, k2⟩ := hw_comp F hd hst1 hst2 h₁ h₂ hyk
        exact Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨k1, h₁⟩) (Submodule.mem_inf.mpr ⟨k2, h₂⟩)
      · exact sup_le (inf_le_inf_left _ h1S) (inf_le_inf_left _ h2S)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SgMulSelf
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.CartanExamples

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def sg (key : ι → ℕ) (i : ι) (A : Finset ι) : ℂ :=
  (-1) ^ (A.filter fun j => key j < key i).card

private def tw (key : ι → ℕ) (i j : ι) : ℂ := if key j < key i then -1 else 1

private theorem tw_self (key : ι → ℕ) (i : ι) : tw key i i = 1 := by simp [tw]

private theorem tw_mul_self (key : ι → ℕ) (i j : ι) : tw key i j * tw key i j = 1 := by
  unfold tw
  split_ifs <;> norm_num

private theorem tw_swap {key : ι → ℕ} (hk : Function.Injective key) {i j : ι} (h : i ≠ j) :
    tw key j i = -tw key i j := by
  have hne : key i ≠ key j := fun e => h (hk e)
  rcases lt_or_gt_of_ne hne with h1 | h1 <;> simp [tw, h1, lt_asymm h1]

private theorem sg_mul_self (key : ι → ℕ) (i : ι) (A : Finset ι) :
    sg key i A * sg key i A = 1 := by
  unfold sg
  rw [← mul_pow]
  norm_num

private theorem star_sg (key : ι → ℕ) (i : ι) (A : Finset ι) :
    star (sg key i A) = sg key i A := by
  unfold sg
  simp

private theorem sg_insert (key : ι → ℕ) (i : ι) {j : ι} {A : Finset ι} (h : j ∉ A) :
    sg key i (insert j A) = tw key i j * sg key i A := by
  unfold sg tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

private theorem sg_erase (key : ι → ℕ) (i : ι) {j : ι} {A : Finset ι} (h : j ∈ A) :
    sg key i (A.erase j) = tw key i j * sg key i A := by
  have h1 := sg_insert key i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]

private def al (key : ι → ℕ) (i : ι) : Matrix (Finset ι) (Finset ι) ℂ :=
  Matrix.of fun A A' => if i ∉ A ∧ A' = insert i A then sg key i A else 0

private theorem al_mul (key : ι → ℕ) (i : ι) (M : Matrix (Finset ι) (Finset ι) ℂ) (A B : Finset ι) :
    (al key i * M) A B = if i ∈ A then 0 else sg key i A * M (insert i A) B := by
  rw [Matrix.mul_apply]
  simp only [al, Matrix.of_apply]
  split_ifs with hi
  · simp [hi]
  · simp [hi]

private theorem alH_mul (key : ι → ℕ) (i : ι) (M : Matrix (Finset ι) (Finset ι) ℂ)
    (A B : Finset ι) :
    ((al key i)ᴴ * M) A B = if i ∈ A then sg key i A * M (A.erase i) B else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, al, Matrix.of_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single (A.erase i)]
    · rw [if_pos ⟨Finset.notMem_erase i A, (Finset.insert_erase hi).symm⟩, star_sg,
        sg_erase key i hi, tw_self, one_mul]
    · intro A' _ hA'
      rw [if_neg, star_zero, zero_mul]
      rintro ⟨h1, rfl⟩
      exact hA' (Finset.erase_insert h1).symm
    · intro hm
      exact absurd (Finset.mem_univ _) hm
  · apply Finset.sum_eq_zero
    intro A' _
    rw [if_neg, star_zero, zero_mul]
    rintro ⟨_, rfl⟩
    exact hi (Finset.mem_insert_self i A')

private theorem ann_ann {key : ι → ℕ} (hk : Function.Injective key) (i j : ι)
    (M : Matrix (Finset ι) (Finset ι) ℂ) :
    al key i * (al key j * M) + al key j * (al key i * M) = 0 := by
  ext A B
  simp only [Matrix.add_apply, Matrix.zero_apply, al_mul]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert key j hi, sg_insert key i hj, tw_swap hk hij, Finset.insert_comm j i]
  ring

private theorem ann_cre {key : ι → ℕ} (hk : Function.Injective key) (i j : ι)
    (M : Matrix (Finset ι) (Finset ι) ℂ) :
    al key i * ((al key j)ᴴ * M) + (al key j)ᴴ * (al key i * M) = if i = j then M else 0 := by
  ext A B
  simp only [Matrix.add_apply, al_mul, alH_mul]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi : i ∈ A
    · rw [if_pos hi, if_pos hi, if_neg (Finset.notMem_erase i A), Finset.insert_erase hi,
        sg_erase key i hi, tw_self, zero_add]
      linear_combination M A B * sg_mul_self key i A
    · rw [if_neg hi, if_neg hi, if_pos (Finset.mem_insert_self i A), Finset.erase_insert hi,
        sg_insert key i hi, tw_self, add_zero]
      linear_combination M A B * sg_mul_self key i A
  rw [if_neg hij, Matrix.zero_apply]
  by_cases hi : i ∈ A
  · rw [if_pos hi, zero_add, if_pos (Finset.mem_erase.2 ⟨hij, hi⟩)]
    simp
  by_cases hj : j ∈ A
  · rw [if_neg hi, if_pos (Finset.mem_insert_of_mem hj), if_pos hj,
      if_neg (fun hm => hi (Finset.mem_of_mem_erase hm)), sg_insert key j hi, sg_erase key i hj,
      tw_swap hk hij, Finset.erase_insert_of_ne hij]
    ring
  · have h1 : j ∉ insert i A := fun hm => (Finset.mem_insert.1 hm).elim (fun e => hij e.symm) hj
    rw [if_neg hi, if_neg h1, if_neg hj]
    simp

private theorem cre_ann (key : ι → ℕ) (i : ι) :
    (al key i)ᴴ * al key i = Matrix.diagonal fun A => if i ∈ A then 1 else 0 := by
  ext A B
  rw [alH_mul, Matrix.diagonal_apply]
  simp only [al, Matrix.of_apply]
  by_cases hi : i ∈ A
  · rw [if_pos hi, if_pos hi, Finset.insert_erase hi, sg_erase key i hi, tw_self, one_mul]
    by_cases hAB : A = B
    · subst hAB
      rw [if_pos ⟨Finset.notMem_erase i A, rfl⟩, if_pos rfl, sg_mul_self]
    · rw [if_neg (fun hc => hAB hc.2.symm), if_neg hAB, mul_zero]
  · rw [if_neg hi, if_neg hi]
    simp

end UpperTheory.RealTr.CartanExamples

open UpperTheory.RealTr.CartanExamples in
theorem UpperTheory.RealTr.carEx :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∃ α : ι → Matrix (Finset ι) (Finset ι) ℂ, (∀ i j, α i * α j + α j * α i = 0) ∧
      (∀ i j, α i * (α j)ᴴ + (α j)ᴴ * α i = if i = j then 1 else 0) ∧ ∀ i, (α i)ᴴ * α i = Matrix.diagonal fun A => if i ∈ A then 1 else 0 := by
  intro ι _ _
  let key : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ)
  have hk : Function.Injective key := fun a b h => (Fintype.equivFin ι).injective (Fin.ext h)
  refine ⟨al key, fun i j => ?_, fun i j => ?_, cre_ann key⟩
  · simpa using ann_ann hk i j 1
  · simpa using ann_cre hk i j 1
end
end

