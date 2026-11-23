module

public import Formalism.HermitianCurvature.StatementTC
public import Formalism.HermitianCurvature.Bundle0003
public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0016

@[expose] public section

namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical

section gen
variable {α : Type}

lemma psd_congr {P : Finset α} {k k' : α → α → ℂ} (h : ∀ x ∈ P, ∀ y ∈ P, k x y = k' x y)
    (hk : PSDOn P k) : PSDOn P k' := by
  unfold TA.PSDOn at hk ⊢
  refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
  · rw [← h x hx y hy, ← h y hy x hx]
    exact hk.1 x hx y hy
  · have e : ∑ x ∈ P, ∑ y ∈ P, conj (a x) * k' x y * a y =
        ∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y :=
      Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [h x hx y hy]
    rw [e]
    exact hk.2 a

lemma psd_zero (P : Finset α) : PSDOn P (fun _ _ => (0 : ℂ)) := by
  unfold TA.PSDOn
  exact ⟨fun _ _ _ _ => by simp, fun a => by simp⟩

lemma psd_add {P : Finset α} {k k' : α → α → ℂ} (hk : PSDOn P k) (hk' : PSDOn P k') :
    PSDOn P (fun x y => k x y + k' x y) := by
  unfold TA.PSDOn at hk hk' ⊢
  refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
  · simp only [hk.1 x hx y hy, hk'.1 x hx y hy, map_add (f := _)]
  · have e : ∑ x ∈ P, ∑ y ∈ P, conj (a x) * (k x y + k' x y) * a y =
        (∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y) +
          ∑ x ∈ P, ∑ y ∈ P, conj (a x) * k' x y * a y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [e, Complex.add_re]
    exact add_nonneg (hk.2 a) (hk'.2 a)

variable {E : Type} [AddCommGroup E]

lemma mk_eq_iff (L : AddSubgroup E) (x y : E) : ((x : E ⧸ L) = (y : E ⧸ L)) ↔ x - y ∈ L := by
  exact QuotientAddGroup.eq_iff_sub_mem

noncomputable def G (L : AddSubgroup E) (S : Finset E) (Th : E → α → α → ℂ) (c : E ⧸ L) : α → α → ℂ :=
  if hc : ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c then Th hc.choose else fun _ _ => 0

end gen

section ta
variable {E : Type} [Field E] [DecidableEq E]

end ta

section main
variable {E : Type} [Field E] [DecidableEq E]

end main

end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1

namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A2

open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism.FourierDecayAlt.TC

end Formalism.FourierDecayAlt.P.RecursionWithDensities.A2

namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1

open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical

theorem psd_congr {α : Type} {Y : Finset α} {k k' : α → α → ℂ}
    (h : ∀ x ∈ Y, ∀ y ∈ Y, k x y = k' x y) (hk : PSDOn Y k) : PSDOn Y k' := by
  unfold TB.PSDOn at hk ⊢
  have e : (Matrix.of fun x y : Y => k' x y) = Matrix.of fun x y : Y => k x y := by
    ext x y
    simp only [Matrix.of_apply]
    exact (h x x.2 y y.2).symm
  rw [e]
  exact hk

theorem psd_zero {α : Type} (Y : Finset α) : PSDOn Y (fun _ _ => (0 : ℂ)) := by
  unfold TB.PSDOn
  have e : (Matrix.of fun x y : Y => (0 : ℂ)) = 0 := by
    ext x y
    simp
  rw [e]
  exact Matrix.PosSemidef.zero

theorem psd_add {α : Type} {Y : Finset α} {k k' : α → α → ℂ} (h : PSDOn Y k) (h' : PSDOn Y k') :
    PSDOn Y (fun x y => k x y + k' x y) := by
  unfold TB.PSDOn at h h' ⊢
  have e : (Matrix.of fun x y : Y => k x y + k' x y) =
      (Matrix.of fun x y : Y => k x y) + Matrix.of fun x y : Y => k' x y := by
    ext x y
    simp
  rw [e]
  exact h.add h'

private theorem sum_attach_ite_eq {α : Type} (X : Finset α) (a : α) (F : α → ℂ) :
    (∑ j ∈ X.attach, if (j : α) = a then F j else 0) = if a ∈ X then F a else 0 := by
  rw [Finset.sum_attach (s := X) (f := fun j => if j = a then F j else 0)]
  first
  | exact Finset.sum_ite_eq' X a F
  | simp

theorem psd_restrict {α : Type} {X : Finset α} (Y : Finset α) {k : α → α → ℂ} (hk : PSDOn X k) :
    PSDOn Y (fun x y => if x ∈ X ∧ y ∈ X then k x y else 0) := by
  unfold TB.PSDOn at hk ⊢
  have hB := hk.conjTranspose_mul_mul_same
    (Matrix.of fun (x : X) (y : Y) => if (x : α) = (y : α) then (1 : ℂ) else 0)
  convert hB using 1
  ext y y'
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite (star : ℂ → ℂ)]
  rw [sum_attach_ite_eq X (y' : α) (fun a => ∑ j ∈ X.attach, if (j : α) = (y : α) then k j a else 0),
    sum_attach_ite_eq X (y : α) (fun a => k a y')]
  by_cases hy : (y : α) ∈ X <;> by_cases hy' : (y' : α) ∈ X <;> simp [hy, hy']

theorem psd_smul {α : Type} {Y : Finset α} {k : α → α → ℂ} (c : ℝ) (hc : 0 ≤ c) (h : PSDOn Y k) :
    PSDOn Y (fun x y => (c : ℂ) * k x y) := by
  unfold TB.PSDOn at h ⊢
  have e : (Matrix.of fun x y : Y => (c : ℂ) * k x y) = (c : ℂ) • Matrix.of fun x y : Y => k x y := by
    ext x y
    simp
  rw [e]
  exact h.smul (Complex.zero_le_real.mpr hc)

variable {E W : Type} [Field E]

theorem domMinOfText : DomMinOfText := by
  intro E W _ D T Th hT i s hs hsi hi
  obtain ⟨_, h2, h3, h4⟩ := hT i s hs hsi hi
  refine ⟨fun t ht => h2 t ?_, fun t _ t' _ hl => h3 t t' hl, fun S _ hS => h4 S hS⟩
  rintro rfl
  exact T.zero_not_mem _ _ ht

theorem majorantPSD : MajorantPSD := by
  intro E W _ D T Th hK hD i s hs hsi hi t ht
  have h1 := (hD i s hs hsi hi).1 t ht
  have h2 : TB.PSDOn (T.X (i - s)) (TB.blk (D.Kr i) s t t) := by
    have hY := hK i ((T.X (i - s)).image fun h => join h s t)
    unfold TB.PSDOn at hY ⊢
    have := hY.submatrix (fun h : T.X (i - s) =>
      (⟨join h.1 s t, Finset.mem_image_of_mem _ h.2⟩ : ((T.X (i - s)).image fun h => join h s t)))
    convert this using 1
    ext x y
    rfl
  refine psd_congr ?_ (psd_add h1 h2)
  intro x _ y _
  exact sub_add_cancel _ _

theorem psd_restrict' {α : Type} {X : Finset α} (Y : Finset α) {k k' : α → α → ℂ} (hk : PSDOn X k)
    (h1 : ∀ x y, x ∈ X ∧ y ∈ X → k' x y = k x y) (h0 : ∀ x y, ¬ (x ∈ X ∧ y ∈ X) → k' x y = 0) :
    PSDOn Y k' := by
  refine psd_congr (fun x _ y _ => ?_) (psd_restrict Y hk)
  show (if x ∈ X ∧ y ∈ X then k x y else 0) = k' x y
  by_cases h : x ∈ X ∧ y ∈ X
  · rw [if_pos h, h1 x y h]
  · rw [if_neg h, h0 x y h]

theorem mk_eq_iff (L : AddSubgroup E) (a b : E) : ((a : E ⧸ L) = (b : E ⧸ L)) ↔ a - b ∈ L := by
  exact QuotientAddGroup.eq_iff_sub_mem

def good (L : AddSubgroup E) (S : Finset E) (c : E ⧸ L) : Prop := ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c

noncomputable def sel (L : AddSubgroup E) (S : Finset E) (c : E ⧸ L) : E :=
  if h : good L S c then h.choose else 0

theorem sel_mem {L : AddSubgroup E} {S : Finset E} {c : E ⧸ L} (h : good L S c) : sel L S c ∈ S := by
  unfold sel
  rw [dif_pos h]
  exact h.choose_spec.1

theorem sel_mk {L : AddSubgroup E} {S : Finset E} {c : E ⧸ L} (h : good L S c) :
    ((sel L S c : E) : E ⧸ L) = c := by
  unfold sel
  rw [dif_pos h]
  exact h.choose_spec.2

noncomputable def KrR (D : Data E W) (T : Tower E) : ℕ → Pt E → Pt E → ℂ :=
  fun i p q => if p ∈ T.X i ∧ q ∈ T.X i then D.Kr i p q else 0

noncomputable def ThR (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) :
    ℕ → ℕ → E → Pt E → Pt E → ℂ :=
  fun i s t h h' =>
    if (1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1) ∧
        good (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s) then
      (if h ∈ T.X (i - s) ∧ h' ∈ T.X (i - s) then
        Th i s (sel (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s)) h h'
      else 0)
    else 0

noncomputable def Dp (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) : Data E W :=
  { D with
    Kr := KrR D T
    K0 := by simp [KrR, Formalism.FourierDecayAlt.P.OneLevelCoefficients.X0, D.K0]
    Th := ThR D T Th }

theorem join_mem (T : Tower E) {i s : ℕ} (hs : 1 ≤ s) (hsi : s ≤ i) {t : E}
    (ht : t ∈ T.Sg (i - s + 1) s) (h : Pt E) : join h s t ∈ T.X i ↔ h ∈ T.X (i - s) := by
  have E1 : ∀ k (hk' : k < h.length) (hk2 : k < (join h s t).length),
      (join h s t)[k]'hk2 = h[k]'hk' := by
    intro k hk' hk2
    first
    | simp [join, List.getElem_append_left hk']
    | simp [join, List.getElem_append, hk']
  have E2 : ∀ k, k ≤ h.length → blockStart (join h s t) k = blockStart h k := by
    intro k hk'
    simp [blockStart, join, List.take_append_of_le_length hk']
  rw [T.isTower i, T.isTower (i - s)]
  constructor
  · rintro ⟨hl, hk⟩
    have hl' : level h + s = i := by simpa [level, join] using hl
    refine ⟨by omega, fun k hk' => ?_⟩
    have hk2 : k < (join h s t).length := by simp [join]; omega
    have := hk k hk2
    rw [E1 k hk' hk2, E2 k hk'.le] at this
    exact this
  · rintro ⟨hl, hk⟩
    refine ⟨?_, fun k hk2 => ?_⟩
    · simp [level, join] at hl ⊢
      omega
    · by_cases hk' : k < h.length
      · rw [E1 k hk' hk2, E2 k hk'.le]
        exact hk k hk'
      · have hkl : k = h.length := by simp [join] at hk2; omega
        subst hkl
        have e1 : (join h s t)[h.length]'hk2 = (s, t) := by simp [join]
        have e2 : blockStart (join h s t) h.length = level h + 1 := by
          simp [blockStart, join, level, List.take_append_of_le_length (le_refl h.length)]
        rw [e1, e2, hl]
        exact ⟨hs, ht⟩

theorem join_not_mem (T : Tower E) {i s : ℕ} {t : E}
    (ht : t ∉ T.Sg (i - s + 1) s) (h : Pt E) : join h s t ∉ T.X i := by
  intro hm
  rw [T.isTower i] at hm
  obtain ⟨hl, hk⟩ := hm
  have hl' : level h + s = i := by simpa [level, join] using hl
  have hk2 : h.length < (join h s t).length := by simp [join]
  have := (hk h.length hk2).2
  have e1 : (join h s t)[h.length]'hk2 = (s, t) := by simp [join]
  have e2 : blockStart (join h s t) h.length = level h + 1 := by
    simp [blockStart, join, level, List.take_append_of_le_length (le_refl h.length)]
  rw [e1, e2] at this
  have e3 : level h = i - s := by omega
  rw [e3] at this
  exact ht this

theorem ThR_psd (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) (hK : KrPSD D)
    (hD : DomMin D T Th) (i s : ℕ) (t : E) (Y : Finset (Pt E)) : PSDOn Y (ThR D T Th i s t) := by
  unfold ThR
  by_cases hc : (1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1) ∧
      good (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s)
  · obtain ⟨⟨hs, hsi, hi⟩, hg⟩ := id hc
    refine psd_congr (fun x _ y _ => ?_)
      (psd_restrict Y (majorantPSD E W D T Th hK hD i s hs hsi hi _ (sel_mem hg)))
    simp only [if_pos hc]
    first
    | exact if_congr Iff.rfl rfl rfl
    | (split_ifs <;> rfl)
  · refine psd_congr (fun x _ y _ => ?_) (psd_zero Y)
    simp only [if_neg hc]

theorem thetaDomination_dp_of_krPSD_of_domMin (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) (hK : KrPSD D)
    (hE : EBounds D) (hD : DomMin D T Th) : (Dp D T Th).ThetaDomination := by
  intro i s hs hsi hi
  obtain ⟨h1, h2, h3⟩ := hD i s hs hsi hi
  have hr : 1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1 := ⟨hs, hsi, hi⟩
  refine ⟨hE i (by omega) hi, ?_, ?_, ?_⟩
  · intro t _ Y _
    show PSDOn Y (fun h h' => ThR D T Th i s t h h' - blk (KrR D T i) s t t h h')
    by_cases ht : t ∈ T.Sg (i - s + 1) s
    · have hg : good (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s) :=
        ⟨t, ht, rfl⟩
      refine psd_restrict' Y (h1 t ht) (fun x y hxy => ?_) (fun x y hxy => ?_)
      · simp only [ThR, if_pos (And.intro hr hg), blk, KrR, join_mem T hs hsi ht, if_pos hxy]
        rw [h2 _ (sel_mem hg) t ht ((mk_eq_iff _ _ _).1 (sel_mk hg)) x hxy.1 y hxy.2]
      · simp only [ThR, blk, KrR, join_mem T hs hsi ht, if_neg hxy, ite_self, sub_zero]
    · refine psd_congr (fun x _ y _ => ?_) (ThR_psd D T Th hK hD i s t Y)
      simp only [blk, KrR, join_not_mem T ht, false_and, if_false, sub_zero]
  · intro t t' htt
    show ThR D T Th i s t = ThR D T Th i s t'
    have e : (t : E ⧸ D.La (i - s + 1) s) = t' := (mk_eq_iff _ _ _).2 htt
    funext h h'
    simp only [ThR, e]
  · intro S hS Y _
    show PSDOn Y (fun h h' => (1 + (D.e i : ℂ)) * KrR D T (i - s) h h' - ∑ t ∈ S, ThR D T Th i s t h h')
    set L := D.La (i - s + 1) s with hL
    set G := T.Sg (i - s + 1) s with hG
    set S' : Finset E := (S.filter (fun t : E => good L G (t : E ⧸ L))).image
      (fun t : E => sel L G (t : E ⧸ L)) with hS'
    have hsub : S' ⊆ G := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
      exact sel_mem (Finset.mem_filter.1 ht).2
    have hinc : ∀ t ∈ S', ∀ t' ∈ S', t - t' ∈ L → t = t' := by
      intro a ha b hb hab
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hb
      have e := (mk_eq_iff L _ _).2 hab
      rw [sel_mk (Finset.mem_filter.1 ht).2, sel_mk (Finset.mem_filter.1 ht').2] at e
      rw [e]
    have hinj : Set.InjOn (fun t : E => sel L G (t : E ⧸ L))
        (S.filter (fun t : E => good L G (t : E ⧸ L)) : Finset E) := by
      intro a ha b hb hab
      have ha' := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
      have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      have e : (a : E ⧸ L) = b := by
        rw [← sel_mk ha'.2, ← sel_mk hb'.2]; exact congrArg _ hab
      exact hS a ha'.1 b hb'.1 ((mk_eq_iff L _ _).1 e)
    refine psd_restrict' Y (h3 S' hsub hinc) (fun x y hxy => ?_) (fun x y hxy => ?_)
    · have hsum : ∑ t ∈ S, ThR D T Th i s t x y = ∑ t₁ ∈ S', Th i s t₁ x y := by
        rw [hS', Finset.sum_image (f := fun t₁ => Th i s t₁ x y) hinj, Finset.sum_filter]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hg : good L G (t : E ⧸ L)
        · simp only [ThR, if_pos hg, if_pos hxy]
          exact if_pos (And.intro hr hg)
        · have : ¬ ((1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1) ∧ good L G (t : E ⧸ L)) := fun h => hg h.2
          simp only [ThR, if_neg hg]
          exact if_neg this
      rw [hsum]
      simp only [KrR, if_pos hxy]
    · have : ∀ t ∈ S, ThR D T Th i s t x y = 0 := by
        intro t _
        simp only [ThR, if_neg hxy, ite_self]
      rw [Finset.sum_eq_zero this]
      simp only [if_neg hxy, KrR, mul_zero, sub_zero]

theorem Dp_Q (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) (ε : ℝ) (k : ℕ)
    (w : W) : (Dp D T Th).Q T ε k w = D.Q T ε k w := by
  unfold TB.Data.Q TB.Data.Sf
  have e : (∑ p ∈ T.X k, ∑ q ∈ T.X k, (Dp D T Th).Kr k p q * (Dp D T Th).gram ε k w p q) =
      ∑ p ∈ T.X k, ∑ q ∈ T.X k, D.Kr k p q * D.gram ε k w p q := by
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    show KrR D T k p q * _ = _
    unfold KrR
    rw [if_pos ⟨hp, hq⟩]
    try rfl
  rw [e]
  try rfl

theorem oneLevelAfterOfOld : OneLevelAfterOfOld := by
  intro hOL E W _ D ep C₄ hG hK hW hA2 hE hWv hP hLi hB hLa hep hC hv hv1 T hTh ε hε σ i hi1 hi hσ
    w hw
  obtain ⟨Th, hD⟩ := hTh
  have hA2' : (Dp D T Th).KernelSupport := by
    intro i s hs hsi hi h h' t t' hl hl' ht ht' htt hne
    refine hA2 i s hs hsi hi h h' t t' hl hl' ht ht' htt ?_
    intro h0
    apply hne
    show KrR D T i (join h s t) (join h' s t') = 0
    simp only [KrR, h0, ite_self]
  have hKP : (Dp D T Th).KernelPSD :=
    ⟨fun i Y => psd_restrict' Y (hK i (T.X i))
      (fun x y hxy => by show KrR D T i x y = _; simp only [KrR, if_pos hxy])
      (fun x y hxy => by show KrR D T i x y = _; simp only [KrR, if_neg hxy]), fun i s t Y => ThR_psd D T Th hK hD i s t Y⟩
  have h := hOL E W (Dp D T Th) ep C₄ hG hKP hW hA2' (thetaDomination_dp_of_krPSD_of_domMin D T Th hK hE hD) hWv hP hLi hB hLa
    hep hC hv hv1 T ε hε σ i hi1 hi
    (fun k hk => ⟨(hσ k hk).1, fun w hw => by rw [Dp_Q]; exact (hσ k hk).2 w hw⟩) w hw
  rw [Dp_Q] at h
  exact h

theorem oneLevelAfter : OneLevelAfter := oneLevelAfterOfOld one_level_inequality_split_by_size

end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1

namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.P.OneLevelCoefficients Finset
open scoped ComplexOrder

variable {E W : Type} [Field E]

theorem theoremAAfterOfSteps : TC.TheoremAAfterOfSteps := by
  intro hOL hLS hJ C₁ C₄ h1 h4
  set C₀ : ℝ := max (3 * C₁) (2 * C₄) with hC₀
  have hC01 : 1 ≤ C₀ := le_trans (by linarith) (le_max_left _ _)
  have hC03 : 3 * C₁ ≤ C₀ := le_max_left _ _
  have hC04 : 2 * C₄ ≤ C₀ := le_max_right _ _
  obtain ⟨C'J, CJ, hJ⟩ := hJ C₀ hC01
  refine ⟨max C₀ CJ, max (max C'J (3 * C₁)) 1, ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hK hf hΘ0 hC' hsm hS hG hKer hW hA2 hEB hDom hE72 hP hE73 hE74 hLat
    hE hCut hA4 R
  set C : ℝ := max C₀ CJ with hC
  have hCC0 : C₀ ≤ C := le_max_left _ _
  have hCCJ : CJ ≤ C := le_max_right _ _
  have hCpos : 0 ≤ C := by linarith
  have hΘ1 : 1 ≤ Θ := le_trans (le_max_right _ _) hC'
  have hΘ3 : 3 * C₁ ≤ Θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC'
  have hΘJ : C'J ≤ Θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC'
  set y : ℝ := Θ ^ (-((D.K : ℝ) - 5 / 2)) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hΘ0.le _
  have hK4 : (4 : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hK
  have hy1 : y ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΘ1 (by linarith)
  set ep : ℝ := (C₁ * y) ^ D.f with hep
  have hep0 : 0 ≤ ep := by positivity
  have ha : 3 ^ D.f * ep = (3 * C₁ * y) ^ D.f := by rw [hep, ← mul_pow, mul_assoc]
  have h3y : 3 * C₁ * y ≤ 1 := by
    calc 3 * C₁ * y ≤ Θ * Θ⁻¹ := mul_le_mul hΘ3 hy1 hy0 hΘ0.le
      _ = 1 := mul_inv_cancel₀ hΘ0.ne'
  have ha1 : 3 ^ D.f * ep ≤ 1 := by
    rw [ha]; exact pow_le_one₀ (by positivity) h3y
  have ha0 : 0 ≤ 3 ^ D.f * ep := by positivity
  have haC : 3 ^ D.f * ep ≤ (C₀ * y) ^ D.f := by
    rw [ha]; exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hC03 hy0) _
  have hb : 2 ^ D.f * ep ≤ 3 ^ D.f * ep :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _) hep0
  have he : ∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1 := hEB
  set e' : ℕ → ℝ := fun i => if 1 ≤ i ∧ i ≤ D.r + 1 then D.e i else 0 with he'
  have he'0 : ∀ i, 0 ≤ e' i := by
    intro i; simp only [he']; split_ifs with h
    · exact (he i h.1 h.2).1
    · exact le_rfl
  have hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + e' i) = ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) := by
    apply Finset.prod_congr rfl
    intro i hi; rw [Finset.mem_Icc] at hi
    simp only [he', if_pos hi]
  have hprod0 : 0 ≤ ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) := by
    apply Finset.prod_nonneg
    intro i hi; rw [Finset.mem_Icc] at hi
    have := (he i hi.1 hi.2).1; linarith
  have hx0 : 0 ≤ (C₀ / Θ) ^ D.f := by positivity
  have hxy : (C₀ / Θ) ^ D.f ≤ (C / Θ) ^ D.f :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hCC0 hΘ0.le) _
  have hr0 : (0 : ℝ) ≤ (D.r : ℝ) + 1 := by positivity
  have hBJ : 1 + CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f ≤ 1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f := by
    have s1 : CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f ≤ C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCCJ hr0) hx0
    have s2 : C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f ≤ C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f :=
      mul_le_mul_of_nonneg_left hxy (by positivity)
    linarith
  have hB0 : 0 ≤ 1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f := by positivity
  have hK0 : (TC.withTh D (fun _ _ _ _ _ => 0)).KernelPSD :=
    ⟨hKer, fun _ _ _ Y => by
      show Matrix.PosSemidef (0 : Matrix Y Y ℂ)
      exact Matrix.PosSemidef.zero⟩
  suffices key : ∀ (T : Tower E) (ε : ℝ), 0 < ε → ∀ σ₀ : ℝ,
      (∀ w ∈ D.Wb D.Ntop, (D.gram ε 0 w [] []).re / D.wt w ≤ σ₀) →
      D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1)) ≤
        ((1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i))) * σ₀ from
    hLS E W (TC.withTh D (fun _ _ _ _ _ => 0)) jn H Vt c hG hK0 hE hCut hA4 _ key R
  intro T ε hε σ₀ hσ₀
  have hempN : D.emp ∈ D.Wb D.Ntop := by
    simp [Data.Wb, D.emp_mem, D.cnt_emp]
  have hσ₀0 : 0 ≤ σ₀ := by
    refine le_trans ?_ (hσ₀ D.emp hempN)
    rw [D.wt_emp, div_one]; exact gram_diag D hG ε hε 0 D.emp []
  set S : ℕ → NNReal := fun k => (D.Wb (D.budget k)).sup (fun w => (D.Q T ε k w).toNNReal) with hSd
  set σ : ℕ → ℝ := fun k => √(S k : ℝ) with hσ
  have hσ0 : ∀ k, 0 ≤ σ k := fun k => Real.sqrt_nonneg _
  have hσsq : ∀ k, σ k ^ 2 = (S k : ℝ) := fun k => Real.sq_sqrt (NNReal.coe_nonneg _)
  have hσQ : ∀ k, ∀ w ∈ D.Wb (D.budget k), D.Q T ε k w ≤ σ k ^ 2 := by
    intro k w hw
    rw [hσsq]
    refine le_trans (Real.le_coe_toNNReal _) ?_
    exact_mod_cast Finset.le_sup (f := fun w => (D.Q T ε k w).toNNReal) hw
  have hSle : ∀ k (X : ℝ), 0 ≤ X → (∀ w ∈ D.Wb (D.budget k), D.Q T ε k w ≤ X) → (S k : ℝ) ≤ X := by
    intro k X hX h
    have : S k ≤ X.toNNReal := Finset.sup_le fun w hw => Real.toNNReal_le_toNNReal (h w hw)
    calc (S k : ℝ) ≤ (X.toNNReal : ℝ) := by exact_mod_cast this
      _ = X := Real.coe_toNNReal _ hX
  have hσle : ∀ k (X : ℝ), 0 ≤ X → (∀ w ∈ D.Wb (D.budget k), √(D.Q T ε k w) ≤ X) → σ k ≤ X := by
    intro k X hX h
    apply Real.sqrt_le_iff.mpr
    exact ⟨hX, hSle k _ (sq_nonneg X) fun w hw => (Real.sqrt_le_iff.mp (h w hw)).2⟩
  have hb0 : D.budget 0 = D.Ntop := by simp [Data.budget, Data.Ntop]
  have hσ00 : σ 0 ^ 2 ≤ σ₀ := by
    rw [hσsq]
    apply hSle 0 σ₀ hσ₀0
    intro w hw
    rw [Q0]; rw [hb0] at hw; exact hσ₀ w hw
  have hrec : ∀ i, 1 ≤ i → i ≤ D.r + 1 →
      σ i ≤ (1 + (C₀ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f) * √(1 + e' i) * σ (i - 1) +
        ∑ t ∈ Icc 2 i, ((C₀ / Θ) ^ D.f) ^ (t - 1) * σ (i - t) := by
    intro i hi1 hi
    have hei : e' i = D.e i := by simp only [he', if_pos (And.intro hi1 hi)]
    rw [hei]
    apply hσle i
    · apply add_nonneg
      · exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (hσ0 _)
      · exact Finset.sum_nonneg fun t _ => mul_nonneg (by positivity) (hσ0 _)
    intro w hw
    refine le_trans (hOL E W D ep C₄ hG hKer hW hA2 hEB hE72 hP hE73 hE74 hLat hep0 h4 hS.1
      (size_le_one D Θ hΘ1 hS) T (hDom T) ε hε σ i hi1 hi (fun k _ => ⟨hσ0 k, hσQ k⟩) w hw) ?_
    apply add_le_add
    · apply mul_le_mul_of_nonneg_right _ (hσ0 _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      have q1 : 0 ≤ 2 ^ D.f * ep := by positivity
      nlinarith
    · apply Finset.sum_le_sum
      intro s hs; rw [Finset.mem_Icc] at hs
      apply mul_le_mul_of_nonneg_right _ (hσ0 _)
      exact coef D Θ C₄ C₀ _ _ hΘ1 h4 hC04 hf hS ha0 ha1 (he i hi1 hi).1 (he i hi1 hi).2 i s hs.1 hs.2 hi
  have hfin := hJ (D.K : ℝ) Θ D.f D.r e' σ hK4 hf hΘJ
    (small D.r D.f C C₀ Θ hΘ0 (by linarith) hCC0 hsm) he'0 hσ0 hrec
  rw [hprod] at hfin
  have hempB : D.emp ∈ D.Wb (D.budget (D.r + 1)) := by
    simp [Data.Wb, D.emp_mem, D.cnt_emp]
  have hQ := hσQ (D.r + 1) D.emp hempB
  have hQS : D.Q T ε (D.r + 1) D.emp = D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1)) := by
    simp [Data.Q, D.wt_emp]
  rw [hQS] at hQ
  have hs0 : 0 ≤ σ 0 ^ 2 := sq_nonneg _
  calc D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1)) ≤ σ (D.r + 1) ^ 2 := hQ
    _ ≤ (1 + CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * σ 0 ^ 2 := hfin
    _ ≤ (1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * σ 0 ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBJ hprod0) hs0
    _ ≤ (1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * σ₀ :=
        mul_le_mul_of_nonneg_left hσ00 (mul_nonneg hB0 hprod0)

end Formalism.FourierDecayAlt.P.RecursionWithDensities.B2

namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate

theorem t_ProductOfEMax : ProductOfEMax := by
  intro r e sd h0 h1
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1),
    Finset.prod_eq_one (fun i hi => by rw [h0 i hi, add_zero]), one_mul, h1]

theorem t_DensLeTwo : DensLeTwo := by
  intro f n h
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have h' : (18 : ℝ) * f ≤ 2 ^ n := by exact_mod_cast h
  have hy : 0 < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hpos
  have hy1 : ((2 : ℝ) ^ n)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have hm := mul_le_mul_of_nonneg_left h' hy.le
  have hx : 12 * (f : ℝ) * ((2 : ℝ) ^ n)⁻¹ ≤ 2 / 3 := by nlinarith
  have hl := Real.log_two_gt_d9
  have h3 : Real.exp (12 * (f : ℝ) * ((2 : ℝ) ^ n)⁻¹) ≤ Real.exp (Real.log 2) :=
    Real.exp_le_exp.mpr (by linarith)
  rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h3

theorem t_DensSize : DensSize := by
  intro k r f h
  have hm : f + 5 ≤ k - 2 * r - 2 := by omega
  have hf : f < 2 ^ f := Nat.lt_two_pow_self
  calc 18 * f ≤ 32 * 2 ^ f := by omega
    _ = 2 ^ (f + 5) := by ring
    _ ≤ 2 ^ (k - 2 * r - 2) := Nat.pow_le_pow_right (by norm_num) hm

theorem t_SumBoundMax : SumBoundMax := by
  intro α Y k m sd hk h
  have h2 := B1.psd_smul (max sd 1 - sd) (by linarith [le_max_left sd 1]) hk
  refine B1.psd_congr (fun x _ y _ => ?_) (B1.psd_add h h2)
  push_cast
  ring

theorem t_RecursionWithDens : RecursionWithDens := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', hC⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c sd hR hC' hr h0 hmax R
  unfold RecHypAfter at hR
  obtain ⟨hK, hf, hΘ, hS, hG, hKr, hWd, hA2, hEb, hDA, hEW, hP, hEL, hEB, hLS, hEE, hCut, hA4⟩ := hR
  have hp := t_ProductOfEMax D.r D.e sd h0 hmax
  have hb := hC E W D Θ jn H Vt c hK hf hΘ hC' hr hS hG hKr hWd hA2 hEb hDA hEW hP hEL hEB hLS hEE
    hCut hA4 R
  rwa [hp] at hb

end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1

namespace Formalism.FourierDecayAlt.P

open RecursionWithDensities

theorem domination_minimum_of_text : Formalism.FourierDecayAlt.TC.DomMinOfText := RecursionWithDensities.B1.domMinOfText

theorem theorem_a_after : Formalism.FourierDecayAlt.TC.TheoremAAfter := RecursionWithDensities.B2.theoremAAfterOfSteps RecursionWithDensities.B1.oneLevelAfter limitStep joint_theorem_A'

theorem density_le_two : Formalism.FourierDecayAlt.TC.DensLeTwo := RecursionWithDensities.J1.t_DensLeTwo

theorem density_size : Formalism.FourierDecayAlt.TC.DensSize := RecursionWithDensities.J1.t_DensSize

theorem sum_bound_max : Formalism.FourierDecayAlt.TC.SumBoundMax := RecursionWithDensities.J1.t_SumBoundMax

theorem recursion_with_densities : Formalism.FourierDecayAlt.TC.RecursionWithDens := RecursionWithDensities.J1.t_RecursionWithDens

end Formalism.FourierDecayAlt.P
