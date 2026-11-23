module

public import Mathlib
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.Bundle0004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0012
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0008

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CarImpFrel
section
open Finset CompanionTheory.D.DSIC

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICFRel

def bil {ι A : Type} [Fintype ι] [Ring A] [Algebra ℂ A] (c a : ι → A) (m : ι → ι → ℂ) : A :=
  ∑ i, ∑ j, m i j • (c i * a j)

theorem pair_comm {ι A : Type} [DecidableEq ι] [Ring A] (c a : ι → A)
    (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i j k l : ι) :
    (c i * a j) * (c k * a l) - (c k * a l) * (c i * a j) =
      (if j = k then c i * a l else 0) - (if l = i then c k * a j else 0) := by
  have h1 : a j * c k = (if j = k then 1 else 0) - c k * a j := eq_sub_of_add_eq (hac j k)
  have h2 : a l * c i = (if l = i then 1 else 0) - c i * a l := eq_sub_of_add_eq (hac l i)
  have h3 : c k * c i = - (c i * c k) := eq_neg_of_add_eq_zero_left (hcc k i)
  have h4 : a l * a j = - (a j * a l) := eq_neg_of_add_eq_zero_left (haa l j)
  have e1 : (c i * a j) * (c k * a l) = (if j = k then c i * a l else 0) - (c i * c k) * (a j * a l) := by
    rw [mul_assoc, ← mul_assoc (a j), h1]
    split_ifs <;> noncomm_ring
  have e2 : (c k * a l) * (c i * a j) = (if l = i then c k * a j else 0) - (c k * c i) * (a l * a j) := by
    rw [mul_assoc, ← mul_assoc (a l), h2]
    split_ifs <;> noncomm_ring
  rw [e1, e2, h3, h4]
  noncomm_ring

theorem bil_comm {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] (c a : ι → A)
    (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (m m' : ι → ι → ℂ) :
    bil c a m * bil c a m' - bil c a m' * bil c a m =
      bil c a (fun i l => ∑ k, m i k * m' k l - ∑ k, m' i k * m k l) := by
  have e1 : bil c a m * bil c a m' =
      ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • ((c i * a j) * (c k * a l)) := by
    unfold bil
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm]
  have e2 : bil c a m' * bil c a m =
      ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • ((c k * a l) * (c i * a j)) := by
    unfold bil
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm, mul_comm (m' k l)]
  have e3 : ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • (if j = k then c i * a l else 0) =
      ∑ i, ∑ l, (∑ k, m i k * m' k l) • (c i * a l) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm (f := fun l k => (m i k * m' k l) • (c i * a l))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    simp
  have e4 : ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • (if l = i then c k * a j else 0) =
      ∑ i, ∑ l, (∑ k, m' i k * m k l) • (c i * a l) := by
    have : ∀ i j k, ∑ l, (m i j * m' k l) • (if l = i then c k * a j else 0) =
        (m' k i * m i j) • (c k * a j) := by
      intro i j k
      simp [mul_comm]
    simp only [this, Finset.sum_smul]
    calc ∑ i, ∑ j, ∑ k, (m' k i * m i j) • (c k * a j)
        = ∑ j, ∑ i, ∑ k, (m' k i * m i j) • (c k * a j) := Finset.sum_comm
      _ = ∑ j, ∑ k, ∑ i, (m' k i * m i j) • (c k * a j) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [e1, e2]
  simp only [← Finset.sum_sub_distrib, ← smul_sub, pair_comm c a haa hcc hac]
  simp only [smul_sub, Finset.sum_sub_distrib, e3, e4, bil, sub_smul]

variable {n : ℕ}

def dl (x y : Fin n) : ℂ := if x = y then 1 else 0

theorem dl_comm (x y : Fin n) : dl x y = dl y x := by
  simp only [dl, eq_comm]

def mm (c d : Fin n) (x y : Fin n × Fin n) : ℂ :=
  dl x.1 c * dl y.1 d * dl x.2 y.2 - dl x.2 d * dl y.2 c * dl x.1 y.1

theorem gop_eq (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (c d : Fin n) :
    (Gop ε c d : Module.End ℂ (Ch ε V)) = bil cre ann (fun i j : NC ε => mm c d i.1 j.1) := by
  unfold Gop bil
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [mm, dl, ite_and, mul_ite, mul_one, mul_zero]
  split_ifs <;> simp_all

theorem sum_pt (ε : Fin n → Bool) (x y : Fin n) (hx : ε x = true) (hy : ε y = false)
    (f : Fin n × Fin n → ℂ) : ∑ k : NC ε, dl k.1.1 x * dl k.1.2 y * f k.1 = f (x, y) := by
  rw [Finset.sum_eq_single (⟨(x, y), hx, hy⟩ : NC ε)]
  · simp [dl]
  · rintro ⟨⟨u, v⟩, h⟩ _ hne
    by_cases h1 : u = x
    · by_cases h2 : v = y
      · subst h1 h2; exact absurd rfl hne
      · simp [dl, h2]
    · simp [dl, h1]
  · simp

theorem sum_mm (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) (i : NC ε) (f : Fin n × Fin n → ℂ) :
    ∑ k : NC ε, mm a b i.1 k.1 * f k.1 = dl i.1.1 a * f (b, i.1.2) - dl i.1.2 b * f (i.1.1, a) := by
  have e : ∀ k : NC ε, mm a b i.1 k.1 * f k.1 =
      dl i.1.1 a * (dl k.1.1 b * dl k.1.2 i.1.2 * f k.1) - dl i.1.2 b * (dl k.1.1 i.1.1 * dl k.1.2 a * f k.1) := by
    intro k
    rw [mm, dl_comm i.1.2 k.1.2, dl_comm i.1.1 k.1.1]; ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  · by_cases h : i.1.1 = a
    · rw [sum_pt ε b i.1.2 (by rw [← hab, ← h]; exact i.2.1) i.2.2]
    · simp [dl, h]
  · by_cases h : i.1.2 = b
    · rw [sum_pt ε i.1.1 a i.2.1 (by rw [hab, ← h]; exact i.2.2)]
    · simp [dl, h]

theorem gop_rel (h : CAR) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] :
    KRel ε (Gop ε : Fin n → Fin n → Module.End ℂ (Ch ε V)) := by
  intro a b c d hab hcd
  have hr : ∀ (x y : Fin n) (T : Module.End ℂ (Ch ε V)), (if x = y then T else 0) = dl x y • T := by
    intro x y T; unfold dl; split_ifs <;> simp
  simp only [gop_eq, hr]
  rw [bil_comm cre ann (fun i j => (h n ε V i j).1) (fun i j => (h n ε V i j).2.1)
    (fun i j => by convert (h n ε V i j).2.2)]
  simp only [bil, Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, ← sub_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Finset.sum_sub_distrib, sum_mm ε a b hab i (fun k => mm c d k j.1), sum_mm ε c d hcd i (fun k => mm a b k j.1)]
  simp only [mm]
  rw [dl_comm b j.1.1, dl_comm d j.1.1, dl_comm a j.1.2, dl_comm c j.1.2, dl_comm a d, dl_comm c b]
  ring

section

variable {ε : Fin n → Bool} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem lift_gop (T : Module.End ℂ V) (c d : Fin n) :
    Commute (lift ε T : Module.End ℂ (Ch ε V)) (Gop ε c d) := by
  have ha : ∀ i : NC ε, Commute (lift ε T : Module.End ℂ (Ch ε V)) (ann i) := by
    intro i
    refine LinearMap.ext fun x => funext fun A => ?_
    by_cases h : i ∈ A <;> simp [ann, h]
  have hc : ∀ i : NC ε, Commute (lift ε T : Module.End ℂ (Ch ε V)) (cre i) := by
    intro i
    refine LinearMap.ext fun x => funext fun A => ?_
    by_cases h : i ∈ A <;> simp [cre, h]
  unfold Gop
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
    ((hc i).mul_right (ha j)).smul_right _

theorem lift_rel (E : Fin n → Fin n → Module.End ℂ V) (hE : KRel ε E) :
    KRel ε (fun c d => (lift ε (E c d) : Module.End ℂ (Ch ε V))) := by
  intro a b c d hab hcd
  refine LinearMap.ext fun x => funext fun A => ?_
  have := LinearMap.congr_fun (hE a b c d hab hcd) (x A)
  split_ifs at this ⊢ <;> simpa using this

end

theorem add_rel {A : Type} [Ring A] (ε : Fin n → Bool) (L G : Fin n → Fin n → A) (hL : KRel ε L) (hG : KRel ε G)
    (hc : ∀ a b c d, Commute (L a b) (G c d)) : KRel ε (fun c d => L c d + G c d) := by
  intro a b c d hab hcd
  have h1 := hL a b c d hab hcd
  have h2 := hG a b c d hab hcd
  have h3 := (hc a b c d).eq
  have h4 := (hc c d a b).eq
  have : (L a b + G a b) * (L c d + G c d) - (L c d + G c d) * (L a b + G a b) =
      (L a b * L c d - L c d * L a b) + (G a b * G c d - G c d * G a b) := by
    simp only [mul_add, add_mul, h3, h4]; abel
  simp only []
  rw [this, h1, h2]
  split_ifs <;> abel

theorem neg_rel {A : Type} [Ring A] (ε : Fin n → Bool) (G : Fin n → Fin n → A) (hG : KRel ε G) :
    KRel ε (fun c d => -G d c) := by
  intro a b c d hab hcd
  have h := hG b a d c hab.symm hcd.symm
  simp only [neg_mul_neg]
  rw [h]
  simp only [eq_comm (a := a) (b := d), eq_comm (a := c) (b := b)]
  split_ifs <;> abel

theorem frel_of_car (h : CAR) : FRel := by
  intro n ε V _ _ E hE
  refine ⟨add_rel ε _ _ (lift_rel E hE) (gop_rel h ε V) fun a b c d => lift_gop _ c d, ?_⟩
  have := add_rel ε _ _ (lift_rel E hE) (neg_rel ε _ (gop_rel h ε V)) fun a b c d => (lift_gop _ d c).neg_right
  simp only [← sub_eq_add_neg] at this
  exact this

theorem car_imp_frel : CompanionTheory.D.DSIC.CAR → CompanionTheory.D.DSIC.FRel := frel_of_car

end GlobalTheory.CompanionTheory.DSICFRel
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CardOther
section
open Finset
open CompanionTheory.D.DSIC

namespace GlobalTheory.CompanionTheory.GamDomProof

variable {n : ℕ}

theorem card_four (ε : Fin n → Bool) (a : Fin n) :
    ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) + (univ.filter fun b => b < a ∧ ε b = ε a).card
      + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card + 1 = n := by
  have h1 : (1 : ℝ) = ∑ b : Fin n, if b = a then (1 : ℝ) else 0 := by simp
  have h2 : (n : ℝ) = ∑ _b : Fin n, (1 : ℝ) := by simp
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [h2]
  nth_rewrite 5 [h1]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne', e]
  · simp [h]
  · by_cases e : ε b = ε a <;> simp [h, h.not_gt, h.ne, e]

theorem card_fst (ε : Fin n → Bool) (a : Fin n) :
    ((A1 ε).filter fun i => i.1.1 = a).card =
      if ε a = true then (univ.filter fun b => b < a ∧ ε b ≠ ε a).card else 0 := by
  split_ifs with h
  · refine card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi hx hy ⊢
      obtain ⟨h1, rfl⟩ := hi
      exact ⟨h1, by simp [hx, hy]⟩
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi ⟨⟨x', y'⟩, hx', hy'⟩ hi' e
      simp only [A1, mem_filter, mem_univ, true_and] at hi hi' e
      apply Subtype.ext
      simp [hi.2, hi'.2, e]
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      refine ⟨⟨(a, b), h, by simpa [h] using hb.2⟩, ?_, rfl⟩
      simp [A1, hb.1]
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨⟨x, y⟩, hx, hy⟩ _ e
    simp only at e hx
    exact h (e ▸ hx)

theorem card_snd (ε : Fin n → Bool) (a : Fin n) :
    ((A1 ε).filter fun i => i.1.2 = a).card =
      if ε a = true then 0 else (univ.filter fun b => a < b ∧ ε b ≠ ε a).card := by
  split_ifs with h
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨⟨x, y⟩, hx, hy⟩ _ e
    simp only at e hy
    rw [e, h] at hy
    exact absurd hy (by simp)
  · have h' : ε a = false := by simpa using h
    refine card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi hx hy ⊢
      obtain ⟨h1, rfl⟩ := hi
      exact ⟨h1, by simp [hx, hy]⟩
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi ⟨⟨x', y'⟩, hx', hy'⟩ hi' e
      simp only [A1, mem_filter, mem_univ, true_and] at hi hi' e
      apply Subtype.ext
      simp [hi.2, hi'.2, e]
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      refine ⟨⟨(b, a), by simpa [h'] using hb.2, h'⟩, ?_, rfl⟩
      simp [A1, hb.1]

theorem card_other (ε : Fin n → Bool) (a : Fin n) (h : ε a = true) :
    (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
      = nb ε false := by
  simp only [nb, card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h' | h' | h'
  · cases e : ε b <;> simp [h, h', h'.not_gt]
  · simp [← h', h]
  · cases e : ε b <;> simp [h, h', h'.not_gt]

theorem gam_eq (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    gam ε lam a = lam a - ((n : ℝ) - 1) / 2 + (univ.filter fun b => b < a ∧ ε b = ε a).card
      + (if ε a = true then (nb ε false : ℝ) else 0) := by
  have h4 := card_four ε a
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, wtA, Pi.add_apply, Pi.sub_apply,
    card_fst, card_snd]
  split_ifs with h
  · rw [← card_other ε a h]
    push_cast
    linarith
  · push_cast
    linarith

theorem pos_le (ε : Fin n → Bool) (m : Fin n → ℤ) (hm : StrictAnti m) (c d : Fin n) (hcd : c < d)
    (e : ε c = ε d) :
    m d + (univ.filter fun b => b < d ∧ ε b = ε d).card ≤
      m c + (univ.filter fun b => b < c ∧ ε b = ε c).card := by
  have h1 : (univ.filter fun b => b < d ∧ ε b = ε d).card ≤
      (univ.filter fun b => b < c ∧ ε b = ε c).card + (Ico c d).card := by
    refine le_trans (card_le_card ?_) (card_union_le _ _)
    intro b hb
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_Ico] at hb ⊢
    rcases lt_or_ge b c with h | h
    · exact Or.inl ⟨h, hb.2.trans e.symm⟩
    · exact Or.inr ⟨h, hb.1⟩
  have h2 : (Ico c d).card ≤ (Ioc (m d) (m c)).card := by
    refine card_le_card_of_injOn m ?_ hm.injective.injOn
    intro b hb
    simp only [coe_Ico, coe_Ioc, Set.mem_Ico, Set.mem_Ioc] at hb ⊢
    exact ⟨hm hb.2, hm.antitone hb.1⟩
  rw [Int.card_Ioc] at h2
  have h3 := hm hcd
  omega

theorem gamDom : CompanionTheory.D.DSIC.GamDom := by
  intro n ε lam ⟨hanti, hint⟩
  choose m hm using hint
  have hm' : StrictAnti m := by
    intro a b hab
    have := hanti hab
    have h : (m b : ℝ) < m a := by rw [← hm, ← hm]; linarith
    exact_mod_cast h
  refine ⟨fun a => m a + (univ.filter fun b => b < a ∧ ε b = ε a).card
    + (if ε a = true then (nb ε false : ℤ) else 0), fun a => ?_, fun c d hcd e => ?_⟩
  · rw [gam_eq, hm]
    push_cast
    rfl
  · have := pos_le ε m hm' c d hcd e
    have h2 : (if ε d = true then (nb ε false : ℤ) else 0) = (if ε c = true then (nb ε false : ℤ) else 0) := by
      rw [e]
    simp only [h2]
    linarith

end GlobalTheory.CompanionTheory.GamDomProof
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasisStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroups_neighborhood_basis : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (U : Set (GL (Fin n) L)), IsOpen U → (1 : GL (Fin n) L) ∈ U → ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r ≤ ε → (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.congK_cofinal | exact GlobalTheory.CompanionTheory.CartGL.congK_cofinal | (intros; apply GlobalTheory.CompanionTheory.CartGL.congK_cofinal <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreApply
section
open Finset CompanionTheory.D.DSIC

noncomputable section

namespace GlobalTheory.CompanionTheory.ChainCAR

variable {n : ℕ} {ε : Fin n → Bool}

theorem key_inj {i j : NC ε} (h : key i = key j) : i = j := by
  unfold key at h
  have hi := i.1.2.2
  have hj := j.1.2.2
  have hn : 0 < n := by omega
  have h2 : (i.1.2 : ℕ) = j.1.2 := by
    have := congrArg (· % n) h
    simpa [Nat.mul_add_mod_of_lt hi, Nat.mul_add_mod_of_lt hj] using this
  have h1 : (i.1.1 : ℕ) = j.1.1 := by
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right hn (Nat.add_right_cancel h)
  exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))

def tw (i j : NC ε) : ℂ := if key j < key i then -1 else 1

theorem tw_self (i : NC ε) : tw i i = 1 := by simp [tw]

theorem tw_mul_self (i j : NC ε) : tw i j * tw i j = 1 := by
  unfold tw; split_ifs <;> simp

theorem tw_swap {i j : NC ε} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : key i ≠ key j := fun e => h (key_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

theorem sg_mul_self (i : NC ε) (A : Finset (NC ε)) : sg i A * sg i A = 1 := by
  unfold sg
  rw [← mul_pow]; simp

theorem sg_insert (i : NC ε) {j : NC ε} {A : Finset (NC ε)} (h : j ∉ A) :
    sg i (insert j A) = tw i j * sg i A := by
  unfold sg tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

theorem sg_erase (i : NC ε) {j : NC ε} {A : Finset (NC ε)} (h : j ∈ A) :
    sg i (A.erase j) = tw i j * sg i A := by
  have h1 := sg_insert i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_apply (i : NC ε) (x : Ch ε V) (A : Finset (NC ε)) :
    ann i x A = if i ∈ A then 0 else sg i A • x (insert i A) := rfl

theorem cre_apply (i : NC ε) (x : Ch ε V) (A : Finset (NC ε)) :
    cre i x A = if i ∈ A then sg i A • x (A.erase i) else 0 := rfl

theorem ann_ann (i j : NC ε) : (ann i * ann j + ann j * ann i : Module.End ℂ (Ch ε V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    ann_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert j hi, sg_insert i hj, tw_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sg i A * (-tw i j * sg j A) + sg j A * (tw i j * sg i A) = 0 := by ring
  rw [this, zero_smul]

theorem cre_cre (i j : NC ε) : (cre i * cre j + cre j * cre i : Module.End ℂ (Ch ε V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    cre_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]
  rw [sg_erase j hi, sg_erase i hj, tw_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sg i A * (-tw i j * sg j A) + sg j A * (tw i j * sg i A) = 0 := by ring
  rw [this, zero_smul]

theorem ann_cre (i j : NC ε) :
    (ann i * cre j + cre j * ann i : Module.End ℂ (Ch ε V)) = if i = j then 1 else 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, ann_apply, cre_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ A
    · simp [hi, sg_erase i hi, tw_self, smul_smul, sg_mul_self, Finset.insert_erase hi]
    · simp [hi, sg_insert i hi, tw_self, smul_smul, sg_mul_self, Finset.erase_insert hi]
  have hji : j ≠ i := fun e => hij e.symm
  rw [if_neg hij, LinearMap.zero_apply, Pi.zero_apply]
  by_cases hi : i ∈ A
  · simp [hi, hij]
  by_cases hj : j ∈ A
  swap
  · simp [hj, hji]
  simp only [hi, hj, Finset.mem_insert, Finset.mem_erase, or_true, and_false, if_true, if_false]
  rw [sg_insert j hi, sg_erase i hj, tw_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul,
    ← add_smul]
  have : sg i A * (-tw i j * sg j A) + sg j A * (tw i j * sg i A) = 0 := by ring
  rw [this, zero_smul]

theorem car : CompanionTheory.D.DSIC.CAR := fun _ _ _ _ _ i j => ⟨ann_ann i j, cre_cre i j, ann_cre i j⟩

end GlobalTheory.CompanionTheory.ChainCAR
end
end

