module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0102

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadColumnWeights
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional.ColumnWeights

theorem getD_flatMap_append {α : Type} (F : α → List ℚ) (s : ℕ) (hF : ∀ a, (F a).length = s) (t : List ℚ) :
    ∀ (l : List α) (j q : ℕ) (hj : j < l.length), q < s →
      (l.flatMap F ++ t).getD (j * s + q) 0 = (F l[j]).getD q 0 := by
  intro l
  induction l with
  | nil =>
    intro j q hj _
    simp at hj
  | cons a l ih =>
    intro j q hj hq
    cases j with
    | zero =>
      rw [List.flatMap_cons, List.append_assoc, zero_mul, zero_add,
        List.getD_append _ _ _ _ (by rw [hF]; exact hq)]
      rfl
    | succ j =>
      rw [List.flatMap_cons, List.append_assoc,
        List.getD_append_right _ _ _ _ (by rw [hF]; nlinarith), hF]
      have e : (j + 1) * s + q - s = j * s + q := by rw [add_mul]; omega
      rw [e]
      exact ih j q (by simpa using hj) hq

theorem flatMap_sublist {α β : Type} (F G : α → List β) (h : ∀ a, (F a).Sublist (G a)) :
    ∀ l : List α, (l.flatMap F).Sublist (l.flatMap G)
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h a).append (flatMap_sublist F G h l)

variable {S : Sizes}

theorem small_sublist (Q : Entries S) : Q.smallPar.Sublist Q.orderList := by
  unfold Entries.smallPar Entries.basePar Entries.orderList
  rw [← List.append_assoc]
  refine List.Sublist.append (List.Sublist.append (List.Sublist.cons _ ?_) ?_) (List.Sublist.refl _)
  · exact flatMap_sublist _ _ (fun a => List.sublist_append_left _ _) _
  · rw [List.map_eq_flatMap]
    exact flatMap_sublist _ _ (fun a => by simp) _

theorem small_int (Q : Entries S) : ∀ x ∈ Q.smallPar, ∃ z : ℤ, x = z := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨j, -, h⟩ := List.mem_flatMap.1 h
    exact block_odd (Q.c j) S.s_odd x h
  · exact base_int Q x h

def ent (Q : Entries S) (j : ℕ) : ℤ := ⌊Q.smallPar.getD j 0⌋

theorem ent_cast (Q : Entries S) (j : ℕ) (hj : j < S.nC S.m) : (ent Q j : ℚ) = Q.smallPar.getD j 0 := by
  rw [← length_small Q] at hj
  obtain ⟨z, hz⟩ := small_int Q _ (List.getElem_mem hj)
  rw [ent, List.getD_eq_getElem _ _ hj, hz, Int.floor_intCast]

theorem ent_succ (Q : Entries S) (hQ : Q.Good) (j : ℕ) (hj : j + 1 < S.nC S.m) : ent Q (j + 1) < ent Q j := by
  have h := List.pairwise_iff_getElem.1 (hQ.order.sublist (small_sublist Q)) j (j + 1)
    (by rw [length_small]; omega) (by rw [length_small]; omega) (by omega)
  have h1 := ent_cast Q j (by omega)
  have h2 := ent_cast Q (j + 1) hj
  rw [List.getD_eq_getElem _ _ (by rw [length_small]; omega)] at h1 h2
  rw [← h1, ← h2] at h
  exact_mod_cast h

theorem ent_add (Q : Entries S) (hQ : Q.Good) (j : ℕ) : ∀ d : ℕ, j + d < S.nC S.m → ent Q (j + d) + d ≤ ent Q j := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := ent_succ Q hQ (j + d) (by omega)
    rw [← add_assoc]
    push_cast
    omega

theorem nC_le {i : ℕ} (hi : i ≤ S.m) : S.nC i ≤ S.nC S.m := by
  unfold Sizes.nC
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _

def kap (Q : Entries S) (hQ : Q.Good) (i : Fin (S.m + 1)) : DomWeight (S.nC i) where
  w r := -ent Q (S.nC S.m - 1 - r) + (r : ℕ) + 1 - ((S.nC i + 1) / 2 : ℕ)
  anti a b hab := by
    have h1 : S.nC i ≤ S.nC S.m := nC_le (by omega)
    have ha := a.2
    have hb := b.2
    have hab' : (a : ℕ) ≤ b := hab
    have h := ent_add Q hQ (S.nC S.m - 1 - b) (b - a) (by omega)
    have e : S.nC S.m - 1 - b + (b - a) = S.nC S.m - 1 - a := by omega
    rw [e] at h
    simp only
    omega

theorem ent_block (Q : Entries S) (j : Fin S.m) (q a : ℕ) (ha : S.s = 2 * a + 1) (hq : q < S.s) :
    ent Q (j * S.s + q) = Q.c j + a - q := by
  have h := getD_flatMap_append (fun i : Fin S.m => block (Q.c i) S.s) S.s (fun _ => length_block _ _) Q.basePar
    (List.finRange S.m) j q (by simp) hq
  rw [ent, Entries.smallPar, h, List.getD_eq_getElem _ _ (by rw [length_block]; exact hq)]
  simp only [block, List.getElem_map, List.getElem_range, List.getElem_finRange, Fin.cast_mk, Fin.eta]
  have : (Q.c j : ℚ) + ((S.s : ℚ) - 1) / 2 - q = ((Q.c j + a - q : ℤ) : ℚ) := by
    rw [ha]; push_cast; ring
  rw [this, Int.floor_intCast]

theorem ent_base (Q : Entries S) (q : ℕ) : ent Q (S.m * S.s + q) = ⌊Q.basePar.getD q 0⌋ := by
  have hl : ((List.finRange S.m).flatMap fun i => block (Q.c i) S.s).length = S.m * S.s := by
    simp [List.length_flatMap, length_block]
  rw [ent, Entries.smallPar, List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]

theorem hw_odd (p : List ℚ) (a : ℕ) (ha : p.length = 2 * a + 1) (i : ℕ) : hw p i = ⌊p.getD i 0⌋ - a + i := by
  have : p.getD i 0 - (((p.length : ℚ) - 1) / 2 - i) = p.getD i 0 + ((-a + i : ℤ) : ℚ) := by
    rw [ha]; push_cast; ring
  rw [hw, this, Int.floor_add_intCast]; ring

theorem exists_column_weights (S : Sizes) (Q : Entries S) (hQ : Q.Good) :
    ∃ kap : ∀ i : Fin (S.m + 1), DomWeight (S.nC i), (∀ r, (kap 0).dual.w r = hw Q.basePar r) ∧
      (∀ r, (kap (Fin.last _)).dual.w r = hw Q.smallPar r) ∧
      ∀ i : Fin S.m, StepW (Q.c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (-Q.c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ))
        (kap i.castSucc) (kap i.succ) := by
  refine ⟨kap Q hQ, fun r => ?_, fun r => ?_, fun i r => ?_⟩
  · obtain ⟨r, hr⟩ := r
    obtain ⟨a, ha⟩ : Odd (S.nC 0) := odd_nC ⟨0, rfl⟩
    have h0 : S.nC S.m = S.m * S.s + S.nC 0 := by unfold Sizes.nC; omega
    simp only [DomWeight.dual, kap, Fin.val_rev, Fin.val_zero] at hr ⊢
    have e : S.nC S.m - 1 - (S.nC 0 - (r + 1)) = S.m * S.s + r := by omega
    rw [e, ent_base, hw_odd _ a (by rw [length_base, ha])]
    omega
  · obtain ⟨r, hr⟩ := r
    obtain ⟨a, ha⟩ : Odd (S.nC S.m) := odd_nC S.m_even
    simp only [DomWeight.dual, kap, Fin.val_rev, Fin.val_last] at hr ⊢
    have e : S.nC S.m - 1 - (S.nC S.m - (r + 1)) = r := by omega
    rw [e, hw_odd _ a (by rw [length_small, ha]), ent]
    omega
  · obtain ⟨r, hr⟩ := r
    simp only [kap, Fin.val_succ, Fin.val_castSucc] at hr ⊢
    split_ifs with h
    · ring
    · obtain ⟨a, ha⟩ := S.s_odd
      have h1 : S.nC (i + 1) = S.nC i + S.s := by unfold Sizes.nC; ring
      have h2 : S.nC S.m = S.nC (i + 1) + (i.rev : ℕ) * S.s := by
        have : S.m = i + 1 + (i.rev : ℕ) := by rw [Fin.val_rev]; have := i.2; omega
        unfold Sizes.nC
        rw [add_assoc _ ((i + 1) * S.s), ← add_mul, ← this]
      have e : S.nC S.m - 1 - r = (i.rev : ℕ) * S.s + (S.nC (i + 1) - 1 - r) := by omega
      rw [e, ent_block Q i.rev _ a ha (by omega)]
      omega

end GlobalTheory.OneFunctional.ColumnWeights
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadRowWeights
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional.RowWeights

def Follows (f g : List ℚ) : Prop :=
  f.Pairwise (· > ·) → g.Pairwise (· > ·) ∧ (∀ x ∈ g, ∃ l ∈ f, l - 1 / 2 ≤ x) ∧ ∀ x ∈ g, ∃ h ∈ f, x ≤ h - 1 / 2

theorem Follows.append {f g f' g' : List ℚ} (h : Follows f g) (h' : Follows f' g') : Follows (f ++ f') (g ++ g') := by
  intro hp
  rw [List.pairwise_append] at hp
  obtain ⟨p1, p2, p3⟩ := hp
  obtain ⟨a1, a2, a3⟩ := h p1
  obtain ⟨b1, b2, b3⟩ := h' p2
  refine ⟨List.pairwise_append.2 ⟨a1, b1, fun x hx y hy => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨l, hl, hlx⟩ := a2 x hx
    obtain ⟨u, hu, huy⟩ := b3 y hy
    have := p3 l hl u hu
    linarith
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨l, hl, hlx⟩ := a2 x hx
      exact ⟨l, List.mem_append_left _ hl, hlx⟩
    · obtain ⟨l, hl, hlx⟩ := b2 x hx
      exact ⟨l, List.mem_append_right _ hl, hlx⟩
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨l, hl, hlx⟩ := a3 x hx
      exact ⟨l, List.mem_append_left _ hl, hlx⟩
    · obtain ⟨l, hl, hlx⟩ := b3 x hx
      exact ⟨l, List.mem_append_right _ hl, hlx⟩

theorem Follows.flatMap {α : Type} {f g : α → List ℚ} (h : ∀ i, Follows (f i) (g i)) (L : List α) :
    Follows (L.flatMap f) (L.flatMap g) := by
  induction L with
  | nil => intro _; simp
  | cons a L ih => rw [List.flatMap_cons, List.flatMap_cons]; exact (h a).append ih

theorem mem_block {x y : ℚ} {n : ℕ} : y ∈ block x n ↔ ∃ i : ℕ, i < n ∧ x + ((n : ℚ) - 1) / 2 - i = y := by
  simp [block]

theorem block_pairwise (x : ℚ) (n : ℕ) : (block x n).Pairwise (· > ·) := by
  rw [block, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} hab => ?_
  have : (a : ℚ) < b := by exact_mod_cast hab
  change _ < _
  linarith

theorem half_le {z w : ℤ} (h : (z : ℚ) + 1 / 2 < w) : (z : ℚ) + 1 / 2 ≤ w - 1 / 2 := by
  have h1 : (z : ℚ) < w := by linarith
  have h2 : z + 1 ≤ w := by exact_mod_cast h1
  have h3 : (z : ℚ) + 1 ≤ w := by exact_mod_cast h2
  linarith

theorem follows_block_append (c : ℤ) {s : ℕ} (hs : Odd s) {a : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) :
    Follows (block c s ++ [a]) (block c (s - 1) ++ [a]) := by
  obtain ⟨r, rfl⟩ := hs
  obtain ⟨z, rfl⟩ := ha
  intro hp
  rw [List.pairwise_append] at hp
  have hbot : (z : ℚ) + 1 / 2 < c - r :=
    hp.2.2 _ (mem_block.2 ⟨2 * r, by omega, by push_cast; ring⟩) _ (List.mem_singleton_self _)
  have htop : ((c : ℚ) + r) ∈ block c (2 * r + 1) := mem_block.2 ⟨0, by omega, by push_cast; ring⟩
  have hb : ∀ x ∈ block (c : ℚ) (2 * r + 1 - 1), (c : ℚ) - r ≤ x ∧ x ≤ c + r - 1 / 2 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_block.1 hx
    have h1 : ((i + 1 : ℕ) : ℚ) ≤ ((2 * r : ℕ) : ℚ) := by exact_mod_cast (by omega : i + 1 ≤ 2 * r)
    have h2 : (0 : ℚ) ≤ i := by positivity
    rw [Nat.add_sub_cancel]
    push_cast at h1 ⊢
    constructor <;> linarith
  refine ⟨List.pairwise_append.2 ⟨block_pairwise _ _, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩,
    fun x hx => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩,
    fun x hx => ⟨_, List.mem_append_left _ htop, ?_⟩⟩
  · rw [List.mem_singleton.1 hy]
    have := (hb x hx).1
    change _ < _
    linarith
  · rcases List.mem_append.1 hx with hx | hx
    · have := (hb x hx).1
      linarith
    · rw [List.mem_singleton.1 hx]; linarith
  · rcases List.mem_append.1 hx with hx | hx
    · exact (hb x hx).2
    · rw [List.mem_singleton.1 hx]
      have h2 : (0 : ℚ) ≤ r := by positivity
      have := half_le (z := z) (w := c + r) (by push_cast; linarith)
      push_cast at this
      exact this

theorem follows_pair_singleton (v : ℤ) {u : ℚ} (hu : ∃ z : ℤ, u = z + 1 / 2) : Follows [(v : ℚ), u] [u] := by
  obtain ⟨z, rfl⟩ := hu
  intro hp
  have h : (z : ℚ) + 1 / 2 < v := by simpa using hp
  refine ⟨List.pairwise_singleton _ _, fun x hx => ⟨z + 1 / 2, by simp, ?_⟩, fun x hx => ⟨v, by simp, ?_⟩⟩
  · rw [List.mem_singleton.1 hx]; linarith
  · rw [List.mem_singleton.1 hx]; exact half_le h

theorem follows_cons_block_succ (b e : ℤ) {t : ℕ} (ht : Odd t) :
    Follows ((-b : ℚ) :: block (-e) t) (block (-e) (t + 1)) := by
  obtain ⟨r, rfl⟩ := ht
  intro hp
  rw [List.pairwise_cons] at hp
  have htop : (-e + r : ℚ) < -b := hp.1 _ (mem_block.2 ⟨0, by omega, by push_cast; ring⟩)
  have htop' : (-e + r + 1 : ℚ) ≤ -b := by
    have : -e + r + 1 ≤ -b := by exact_mod_cast htop
    exact_mod_cast this
  have hbot : (-e - r : ℚ) ∈ block (-e) (2 * r + 1) := mem_block.2 ⟨2 * r, by omega, by push_cast; ring⟩
  refine ⟨block_pairwise _ _, fun x hx => ⟨_, List.mem_cons_of_mem _ hbot, ?_⟩, fun x hx => ⟨_, List.mem_cons_self, ?_⟩⟩
  · obtain ⟨i, hi, rfl⟩ := mem_block.1 hx
    have h1 : ((i : ℕ) : ℚ) ≤ ((2 * r + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : i ≤ 2 * r + 1)
    push_cast at h1 ⊢
    linarith
  · obtain ⟨i, hi, rfl⟩ := mem_block.1 hx
    have h2 : (0 : ℚ) ≤ i := by positivity
    push_cast
    linarith

variable {S : Sizes}

theorem bigPar_pairwise (Q : Entries S) (hQ : Q.Good) : Q.bigPar.Pairwise (· > ·) := by
  have h1 := Follows.flatMap (fun i => follows_block_append (Q.c i) S.s_odd (hQ.a_half i.succ)) (List.finRange S.m)
  have h2 := Follows.flatMap (fun i => follows_pair_singleton (Q.v i) (hQ.u_half i)) (List.finRange (S.k - 1))
  have h3 := Follows.flatMap (fun j => follows_cons_block_succ (Q.b j) (Q.e j) S.t_odd) (List.finRange S.m)
  have ho := hQ.order
  rw [Entries.orderList, List.cons_append, List.cons_append, List.pairwise_cons] at ho
  obtain ⟨p1, -, p3⟩ := (h1.append h2).append h3 ho.2
  rw [← List.map_eq_flatMap] at p1 p3
  rw [Entries.bigPar, Entries.psiPar, List.cons_append, List.cons_append, List.pairwise_cons]
  refine ⟨fun x hx => ?_, p1⟩
  obtain ⟨u, hu, hxu⟩ := p3 x hx
  have := ho.1 u hu
  change _ < _
  linarith

theorem hw_big_anti (Q : Entries S) (hQ : Q.Good) {i j : ℕ} (hij : i ≤ j) (hj : j < Q.bigPar.length) :
    hw Q.bigPar j ≤ hw Q.bigPar i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    refine le_trans ?_ (ih (by omega))
    have h1 := hw_big Q hQ j (by omega)
    have h2 := hw_big Q hQ (j + 1) hj
    have h3 : Q.bigPar[j] > Q.bigPar[j + 1] :=
      List.pairwise_iff_getElem.1 (bigPar_pairwise Q hQ) j (j + 1) (by omega) hj (by omega)
    have h4 : (hw Q.bigPar (j + 1) : ℚ) < hw Q.bigPar j + 1 := by
      rw [h1, h2]; push_cast; linarith
    have h5 : hw Q.bigPar (j + 1) < hw Q.bigPar j + 1 := by exact_mod_cast h4
    omega

theorem getElem?_flatMap {α β : Type} (f : α → List β) (n : ℕ) (hf : ∀ a, (f a).length = n) (L : List α) (j r : ℕ)
    (hj : j < L.length) (hr : r < n) : (L.flatMap f)[j * n + r]? = (f L[j])[r]? := by
  induction L generalizing j with
  | nil => simp at hj
  | cons a L ih =>
    rw [List.flatMap_cons]
    cases j with
    | zero => rw [List.getElem?_append_left (by rw [hf]; omega)]; simp
    | succ j =>
      rw [List.getElem?_append_right (by rw [hf]; nlinarith), hf,
        show (j + 1) * n + r - n = j * n + r by rw [add_mul]; omega, ih j (by simpa using hj)]
      simp

theorem nR_mono {i j : ℕ} (h : i ≤ j) : S.nR i ≤ S.nR j := by
  unfold Sizes.nR
  have := Nat.mul_le_mul_right (S.t + 1) h
  omega

theorem nR_succ (j : ℕ) : S.nR (j + 1) = S.nR j + (S.t + 1) := by
  unfold Sizes.nR; ring

theorem cast_half (j : ℕ) : ((S.nR j / 2 : ℕ) : ℚ) = (S.nR j : ℚ) / 2 := by
  obtain ⟨r, hr⟩ := even_nR (S := S) j
  rw [hr, show (r + r) / 2 = r by omega]
  push_cast; ring

theorem bigPar_block (Q : Entries S) (j : Fin S.m) (r : ℕ) (hr : r < S.t + 1) (h : S.nR j + r < Q.bigPar.length) :
    Q.bigPar[S.nR j + r] = -Q.e j + (S.t : ℚ) / 2 - r := by
  have h1 : Q.bigPar[S.nR j + r]? = some (-Q.e j + (S.t : ℚ) / 2 - r) := by
    rw [Entries.bigPar, List.getElem?_append_right (by rw [length_psi]; unfold Sizes.nR; omega), length_psi,
      show S.nR j + r - S.nR 0 = j * (S.t + 1) + r by unfold Sizes.nR; omega,
      getElem?_flatMap _ (S.t + 1) (fun a => length_block _ _) _ _ _ (by simp) hr]
    simp [block, hr]
  rw [List.getElem?_eq_getElem h] at h1
  exact Option.some.inj h1

theorem exists_row_weights (S : Sizes) (Q : Entries S) (hQ : Q.Good) :
    ∃ lam : ∀ j : Fin (S.m + 1), DomWeight (S.nR j), (∀ i, (lam 0).w i = hw Q.psiPar i) ∧
      (∀ i, (lam (Fin.last _)).w i = hw Q.bigPar i) ∧
      ∀ j : Fin S.m, StepW (Q.e j - (S.nR j.succ / 2 : ℕ)) (-Q.e j + (S.nR j.castSucc / 2 : ℕ))
        (lam j.castSucc) (lam j.succ) := by
  have hlen : ∀ (j : Fin (S.m + 1)) (i : Fin (S.nR j)), i.1 < Q.bigPar.length := fun j i => by
    rw [length_big]
    exact lt_of_lt_of_le i.2 (nR_mono (Nat.lt_succ_iff.1 j.2))
  refine ⟨fun j => ⟨fun i => hw Q.bigPar i + (S.nR S.m / 2 : ℕ) - (S.nR j / 2 : ℕ), fun i i' hi => ?_⟩,
    fun i => ?_, fun i => ?_, fun j i => ?_⟩
  · have := hw_big_anti Q hQ (i := i) (j := i') hi (hlen j i')
    dsimp only
    omega
  · have hi : i.1 < Q.psiPar.length := by rw [length_psi]; exact i.2
    have h1 := hw_big Q hQ i (hlen 0 i)
    have h2 := hw_psi Q hQ i hi
    have h3 : Q.bigPar[i.1]'(hlen 0 i) = Q.psiPar[i.1] := List.getElem_append_left hi
    rw [h3, length_big] at h1
    rw [length_psi] at h2
    have : ((hw Q.bigPar i + (S.nR S.m / 2 : ℕ) - (S.nR 0 / 2 : ℕ) : ℤ) : ℚ) = hw Q.psiPar i := by
      rw [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_natCast, cast_half, cast_half, h1, h2]
      ring
    exact_mod_cast this
  · simp
  · dsimp only
    split_ifs with h
    · ring
    · have hi := i.2
      simp only [Fin.val_succ, Fin.val_castSucc, nR_succ] at hi h
      obtain ⟨r, hr⟩ : ∃ r, i.1 = S.nR j + r := ⟨i.1 - S.nR j, by omega⟩
      have h0 := hlen j.succ i
      have h1 := hw_big Q hQ i h0
      have h2 : Q.bigPar[i.1] = -Q.e j + (S.t : ℚ) / 2 - r := by
        rw [← bigPar_block Q j r (by omega) (hr ▸ h0)]
        simp only [hr]
      rw [h2, length_big] at h1
      have : ((hw Q.bigPar i + (S.nR S.m / 2 : ℕ) - (S.nR (j + 1) / 2 : ℕ) : ℤ) : ℚ) =
          ((-Q.e j + (S.nR j / 2 : ℕ) : ℤ) : ℚ) := by
        rw [Int.cast_sub, Int.cast_add, Int.cast_add, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, cast_half,
          cast_half, cast_half, h1, nR_succ, hr]
        push_cast
        ring
      exact_mod_cast this

end GlobalTheory.OneFunctional.RowWeights
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorMvPolynomialProdEquiv
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

noncomputable section

namespace GlobalTheory.PolyTensor

theorem curry_sum_mapDomain {ι β : Type} [Fintype ι] (v : ι → (β →₀ ℕ)) (τ : ι) :
    (∑ σ, Finsupp.mapDomain (fun x => (σ, x)) (v σ)).curry τ = v τ := by
  classical
  ext x
  rw [Finsupp.curry_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply_of_injective (fun a b h => (Prod.mk.inj h).2) (v τ) x
  · intro σ _ hσ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨y, hy⟩
    exact hσ (congrArg Prod.fst hy)
  · intro h
    exact absurd (Finset.mem_univ τ) h

def expEquiv (ι σ : Type) [Fintype ι] : (ι → (σ →₀ ℕ)) ≃ (ι × σ →₀ ℕ) :=
  Equiv.ofBijective (fun v => ∑ τ, Finsupp.mapDomain (fun x => (τ, x)) (v τ)) <| by
    classical
    refine ⟨fun v w h => funext fun τ => ?_, fun m => ⟨fun τ => m.curry τ, ?_⟩⟩
    · rw [← curry_sum_mapDomain v τ, ← curry_sum_mapDomain w τ]
      exact congrArg (fun m : ι × σ →₀ ℕ => m.curry τ) h
    · ext ⟨τ, x⟩
      have := DFunLike.congr_fun (curry_sum_mapDomain (fun τ => m.curry τ) τ) x
      simpa only [Finsupp.curry_apply] using this

theorem exists_piTensor_equiv : ∀ (ι σ : Type) [Fintype ι],
    ∃ e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ,
      ∀ f : ι → MvPolynomial σ ℂ,
        e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  intro ι σ _
  classical
  let bT := Basis.piTensorProduct (fun _ : ι => MvPolynomial.basisMonomials σ ℂ)
  let e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
    bT.equiv (MvPolynomial.basisMonomials (ι × σ) ℂ) (expEquiv ι σ)

  have key : e.toLinearMap.compMultilinearMap (PiTensorProduct.tprod ℂ) =
      (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
        (fun τ => (rename (Prod.mk τ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (ι × σ) ℂ).toLinearMap) := by
    refine Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials σ ℂ) fun v => ?_
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, ← Basis.piTensorProduct_apply]
    change bT.equiv (MvPolynomial.basisMonomials (ι × σ) ℂ) (expEquiv ι σ) (bT v) = _
    rw [Module.Basis.equiv_apply]
    simp only [MvPolynomial.coe_basisMonomials, AlgHom.toLinearMap_apply,
      MvPolynomial.rename_monomial, expEquiv, Equiv.ofBijective_apply]
    exact MvPolynomial.monomial_sum_one _ _
  refine ⟨e, fun f => ?_⟩
  simpa using MultilinearMap.congr_fun key f

end GlobalTheory.PolyTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleOfIsAtom
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.MaschkeForms

open Representation

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_of_isAtom {π : Representation ℂ G V} {U : Subrepresentation π}
    (hU : IsAtom U) : U.toRepresentation.IsIrreducible := by
  have hne : U.toSubmodule ≠ ⊥ := fun h => hU.1 (Subrepresentation.toSubmodule_injective h)
  have hnt : Nontrivial (Subrepresentation U.toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    have h' : (⊥ : Submodule ℂ U.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [← U.toSubmodule.map_subtype_top, ← h', Submodule.map_bot]
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation π := ⟨S.toSubmodule.map U.toSubmodule.subtype, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, S.apply_mem_toSubmodule g hx, rfl⟩⟩
  have hT : T ≤ U := U.toSubmodule.map_subtype_le S.toSubmodule
  have hinj := Submodule.map_injective_of_injective U.toSubmodule.injective_subtype
  rcases hU.le_iff.mp hT with h | h
  · left
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans (Submodule.map_bot _).symm
  · right
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans U.toSubmodule.map_subtype_top.symm

end GlobalTheory.MaschkeForms
end
end

