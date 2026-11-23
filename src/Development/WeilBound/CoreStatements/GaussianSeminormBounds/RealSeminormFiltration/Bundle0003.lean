module

public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreDefs

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasW
section
noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

def rho2 {r s : ℕ} : Ix r s → ℚ
  | .inl k => (r : ℚ) - 1 - 2 * (k : ℕ)
  | .inr l => (s : ℚ) - 1 - 2 * (l : ℕ)

theorem cw_cnt_lt {n : ℕ} (i : Fin n) (c : ℚ) :
    ∑ j : Fin n, (if i < j then c else 0) = ((n : ℚ) - 1 - (i : ℕ)) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have h := i.2
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem cw_cnt_gt {n : ℕ} (j : Fin n) (c : ℚ) :
    ∑ i : Fin n, (if i < j then c else 0) = ((j : ℕ) : ℚ) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, Finset.filter_gt_eq_Iio, Fin.card_Iio]

theorem cw_blk {n : ℕ} (f : Fin n → ℚ) :
    ∑ i, ∑ j, (if i < j then f i - f j else 0) = ∑ i : Fin n, ((n : ℚ) - 1 - 2 * (i : ℕ)) * f i := by
  have e : ∀ i j : Fin n, (if i < j then f i - f j else 0) = (if i < j then f i else 0) - (if i < j then f j else 0) := by
    intro i j
    split_ifs <;> ring
  simp_rw [e, Finset.sum_sub_distrib, cw_cnt_lt]
  rw [Finset.sum_comm (f := fun i j => if i < j then f j else 0)]
  simp_rw [cw_cnt_gt]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem cw_two {ι : Type} [Fintype ι] [DecidableEq ι] (G H : ι → ℚ) {a b : ι} (hab : a ≠ b)
    (h : ∀ x, x ≠ a → x ≠ b → G x = H x) : ∑ x, G x = ∑ x, H x + (G b - H b) + (G a - H a) := by
  have key : ∑ x, (G x - H x) = (G a - H a) + (G b - H b) :=
    Fintype.sum_eq_add a b hab (fun x hx => by rw [h x hx.1 hx.2, sub_self])
  rw [Finset.sum_sub_distrib] at key
  linarith

theorem cw_root {r s : ℕ} {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    ν a = La a - 1 ∧ ν b = La b + 1 ∧ ∀ x, x ≠ a → x ≠ b → ν x = La x := by
  refine ⟨?_, ?_, ?_⟩
  · have := h a
    rw [if_pos rfl, if_neg hab] at this
    linarith
  · have := h b
    rw [if_neg (Ne.symm hab), if_pos rfl] at this
    linarith
  · intro x hxa hxb
    have := h x
    rw [if_neg hxa, if_neg hxb] at this
    linarith

theorem cw_init {r p : ℕ} (hp : p ≤ r) (c : ℚ) :
    ∑ k : Fin r, (if (k : ℕ) < p then c else 0) = p * c := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < p then c else 0) r, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have e : (Finset.range r).filter (fun k => k < p) = Finset.range p := by
    ext k
    simp
    omega
  rw [e, Finset.card_range]

theorem cw_fin {r q : ℕ} (hq : q ≤ r) (c : ℚ) :
    ∑ k : Fin r, (if r ≤ (k : ℕ) + q then c else 0) = q * c := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if r ≤ k + q then c else 0) r, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have e : (Finset.range r).filter (fun k => r ≤ k + q) = Finset.Ico (r - q) r := by
    ext k
    simp
    omega
  rw [e, Nat.card_Ico, show r - (r - q) = q by omega]

theorem casW_eq {r s : ℕ} (μ : Ix r s → ℚ) : casW μ = ∑ x, μ x ^ 2 + ∑ x, rho2 x * μ x := by
  unfold casW
  congr 1
  simp only [Fintype.sum_sum_type, posC, rho2]
  simp only [if_false, ite_false, Finset.sum_const_zero, add_zero, zero_add]
  rw [cw_blk, cw_blk]

theorem casW_root {r s : ℕ} {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    casW ν = casW La + 2 * (La b - La a) + 2 + (rho2 b - rho2 a) := by
  obtain ⟨ha, hb, hx⟩ := cw_root hab h
  rw [casW_eq, casW_eq, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have key := cw_two (fun x => ν x ^ 2 + rho2 x * ν x) (fun x => La x ^ 2 + rho2 x * La x) hab
    (fun x h1 h2 => by simp only [hx x h1 h2])
  simp only [ha, hb] at key
  linear_combination key

private theorem shiftNu_sub_lemma {r s : ℕ} (c : ℚ) (μ μ' : Ix r s → ℚ) (x : Ix r s) :
    shiftNu c μ x = shiftNu c μ' x + (μ x - μ' x) := by
  cases x <;> simp only [shiftNu] <;> ring

theorem degW_root {r s : ℕ} (c : ℚ) {ν La : Ix r s → ℚ} {a b : Ix r s} (hab : a ≠ b) (h : RootTo ν a b La) :
    degW c ν = degW c La + (|shiftNu c La b + 1| - |shiftNu c La b|) + (|shiftNu c La a - 1| - |shiftNu c La a|) := by
  obtain ⟨ha, hb, hx⟩ := cw_root hab h
  have key := cw_two (fun x => |shiftNu c ν x|) (fun x => |shiftNu c La x|) hab
    (fun x h1 h2 => by
      show |shiftNu c ν x| = |shiftNu c La x|
      rw [shiftNu_sub_lemma c ν La x, hx x h1 h2, sub_self, add_zero])
  have e1 : shiftNu c ν b = shiftNu c La b + 1 := by
    rw [shiftNu_sub_lemma c ν La b, hb]
    ring
  have e2 : shiftNu c ν a = shiftNu c La a - 1 := by
    rw [shiftNu_sub_lemma c ν La a, ha]
    ring
  simp only [e1, e2] at key
  unfold degW
  exact key

theorem degW_laPos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) :
    degW (cPair p q) (laPos p q r s n m) = p * n + q * m := by
  unfold degW
  rw [Fintype.sum_sum_type]
  simp only [shiftNu, laPos, add_sub_cancel_right, sub_add_cancel]
  have e : ∀ (P : Prop) [Decidable P] (t : ℕ), |(if P then (t : ℚ) else 0)| = if P then (t : ℚ) else 0 := by
    intro P _ t
    split_ifs <;> simp
  simp only [e]
  rw [cw_init hp, cw_init hq]

theorem degW_laNeg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) :
    degW (cPair p q) (laNeg p q r s n m) = q * n + p * m := by
  unfold degW
  rw [Fintype.sum_sum_type]
  simp only [shiftNu, laNeg, add_sub_cancel_right, sub_add_cancel]
  have e : ∀ (P : Prop) [Decidable P] (t : ℕ), |(if P then -(t : ℚ) else 0)| = if P then (t : ℚ) else 0 := by
    intro P _ t
    split_ifs <;> simp
  simp only [e]
  rw [cw_fin hq, cw_fin hp]

theorem degW_const {p q : ℕ} (c c0 : ℚ) :
    degW c (fun _ : Ix p q => c0) = p * |c0 - c| + q * |c0 + c| := by
  unfold degW
  simp [Fintype.sum_sum_type, shiftNu]

end PositivityTheory.KReal

end
end

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreShape
section
noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem pad_all (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    ∀ v ∈ a ++ List.replicate (p - a.length - b.length) 0 ++ b, v = z := by
  intro v hv
  have hlen : (a ++ List.replicate (p - a.length - b.length) 0 ++ b).length = p := by
    simp only [List.length_append, List.length_replicate]
    omega
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have h1 := h ⟨i, hlen ▸ hi⟩
  simp only [pad, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some] at h1
  exact_mod_cast h1

theorem pad_pos (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ) (hz : 0 < z)
    (hb : ∀ v ∈ b, v < 0)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    a = List.replicate p z ∧ b = [] := by
  have hall := pad_all a b p hl z h
  have hb' : b = [] := by
    rcases b with _ | ⟨v, b⟩
    · rfl
    · exfalso
      have h1 := hall v (by simp)
      have h2 := hb v (by simp)
      omega
  subst hb'
  have hk : p - a.length - ([] : List ℤ).length = 0 := by
    by_contra hne
    have := hall 0 (List.mem_append.2 (Or.inl (List.mem_append.2
      (Or.inr (List.mem_replicate.2 ⟨hne, rfl⟩)))))
    omega
  refine ⟨List.eq_replicate_iff.2 ⟨?_, fun v hv => hall v (by simp [hv])⟩, rfl⟩
  simp only [List.length_nil] at hk hl
  omega

theorem pad_neg (a b : List ℤ) (p : ℕ) (hl : a.length + b.length ≤ p) (z : ℤ) (hz : z < 0)
    (ha : ∀ v ∈ a, 0 < v)
    (h : ∀ i : Fin p, (pad a (p - a.length - b.length) b).getD i 0 = (z : ℚ)) :
    a = [] ∧ b = List.replicate p z := by
  have hall := pad_all a b p hl z h
  have ha' : a = [] := by
    rcases a with _ | ⟨v, a⟩
    · rfl
    · exfalso
      have h1 := hall v (by simp)
      have h2 := ha v (by simp)
      omega
  subst ha'
  have hk : p - ([] : List ℤ).length - b.length = 0 := by
    by_contra hne
    have := hall 0 (List.mem_append.2 (Or.inl (List.mem_append.2
      (Or.inr (List.mem_replicate.2 ⟨hne, rfl⟩)))))
    omega
  refine ⟨rfl, List.eq_replicate_iff.2 ⟨?_, fun v hv => hall v (by simp [hv])⟩⟩
  simp only [List.length_nil] at hk hl
  omega

theorem getD_pad_left (p k i : ℕ) (z : ℤ) :
    (pad (List.replicate p z) k []).getD i 0 = if i < p then (z : ℚ) else 0 := by
  simp only [pad, List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append, List.getElem?_replicate, List.length_replicate]
  split_ifs <;> simp_all <;> omega

theorem getD_pad_right (q r i : ℕ) (z : ℤ) (hq : q ≤ r) (hi : i < r) :
    (pad [] (r - q) (List.replicate q z)).getD i 0 = if r ≤ i + q then (z : ℚ) else 0 := by
  simp only [pad, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append, List.getElem?_replicate, List.length_replicate]
  split_ifs <;> simp_all <;> omega

theorem shift_pos_eq (p q r s n m : ℕ) :
    shiftNu (cPair p q) (laPos p q r s n m) =
      ofBlocks (pad (List.replicate p (n : ℤ)) (r - p) []) (pad (List.replicate q (m : ℤ)) (s - q) []) := by
  funext x
  rcases x with k | l
  · simp only [shiftNu, laPos, ofBlocks, getD_pad_left]
    split_ifs <;> push_cast <;> ring
  · simp only [shiftNu, laPos, ofBlocks, getD_pad_left]
    split_ifs <;> push_cast <;> ring

theorem shift_neg_eq (p q r s n m : ℕ) (hq : q ≤ r) (hp : p ≤ s) :
    shiftNu (cPair p q) (laNeg p q r s n m) =
      ofBlocks (pad [] (r - q) (List.replicate q (-(n : ℤ)))) (pad [] (s - p) (List.replicate p (-(m : ℤ)))) := by
  funext x
  rcases x with k | l
  · simp only [shiftNu, laNeg, ofBlocks, getD_pad_right q r k _ hq k.isLt]
    split_ifs <;> push_cast <;> ring
  · simp only [shiftNu, laNeg, ofBlocks, getD_pad_right p s l _ hp l.isLt]
    split_ifs <;> push_cast <;> ring

theorem shiftNu_inj {r s : ℕ} (c : ℚ) {μ ν : Ix r s → ℚ} (h : shiftNu c μ = shiftNu c ν) : μ = ν := by
  funext x
  have := congrFun h x
  rcases x with k | l <;> simp only [shiftNu] at this <;> linarith

theorem shape_pos {p q r s n m : ℕ} (hp : p ≤ r) (hq : q ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = n + cPair r s) (h2 : c0 = m - cPair r s) :
    JointShape p q r s (fun _ => c0) (laPos p q r s n m) ∧
      ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = laPos p q r s n m := by
  have hn' : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hm' : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  refine ⟨⟨List.replicate p (n : ℤ), [], List.replicate q (m : ℤ), [], ?_⟩, ?_⟩
  · refine ⟨fun v hv => (List.eq_of_mem_replicate hv) ▸ hn', fun v hv => (List.eq_of_mem_replicate hv) ▸ hm',
      fun v hv => by simp at hv, fun v hv => by simp at hv,
      List.pairwise_replicate.2 (Or.inr le_rfl), List.Pairwise.nil,
      List.pairwise_replicate.2 (Or.inr le_rfl), List.Pairwise.nil, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using hp
    · simpa using hq
    · funext x
      rcases x with i | j
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.zero_sub, getD_pad_left, i.isLt, if_true]
        rw [h1]; push_cast; ring
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.zero_sub, getD_pad_left, j.isLt, if_true]
        rw [h2]; push_cast; ring
    · simp only [List.length_replicate, List.length_nil, Nat.sub_zero]
      exact shift_pos_eq p q r s n m
  · rintro ν ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, -, -, hs1, hs2⟩
    have hA := pad_pos a b p hab (n : ℤ) hn' hb (fun i => by
      have hx := congrFun hs1 (Sum.inl i)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h1]; push_cast; ring)
    have hC := pad_pos c d q hcd (m : ℤ) hm' hd (fun j => by
      have hx := congrFun hs1 (Sum.inr j)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h2]; push_cast; ring)
    obtain ⟨rfl, rfl⟩ := hA
    obtain ⟨rfl, rfl⟩ := hC
    apply shiftNu_inj (cPair p q)
    rw [hs2, shift_pos_eq]
    simp only [List.length_replicate, List.length_nil, Nat.sub_zero]

theorem shape_neg {p q r s n m : ℕ} (hq : q ≤ r) (hp : p ≤ s) (hn : 0 < n) (hm : 0 < m) (c0 : ℚ)
    (h1 : c0 = -m + cPair r s) (h2 : c0 = -n - cPair r s) :
    JointShape p q r s (fun _ => c0) (laNeg p q r s n m) ∧
      ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = laNeg p q r s n m := by
  have hn' : (-(n : ℤ)) < 0 := by
    have : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
    omega
  have hm' : (-(m : ℤ)) < 0 := by
    have : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
    omega
  refine ⟨⟨[], List.replicate p (-(m : ℤ)), [], List.replicate q (-(n : ℤ)), ?_⟩, ?_⟩
  · refine ⟨fun v hv => by simp at hv, fun v hv => by simp at hv,
      fun v hv => (List.eq_of_mem_replicate hv) ▸ hm', fun v hv => (List.eq_of_mem_replicate hv) ▸ hn',
      List.Pairwise.nil, List.pairwise_replicate.2 (Or.inr le_rfl),
      List.Pairwise.nil, List.pairwise_replicate.2 (Or.inr le_rfl), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using hq
    · simpa using hp
    · funext x
      rcases x with i | j
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.sub_zero]
        have e := getD_pad_right p p i (-(m : ℤ)) le_rfl i.isLt
        rw [Nat.sub_self, if_pos (by omega)] at e
        rw [e, h1]; push_cast; ring
      · simp only [shiftNu, ofBlocks, List.length_replicate, List.length_nil, Nat.sub_self,
          Nat.sub_zero]
        have e := getD_pad_right q q j (-(n : ℤ)) le_rfl j.isLt
        rw [Nat.sub_self, if_pos (by omega)] at e
        rw [e, h2]; push_cast; ring
    · simp only [List.length_replicate, List.length_nil, Nat.sub_zero]
      exact shift_neg_eq p q r s n m hq hp
  · rintro ν ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, -, -, hs1, hs2⟩
    have hA := pad_neg a b p hab (-(m : ℤ)) hm' ha (fun i => by
      have hx := congrFun hs1 (Sum.inl i)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h1]; push_cast; ring)
    have hC := pad_neg c d q hcd (-(n : ℤ)) hn' hc (fun j => by
      have hx := congrFun hs1 (Sum.inr j)
      simp only [shiftNu, ofBlocks] at hx
      rw [← hx, h2]; push_cast; ring)
    obtain ⟨rfl, rfl⟩ := hA
    obtain ⟨rfl, rfl⟩ := hC
    apply shiftNu_inj (cPair p q)
    rw [hs2, shift_neg_eq p q r s n m hq hp]
    simp only [List.length_replicate, List.length_nil, Nat.sub_zero]

end PositivityTheory.KReal

end
end

