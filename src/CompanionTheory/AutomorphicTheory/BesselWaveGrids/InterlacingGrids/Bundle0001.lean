module

public import Mathlib

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.CloudProd
section
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem cloud_weight_prod (c : ℝ) (n : ℕ) :
    ∏ j ∈ range (n + 1), (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) = (2 + c) * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, if_neg (Nat.succ_ne_zero n)]
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp

theorem cloud_factor_le (c g d : ℝ) (j : ℕ) (hc : 0 ≤ c) (hg : 1 + c ≤ g) (hd : (j : ℝ) * g ≤ d) :
    1 + (1 + c) / max d 1 ≤ (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) := by
  split_ifs with hj
  · have : (1 + c) / max d 1 ≤ 1 + c := div_le_self (by linarith) (le_max_right _ _)
    linarith
  · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    have hpos : 0 < (j : ℝ) * (1 + c) := by positivity
    have h1 : (j : ℝ) * (1 + c) ≤ (j : ℝ) * g := mul_le_mul_of_nonneg_left hg (by positivity)
    have h2 : (j : ℝ) * (1 + c) ≤ max d 1 := le_trans (h1.trans hd) (le_max_left _ _)
    have h3 : (1 + c) / max d 1 ≤ (1 + c) / ((j : ℝ) * (1 + c)) :=
      div_le_div_of_nonneg_left (by linarith) hpos h2
    have h4 : (1 + c) / ((j : ℝ) * (1 + c)) = 1 / j := by
      have : (1 + c) ≠ 0 := by linarith
      have : (j : ℝ) ≠ 0 := by linarith
      field_simp
    linarith

theorem prod_le_prod_range_of_rank (A : Finset ℕ) (F : ℕ → ℝ) (φ : ℕ → ℕ) (w : ℕ → ℝ) (k : ℕ)
    (hF0 : ∀ s ∈ A, 0 ≤ F s) (hF : ∀ s ∈ A, F s ≤ w (φ s)) (hinj : Set.InjOn φ A)
    (hmap : ∀ s ∈ A, φ s < k) (hw : ∀ j, 1 ≤ w j) :
    ∏ s ∈ A, F s ≤ ∏ j ∈ range k, w j := by
  classical
  calc ∏ s ∈ A, F s ≤ ∏ s ∈ A, w (φ s) := prod_le_prod₀ hF0 hF
    _ = ∏ j ∈ A.image φ, w j := (prod_image hinj).symm
    _ ≤ ∏ j ∈ range k, w j := by
      apply prod_le_prod_of_subset_of_one_le₀
      · intro j hj
        obtain ⟨s, hs, rfl⟩ := mem_image.mp hj
        exact mem_range.mpr (hmap s hs)
      · intro j _
        exact le_trans zero_le_one (hw j)
      · intro j _ _
        exact hw j

theorem cloud_gap_sum (k : ℕ) (lam : ℕ → ℝ) (g : ℝ)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s) (s : ℕ) (hs : 1 ≤ s) :
    ∀ s', s ≤ s' → s' ≤ k - 1 → lam s' + ((s' : ℝ) - s) * g ≤ lam s := by
  intro s' hss'
  induction s', hss' using Nat.le_induction with
  | base => intro _; simp
  | succ n hn ih =>
    intro hn1
    have h1 := hgap n (by omega) hn1
    have h2 := ih (by omega)
    have h3 : (((n + 1 : ℕ) : ℝ) - s) * g = ((n : ℝ) - s) * g + g := by push_cast; ring
    rw [h3]
    linarith

theorem cloud_prod_le (k : ℕ) (lam : ℕ → ℝ) (c g Y : ℝ) (hk : 1 ≤ k) (hc : 0 ≤ c) (hg : 1 + c ≤ g)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s) :
    ∏ s ∈ Icc 1 (k - 1), (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) ^ 2 * (k : ℝ) ^ 2 := by
  classical
  have hF0 : ∀ s, 0 ≤ 1 + (1 + c) / max |Y + lam s| 1 := fun s => by
    have : 0 ≤ (1 + c) / max |Y + lam s| 1 :=
      div_nonneg (by linarith) (le_trans zero_le_one (le_max_right _ _))
    linarith
  have hw : ∀ j : ℕ, 1 ≤ (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) := fun j => by
    split_ifs
    · linarith
    · have : (0 : ℝ) ≤ 1 / (j : ℝ) := by positivity
      linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hW : ∏ j ∈ range k, (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) = (2 + c) * k := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [cloud_weight_prod]
    push_cast
    ring
  have hone : (1 : ℝ) ≤ (2 + c) * k := by nlinarith
  have hbound0 : 0 ≤ (2 + c) * k := by positivity
  rw [← prod_filter_mul_prod_filter_not (Icc 1 (k - 1)) (fun s => 0 < Y + lam s)]
  have hL : ∏ s ∈ (Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s),
      (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) * k := by
    by_cases hne : ((Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s)).Nonempty
    · have ht := max'_mem _ hne
      set t := ((Icc 1 (k - 1)).filter (fun s => 0 < Y + lam s)).max' hne with ht_def
      rw [mem_filter, mem_Icc] at ht
      rw [← hW]
      apply prod_le_prod_range_of_rank _ _ (fun s => t - s) _ k (fun s _ => hF0 s) _ _ _ hw
      · intro s hs
        have hst : s ≤ t := le_max' _ _ hs
        rw [mem_filter, mem_Icc] at hs
        apply cloud_factor_le c g _ _ hc hg
        have h1 := cloud_gap_sum k lam g hgap s hs.1.1 t hst ht.1.2
        have h2 := le_abs_self (Y + lam s)
        show (((t - s : ℕ) : ℝ)) * g ≤ |Y + lam s|
        rw [Nat.cast_sub hst]
        linarith [ht.2]
      · intro a ha b hb hab
        have ha' : a ≤ t := le_max' _ _ (mem_coe.mp ha)
        have hb' : b ≤ t := le_max' _ _ (mem_coe.mp hb)
        simp only at hab
        omega
      · intro s hs
        have hst : s ≤ t := le_max' _ _ hs
        show t - s < k
        omega
    · rw [not_nonempty_iff_eq_empty.mp hne, prod_empty]
      exact hone
  have hR : ∏ s ∈ (Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s),
      (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) * k := by
    by_cases hne : ((Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s)).Nonempty
    · have hu := min'_mem _ hne
      set u := ((Icc 1 (k - 1)).filter (fun s => ¬ 0 < Y + lam s)).min' hne with hu_def
      rw [mem_filter, mem_Icc] at hu
      rw [← hW]
      apply prod_le_prod_range_of_rank _ _ (fun s => s - u) _ k (fun s _ => hF0 s) _ _ _ hw
      · intro s hs
        have hus : u ≤ s := min'_le _ _ hs
        rw [mem_filter, mem_Icc] at hs
        apply cloud_factor_le c g _ _ hc hg
        have h1 := cloud_gap_sum k lam g hgap u hu.1.1 s hus hs.1.2
        have h2 := neg_le_abs (Y + lam s)
        show (((s - u : ℕ) : ℝ)) * g ≤ |Y + lam s|
        rw [Nat.cast_sub hus]
        have := not_lt.mp hu.2
        linarith
      · intro a ha b hb hab
        have ha' : u ≤ a := min'_le _ _ (mem_coe.mp ha)
        have hb' : u ≤ b := min'_le _ _ (mem_coe.mp hb)
        simp only at hab
        omega
      · intro s hs
        have hus : u ≤ s := min'_le _ _ hs
        rw [mem_filter, mem_Icc] at hs
        show s - u < k
        omega
    · rw [not_nonempty_iff_eq_empty.mp hne, prod_empty]
      exact hone
  calc _ ≤ ((2 + c) * k) * ((2 + c) * k) :=
        mul_le_mul_of_nonneg hL hR (prod_nonneg fun s _ => hF0 s) hbound0
    _ = (2 + c) ^ 2 * (k : ℝ) ^ 2 := by ring

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.FreeFamily
section
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem exists_free_family (Y : Finset ℝ) (w : List (Bool × ℝ)) (K D : ℕ)
    (hw : ∀ l ∈ w, ∃ y ∈ Y, l = (true, y) ∨ l = (false, y + 1))
    (hcard : w.length + K * D ≤ Y.card) :
    ∃ g : Fin K → Fin D → ℝ, (∀ a i, g a i ∈ Y) ∧
      (∀ a i a' i', g a i = g a' i' → a = a' ∧ i = i') ∧
      ∀ a i, ∀ l ∈ w, ∃ y ∈ Y, y ≠ g a i ∧ (l = (true, y) ∨ l = (false, y + 1)) := by
  classical
  choose! f hfY hf using hw
  set S : Finset ℝ := (w.map f).toFinset with hS
  have hSc : S.card ≤ w.length := by
    calc S.card ≤ (w.map f).length := List.toFinset_card_le _
      _ = w.length := List.length_map _
  have hT : K * D ≤ (Y \ S).card := by
    have h1 := Finset.le_card_sdiff S Y
    generalize K * D = m at hcard ⊢
    omega
  obtain ⟨emb⟩ : Nonempty (Fin (K * D) ↪ ↥(Y \ S)) := by
    rw [Function.Embedding.nonempty_iff_card_le]
    simpa using hT
  let φ : Fin K × Fin D ≃ Fin (K * D) := finProdFinEquiv
  refine ⟨fun a i => (emb (φ (a, i)) : ℝ), ?_, ?_, ?_⟩
  · intro a i
    exact (Finset.mem_sdiff.mp (emb (φ (a, i))).2).1
  · intro a i a' i' h
    have h1 := emb.injective (Subtype.ext h)
    have h2 := φ.injective h1
    simp only [Prod.mk.injEq] at h2
    exact h2
  · intro a i l hl
    refine ⟨f l, hfY l hl, ?_, hf l hl⟩
    intro heq
    have heq' : f l = (emb (φ (a, i)) : ℝ) := heq
    have hmem := (Finset.mem_sdiff.mp (emb (φ (a, i))).2).2
    apply hmem
    rw [← heq', hS, List.mem_toFinset, List.mem_map]
    exact ⟨l, hl, rfl⟩

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.GridSum
section
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem grid_sqrt_le {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (nn Q : ℝ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β)
    (hpos : ∀ a i, 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧ 0 < Q (grid a i))
    (hb : ∀ a i, nn (grid a i) * nn (grid a i + 1) ≤ β ^ 2 * Q (grid a i))
    (n : Fin K → Fin (d + 1)) :
    Real.sqrt (((List.ofFn fun a => grid a (n a)).map nn).prod *
        ((List.ofFn fun a => grid a (n a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (n a)).map Q).prod) ≤ β ^ K := by
  have hmap : ∀ h : ℝ → ℝ,
      ((List.ofFn fun a => grid a (n a)).map h).prod = ∏ a, h (grid a (n a)) := by
    intro h
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  simp only [hmap]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  have hle : ∏ a, nn (grid a (n a)) * nn (grid a (n a) + 1) / Q (grid a (n a)) ≤
      ∏ _a : Fin K, β ^ 2 := by
    apply Finset.prod_le_prod₀
    · intro a _
      have h := hpos a (n a)
      exact div_nonneg (mul_nonneg h.1.le h.2.1.le) h.2.2.le
    · intro a _
      rw [div_le_iff₀ (hpos a (n a)).2.2]
      exact hb a (n a)
  calc _ ≤ Real.sqrt (∏ _a : Fin K, β ^ 2) := Real.sqrt_le_sqrt hle
    _ = β ^ K := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, pow_mul',
        Real.sqrt_sq (pow_nonneg hβ K)]

theorem grid_sum_le {K d : ℕ} (grid c : Fin K → Fin (d + 1) → ℝ) (nn Q : ℝ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β)
    (hc : ∀ a, ∑ i, |c a i| ≤ 1)
    (hpos : ∀ a i, 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧ 0 < Q (grid a i))
    (hb : ∀ a i, nn (grid a i) * nn (grid a i + 1) ≤ β ^ 2 * Q (grid a i)) :
    ∑ n : Fin K → Fin (d + 1), |∏ a, c a (n a)| *
      Real.sqrt (((List.ofFn fun a => grid a (n a)).map nn).prod *
        ((List.ofFn fun a => grid a (n a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (n a)).map Q).prod) ≤ β ^ K := by
  calc _ ≤ ∑ n : Fin K → Fin (d + 1), |∏ a, c a (n a)| * β ^ K := by
        apply Finset.sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_left (grid_sqrt_le grid nn Q β hβ hpos hb n) (abs_nonneg _)
    _ = (∏ a, ∑ i, |c a i|) * β ^ K := by
        rw [← Finset.sum_mul, Fintype.prod_sum]
        simp only [Finset.abs_prod]
    _ ≤ 1 * β ^ K := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hβ K)
        apply Finset.prod_le_one₀
        · intro a _
          exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
        · intro a _
          exact hc a
    _ = β ^ K := one_mul _

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.LagSum
section
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem lag_abs_term_le {d : ℕ} (y : Fin (d + 1) → ℝ) (h : ∀ i j, i ≠ j → 5 ≤ |y i - y j|)
    (j : Fin (d + 1)) :
    |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹| ≤ (1 / 5 : ℝ) ^ d := by
  rw [abs_prod]
  have hcard : ((univ : Finset (Fin (d + 1))).erase j).card = d := by
    rw [Finset.card_erase_of_mem (mem_univ j)]; simp
  calc ∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, |(y j - y i)⁻¹|
      ≤ ∏ _i ∈ (univ : Finset (Fin (d + 1))).erase j, (1 / 5 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i _; exact abs_nonneg _
        · intro i hi
          have hij : j ≠ i := (Finset.ne_of_mem_erase hi).symm
          rw [abs_inv]
          have hx : 0 < |y j - y i| := lt_of_lt_of_le (by norm_num) (h j i hij)
          simpa only [one_div] using
            (div_le_div_iff₀ (a := (1 : ℝ)) (b := |y j - y i|) (c := 1) (d := 5)
              hx (by norm_num : 0 < (5 : ℝ))).2 (by simpa using h j i hij)
    _ = (1 / 5 : ℝ) ^ d := by rw [Finset.prod_const, hcard]

theorem lag_abs_sum_le_one {d : ℕ} (y : Fin (d + 1) → ℝ) (h : ∀ i j, i ≠ j → 5 ≤ |y i - y j|) :
    ∑ j, |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹| ≤ 1 := by
  have hn : (d : ℝ) + 1 ≤ 5 ^ d := by
    have : d + 1 ≤ 5 ^ d := Nat.lt_pow_self (by norm_num)
    exact_mod_cast this
  calc ∑ j, |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹|
      ≤ ∑ _j : Fin (d + 1), (1 / 5 : ℝ) ^ d :=
        Finset.sum_le_sum (fun j _ => lag_abs_term_le y h j)
    _ = ((d : ℝ) + 1) / 5 ^ d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow, one_pow]
        push_cast; ring
    _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hn

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.PairOKOfInterlace
section
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

def Pst (k r : ℕ) (lam : ℕ → ℝ) (c Y : ℝ) : ℝ := ∏ s ∈ Icc 1 (k + 2 * r + 1), (|Y + lam s| + c)

def PairOK (k : ℕ) (lam v : ℕ → ℝ) (e : ℕ) (x : ℝ) : Prop :=
  ∀ s, 1 ≤ s → s ≤ k - 1 → s ≠ e →
    (x < lam s → lam s + 1 / 2 ≤ v s) ∧ (lam s ≤ x → v (s + 1) ≤ lam s - 1 / 2)

theorem pairOK_of_interlace (k : ℕ) (lam v : ℕ → ℝ) (e : ℕ) (x : ℝ)
    (h : ∀ s, 1 ≤ s → s ≤ k - 1 → lam s + 1 / 2 ≤ v s ∧ v (s + 1) ≤ lam s - 1 / 2) :
    PairOK k lam v e x := by
  intro s hs1 hsk _
  exact ⟨fun _ => (h s hs1 hsk).1, fun _ => (h s hs1 hsk).2⟩

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.ProgYInjective
section
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

noncomputable def progY (y0 : ℝ) (M : ℕ) : Finset ℝ := (range M).image fun i : ℕ => y0 + 5 * (i : ℝ)

lemma progY_injective (y0 : ℝ) : Function.Injective fun i : ℕ => y0 + 5 * (i : ℝ) := by
  intro i j h
  have : (i : ℝ) = j := by simpa using h
  exact_mod_cast this

theorem progY_card (y0 : ℝ) (M : ℕ) : (progY y0 M).card = M := by
  unfold progY
  rw [card_image_of_injective _ (progY_injective y0), card_range]

theorem progY_sep (y0 : ℝ) (M : ℕ) : ∀ y ∈ progY y0 M, ∀ y' ∈ progY y0 M, y ≠ y' → 5 ≤ |y - y'| := by
  intro y hy y' hy' hne
  simp only [progY, mem_image, mem_range] at hy hy'
  obtain ⟨i, -, rfl⟩ := hy
  obtain ⟨j, -, rfl⟩ := hy'
  have hij : i ≠ j := by
    rintro rfl
    exact hne rfl
  have hsub : y0 + 5 * (i : ℝ) - (y0 + 5 * (j : ℝ)) = 5 * ((i : ℤ) - (j : ℤ) : ℤ) := by
    push_cast; ring
  rw [hsub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5)]
  have h1 : (1 : ℝ) ≤ |(((i : ℤ) - (j : ℤ) : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    have : (1 : ℤ) ≤ |(i : ℤ) - (j : ℤ)| := by
      exact Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hij))
    exact_mod_cast this
  linarith

theorem progY_cut (lo hi : ℝ) (M : ℕ) (hlen : 5 * (M : ℝ) ≤ hi - lo) :
    ∀ y ∈ progY (2 - hi) M, (lo + 2 ≤ -y ∧ -y ≤ hi - 2) ∧ (lo + 2 ≤ -(y + 1) ∧ -(y + 1) ≤ hi - 2) := by
  intro y hy
  simp only [progY, mem_image, mem_range] at hy
  obtain ⟨i, hi', rfl⟩ := hy
  have hiM : (i : ℝ) + 1 ≤ M := by exact_mod_cast hi'
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
end

