module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem list_neg {α : Type} (d : α → ℤ × ℤ) (L : List α) (h : ((L.map d).sum).2 < 0) :
    ∃ a ∈ L, (d a).2 < 0 := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Prod.snd_add] at h
    by_cases hb : (d b).2 < 0
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨a, ha, h'⟩ := ih (by omega)
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

private theorem list_pos {α : Type} (d : α → ℤ × ℤ) (L : List α) (h : 0 < ((L.map d).sum).2) :
    ∃ a ∈ L, 0 < (d a).2 := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Prod.snd_add] at h
    by_cases hb : 0 < (d b).2
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨a, ha, h'⟩ := ih (by omega)
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

private theorem span_zero {O S K : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing K] [Algebra O K]
    (B : Subalgebra O S) (ξ : B →ₐ[O] K) (T : Set S) (hT : ∀ y ∈ T, ∃ h : y ∈ B, ξ ⟨y, h⟩ = 0)
    (x : B) (hx : x.1 ∈ Submodule.span O T) : ξ x = 0 := by
  obtain ⟨x, hxB⟩ := x
  have hx' : x ∈ Submodule.span O T := hx
  clear hx
  suffices H : ∃ h : x ∈ B, ξ ⟨x, h⟩ = 0 by
    obtain ⟨_, h⟩ := H
    exact h
  clear hxB
  induction hx' using Submodule.span_induction with
  | mem y hy => exact hT y hy
  | zero => exact ⟨B.zero_mem, map_zero ξ⟩
  | add y z _ _ hy hz =>
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨B.add_mem hy1 hz1, ?_⟩
    have e : (⟨y + z, B.add_mem hy1 hz1⟩ : B) = ⟨y, hy1⟩ + ⟨z, hz1⟩ := rfl
    rw [e, map_add (f := _), hy2, hz2, add_zero]
  | smul a y _ hy =>
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨B.smul_mem hy1 a, ?_⟩
    have e : (⟨a • y, B.smul_mem hy1 a⟩ : B) = a • ⟨y, hy1⟩ := rfl
    rw [e, map_smul, hy2, smul_zero]

private theorem prod_zero {O S K α : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing K] [Algebra O K]
    (B : Subalgebra O S) (ξ : B →ₐ[O] K) (e : α → B) (L : List α) (a : α) (ha : a ∈ L) (h0 : ξ (e a) = 0) :
    ∃ h : (L.map fun a => (e a).1).prod ∈ B, ξ ⟨_, h⟩ = 0 := by
  have hp : (((L.map e).prod : B) : S) = (L.map fun a => (e a).1).prod := by
    simpa [List.map_map, Function.comp_def] using map_list_prod B.val (L.map e)
  have hm : (L.map fun a => (e a).1).prod ∈ B := by
    rw [← hp]
    exact ((L.map e).prod).2
  refine ⟨hm, ?_⟩
  have e1 : (⟨_, hm⟩ : B) = (L.map e).prod := Subtype.ext hp.symm
  rw [e1, map_list_prod, List.map_map]
  apply List.prod_eq_zero
  simp only [List.mem_map, Function.comp_apply]
  exact ⟨a, ha, h0⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.signs :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ((∀ i j, (wt i j).2 < 0 → ¬ Ge (M.rep ξ) i j) → NegZero M.gr (ξ.comp M.toSS)) ∧ ((∀ i j, 0 < (wt i j).2 → ¬ Ge (M.rep ξ) i j) → PosZero M.gr (ξ.comp M.toSS)) ∧ (PosZero M.gr (ξ.comp M.toSS) → ¬ Ge (M.rep ξ) 0 2) ∧ (NegZero M.gr (ξ.comp M.toSS) → ¬ Ge (M.rep ξ) 2 0) ∧ ∀ ξ' : M.SS →ₐ[c.O] PadicAlgCl l, Same0 M.gr (ξ.comp M.toSS) (ξ'.comp M.toSS) → (∀ g i, M.rep ξ g i i = M.rep ξ' g i i) ∧ (DiagType (M.rep ξ) → DiagType (M.rep ξ')) := by
  intro Ω _ _ _ l _ c D hD M _ h0 ξ
  have hv : ∀ (ζ : M.SS →ₐ[c.O] PadicAlgCl l) g i j, M.rep ζ g i j = ζ (M.ent g i j) := fun _ _ _ _ => rfl
  have hwt : ∀ i j : Fin 4, (wt i j).1 = 0 → True := fun _ _ _ => trivial
  have zero_of : ∀ n : ℤ, ∀ f ∈ M.gr n,
      (∀ L : List (G ℚ Ω × Fin 4 × Fin 4), (L.map fun a => wt a.2.1 a.2.2).sum = ((0 : ℤ), n) →
        ∃ a ∈ L, ξ (M.ent a.1 a.2.1 a.2.2) = 0) → ξ (M.toSS f) = 0 := by
    intro n f hf hL
    have hx := (kerA D hD M).2.2 n f hf
    rw [spanMono D hD M h0] at hx
    apply span_zero M.SS ξ (mono M.ru.hom ((0 : ℤ), n)) _ (M.toSS f) hx
    rintro y ⟨L, hsum, rfl⟩
    obtain ⟨a, ha, hz⟩ := hL L hsum
    exact prod_zero M.SS ξ (fun a => M.ent a.1 a.2.1 a.2.2) L a ha hz
  have from_part : ∀ n : ℤ, ∀ g i j, wt i j = ((0 : ℤ), n) → ∃ f ∈ M.gr n, M.toSS f = M.ent g i j := by
    intro n g i j he
    apply (kerA D hD M).2.1 n (M.ent g i j)
    have := M.entry_mem g i j
    rw [he] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hneg n hn f hf
    change ξ (M.toSS f) = 0
    apply zero_of n f hf
    intro L hsum
    obtain ⟨a, ha, hlt⟩ := list_neg (fun a => wt a.2.1 a.2.2) L (by rw [hsum]; exact hn)
    refine ⟨a, ha, ?_⟩
    by_contra hne
    exact hneg _ _ hlt ⟨a.1, hne⟩
  · intro hpos n hn f hf
    change ξ (M.toSS f) = 0
    apply zero_of n f hf
    intro L hsum
    obtain ⟨a, ha, hlt⟩ := list_pos (fun a => wt a.2.1 a.2.2) L (by rw [hsum]; exact hn)
    refine ⟨a, ha, ?_⟩
    by_contra hne
    exact hpos _ _ hlt ⟨a.1, hne⟩
  · rintro hpos ⟨g, hg⟩
    obtain ⟨f, hf, hfx⟩ := from_part 1 g 0 2 (by decide)
    apply hg
    have := hpos 1 one_pos f hf
    change ξ (M.toSS f) = 0 at this
    rw [hfx] at this
    exact this
  · rintro hneg ⟨g, hg⟩
    obtain ⟨f, hf, hfx⟩ := from_part (-1) g 2 0 (by decide)
    apply hg
    have := hneg (-1) (by norm_num) f hf
    change ξ (M.toSS f) = 0 at this
    rw [hfx] at this
    exact this
  · intro ξ' hs
    have key : ∀ x : M.SS, (x : M.S) ∈ M.sPart ((0 : ℤ), 0) → ξ x = ξ' x := by
      intro x hx
      obtain ⟨f, hf, rfl⟩ := (kerA D hD M).2.1 0 x hx
      exact hs f hf
    constructor
    · intro g i
      rw [hv, hv]
      apply key
      have := M.entry_mem g i i
      rwa [show wt i i = ((0 : ℤ), 0) by simp [wt]] at this
    · intro hd i j hij ⟨g, hg⟩ ⟨h, hh⟩
      rw [hv] at hg hh
      have hp : ((M.ent g i j * M.ent h j i : M.SS) : M.S) ∈ M.sPart ((0 : ℤ), 0) := by
        rw [spanMono D hD M h0]
        apply Submodule.subset_span
        refine ⟨[(g, i, j), (h, j, i)], ?_, ?_⟩
        · refine Prod.ext ?_ ?_ <;> simp [wt] <;> ring
        · simp [Model.ent]
      have he := key _ hp
      rw [map_mul, map_mul] at he
      apply mul_ne_zero hg hh
      rw [← he]
      by_cases a : ξ (M.ent g i j) = 0
      · rw [a, zero_mul]
      · have hnot := hd i j hij ⟨g, by rw [hv]; exact a⟩
        have hz : ξ (M.ent h j i) = 0 := by
          by_contra hz
          exact hnot ⟨h, by rw [hv]; exact hz⟩
        rw [hz, mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoPowClogLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem two_pow_clog_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ Nat.clog 2 m ≤ 2 * m := by
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · have hk : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) h1
    have hlt := Nat.pow_pred_clog_lt_self 2 h1
    obtain ⟨k, hk'⟩ : ∃ k, Nat.clog 2 m = k + 1 := ⟨Nat.clog 2 m - 1, by omega⟩
    rw [hk'] at hlt ⊢
    simp only [Nat.pred_eq_sub_one, Nat.add_sub_cancel] at hlt
    rw [pow_succ]
    linarith
  · have : m = 1 := by omega
    subst this
    simp

private theorem nII_le (X l N o q c n f : ℕ) (hX : 16 ≤ X) (hl : l ≤ X) (hN : N ≤ X) (ho : o ≤ X) (hq : q ≤ X)
    (hc : 2 ^ c ≤ X) (hn : 2 ^ n ≤ l ^ f) (hl0 : 0 < l) (hN0 : 0 < N) :
    2 ^ Nat.clog 2 (max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2)) ≤ X ^ (2 * f + 10) := by
  have hX1 : 1 ≤ X := by omega
  have hX2 : 2 ≤ X := by omega
  have hmono : ∀ {i j : ℕ}, i ≤ j → X ^ i ≤ X ^ j := fun h => Nat.pow_le_pow_right hX1 h
  have mlp : ∀ {a b i j : ℕ}, a ≤ X ^ i → b ≤ X ^ j → a * b ≤ X ^ (i + j) := by
    intro a b i j ha hb
    rw [pow_add]
    exact Nat.mul_le_mul ha hb
  have h4 : 4 ^ n ≤ X ^ (f * 2) := by
    have e4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [e4, pow_mul]
    exact Nat.pow_le_pow_left (hn.trans (Nat.pow_le_pow_left hl f)) 2
  have hA1 : l * N * 4 ^ n ≤ X ^ (1 + 1 + f * 2) :=
    mlp (mlp (hl.trans (pow_one X).ge) (hN.trans (pow_one X).ge)) h4
  have hB : 2 ^ c * o * l ^ 3 * q ^ 2 ≤ X ^ (1 + 1 + 3 + 2) :=
    mlp (mlp (mlp (hc.trans (pow_one X).ge) (ho.trans (pow_one X).ge))
      (Nat.pow_le_pow_left hl 3)) (Nat.pow_le_pow_left hq 2)
  have hA2 : 2 ^ (c + 6) * o * l ^ 3 * q ^ 2 ≤ 64 * X ^ (1 + 1 + 3 + 2) := by
    calc 2 ^ (c + 6) * o * l ^ 3 * q ^ 2 = 64 * (2 ^ c * o * l ^ 3 * q ^ 2) := by ring
      _ ≤ 64 * X ^ (1 + 1 + 3 + 2) := Nat.mul_le_mul_left 64 hB
  have hpos : 1 ≤ l * N * 4 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmax1 : 1 ≤ max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) := hpos.trans (le_max_left _ _)
  have k1 : 2 * (l * N * 4 ^ n) ≤ X ^ (2 * f + 10) :=
    calc 2 * (l * N * 4 ^ n) ≤ X * X ^ (1 + 1 + f * 2) := Nat.mul_le_mul hX2 hA1
      _ = X ^ (1 + (1 + 1 + f * 2)) := by ring
      _ ≤ X ^ (2 * f + 10) := hmono (by omega)
  have h128 : 128 ≤ X ^ 2 := by nlinarith
  have k2 : 2 * (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) ≤ X ^ (2 * f + 10) :=
    calc 2 * (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) ≤ 2 * (64 * X ^ (1 + 1 + 3 + 2)) := Nat.mul_le_mul_left 2 hA2
      _ = 128 * X ^ (1 + 1 + 3 + 2) := by ring
      _ ≤ X ^ 2 * X ^ (1 + 1 + 3 + 2) := Nat.mul_le_mul_right _ h128
      _ = X ^ (2 + (1 + 1 + 3 + 2)) := by ring
      _ ≤ X ^ (2 * f + 10) := hmono (by omega)
  calc 2 ^ Nat.clog 2 (max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2))
      ≤ 2 * max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) := two_pow_clog_le _ hmax1
    _ ≤ X ^ (2 * f + 10) := by
      rcases max_choice (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) with h | h <;> rw [h] <;> assumption

private theorem le_pow_self' {X : ℕ} (hX : 2 ≤ X) (k : ℕ) : k ≤ X ^ k := by
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ X ^ k := Nat.pow_le_pow_left hX k

private theorem mul_le_pow' {X a b i j : ℕ} (ha : a ≤ X ^ i) (hb : b ≤ X ^ j) : a * b ≤ X ^ (i + j) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

private theorem two_pow_nIII_le {X l q P n f : ℕ} (hX : 2 ≤ X) (hl : l ≤ X) (hl0 : 0 < l) (hn : 2 ^ n < l ^ f) :
    2 ^ Nat.clog 2 (max (l * q * P * 4 ^ n) (8 * l ^ 2)) ≤ X ^ (1 + (10 + q + P + 2 * f)) := by
  have hX1 : 1 ≤ X := by omega
  have hmono : ∀ {i j : ℕ}, i ≤ j → X ^ i ≤ X ^ j := fun h => Nat.pow_le_pow_right hX1 h
  have h4 : 4 ^ n ≤ X ^ (f * 2) := by
    have e4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [e4, pow_mul]
    exact Nat.pow_le_pow_left (hn.le.trans (Nat.pow_le_pow_left hl f)) 2
  have hA1 : l * q * P * 4 ^ n ≤ X ^ (1 + q + P + f * 2) :=
    mul_le_pow' (mul_le_pow' (mul_le_pow' (hl.trans (pow_one X).ge) (le_pow_self' hX q))
      (le_pow_self' hX P)) h4
  have h8 : 8 ≤ X ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ X ^ 3 := Nat.pow_le_pow_left hX 3
  have hA2 : 8 * l ^ 2 ≤ X ^ (3 + 2) := mul_le_pow' h8 (Nat.pow_le_pow_left hl 2)
  have hmax1 : 1 ≤ max (l * q * P * 4 ^ n) (8 * l ^ 2) :=
    (Nat.one_le_iff_ne_zero.mpr (by positivity)).trans (le_max_right _ _)
  have k1 : 2 * (l * q * P * 4 ^ n) ≤ X ^ (1 + (10 + q + P + 2 * f)) :=
    calc 2 * (l * q * P * 4 ^ n) ≤ X * X ^ (1 + q + P + f * 2) := Nat.mul_le_mul hX hA1
      _ = X ^ (1 + (1 + q + P + f * 2)) := by ring
      _ ≤ X ^ (1 + (10 + q + P + 2 * f)) := hmono (by omega)
  have k2 : 2 * (8 * l ^ 2) ≤ X ^ (1 + (10 + q + P + 2 * f)) :=
    calc 2 * (8 * l ^ 2) ≤ X * X ^ (3 + 2) := Nat.mul_le_mul hX hA2
      _ = X ^ (1 + (3 + 2)) := by ring
      _ ≤ X ^ (1 + (10 + q + P + 2 * f)) := hmono (by omega)
  calc 2 ^ Nat.clog 2 (max (l * q * P * 4 ^ n) (8 * l ^ 2))
      ≤ 2 * max (l * q * P * 4 ^ n) (8 * l ^ 2) := two_pow_clog_le _ hmax1
    _ ≤ X ^ (1 + (10 + q + P + 2 * f)) := by
      rcases max_choice (l * q * P * 4 ^ n) (8 * l ^ 2) with h | h <;> rw [h] <;> assumption

private theorem pZero_le' (m : ℕ) : pZero m ≤ 2 * m + 10 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [pZero]
  · exact (pZeroLe m hm).2.2.2

private theorem final_le (C A a B o l n N P e : ℕ) (hl : 2 ≤ l) (hN : 0 < N) (he : 0 < e) (hP : P ≤ B)
    (hn : 2 ^ n ≤ (l * N * e) ^ a) :
    (2 * C * ((l - 1) * 2 ^ n * (2 * o) : ℕ) * (((l * 2 ^ n * N * P : ℕ) : ℝ) * (e + 1)) ^ A *
      Real.log (pZero (l * N * P)) : ℝ) ≤
      ((l : ℝ) * N * e) ^ (2 * C + (1 + a + 2 * o) + (1 + a + 1 + B + 2) * A + (2 + (1 + 1 + B) + 10 + 1)) := by
  obtain ⟨X, hXdef⟩ : ∃ X, X = l * N * e := ⟨_, rfl⟩
  rw [← hXdef] at hn
  have hNe : 1 ≤ N * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hle : 1 ≤ l * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hlN : 1 ≤ l * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hlX : l ≤ X := by
    calc l = l * 1 := (mul_one _).symm
      _ ≤ l * (N * e) := Nat.mul_le_mul_left _ hNe
      _ = X := by rw [hXdef]; ring
  have hNX : N ≤ X := by
    calc N = N * 1 := (mul_one _).symm
      _ ≤ N * (l * e) := Nat.mul_le_mul_left _ hle
      _ = X := by rw [hXdef]; ring
  have heX : e ≤ X := by
    calc e = 1 * e := (one_mul _).symm
      _ ≤ (l * N) * e := Nat.mul_le_mul_right _ hlN
      _ = X := by rw [hXdef]
  have hX2 : 2 ≤ X := hl.trans hlX
  have hX1 : 1 ≤ X := by omega
  have hmono : ∀ {i j : ℕ}, i ≤ j → X ^ i ≤ X ^ j := fun h => Nat.pow_le_pow_right hX1 h
  have hPB : P ≤ X ^ B := hP.trans (le_pow_self' hX2 B)
  have b1 : 2 * C ≤ X ^ (2 * C) := le_pow_self' hX2 _
  have b2 : (l - 1) * 2 ^ n * (2 * o) ≤ X ^ (1 + a + 2 * o) :=
    mul_le_pow' (mul_le_pow' (((Nat.sub_le l 1).trans hlX).trans (pow_one X).ge) hn) (le_pow_self' hX2 _)
  have he1 : e + 1 ≤ X ^ 2 := by nlinarith
  have b3 : l * 2 ^ n * N * P * (e + 1) ≤ X ^ (1 + a + 1 + B + 2) :=
    mul_le_pow' (mul_le_pow' (mul_le_pow' (mul_le_pow' (hlX.trans (pow_one X).ge) hn)
      (hNX.trans (pow_one X).ge)) hPB) he1
  have hy : l * N * P ≤ X ^ (1 + 1 + B) :=
    mul_le_pow' (mul_le_pow' (hlX.trans (pow_one X).ge) (hNX.trans (pow_one X).ge)) hPB
  have hy1 : 1 ≤ X ^ (1 + 1 + B) := Nat.one_le_pow _ _ (by omega)
  have h16 : 16 ≤ X ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ X ^ 4 := Nat.pow_le_pow_left hX2 4
  have b4 : pZero (l * N * P) ≤ X ^ (2 + (1 + 1 + B) + 10 + 1) := by
    calc pZero (l * N * P) ≤ 2 * (l * N * P) + 10 := pZero_le' _
      _ ≤ 2 * X ^ (1 + 1 + B) + 10 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hy) 10
      _ ≤ X ^ 4 * X ^ (1 + 1 + B) := by nlinarith
      _ = X ^ (4 + (1 + 1 + B)) := by ring
      _ ≤ X ^ (2 + (1 + 1 + B) + 10 + 1) := hmono (by omega)
  have hXr : ((l : ℝ) * N * e) = (X : ℝ) := by rw [hXdef]; push_cast; ring
  rw [hXr]
  have c1 : 2 * (C : ℝ) ≤ (X : ℝ) ^ (2 * C) := by exact_mod_cast b1
  have c2 : (((l - 1) * 2 ^ n * (2 * o) : ℕ) : ℝ) ≤ (X : ℝ) ^ (1 + a + 2 * o) := by exact_mod_cast b2
  have c3 : (((l * 2 ^ n * N * P : ℕ) : ℝ) * (e + 1)) ≤ (X : ℝ) ^ (1 + a + 1 + B + 2) := by
    have : (((l * 2 ^ n * N * P * (e + 1) : ℕ) : ℝ)) ≤ (X : ℝ) ^ (1 + a + 1 + B + 2) := by exact_mod_cast b3
    simpa using this
  have hlog0 : 0 ≤ Real.log (pZero (l * N * P)) := Real.log_natCast_nonneg _
  have c4 : Real.log (pZero (l * N * P)) ≤ (X : ℝ) ^ (2 + (1 + 1 + B) + 10 + 1) := by
    have hb4 : ((pZero (l * N * P) : ℕ) : ℝ) ≤ (X : ℝ) ^ (2 + (1 + 1 + B) + 10 + 1) := by exact_mod_cast b4
    exact (Real.log_le_self (Nat.cast_nonneg _)).trans hb4
  have hY0 : 0 ≤ (((l * 2 ^ n * N * P : ℕ) : ℝ) * (e + 1)) := by positivity
  have s1 := mul_le_mul c1 c2 (by positivity) (by positivity)
  have s2 := mul_le_mul s1 (pow_le_pow_left₀ hY0 c3 A) (by positivity) (by positivity)
  have s3 := mul_le_mul s2 c4 hlog0 (by positivity)
  refine s3.trans (le_of_eq ?_)
  rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]

theorem UpperTheory.V.GradeZeroInterpolatingElement.arith :
    ∀ (χ : Formalism.HC.PChar) (C A : ℕ), ∃ C' : ℕ, ∀ h : Host, h.chi = χ → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 2 ≤ e → ∀ ψ ∈ h.X c e, ∀ n' p₁ : ℕ, (n' = h.nII l ψ ∧ p₁ = 1) ∨ (n' = h.nIII l ψ ∧ p₁ = UpperTheory.V.pOne χ) → (2 * C * ((l - 1) * 2 ^ n' * (2 * h.o) : ℕ) * (((l * 2 ^ n' * h.N * p₁ : ℕ) : ℝ) * (e + 1)) ^ A * Real.log (pZero (l * h.N * p₁)) : ℝ) ≤ ((l : ℝ) * h.N * e) ^ C' := by
  intro χ C A
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = (2 * (4 * ordC χ).totient + 10) +
      (1 + (10 + χ.N + pOne χ + 2 * (4 * ordC χ).totient)) := ⟨_, rfl⟩
  refine ⟨2 * C + (1 + a + 2 * ordC χ) + (1 + a + 1 + (1 + pOne χ) + 2) * A +
    (2 + (1 + 1 + (1 + pOne χ)) + 10 + 1), ?_⟩
  intro h hχ
  subst hχ
  intro l _ c e hl2 he ψ hψ n' p₁ hcase
  have pl : l.Prime := Fact.out
  have hl : 2 ≤ l := pl.two_le
  have hN0 := h.N_pos
  have hchar := ((Host.mem_X h).1 hψ).1
  obtain ⟨-, -, hn0, -, -⟩ := cmDatum_char_two_adic_order_bounds h c.O ψ hchar l pl hl2
  have hidx := hostIndex h
  have hNe : 1 ≤ h.N * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hle : 1 ≤ l * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hlX : l ≤ l * h.N * e := by
    calc l = l * 1 := (mul_one _).symm
      _ ≤ l * (h.N * e) := Nat.mul_le_mul_left _ hNe
      _ = l * h.N * e := by ring
  have hNX : h.N ≤ l * h.N * e := by
    calc h.N = h.N * 1 := (mul_one _).symm
      _ ≤ h.N * (l * e) := Nat.mul_le_mul_left _ hle
      _ = l * h.N * e := by ring
  have h16 : 16 ≤ h.N := Nat.le_of_dvd hN0 hidx.2.2.1
  have hX16 : 16 ≤ l * h.N * e := h16.trans hNX
  have hX1 : 1 ≤ l * h.N * e := by omega
  have hX2 : 2 ≤ l * h.N * e := by omega
  have hqN : h.q ≤ h.N := Nat.le_of_dvd hN0 h.q_dvd
  have hoq : h.o ≤ h.q := hidx.2.2.2.2.1
  have hcN : 2 ^ c2 ψ ≤ h.N := Nat.le_of_dvd hN0 (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.2.1
  have hP : p₁ ≤ 1 + pOne h.chi := by
    rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  have hn : 2 ^ n' ≤ (l * h.N * e) ^ a := by
    rw [ha]
    rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · have key := nII_le (l * h.N * e) l h.N h.o h.q (c2 ψ) (n0 l ψ) (4 * h.o).totient hX16 hlX hNX
        ((hoq.trans hqN).trans hNX) (hqN.trans hNX) (hcN.trans hNX) hn0.le (by omega) hN0
      unfold Host.nII
      exact key.trans (Nat.pow_le_pow_right hX1 (Nat.le_add_right _ _))
    · have key := two_pow_nIII_le (X := l * h.N * e) (q := h.q) (P := pOne h.chi)
        (f := (4 * h.o).totient) hX2 hlX (by omega) hn0
      unfold Host.nIII
      exact key.trans (Nat.pow_le_pow_right hX1 (Nat.le_add_left _ _))
  exact final_le C A a (1 + pOne h.chi) h.o l n' h.N p₁ e hl hN0 (by omega) hP hn
end

