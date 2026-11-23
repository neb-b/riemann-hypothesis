module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.G6Decomposition
section
namespace UpperTheory.Reformulated.B.StringRepresentationDecomposition

open Matrix

section

variable {K : Type*} [NormedField K]

private def Small {a b : Type*} (A : Matrix a b K) : Prop := ∀ i j, ‖A i j‖ ≤ 1

private def Good {a : Type*} [Fintype a] [DecidableEq a] (A : Matrix a a K) : Prop :=
  Small A ∧ ∃ B : Matrix a a K, Small B ∧ A * B = 1

private def Smith {a : Type*} [Fintype a] [DecidableEq a] (M : Matrix a a K) : Prop :=
  ∃ (U V : Matrix a a K) (d : a → K), Good U ∧ Good V ∧ M = U * diagonal d * V

private lemma small_zero {a b : Type*} : Small (0 : Matrix a b K) := by
  intro i j; simp

private lemma small_one {a : Type*} [DecidableEq a] : Small (1 : Matrix a a K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

private lemma small_neg {a b : Type*} {A : Matrix a b K} (h : Small A) : Small (-A) := by
  intro i j; simpa using h i j

private lemma small_blocks {a b : Type*} {A : Matrix a a K} {B : Matrix a b K}
    {C : Matrix b a K} {D : Matrix b b K} (hA : Small A) (hB : Small B) (hC : Small C)
    (hD : Small D) : Small (fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  exacts [hA i j, hB i j, hC i j, hD i j]

private lemma small_mul [IsUltrametricDist K] {a : Type*} [Fintype a] {A B : Matrix a a K}
    (hA : Small A) (hB : Small B) : Small (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro k _
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

private lemma good_one {a : Type*} [Fintype a] [DecidableEq a] : Good (1 : Matrix a a K) :=
  ⟨small_one, 1, small_one, Matrix.mul_one _⟩

private lemma good_mul [IsUltrametricDist K] {a : Type*} [Fintype a] [DecidableEq a]
    {A B : Matrix a a K} (hA : Good A) (hB : Good B) : Good (A * B) := by
  obtain ⟨h1, A', h2, h3⟩ := hA
  obtain ⟨h4, B', h5, h6⟩ := hB
  refine ⟨small_mul h1 h4, B' * A', small_mul h5 h2, ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h6, Matrix.one_mul, h3]

private lemma good_submatrix {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {A : Matrix a a K} (hA : Good A) (f g : b ≃ a) :
    Good (A.submatrix f g) := by
  obtain ⟨h1, A', h2, h3⟩ := hA
  refine ⟨fun i j => h1 _ _, A'.submatrix g f, fun i j => h2 _ _, ?_⟩
  rw [Matrix.submatrix_mul_equiv, h3, Matrix.submatrix_one_equiv]

private lemma smith_submatrix {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {M : Matrix a a K} (hM : Smith M) (f g : b ≃ a) :
    Smith (M.submatrix f g) := by
  obtain ⟨U, V, d, hU, hV, rfl⟩ := hM
  refine ⟨U.submatrix f f, V.submatrix f g, d ∘ f, good_submatrix hU f f,
    good_submatrix hV f g, ?_⟩
  rw [← Matrix.submatrix_diagonal_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

private lemma smith_mul [IsUltrametricDist K] {a : Type*} [Fintype a] [DecidableEq a]
    {L M R : Matrix a a K} (hL : Good L) (hM : Smith M) (hR : Good R) :
    Smith (L * M * R) := by
  obtain ⟨U, V, d, hU, hV, rfl⟩ := hM
  exact ⟨L * U, V * R, d, good_mul hL hU, good_mul hV hR, by simp only [Matrix.mul_assoc]⟩

private lemma good_lower {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {C : Matrix b a K} (hC : Small C) :
    Good (fromBlocks (1 : Matrix a a K) 0 C (1 : Matrix b b K)) := by
  refine ⟨small_blocks small_one small_zero hC small_one, fromBlocks 1 0 (-C) 1,
    small_blocks small_one small_zero (small_neg hC) small_one, ?_⟩
  simp [Matrix.fromBlocks_multiply]

private lemma good_upper {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {C : Matrix a b K} (hC : Small C) :
    Good (fromBlocks (1 : Matrix a a K) C 0 (1 : Matrix b b K)) := by
  refine ⟨small_blocks small_one hC small_zero small_one, fromBlocks 1 (-C) 0 1,
    small_blocks small_one (small_neg hC) small_zero small_one, ?_⟩
  simp [Matrix.fromBlocks_multiply]

private lemma good_diag {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {U : Matrix b b K} (hU : Good U) :
    Good (fromBlocks (1 : Matrix a a K) 0 0 U) := by
  obtain ⟨h1, U', h2, h3⟩ := hU
  refine ⟨small_blocks small_one small_zero small_zero h1, fromBlocks 1 0 0 U',
    small_blocks small_one small_zero small_zero h2, ?_⟩
  simp [Matrix.fromBlocks_multiply, h3]

private lemma smith_diag {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (c : a → K) {D : Matrix b b K} (hD : Smith D) :
    Smith (fromBlocks (diagonal c) 0 0 D) := by
  obtain ⟨U, V, d, hU, hV, rfl⟩ := hD
  refine ⟨fromBlocks 1 0 0 U, fromBlocks 1 0 0 V, Sum.elim c d, good_diag hU, good_diag hV, ?_⟩
  rw [← Matrix.fromBlocks_diagonal]
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add]

private lemma smith_step [IsUltrametricDist K] {b : Type*} [Fintype b] [DecidableEq b]
    (ih : ∀ D : Matrix b b K, Smith D) (N : Matrix (Unit ⊕ b) (Unit ⊕ b) K)
    (hN : ∀ i j, ‖N i j‖ ≤ ‖N (Sum.inl ()) (Sum.inl ())‖) : Smith N := by
  set x := N (Sum.inl ()) (Sum.inl ()) with hx
  by_cases h0 : x = 0
  · refine ⟨1, 1, 0, good_one, good_one, ?_⟩
    ext i j
    have := hN i j
    rw [h0, norm_zero] at this
    simp [norm_le_zero_iff.mp this, Matrix.diagonal_apply]
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr h0
  let C : Matrix b Unit K := Matrix.of fun i _ => N (Sum.inr i) (Sum.inl ()) / x
  let B : Matrix Unit b K := Matrix.of fun _ j => N (Sum.inl ()) (Sum.inr j) / x
  let D : Matrix b b K := Matrix.of fun i j => N (Sum.inr i) (Sum.inr j) -
    N (Sum.inr i) (Sum.inl ()) * N (Sum.inl ()) (Sum.inr j) / x
  have hC : Small C := fun i j => by
    simp only [C, Matrix.of_apply, norm_div]
    exact (div_le_one hpos).mpr (hN _ _)
  have hB : Small B := fun i j => by
    simp only [B, Matrix.of_apply, norm_div]
    exact (div_le_one hpos).mpr (hN _ _)
  have key : N = fromBlocks 1 0 C 1 * fromBlocks (diagonal fun _ => x) 0 0 D
      * fromBlocks 1 B 0 1 := by
    simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
    ext (i | i) (j | j)
    · simp [hx]
    · simp [B, Matrix.mul_apply]
      field_simp
    · simp [C, Matrix.mul_apply, h0]
    · simp [B, C, D, Matrix.mul_apply]
      field_simp
      ring
  rw [key]
  exact smith_mul (good_lower hC) (smith_diag _ (ih D)) (good_upper hB)

private lemma smith_fin [IsUltrametricDist K] (n : ℕ) :
    ∀ M : Matrix (Fin n) (Fin n) K, Smith M := by
  induction n with
  | zero => exact fun M => ⟨1, 1, 0, good_one, good_one, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro M
    obtain ⟨⟨p, q⟩, hpq⟩ := Finite.exists_max (fun x : Fin (n + 1) × Fin (n + 1) => ‖M x.1 x.2‖)
    let e : Fin (n + 1) ≃ Unit ⊕ Fin n := Fintype.equivOfCardEq (by simp [add_comm])
    let f : Fin (n + 1) ≃ Unit ⊕ Fin n := e.trans (Equiv.swap (e p) (Sum.inl ()))
    let g : Fin (n + 1) ≃ Unit ⊕ Fin n := e.trans (Equiv.swap (e q) (Sum.inl ()))
    have hf : f.symm (Sum.inl ()) = p := by simp [f]
    have hg : g.symm (Sum.inl ()) = q := by simp [g]
    have h := smith_step ih (M.submatrix f.symm g.symm) (fun i j => by
      simp only [Matrix.submatrix_apply, hf, hg]
      exact hpq (_, _))
    have h2 := smith_submatrix h f g
    simpa using h2

private lemma good_gl {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : Good A) :
    ∃ U : GL (Fin n) K, (↑U : Matrix (Fin n) (Fin n) K) = A ∧
      Small (↑U⁻¹ : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨_, B, h2, h3⟩ := hA
  exact ⟨⟨A, B, h3, mul_eq_one_comm.mp h3⟩, rfl, h2⟩

end

end UpperTheory.Reformulated.B.StringRepresentationDecomposition

theorem UpperTheory.Reformulated.B.StringRepresentationDecomposition.smith_gen.{u_1} :
    ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] {n : ℕ} (P : GL (Fin n) K),
      ∃ (U : GL (Fin n) K) (V : GL (Fin n) K) (d : Fin n → K),
        (∀ (i j : Fin n), ‖(↑U : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
          (∀ (i j : Fin n), ‖(↑U⁻¹ : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
            (∀ (i j : Fin n), ‖(↑V : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
              (∀ (i j : Fin n), ‖(↑V⁻¹ : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
                (∀ (i : Fin n), d i ≠ (0 : K)) ∧
                  (↑P : Matrix (Fin n) (Fin n) K) =
                    (↑U : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d * (↑V : Matrix (Fin n) (Fin n) K) := by
  intro K _ _ n P
  obtain ⟨A, B, d, hA, hB, h⟩ := smith_fin n (↑P : Matrix (Fin n) (Fin n) K)
  obtain ⟨U, rfl, hU⟩ := good_gl hA
  obtain ⟨V, rfl, hV⟩ := good_gl hB
  refine ⟨U, V, d, hA.1, hU, hB.1, hV, ?_, h⟩
  have hdet : (↑P : Matrix (Fin n) (Fin n) K).det ≠ 0 := P.det_ne_zero
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  intro i
  exact Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul hdet)) i
    (Finset.mem_univ i)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GaloisBoundSecond
section
open NumberField

private lemma norm_le_prod {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (I : Ideal (RingOfIntegers F)) (y : RingOfIntegers F) (hy : y ∈ I) (h0 : y ≠ 0) :
    (Ideal.absNorm I : ℝ) ≤ ∏ w : InfinitePlace F, w (y : F) := by
  have hdvd : Ideal.absNorm I ∣ Ideal.absNorm (Ideal.span {y}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem I).2 hy)
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hpos : 0 < (Algebra.norm ℤ y).natAbs := by
    rw [Int.natAbs_pos]
    exact (Algebra.norm_ne_zero_iff).2 h0
  have hle := Nat.le_of_dvd hpos hdvd
  have hprod : ∏ w : InfinitePlace F, w (y : F) = ((|Algebra.norm ℚ (y : F)| : ℚ) : ℝ) := by
    rw [← InfinitePlace.prod_eq_abs_norm]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(NumberField.IsTotallyReal.isReal w).mult_eq_one, pow_one]
  rw [hprod, ← Algebra.coe_norm_int]
  have : ((Algebra.norm ℤ y).natAbs : ℝ) = |((Algebra.norm ℤ y : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h2 : (Ideal.absNorm I : ℝ) ≤ ((Algebra.norm ℤ y).natAbs : ℝ) := by exact_mod_cast hle
  rw [this] at h2
  push_cast
  exact h2

private lemma sep {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (N : ℕ) (hN : 0 < N) (I : Ideal (RingOfIntegers F)) (x x' : F)
    (hx : ∃ y ∈ I, (y : F) = (N : F) * x) (hx' : ∃ y ∈ I, (y : F) = (N : F) * x') (hne : x ≠ x') :
    (Ideal.absNorm I : ℝ) ≤ ∏ w : InfinitePlace F, w ((N : F) * (x - x')) := by
  obtain ⟨y, hy, hyx⟩ := hx
  obtain ⟨y', hy', hyx'⟩ := hx'
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoe : ((y - y' : RingOfIntegers F) : F) = (N : F) * (x - x') := by
    have e : ((y - y' : RingOfIntegers F) : F) = (y : F) - (y' : F) := map_sub _ _ _
    rw [e, hyx, hyx']
    ring
  have h0 : y - y' ≠ 0 := by
    intro h
    rw [h] at hcoe
    have : (N : F) * (x - x') = 0 := by simpa using hcoe.symm
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hN' h1
    · exact hne (sub_eq_zero.1 h1)
  have := norm_le_prod I (y - y') (I.sub_mem hy hy') h0
  rwa [hcoe] at this

private lemma key {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (N : ℕ) (hN : 0 < N) (I : Ideal (RingOfIntegers F)) (hI : I ≠ ⊥) (B : ℝ) (hB : 0 ≤ B)
    (S : Set F)
    (hS : S = {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = (N : F) * x) ∧
      ∀ w : InfinitePlace F, (w : F → ℝ) x ≤ B}) :
    S.Finite ∧ (S.ncard : ℝ) * (Ideal.absNorm I : ℝ) ≤ (4 * B * N) ^ Module.finrank ℚ F := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rcases S.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
  · subst hE
    refine ⟨Set.finite_empty, ?_⟩
    simp only [Set.ncard_empty, Nat.cast_zero, zero_mul]
    positivity
  have hmem : ∀ x, x ∈ S → x ≠ 0 ∧ (∃ y ∈ I, (y : F) = (N : F) * x) ∧
      ∀ w : InfinitePlace F, (w : F → ℝ) x ≤ B := fun x hx => by
    rw [hS] at hx; exact hx
  set n := Module.finrank ℚ F with hn_def
  have hn : 0 < n := Module.finrank_pos
  have hcard : Fintype.card (InfinitePlace F) = n := by
    rw [hn_def, ← InfinitePlace.sum_mult_eq, Finset.card_univ.symm, Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun w _ => ((NumberField.IsTotallyReal.isReal w).mult_eq_one).symm
  set C : ℝ := B * N with hC
  have hC0 : 0 ≤ C := by positivity
  set A : ℝ := (Ideal.absNorm I : ℝ) with hA
  have hA0 : 0 < A := by
    have : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    rw [hA]; exact_mod_cast Nat.pos_of_ne_zero this
  set s : ℝ := A ^ ((n : ℝ)⁻¹) with hs_def
  have hs : s ^ n = A := Real.rpow_inv_natCast_pow hA0.le hn.ne'
  have hs0 : 0 < s := Real.rpow_pos_of_pos hA0 _
  have hN'F : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hwN : ∀ (w : InfinitePlace F) (z : F), w ((N : F) * z) = N * w z := by
    intro w z
    rw [map_mul]
    congr 1
    have := w.norm_embedding_eq (N : F)
    rw [← this]
    simp
  have hAC : A ≤ C ^ n := by
    have h1 := sep N hN I x0 0 (hmem x0 hx0).2.1 ⟨0, I.zero_mem, by simp⟩ (hmem x0 hx0).1
    refine h1.trans ?_
    rw [← hcard, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun w _ => w.1.nonneg _) fun w _ => ?_
    rw [sub_zero, hwN, hC, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hmem x0 hx0).2.2 w) hNr.le
  have hsC : s ≤ C := by
    have : s ^ n ≤ C ^ n := by rw [hs]; exact hAC
    exact (pow_le_pow_iff_left₀ hs0.le hC0 hn.ne').1 this
  let ρ : InfinitePlace F → (F →+* ℝ) := fun w =>
    InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w)
  have hρ : ∀ w z, |ρ w z| = w z := fun w z => by
    simpa [Real.norm_eq_abs] using
      InfinitePlace.norm_embedding_of_isReal (NumberField.IsTotallyReal.isReal w) z
  set K : ℤ := ⌊2 * C / s⌋ with hK
  let f : F → InfinitePlace F → ℤ := fun x w => ⌊((N : ℝ) * ρ w x + C) / s⌋
  let T : Finset (InfinitePlace F → ℤ) := Fintype.piFinset fun _ => Finset.Icc 0 K
  have hmaps : ∀ x ∈ S, f x ∈ (T : Set (InfinitePlace F → ℤ)) := by
    intro x hx
    simp only [T, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro w
    have hb : |ρ w x| ≤ B := by rw [hρ]; exact (hmem x hx).2.2 w
    obtain ⟨hb1, hb2⟩ := abs_le.1 hb
    have h1 : -C ≤ (N : ℝ) * ρ w x := by
      have := mul_le_mul_of_nonneg_left hb1 hNr.le
      rw [hC]; linarith
    have h2 : (N : ℝ) * ρ w x ≤ C := by
      have := mul_le_mul_of_nonneg_left hb2 hNr.le
      rw [hC]; linarith
    constructor
    · exact Int.floor_nonneg.2 (div_nonneg (by linarith) hs0.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hs0.le)
  have hinj : Set.InjOn f S := by
    intro x hx x' hx' hff
    by_contra hne
    have h1 := sep N hN I x x' (hmem x hx).2.1 (hmem x' hx').2.1 hne
    have hz : (N : F) * (x - x') ≠ 0 := mul_ne_zero hN'F (sub_ne_zero.2 hne)
    have h2 : ∏ w : InfinitePlace F, w ((N : F) * (x - x')) < ∏ _w : InfinitePlace F, s := by
      refine Finset.prod_lt_prod_of_nonempty₀ (fun w _ => w.pos_iff.2 hz) (fun w _ => ?_)
        Finset.univ_nonempty
      have hw := congrFun hff w
      have h3 := Int.abs_sub_lt_one_of_floor_eq_floor hw
      rw [← sub_div, abs_div, abs_of_pos hs0, div_lt_one hs0] at h3
      have h4 : w ((N : F) * (x - x')) = |(N : ℝ) * ρ w x + C - ((N : ℝ) * ρ w x' + C)| := by
        rw [hwN, ← hρ w (x - x'), map_sub, ← abs_of_pos hNr, ← abs_mul, abs_of_pos hNr]
        congr 1
        ring
      rw [h4]
      exact h3
    rw [Finset.prod_const, Finset.card_univ, hcard, hs] at h2
    linarith
  have hTfin : (T : Set (InfinitePlace F → ℤ)).Finite := T.finite_toSet
  refine ⟨Set.Finite.of_injOn (f := f) hmaps hinj hTfin, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn f hmaps hinj hTfin
  have hK0 : 0 ≤ K := Int.floor_nonneg.2 (by positivity)
  have hTc : (T : Set (InfinitePlace F → ℤ)).ncard = (K.toNat + 1) ^ n := by
    rw [Set.ncard_coe_finset]
    simp only [T, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ, hcard]
    congr 1
    omega
  rw [hTc] at hle
  have hle' : (S.ncard : ℝ) ≤ ((K : ℝ) + 1) ^ n := by
    have : (S.ncard : ℝ) ≤ (((K.toNat + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast hle
    refine this.trans (le_of_eq ?_)
    push_cast
    congr 2
    exact_mod_cast Int.toNat_of_nonneg hK0
  have hKs : ((K : ℝ) + 1) * s ≤ 4 * C := by
    have h1 : (K : ℝ) ≤ 2 * C / s := Int.floor_le _
    have h2 : (K : ℝ) * s ≤ 2 * C := (le_div_iff₀ hs0).1 h1
    nlinarith
  have hK1 : (0 : ℝ) ≤ (K : ℝ) + 1 := by
    have : (0 : ℝ) ≤ K := by exact_mod_cast hK0
    linarith
  calc (S.ncard : ℝ) * A ≤ ((K : ℝ) + 1) ^ n * s ^ n := by
        rw [hs]; exact mul_le_mul_of_nonneg_right hle' hA0.le
    _ = (((K : ℝ) + 1) * s) ^ n := (mul_pow _ _ _).symm
    _ ≤ (4 * C) ^ n := pow_le_pow_left₀ (by positivity) hKs n
    _ = (4 * B * N) ^ n := by rw [hC]; ring_nf

theorem UpperTheory.Reformulated.B.GaloisBoundSecond.main :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] [NumberField.IsTotallyReal F] (N : ℕ),
      (0 : ℕ) < N →
        ∀ (I : Ideal (NumberField.RingOfIntegers F)),
          I ≠ ⊥ →
            ∀ (B : ℝ),
              (0 : ℝ) ≤ B →
                {x : F |
                      x ≠ (0 : F) ∧
                        (∃ y ∈ I, (↑y : F) = (↑N : F) * x) ∧
                          ∀ (w : NumberField.InfinitePlace F), (w : F → ℝ) x ≤ B}.Finite ∧
                  (↑{x : F |
                              x ≠ (0 : F) ∧
                                (∃ y ∈ I, (↑y : F) = (↑N : F) * x) ∧
                                  ∀ (w : NumberField.InfinitePlace F), (w : F → ℝ) x ≤ B}.ncard :
                        ℝ) *
                      (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers F) → ℕ) I) : ℝ) ≤
                    ((4 : ℝ) * B * (↑N : ℝ)) ^ Module.finrank ℚ F := by
  intro F _ _ _ N hN I hI B hB
  exact key N hN I hI B hB _ rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GlR
section
noncomputable def UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR :
    {K : Type} → [inst : CommRing K] → Subring K → (n : ℕ) → Subgroup (GL (Fin n) K) :=
  fun {K} _ R n =>
  { carrier := {g | (∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ R) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ R}
    one_mem' := by
      have h : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) K) i j ∈ R := fun i j => by
        rw [Matrix.one_apply]
        split_ifs
        exacts [R.one_mem, R.zero_mem]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [Units.val_one]
        exact h i j
      · rw [inv_one, Units.val_one]
        exact h i j
    mul_mem' := by
      rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [Units.val_mul, Matrix.mul_apply]
        exact R.sum_mem fun k _ => R.mul_mem (ha i k) (hb k j)
      · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
        exact R.sum_mem fun k _ => R.mul_mem (hb' i k) (ha' k j)
    inv_mem' := by
      rintro a ⟨ha, ha'⟩
      refine ⟨ha', fun i j => ?_⟩
      rw [inv_inv]
      exact ha i j }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GradedSpanProducts
section
noncomputable def UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan.{u_1} :
    {Ω : Type u_1} → [inst : CommRing Ω] → {q r : ℕ} → (Fin q → Ω) → (Fin r → ℕ) → (Fin r → Ω) → ℕ → AddSubgroup Ω :=
    fun {Ω : Type u_1} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω) (n : ℕ) ↦
      AddSubgroup.closure
        {x : Ω | ∃ (l : Fin r) (μ : Fin q → ℕ), d l + ∑ j : Fin q, μ j = n ∧ x = t l * ∏ j : Fin q, w j ^ μ j}

@[reducible] noncomputable def UpperTheory.Reformulated.B.GradedSpanProducts.pc :
    {Ω : Type} → [inst : Field Ω] → {q : ℕ} → (Fin q → Ω) → ℕ → AddSubgroup Ω :=
    fun {Ω : Type} [Field Ω] {q : ℕ} (w : Fin q → Ω) (n : ℕ) ↦
      UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan w (fun (x : Fin (1 : ℕ)) ↦ (0 : ℕ)) (fun (x : Fin (1 : ℕ)) ↦ (1 : Ω)) n

theorem UpperTheory.Reformulated.B.GradedSpanProducts.pc_mul :
    ∀ {Ω : Type} [inst : Field Ω] {q : ℕ} (w : Fin q → Ω) {a b : ℕ} {x z : Ω},
      x ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w a → z ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w b → x * z ∈ UpperTheory.Reformulated.B.GradedSpanProducts.pc w (a + b) := by
  intro Ω _ q w a b x z hx hz
  unfold UpperTheory.Reformulated.B.GradedSpanProducts.pc UpperTheory.Reformulated.B.GradedSpanProducts.gradedSpan at *
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨l, μ, hμ, rfl⟩ := hx
      obtain ⟨_, ν, hν, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨l, fun j => μ j + ν j, ?_, ?_⟩
      · simp only [zero_add] at hμ hν ⊢
        rw [Finset.sum_add_distrib, hμ, hν]
      · simp only [one_mul, pow_add, Finset.prod_mul_distrib]
    | zero => rw [mul_zero]; exact AddSubgroup.zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact AddSubgroup.add_mem _ h1 h2
    | neg z _ h => rw [mul_neg]; exact AddSubgroup.neg_mem _ h
  | zero => rw [zero_mul]; exact AddSubgroup.zero_mem _
  | add x y _ _ h1 h2 => rw [add_mul]; exact AddSubgroup.add_mem _ h1 h2
  | neg x _ h => rw [neg_mul]; exact AddSubgroup.neg_mem _ h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HeckeMap
section
noncomputable def UpperTheory.Reformulated.B.Qf17.heckePol :
    {A : Type} → [inst : CommRing A] → ℕ → ℕ → (ℕ → A) → Polynomial A :=
    fun {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) ↦
      ∑ j ∈ Finset.range (n + (1 : ℕ)),
        (Polynomial.C : A → Polynomial A) ((-1 : A) ^ j * (↑q : A) ^ (j * (j - (1 : ℕ)) / (2 : ℕ)) * a j) *
          Polynomial.X ^ (n - j)

theorem UpperTheory.Reformulated.B.Qf17.hecke_map :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A),
      Polynomial.map f (UpperTheory.Reformulated.B.Qf17.heckePol n q a) = UpperTheory.Reformulated.B.Qf17.heckePol n q fun (j : ℕ) ↦ (f : A → B) (a j) := by
  intro A B _ _ f n q a
  unfold UpperTheory.Reformulated.B.Qf17.heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    map_mul f, map_mul f, map_pow f, map_pow f, map_neg f, map_one f, map_natCast f]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IofAdd
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk7.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qk7.iof_add :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] {x y : UpperTheory.Reformulated.B.Qk7.Om v}, ‖x‖ < (1 : ℝ) → ‖y‖ < (1 : ℝ) → ‖x + y‖ < (1 : ℝ) := by
  intro v inst x y hx hy
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x y) (max_lt hx hy)
end

