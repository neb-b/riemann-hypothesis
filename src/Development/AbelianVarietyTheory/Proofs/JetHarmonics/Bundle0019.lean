module

public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QdetTopThreeOrders
section
open Finset

namespace GlobalTheory.CapelliTop
variable {A : Type} [Ring A] {n : ℕ}

def oprod (S : Finset (Fin n)) (e : Fin n → A) : A :=
  (List.ofFn fun k => if k ∈ S then e k else 1).prod

theorem prod_add_expand [Algebra ℂ A] (c : Fin n → ℂ) (e : Fin n → A) :
    (List.ofFn fun k => c k • (1 : A) + e k).prod =
      ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, c k) • oprod S e := by
  have h := (MultilinearMap.mkPiAlgebraFin ℂ n A).map_add_univ e (fun k => c k • (1 : A))
  simp only [MultilinearMap.mkPiAlgebraFin_apply] at h
  have h0 : (fun k => c k • (1 : A) + e k) = e + fun k => c k • (1 : A) := by
    funext k; simp [add_comm]
  rw [h0, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 := (MultilinearMap.mkPiAlgebraFin ℂ n A).map_smul_univ (fun k => if k ∈ S then 1 else c k)
    (fun k => if k ∈ S then e k else 1)
  simp only [MultilinearMap.mkPiAlgebraFin_apply] at h1
  have h2 : S.piecewise e (fun k => c k • (1 : A)) =
      fun k => (if k ∈ S then (1 : ℂ) else c k) • (if k ∈ S then e k else 1) := by
    funext k; by_cases hk : k ∈ S <;> simp [hk]
  rw [h2, h1, oprod]
  congr 1
  rw [← Finset.prod_mul_prod_compl S, Finset.prod_eq_one (s := S) (fun k hk => by simp [hk]), one_mul]
  exact Finset.prod_congr rfl fun k hk => by simp [Finset.mem_compl.1 hk]

theorem list_ite {ι : Type} (p : ι → Prop) [DecidablePred p] (e : ι → A) (l : List ι) :
    (l.map fun k => if p k then e k else 1).prod = ((l.filter fun k => decide (p k)).map e).prod := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

theorem oprod_eq (S : Finset (Fin n)) (e : Fin n → A) (l : List (Fin n)) (hl : l.Pairwise (· < ·))
    (h : ∀ k, k ∈ l ↔ k ∈ S) : oprod S e = (l.map e).prod := by
  rw [oprod, List.ofFn_eq_map, list_ite]
  congr 2
  have h1 : ((List.finRange n).filter fun k => decide (k ∈ S)).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange n).filter _
  exact h1.eq_of_mem_iff hl (fun k => by simp [h])

def subdet (E : Fin n → Fin n → A) (S : Finset (Fin n)) : A :=
  ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ S → σ k = k),
    ((Equiv.Perm.sign σ : ℤ) : A) * oprod S (fun k => E (σ k) k)

theorem qdet_expand [Algebra ℂ A] (E : Fin n → Fin n → A) (u : ℂ) :
    Formalism.REAL.qdet E u = ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, (u - (k : ℂ))) • subdet E S := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  have h : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod =
      ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, (if σ k = k then u - (k : ℂ) else 0)) •
        oprod S (fun k => E (σ k) k) := by
    intro σ
    rw [← prod_add_expand]
    congr 2
    funext k
    by_cases hk : σ k = k <;> simp [Formalism.REAL.Tm, hk, Algebra.algebraMap_eq_smul_one]
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [subdet, Finset.smul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]
  split_ifs with hσ
  · congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [if_pos (hσ k (Finset.mem_compl.1 hk))]
  · push Not at hσ
    obtain ⟨k, hk, hk'⟩ := hσ
    rw [Finset.prod_eq_zero (Finset.mem_compl.2 hk) (if_neg hk'), zero_smul]

theorem subdet_empty (E : Fin n → Fin n → A) : subdet E ∅ = 1 := by
  have : univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ (∅ : Finset (Fin n)) → σ k = k) = {1} := by
    ext σ; simp [Equiv.ext_iff]
  rw [subdet, this, Finset.sum_singleton, oprod_eq _ _ [] (by simp) (by simp)]
  simp

theorem subdet_single (E : Fin n → Fin n → A) (i : Fin n) : subdet E {i} = E i i := by
  have : univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ ({i} : Finset (Fin n)) → σ k = k) = {1} := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      ext k
      by_cases hk : k = i
      · subst hk
        by_contra hne
        have hne' : σ k ≠ k := fun h' => hne (by simp [h'])
        exact hne' (σ.injective (h _ hne'))
      · simp [h k hk]
    · rintro rfl; simp
  rw [subdet, this, Finset.sum_singleton, oprod_eq _ _ [i] (by simp) (by simp)]
  simp

theorem subdet_pair (E : Fin n → Fin n → A) (i j : Fin n) (hij : i < j) :
    subdet E {i, j} = E i i * E j j - E j i * E i j := by
  have hne : i ≠ j := hij.ne
  have : univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ ({i, j} : Finset (Fin n)) → σ k = k) =
      {1, Equiv.swap i j} := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_singleton, mem_insert, not_or]
    constructor
    · intro h
      have key : ∀ k, k = i ∨ k = j → σ k = i ∨ σ k = j := by
        intro k hk
        by_contra hc
        have h1 := σ.injective (h _ (not_or.1 hc))
        rw [h1] at hc
        exact hc hk
      have hinj : σ i ≠ σ j := σ.injective.ne hne
      rcases key i (Or.inl rfl) with hi | hi <;> rcases key j (Or.inr rfl) with hj | hj
      · exact absurd (hi.trans hj.symm) hinj
      · left
        refine Equiv.ext fun k => ?_
        by_cases h1 : k = i
        · simp [h1, hi]
        by_cases h2 : k = j
        · simp [h2, hj]
        simp [h k ⟨h1, h2⟩]
      · right
        refine Equiv.ext fun k => ?_
        by_cases h1 : k = i
        · simp [h1, hi]
        by_cases h2 : k = j
        · simp [h2, hj]
        rw [h k ⟨h1, h2⟩, Equiv.swap_apply_of_ne_of_ne h1 h2]
      · exact absurd (hi.trans hj.symm) hinj
    · rintro (rfl | rfl) k hk
      · simp
      · exact Equiv.swap_apply_of_ne_of_ne hk.1 hk.2
  have h1 : (1 : Equiv.Perm (Fin n)) ≠ Equiv.swap i j := fun h => hne (Equiv.swap_eq_one_iff.1 h.symm)
  rw [subdet, this, Finset.sum_pair h1, oprod_eq _ _ [i, j] (by simp [hij]) (by simp),
    oprod_eq _ _ [i, j] (by simp [hij]) (by simp), Equiv.Perm.sign_swap hne]
  simp [sub_eq_add_neg]

theorem sum_split {M : Type} [AddCommMonoid M] (F : Finset (Fin n) → M) :
    ∑ S, F S = F ∅ + ∑ i, F {i} + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F {i, j} +
      ∑ S ∈ univ.filter (fun S : Finset (Fin n) => 3 ≤ S.card), F S := by
  have h0 : univ.filter (fun S : Finset (Fin n) => S.card = 0) = {∅} := by
    ext S; simp
  have h1 : ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 1), F S = ∑ i, F {i} := by
    symm
    refine Finset.sum_bij (fun i _ => {i}) (by simp) (by simp) ?_ (by simp)
    intro S hS
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 (mem_filter.1 hS).2
    exact ⟨a, mem_univ _, rfl⟩
  have h2 : ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 2), F S =
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F {i, j} := by
    rw [Finset.sum_sigma']
    symm
    refine Finset.sum_bij (fun p _ => {p.1, p.2}) ?_ ?_ ?_ (by simp)
    · rintro ⟨i, j⟩ hp
      have : i < j := by simpa using hp
      simp [Finset.card_pair this.ne]
    · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' h
      have a1 : i < j := by simpa using hp
      have a2 : i' < j' := by simpa using hp'
      have h' : ({i, j} : Finset (Fin n)) = {i', j'} := h
      have b1 : i ∈ ({i', j'} : Finset (Fin n)) := h' ▸ by simp
      have b2 : j ∈ ({i', j'} : Finset (Fin n)) := h' ▸ by simp
      have b3 : i' ∈ ({i, j} : Finset (Fin n)) := h' ▸ by simp
      simp only [mem_insert, mem_singleton] at b1 b2 b3
      have : i = i' ∧ j = j' := by omega
      obtain ⟨rfl, rfl⟩ := this
      rfl
    · intro S hS
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (mem_filter.1 hS).2
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨⟨a, b⟩, by simpa using h, rfl⟩
      · exact ⟨⟨b, a⟩, by simpa using h, Finset.pair_comm _ _⟩
  have h0' : F ∅ = ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 0), F S := by
    rw [h0, Finset.sum_singleton]
  rw [← h1, ← h2, h0']
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rcases hc : S.card with _ | _ | _ | m <;> simp

end GlobalTheory.CapelliTop

namespace GlobalTheory
open CapelliTop

theorem qdet_top_three_orders :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), ∃ Rm : ℕ → A, ∀ u : ℂ,
      Formalism.REAL.qdet E u = (∏ l : Fin n, (u - (l : ℂ))) • (1 : A) +
        ∑ i : Fin n, (∏ l ∈ univ.erase i, (u - (l : ℂ))) • E i i +
        ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j),
          (∏ l ∈ (univ.erase i).erase j, (u - (l : ℂ))) • (E i i * E j j - E j i * E i j) +
        ∑ d ∈ range (n - 2), u ^ d • Rm d := by
  intro A _ _ n E
  let p : Finset (Fin n) → Polynomial ℂ := fun S => ∏ k ∈ Sᶜ, (Polynomial.X - Polynomial.C (k : ℂ))
  refine ⟨fun d => ∑ S ∈ univ.filter (fun S : Finset (Fin n) => 3 ≤ S.card),
    (p S).coeff d • subdet E S, fun u => ?_⟩
  rw [qdet_expand, sum_split]
  congr 1
  · congr 1
    · congr 1
      · rw [subdet_empty, Finset.compl_empty]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [subdet_single, Finset.compl_singleton]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
      rw [subdet_pair E i j (mem_filter.1 hj).2]
      congr 2
      ext k; simp [and_comm]
  · simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hS3 := (mem_filter.1 hS).2
    have hle : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hdeg : (p S).natDegree < n - 2 := by
      have : (p S).natDegree = Sᶜ.card := Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ _
      rw [this, Finset.card_compl, Fintype.card_fin]
      omega
    have hev : (p S).eval u = ∏ k ∈ Sᶜ, (u - (k : ℂ)) := by
      simp [p, Polynomial.eval_prod]
    rw [← hev, Polynomial.eval_eq_sum_range' hdeg, Finset.sum_smul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_smul, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallCombinationStrictMinMod
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_zero' (hQ : ∀ x, 2 * Q x = Bf x x) : Q 0 = 0 := by
  have h := hQ 0
  simp only [map_zero, AddMonoidHom.zero_apply] at h
  omega

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_nonneg_of_pos (hQ : ∀ x, 2 * Q x = Bf x x) (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x)
    (x : X) : 0 ≤ Q x := by
  by_cases hx : x = 0
  · subst hx
    rw [quad_zero' hQ]
  · linarith [hpos x hx]

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_add_eq_add_add_bilin (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (x y : X) : Q (x + y) = Q x + Q y + Bf x y := by
  have h := hQ (x + y)
  simp only [map_add (f := _), AddMonoidHom.add_apply] at h
  linarith [hQ x, hQ y, hsym y x]

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_zsmul' (hQ : ∀ x, 2 * Q x = Bf x x) (k : ℤ) (x : X) :
    Q (k • x) = k ^ 2 * Q x := by
  have h := hQ (k • x)
  simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_eq_mul, zsmul_eq_mul] at h
  have h2 : 2 * Q (k • x) = 2 * (k ^ 2 * Q x) := by rw [h, ← hQ x]; ring
  exact mul_left_cancel₀ two_ne_zero h2

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma bilin_sq_le_four_mul_quad (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x) (x y : X) : Bf x y ^ 2 ≤ 4 * Q x * Q y := by
  by_cases hx : x = 0
  · subst hx
    rw [quad_zero' hQ]
    simp
  · have hx1 := hpos x hx
    have hw := quad_nonneg_of_pos hQ hpos (Bf x y • x + (-(2 * Q x)) • y)
    rw [quad_add_eq_add_add_bilin hsym hQ, quad_zsmul' hQ, quad_zsmul' hQ] at hw
    simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_eq_mul, zsmul_eq_mul] at hw
    nlinarith

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_add_le_add_sq_mul (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x) {x y : X} {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : 0 ≤ C) (hx : (Q x : ℝ) ≤ a ^ 2 * C) (hy : (Q y : ℝ) ≤ b ^ 2 * C) :
    (Q (x + y) : ℝ) ≤ (a + b) ^ 2 * C := by
  have hcs : (Bf x y : ℝ) ^ 2 ≤ 4 * (Q x : ℝ) * Q y := by
    exact_mod_cast bilin_sq_le_four_mul_quad hsym hQ hpos x y
  have hx0 : (0 : ℝ) ≤ Q x := by exact_mod_cast quad_nonneg_of_pos hQ hpos x
  have hy0 : (0 : ℝ) ≤ Q y := by exact_mod_cast quad_nonneg_of_pos hQ hpos y
  have hprod : (Q x : ℝ) * Q y ≤ (a ^ 2 * C) * (b ^ 2 * C) :=
    mul_le_mul hx hy hy0 (by positivity)
  have hB : (Bf x y : ℝ) ≤ 2 * a * b * C := by
    have h2 : (Bf x y : ℝ) ^ 2 ≤ (2 * a * b * C) ^ 2 := by nlinarith
    exact (abs_le_of_sq_le_sq' h2 (by positivity)).2
  have hadd : (Q (x + y) : ℝ) = Q x + Q y + Bf x y := by
    exact_mod_cast quad_add_eq_add_add_bilin hsym hQ x y
  rw [hadd]
  nlinarith

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_nsmul' (hQ : ∀ x, 2 * Q x = Bf x x) (m : ℕ) (x : X) :
    Q (m • x) = (m : ℤ) ^ 2 * Q x := by
  have h := quad_zsmul' hQ (m : ℤ) x
  rwa [natCast_zsmul] at h


variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
theorem _root_.GlobalTheory.small_combination_strict_min_mod :
    ∀ (X : Type) [AddCommGroup X] (Bf : X →+ X →+ ℤ) (Q : X → ℤ), (∀ x y, Bf x y = Bf y x) →
    (∀ x, 2 * Q x = Bf x x) → (∀ x, x ≠ 0 → 1 ≤ Q x) →
    ∀ (n D q : ℕ) (b : Fin n → X) (Cc M₀ : ℝ), 0 ≤ Cc → 0 ≤ M₀ → (∀ j, (Q (b j) : ℝ) ≤ Cc) →
    (∀ j z, |(Bf (b j) z : ℝ)| ≤ M₀ * Q z) → (D : ℝ) * M₀ < q →
    ∀ e : Fin n → ℕ, ∑ j, e j ≤ D →
    ((Q (∑ j, e j • b j) : ℝ) ≤ (D : ℝ) ^ 2 * Cc) ∧
      ∀ z, z ≠ 0 → Q (∑ j, e j • b j) < Q (∑ j, e j • b j + q • z) := by
  intro X _ Bf Q hsym hQ hpos n D q b Cc M₀ hCc hM₀ hb hBb hq e he
  have hsumR : (∑ j, (e j : ℝ)) ≤ D := by exact_mod_cast he
  have hsum0 : (0 : ℝ) ≤ ∑ j, (e j : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  constructor
  · have key : ∀ s : Finset (Fin n),
        (Q (∑ j ∈ s, e j • b j) : ℝ) ≤ (∑ j ∈ s, (e j : ℝ)) ^ 2 * Cc := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp [quad_zero' hQ]
      · intro j s hj ih
        rw [Finset.sum_insert hj, Finset.sum_insert hj]
        refine quad_add_le_add_sq_mul hsym hQ hpos (Nat.cast_nonneg _)
          (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hCc ?_ ih
        rw [quad_nsmul' hQ]
        push_cast
        exact mul_le_mul_of_nonneg_left (hb j) (by positivity)
    calc (Q (∑ j, e j • b j) : ℝ) ≤ (∑ j, (e j : ℝ)) ^ 2 * Cc := key Finset.univ
      _ ≤ (D : ℝ) ^ 2 * Cc :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hsum0 hsumR 2) hCc
  · intro z hz
    have hz1 : (1 : ℝ) ≤ Q z := by exact_mod_cast hpos z hz
    have hBv : Bf (∑ j, e j • b j) z = ∑ j, (e j : ℤ) * Bf (b j) z := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_nsmul, nsmul_eq_mul]
    have hBvR : (Bf (∑ j, e j • b j) z : ℝ) = ∑ j, (e j : ℝ) * Bf (b j) z := by
      rw [hBv]; push_cast; rfl
    have hMz : (0 : ℝ) ≤ M₀ * Q z := mul_nonneg hM₀ (by linarith)
    have habs : |(Bf (∑ j, e j • b j) z : ℝ)| ≤ (∑ j, (e j : ℝ)) * (M₀ * Q z) := by
      rw [hBvR, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hBb j z) (Nat.cast_nonneg _)
    have h2 : (∑ j, (e j : ℝ)) * (M₀ * Q z) ≤ D * (M₀ * Q z) :=
      mul_le_mul_of_nonneg_right hsumR hMz
    have hlow := neg_abs_le (Bf (∑ j, e j • b j) z : ℝ)
    have hbound : -((D : ℝ) * M₀ * Q z) ≤ (Bf (∑ j, e j • b j) z : ℝ) := by nlinarith
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) hM₀) hq
    have hadd : (Q (∑ j, e j • b j + q • z) : ℝ)
        = Q (∑ j, e j • b j) + (q : ℝ) ^ 2 * Q z + q * Bf (∑ j, e j • b j) z := by
      rw [quad_add_eq_add_add_bilin hsym hQ, quad_nsmul' hQ, map_nsmul, nsmul_eq_mul]
      push_cast
      ring
    have hfin : (Q (∑ j, e j • b j) : ℝ) < Q (∑ j, e j • b j + q • z) := by
      rw [hadd]
      nlinarith [mul_pos hq0 (mul_pos (show (0 : ℝ) < q - D * M₀ by linarith)
        (show (0 : ℝ) < Q z by linarith)),
        mul_nonneg hq0.le (show (0 : ℝ) ≤ Bf (∑ j, e j • b j) z + D * M₀ * Q z by linarith)]
    exact_mod_cast hfin

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorEqZeroOfForallGeometricPoint
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem exists_algHom_ker_eq_of_isMaximal (F B : Type) [Field F] [IsAlgClosed F] [CommRing B]
    [Algebra F B] [Module.Finite F B] (m : Ideal B) [m.IsMaximal] :
    ∃ ψ : B →ₐ[F] F, ∀ b, ψ b = 0 → b ∈ m := by
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  have hb : Function.Bijective (algebraMap F (B ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : F ≃ₐ[F] (B ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ m)) hb
  refine ⟨(e.symm : (B ⧸ m) →ₐ[F] F).comp (Ideal.Quotient.mkₐ F m), fun b h => ?_⟩
  have h' : e.symm (Ideal.Quotient.mk m b) = 0 := h
  rw [map_eq_zero_iff _ e.symm.injective] at h'
  exact Ideal.Quotient.eq_zero_iff_mem.mp h'

theorem tensor_eq_zero_of_forall_geometric_point :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] [IsReduced (TensorProduct O F A)] (M : Type) [AddCommGroup M] [Module O M] [Module.Flat O M] (t : TensorProduct O A M), (∀ φ : A →ₐ[O] F, TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) t = 0) → t = 0 := by
  intro O F _ _ _ _ hinj A _ _ _ _ _ M _ _ _ t ht
  classical
  haveI : IsArtinianRing (TensorProduct O F A) := IsArtinianRing.of_finite F _
  have hpt : ∀ m : MaximalSpectrum (TensorProduct O F A),
      ∃ ψ : TensorProduct O F A →ₐ[F] F, ∀ b, ψ b = 0 → b ∈ m.asIdeal := fun m =>
    haveI := m.isMaximal
    exists_algHom_ker_eq_of_isMaximal F _ m.asIdeal
  choose ψ hψ using hpt
  let φ : MaximalSpectrum (TensorProduct O F A) → (A →ₐ[O] F) := fun m =>
    ((ψ m).restrictScalars O).comp Algebra.TensorProduct.includeRight
  let L : A →ₗ[O] (MaximalSpectrum (TensorProduct O F A) → F) :=
    LinearMap.pi fun m => (φ m).toLinearMap
  have hR : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[O] TensorProduct O F A) :=
    Algebra.TensorProduct.includeRight_injective hinj
  have hL : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    apply hR
    rw [map_zero]
    have hmem : (Algebra.TensorProduct.includeRight a : TensorProduct O F A) ∈
        Ideal.jacobson (⊥ : Ideal (TensorProduct O F A)) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro J ⟨-, hJ⟩
      exact hψ ⟨J, hJ⟩ _ (congrFun ha ⟨J, hJ⟩)
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := TensorProduct O F A)
    have h2 := Ideal.pow_mem_pow hmem n
    rw [hn] at h2
    exact IsNilpotent.eq_zero ⟨n, by simpa using h2⟩
  have hLM : Function.Injective (L.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap L hL
  haveI : Fintype (MaximalSpectrum (TensorProduct O F A)) := Fintype.ofFinite _
  apply hLM
  rw [map_zero]
  apply (TensorProduct.piLeft O M (fun _ : MaximalSpectrum (TensorProduct O F A) => F)).injective
  rw [map_zero]
  funext m
  have key : ∀ s : TensorProduct O A M,
      TensorProduct.piLeft O M (fun _ : MaximalSpectrum (TensorProduct O F A) => F)
        (L.rTensor M s) m
      = TensorProduct.map (φ m).toLinearMap (LinearMap.id : M →ₗ[O] M) s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [L, TensorProduct.piLeft]
    | add s s' h h' => rw [map_add (f := _), map_add (f := _), Pi.add_apply, h, h', map_add (f := _)]
  rw [key, ht]
  rfl

end GlobalTheory
end

