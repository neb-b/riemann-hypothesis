module

public import Development.AutomorphicArithmetic.ThickFrames.MarkedLow

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThickFrames.SharesOfCounts
section
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.shares_of_counts :
    ∀ (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A) (T : Finset A) (δ η D : ℝ),
      0 < δ → η ≤ 1 → 0 ≤ D → 4 * A0.index * D ≤ η * (δ * Nat.card A0) →
      (∀ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) - (if γ ∈ A0 then δ else 3 / 4 * δ) * Nat.card A0| ≤ D) →
      δ * Fintype.card A / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card A ∧
        ∀ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) -
          (if γ ∈ A0 then 4 else 3) / (3 * (A0.index : ℝ) + 1) * (T.card : ℝ)| ≤ η * (T.card : ℝ) := by
  intro A _ _ _ A0 T δ η D hδ hη hD hDη hc
  set m : ℕ := A0.index with hm_def
  set n : ℕ := Nat.card A0 with hn_def
  have hm : (1:ℝ) ≤ m := by
    have h0 : A0.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  have hn : (1:ℝ) ≤ n := by
    have h0 : 0 < Nat.card A0 := Nat.card_pos
    exact_mod_cast h0
  have hA : (Fintype.card A : ℝ) = m * n := by
    have h1 : n * m = Fintype.card A := by
      rw [hn_def, hm_def, A0.card_mul_index, Nat.card_eq_fintype_card]
    rw [← h1]
    push_cast
    ring
  have hcardA0 : (Finset.univ.filter fun x : A => x ∈ A0).card = n := by
    rw [hn_def, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsumN : ∑ γ : A, (T.filter fun t => t - γ ∈ A0).card = T.card * n := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have inner : ∀ t : A, (∑ γ : A, if t - γ ∈ A0 then 1 else 0) = n := by
      intro t
      have h2 := Equiv.sum_comp (Equiv.subLeft t) (fun x => if x ∈ A0 then (1:ℕ) else 0)
      simp only [Equiv.subLeft_apply] at h2
      rw [h2, ← Finset.card_filter]
      exact hcardA0
    rw [Finset.sum_congr rfl (fun t _ => inner t), Finset.sum_const, smul_eq_mul]
  have hsum : (∑ γ : A, ((T.filter fun t => t - γ ∈ A0).card : ℝ)) = n * T.card := by
    have h3 := congrArg (Nat.cast : ℕ → ℝ) hsumN
    push_cast at h3
    rw [h3]
    ring
  have hf : (∑ γ : A, (if γ ∈ A0 then δ else 3 / 4 * δ) * (n:ℝ)) = (3 * m + 1) / 4 * δ * n * n := by
    have hpt : ∀ γ : A, (if γ ∈ A0 then δ else 3 / 4 * δ) * (n:ℝ)
        = 3 / 4 * δ * n + (if γ ∈ A0 then δ / 4 * n else 0) := by
      intro γ
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun γ _ => hpt γ), Finset.sum_add_distrib, ← Finset.sum_filter,
      Finset.sum_const, Finset.sum_const, hcardA0, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, hA]
    ring
  have hdiff : |(n:ℝ) * T.card - (3 * m + 1) / 4 * δ * n * n| ≤ m * n * D := by
    rw [← hsum, ← hf, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) - (if γ ∈ A0 then δ else 3 / 4 * δ) * n| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ γ : A, D := Finset.sum_le_sum fun γ _ => hc γ
      _ = m * n * D := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hA]
  have hn0 : (0:ℝ) < n := by linarith
  have hT : |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ m * D := by
    have he : (n:ℝ) * T.card - (3 * m + 1) / 4 * δ * n * n = n * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) := by ring
    rw [he, abs_mul, abs_of_pos hn0] at hdiff
    have h4 : (n:ℝ) * |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ n * (m * D) := by linarith
    exact le_of_mul_le_mul_left h4 hn0
  have hδn : 0 < δ * n := mul_pos hδ hn0
  have hηδ : η * (δ * n) ≤ δ * n := mul_le_of_le_one_left (le_of_lt hδn) hη
  have hmD : 0 ≤ (m:ℝ) * D := mul_nonneg (by linarith) hD
  have hmδn : 0 ≤ (m:ℝ) * (δ * n) := mul_nonneg (by linarith) (le_of_lt hδn)
  have hm1δn : 0 ≤ ((m:ℝ) - 1) * (δ * n) := mul_nonneg (by linarith) (le_of_lt hδn)
  rw [abs_le] at hT
  have hX1 : 3 * m * δ * n / 4 ≤ (T.card : ℝ) := by nlinarith
  have hη0 : 0 ≤ η := by
    by_contra hneg
    push_neg at hneg
    have h5 : η * (δ * n) < 0 := mul_neg_of_neg_of_pos hneg hδn
    linarith
  have hηX : 3 * D ≤ η * T.card := by
    have hmm : 0 ≤ D * ((m:ℝ) * m - 1) := mul_nonneg hD (by nlinarith)
    calc 3 * D ≤ 3 * m * m * D := by nlinarith
      _ = (3 * m / 4) * (4 * m * D) := by ring
      _ ≤ (3 * m / 4) * (η * (δ * n)) := mul_le_mul_of_nonneg_left hDη (by positivity)
      _ = η * (3 * m * δ * n / 4) := by ring
      _ ≤ η * T.card := mul_le_mul_of_nonneg_left hX1 hη0
  have hK : (0:ℝ) < 3 * m + 1 := by linarith
  have key : ∀ w c : ℝ, 0 ≤ w → w ≤ 4 → |c - w * δ * n / 4| ≤ D →
      |c - w / (3 * m + 1) * T.card| ≤ η * T.card := by
    intro w c hw0 hw4 hcw
    have hE : w / (3 * m + 1) * (T.card : ℝ)
        = w * δ * n / 4 + w * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) / (3 * m + 1) := by
      field_simp
      ring
    have h1 : |w * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) / (3 * m + 1)| ≤ 2 * D := by
      rw [abs_div, abs_mul, abs_of_nonneg hw0, abs_of_pos hK, div_le_iff₀ hK]
      have habs : |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ m * D := abs_le.mpr hT
      calc w * |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ 4 * (m * D) :=
            mul_le_mul hw4 habs (abs_nonneg _) (by norm_num)
        _ ≤ 2 * D * (3 * m + 1) := by nlinarith
    rw [hE]
    rw [abs_le] at hcw h1 ⊢
    constructor <;> linarith [hcw.1, hcw.2, h1.1, h1.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]; nlinarith
  · rw [hA]; nlinarith
  · intro γ
    have hcγ := hc γ
    by_cases hγ : γ ∈ A0
    · simp only [if_pos hγ] at hcγ ⊢
      have e : (4:ℝ) * δ * n / 4 = δ * n := by ring
      exact key 4 _ (by norm_num) le_rfl (by rw [e]; exact hcγ)
    · simp only [if_neg hγ] at hcγ ⊢
      have e : (3:ℝ) * δ * n / 4 = 3 / 4 * δ * n := by ring
      exact key 3 _ (by norm_num) (by norm_num) (by rw [e]; exact hcγ)
end

-- bundled from Development.AutomorphicArithmetic.ThickFrames.expectationSpec
section
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

section
variable {p : ℕ → ℝ}

private theorem ex_empty (f : Finset ℕ → ℝ) : exP p ∅ f = f ∅ := by simp [exP]

private theorem ex_insert {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (f : Finset ℕ → ℝ) :
    exP p (insert a S) f = (1 - p a) * exP p S f + p a * exP p S (fun T => f (insert a T)) := by
  unfold exP
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun T hT => ?_
    have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
    have h2 : a ∉ S \ T := fun h => ha (Finset.mem_sdiff.1 h).1
    rw [Finset.insert_sdiff_of_notMem _ haT, Finset.prod_insert h2]
    ring
  · refine Finset.sum_congr rfl fun T hT => ?_
    have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
    have e : insert a S \ insert a T = S \ T := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · tauto
      · rintro ⟨h1, h2⟩
        refine ⟨Or.inr h1, ?_⟩
        rintro (rfl | h)
        · exact ha h1
        · exact h2 h
    rw [Finset.prod_insert haT, e]
    ring

private theorem ex_congr {S : Finset ℕ} {f g : Finset ℕ → ℝ} (h : ∀ T ⊆ S, f T = g T) :
    exP p S f = exP p S g :=
  Finset.sum_congr rfl fun T hT => by rw [h T (Finset.mem_powerset.1 hT)]

private theorem ex_const (S : Finset ℕ) (c : ℝ) : exP p S (fun _ => c) = c := by
  induction S using Finset.induction_on with
  | empty => exact ex_empty _
  | insert a S ha ih => rw [ex_insert ha, ih]; ring

private theorem ex_add (S : Finset ℕ) (f g : Finset ℕ → ℝ) :
    exP p S (fun T => f T + g T) = exP p S f + exP p S g := by
  unfold exP
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun T _ => by ring

private theorem ex_mul_left (S : Finset ℕ) (c : ℝ) (f : Finset ℕ → ℝ) :
    exP p S (fun T => c * f T) = c * exP p S f := by
  unfold exP
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun T _ => by ring

private theorem ex_sum {ι : Type*} (S : Finset ℕ) (I : Finset ι) (f : ι → Finset ℕ → ℝ) :
    exP p S (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, exP p S (f i) := by
  unfold exP
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun T _ => by rw [Finset.mul_sum]

private theorem ex_mono {S : Finset ℕ} (hp : ∀ a ∈ S, 0 ≤ p a ∧ p a ≤ 1) {f g : Finset ℕ → ℝ}
    (h : ∀ T ⊆ S, f T ≤ g T) : exP p S f ≤ exP p S g := by
  refine Finset.sum_le_sum fun T hT => ?_
  have hT' := Finset.mem_powerset.1 hT
  refine mul_le_mul_of_nonneg_left (h T hT') (mul_nonneg ?_ ?_)
  · exact Finset.prod_nonneg fun a ha => (hp a (hT' ha)).1
  · exact Finset.prod_nonneg fun a ha => sub_nonneg.2 (hp a (Finset.mem_sdiff.1 ha).1).2

private theorem ex_union {A B : Finset ℕ} (hAB : Disjoint A B) (f : Finset ℕ → ℝ) :
    exP p (A ∪ B) f = exP p A (fun T => exP p B (fun U => f (T ∪ U))) := by
  induction A using Finset.induction_on generalizing f with
  | empty => rw [ex_empty]; simp
  | insert a A ha ih =>
    rw [Finset.disjoint_insert_left] at hAB
    have : a ∉ A ∪ B := by simp [ha, hAB.1]
    rw [Finset.insert_union, ex_insert this, ex_insert ha, ih hAB.2, ih hAB.2]
    simp only [Finset.insert_union]

private theorem ex_split {A S : Finset ℕ} (hA : A ⊆ S) (f g : Finset ℕ → ℝ) :
    exP p S (fun T => f (T ∩ A) * g (T \ A)) = exP p A f * exP p (S \ A) g := by
  conv_lhs => rw [← Finset.union_sdiff_of_subset hA]
  rw [ex_union Finset.disjoint_sdiff, mul_comm, ← ex_mul_left]
  refine ex_congr fun T hT => ?_
  rw [mul_comm, ← ex_mul_left]
  refine ex_congr fun U hU => ?_
  have e1 : (T ∪ U) ∩ A = T := by
    ext x
    have := @hT x
    have := @hU x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  have e2 : (T ∪ U) \ A = U := by
    ext x
    have := @hT x
    have := @hU x
    simp only [Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  rw [e1, e2]

private theorem ex_restrict {A S : Finset ℕ} (hA : A ⊆ S) (f : Finset ℕ → ℝ) :
    exP p S (fun T => f (T ∩ A)) = exP p A f := by
  have := ex_split (p := p) hA f (fun _ => 1)
  simpa [ex_const] using this

private theorem ex_prod {ι : Type*} (J : Finset ι) (A : ι → Finset ℕ) (g : ι → Finset ℕ → ℝ)
    (hd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (A i) (A j)) (S : Finset ℕ)
    (hS : ∀ j ∈ J, A j ⊆ S) :
    exP p S (fun T => ∏ j ∈ J, g j (T ∩ A j)) = ∏ j ∈ J, exP p (A j) (g j) := by
  classical
  induction J using Finset.induction_on generalizing S with
  | empty => simp [ex_const]
  | insert a J ha ih =>
    have hda : ∀ j ∈ J, Disjoint (A a) (A j) := fun j hj =>
      hd a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (fun h => ha (h ▸ hj))
    rw [Finset.prod_insert ha,
      ← ih (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
        (S \ A a) (fun j hj => Finset.subset_sdiff.2
          ⟨hS j (Finset.mem_insert_of_mem hj), (hda j hj).symm⟩),
      ← ex_split (hS a (Finset.mem_insert_self _ _))]
    refine ex_congr fun T _ => ?_
    rw [Finset.prod_insert ha]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    congr 1
    ext x
    have : x ∈ A a → x ∉ A j := fun h => Finset.disjoint_left.1 (hda j hj) h
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto

end

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.expectation_spec :
    ∀ (p : ℕ → ℝ),
      (∀ (S : Finset ℕ) (c : ℝ), exP p S (fun _ => c) = c) ∧
      (∀ (S : Finset ℕ) (f g : Finset ℕ → ℝ), exP p S (fun T => f T + g T) = exP p S f + exP p S g) ∧
      (∀ (S : Finset ℕ) (I : Finset ℕ) (f : ℕ → Finset ℕ → ℝ), exP p S (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, exP p S (f i)) ∧
      (∀ (S : Finset ℕ) (f g : Finset ℕ → ℝ), (∀ a ∈ S, 0 ≤ p a ∧ p a ≤ 1) → (∀ T ⊆ S, f T ≤ g T) → exP p S f ≤ exP p S g) ∧
      (∀ (a : ℕ) (S : Finset ℕ) (f : Finset ℕ → ℝ), a ∉ S →
        exP p (insert a S) f = (1 - p a) * exP p S f + p a * exP p S (fun T => f (insert a T))) ∧
      (∀ (A S : Finset ℕ) (f : Finset ℕ → ℝ), A ⊆ S → exP p S (fun T => f (T ∩ A)) = exP p A f) ∧
      (∀ (J : Finset ℕ) (A : ℕ → Finset ℕ) (g : ℕ → Finset ℕ → ℝ) (S : Finset ℕ),
        (∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (A i) (A j)) → (∀ j ∈ J, A j ⊆ S) →
        exP p S (fun T => ∏ j ∈ J, g j (T ∩ A j)) = ∏ j ∈ J, exP p (A j) (g j)) := by
  intro p
  exact ⟨ex_const, ex_add, fun S I f => ex_sum S I f, fun _ _ _ hp h => ex_mono hp h,
    fun _ _ f ha => ex_insert ha f, fun _ _ f hA => ex_restrict hA f,
    fun J A g S hd hS => ex_prod J A g hd S hS⟩
end

-- bundled from Development.AutomorphicArithmetic.ThickFrames.orbitSum
section
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

namespace UpperTheory.BernoulliSumsFrobeniusOrbits

private lemma fibre_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : α → ℝ) (f : β → α) (hf : Function.Injective f) (S : Finset β) :
    ∑ T : Finset α, (if univ.filter (fun i => f i ∈ T) = S then pw p T else 0) =
      pw (fun i => p (f i)) S := by
  classical
  set g : α → ℝ := fun a => if a ∈ (univ \ S).image f then 0 else p a with hg
  set h : α → ℝ := fun a => if a ∈ S.image f then 0 else 1 - p a with hh
  have h1 := Finset.prod_add g h (univ : Finset α)
  rw [powerset_univ] at h1
  have h2 : ∏ a, (g a + h a) = pw (fun i => p (f i)) S := by
    rw [← Finset.prod_subset (subset_univ ((univ : Finset β).image f)), prod_image hf.injOn]
    · rw [pw, ← prod_sdiff (subset_univ S), mul_comm]
      congr 1
      · refine prod_congr rfl fun i hi => ?_
        simp [hg, hh, hf.eq_iff, hi]
      · refine prod_congr rfl fun i hi => ?_
        have hi' : i ∉ S := (mem_sdiff.mp hi).2
        simp [hg, hh, hf.eq_iff, hi']
    · intro a _ ha
      have ha1 : a ∉ (univ \ S).image f := fun h' => ha (image_subset_image (subset_univ _) h')
      have ha2 : a ∉ S.image f := fun h' => ha (image_subset_image (subset_univ _) h')
      simp only [hg, hh, if_neg ha1, if_neg ha2]
      ring
  rw [← h2, h1]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with hT
  · rw [pw]
    congr 1
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ (univ \ S).image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        exact (mem_sdiff.mp hi).2 (hT ▸ mem_filter.mpr ⟨mem_univ _, ha⟩)
      simp only [hg, if_neg this]
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ S.image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        rw [← hT] at hi
        exact (mem_sdiff.mp ha).2 (mem_filter.mp hi).2
      simp only [hh, if_neg this]
  · have : ∃ i, ¬ (f i ∈ T ↔ i ∈ S) := by
      by_contra hc
      push Not at hc
      exact hT (by ext i; simp [hc i])
    obtain ⟨i, hi⟩ := this
    by_cases hiS : i ∈ S
    · have hT' : f i ∉ T := fun h' => hi ⟨fun _ => hiS, fun _ => h'⟩
      rw [prod_eq_zero (s := univ \ T) (i := f i) (by simp [hT']), mul_zero]
      simp only [hh, if_pos (mem_image_of_mem f hiS)]
    · have hT' : f i ∈ T := by
        by_contra h'
        exact hi ⟨fun h'' => absurd h'' h', fun h'' => absurd h'' hiS⟩
      rw [prod_eq_zero (s := T) (i := f i) hT', zero_mul]
      simp only [hg, if_pos (mem_image_of_mem f (mem_sdiff.mpr ⟨mem_univ i, hiS⟩))]

private lemma marginal {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : α → ℝ) (f : β → α) (hf : Function.Injective f) (F : Finset β → ℝ) :
    ∑ T : Finset α, pw p T * F (univ.filter (fun i => f i ∈ T)) =
      ∑ S : Finset β, pw (fun i => p (f i)) S * F S := by
  calc ∑ T : Finset α, pw p T * F (univ.filter (fun i => f i ∈ T))
      = ∑ T : Finset α, ∑ S : Finset β,
          (if univ.filter (fun i => f i ∈ T) = S then pw p T else 0) * F S := by
        refine sum_congr rfl fun T _ => ?_
        simp only [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp
    _ = _ := by
        rw [sum_comm]
        refine sum_congr rfl fun S _ => ?_
        rw [← sum_mul, fibre_sum p f hf S]

private lemma fin_sum_eq (n : ℕ) (q : ℕ → ℝ) (F : Finset ℕ → ℝ) :
    (∑ S : Finset (Fin n), pw (fun i : Fin n => q i) S * F (S.map Fin.valEmbedding)) =
      exP q (range n) F := by
  unfold exP
  refine Finset.sum_bij (fun S _ => S.map Fin.valEmbedding) ?_ ?_ ?_ ?_
  · intro S _
    rw [mem_powerset]
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    simp
  · intro S _ S' _ h
    exact Finset.map_injective _ h
  · intro T hT
    refine ⟨univ.filter (fun i : Fin n => (i : ℕ) ∈ T), mem_univ _, ?_⟩
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      exact ⟨⟨x, mem_range.mp (mem_powerset.mp hT hx)⟩, hx, rfl⟩
  · intro S _
    have e : range n \ S.map Fin.valEmbedding = (univ \ S).map Fin.valEmbedding := by
      ext x
      simp only [mem_sdiff, mem_range, mem_map, mem_univ, true_and, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨hx, hx'⟩
        exact ⟨⟨x, hx⟩, fun h => hx' ⟨_, h, rfl⟩, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        refine ⟨i.2, ?_⟩
        rintro ⟨j, hj, hji⟩
        exact hi (Fin.ext hji ▸ hj)
    rw [e, prod_map, prod_map]
    rfl

private lemma bernoulliExpectation_mem_and (q : ℕ → ℝ) {S : Finset ℕ} {i₀ : ℕ} (hm : i₀ ∈ S) (A : Finset ℕ → Prop) :
    exP q S (fun T => ind (i₀ ∈ T ∧ A T)) =
      q i₀ * exP q (S.erase i₀) (fun U => ind (A (insert i₀ U))) := by
  unfold exP
  conv_lhs => rw [← Finset.insert_erase hm]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase _ _), Finset.sum_eq_zero, zero_add, mul_sum]
  · refine Finset.sum_congr rfl fun T hT => ?_
    have hT' : i₀ ∉ T := fun h => Finset.notMem_erase _ _ (Finset.mem_powerset.1 hT h)
    have e : insert i₀ (S.erase i₀) \ insert i₀ T = S.erase i₀ \ T := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_erase]
      tauto
    rw [e, prod_insert hT']
    simp only [mem_insert_self, true_and]
    ring
  · intro T hT
    have hT' : i₀ ∉ T := fun h => Finset.notMem_erase _ _ (Finset.mem_powerset.1 hT h)
    simp [ind, hT']

end UpperTheory.BernoulliSumsFrobeniusOrbits

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_sum :
    ∀ (α : Type) [Fintype α] [DecidableEq α] [AddCommGroup α] (p : α → ℝ) (b h t : α), (∃ i : ℕ, b + i • h = t) →
      ∀ A : Finset ℕ → Prop, ∃ i₀ < addOrderOf h, b + i₀ • h = t ∧
        ∑ T : Finset α, pw p T * ind (t ∈ T ∧ A ((univ.filter (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)).map Fin.valEmbedding)) =
          p t * exP (fun i => p (b + i • h)) ((range (addOrderOf h)).erase i₀) (fun U => ind (A (insert i₀ U))) := by
  intro α _ _ _ p b h t ht A
  obtain ⟨i, hi⟩ := ht
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  have hlt : i % addOrderOf h < addOrderOf h := Nat.mod_lt _ hpos
  have ht : b + (i % addOrderOf h) • h = t := by rw [mod_addOrderOf_nsmul, hi]
  refine ⟨i % addOrderOf h, hlt, ht, ?_⟩
  have hinj : Function.Injective (fun j : Fin (addOrderOf h) => b + (j : ℕ) • h) := by
    intro j k hjk
    have := add_left_cancel hjk
    exact Fin.ext (nsmul_injOn_Iio_addOrderOf j.2 k.2 this)
  have h1 := bernoulliExpectation_mem_and (fun i => p (b + i • h)) (mem_range.2 hlt) A
  rw [ht] at h1
  rw [← h1, ← fin_sum_eq, ← marginal p _ hinj
    (fun S => ind (i % addOrderOf h ∈ S.map Fin.valEmbedding ∧ A (S.map Fin.valEmbedding)))]
  refine sum_congr rfl fun T _ => ?_
  have : t ∈ T ↔ i % addOrderOf h ∈ (univ.filter
      (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)).map Fin.valEmbedding := by
    rw [show i % addOrderOf h = Fin.valEmbedding (⟨_, hlt⟩ : Fin (addOrderOf h)) from rfl,
      Finset.mem_map']
    simp [hi]
  simp only [this]
end

