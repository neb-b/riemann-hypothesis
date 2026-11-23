module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsolateAbstract
section
namespace GlobalTheory

theorem isolate_abstract : ∀ (X : Type) [AddCommGroup X] (Γ G : AddSubgroup X) (V : Type) [AddCommGroup V] [Module ℂ V] (T : X → V →ₗ[ℂ] V) (W : Set V) (β : X → X → ℂ) (a : X → ℂ) (χ : X → X → ℂ), Γ ≤ G → (∀ v, T 0 v = v) → (∀ x y v, T x (T y v) = β x y • T (x + y) v) → (∀ x y, β x y ≠ 0) → (∀ γ ∈ Γ, a γ ≠ 0 ∧ ∀ v ∈ W, T γ v = a γ • v) → (∀ γ ∈ Γ, ∀ x v, T γ (T x v) = χ x γ • T x (T γ v)) → (∀ x, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, χ (x + γ') γ = χ x γ) → (∀ x ∈ G, ∀ y ∈ G, x - y ∉ Γ → ∃ γ ∈ Γ, χ x γ ≠ χ y γ) → ∀ (J : Finset X) (c : X → ℂ), (∀ x ∈ J, x ∈ G) → (∀ v ∈ W, ∑ x ∈ J, c x • T x v = 0) ∨ ∃ κ : X →₀ ℂ, (∀ y ∈ κ.support, y ∈ G) ∧ ∀ v ∈ W, ∑ y ∈ κ.support, κ y • T y (∑ x ∈ J, c x • T x v) = v := by
  intro X _ Γ G V _ _ T W β a χ hΓG hT0 hTT hβ ha hχ hχc hsep J c hJ
  classical
  obtain ⟨A, hA⟩ : ∃ A : Submodule ℂ (V →ₗ[ℂ] V), A = Submodule.span ℂ (T '' (G : Set X)) := ⟨_, rfl⟩
  have hTA : ∀ y ∈ G, T y ∈ A := fun y hy => hA ▸ Submodule.subset_span ⟨y, hy, rfl⟩
  have hmulT : ∀ y ∈ G, ∀ g ∈ A, T y * g ∈ A := by
    intro y hy g hg
    rw [hA] at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨z, hz, rfl⟩ := hg
      have e : T y * T z = β y z • T (y + z) := by ext v; simp [hTT]
      rw [e]; exact A.smul_mem _ (hTA _ (G.add_mem hy hz))
    | zero => simp
    | add f g _ _ hf hg => rw [mul_add]; exact A.add_mem hf hg
    | smul r f _ hf => rw [mul_smul_comm]; exact A.smul_mem r hf
  have hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A := by
    intro f hf g hg
    rw [hA] at hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨y, hy, rfl⟩ := hf; exact hmulT y hy g hg
    | zero => simp
    | add f f' _ _ h h' => rw [add_mul]; exact A.add_mem h h'
    | smul r f _ h => rw [smul_mul_assoc]; exact A.smul_mem r h
  have hone : (1 : V →ₗ[ℂ] V) ∈ A := by
    have e : (1 : V →ₗ[ℂ] V) = T 0 := by ext v; simp [hT0]
    rw [e]; exact hTA 0 G.zero_mem
  have hκ : ∀ L ∈ A, ∃ κ : X →₀ ℂ, (∀ y ∈ κ.support, y ∈ G) ∧ ∀ u, ∑ y ∈ κ.support, κ y • T y u = L u := by
    intro L hL
    rw [hA, Finsupp.mem_span_image_iff_linearCombination] at hL
    obtain ⟨l, hl, rfl⟩ := hL
    refine ⟨l, fun y hy => (Finsupp.mem_supported _ _).1 hl hy, fun u => ?_⟩
    simp [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  have hshift : ∀ x0 x, x - x0 ∈ Γ → ∀ v ∈ W, T x v = ((β x0 (x - x0))⁻¹ * a (x - x0)) • T x0 v := by
    intro x0 x h v hv
    have h1 := hTT x0 (x - x0) v
    have e : x0 + (x - x0) = x := by abel
    rw [(ha _ h).2 v hv, map_smul, e] at h1
    rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ (hβ _ _), one_smul]
  have hcls : ∀ x0 (c : X → ℂ), ∀ v ∈ W, ∑ x ∈ J, (if x - x0 ∈ Γ then c x else 0) • T x v
      = (∑ x ∈ J, if x - x0 ∈ Γ then c x * ((β x0 (x - x0))⁻¹ * a (x - x0)) else 0) • T x0 v := by
    intro x0 c v hv
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [mul_smul, ← hshift x0 x h v hv]
    · simp
  have hQ : ∀ γ ∈ Γ, ∀ k : ℂ, ∀ c : X → ℂ, ∀ v ∈ W,
      ((a γ)⁻¹ • T γ - k • (1 : V →ₗ[ℂ] V)) (∑ x ∈ J, c x • T x v) = ∑ x ∈ J, (c x * (χ x γ - k)) • T x v := by
    intro γ hγ k c v hv
    have hb : ∀ x, T γ (T x v) = (χ x γ * a γ) • T x v := by
      intro x; rw [hχ γ hγ x v, (ha γ hγ).2 v hv, map_smul, smul_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sum, map_smul, hb,
      Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [smul_smul, ← sub_smul]
    congr 1
    have := (ha γ hγ).1
    field_simp
  have hQA : ∀ γ ∈ Γ, ∀ k : ℂ, ((a γ)⁻¹ • T γ - k • (1 : V →ₗ[ℂ] V)) ∈ A := fun γ hγ k =>
    A.sub_mem (A.smul_mem _ (hTA γ (hΓG hγ))) (A.smul_mem _ hone)
  have hproj : ∀ x0 ∈ G, ∀ n : ℕ, ∀ c : X → ℂ, (J.filter (fun x => c x ≠ 0 ∧ x - x0 ∉ Γ)).card = n →
      ∃ L ∈ A, ∃ s : ℂ, s ≠ 0 ∧ ∀ v ∈ W,
        L (∑ x ∈ J, c x • T x v) = s • ∑ x ∈ J, (if x - x0 ∈ Γ then c x else 0) • T x v := by
    intro x0 hx0 n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro c hn
    by_cases hS : ∃ x1 ∈ J, c x1 ≠ 0 ∧ x1 - x0 ∉ Γ
    · obtain ⟨x1, hx1J, hcx1, hx1⟩ := hS
      obtain ⟨γ, hγ, hne⟩ := hsep x1 (hJ x1 hx1J) x0 hx0 hx1
      obtain ⟨c', hc'⟩ : ∃ c' : X → ℂ, c' = fun x => c x * (χ x γ - χ x1 γ) := ⟨_, rfl⟩
      have hsub : J.filter (fun x => c' x ≠ 0 ∧ x - x0 ∉ Γ) ⊂ J.filter (fun x => c x ≠ 0 ∧ x - x0 ∉ Γ) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨x1, by simp [hx1J, hcx1, hx1], ?_⟩
          simp [hc']
        · intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, fun h => hx.2.1 (by simp [hc', h]), hx.2.2⟩
      obtain ⟨L', hL', s', hs', hL'eq⟩ := ih _ (hn ▸ Finset.card_lt_card hsub) c' rfl
      refine ⟨L' * ((a γ)⁻¹ • T γ - χ x1 γ • (1 : V →ₗ[ℂ] V)), hmul _ hL' _ (hQA γ hγ _),
        s' * (χ x0 γ - χ x1 γ), mul_ne_zero hs' (sub_ne_zero.2 (Ne.symm hne)), fun v hv => ?_⟩
      rw [Module.End.mul_apply, hQ γ hγ _ c v hv,
        show (∑ x ∈ J, (c x * (χ x γ - χ x1 γ)) • T x v) = ∑ x ∈ J, c' x • T x v by rw [hc'],
        hL'eq v hv, mul_smul]
      congr 1
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with h
      · have hχx : χ x γ = χ x0 γ := by simpa using hχc x0 γ hγ (x - x0) h
        simp only [hc', smul_smul, hχx, mul_comm]
      · simp
    · push_neg at hS
      refine ⟨1, hone, 1, one_ne_zero, fun v hv => ?_⟩
      rw [Module.End.one_apply, one_smul]
      refine Finset.sum_congr rfl fun x hx => ?_
      split_ifs with h
      · rfl
      · by_cases hc : c x = 0
        · simp [hc]
        · exact absurd (hS x hx hc) h
  have main : ∀ n : ℕ, ∀ c : X → ℂ, (J.filter (fun x => c x ≠ 0)).card = n →
      (∀ v ∈ W, ∑ x ∈ J, c x • T x v = 0) ∨ ∃ L ∈ A, ∀ v ∈ W, L (∑ x ∈ J, c x • T x v) = v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro c hn
    by_cases hS : ∃ x0 ∈ J, c x0 ≠ 0
    · obtain ⟨x0, hx0J, hcx0⟩ := hS
      have hx0 := hJ x0 hx0J
      obtain ⟨d, hd⟩ : ∃ d : ℂ, d = ∑ x ∈ J, if x - x0 ∈ Γ then c x * ((β x0 (x - x0))⁻¹ * a (x - x0)) else 0 :=
        ⟨_, rfl⟩
      by_cases hd0 : d = 0
      · obtain ⟨c'', hc''⟩ : ∃ c'' : X → ℂ, c'' = fun x => if x - x0 ∈ Γ then 0 else c x := ⟨_, rfl⟩
        have hsub : J.filter (fun x => c'' x ≠ 0) ⊂ J.filter (fun x => c x ≠ 0) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨x0, by simp [hx0J, hcx0], ?_⟩
            simp [hc'']
          · intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            refine ⟨hx.1, fun h => hx.2 ?_⟩
            simp [hc'', h]
        have heq : ∀ v ∈ W, ∑ x ∈ J, c x • T x v = ∑ x ∈ J, c'' x • T x v := by
          intro v hv
          have h1 := hcls x0 c v hv
          rw [← hd, hd0, zero_smul] at h1
          calc ∑ x ∈ J, c x • T x v
              = ∑ x ∈ J, ((if x - x0 ∈ Γ then c x else 0) • T x v + c'' x • T x v) :=
                Finset.sum_congr rfl fun x _ => by simp only [hc'']; split_ifs <;> simp
            _ = ∑ x ∈ J, c'' x • T x v := by rw [Finset.sum_add_distrib, h1, zero_add]
        rcases ih _ (hn ▸ Finset.card_lt_card hsub) c'' rfl with h | ⟨L, hL, hLeq⟩
        · exact Or.inl fun v hv => by rw [heq v hv]; exact h v hv
        · exact Or.inr ⟨L, hL, fun v hv => by rw [heq v hv]; exact hLeq v hv⟩
      · obtain ⟨L, hL, s, hs, hLeq⟩ := hproj x0 hx0 _ c rfl
        refine Or.inr ⟨(((s * d) * β (-x0) x0)⁻¹ • T (-x0)) * L,
          hmul _ (A.smul_mem _ (hTA _ (G.neg_mem hx0))) _ hL, fun v hv => ?_⟩
        rw [Module.End.mul_apply, LinearMap.smul_apply, hLeq v hv, hcls x0 c v hv, ← hd, map_smul, map_smul,
          hTT, neg_add_cancel, hT0, smul_smul, smul_smul, smul_smul]
        have hβ' := hβ (-x0) x0
        have e : ((s * d) * β (-x0) x0)⁻¹ * s * d * β (-x0) x0 = 1 := by
          field_simp
        rw [e, one_smul]
    · push_neg at hS
      exact Or.inl fun v _ => Finset.sum_eq_zero fun x hx => by simp [hS x hx]
  rcases main _ c rfl with h | ⟨L, hL, hLeq⟩
  · exact Or.inl h
  · obtain ⟨κ, hκG, hκeq⟩ := hκ L hL
    exact Or.inr ⟨κ, hκG, fun v hv => by rw [hκeq, hLeq v hv]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedGainRapidDecay
section
open Finset

namespace GlobalTheory.IterGain

noncomputable def words {ι : Type} [DecidableEq ι] (B : Finset ι) : ℕ → Finset (List ι)
  | 0 => {[]}
  | k + 1 => insert [] ((words B k ×ˢ B).image (fun p => p.1 ++ [p.2]))

theorem nil_mem {ι : Type} [DecidableEq ι] (B : Finset ι) (k : ℕ) : [] ∈ words B k := by
  cases k <;> simp [words]

theorem append_mem {ι : Type} [DecidableEq ι] {B : Finset ι} {k : ℕ} {l : List ι} {i : ι}
    (hl : l ∈ words B k) (hi : i ∈ B) : l ++ [i] ∈ words B (k + 1) := by
  simp only [words, mem_insert, mem_image, mem_product, Prod.exists]
  exact Or.inr ⟨l, i, ⟨hl, hi⟩, rfl⟩

theorem mem_letters {ι : Type} [DecidableEq ι] (B : Finset ι) :
    ∀ (k : ℕ), ∀ l ∈ words B k, ∀ i ∈ l, i ∈ B := by
  intro k
  induction k with
  | zero => intro l hl i hi; simp [words] at hl; subst hl; simp at hi
  | succ k ih =>
    intro l hl i hi
    simp only [words, mem_insert, mem_image, mem_product, Prod.exists] at hl
    rcases hl with rfl | ⟨l', j, ⟨hl', hj⟩, rfl⟩
    · simp at hi
    · rcases List.mem_append.1 hi with h | h
      · exact ih l' hl' i h
      · simp at h; subst h; exact hj

theorem root_le {x y : ℝ} {m : ℕ} (hm : m ≠ 0) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ m ≤ y ^ m) :
    x ≤ y := (pow_le_pow_iff_left₀ hx hy hm).1 h

theorem step {G ι : Type} [DecidableEq ι] (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ))
    (Dr : ι → (G → ℂ) → G → ℂ) (m : ℕ) (C δ₀ K : ℝ) (Q : G → ℝ) (A : ℕ)
    (hm : m ≠ 0) (hδ₀ : 0 < δ₀) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKm : K ^ m = C)
    (hq : ∀ g, 1 ≤ q g) (hQ1 : ∀ g, 1 ≤ Q g) (hQm : ∀ g, Q g ^ m = q g)
    (hcl : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒)
    (hgain : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ m ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i))
    (k : ℕ) : ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ words B k, 0 ≤ c l) →
      (∀ l ∈ words B k, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) →
      ∀ g, ‖ψ g‖ * Q g ^ k ≤ Ck * q g ^ A * ∑ l ∈ words B k, c l := by
  induction k with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro ψ _ c _ hc g
    have h := hc [] (nil_mem B 0) g
    simp only [List.foldr_nil] at h
    simp [words]
    linarith
  | succ k ih =>
    obtain ⟨Ck, hCk0, hCk⟩ := ih
    have hK0 : 0 ≤ K := by linarith
    have hC0 : 0 ≤ C := by linarith
    have hQ0 : ∀ g, 0 ≤ Q g := fun g => by linarith [hQ1 g]
    have hq0 : ∀ g, 0 ≤ q g := fun g => by linarith [hq g]
    set M := K / δ₀ with hM
    have hM0 : 0 ≤ M := div_nonneg hK0 hδ₀.le
    set X1 := M ^ (k + 1)
    set X2 := C * K ^ (k + 1) * Ck * C ^ A * ((B.card : ℝ) * ((words B k).card : ℝ))
    have hX1 : 0 ≤ X1 := pow_nonneg hM0 _
    have hX2 : 0 ≤ X2 := by positivity
    refine ⟨X1 + X2, add_nonneg hX1 hX2, ?_⟩
    intro ψ hψ c hc0 hc g
    set T := ∑ l ∈ words B (k + 1), c l with hT
    have hT0 : 0 ≤ T := sum_nonneg hc0
    have hqA : 0 ≤ q g ^ A := pow_nonneg (hq0 g) _
    obtain ⟨δ, hδ, _, hδq, hcase⟩ := hgain g
    have hδQ : δ * Q g ≤ K := by
      apply root_le hm (mul_nonneg hδ.le (hQ0 g)) hK0
      rw [mul_pow, hQm, hKm]; linarith [mul_comm (q g) (δ ^ m)]
    have hQgw : ∀ w, q g ≤ C * q w → Q g ≤ K * Q w := by
      intro w hw
      apply root_le hm (hQ0 g) (mul_nonneg hK0 (hQ0 w))
      rw [mul_pow, hQm, hKm, hQm]; exact hw
    suffices h : ‖ψ g‖ * Q g ^ (k + 1) ≤ X1 * q g ^ A * T ∨
        ‖ψ g‖ * Q g ^ (k + 1) ≤ X2 * q g ^ A * T by
      have e1 : 0 ≤ X1 * q g ^ A * T := by positivity
      have e2 : 0 ≤ X2 * q g ^ A * T := mul_nonneg (mul_nonneg hX2 hqA) hT0
      rcases h with h | h <;> nlinarith
    rcases hcase with hδ0 | ⟨Ω, hΩ, hbound⟩
    · left
      have hQM : Q g ≤ M := by
        rw [hM, le_div_iff₀ hδ₀]; nlinarith [hQ0 g]
      have h0 : ‖ψ g‖ ≤ c [] * q g ^ A := by simpa using hc [] (nil_mem B _) g
      have hcT : c [] ≤ T := single_le_sum (f := c) (fun l hl => hc0 l hl) (nil_mem B _)
      have hQk : Q g ^ (k + 1) ≤ X1 := pow_le_pow_left₀ (hQ0 g) hQM _
      calc ‖ψ g‖ * Q g ^ (k + 1) ≤ (c [] * q g ^ A) * X1 :=
            mul_le_mul h0 hQk (pow_nonneg (hQ0 g) _) (by nlinarith [norm_nonneg (ψ g)])
        _ ≤ (T * q g ^ A) * X1 := by gcongr
        _ = X1 * q g ^ A * T := by ring
    · right
      set S : ι → ℝ := fun i => ∑ l ∈ words B k, c (l ++ [i]) with hS
      have hS0 : ∀ i ∈ B, 0 ≤ S i := fun i hi =>
        sum_nonneg (fun l hl => hc0 _ (append_mem hl hi))
      have hQgk : 0 < Q g ^ k := pow_pos (by linarith [hQ1 g]) _
      set P := K ^ k * Ck * C ^ A * q g ^ A with hP
      have hP0 : 0 ≤ P := by positivity
      set ci : ι → ℝ := fun i => P * S i / Q g ^ k with hci
      have hDr : ∀ i ∈ B, 0 ≤ ci i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ ci i := by
        intro i hi
        refine ⟨div_nonneg (mul_nonneg hP0 (hS0 i hi)) hQgk.le, ?_⟩
        intro w hw
        have hb := hCk (Dr i ψ) (hcl ψ hψ i hi) (fun l => c (l ++ [i]))
          (fun l hl => hc0 _ (append_mem hl hi))
          (fun l hl g' => by
            have := hc (l ++ [i]) (append_mem hl hi) g'
            simpa [List.foldr_append] using this) w
        have h1 : Q g ^ k ≤ K ^ k * Q w ^ k := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (hQ0 g) (hQgw w (hΩ w hw).2) k
        have h2 : q w ^ A ≤ C ^ A * q g ^ A := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (hq0 w) (hΩ w hw).1 A
        rw [hci, le_div_iff₀ hQgk]
        calc ‖Dr i ψ w‖ * Q g ^ k ≤ ‖Dr i ψ w‖ * (K ^ k * Q w ^ k) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = K ^ k * (‖Dr i ψ w‖ * Q w ^ k) := by ring
          _ ≤ K ^ k * (Ck * q w ^ A * S i) :=
              mul_le_mul_of_nonneg_left hb (pow_nonneg hK0 _)
          _ ≤ K ^ k * (Ck * (C ^ A * q g ^ A) * S i) := by
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK0 _)
              apply mul_le_mul_of_nonneg_right _ (hS0 i hi)
              exact mul_le_mul_of_nonneg_left h2 hCk0
          _ = P * S i := by rw [hP]; ring
      have hmain := hbound ψ hψ ci hDr
      have hsum : ∑ i ∈ B, ci i = P * (∑ i ∈ B, S i) / Q g ^ k := by
        rw [hci]; simp only; rw [← Finset.sum_div, ← Finset.mul_sum]
      have hSsum : ∑ i ∈ B, S i ≤ (B.card : ℝ) * ((words B k).card : ℝ) * T := by
        calc ∑ i ∈ B, S i ≤ ∑ i ∈ B, ∑ l ∈ words B k, T :=
              sum_le_sum (fun i hi => sum_le_sum (fun l hl =>
                single_le_sum (f := c) (fun l hl => hc0 l hl) (append_mem hl hi)))
          _ = (B.card : ℝ) * ((words B k).card : ℝ) * T := by
              simp [sum_const, nsmul_eq_mul]; ring
      have hSum0 : 0 ≤ ∑ i ∈ B, S i := sum_nonneg hS0
      calc ‖ψ g‖ * Q g ^ (k + 1) ≤ (C * δ * ∑ i ∈ B, ci i) * Q g ^ (k + 1) :=
            mul_le_mul_of_nonneg_right hmain (pow_nonneg (hQ0 g) _)
        _ = C * (δ * Q g) * (P * ∑ i ∈ B, S i) := by
            rw [hsum]; field_simp; ring
        _ ≤ C * K * (P * ((B.card : ℝ) * ((words B k).card : ℝ) * T)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hδQ hC0)
              (mul_le_mul_of_nonneg_left hSsum hP0) (mul_nonneg hP0 hSum0) (mul_nonneg hC0 hK0)
        _ = X2 * q g ^ A * T := by rw [hP]; ring

end GlobalTheory.IterGain

namespace GlobalTheory


open GlobalTheory.IterGain in
theorem iterated_gain_rapid_decay : ∀ (G ι : Type) (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ))
    (Dr : ι → (G → ℂ) → G → ℂ) (b : ℕ) (C δ₀ : ℝ), 0 < δ₀ → (∀ g, 1 ≤ q g) →
    (∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒) →
    (∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ b ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i)) →
    ∀ A N : ℕ, ∃ (L : Finset (List ι)) (C' : ℝ), (∀ l ∈ L, ∀ i ∈ l, i ∈ B) ∧
      ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ L, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) →
        ∀ g, ‖ψ g‖ * q g ^ N ≤ C' * ∑ l ∈ L, c l := by
  intro G ι B q 𝓒 Dr b C δ₀ hδ₀ hq hcl hgain A N
  classical
  set m := b + 1 with hmdef
  have hm : m ≠ 0 := Nat.succ_ne_zero b
  set C1 := max C 1 with hC1
  have hC1 : 1 ≤ C1 := le_max_right _ _
  have hCC1 : C ≤ C1 := le_max_left _ _
  have hq0 : ∀ g, 0 ≤ q g := fun g => by linarith [hq g]
  have hgain' : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ m ≤ C1 ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C1 * q g ∧ q g ≤ C1 * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C1 * δ * ∑ i ∈ B, c i) := by
    intro g
    obtain ⟨δ, hδ, hδ1, hqδ, hcase⟩ := hgain g
    refine ⟨δ, hδ, hδ1, ?_, ?_⟩
    · have h1 : q g * δ ^ m ≤ q g * δ ^ b := by
        rw [hmdef, pow_succ, ← mul_assoc]
        exact mul_le_of_le_one_right (mul_nonneg (hq0 g) (pow_nonneg hδ.le _)) hδ1
      linarith
    · rcases hcase with h | ⟨Ω, hΩ, hbd⟩
      · exact Or.inl h
      · refine Or.inr ⟨Ω, fun w hw => ⟨?_, ?_⟩, ?_⟩
        · exact (hΩ w hw).1.trans (mul_le_mul_of_nonneg_right hCC1 (hq0 g))
        · exact (hΩ w hw).2.trans (mul_le_mul_of_nonneg_right hCC1 (hq0 w))
        · intro ψ hψ c hc
          have hs : 0 ≤ ∑ i ∈ B, c i := sum_nonneg (fun i hi => (hc i hi).1)
          exact (hbd ψ hψ c hc).trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC1 hδ.le) hs)
  set K : ℝ := C1 ^ ((m : ℝ)⁻¹) with hK
  set Q : G → ℝ := fun g => q g ^ ((m : ℝ)⁻¹) with hQ
  have hKm : K ^ m = C1 := Real.rpow_inv_natCast_pow (by linarith) hm
  have hK1 : 1 ≤ K := Real.one_le_rpow hC1 (by positivity)
  have hQm : ∀ g, Q g ^ m = q g := fun g => Real.rpow_inv_natCast_pow (hq0 g) hm
  have hQ1 : ∀ g, 1 ≤ Q g := fun g => Real.one_le_rpow (hq g) (by positivity)
  obtain ⟨Ck, _, hCk⟩ := step B q 𝓒 Dr m C1 δ₀ K Q A hm hδ₀ hC1 hK1 hKm hq hQ1 hQm hcl hgain'
    (m * (A + N))
  refine ⟨words B (m * (A + N)), Ck, mem_letters B _, ?_⟩
  intro ψ hψ c hc g
  have hqA : 0 < q g ^ A := pow_pos (by linarith [hq g]) _
  have hc0 : ∀ l ∈ words B (m * (A + N)), 0 ≤ c l := by
    intro l hl
    by_contra h
    push_neg at h
    have h1 := hc l hl g
    have h2 : c l * q g ^ A < 0 := mul_neg_of_neg_of_pos h hqA
    linarith [norm_nonneg (List.foldr Dr ψ l g)]
  have h := hCk ψ hψ c hc0 hc g
  rw [pow_mul, hQm, pow_add] at h
  have h' : q g ^ A * (‖ψ g‖ * q g ^ N) ≤ q g ^ A * (Ck * ∑ l ∈ words B (m * (A + N)), c l) := by
    linarith
  exact le_of_mul_le_mul_left h' hqA

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixExpSmulMulEqMulExpSmulOfIntertwine
section
open Matrix

namespace GlobalTheory

theorem matrix_pow_mul_eq_mul_pow_of_intertwine {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) (n : ℕ) :
    X ^ n * ε = ε * β ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem matrix_hasSum_exp {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) (NormedSpace.exp X) := by
  let _ : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X

theorem matrix_exp_mul_eq_mul_exp_of_intertwine {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) :
    NormedSpace.exp X * ε = ε * NormedSpace.exp β := by
  let g : Matrix (Fin m) (Fin m) ℂ →+ Matrix (Fin m) (Fin r) ℂ :=
    AddMonoidHom.mk' (fun A => A * ε) (fun A B => Matrix.add_mul A B ε)
  have hg : Continuous g := Continuous.matrix_mul continuous_id continuous_const
  let g' : Matrix (Fin r) (Fin r) ℂ →+ Matrix (Fin m) (Fin r) ℂ :=
    AddMonoidHom.mk' (fun A => ε * A) (fun A B => Matrix.mul_add ε A B)
  have hg' : Continuous g' := Continuous.matrix_mul continuous_const continuous_id
  have hL := (matrix_hasSum_exp X).map g hg
  have hR := (matrix_hasSum_exp β).map g' hg'
  have key : (g ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) =
      (g' ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • β ^ n) := by
    funext n
    simp only [Function.comp, g, g', AddMonoidHom.mk'_apply, Matrix.smul_mul, Matrix.mul_smul,
      matrix_pow_mul_eq_mul_pow_of_intertwine X ε β h n]
  rw [key] at hL
  exact hL.unique hR

theorem matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine :
    ∀ (m r : ℕ) (X : Matrix (Fin m) (Fin m) ℂ) (ε : Matrix (Fin m) (Fin r) ℂ)
      (β : Matrix (Fin r) (Fin r) ℂ), X * ε = ε * β →
      ∀ s : ℝ, NormedSpace.exp (s • X) * ε = ε * NormedSpace.exp (s • β) := by
  intro m r X ε β h s
  apply matrix_exp_mul_eq_mul_exp_of_intertwine
  rw [Matrix.smul_mul, Matrix.mul_smul, h]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormEigenvalueLeOne
section
namespace GlobalTheory.EigenvalueNormBound

theorem pow_mulVec_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (μ : ℂ)
    (h : Matrix.mulVec M v = μ • v) (k : ℕ) : Matrix.mulVec (M ^ k) v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

theorem norm_eigenvalue_le_one : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (C : ℝ),
    (∀ (k : ℕ) (i j : Fin n), ‖(M ^ k) i j‖ ≤ C) → ∀ (v : Fin n → ℂ), v ≠ (0 : Fin n → ℂ) →
    ∀ (μ : ℂ), Matrix.mulVec M v = μ • v → ‖μ‖ ≤ (1 : ℝ) := by
  intro n M C hC v hv μ hμ
  by_contra hlt
  rw [not_le] at hlt

  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    exact hv (funext fun j => by_contra fun hj => h ⟨j, hj⟩)
  have hvi : 0 < ‖v i‖ := norm_pos_iff.mpr hi

  have bound : ∀ k : ℕ, ‖μ‖ ^ k * ‖v i‖ ≤ C * ∑ j, ‖v j‖ := by
    intro k
    have e := congrFun (pow_mulVec_eq M v μ hμ k) i
    have hk : ‖μ‖ ^ k * ‖v i‖ = ‖∑ j, (M ^ k) i j * v j‖ := by
      have : (M ^ k).mulVec v i = ∑ j, (M ^ k) i j * v j := by simp [Matrix.mulVec, dotProduct]
      rw [← this, e, Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    rw [hk]
    calc ‖∑ j, (M ^ k) i j * v j‖ ≤ ∑ j, ‖(M ^ k) i j * v j‖ := norm_sum_le _ _
      _ = ∑ j, ‖(M ^ k) i j‖ * ‖v j‖ := by simp only [norm_mul]
      _ ≤ ∑ j, C * ‖v j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hC k i j) (norm_nonneg _)
      _ = C * ∑ j, ‖v j‖ := by rw [Finset.mul_sum]

  have htend : Filter.Tendsto (fun k : ℕ => ‖μ‖ ^ k * ‖v i‖) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hvi (tendsto_pow_atTop_atTop_of_one_lt hlt)
  obtain ⟨k, hk⟩ := (htend.eventually_gt_atTop (C * ∑ j, ‖v j‖)).exists
  exact absurd (bound k) (not_le.mpr hk)

end GlobalTheory.EigenvalueNormBound
end

