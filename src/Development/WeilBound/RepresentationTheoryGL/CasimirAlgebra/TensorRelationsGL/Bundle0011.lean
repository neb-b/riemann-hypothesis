module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallAlgA

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransFinA
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TF

theorem coef {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (d : ℕ) (y : ℕ → Y) (S : Set ℂ) (hS : S.Infinite)
    (h : ∀ u ∈ S, ∑ i ∈ Finset.range d, u ^ i • y i = 0) : ∀ i ∈ Finset.range d, y i = 0 := by
  intro i hi
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  set p : Polynomial ℂ := ∑ j ∈ Finset.range d, Polynomial.C (f (y j)) * Polynomial.X ^ j with hp
  have hroot : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply hS.mono
    intro u hu
    have hfu := congrArg f (h u hu)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hfu
    show Polynomial.eval u p = 0
    simp only [hp, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hfu]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q i) hroot
  simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa [hi] using hc

theorem qdet_mem {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (B : Subalgebra ℂ A)
    (hF : ∀ a b, F a b ∈ B) (u : ℂ) : qdet F u ∈ B := by
  unfold qdet qminor
  refine B.sum_mem fun σ _ => B.mul_mem ?_ (B.list_prod_mem ?_)
  · exact intCast_mem B _
  · intro z hz
    rw [List.mem_ofFn] at hz
    obtain ⟨k, rfl⟩ := hz
    unfold Tm
    refine B.add_mem ?_ (hF _ _)
    split_ifs
    · exact B.algebraMap_mem _
    · exact B.zero_mem

theorem inv_aux {A : Type*} [Ring A] [Algebra ℂ A] (B : Subalgebra ℂ A) (x : A) (hx : x ∈ B) (u : ℂ) :
    ∀ L : List ℂ, (∀ c ∈ L, u + c ≠ 0) → ∃ h ∈ B, Commute h x ∧ ∃ β : ℂ, β ≠ 0 ∧
      (L.map fun c => x - algebraMap ℂ A c).prod = (algebraMap ℂ A u + x) * h + algebraMap ℂ A β := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨0, B.zero_mem, Commute.zero_left x, 1, one_ne_zero, ?_⟩
    simp
  | cons c L ih =>
    intro hL
    obtain ⟨h, hB, hc, β, hβ, heq⟩ := ih (fun d hd => hL d (List.mem_cons_of_mem _ hd))
    have hs : u + c ≠ 0 := hL c (by simp)
    have hcm : Commute ((x - algebraMap ℂ A c) * h + algebraMap ℂ A β) x :=
      (((Commute.refl x).sub_left (Algebra.commute_algebraMap_left c x)).mul_left hc).add_left
        (Algebra.commute_algebraMap_left β x)
    refine ⟨(x - algebraMap ℂ A c) * h + algebraMap ℂ A β,
      B.add_mem (B.mul_mem (B.sub_mem hx (B.algebraMap_mem c)) hB) (B.algebraMap_mem β),
      hcm, -((u + c) * β), neg_ne_zero.mpr (mul_ne_zero hs hβ), ?_⟩
    rw [List.map_cons, List.prod_cons, heq]
    have hq : x - algebraMap ℂ A c = (algebraMap ℂ A u + x) - algebraMap ℂ A (u + c) := by
      rw [map_add (f := _)]; abel
    rw [hq, map_neg, map_mul]
    have ht := Algebra.commutes (u + c) (algebraMap ℂ A u + x)
    generalize algebraMap ℂ A u + x = v at ht ⊢
    generalize algebraMap ℂ A (u + c) = t at ht ⊢
    generalize algebraMap ℂ A β = w
    calc (v - t) * (v * h + w) = v * v * h + v * w - t * v * h - t * w := by noncomm_ring
      _ = v * v * h + v * w - v * t * h - t * w := by rw [ht]
      _ = v * ((v - t) * h + w) + -(t * w) := by noncomm_ring

theorem inv_of_alg {A : Type*} [Ring A] [Algebra ℂ A] (B : Subalgebra ℂ A) (x : A) (hx : x ∈ B) (u : ℂ)
    (L : List ℂ) (h0 : (L.map fun c => x - algebraMap ℂ A c).prod = 0) (hu : ∀ c ∈ L, u + c ≠ 0) :
    ∃ h ∈ B, h * (algebraMap ℂ A u + x) = 1 := by
  obtain ⟨h, hB, hc, β, hβ, heq⟩ := inv_aux B x hx u L hu
  rw [h0] at heq
  have hv : h * (algebraMap ℂ A u + x) = (algebraMap ℂ A u + x) * h :=
    ((Algebra.commute_algebraMap_left u h).symm.add_right hc).eq
  have hvh : (algebraMap ℂ A u + x) * h = -algebraMap ℂ A β := eq_neg_of_add_eq_zero_left heq.symm
  refine ⟨algebraMap ℂ A (-β⁻¹) * h, B.mul_mem (B.algebraMap_mem _) hB, ?_⟩
  rw [mul_assoc, hv, hvh, mul_neg, ← map_mul]
  simp [hβ]

theorem left_inv_prod {A : Type*} [Ring A] (B : Subring A) :
    ∀ l : List A, (∀ a ∈ l, ∃ h ∈ B, h * a = 1) → ∃ h ∈ B, h * l.prod = 1 := by
  intro l
  induction l with
  | nil => intro _; exact ⟨1, B.one_mem, by simp⟩
  | cons a l ih =>
    intro hl
    obtain ⟨ha, hB, hae⟩ := hl a (List.mem_cons_self ..)
    obtain ⟨h, hB', he⟩ := ih fun b hb => hl b (List.mem_cons_of_mem _ hb)
    refine ⟨h * ha, B.mul_mem hB' hB, ?_⟩
    rw [List.prod_cons, mul_assoc, ← mul_assoc ha, hae, one_mul, he]

theorem eig_prod {W : Type*} [AddCommGroup W] [Module ℂ W] (φ : W →ₗ[ℂ] ℂ) :
    ∀ l : List (Module.End ℂ W), (∀ a ∈ l, ∃ μ : ℂ, μ ≠ 0 ∧ φ ∘ₗ a = μ • φ) →
      ∃ μ : ℂ, μ ≠ 0 ∧ φ ∘ₗ l.prod = μ • φ := by
  intro l hl
  induction l with
  | nil => exact ⟨1, one_ne_zero, by ext; simp⟩
  | cons a l ih =>
    obtain ⟨μa, hμa, ha⟩ := hl a (by simp)
    obtain ⟨μl, hμl, hl1⟩ := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    refine ⟨μa * μl, mul_ne_zero hμa hμl, LinearMap.ext fun w => ?_⟩
    have e1 := LinearMap.congr_fun ha (l.prod w)
    have e2 := LinearMap.congr_fun hl1 w
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [List.prod_cons, Module.End.mul_apply, e1, e2, mul_assoc]

end TF

end PositivityTheory.Rg.Cz
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallAlg
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

open WallAlgP in
theorem wallAlg_of (hA : TensorGl) (_hJ : JMComm) (hQ : QdetFacts) (hS : Spectrum) : WallAlg := by
  unfold WallAlg
  intro n M _ _ E₁ E₂ h₁ h₂ hcomm s₁ s₂ c hc₁ hc₂ m X hX hperm hOm htot
  obtain ⟨ξ0, hξ0X, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  have eqA : (n:ℂ) * (s₁ + s₂) + n * (n - 1) + m = n * c := by
    have tr₁ := (hQ n M E₁ h₁).2.2.1 _ hc₁
    have tr₂ := (hQ n M E₂ h₂).2.2.1 _ hc₂
    have key1 := trace_rel E₁ E₂ c _ _ ξ0 tr₁ tr₂ (fun a b => htot a b ξ0 hξ0X)
    have e := smul_left_injective ℂ hξ0 key1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e
    linear_combination e
  refine ⟨eqA, fun hm => ?_⟩
  have hOmC : ∀ (σ : Equiv.Perm (Fin m)) (p : Fin m), pm σ * Om E₁ p = Om E₁ (σ p) * pm σ :=
    (hA n M (Fin m) E₁ h₁ Finset.univ).2.2.2
  have key : ∀ k, k < n → k ≤ m → (∃ ξ ∈ X, alt (firstG m k) ξ ≠ 0) →
      k < m ∧ ∃ ξ ∈ X, alt (firstG m (k + 1)) ξ ≠ 0 := by
    intro k hkn hkm hPk
    by_contra hneg
    have hout : ∀ ξ ∈ X, ∀ i : Fin m, k ≤ (i:ℕ) →
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), pm (Equiv.swap j i) (alt (firstG m k) ξ) = alt (firstG m k) ξ := by
      intro ξ hξ i hi
      have hk : k < m := lt_of_le_of_lt hi i.isLt
      have hz : ∀ η ∈ X, alt (firstG m (k + 1)) η = 0 := by
        intro η hη
        by_contra hne
        exact hneg ⟨hk, η, hη, hne⟩
      exact outer hk X hperm hz ξ hξ i hi
    have hsw : ∀ ξ : TV n M (Fin m), ∀ i j : Fin m, i ≠ j → (i:ℕ) < k → (j:ℕ) < k →
        pm (Equiv.swap i j) (alt (firstG m k) ξ) = -alt (firstG m k) ξ := by
      intro ξ i j hij hi hj
      have hmem : Equiv.swap i j ∈ firstG m k := by
        rw [mem_firstG]
        intro l hl
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          rw [h] at hl
          omega
        · intro h
          rw [h] at hl
          omega
      rw [pm_alt_first _ hmem, Equiv.Perm.sign_swap hij]
      simp
    have hinv : ∀ y ∈ X.map (alt (firstG m k)),
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E₁ j) y ∈ X.map (alt (firstG m k)) := by
      intro y hy
      obtain ⟨ξ, hξ, rfl⟩ := Submodule.mem_map.mp hy
      simp only [xJ, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
      refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j hj => Submodule.sum_mem _ fun i hi => ?_)
      · rw [← om_alt E₁ hOmC k ξ]
        exact Submodule.mem_map_of_mem (Submodule.sum_mem _ fun j _ => hOm j ξ hξ)
      · have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        rw [hsw ξ i j (ne_of_lt hi') (lt_trans (show (i:ℕ) < (j:ℕ) from hi') hj') hj']
        exact Submodule.neg_mem _ (Submodule.mem_map_of_mem hξ)
    obtain ⟨ξ1, hξ1X, hξ1⟩ := hPk
    obtain ⟨L₁, hL₁⟩ := (hS n M E₁ h₁ (fun _ => s₁) s₁ hc₁ (fun _ => ⟨0, by simp⟩) m).1 k hkm
    obtain ⟨L₂, hL₂⟩ := (hS n M E₂ h₂ (fun _ => s₂) s₂ hc₂ (fun _ => ⟨0, by simp⟩) m).1 k hkm
    obtain ⟨w, hwY, hw0, r₁, hw1⟩ := eigen (X.map (alt (firstG m k))) _ hinv
      (fun r : ℕ => (k:ℂ) * s₁ + r) L₁ hL₁ (alt (firstG m k) ξ1) (Submodule.mem_map_of_mem hξ1X) hξ1
    obtain ⟨ζ, hζ, rfl⟩ := Submodule.mem_map.mp hwY
    have hwX : alt (firstG m k) ζ ∈ X := alt_mem X hperm ζ hζ
    have hw := fun a b => htot a b _ hwX
    set w := alt (firstG m k) ζ with hwdef
    have hT : ∀ E : Fin n → Fin n → Module.End ℂ M, (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E j) w =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), Om E j w +
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w := by
      intro E
      simp only [xJ, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
    have hsplit : ∀ j : Fin m, (j:ℕ) < k →
        ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
          ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w +
            ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), pm (Equiv.swap j p) w := by
      intro j hj
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases h1 : p = j
      · subst h1
        simp [not_le.mpr hj]
      · by_cases h2 : (p:ℕ) < k
        · simp [h1, h2, not_le.mpr h2]
        · simp [h1, h2, not_lt.mp h2]
    have e1 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), (∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w +
            ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), pm (Equiv.swap j p) w) :=
      Finset.sum_congr rfl fun j hj => hsplit j (Finset.mem_filter.mp hj).2
    have e2 : ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), pm (Equiv.swap j p) w =
        ∑ p ∈ Finset.univ.filter (fun p : Fin m => k ≤ (p:ℕ)), w :=
      Finset.sum_congr rfl fun p hp => hout ζ hζ p (Finset.mem_filter.mp hp).2
    have e3 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p:ℕ) < k ∧ p ≠ j), pm (Equiv.swap j p) w =
        2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w :=
      symm_sum (fun i j => pm (Equiv.swap i j) w) (fun i j => by simp only [Equiv.swap_comm i j])
    have hmid : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w =
        2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < j), pm (Equiv.swap i j) w +
          ((m:ℂ) - k) • w := by
      rw [e1, Finset.sum_add_distrib, e3, Finset.sum_comm, e2, Finset.sum_const, card_highS hkm,
        ← Nat.cast_smul_eq_nsmul ℂ (m - k), Nat.cast_sub hkm]
    have hsum : ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k),
        (Om E₁ j w + Om E₂ j w + ∑ p ∈ Finset.univ.filter (fun p : Fin m => p ≠ j), pm (Equiv.swap j p) w + (n:ℂ) • w) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), c • w :=
      Finset.sum_congr rfl fun j _ => contr E₁ E₂ c w hw j
    simp only [Finset.sum_add_distrib, Finset.sum_const, card_lowS hkm] at hsum
    rw [hmid] at hsum
    have h1 := hw1
    rw [hT E₁] at h1
    have hT2 : (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j:ℕ) < k), xJ E₂ j) w =
        ((k:ℂ) * c - k * n - (m - k) - ((k:ℂ) * s₁ + r₁)) • w := by
      rw [hT E₂]
      linear_combination (norm := module) hsum - h1
    obtain ⟨r₂, hr₂⟩ := eigen_val _ (fun r : ℕ => (k:ℂ) * s₂ + r) L₂ hL₂ w hw0 _ hT2
    have hr : (k:ℂ) * c - k * n - (m - k) - ((k:ℂ) * s₁ + r₁) = k * s₂ + r₂ := hr₂
    have hfin : (m:ℂ) * k = m * n + n * (r₁ + r₂) := by
      linear_combination (n:ℂ) * hr + (k:ℂ) * eqA
    have hnat : m * k = m * n + n * (r₁ + r₂) := by exact_mod_cast hfin
    have h3 : m * (k + 1) ≤ m * n := Nat.mul_le_mul_left m hkn
    nlinarith [Nat.zero_le (n * (r₁ + r₂))]
  have hall : ∀ k, k ≤ n → k ≤ m ∧ ∃ ξ ∈ X, alt (firstG m k) ξ ≠ 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨Nat.zero_le _, ξ0, hξ0X, by rwa [alt_zero]⟩
    | succ k ih =>
      intro hk
      obtain ⟨hkm, hP⟩ := ih (Nat.le_of_succ_le hk)
      exact key k (Nat.lt_of_succ_le hk) hkm hP
  exact hall n le_rfl

end PositivityTheory.Rg.Cz

end
end

