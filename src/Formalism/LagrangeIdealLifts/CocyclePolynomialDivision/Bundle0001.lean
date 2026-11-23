module

public import Formalism.LagrangeIdealLifts.Statement

@[expose] public section

-- bundled from Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.Graded
section
namespace Formalism.LIFT

theorem gammaGradedStep_holds : GradedStep := by
  intro ℓ _ A _ _ B M D _ _ _ _ W i n hn
  obtain ⟨t, ht⟩ := B.γX
  obtain ⟨n', hn', hγ⟩ := W.γ_N n hn
  have hw : ∀ k : ℕ, ∃ r : A, (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t) ^ k
      = algebraMap ℤ_[ℓ] A ((B.u : ℤ_[ℓ]) ^ k) + B.X * r := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t)
        + algebraMap ℤ_[ℓ] A ((B.u : ℤ_[ℓ]) ^ k) * t, ?_⟩
      rw [pow_succ, hr, pow_succ, map_mul]; ring
  obtain ⟨r, hr⟩ := hw i
  have hγn : W.γ n = n + B.X • n' := by rw [← hγ]; abel
  refine ⟨r • n + (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t) ^ i • n', ?_, ?_⟩
  · exact W.N.add_mem (W.N.smul_mem _ hn) (W.N.smul_mem _ hn')
  · rw [W.γ_smul, map_pow, ht, mul_pow, hγn, hr,
      ← algebraMap_smul A ((B.u : ℤ_[ℓ]) ^ i) (B.X ^ i • n)]
    module

theorem uGraded_of (h : GradedStep) : UGraded := by
  intro ℓ _ A _ _ B M D _ _ _ _ W K
  induction K with
  | zero =>
    intro n hn
    exact ⟨0, W.N.zero_mem, n, hn, by simp⟩
  | succ K ih =>
    intro n hn
    obtain ⟨x, hx, n', hn', he⟩ := ih n hn
    obtain ⟨n'', hn'', hg⟩ := h ℓ A B M D W (K + 1) n' hn'
    refine ⟨((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • x + B.X ^ K • n', ?_, -n'', W.N.neg_mem hn'', ?_⟩
    · exact W.N.add_mem (Submodule.smul_of_tower_mem _ _ hx) (W.N.smul_mem _ hn')
    · rw [Finset.prod_Icc_succ_top (by omega), mul_comm, mul_smul, he]
      have e1 : B.X • (((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • x + B.X ^ K • n')
          = ((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • (B.X • x) + B.X ^ (K + 1) • n' := by
        rw [smul_add, smul_comm, ← mul_smul, ← pow_succ']
      rw [e1, LinearMap.map_add (f := _), LinearMap.map_smul]
      have e2 : W.γ (B.X ^ (K + 1) • n') = ((B.u : ℤ_[ℓ]) ^ (K + 1)) • (B.X ^ (K + 1) • n')
          + B.X ^ (K + 1 + 1) • n'' := by rw [← hg]; abel
      rw [e2]
      simp only [sub_smul, one_smul, smul_add, smul_sub, smul_neg]
      abel

namespace GradedDegree

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}

theorem X_pow_inj {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D) (k : ℕ) (x : D) (h : B.X ^ k • x = 0) : x = 0 := by
  induction k generalizing x with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply W.X_inj
    rw [← mul_smul, ← pow_succ']
    exact h

theorem aeval_mul_X {D : Type} [AddCommGroup D] [Module ℤ_[ℓ] D] (g : D →ₗ[ℤ_[ℓ]] D)
    (p : Polynomial ℤ_[ℓ]) : Polynomial.aeval g (p * Polynomial.X) = Polynomial.aeval g p * g := by
  rw [map_mul, Polynomial.aeval_X]

theorem aeval_mem {D : Type} [AddCommGroup D] [Module ℤ_[ℓ] D] (g : D →ₗ[ℤ_[ℓ]] D)
    (S : D → Prop) (hadd : ∀ x y, S x → S y → S (x + y))
    (hsmul : ∀ (c : ℤ_[ℓ]) x, S x → S (c • x)) (hg : ∀ x, S x → S (g x))
    (p : Polynomial ℤ_[ℓ]) : ∀ x, S x → S (Polynomial.aeval g p x) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro c x hx
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact hsmul c x hx
  · intro p q hp hq x hx
    rw [map_add (f := _), LinearMap.add_apply]
    exact hadd _ _ (hp x hx) (hq x hx)
  · intro k c h x hx
    rw [pow_succ, ← mul_assoc, aeval_mul_X, Module.End.mul_apply]
    exact h _ (hg x hx)

theorem hom_aeval {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A D'] {W : WD B M D} {W' : WD B M D'} (f : Hom W W')
    (p : Polynomial ℤ_[ℓ]) : ∀ x, f.f (Polynomial.aeval W.γ p x) = Polynomial.aeval W'.γ p (f.f x) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro c x
    rw [Polynomial.aeval_C, Polynomial.aeval_C, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, LinearMap.map_smul_of_tower]
  · intro p q hp hq x
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  · intro k c h x
    rw [pow_succ, ← mul_assoc, aeval_mul_X, aeval_mul_X, Module.End.mul_apply,
      Module.End.mul_apply, h, f.γ_comm]

theorem graded_prod (hG : GradedStep) {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D) (i j : ℕ) (hij : i ≤ j) :
    ∀ m ∈ W.N, ∃ m' ∈ W.N, Polynomial.aeval W.γ
      (∏ k ∈ Finset.Ico i j, (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ k))) (B.X ^ i • m)
        = B.X ^ j • m' := by
  induction j, hij using Nat.le_induction with
  | base => intro m hm; exact ⟨m, hm, by simp⟩
  | succ j hij ih =>
    intro m hm
    obtain ⟨m', hm', he⟩ := ih m hm
    obtain ⟨m'', hm'', hg⟩ := hG ℓ A B M D W j m' hm'
    refine ⟨m'', hm'', ?_⟩
    rw [Finset.prod_Ico_succ_top hij, mul_comm, map_mul, Module.End.mul_apply, he, map_sub,
      Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, hg]

end GradedDegree

open GradedDegree in
theorem wBTail_of (hG : GradedStep) (hL : LagrangeIdealCyc) : WBTail := by
  intro ℓ _ A _ _ B M D₁ D₂ _ _ _ _ _ _ _ _ W₁ W₂ f s a hs hs2 hv hX n hn
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp (hL ℓ B.u s hs hs2 hv a)
  let S : D₂ → Prop := fun y => ∃ m ∈ W₁.N, y = f.f (B.X ^ a • m)
  have hadd : ∀ x y, S x → S y → S (x + y) := by
    rintro x y ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m + m', W₁.N.add_mem hm hm', by rw [smul_add, map_add (f := _)]⟩
  have hsmul : ∀ (c : ℤ_[ℓ]) x, S x → S (c • x) := by
    rintro c x ⟨m, hm, rfl⟩
    exact ⟨c • m, Submodule.smul_of_tower_mem _ _ hm,
      by rw [smul_comm (B.X ^ a) c m]; exact (LinearMap.map_smul_of_tower f.f c _).symm⟩
  have hγS : ∀ x, S x → S (W₂.γ x) := by
    rintro x ⟨m, hm, rfl⟩
    obtain ⟨m', hm', hg⟩ := hG ℓ A B M D₁ W₁ a m hm
    refine ⟨((B.u : ℤ_[ℓ]) ^ a) • m + B.X • m',
      W₁.N.add_mem (Submodule.smul_of_tower_mem _ _ hm) (W₁.N.smul_mem _ hm'), ?_⟩
    have e : W₁.γ (B.X ^ a • m) = ((B.u : ℤ_[ℓ]) ^ a) • (B.X ^ a • m) + B.X ^ (a + 1) • m' := by
      rw [← hg]; abel
    rw [← f.γ_comm, e, smul_add, smul_comm (B.X ^ a) ((B.u : ℤ_[ℓ]) ^ a) m, ← mul_smul, ← pow_succ]
  obtain ⟨m, hm, hfm⟩ := hX n hn
  have hP₁ : S (Polynomial.aeval W₂.γ
      (∏ i ∈ Finset.range a, (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ i))) (B.X ^ a • n)) := by
    obtain ⟨m₁, hm₁, h1⟩ := graded_prod hG W₁ 0 a (Nat.zero_le a) m hm
    rw [← Finset.range_eq_Ico, pow_zero, one_smul] at h1
    exact ⟨m₁, hm₁, by rw [← hfm, ← hom_aeval, h1]⟩
  have hP₂ : S (Polynomial.aeval W₂.γ
      (∏ i ∈ Finset.Ico a (2 * a), (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ i)))
        (B.X ^ a • n)) := by
    obtain ⟨n₂, hn₂, h2⟩ := graded_prod hG W₂ a (2 * a) (by omega) n hn
    obtain ⟨m₂, hm₂, hfm₂⟩ := hX n₂ hn₂
    exact ⟨m₂, hm₂, by rw [h2, LinearMap.map_smul, hfm₂, ← mul_smul, ← pow_add, two_mul]⟩
  have key : S (Polynomial.aeval W₂.γ (Polynomial.C ((ℓ : ℤ_[ℓ]) ^
      (2 * a * s + padicValNat ℓ (2 * a).factorial))) (B.X ^ a • n)) := by
    rw [← hαβ, map_add (f := _), map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply]
    exact hadd _ _ (aeval_mem W₂.γ S hadd hsmul hγS α _ hP₁)
      (aeval_mem W₂.γ S hadd hsmul hγS β _ hP₂)
  rw [Polynomial.aeval_C, Module.algebraMap_end_apply] at key
  obtain ⟨m₃, hm₃, h3⟩ := key
  refine ⟨m₃, hm₃, ?_⟩
  have h0 := X_pow_inj W₂ a (f.f m₃ - ((ℓ : ℤ_[ℓ]) ^ (2 * a * s + padicValNat ℓ (2 * a).factorial)) • n)
    (by rw [smul_sub, ← LinearMap.map_smul, smul_comm (B.X ^ a), ← h3, sub_self])
  exact sub_eq_zero.mp h0

end Formalism.LIFT
end

-- bundled from Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.LagrangeIdeal
section
noncomputable section

namespace Formalism.LIFT

open Polynomial

theorem prod_X_sub_C_dvd_of_injOn {R : Type} [CommRing R] [IsDomain R] {ι : Type}
    (S : Finset ι) (c : ι → R) (hc : Set.InjOn c S) (G : R[X])
    (hG : ∀ a ∈ S, G.eval (c a) = 0) : (∏ a ∈ S, (X - C (c a))) ∣ G := by
  classical
  by_cases hG0 : G = 0
  · rw [hG0]
    exact dvd_zero _
  have hle : S.val.map c ≤ G.roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map_on (fun a ha b hb hab => hc ha hb hab) S.nodup)]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hG0).mpr (hG a ha)
  calc (∏ a ∈ S, (X - C (c a))) = ((S.val.map c).map fun x => X - C x).prod := by
        rw [Multiset.map_map]
        rfl
    _ ∣ (G.roots.map fun x => X - C x).prod :=
        Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)
    _ ∣ G := Polynomial.prod_multiset_X_sub_C_dvd G

theorem lagrangian_ideal_holds : LagrangeIdeal := by
  intro R _ _ ℓ ι _ S₁ S₂ c w hdisj hw
  set N := S₁.sup fun a => (∑ b ∈ S₂, w a b) + ∑ a' ∈ S₁.erase a, w a a' with hN
  by_cases hℓN : ℓ ^ N = 0
  · rw [hℓN, map_zero]
    exact Ideal.zero_mem _
  have hleN : ∀ a ∈ S₁, (∑ a' ∈ S₁.erase a, w a a') + ∑ b ∈ S₂, w a b ≤ N := by
    intro a ha
    rw [add_comm]
    exact Finset.le_sup (f := fun a => (∑ b ∈ S₂, w a b) + ∑ a' ∈ S₁.erase a, w a a') ha
  have hval : ∀ a ∈ S₁, ∃ u : R,
      ℓ ^ N = ((∏ a' ∈ S₁.erase a, (c a - c a')) * ∏ b ∈ S₂, (c a - c b)) * u := by
    intro a ha
    have hassoc : Associated ((∏ a' ∈ S₁.erase a, (c a - c a')) * ∏ b ∈ S₂, (c a - c b))
        (ℓ ^ ((∑ a' ∈ S₁.erase a, w a a') + ∑ b ∈ S₂, w a b)) := by
      rw [pow_add, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
      refine Associated.mul_mul (Associated.prod _ _ _ fun a' ha' => ?_) (Associated.prod _ _ _ fun b hb => ?_)
      · exact hw a ha a' (Finset.mem_union_left _ (Finset.mem_of_mem_erase ha'))
          (Finset.ne_of_mem_erase ha').symm
      · refine hw a ha b (Finset.mem_union_right _ hb) ?_
        intro hab
        subst hab
        exact Finset.disjoint_left.mp hdisj ha hb
    exact (hassoc.dvd_iff_dvd_left).mpr (pow_dvd_pow ℓ (hleN a ha))
  choose! u hu using hval
  have hinj : Set.InjOn c S₁ := by
    intro a ha a' ha' heq
    by_contra hne
    have hw' : w a a' ≤ N := le_trans (Finset.single_le_sum (f := fun x => w a x)
      (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨Ne.symm hne, ha'⟩)) (le_trans (Nat.le_add_right _ _) (hleN a ha))
    have hpow : ℓ ^ w a a' ≠ 0 := by
      intro h0
      apply hℓN
      rw [← Nat.add_sub_cancel' hw', pow_add, h0, zero_mul]
    have := (hw a ha a' (Finset.mem_union_left _ ha') hne).ne_zero_iff.mpr hpow
    exact this (by rw [heq, sub_self])
  set F : R[X] := ∑ a ∈ S₁, C (u a) * ∏ a' ∈ S₁.erase a, (X - C (c a')) with hF
  have hQ : (∏ a ∈ S₁, (X - C (c a))) ∣ F * ∏ b ∈ S₂, (X - C (c b)) - C (ℓ ^ N) := by
    apply prod_X_sub_C_dvd_of_injOn S₁ c hinj
    intro a ha
    rw [eval_sub, eval_mul, eval_C, hF, Polynomial.eval_finsetSum, Finset.sum_eq_single a]
    · simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
      rw [hu a ha]
      ring
    · intro a₀ _ hne
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hne, ha⟩)
        (by simp), mul_zero]
    · intro h
      exact absurd ha h
  obtain ⟨k, hk⟩ := hQ
  have hC : C (ℓ ^ N) = F * ∏ b ∈ S₂, (X - C (c b)) - (∏ a ∈ S₁, (X - C (c a))) * k := by
    rw [← hk]
    ring
  rw [hC]
  refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
  · simp
  · simp

theorem lagrangian_ideal_integral_holds : LagrangeIdealInt := by
  intro ℓ _ R _ _ S₁ S₂ c hdisj hw
  exact lagrangian_ideal_holds R (ℓ : R) ℤ S₁ S₂ c (fun a b => padicValInt ℓ (a - b)) hdisj hw

end Formalism.LIFT
end
end

