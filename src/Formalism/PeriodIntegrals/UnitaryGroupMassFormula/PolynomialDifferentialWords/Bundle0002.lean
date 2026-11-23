module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaMain
section
open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

theorem symbolMapInjective : KappaInj := by
  intro K _ _ k d A B h
  have hmono : ∀ g : Fin k →₀ ℕ, A (mono K k d g) = B (mono K k d g) := by
    intro g
    apply Subtype.ext
    ext m
    have h1 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.sumElim m g)) h
    rw [coeff_kappa, coeff_kappa] at h1
    exact mul_left_cancel₀ (invFact_ne_zero g) h1
  apply LinearMap.ext
  intro F
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_mono F, map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, map_smul, hmono g]

theorem symbolMapBihomogeneous : KappaBihom := by
  intro K _ _ k d A
  show kappa K k d A ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d
  have key : ∀ m g : Fin k →₀ ℕ, AddMonoidAlgebra.coeff (kappa K k d A) (Finsupp.sumElim m g) ≠ 0 →
      m.degree = d ∧ g.degree = d := by
    intro m g h
    rw [coeff_kappa] at h
    have h2 : AddMonoidAlgebra.coeff (A (mono K k d g) : MvPolynomial (Fin k) K) m ≠ 0 := right_ne_zero_of_mul h
    refine ⟨degree_of_coeff_ne _ h2, ?_⟩
    by_contra hg
    have h0 : mono K k d g = 0 := by
      unfold mono
      rw [dite_eq_right hg]
    rw [h0, map_zero] at h2
    simp at h2
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩ <;> rw [mem_weightedHomogeneousSubmodule] <;> intro n hn <;>
    obtain ⟨m, g, rfl⟩ := exists_sumElim n
  · rw [weight_wx]
    exact (key m g hn).1
  · rw [weight_wxi]
    exact (key m g hn).2

theorem symbolMapMulLeft : KappaLeft := by
  intro K _ _ k d a b A
  set_option synthInstance.maxHeartbeats 100000 in
    rw [kappa_apply, kappa_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_apply_eq_comp, Ed_val, Derivation.map_smul, mul_smul_comm]
  congr 1
  simp only [Derivation.leibniz, pderiv_inl_xi, smul_eq_mul]
  rw [pderiv_rename Sum.inl_injective, map_mul, rename_X]
  ring

private theorem coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth {σ : Type} {K : Type} [Field K] (i : σ) (P : MvPolynomial σ K)
    (n : σ →₀ ℕ) : AddMonoidAlgebra.coeff (pderiv i P) n = AddMonoidAlgebra.coeff P (n + Finsupp.single i 1) * ((n i : K) + 1) := by
  classical
  induction P using MvPolynomial.induction_on'
  next u c =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : u = n + Finsupp.single i 1
    · subst h
      simp
    · rw [ite_eq_right h, zero_mul]
      split_ifs with h2
      · have hu : u i = 0 := by
          by_contra hne
          apply h
          rw [← h2, tsub_add_cancel_of_le]
          rw [Finsupp.single_le_iff]
          omega
        simp [hu]
      · rfl
  next p q hp hq =>
    rw [map_add (f := _), AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp, hq, add_mul]

theorem symbolMapMulRight : KappaRight := by
  intro K _ _ k d a b A
  apply pol_ext
  intro m g
  rw [coeff_kappa, mul_apply_eq_comp, Ed_mono, map_smul, Submodule.coe_smul, coeff_smul, coeff_X_mul']
  by_cases hb : g b = 0
  · rw [ite_eq_right (by simp [hb])]
    simp [hb]
  · rw [ite_eq_left (by simp [hb]), sumElim_sub_single_inr, coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth, sumElim_add_single_inr, coeff_kappa]
    simp only [Finsupp.sumElim_apply, Sum.elim_inr]
    have h1 := invFact_add_single (K := K) (g - single b 1) a
    have h2 := invFact_add_single (K := K) (g - single b 1) b
    have hle : single b 1 ≤ g := by
      rw [Finsupp.single_le_iff]
      omega
    rw [tsub_add_cancel_of_le hle] at h2
    have h3 : ((g - single b 1 : Fin k →₀ ℕ) b : K) + 1 = (g b : K) := by
      have h4 : (g - single b 1 : Fin k →₀ ℕ) b + 1 = g b := by
        simp
        omega
      exact_mod_cast h4
    rw [h3] at h2
    linear_combination (AddMonoidAlgebra.coeff (A (mono K k d (g - single b 1 + single a 1)) : MvPolynomial (Fin k) K) m) * h2 -
      (AddMonoidAlgebra.coeff (A (mono K k d (g - single b 1 + single a 1)) : MvPolynomial (Fin k) K) m) * h1

private theorem coeff_sumElim_tt_pow (K : Type) [Field K] (k d : ℕ) (m g : Fin k →₀ ℕ) :
    AddMonoidAlgebra.coeff (tt K k ^ d) (Finsupp.sumElim m g) =
      if m = g ∧ g.degree = d then ((Nat.multinomial Finset.univ ⇑g : ℕ) : K) else 0 := by
  classical
  have hprod : ∀ f : Fin k → ℕ, ∏ i, (X (Sum.inl i) * X (Sum.inr i) : Pol K k) ^ f i =
      monomial (Finsupp.sumElim (Finsupp.equivFunOnFinite.symm f) (Finsupp.equivFunOnFinite.symm f)) 1 := by
    intro f
    rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
    simp [mul_pow, Finset.prod_mul_distrib]
  rw [tt, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp only [hprod, ← map_natCast (C : K →+* Pol K k), coeff_C_mul, coeff_monomial, sumElim_inj, mul_ite,
    mul_one, mul_zero]
  by_cases h : m = g ∧ g.degree = d
  · obtain ⟨hmg, hd⟩ := h
    rw [ite_eq_left ⟨hmg, hd⟩, Finset.sum_eq_single (⇑g)]
    · simp [hmg]
    · intro f _ hf
      rw [ite_eq_right]
      rintro ⟨_, h2⟩
      apply hf
      rw [← h2]
      simp
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      rw [← hd, Finsupp.degree_eq_sum]
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun f hf => ?_
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    apply h
    refine ⟨h1.symm.trans h2, ?_⟩
    rw [← h2, Finsupp.degree_eq_sum]
    have h3 := (Finset.mem_piAntidiag.1 hf).1
    simpa using h3

theorem symbolMapOne : KappaId := by
  intro K _ _ k d
  apply pol_ext
  intro m g
  rw [coeff_kappa, one_apply_eq_self, mono_val, coeff_smul, smul_eq_mul, coeff_sumElim_tt_pow]
  by_cases h : m = g ∧ g.degree = d
  · obtain ⟨hmg, hd⟩ := h
    rw [ite_eq_left hd, ite_eq_left ⟨hmg, hd⟩, coeff_monomial, ite_eq_left hmg.symm, mul_one]
    have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin k)) ⇑g
    have hsum : ∑ i, g i = d := by rw [← hd, Finsupp.degree_eq_sum]
    rw [hsum] at hspec
    have hcast : ((d.factorial : ℕ) : K) =
        (∏ i, ((g i).factorial : K)) * (Nat.multinomial Finset.univ ⇑g : K) := by
      exact_mod_cast hspec.symm
    have hM : (Nat.multinomial Finset.univ ⇑g : K) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hcast
      exact (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)) hcast
    unfold invFact
    rw [prodFact_fintype, hcast, mul_inv, mul_assoc, inv_mul_cancel₀ hM, mul_one]
  · rw [ite_eq_right h, mul_zero]
    split_ifs with hd
    · rw [coeff_monomial, ite_eq_right (fun hgm => h ⟨hgm.symm, hd⟩), mul_zero]
    · simp

end PI.OpWords
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.VanishMain
section
open MvPolynomial

noncomputable section

namespace PI.OpWords

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

lemma eval_eq_zero_of_support (g : Pol K k) (p : Fin k ⊕ Fin k → K)
    (h : ∀ m ∈ g.support, ∃ i, m i ≠ 0 ∧ p i = 0) : eval p g = 0 := by
  rw [eval_eq]
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨i, hmi, hpi⟩ := h m hm
  rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hmi) (by rw [hpi]; exact zero_pow hmi), mul_zero]

lemma xdeg_of_bihom {d : ℕ} {g : Pol K k} (hg : g ∈ Bihom K k d) {m : Fin k ⊕ Fin k →₀ ℕ}
    (hm : m ∈ g.support) : ∑ a, m (Sum.inl a) = d := by
  have hg' : g ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hg
  have hx := (Submodule.mem_inf.1 hg').1
  rw [mem_weightedHomogeneousSubmodule] at hx
  have h1 := hx (MvPolynomial.mem_support_iff.1 hm)
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, wx, Fintype.sum_sum_type] using h1

lemma eval_base {d c : ℕ} (hcd : c < d) (i0 : Fin k) {g : Pol K k} (hg : g ∈ Bihom K k d)
    (hw : WtLe K k c g) (p : Fin k ⊕ Fin k → K) (hx : ∀ b, b ≠ i0 → p (Sum.inl b) = 0)
    (hxi : p (Sum.inr i0) = 0) : eval p g = 0 := by
  apply eval_eq_zero_of_support
  intro m hm
  by_contra hne
  push_neg at hne
  have hzero : ∀ b, b ≠ i0 → m (Sum.inl b) = 0 := by
    intro b hb
    by_contra h0
    exact hne _ h0 (hx b hb)
  have hr : m (Sum.inr i0) = 0 := by
    by_contra h0
    exact hne _ h0 hxi
  have hsum := xdeg_of_bihom hg hm
  rw [Finset.sum_eq_single i0 (fun b _ hb => hzero b hb)
    (fun h => absurd (Finset.mem_univ i0) h)] at hsum
  have h2 := hw m hm i0
  omega

lemma iter_mem (W : Submodule K (Pol K k)) (hst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W)
    (a b : Fin k) {g : Pol K k} (hg : g ∈ W) (n : ℕ) : (Rop K k a b)^[n] g ∈ W := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hst _ ih a b

lemma vanish_at {d c : ℕ} (W : Submodule K (Pol K k)) (hW : W ≤ Bihom K k d)
    (hst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) (hwt : ∀ f ∈ W, WtLe K k c f) (hcd : c < d)
    (i0 : Fin k) (S : Finset (Fin k)) :
    ∀ p : Fin k ⊕ Fin k → K, p (Sum.inl i0) ≠ 0 → (∀ b, b ≠ i0 → p (Sum.inl b) ≠ 0 → b ∈ S) →
      ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → ∀ g ∈ W, eval p g = 0 := by
  classical
  induction S using Finset.induction_on
  next =>
    intro p hp0 hS hq g hg
    have hx : ∀ b, b ≠ i0 → p (Sum.inl b) = 0 := by
      intro b hb
      by_contra h
      exact absurd (hS b hb h) (by simp)
    have hxi : p (Sum.inr i0) = 0 := by
      rw [Finset.sum_eq_single i0 (fun b _ hb => by rw [hx b hb, zero_mul])
        (fun h => absurd (Finset.mem_univ i0) h)] at hq
      exact (mul_eq_zero.1 hq).resolve_left hp0
    exact eval_base hcd i0 (hW hg) (hwt g hg) p hx hxi
  next b S hbS ih =>
    intro p hp0 hS hq g hg
    by_cases hpb : p (Sum.inl b) = 0
    · refine ih p hp0 ?_ hq g hg
      intro b' hb' hne
      rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
      · subst h
        exact absurd hpb hne
      · exact h
    by_cases hbi : b = i0
    · refine ih p hp0 ?_ hq g hg
      intro b' hb' hne
      rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
      · exact absurd (h.trans hbi) hb'
      · exact h
    have hib : i0 ≠ b := Ne.symm hbi
    have hshl : ∀ (t : K) (y : Fin k ⊕ Fin k → K) (j : Fin k),
        shiftPt i0 b t y (Sum.inl j) = y (Sum.inl j) + t * (if j = b then y (Sum.inl i0) else 0) := by
      intro t y j
      by_cases h : j = b <;> simp [shiftPt, rop_apply, pderiv_X, Pi.single_apply, h] <;> ring
    have hshr : ∀ (t : K) (y : Fin k ⊕ Fin k → K) (j : Fin k),
        shiftPt i0 b t y (Sum.inr j) = y (Sum.inr j) - t * (if j = i0 then y (Sum.inr b) else 0) := by
      intro t y j
      by_cases h : j = i0 <;> simp [shiftPt, rop_apply, pderiv_X, Pi.single_apply, h] <;> ring
    obtain ⟨s, hs⟩ : ∃ s : K, s = -(p (Sum.inl b) / p (Sum.inl i0)) := ⟨_, rfl⟩
    have hq0 : shiftPt i0 b s p (Sum.inl i0) = p (Sum.inl i0) := by
      rw [hshl, if_neg hib, mul_zero, add_zero]
    have hqb : shiftPt i0 b s p (Sum.inl b) = 0 := by
      rw [hshl, if_pos rfl, hs, neg_mul, div_mul_cancel₀ _ hp0]
      ring
    have hqj : ∀ j, j ≠ b → shiftPt i0 b s p (Sum.inl j) = p (Sum.inl j) := by
      intro j hj
      rw [hshl, if_neg hj, mul_zero, add_zero]
    have hquad : ∑ i, shiftPt i0 b s p (Sum.inl i) * shiftPt i0 b s p (Sum.inr i) = 0 := by
      simp only [hshl, hshr, mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hbi, hib, if_false, hq]
      ring
    have ihq : ∀ g ∈ W, eval (shiftPt i0 b s p) g = 0 := by
      refine ih _ (by rw [hq0]; exact hp0) ?_ hquad
      intro b' hb' hne
      by_cases hbb : b' = b
      · subst hbb
        exact absurd hqb hne
      · rw [hqj b' hbb] at hne
        rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
        · exact absurd h hbb
        · exact h
    have hback : shiftPt i0 b (-s) (shiftPt i0 b s p) = p := by
      funext v
      rcases v with j | j
      · by_cases h : j = b <;> simp [hshl, h, hib] <;> ring
      · by_cases h : j = i0 <;> simp [hshr, h, hbi] <;> ring
    have hE := expFormula i0 b hib (-s) g
    unfold ExpFormula at hE
    obtain ⟨N, _, hsum⟩ := hE
    rw [← hback, hsum N le_rfl]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [ihq _ (iter_mem W hst i0 b hg n), mul_zero]

theorem vanishingOnQuadric : Vanish := by
  intro K _ _ k d c W hW hst hwt hcd f hf p hp
  by_cases h : ∃ i0, p (Sum.inl i0) ≠ 0
  · obtain ⟨i0, hi0⟩ := h
    exact vanish_at W hW hst hwt hcd i0 Finset.univ p hi0 (fun b _ _ => Finset.mem_univ b) hp f hf
  · push_neg at h
    apply eval_eq_zero_of_support
    intro m hm
    have hsum := xdeg_of_bihom (hW hf) hm
    have hex : ∃ a, m (Sum.inl a) ≠ 0 := by
      by_contra h0
      push_neg at h0
      simp [h0] at hsum
      omega
    obtain ⟨a, ha⟩ := hex
    exact ⟨Sum.inl a, ha, h a⟩

end PI.OpWords
end
end

