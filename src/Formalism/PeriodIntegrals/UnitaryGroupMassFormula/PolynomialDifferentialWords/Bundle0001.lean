module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight
public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.DivideAll
section
open MvPolynomial

noncomputable section

namespace PI.OpWords

theorem wtLe_span (K : Type) [Field K] (k : ℕ) (c : ℤ) (s : Set (Pol K k))
    (hs : ∀ f ∈ s, WtLe K k c f) : ∀ f ∈ Submodule.span K s, WtLe K k c f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm a
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact hx m h a
    · exact hy m h a
  | smul r x _ hx =>
    intro m hm a
    exact hx m (support_smul hm) a

theorem kappa_ad (hL : KappaLeft) (hR : KappaRight) (K : Type) [Field K] [CharZero K] (k d : ℕ)
    (a b : Fin k) (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :
    kappa K k d (Formalism.MainNotions.TestSideCounting.Ed K k d a b * A - A * Formalism.MainNotions.TestSideCounting.Ed K k d a b) =
      Rop K k a b (kappa K k d A) := by
  rw [map_sub, hL K k d a b A, hR K k d a b A]
  rfl

theorem divide_all (hV : Vanish) (hD : DivT) (hRB : RBihom) (hRT : RTT) (hTW : TTWt)
    (K : Type) [Field K] [CharZero K] (k c : ℕ) : ∀ n : ℕ, ∀ (W : Submodule K (Pol K k)),
    W ≤ Bihom K k (c + n) → (∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) → (∀ f ∈ W, WtLe K k c f) →
    ∀ f ∈ W, ∃ g ∈ Bihom K k c, f = tt K k ^ n * g := by
  intro n
  induction n with
  | zero =>
    intro W hW _ _ f hf
    exact ⟨f, by simpa using hW hf, by simp⟩
  | succ n ih =>
    intro W hW hst hwt f hf
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hf' : f ∈ weightedHomogeneousSubmodule K (wx 0) (c + (n + 1)) ⊓
          weightedHomogeneousSubmodule K (wxi 0) (c + (n + 1)) := hW hf
      have h1 := (Submodule.mem_inf.1 hf').1
      rw [mem_weightedHomogeneousSubmodule] at h1
      rw [mul_zero]
      ext m
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      by_contra h
      have h2 := h1 h
      have h3 : m = 0 := by
        ext v
        rcases v with i | i <;> exact i.elim0
      rw [h3, map_zero] at h2
      omega
    · have htt : tt K k ≠ 0 := by
        intro h
        have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
        simp [tt] at h1
        omega
      have hdiv : ∀ f ∈ W, ∃ g ∈ Bihom K k (c + n), f = tt K k * g := by
        intro f hf
        have hv := hV K k (c + (n + 1)) c W hW hst hwt (by omega) f hf
        obtain ⟨g, hg, rfl⟩ := hD K k (c + (n + 1)) (by omega) f (hW hf) hv
        exact ⟨g, by simpa using hg, rfl⟩
      let W' : Submodule K (Pol K k) := W.comap (LinearMap.mulLeft K (tt K k))
      have hmem : ∀ g, g ∈ W' ↔ tt K k * g ∈ W := fun g => Iff.rfl
      have hW' : W' ≤ Bihom K k (c + n) := by
        intro g hg
        obtain ⟨g', hg', he⟩ := hdiv _ ((hmem g).1 hg)
        rw [mul_left_cancel₀ htt he]
        exact hg'
      have hst' : ∀ f ∈ W', ∀ a b, Rop K k a b f ∈ W' := by
        intro g hg a b
        rw [hmem, ← hRT K k a b g]
        exact hst _ ((hmem g).1 hg) a b
      have hwt' : ∀ f ∈ W', WtLe K k c f := by
        intro g hg
        exact hTW K k c g (hwt _ ((hmem g).1 hg))
      obtain ⟨g, hg, rfl⟩ := hdiv f hf
      obtain ⟨g'', hg'', rfl⟩ := ih W' hW' hst' hwt' g ((hmem g).2 hf)
      exact ⟨g'', hg'', by ring⟩

theorem opWords_of (hI : KappaInj) (hL : KappaLeft) (hR : KappaRight) (hB : KappaBihom)
    (hE : WtOfEig) (hRB : RBihom) (hRT : RTT) (hTW : TTWt) (hD : DivT) (hV : Vanish)
    (hS : Surj) : Formalism.MainNotions.TestSideCounting.OpBound := by
  intro K _ _ k d c WW Sg hst hspan heig A hA
  have key : ∃ c' : ℕ, c' ≤ c ∧ c' ≤ d ∧ ∃ g ∈ Bihom K k c', kappa K k d A = tt K k ^ (d - c') * g := by
    rcases Nat.lt_or_ge c d with hcd | hdc
    · let W : Submodule K (Pol K k) := WW.map (kappa K k d)
      have hW : W ≤ Bihom K k (c + (d - c)) := by
        have e : c + (d - c) = d := by omega
        rw [e]
        rintro f ⟨A', _, rfl⟩
        exact hB K k d A'
      have hWst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W := by
        rintro f ⟨A', hA', rfl⟩ a b
        rw [← kappa_ad hL hR K k d a b A']
        exact Submodule.mem_map_of_mem (hst A' hA' a b)
      have hWwt : ∀ f ∈ W, WtLe K k c f := by
        have hWeq : W = Submodule.span K (kappa K k d '' Sg) := by
          show WW.map (kappa K k d) = _
          rw [hspan, Submodule.map_span]
        rw [hWeq]
        apply wtLe_span
        rintro f ⟨A', hA', rfl⟩ m hm a
        obtain ⟨ω, hω, hωc⟩ := heig A' hA'
        have h1 : Rop K k a a (kappa K k d A') = (ω a : K) • kappa K k d A' := by
          rw [← kappa_ad hL hR K k d a a A', hω a, map_smul]
        have h2 := hE K k a (ω a) (kappa K k d A') h1 m hm
        rw [h2]
        exact_mod_cast hωc a
      obtain ⟨g, hg, he⟩ := divide_all hV hD hRB hRT hTW K k c (d - c) W hW hWst hWwt _
        (Submodule.mem_map_of_mem hA)
      exact ⟨c, le_rfl, hcd.le, g, hg, he⟩
    · exact ⟨d, hdc, le_rfl, kappa K k d A, hB K k d A, by simp⟩
  obtain ⟨c', hc'c, hc'd, g, hg, he⟩ := key
  have hsurj := hS K k d c' hc'd g hg
  rw [← he] at hsurj
  obtain ⟨B, hB', hBe⟩ := Submodule.mem_map.1 hsurj
  have hAB : B = A := hI K k d hBe
  subst hAB
  have hmono : Wc K k d c' ≤ Wc K k d c := by
    unfold Wc
    apply Submodule.span_mono
    rintro Bx ⟨l, hl, rfl⟩
    exact ⟨l, le_trans hl hc'c, rfl⟩
  exact hmono hB'

end PI.OpWords
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaCoeff
section
open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

variable {K : Type} [Field K] {k d : ℕ}

lemma mapDomain_inl_add_inr (u g : Fin k →₀ ℕ) :
    u.mapDomain Sum.inl + g.mapDomain Sum.inr = Finsupp.sumElim u g := by
  ext v
  rcases v with i | i
  · simp [Finsupp.mapDomain_apply_of_injective Sum.inl_injective, Finsupp.mapDomain_notin_range]
  · simp [Finsupp.mapDomain_apply_of_injective Sum.inr_injective, Finsupp.mapDomain_notin_range]

lemma sumElim_inj {u g u' g' : Fin k →₀ ℕ} :
    Finsupp.sumElim u g = Finsupp.sumElim u' g' ↔ u = u' ∧ g = g' := by
  constructor
  · intro h
    constructor
    · ext i
      have h1 := congrArg (fun f => f (Sum.inl i)) h
      simpa using h1
    · ext i
      have h1 := congrArg (fun f => f (Sum.inr i)) h
      simpa using h1
  · rintro ⟨rfl, rfl⟩
    rfl

lemma exists_sumElim (n : Fin k ⊕ Fin k →₀ ℕ) : ∃ m g : Fin k →₀ ℕ, n = Finsupp.sumElim m g := by
  refine ⟨Finsupp.comapDomain Sum.inl n Sum.inl_injective.injOn,
    Finsupp.comapDomain Sum.inr n Sum.inr_injective.injOn, ?_⟩
  ext v
  rcases v with i | i <;> simp [Finsupp.comapDomain_apply]

lemma pol_ext {P Q : Pol K k}
    (h : ∀ m g : Fin k →₀ ℕ, AddMonoidAlgebra.coeff P (Finsupp.sumElim m g) = AddMonoidAlgebra.coeff Q (Finsupp.sumElim m g)) : P = Q := by
  ext n
  obtain ⟨m, g, rfl⟩ := exists_sumElim n
  exact h m g

lemma sumElim_sub_single_inr (m g : Fin k →₀ ℕ) (b : Fin k) :
    Finsupp.sumElim m g - single (Sum.inr b) 1 = Finsupp.sumElim m (g - single b 1) := by
  ext v
  rcases v with i | i <;> simp [Finsupp.single_apply]

lemma sumElim_add_single_inr (m g : Fin k →₀ ℕ) (b : Fin k) :
    Finsupp.sumElim m g + single (Sum.inr b) 1 = Finsupp.sumElim m (g + single b 1) := by
  ext v
  rcases v with i | i <;> simp [Finsupp.single_apply]

lemma coeff_term (P : MvPolynomial (Fin k) K) (m g g' : Fin k →₀ ℕ) :
    AddMonoidAlgebra.coeff (rename Sum.inl P * monomial (g'.mapDomain Sum.inr) (1 : K)) (Finsupp.sumElim m g) =
      if g' = g then AddMonoidAlgebra.coeff P m else 0 := by
  classical
  induction P using MvPolynomial.induction_on'
  next u c =>
    rw [rename_monomial, monomial_mul, mapDomain_inl_add_inr]
    simp only [coeff_monomial, sumElim_inj, mul_one]
    by_cases h1 : u = m <;> by_cases h2 : g' = g <;> simp [h1, h2]
  next p q hp hq =>
    rw [map_add (f := _), add_mul, MvPolynomial.coeff_add, hp, hq]
    split_ifs <;> simp [MvPolynomial.coeff_add]

lemma mono_val (g : Fin k →₀ ℕ) :
    (mono K k d g : MvPolynomial (Fin k) K) = if g.degree = d then monomial g 1 else 0 := by
  unfold mono
  split_ifs <;> rfl

lemma mem_antidiag_iff (g : Fin k →₀ ℕ) :
    g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d ↔ g.degree = d := by
  rw [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  simp

lemma kappa_apply (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :
    kappa K k d A = ∑ g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d,
      invFact K g • (rename Sum.inl ((A (mono K k d g) : MvPolynomial (Fin k) K)) *
        monomial (g.mapDomain Sum.inr) (1 : K)) := by
  simp [kappa]

lemma coeff_kappa (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) (m g : Fin k →₀ ℕ) :
    AddMonoidAlgebra.coeff (kappa K k d A) (Finsupp.sumElim m g) =
      invFact K g * AddMonoidAlgebra.coeff (A (mono K k d g) : MvPolynomial (Fin k) K) m := by
  classical
  rw [kappa_apply, coeff_sum]
  simp only [coeff_smul, coeff_term, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [mem_antidiag_iff] at h
    have h0 : mono K k d g = 0 := by
      unfold mono
      rw [dite_eq_right h]
    rw [h0, map_zero]
    simp

lemma degree_of_coeff_ne (F : ↥(homogeneousSubmodule (Fin k) K d)) {m : Fin k →₀ ℕ}
    (h : AddMonoidAlgebra.coeff (F : MvPolynomial (Fin k) K) m ≠ 0) : m.degree = d := by
  have hF := (mem_homogeneousSubmodule d _).1 F.2
  rw [Finsupp.degree_eq_weight_one]
  exact hF h

lemma eq_sum_mono (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    F = ∑ g ∈ (F : MvPolynomial (Fin k) K).support,
      AddMonoidAlgebra.coeff (F : MvPolynomial (Fin k) K) g • mono K k d g := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  conv_lhs => rw [(F : MvPolynomial (Fin k) K).as_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [Submodule.coe_smul, mono_val, if_pos (degree_of_coeff_ne F (MvPolynomial.mem_support_iff.1 hg)),
    smul_monomial, smul_eq_mul, mul_one]

lemma prodFact_fintype (g : Fin k →₀ ℕ) :
    g.prod (fun _ n => (n.factorial : K)) = ∏ i, ((g i).factorial : K) := by
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)

lemma prodFact_ne_zero [CharZero K] (g : Fin k →₀ ℕ) :
    g.prod (fun _ n => (n.factorial : K)) ≠ 0 := by
  rw [prodFact_fintype]
  exact Finset.prod_ne_zero_iff.2 (fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))

lemma invFact_ne_zero [CharZero K] (g : Fin k →₀ ℕ) : invFact K g ≠ 0 := by
  unfold invFact
  exact inv_ne_zero (prodFact_ne_zero g)

lemma prodFact_add_single (g : Fin k →₀ ℕ) (i : Fin k) :
    (g + single i 1).prod (fun _ n => (n.factorial : K)) =
      ((g i : K) + 1) * g.prod (fun _ n => (n.factorial : K)) := by
  rw [prodFact_fintype, prodFact_fintype, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h1 : ∏ j ∈ Finset.univ.erase i, (((g + single i 1 : Fin k →₀ ℕ) j).factorial : K) =
      ∏ j ∈ Finset.univ.erase i, ((g j).factorial : K) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    simp [Finsupp.single_apply, Finset.ne_of_mem_erase hj, Ne.symm (Finset.ne_of_mem_erase hj)]
  rw [h1, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

lemma invFact_add_single [CharZero K] (g : Fin k →₀ ℕ) (i : Fin k) :
    invFact K (g + single i 1) * ((g i : K) + 1) = invFact K g := by
  unfold invFact
  rw [prodFact_add_single, mul_inv]
  have h1 : ((g i : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (g i)
  rw [mul_comm ((g i : K) + 1)⁻¹ _, mul_assoc, inv_mul_cancel₀ h1, mul_one]

lemma degree_sub_add (g : Fin k →₀ ℕ) (a b : Fin k) (hb : g b ≠ 0) :
    (g - single b 1 + single a 1).degree = g.degree := by
  have hle : single b 1 ≤ g := by
    rw [Finsupp.single_le_iff]
    omega
  have hs : ∀ c : Fin k, (single c 1 : Fin k →₀ ℕ).degree = 1 := fun c => by
    rw [Finsupp.degree_eq_sum]
    simp [Finsupp.single_apply]
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add (f := _), map_add (f := _), hs, hs]

lemma Ed_val (a b : Fin k) (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    (Formalism.MainNotions.TestSideCounting.Ed K k d a b F : MvPolynomial (Fin k) K) = X a * pderiv b (F : MvPolynomial (Fin k) K) :=
  rfl

lemma Ed_mono (a b : Fin k) (g : Fin k →₀ ℕ) :
    Formalism.MainNotions.TestSideCounting.Ed K k d a b (mono K k d g) =
      ((g b : ℕ) : K) • mono K k d (g - single b 1 + single a 1) := by
  apply Subtype.ext
  rw [Ed_val, Submodule.coe_smul, mono_val, mono_val]
  by_cases hb : g b = 0
  · split_ifs <;> simp [pderiv_monomial, hb]
  · rw [degree_sub_add g a b hb]
    split_ifs with h
    · rw [pderiv_monomial, X, monomial_mul, smul_monomial, add_comm (Finsupp.single a 1)]
      simp
    · simp

lemma pderiv_inl_xi (b : Fin k) (g : Fin k →₀ ℕ) :
    pderiv (Sum.inl b) (monomial (g.mapDomain Sum.inr) (1 : K) : Pol K k) = 0 := by
  simp [pderiv_monomial, Finsupp.mapDomain_notin_range]

lemma weight_wx (m g : Fin k →₀ ℕ) : Finsupp.weight (wx k) (Finsupp.sumElim m g) = m.degree := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wx, Fintype.sum_sum_type, Finsupp.degree_eq_sum]

lemma weight_wxi (m g : Fin k →₀ ℕ) : Finsupp.weight (wxi k) (Finsupp.sumElim m g) = g.degree := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wxi, Fintype.sum_sum_type, Finsupp.degree_eq_sum]

end PI.OpWords
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.VanishExp
section
open MvPolynomial

noncomputable section

namespace PI.OpWords

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

def shiftPt (a b : Fin k) (s : K) (p : Fin k ⊕ Fin k → K) : Fin k ⊕ Fin k → K :=
  fun i => p i + s * eval p (Rop K k a b (X i))

lemma rop_apply (a b : Fin k) (f : Pol K k) :
    Rop K k a b f = X (Sum.inl a) * pderiv (Sum.inl b) f - X (Sum.inr b) * pderiv (Sum.inr a) f := rfl

lemma rop_C (a b : Fin k) (r : K) : Rop K k a b (C r) = 0 := by
  simp [rop_apply]

lemma rop_mul (a b : Fin k) (f g : Pol K k) :
    Rop K k a b (f * g) = Rop K k a b f * g + f * Rop K k a b g := by
  rw [rop_apply, rop_apply, rop_apply]
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

lemma rop_rop_X (a b : Fin k) (hab : a ≠ b) (i : Fin k ⊕ Fin k) :
    Rop K k a b (Rop K k a b (X i)) = 0 := by
  rcases i with j | j
  · by_cases h : j = b
    · subst h
      simp [rop_apply, pderiv_X, Pi.single_apply, hab, Ne.symm hab]
    · simp [rop_apply, pderiv_X, Pi.single_apply, h, Ne.symm h]
  · by_cases h : j = a
    · subst h
      simp [rop_apply, pderiv_X, Pi.single_apply, hab, Ne.symm hab]
    · simp [rop_apply, pderiv_X, Pi.single_apply, h, Ne.symm h]

lemma rop_iter_mul_X (a b : Fin k) (hab : a ≠ b) (g : Pol K k) (i : Fin k ⊕ Fin k) (n : ℕ) :
    (Rop K k a b)^[n + 1] (g * X i) = (Rop K k a b)^[n + 1] g * X i
      + (n + 1) • ((Rop K k a b)^[n] g * Rop K k a b (X i)) := by
  induction n with
  | zero => simp [rop_mul]
  | succ n ih =>
    have e1 : (Rop K k a b)^[n + 1 + 1] (g * X i) = Rop K k a b ((Rop K k a b)^[n + 1] (g * X i)) :=
      Function.iterate_succ_apply' _ _ _
    have e2 : (Rop K k a b)^[n + 1 + 1] g = Rop K k a b ((Rop K k a b)^[n + 1] g) :=
      Function.iterate_succ_apply' _ _ _
    have e3 : (Rop K k a b)^[n + 1] g = Rop K k a b ((Rop K k a b)^[n] g) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, ih, map_add (f := _), map_nsmul, rop_mul, rop_mul, rop_rop_X a b hab i, e2, ← e3]
    rw [mul_zero, add_zero, succ_nsmul _ (n + 1)]
    abel

def ExpFormula (a b : Fin k) (s : K) (g : Pol K k) : Prop :=
  ∃ N : ℕ, (∀ n, N < n → (Rop K k a b)^[n] g = 0) ∧
    ∀ M, N ≤ M → ∀ p : Fin k ⊕ Fin k → K,
      eval (shiftPt a b s p) g =
        ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval p ((Rop K k a b)^[n] g)

theorem expFormula (a b : Fin k) (hab : a ≠ b) (s : K) (g : Pol K k) : ExpFormula a b s g := by
  unfold ExpFormula
  induction g using MvPolynomial.induction_on
  next r =>
    have hz : ∀ n, (Rop K k a b)^[n + 1] (C r) = 0 := by
      intro n
      rw [Function.iterate_succ_apply, rop_C]
      exact Function.iterate_fixed (map_zero _) n
    refine ⟨0, fun n hn => ?_, fun M _ x => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact hz m
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro n _ hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hz m]
        simp
      · intro h
        simp at h
  next p q hp hq =>
    obtain ⟨N1, hz1, hs1⟩ := hp
    obtain ⟨N2, hz2, hs2⟩ := hq
    refine ⟨max N1 N2, fun n hn => ?_, fun M hM x => ?_⟩
    · rw [← Module.End.coe_pow, map_add (f := _), Module.End.coe_pow, hz1 n (by omega), hz2 n (by omega), add_zero]
    · rw [map_add (f := _), hs1 M (by omega) x, hs2 M (by omega) x, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Module.End.coe_pow, map_add (f := _), map_add (f := _)]
      ring
  next p i hp =>
    obtain ⟨N, hz, hsum⟩ := hp
    refine ⟨N + 1, fun n hn => ?_, fun M hM x => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [rop_iter_mul_X a b hab p i m, hz (m + 1) (by omega), hz m (by omega)]
      simp
    · have hterm : ∀ m : ℕ, eval x ((Rop K k a b)^[m + 1] (p * X i)) =
          eval x ((Rop K k a b)^[m + 1] p) * x i +
            ((m : K) + 1) * (eval x ((Rop K k a b)^[m] p) * eval x (Rop K k a b (X i))) := by
        intro m
        rw [rop_iter_mul_X a b hab p i m, map_add (f := _), eval_mul, eval_X, map_nsmul, eval_mul, nsmul_eq_mul]
        push_cast
        ring
      have hTM : s ^ M / (M.factorial : K) * eval x ((Rop K k a b)^[M] p) = 0 := by
        rw [hz M (by omega), map_zero, mul_zero]
      have hfac : ∀ m : ℕ, s ^ (m + 1) / ((m + 1).factorial : K) * ((m : K) + 1) =
          s * (s ^ m / (m.factorial : K)) := by
        intro m
        have h1 : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        have h2 : (m.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        rw [Nat.factorial_succ, Nat.cast_mul]
        push_cast
        (try field_simp)
        (try ring)
      have hR : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] (p * X i)) =
          ∑ m ∈ Finset.range M, (s ^ (m + 1) / ((m + 1).factorial : K) * eval x ((Rop K k a b)^[m + 1] p) * x i +
            s * eval x (Rop K k a b (X i)) * (s ^ m / (m.factorial : K) * eval x ((Rop K k a b)^[m] p))) +
          s ^ 0 / ((0 : ℕ).factorial : K) * eval x ((Rop K k a b)^[0] p) * x i := by
        rw [Finset.sum_range_succ']
        congr 1
        · refine Finset.sum_congr rfl fun m _ => ?_
          simp only [hterm]
          linear_combination (eval x ((Rop K k a b)^[m] p) * eval x (Rop K k a b (X i))) * hfac m
        · simp
      have hS1 : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] p) =
          ∑ m ∈ Finset.range M, s ^ (m + 1) / ((m + 1).factorial : K) * eval x ((Rop K k a b)^[m + 1] p) +
          s ^ 0 / ((0 : ℕ).factorial : K) * eval x ((Rop K k a b)^[0] p) := Finset.sum_range_succ' _ _
      have hS2 : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] p) =
          ∑ m ∈ Finset.range M, s ^ m / (m.factorial : K) * eval x ((Rop K k a b)^[m] p) := by
        rw [Finset.sum_range_succ, hTM, add_zero]
      have hxi : shiftPt a b s x i = x i + s * eval x (Rop K k a b (X i)) := rfl
      rw [hR, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← hS2, eval_mul, eval_X,
        hsum M (by omega) x, hxi, hS1]
      ring

end PI.OpWords
end
end

