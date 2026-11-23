module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResidueMultisetEqOfShiftedSeriesEq
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.AlcMult


open Polynomial in
noncomputable def linProd {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) : k[X] :=
  ∏ i, (1 - Polynomial.C (a i) * Polynomial.X)

open Polynomial in
theorem linProd_ne_zero {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) :
    linProd a ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp [linProd, Polynomial.eval_prod] at this

open Polynomial in
theorem count_roots_factor {k : Type} [Field k] [DecidableEq k] (c y : k) (hy : y ≠ 0) :
    Multiset.count y⁻¹ (1 - Polynomial.C c * Polynomial.X).roots = if c = y then 1 else 0 := by
  by_cases hc : c = 0
  · subst hc
    have : (0 : k) ≠ y := fun h => hy h.symm
    simp [this]
  · have e : (1 - Polynomial.C c * Polynomial.X) = Polynomial.C (-c) * (Polynomial.X - Polynomial.C c⁻¹) := by
      rw [mul_sub, ← Polynomial.C_mul]
      simp [hc]
      ring
    rw [e, Polynomial.roots_C_mul _ (neg_ne_zero.mpr hc), Polynomial.roots_X_sub_C,
      Multiset.count_singleton]
    by_cases h : c = y
    · simp [h]
    · have : y⁻¹ ≠ c⁻¹ := fun h' => h (inv_injective h').symm
      simp [h, this]

open Polynomial in
theorem count_roots_linProd {k : Type} [Field k] [DecidableEq k] {ι : Type} [Fintype ι] (a : ι → k) (y : k)
    (hy : y ≠ 0) :
    Multiset.count y⁻¹ (linProd a).roots = (Finset.univ.filter fun i => a i = y).card := by
  classical
  have h := linProd_ne_zero a
  unfold linProd at h ⊢
  rw [Polynomial.roots_prod _ _ h, Multiset.count_bind]
  simp only [count_roots_factor _ _ hy]
  rw [Finset.card_filter]
  rfl

theorem coe_linProd {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) :
    ((linProd a : Polynomial k) : PowerSeries k) = ∏ i, (1 - PowerSeries.C (a i) * PowerSeries.X) := by
  rw [linProd, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp

end GlobalTheory.AlcMult

namespace GlobalTheory.AlcMult

theorem zmod_const_of_step (p : ℕ) [Fact p.Prime] (m m' : ZMod p → ℕ)
    (h : ∀ y : ZMod p, y + 1 ≠ 0 → m y + m' (y + 1) = m' y + m (y + 1))
    (hs : ∑ x, m x = ∑ x, m' x) : ∀ x, m x = m' x := by
  set d : ZMod p → ℤ := fun x => (m x : ℤ) - m' x with hd
  have step : ∀ y : ZMod p, y + 1 ≠ 0 → d (y + 1) = d y := by
    intro y hy
    have := h y hy
    simp only [hd]
    omega
  have hp := (Fact.out : p.Prime)
  have hn : ∀ n : ℕ, n < p → d (n : ZMod p) = d 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hlt
      have hne : ((n : ZMod p) + 1) ≠ 0 := by
        intro h0
        have : ((n + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact h0
        rw [ZMod.natCast_eq_zero_iff] at this
        exact absurd (Nat.le_of_dvd (Nat.succ_pos n) this) (by omega)
      push_cast
      rw [step _ hne, ih (by omega)]
  have hc : ∀ x, d x = d 0 := by
    intro x
    have := hn x.val (ZMod.val_lt x)
    rwa [ZMod.natCast_zmod_val] at this
  have hsum : ∑ x, d x = 0 := by
    simp only [hd, Finset.sum_sub_distrib]
    have hs' : (∑ x, (m x : ℤ)) = ∑ x, (m' x : ℤ) := by exact_mod_cast hs
    rw [hs', sub_self]
  rw [Finset.sum_congr rfl (fun x _ => hc x), Finset.sum_const, Finset.card_univ, ZMod.card] at hsum
  have h0 : d 0 = 0 := by
    rcases smul_eq_zero.mp hsum with h | h
    · exact absurd h hp.ne_zero
    · exact h
  intro x
  have := hc x
  rw [h0] at this
  simp only [hd] at this
  omega

end GlobalTheory.AlcMult

namespace GlobalTheory.AlcMult

theorem card_cast_eq {p : ℕ} {k : Type} [Field k] [CharP k p] [DecidableEq k] {N : ℕ}
    (l : Fin N → ℕ) (z : ZMod p) :
    (Finset.univ.filter fun i => (l i : k) = ZMod.castHom (dvd_refl p) k z).card =
      (Finset.univ.filter fun i => (l i : ZMod p) = z).card := by
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [← map_natCast (ZMod.castHom (dvd_refl p) k) (l i)]
  exact (ZMod.castHom_injective k).eq_iff

theorem card_cast_succ_eq {p : ℕ} {k : Type} [Field k] [CharP k p] [DecidableEq k] {N : ℕ}
    (l : Fin N → ℕ) (z : ZMod p) :
    (Finset.univ.filter fun i => (l i : k) + 1 = ZMod.castHom (dvd_refl p) k z).card =
      (Finset.univ.filter fun i => (l i : ZMod p) = z - 1).card := by
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [← map_natCast (ZMod.castHom (dvd_refl p) k) (l i), ← map_one (ZMod.castHom (dvd_refl p) k),
    ← map_add, (ZMod.castHom_injective k).eq_iff, eq_sub_iff_add_eq]

theorem sum_card_fiber {p : ℕ} [NeZero p] {N : ℕ} (l : Fin N → ℕ) :
    ∑ x : ZMod p, (Finset.univ.filter fun i => (l i : ZMod p) = x).card = N := by
  classical
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun i => (l i : ZMod p)) (s := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  simp

end GlobalTheory.AlcMult

open GlobalTheory.AlcMult in
theorem GlobalTheory.Alc.multiset_eq_of_series_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (l l' : Fin N → ℕ), (∏ i, (1 - PowerSeries.C ((l i : k) + 1) * PowerSeries.X)) * ∏ i, (1 - PowerSeries.C (l' i : k) * PowerSeries.X) = (∏ i, (1 - PowerSeries.C ((l' i : k) + 1) * PowerSeries.X)) * ∏ i, (1 - PowerSeries.C (l i : k) * PowerSeries.X) → ∀ x : ZMod p, (Finset.univ.filter fun i => (l i : ZMod p) = x).card = (Finset.univ.filter fun i => (l' i : ZMod p) = x).card := by
  intro p hp k _ _ N l l' H
  haveI : Fact p.Prime := ⟨hp⟩
  letI : DecidableEq k := Classical.decEq k
  have HP : linProd (fun i => (l i : k) + 1) * linProd (fun i => (l' i : k)) =
      linProd (fun i => (l' i : k) + 1) * linProd (fun i => (l i : k)) := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_mul, Polynomial.coe_mul, coe_linProd, coe_linProd, coe_linProd, coe_linProd]
    exact H
  have hcount : ∀ y : k, y ≠ 0 →
      (Finset.univ.filter fun i => (l i : k) + 1 = y).card +
        (Finset.univ.filter fun i => (l' i : k) = y).card =
      (Finset.univ.filter fun i => (l' i : k) + 1 = y).card +
        (Finset.univ.filter fun i => (l i : k) = y).card := by
    intro y hy
    have e := congrArg (fun q => Multiset.count y⁻¹ q.roots) HP
    rw [Polynomial.roots_mul (mul_ne_zero (linProd_ne_zero _) (linProd_ne_zero _)),
      Polynomial.roots_mul (mul_ne_zero (linProd_ne_zero _) (linProd_ne_zero _)),
      Multiset.count_add, Multiset.count_add, count_roots_linProd _ _ hy, count_roots_linProd _ _ hy,
      count_roots_linProd _ _ hy, count_roots_linProd _ _ hy] at e
    exact e
  apply zmod_const_of_step p
  · intro y hy
    have hne : ZMod.castHom (dvd_refl p) k (y + 1) ≠ 0 := by
      rw [← map_zero (ZMod.castHom (dvd_refl p) k)]
      exact fun h => hy ((ZMod.castHom_injective k) h)
    have := hcount _ hne
    rw [card_cast_succ_eq, card_cast_succ_eq, card_cast_eq, card_cast_eq, add_sub_cancel_right] at this
    exact this
  · rw [sum_card_fiber, sum_card_fiber]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeight
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem rowE_apply_eq_sum (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b f = ∑ s : Fin n, X (a, s) * pderiv (b, s) f := by
  simp [rowE, LinearMap.sum_apply]

theorem weight_rowW_eq_sum {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) d a = ∑ s : Fin n, d (a, s) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

theorem weight_rowW_single {r n : ℕ} (v : Fin r × Fin n) :
    Finsupp.weight (rowW r n) (Finsupp.single v 1) = Pi.single v.1 1 := by
  simp [Finsupp.weight_apply, rowW]

theorem X_mul_monomial_pderiv_term {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (s : Fin n)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    X (a, s) * pderiv (b, s) (monomial d c) =
      monomial (Finsupp.single (a, s) 1 + (d - Finsupp.single (b, s) 1)) (c * (d (b, s) : R)) := by
  rw [pderiv_monomial, X, monomial_mul, one_mul]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem rowE_diag_monomial {R : Type} [CommRing R] {r n : ℕ} (a : Fin r) (μ : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ) :
    rowE R r n a a (monomial d c) = (μ a : R) • monomial d c := by
  rw [rowE_apply_eq_sum]
  have hterm : ∀ s : Fin n, X (a, s) * pderiv (a, s) (monomial d c) = monomial d (c * (d (a, s) : R)) := by
    intro s
    rw [X_mul_monomial_pderiv_term]
    by_cases h : d (a, s) = 0
    · simp [h]
    · rw [add_comm, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))]
  simp_rw [hterm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← Finset.mul_sum, smul_monomial, smul_eq_mul, mul_comm]
  congr 2
  rw [← hd, weight_rowW_eq_sum]
  push_cast
  rfl

theorem rowE_monomial_eq_zero {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (μ : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ) (hb : μ b = 0) :
    rowE R r n a b (monomial d c) = 0 := by
  rw [rowE_apply_eq_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have h0 : d (b, s) = 0 := by
    have h1 : ∑ t : Fin n, d (b, t) = 0 := by rw [← weight_rowW_eq_sum, hd, hb]
    exact (Finset.sum_eq_zero_iff.mp h1) s (Finset.mem_univ _)
  rw [X_mul_monomial_pderiv_term, h0]
  simp

theorem rowE_monomial_weight {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (μ μ' : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ)
    (hμ : μ' + Pi.single b 1 = μ + Pi.single a 1) :
    IsWeightedHomogeneous (rowW r n) (rowE R r n a b (monomial d c)) μ' := by
  rw [rowE_apply_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s _ => ?_
  rw [X_mul_monomial_pderiv_term]
  by_cases h : d (b, s) = 0
  · rw [h]; simp only [Nat.cast_zero, mul_zero, map_zero]
    exact isWeightedHomogeneous_zero R _ _
  · refine isWeightedHomogeneous_monomial _ _ _ ?_
    have hle : Finsupp.single (b, s) 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h)
    have hsplit : Finsupp.weight (rowW r n) (d - Finsupp.single (b, s) 1) + Pi.single b 1 = μ := by
      rw [← weight_rowW_single (b, s), ← map_add (f := _), tsub_add_cancel_of_le hle, hd]
    rw [map_add (f := _), weight_rowW_single]
    apply add_right_cancel (b := Pi.single b 1)
    rw [hμ, ← hsplit]
    simp only
    abel

theorem rowE_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin n) R),
    IsWeightedHomogeneous (rowW r n) f μ → (∀ a, rowE R r n a a f = (μ a : R) • f) ∧
      ∀ a b, a ≠ b → (μ b = 0 → rowE R r n a b f = 0) ∧
        ∀ μ' : Fin r → ℕ, μ' + Pi.single b 1 = μ + Pi.single a 1 →
          IsWeightedHomogeneous (rowW r n) (rowE R r n a b f) μ' := by
  intro R _ r n μ f hf
  have hmon : ∀ d ∈ f.support, Finsupp.weight (rowW r n) d = μ := fun d hd => hf (mem_support_iff.mp hd)
  refine ⟨fun a => ?_, fun a b _ => ⟨fun hb => ?_, fun μ' hμ => ?_⟩⟩
  · conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun d hd => rowE_diag_monomial a μ d _ (hmon d hd)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [f.as_sum, map_sum]
    exact Finset.sum_eq_zero fun d hd => rowE_monomial_eq_zero a b μ d _ (hmon d hd) hb
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [f.as_sum, map_sum]
    exact IsWeightedHomogeneous.sum _ _ _ fun d hd => rowE_monomial_weight a b μ μ' d _ (hmon d hd) hμ

end GlobalTheory.Alc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChang
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rowE_apply (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b P = ∑ s : Fin n, X (a, s) * pderiv (b, s) P := by
  simp [rowE, LinearMap.sum_apply]

theorem rowE_X (R : Type) [CommRing R] (r n : ℕ) (a b c : Fin r) (t : Fin n) :
    rowE R r n a b (X (c, t)) = if b = c then X (a, t) else 0 := by
  rw [rowE_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single t]
    · simp
    · intro s _ hs
      rw [pderiv_X_of_ne (by simp [Ne.symm hs])]; simp
    · simp
  · refine Finset.sum_eq_zero fun s _ => ?_
    rw [pderiv_X_of_ne (by simp [Ne.symm h])]; simp

theorem rowE_mul (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P Q : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b (P * Q) = rowE R r n a b P * Q + P * rowE R r n a b Q := by
  simp only [rowE_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Derivation.leibniz, smul_eq_mul]; ring

theorem rowE_C (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (x : R) :
    rowE R r n a b (C x) = 0 := by
  simp [rowE_apply]

theorem glRel_rowE (R : Type) [CommRing R] (r n : ℕ) : GlRel (rowE R r n) := by
  intro a b c d
  refine LinearMap.ext fun P => ?_
  induction P using MvPolynomial.induction_on with
  | C x => split_ifs <;> simp [rowE_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    obtain ⟨e, t⟩ := v
    have hX : (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) (X (e, t)) =
        ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) (X (e, t)) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, rowE_X]
      split_ifs <;> simp_all [rowE_X]
    have hL : ∀ P Q, (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) (P * Q) =
        (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) P * Q +
          P * (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) Q := by
      intro P Q
      simp only [LinearMap.sub_apply, Module.End.mul_apply, rowE_mul, map_add (f := _)]; ring
    have hR : ∀ P Q, ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) (P * Q) =
        ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) P * Q +
          P * ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) Q := by
      intro P Q
      split_ifs <;> simp [rowE_mul] <;> ring
    rw [hL, hR, hp, hX]

theorem rowE_eq_rowDiv (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b P = rowDiv R a b 1 P ∧ rowDiv R a b 0 P = P := by
  induction P using MvPolynomial.induction_on with
  | C x => simp [rowE_C, rowDiv, rowGen, Polynomial.algebraMap_apply, Polynomial.coeff_C]
  | add p q hp hq =>
    simp only [rowDiv, map_add (f := _), Polynomial.coeff_add] at *
    exact ⟨by rw [hp.1, hq.1], by rw [hp.2, hq.2]⟩
  | mul_X p v hp =>
    obtain ⟨e, t⟩ := v
    simp only [rowDiv, map_mul] at *
    have h0 : (rowGen R a b (X (e, t) : MvPolynomial (Fin r × Fin n) R)).coeff 0 = X (e, t) := by
      simp only [rowGen, aeval_X]; split_ifs <;> simp
    have h1 : (rowGen R a b (X (e, t) : MvPolynomial (Fin r × Fin n) R)).coeff 1 =
        if b = e then X (a, t) else 0 := by
      simp only [rowGen, aeval_X]
      by_cases h : e = b
      · simp [h, Polynomial.coeff_C]
      · simp [h, Ne.symm h, Polynomial.coeff_C]
    refine ⟨?_, by rw [Polynomial.mul_coeff_zero, hp.2, h0]⟩
    rw [rowE_mul, rowE_X, Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [hp.1, hp.2, h0, h1, add_comm]

theorem map_rowE {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n : ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (rowE R r n a b f) = rowE S r n a b (map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rowE_apply, map_sum, map_mul, map_X, pderiv_map]

theorem map_rowE_pow {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n k : ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ ((rowE R r n ^ k) a b f) = (rowE S r n ^ k) a b (map φ f) := by
  induction k generalizing a b f with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pow_succ, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, map_sum, ih, map_rowE]

theorem map_gel {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (gel R r n k f) = gel S r n k (map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gel, Matrix.trace, Matrix.diag, LinearMap.sum_apply, map_sum, map_rowE_pow]

theorem rowOperators_main : ∀ (R : Type) [CommRing R] (r n : ℕ), GlRel (rowE R r n) ∧
    (∀ a b f, rowE R r n a b f = rowDiv R a b 1 f) ∧
    ∀ (S : Type) [CommRing S] (φ : R →+* S) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R),
      map φ (gel R r n k f) = gel S r n k (map φ f) := by
  intro R _ r n
  exact ⟨glRel_rowE R r n, fun a b f => (rowE_eq_rowDiv R r n a b f).1,
    fun S _ φ k f => map_gel φ r n k f⟩

end GlobalTheory.Alc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceEPowerHighestWeightValueGeneratingSeries
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem hcRow_succ (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) (i : Fin N) (k : ℕ) :
    ∑ l, (hcMat R μ ^ (k+1)) i l =
      shift R μ i * ∑ l, (hcMat R μ ^ k) i l - ∑ j ∈ Finset.univ.filter (fun j => i < j), ∑ l, (hcMat R μ ^ k) j l := by
  rw [pow_succ']
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hpt : ∀ j : Fin N, hcMat R μ i j * ∑ l, (hcMat R μ ^ k) j l =
      (if j = i then shift R μ i * ∑ l, (hcMat R μ ^ k) j l else 0) +
      (if i < j then -∑ l, (hcMat R μ ^ k) j l else 0) := by
    intro j
    simp only [hcMat, Matrix.of_apply]
    by_cases h1 : j = i
    · subst h1; simp
    · by_cases h2 : i < j
      · simp [h1, h2]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_ite_eq' , ← Finset.sum_filter,
    Finset.sum_neg_distrib]
  simp [sub_eq_add_neg]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

def hcRowSeries (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) : PowerSeries R :=
  PowerSeries.mk fun k => ∑ l, (hcMat R μ ^ k) i l

theorem hcRowSeries_eq (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) (i : Fin N) :
    (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) * hcRowSeries R μ i =
      1 - PowerSeries.X * ∑ j ∈ Finset.univ.filter (fun j => i < j), hcRowSeries R μ j := by
  ext n
  cases n with
  | zero => simp [hcRowSeries, sub_mul, mul_assoc, Matrix.one_apply]
  | succ k =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hcRowSeries, sub_mul, mul_assoc, PowerSeries.coeff_succ_X_mul, map_sum, hcRow_succ]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem hcTelescope (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) :
    ∀ d, d ≤ N →
      (1 - PowerSeries.X * ∑ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), hcRowSeries R μ j) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j) * PowerSeries.X) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j + 1) * PowerSeries.X) := by
  intro d
  induction d with
  | zero =>
    intro _
    have : Finset.univ.filter (fun j : Fin N => N - 0 ≤ j.val) = ∅ := by
      ext j; simp
    rw [this]; simp
  | succ d ih =>
    intro hd
    set i : Fin N := ⟨N - d - 1, by omega⟩ with hi
    have hS : Finset.univ.filter (fun j : Fin N => N - (d+1) ≤ j.val) =
        insert i (Finset.univ.filter (fun j : Fin N => N - d ≤ j.val)) := by
      ext j; simp [hi, Fin.ext_iff]; omega
    have hnot : i ∉ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val) := by
      simp [hi]; omega
    have hgt : Finset.univ.filter (fun j : Fin N => i < j) = Finset.univ.filter (fun j : Fin N => N - d ≤ j.val) := by
      ext j; simp [hi, Fin.lt_iff_val_lt_val]; omega
    have h := hcRowSeries_eq R N μ i
    rw [hgt] at h
    have IH := ih (by omega)
    rw [hS, Finset.sum_insert hnot, Finset.prod_insert hnot, Finset.prod_insert hnot]
    rw [map_add (f := _), map_one]
    linear_combination (1 - PowerSeries.C (shift R μ i) * PowerSeries.X - PowerSeries.X) * IH
      - PowerSeries.X * (∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j) * PowerSeries.X)) * h

theorem hcVal_generating (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) :
    (1 - PowerSeries.X * PowerSeries.mk (hcVal R μ)) * ∏ i, (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) =
      ∏ i, (1 - PowerSeries.C (shift R μ i + 1) * PowerSeries.X) := by
  have h := hcTelescope R N μ N le_rfl
  have hU : Finset.univ.filter (fun j : Fin N => N - N ≤ j.val) = Finset.univ := by
    ext j; simp
  have hmk : PowerSeries.mk (hcVal R μ) = ∑ j, hcRowSeries R μ j := by
    ext n; simp [hcVal, hcRowSeries, map_sum]
  rw [hU] at h
  rw [hmk]
  exact h

end GlobalTheory.Alc
end

