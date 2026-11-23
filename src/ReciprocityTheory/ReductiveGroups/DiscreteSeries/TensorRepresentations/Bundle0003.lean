module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARKinv
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem carKinv_triple₁ {R : Type*} [Ring R] (A B C δ : R) (h1 : C * A + A * C = 0)
    (h2 : B * C + C * B = δ) : A * B * C - C * (A * B) = A * δ := by
  calc A * B * C - C * (A * B) = A * (B * C + C * B) - (C * A + A * C) * B := by noncomm_ring
    _ = A * δ := by rw [h1, h2]; noncomm_ring

theorem carKinv_triple₂ {R : Type*} [Ring R] (A B C δ : R) (h1 : C * A + A * C = δ)
    (h2 : B * C + C * B = 0) : A * B * C - C * (A * B) = -(δ * B) := by
  calc A * B * C - C * (A * B) = A * (B * C + C * B) - (C * A + A * C) * B := by noncomm_ring
    _ = -(δ * B) := by rw [h1, h2]; noncomm_ring

theorem carKinv_sum_mul_comm {R ι κ : Type*} [Ring R] (s : Finset ι) (t : Finset κ)
    (f : ι → κ → R) (X : R) (h : ∑ i ∈ s, ∑ c ∈ t, (f i c * X - X * f i c) = 0) :
    (∑ i ∈ s, ∑ c ∈ t, f i c) * X = X * ∑ i ∈ s, ∑ c ∈ t, f i c := by
  rw [← sub_eq_zero, ← h, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem carKinv_expand {R : Type*} [Ring R] (P Q A S : R) (hQA : Q * A = A * Q)
    (hPS : P * S = S * P) :
    P * Q * (A + S) - (A + S) * (P * Q) = (P * A - A * P) * Q - P * (S * Q - Q * S) := by
  calc P * Q * (A + S) - (A + S) * (P * Q)
      = (P * A - A * P) * Q - P * (S * Q - Q * S) + P * (Q * A - A * Q) + (P * S - S * P) * Q := by
        noncomm_ring
    _ = (P * A - A * P) * Q - P * (S * Q - Q * S) := by
        rw [hQA, hPS, sub_self, sub_self, mul_zero, zero_mul, add_zero, add_zero]

theorem carKinv_E_sgE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (a b c d : Fin n) : E c d * sgE ε cp cm a b = sgE ε cp cm a b * E c d := by
  have key : ∀ x y u v, E c d * (cp x y * cm u v) = cp x y * cm u v * E c d := by
    intro x y u v
    rw [← mul_assoc, (hEC c d x y).1, mul_assoc, (hEC c d u v).2, ← mul_assoc]
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => key _ _ _ _
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun x _ => key _ _ _ _)
  · simp

theorem carKinv_sg_cp_plus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = true) (hb : ε b = true) (hc : ε c = false) :
    sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b = if b = i then cp a c else 0 := by
  have hs : sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by simp [sgE, ha, hb]
  have hcm : c ∈ minusIdx ε := by simp [minusIdx, hc]
  rw [hs, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun x _ => carKinv_triple₁ _ _ _ _ (hC i c a x).1 (hC b x i c).2.2]
  by_cases hbi : b = i
  · subst hbi
    simp [mul_ite, Finset.sum_ite_eq', hcm]
  · simp [hbi]

theorem carKinv_sg_cp_minus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = false) (hb : ε b = false) (hi : ε i = true) :
    sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b = -(if a = c then cp i b else 0) := by
  have hs : sgE ε cp cm a b = -∑ y ∈ plusIdx ε, cp y b * cm y a := by simp [sgE, ha, hb]
  have hip : i ∈ plusIdx ε := by simp [plusIdx, hi]
  have e : ∀ S T : Module.End ℂ W, (-S) * T - T * (-S) = -(S * T - T * S) := fun S T => by noncomm_ring
  rw [hs, e, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun y _ => carKinv_triple₁ _ _ _ _ (hC i c y b).1 (hC y a i c).2.2]
  congr 1
  by_cases hac : a = c
  · subst hac
    simp [mul_ite, Finset.sum_ite_eq', hip]
  · simp [hac]

theorem carKinv_sg_cm_plus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = true) (hb : ε b = true) (hc : ε c = false) :
    sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b = -(if i = a then cm b c else 0) := by
  have hs : sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by simp [sgE, ha, hb]
  have hcm : c ∈ minusIdx ε := by simp [minusIdx, hc]
  rw [hs, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun x _ => carKinv_triple₂ _ _ _ _ (hC i c a x).2.2 (hC b x i c).2.1,
    Finset.sum_neg_distrib]
  congr 1
  by_cases hia : i = a
  · subst hia
    simp [ite_mul, Finset.sum_ite_eq, hcm]
  · simp [hia]

theorem carKinv_sg_cm_minus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = false) (hb : ε b = false) (hi : ε i = true) :
    sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b = if c = b then cm i a else 0 := by
  have hs : sgE ε cp cm a b = -∑ y ∈ plusIdx ε, cp y b * cm y a := by simp [sgE, ha, hb]
  have hip : i ∈ plusIdx ε := by simp [plusIdx, hi]
  have e : ∀ S T : Module.End ℂ W, (-S) * T - T * (-S) = -(S * T - T * S) := fun S T => by noncomm_ring
  rw [hs, e, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun y _ => carKinv_triple₂ _ _ _ _ (hC i c y b).2.2 (hC y a i c).2.1,
    Finset.sum_neg_distrib, neg_neg]
  by_cases hcb : c = b
  · subst hcb
    simp [ite_mul, Finset.sum_ite_eq, hip]
  · simp [hcb]

theorem carKinv_term_d {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b i c : Fin n) :
    E c i * cp i c * diagE ε E cp cm a b - diagE ε E cp cm a b * (E c i * cp i c) =
      ((if i = a then E c b else 0) - (if b = c then E a i else 0)) * cp i c -
        E c i * (sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b) := by
  unfold diagE
  rw [carKinv_expand _ _ _ _ (hEC a b i c).1.symm (carKinv_E_sgE hEC ε a b c i), hE c i a b]

theorem carKinv_term_d' {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b i c : Fin n) :
    E i c * cm i c * diagE ε E cp cm a b - diagE ε E cp cm a b * (E i c * cm i c) =
      ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
        E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) := by
  unfold diagE
  rw [carKinv_expand _ _ _ _ (hEC a b i c).2.symm (carKinv_E_sgE hEC ε a b i c), hE i c a b]

theorem dOp_comm_diagE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) :
    dOp ε E cp * diagE ε E cp cm a b = diagE ε E cp cm a b * dOp ε E cp := by
  unfold dOp
  apply carKinv_sum_mul_comm
  simp_rw [carKinv_term_d hE hEC]
  have hpl : ∀ x, x ∈ plusIdx ε ↔ ε x = true := fun x => by simp [plusIdx]
  have hmi : ∀ x, x ∈ minusIdx ε ↔ ε x = false := fun x => by simp [minusIdx]
  cases hεa : ε a
  ·
    have hεb : ε b = false := by rw [← hab]; exact hεa
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := (hpl i).1 hi
    have hia : i ≠ a := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun c _ => show
        ((if i = a then E c b else 0) - (if b = c then E a i else 0)) * cp i c -
          E c i * (sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b) =
        (if a = c then E a i * cp i b else 0) - (if b = c then E a i * cp i b else 0) by
      rw [carKinv_sg_cp_minus hC ε a b i c hεa hεb hi']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos ((hmi a).2 hεa),
      if_pos ((hmi b).2 hεb), sub_self]
  ·
    have hεb : ε b = true := by rw [← hab]; exact hεa
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := (hmi c).1 hc
    have hbc : b ≠ c := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun i _ => show
        ((if i = a then E c b else 0) - (if b = c then E a i else 0)) * cp i c -
          E c i * (sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b) =
        (if i = a then E c b * cp a c else 0) - (if b = i then E c b * cp a c else 0) by
      rw [carKinv_sg_cp_plus hC ε a b i c hεa hεb hc']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hpl a).2 hεa),
      if_pos ((hpl b).2 hεb), sub_self]

theorem dOp'_comm_diagE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) :
    dOp' ε E cm * diagE ε E cp cm a b = diagE ε E cp cm a b * dOp' ε E cm := by
  unfold dOp'
  rw [neg_mul, mul_neg, neg_inj]
  apply carKinv_sum_mul_comm
  simp_rw [carKinv_term_d' hE hEC]
  have hpl : ∀ x, x ∈ plusIdx ε ↔ ε x = true := fun x => by simp [plusIdx]
  have hmi : ∀ x, x ∈ minusIdx ε ↔ ε x = false := fun x => by simp [minusIdx]
  cases hεa : ε a
  ·
    have hεb : ε b = false := by rw [← hab]; exact hεa
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := (hpl i).1 hi
    have hib : b ≠ i := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun c _ => show
        ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
          E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) =
        (if c = a then E i b * cm i a else 0) - (if c = b then E i b * cm i a else 0) by
      rw [carKinv_sg_cm_minus hC ε a b i c hεa hεb hi']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos ((hmi a).2 hεa),
      if_pos ((hmi b).2 hεb), sub_self]
  ·
    have hεb : ε b = true := by rw [← hab]; exact hεa
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := (hmi c).1 hc
    have hca : c ≠ a := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun i _ => show
        ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
          E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) =
        (if i = a then E a c * cm b c else 0) - (if b = i then E a c * cm b c else 0) by
      rw [carKinv_sg_cm_plus hC ε a b i c hεa hεb hc']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hpl a).2 hεa),
      if_pos ((hpl b).2 hεb), sub_self]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARSqA
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem csq_sum_univ_pm {R : Type*} [AddCommMonoid R] (ε : Fin n → Bool) (f : Fin n → R) :
    ∑ a, f a = ∑ a ∈ plusIdx ε, f a + ∑ a ∈ minusIdx ε, f a := by
  unfold plusIdx minusIdx
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => ε a = true) f]
  congr 1

theorem sum_comm_pair_pair {R : Type*} [AddCommMonoid R] {ι κ ι' κ' : Type*} (s : Finset ι) (s' : Finset ι')
    (t : Finset κ) (t' : Finset κ') (f : ι → ι' → κ → κ' → R) :
    ∑ a ∈ s, ∑ b ∈ s', ∑ i ∈ t, ∑ j ∈ t', f a b i j = ∑ i ∈ t, ∑ j ∈ t', ∑ a ∈ s, ∑ b ∈ s', f a b i j := by
  calc _ = ∑ a ∈ s, ∑ i ∈ t, ∑ b ∈ s', ∑ j ∈ t', f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a ∈ s, ∑ i ∈ t, ∑ j ∈ t', ∑ b ∈ s', f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ t, ∑ a ∈ s, ∑ j ∈ t', ∑ b ∈ s', f a b i j := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem csq_filter_eq_plus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ plusIdx ε) :
    univ.filter (fun b => ε b = ε a) = plusIdx ε := by
  have h : ε a = true := by simpa [plusIdx] using ha
  ext b
  simp [plusIdx, h]

theorem csq_filter_eq_minus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ minusIdx ε) :
    univ.filter (fun b => ε b = ε a) = minusIdx ε := by
  have h : ε a = false := by simpa [minusIdx] using ha
  ext b
  simp [minusIdx, h]

theorem casimirK_pm {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ M) :
    casimirK ε F = ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, F a b * F b a +
      ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, F a b * F b a := by
  unfold casimirK
  rw [csq_sum_univ_pm ε]
  congr 1
  · exact Finset.sum_congr rfl fun a ha => by rw [csq_filter_eq_plus ε ha]
  · exact Finset.sum_congr rfl fun a ha => by rw [csq_filter_eq_minus ε ha]

theorem csq_sgE_pp (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W) {a b : Fin n}
    (ha : a ∈ plusIdx ε) (hb : b ∈ plusIdx ε) :
    sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by
  have ha' : ε a = true := by simpa [plusIdx] using ha
  have hb' : ε b = true := by simpa [plusIdx] using hb
  simp [sgE, ha', hb']

theorem csq_sgE_mm (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W) {a b : Fin n}
    (ha : a ∈ minusIdx ε) (hb : b ∈ minusIdx ε) :
    sgE ε cp cm a b = -∑ i ∈ plusIdx ε, cp i b * cm i a := by
  have ha' : ε a = false := by simpa [minusIdx] using ha
  have hb' : ε b = false := by simpa [minusIdx] using hb
  simp [sgE, ha', hb']

theorem csq_two_rhoHol_plus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ plusIdx ε) :
    (2 : ℂ) * ((rhoHol ε a : ℝ) : ℂ) = (qOf ε : ℂ) := by
  have ha' : ε a = true := by simpa [plusIdx] using ha
  rw [show rhoHol ε a = (qOf ε : ℝ) / 2 by simp [rhoHol, ha']]
  push_cast
  ring

theorem csq_two_rhoHol_minus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ minusIdx ε) :
    (2 : ℂ) * ((rhoHol ε a : ℝ) : ℂ) = -(pOf ε : ℂ) := by
  have ha' : ε a = false := by simpa [minusIdx] using ha
  rw [show rhoHol ε a = -(pOf ε : ℝ) / 2 by simp [rhoHol, ha']]
  push_cast
  ring

theorem two_rho_sum {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (F : Fin n → Module.End ℂ M) :
    (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • F a =
      ∑ a ∈ plusIdx ε, (qOf ε : ℂ) • F a - ∑ a ∈ minusIdx ε, (pOf ε : ℂ) • F a := by
  rw [Finset.smul_sum, csq_sum_univ_pm ε, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun a ha => by rw [smul_smul, csq_two_rhoHol_plus ε ha]
  · exact Finset.sum_congr rfl fun a ha => by rw [smul_smul, csq_two_rhoHol_minus ε ha, neg_smul]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.GelfandHW
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def hwShift (ν : Fin n → ℝ) : Fin n → ℂ := fun r => ((ν r : ℝ) : ℂ) + (((n - 1 - (r : ℕ) : ℕ) : ℝ) : ℂ)

theorem hwShift_eq_icShift (ν : Fin n → ℝ) : hwShift ν = icShift (ν + rho n) := by
  funext r
  have hr := r.isLt
  simp only [hwShift, icShift, rho, Pi.add_apply]
  rw [Nat.cast_sub (by omega : (r : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

theorem ePow_hw_lower {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) (s r : Fin n) (hsr : s < r) : ePow E k s r v = 0 := by
  induction k generalizing s r with
  | zero => simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, hsr.ne]
  | succ k ih =>
    rw [show ePow E (k + 1) s r = ∑ c, E s c * ePow E k c r from by simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply], LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro c _
    rw [Module.End.mul_apply]
    rcases lt_or_ge c r with hcr | hrc
    · rw [ih c r hcr, map_zero]
    · have hc := ePow_comm hE k s c c r
      rw [if_pos rfl, if_neg hsr.ne'] at hc
      have hc' := congrArg (fun f => f v) hc
      simp only [LinearMap.sub_apply, Module.End.mul_apply, sub_zero] at hc'
      rw [hv.2 s c (lt_of_lt_of_le hsr hrc), map_zero, sub_zero, ih s r hsr] at hc'
      exact hc'

theorem ePow_hw_diag {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) (r : Fin n) : ePow E k r r v = gx (hwShift ν) k r • v := by
  induction k generalizing r with
  | zero => simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, gx]
  | succ k ih =>
    have key : ∀ c, E r c (ePow E k c r v) =
        ((if c = r then (ν r : ℂ) * gx (hwShift ν) k r else 0) +
         (if r < c then gx (hwShift ν) k r - gx (hwShift ν) k c else 0)) • v := by
      intro c
      rcases lt_trichotomy c r with h | h | h
      · rw [ePow_hw_lower hE hv k c r h, map_zero, if_neg h.ne, if_neg (not_lt.2 h.le)]
        simp
      · subst h
        rw [ih, LinearMap.map_smul, hv.1, smul_smul, if_pos rfl, if_neg (lt_irrefl _), add_zero,
          mul_comm]
      · have hc := ePow_comm hE k r c c r
        rw [if_pos rfl, if_pos rfl] at hc
        have hc' := congrArg (fun f => f v) hc
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc'
        rw [hv.2 r c h, map_zero, sub_zero, ih, ih c] at hc'
        rw [if_neg h.ne', if_pos h, zero_add, sub_smul]
        exact hc'
    rw [show ePow E (k + 1) r r = ∑ c, E r c * ePow E k c r from by simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply], LinearMap.sum_apply]
    simp only [Module.End.mul_apply, key]
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← Finset.sum_filter,
      Finset.sum_sub_distrib, Finset.sum_const]
    have hf : (univ.filter fun c => r < c) = Finset.Ioi r := by ext; simp
    rw [hf, Fin.card_Ioi, nsmul_eq_mul]
    simp only [gx, hwShift, hf]
    push_cast
    ring

theorem gelfand_hw {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) : gelfand E k v = gval (icShift (ν + rho n)) k • v := by
  unfold gelfand
  rw [LinearMap.sum_apply]
  simp only [ePow_hw_diag hE hv k, ← Finset.sum_smul, sum_gx_eq_gval, hwShift_eq_icShift]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.InhabCAR
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

abbrev Fock (n : ℕ) := ExteriorAlgebra ℂ (Fin n × Fin n → ℂ)

def cpFock (i a : Fin n) : Module.End ℂ (Fock n) :=
  LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ (Pi.single (i, a) (1 : ℂ)))

def cmFock (i a : Fin n) : Module.End ℂ (Fock n) :=
  CliffordAlgebra.contractLeft (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin n => ℂ) (i, a))

theorem isCAR_fock : IsCAR (cpFock (n := n)) cmFock := by
  intro i a j b
  refine ⟨?_, ?_, ?_⟩
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cpFock, LinearMap.mulLeft_apply,
      LinearMap.zero_apply]
    rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cmFock, LinearMap.zero_apply]
    rw [CliffordAlgebra.contractLeft_comm, neg_add_cancel]
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cmFock, cpFock, LinearMap.mulLeft_apply]
    rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
    by_cases h : i = j ∧ a = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg h]
      have hne : (i, a) ≠ (j, b) := fun e => h ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
      simp [LinearMap.proj_apply, Pi.single_apply, hne]

end ReciprocityTheory.ChartRestriction.DS
end
end

