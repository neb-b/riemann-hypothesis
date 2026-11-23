module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import Mathlib

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BoundaryCreationAnticommutator
section
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Cartan

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem anticommutator_triple_product {R : Type*} [Ring R] (K Aj Ai C d₁ d₂ : R) (h₁ : Ai * C + C * Ai = d₁)
    (h₂ : Aj * C + C * Aj = d₂) (h₃ : K * C + C * K = 0) :
    K * Aj * Ai * C + C * (K * Aj * Ai) = K * Aj * d₁ - K * d₂ * Ai := by
  subst h₁ h₂
  have h : C * K = -(K * C) := eq_neg_of_add_eq_zero_right h₃
  have h' : C * (K * Aj * Ai) = -(K * C * Aj * Ai) := by
    rw [← mul_assoc, ← mul_assoc, h]; noncomm_ring
  rw [h']
  noncomm_ring

theorem tri_anti (i j k e : Pos n) :
    (cre k * ann j * ann i * cre e + cre e * (cre k * ann j * ann i) : Module.End ℂ (Cn n V)) =
      (if i = e then cre k * ann j else 0) - (if j = e then cre k * ann i else 0) := by
  rw [anticommutator_triple_product _ _ _ _ _ _ (CompanionTheory.D.LK.Car.ann_cre i e) (CompanionTheory.D.LK.Car.ann_cre j e)
    (CompanionTheory.D.LK.Car.cre_cre k e)]
  congr 1
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem cre_mul_lift (φ : Module.End ℂ V) (e : Pos n) :
    (cre e * (lift n φ : Module.End ℂ (Cn n V)) : Module.End ℂ (Cn n V)) = (lift n φ : Module.End ℂ (Cn n V)) * cre e :=
  LinearMap.ext fun x => (CompanionTheory.D.LK.lift_cre φ e x).symm

theorem part_one (E : Fin n → Fin n → Module.End ℂ V) (e : Pos n) :
    ((∑ i : Pos n, if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) * cre e +
      cre e * ∑ i : Pos n, if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0 :
      Module.End ℂ (Cn n V)) = lift n (E e.1.1 e.1.2) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have h : ∀ i : Pos n,
      ((if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) * cre e +
        cre e * (if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) :
        Module.End ℂ (Cn n V)) = if i = e then (lift n (E e.1.1 e.1.2) : Module.End ℂ (Cn n V)) else 0 := by
    intro i
    rw [if_pos (rfl : cpt (allT n) i), ← mul_assoc (cre e), cre_mul_lift, mul_assoc, mul_assoc, ← mul_add,
      CompanionTheory.D.LK.Car.ann_cre]
    by_cases hi : i = e
    · subst hi; simp
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp

theorem sum_anti {R : Type*} [Ring R] (T P Q : Pos n → Pos n → Pos n → R) (c : R)
    (h : ∀ i j k, T i j k * c + c * T i j k = P i j k - Q i j k) :
    (∑ i, ∑ j, ∑ k, T i j k) * c + c * ∑ i, ∑ j, ∑ k, T i j k =
      ∑ i, ∑ j, ∑ k, P i j k - ∑ i, ∑ j, ∑ k, Q i j k := by
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, h, Finset.sum_sub_distrib]

theorem part_two (e : Pos n) :
    ((∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) * cre e +
      cre e * ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0 : Module.End ℂ (Cn n V)) = adL e.1.1 e.1.2 := by
  have h : ∀ i j k : Pos n,
      ((if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) * cre e +
        cre e * (if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) : Module.End ℂ (Cn n V)) =
      (if i = e ∧ e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0) -
        (if j = e ∧ i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0) := by
    intro i j k
    by_cases ht : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2
    · rw [if_pos ⟨rfl, rfl, ht⟩, tri_anti]
      obtain ⟨t1, t2, t3⟩ := ht
      congr 1
      · by_cases hi : i = e
        · subst hi
          rw [if_pos rfl, if_pos ⟨rfl, t1, Prod.ext t2 t3⟩]
        · rw [if_neg hi, if_neg fun c => hi c.1]
      · by_cases hj : j = e
        · subst hj
          rw [if_pos rfl, if_pos ⟨rfl, t1, Prod.ext t2 t3⟩]
        · rw [if_neg hj, if_neg fun c => hj c.1]
    · rw [if_neg fun c => ht c.2.2, zero_mul, mul_zero, add_zero, if_neg, if_neg, sub_zero]
      · rintro ⟨rfl, c1, c2⟩
        exact ht ⟨c1, by rw [c2], by rw [c2]⟩
      · rintro ⟨rfl, c1, c2⟩
        exact ht ⟨c1, by rw [c2], by rw [c2]⟩
  rw [sum_anti _ _ _ _ h]
  have s₁ : (∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      (if i = e ∧ e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0 : Module.End ℂ (Cn n V))) =
      ∑ j : Pos n, ∑ k : Pos n,
        (if e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0 : Module.End ℂ (Cn n V)) := by
    rw [Finset.sum_eq_single e]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have s₂ : (∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      (if j = e ∧ i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0 : Module.End ℂ (Cn n V))) =
      ∑ i : Pos n, ∑ k : Pos n,
        (if i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0 : Module.End ℂ (Cn n V)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single e]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [s₁, s₂]
  simp only [adL, adC, sub_smul, ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib]

theorem cartan (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (e : Pos n) :
    (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2 := by
  have h₁ := part_one E e
  have h₂ := part_two (V := V) e
  unfold bd lF
  rw [add_mul, mul_add, add_add_add_comm, h₁, h₂]

end GlobalTheory.CompanionTheory.Cartan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CanonicalAnticommutationRelationsConsequence
section
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CliffordCoeff

section SlopeTestRemainingChoices

variable {R : Type} [Ring R]

theorem comm_prod (D C X : R) :
    (D * C) * X - X * (D * C) = D * (C * X + X * C) - (D * X + X * D) * C := by
  noncomm_ring

theorem ad_mul (A x y : R) :
    A * (x * y) - (x * y) * A = (A * x - x * A) * y + x * (A * y - y * A) := by
  noncomm_ring

theorem ad_sub (x y z : R) :
    (x - y) * z - z * (x - y) = (x * z - z * x) - (y * z - z * y) := by
  noncomm_ring

theorem comm_sum {ι : Type} [Fintype ι] (u v : ι → R) (x : R) :
    (∑ r, u r * v r) * x - x * (∑ r, u r * v r)
      = ∑ r, (u r * (v r * x + x * v r) - (u r * x + x * u r) * v r) := by
  simp only [sum_mul, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun r _ => comm_prod _ _ _

variable {n : ℕ} {τ : Fin n → Fin n → Prop} [DecidableRel τ] {c d L : Fin n → Fin n → R}
  {p q : Fin n}

theorem ad_d
    (hd : ∀ a b a' b', d a b * d a' b' + d a' b' * d a b = 0)
    (hcd : ∀ a b a' b', c a b * d a' b' + d a' b' * c a b = if a = a' ∧ b = b' ∧ τ a b then 1 else 0)
    (hdτ : ∀ a b, ¬τ a b → d a b = 0)
    (h1 : ∀ b, τ p b ↔ τ q b) (h2 : ∀ a, τ a p ↔ τ a q) (a e : Fin n) :
    (∑ r, d p r * c q r - ∑ r, d r q * c r p) * d a e
        - d a e * (∑ r, d p r * c q r - ∑ r, d r q * c r p)
      = (if q = a then d p e else 0) - (if p = e then d a q else 0) := by
  have e1 : (∑ r, d p r * c q r) * d a e - d a e * (∑ r, d p r * c q r)
      = if q = a then d p e else 0 := by
    rw [comm_sum]
    simp only [hd, hcd, zero_mul, sub_zero]
    rw [Fintype.sum_eq_single e (fun r hr => by simp [hr])]
    by_cases hq : q = a
    · subst hq
      by_cases ht : τ q e
      · simp [ht]
      · have : d p e = 0 := hdτ _ _ fun h => ht ((h1 e).1 h)
        simp [ht, this]
    · simp [hq]
  have e2 : (∑ r, d r q * c r p) * d a e - d a e * (∑ r, d r q * c r p)
      = if p = e then d a q else 0 := by
    rw [comm_sum]
    simp only [hd, hcd, zero_mul, sub_zero]
    rw [Fintype.sum_eq_single a (fun r hr => by simp [hr])]
    by_cases hp : p = e
    · subst hp
      by_cases ht : τ a p
      · simp [ht]
      · have : d a q = 0 := hdτ _ _ fun h => ht ((h2 a).2 h)
        simp [ht, this]
    · simp [hp]
  rw [ad_sub, e1, e2]

theorem ad_c
    (hc : ∀ a b a' b', c a b * c a' b' + c a' b' * c a b = 0)
    (hcd : ∀ a b a' b', c a b * d a' b' + d a' b' * c a b = if a = a' ∧ b = b' ∧ τ a b then 1 else 0)
    (hcτ : ∀ a b, ¬τ a b → c a b = 0)
    (h1 : ∀ b, τ p b ↔ τ q b) (h2 : ∀ a, τ a p ↔ τ a q) (a b : Fin n) :
    (∑ r, d p r * c q r - ∑ r, d r q * c r p) * c a b
        - c a b * (∑ r, d p r * c q r - ∑ r, d r q * c r p)
      = (if q = b then c a p else 0) - (if p = a then c q b else 0) := by
  have hdc : ∀ a b a' b', d a' b' * c a b + c a b * d a' b'
      = if a = a' ∧ b = b' ∧ τ a b then 1 else 0 := fun a b a' b' => by
    rw [add_comm]; exact hcd a b a' b'
  have e1 : (∑ r, d p r * c q r) * c a b - c a b * (∑ r, d p r * c q r)
      = - (if p = a then c q b else 0) := by
    rw [comm_sum]
    simp only [hc, hdc, mul_zero, zero_sub, sum_neg_distrib]
    rw [Fintype.sum_eq_single b (fun r hr => by simp [hr.symm])]
    by_cases hp : p = a
    · subst hp
      by_cases ht : τ p b
      · simp [ht]
      · have : c q b = 0 := hcτ _ _ fun h => ht ((h1 b).2 h)
        simp [ht, this]
    · simp [hp, Ne.symm hp]
  have e2 : (∑ r, d r q * c r p) * c a b - c a b * (∑ r, d r q * c r p)
      = - (if q = b then c a p else 0) := by
    rw [comm_sum]
    simp only [hc, hdc, mul_zero, zero_sub, sum_neg_distrib]
    rw [Fintype.sum_eq_single a (fun r hr => by simp [hr.symm])]
    by_cases hq : q = b
    · subst hq
      by_cases ht : τ a q
      · simp [ht]
      · have : c a p = 0 := hcτ _ _ fun h => ht ((h2 a).1 h)
        simp [ht, this]
    · simp [hq, Ne.symm hq]
  rw [ad_sub, e1, e2]
  abel

theorem ad_triple (A : R)
    (hAd : ∀ a e, A * d a e - d a e * A
      = (if q = a then d p e else 0) - (if p = e then d a q else 0))
    (hAc : ∀ a b, A * c a b - c a b * A
      = (if q = b then c a p else 0) - (if p = a then c q b else 0)) :
    A * (∑ a, ∑ b, ∑ e, d a e * c b e * c a b) - (∑ a, ∑ b, ∑ e, d a e * c b e * c a b) * A
      = 0 := by
  have step : ∀ a b e, A * (d a e * c b e * c a b) - (d a e * c b e * c a b) * A
      = (if q = a then d p e else 0) * c b e * c a b
        - (if p = e then d a q else 0) * c b e * c a b
        + d a e * (if q = e then c b p else 0) * c a b
        - d a e * (if p = b then c q e else 0) * c a b
        + d a e * c b e * (if q = b then c a p else 0)
        - d a e * c b e * (if p = a then c q b else 0) := by
    intro a b e
    rw [ad_mul, ad_mul, hAd, hAc, hAc]
    simp only [sub_mul, mul_sub, add_mul, mul_add, mul_assoc]
    abel
  have s1 : ∑ a, ∑ b, ∑ e, (if q = a then d p e else 0) * c b e * c a b
      = ∑ b, ∑ e, d p e * c b e * c q b := by
    rw [Fintype.sum_eq_single q (fun a ha => by simp [Ne.symm ha])]
    simp
  have s6 : ∑ a, ∑ b, ∑ e, d a e * c b e * (if p = a then c q b else 0)
      = ∑ b, ∑ e, d p e * c b e * c q b := by
    rw [Fintype.sum_eq_single p (fun a ha => by simp [Ne.symm ha])]
    simp
  have s2 : ∑ a, ∑ b, ∑ e, (if p = e then d a q else 0) * c b e * c a b
      = ∑ a, ∑ b, d a q * c b p * c a b := by
    simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
  have s3 : ∑ a, ∑ b, ∑ e, d a e * (if q = e then c b p else 0) * c a b
      = ∑ a, ∑ b, d a q * c b p * c a b := by
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, sum_ite_eq, mem_univ, if_true]
  have s4 : ∑ a, ∑ b, ∑ e, d a e * (if p = b then c q e else 0) * c a b
      = ∑ a, ∑ e, d a e * c q e * c a p := by
    refine sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_eq_single p (fun b hb => by simp [Ne.symm hb])]
    simp
  have s5 : ∑ a, ∑ b, ∑ e, d a e * c b e * (if q = b then c a p else 0)
      = ∑ a, ∑ e, d a e * c q e * c a p := by
    refine sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_eq_single q (fun b hb => by simp [Ne.symm hb])]
    simp
  have hs : A * (∑ a, ∑ b, ∑ e, d a e * c b e * c a b)
      - (∑ a, ∑ b, ∑ e, d a e * c b e * c a b) * A
      = ∑ a, ∑ b, ∑ e, (A * (d a e * c b e * c a b) - (d a e * c b e * c a b) * A) := by
    simp only [mul_sum, sum_mul, sum_sub_distrib]
  rw [hs]
  simp only [step, sum_add_distrib, sum_sub_distrib]
  rw [s1, s2, s3, s4, s5, s6]
  abel

theorem ad_first (A : R) (hAL : ∀ a b, A * L a b = L a b * A)
    (hAc : ∀ a b, A * c a b - c a b * A
      = (if q = b then c a p else 0) - (if p = a then c q b else 0)) :
    A * (∑ a, ∑ b, L a b * c a b) - (∑ a, ∑ b, L a b * c a b) * A
      = ∑ a, L a q * c a p - ∑ b, L p b * c q b := by
  have hs : A * (∑ a, ∑ b, L a b * c a b) - (∑ a, ∑ b, L a b * c a b) * A
      = ∑ a, ∑ b, (A * (L a b * c a b) - (L a b * c a b) * A) := by
    simp only [mul_sum, sum_mul, sum_sub_distrib]
  have step : ∀ a b, A * (L a b * c a b) - (L a b * c a b) * A
      = L a b * (if q = b then c a p else 0) - L a b * (if p = a then c q b else 0) := by
    intro a b
    rw [ad_mul, hAL, sub_self, zero_mul, zero_add, hAc, mul_sub]
  rw [hs]
  simp only [step, sum_sub_distrib]
  congr 1
  · simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]
  · rw [Fintype.sum_eq_single p (fun a ha => by simp [Ne.symm ha])]
    simp

theorem ad_L_first
    (hLc : ∀ a b a' b', Commute (L a b) (c a' b'))
    (hLL : ∀ a b, L p q * L a b - L a b * L p q
      = (if q = a then L p b else 0) - (if b = p then L a q else 0)) :
    L p q * (∑ a, ∑ b, L a b * c a b) - (∑ a, ∑ b, L a b * c a b) * L p q
      = ∑ b, L p b * c q b - ∑ a, L a q * c a p := by
  have hs : L p q * (∑ a, ∑ b, L a b * c a b) - (∑ a, ∑ b, L a b * c a b) * L p q
      = ∑ a, ∑ b, (L p q * (L a b * c a b) - (L a b * c a b) * L p q) := by
    simp only [mul_sum, sum_mul, sum_sub_distrib]
  have step : ∀ a b, L p q * (L a b * c a b) - (L a b * c a b) * L p q
      = (if q = a then L p b else 0) * c a b - (if b = p then L a q else 0) * c a b := by
    intro a b
    rw [ad_mul, hLL, (hLc p q a b).eq, sub_self, mul_zero, add_zero, sub_mul]
  rw [hs]
  simp only [step, sum_sub_distrib]
  congr 1
  · rw [Fintype.sum_eq_single q (fun a ha => by simp [Ne.symm ha])]
    simp
  · simp only [ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true]

end SlopeTestRemainingChoices

theorem commute_shifted_dirac : ∀ (n : ℕ) (R : Type) [Ring R] (τ : Fin n → Fin n → Prop) [DecidableRel τ] (c d L : Fin n → Fin n → R) (p q : Fin n),
    (∀ a b a' b', c a b * c a' b' + c a' b' * c a b = 0) →
    (∀ a b a' b', d a b * d a' b' + d a' b' * d a b = 0) →
    (∀ a b a' b', c a b * d a' b' + d a' b' * c a b = if a = a' ∧ b = b' ∧ τ a b then 1 else 0) →
    (∀ a b, ¬τ a b → c a b = 0) → (∀ a b, ¬τ a b → d a b = 0) →
    (∀ b, τ p b ↔ τ q b) → (∀ a, τ a p ↔ τ a q) →
    (∀ a b a' b', Commute (L a b) (c a' b')) → (∀ a b a' b', Commute (L a b) (d a' b')) →
    (∀ a b, L p q * L a b - L a b * L p q = (if q = a then L p b else 0) - (if b = p then L a q else 0)) →
    Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p))
      ((∑ a, ∑ b, L a b * c a b) + ∑ a, ∑ b, ∑ e, d a e * c b e * c a b) := by
  intro n R _ τ _ c d L p q hc hd hcd hcτ hdτ h1 h2 hLc hLd hLL
  have hAd := ad_d (p := p) (q := q) (c := c) hd hcd hdτ h1 h2
  have hAc := ad_c (p := p) (q := q) (d := d) hc hcd hcτ h1 h2
  have hAL : ∀ a b, (∑ r, d p r * c q r - ∑ r, d r q * c r p) * L a b
      = L a b * (∑ r, d p r * c q r - ∑ r, d r q * c r p) := by
    intro a b
    have : Commute (∑ r, d p r * c q r - ∑ r, d r q * c r p) (L a b) :=
      Commute.sub_left
        (Commute.sum_left _ _ _ fun r _ => ((hLd a b p r).symm).mul_left (hLc a b q r).symm)
        (Commute.sum_left _ _ _ fun r _ => ((hLd a b r q).symm).mul_left (hLc a b r p).symm)
    exact this.eq
  have hB1 := ad_first (L := L) (p := p) (q := q) (c := c) _ hAL hAc
  have hB2 := ad_L_first (L := L) (p := p) (q := q) (c := c) hLc hLL
  have hQ1 := ad_triple (p := p) (q := q) (c := c) (d := d) _ hAd hAc
  have hQ2 : Commute (L p q) (∑ a, ∑ b, ∑ e, d a e * c b e * c a b) :=
    Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ =>
      Commute.sum_right _ _ _ fun e _ =>
        ((hLd p q a e).mul_right (hLc p q b e)).mul_right (hLc p q a b)
  generalize (∑ r, d p r * c q r - ∑ r, d r q * c r p) = A at *
  generalize (∑ a, ∑ b, ∑ e, d a e * c b e * c a b) = Q at *
  generalize (∑ a, ∑ b, L a b * c a b) = B at *
  have key : (L p q + A) * (B + Q) - (B + Q) * (L p q + A)
      = (L p q * B - B * L p q) + (A * B - B * A) + (L p q * Q - Q * L p q) + (A * Q - Q * A) := by
    noncomm_ring
  have hQ2' : L p q * Q - Q * L p q = 0 := sub_eq_zero.2 hQ2.eq
  rw [hB1, hB2, hQ1, hQ2'] at key
  refine sub_eq_zero.1 ?_
  rw [key]
  abel

end GlobalTheory.CompanionTheory.CliffordCoeff
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreationProductSingleBasis
section
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Chains

theorem cre_single {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (f : Pos n) (S : Finset (Pos n)) (w : V)
    (h : f ∉ S) :
    (cre f : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V) =
      CompanionTheory.D.LK.sg f (insert f S) • (Pi.single (insert f S) w : Cn n V) := by
  funext A
  show (if f ∈ A then CompanionTheory.D.LK.sg f A • (Pi.single S w : Cn n V) (A.erase f) else 0) = _
  by_cases hA : A = insert f S
  · subst hA
    rw [if_pos (Finset.mem_insert_self f S), Finset.erase_insert h]
    simp [Pi.single_apply]
  · have hr : (CompanionTheory.D.LK.sg f (insert f S) • (Pi.single (insert f S) w : Cn n V)) A = 0 := by
      simp [Pi.single_apply, hA]
    rw [hr]
    split_ifs with hf
    · have hne : A.erase f ≠ S := fun he => hA (by rw [← he, Finset.insert_erase hf])
      simp [Pi.single_apply, hne]
    · rfl

theorem sg_ne_zero {n : ℕ} (f : Pos n) (A : Finset (Pos n)) : CompanionTheory.D.LK.sg f A ≠ 0 := by
  delta CompanionTheory.D.LK.sg
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

theorem prod_cre_single : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (l : List (Pos n)) (S : Finset (Pos n)) (w : V),
    l.Nodup → (∀ i ∈ l, i ∉ S) → ∃ c : ℂ, c ≠ 0 ∧
      ((l.map cre).prod : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V) = c • (Pi.single (S ∪ l.toFinset) w : Cn n V) := by
  intro n V _ _ l S w
  induction l with
  | nil =>
    intro _ _
    refine ⟨1, one_ne_zero, ?_⟩
    simp
  | cons a l ih =>
    intro hnd hS
    obtain ⟨c, hc, hcl⟩ := ih hnd.of_cons (fun i hi => hS i (by simp [hi]))
    have ha : a ∉ S ∪ l.toFinset := by
      rw [Finset.mem_union, not_or, List.mem_toFinset]
      exact ⟨hS a (by simp), (List.nodup_cons.1 hnd).1⟩
    refine ⟨c * CompanionTheory.D.LK.sg a (insert a (S ∪ l.toFinset)), mul_ne_zero hc (sg_ne_zero _ _), ?_⟩
    rw [List.map_cons, List.prod_cons]
    show cre a (((l.map cre).prod : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V)) = _
    rw [hcl, map_smul, cre_single a _ w ha, smul_smul, List.toFinset_cons, Finset.union_insert]

end GlobalTheory.CompanionTheory.Chains
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreationProductSupportDegree
section
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgExh

theorem suppIn_deg_cre_prod : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (P : Pos n → Prop) (l : List (Pos n)) (x : Cn n V) (j : ℕ),
    (∀ i ∈ l, P i) → SuppIn P x → Deg j x →
      SuppIn P (((l.map cre).prod : Module.End ℂ (Cn n V)) x) ∧
        Deg (j + l.length) (((l.map cre).prod : Module.End ℂ (Cn n V)) x) := by
  intro n V _ _ P l x j hl hx hd
  induction l with
  | nil => simpa using And.intro hx hd
  | cons i l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hl k (List.mem_cons_of_mem i hk)
    have hi : P i := hl i List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons]
    constructor
    · intro A hA k hk
      obtain ⟨h1, h2⟩ := CompanionTheory.D.LK.cre_ne hA
      by_cases hki : k = i
      · exact hki ▸ hi
      · exact ih1 _ h2 k (Finset.mem_erase.2 ⟨hki, hk⟩)
    · intro A hA
      obtain ⟨h1, h2⟩ := CompanionTheory.D.LK.cre_ne hA
      have h3 := ih2 _ h2
      have h4 := Finset.card_erase_add_one h1
      omega

end GlobalTheory.CompanionTheory.RgExh
end

