module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.MuMEvalPowEqZero
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Polynomial

variable (l : ℕ) [Fact l.Prime]

def muM : Submonoid ℂ_[l] where
  carrier := muP l
  one_mem' := ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), one_pow 1⟩
  mul_mem' := by
    rintro a b ⟨n, hn, hln, ha⟩ ⟨m, hm, hlm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
      · exact hln h
      · exact hlm h
    · rw [mul_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hb, one_pow, one_mul]

theorem muM_common (S : Finset (muM l)) :
    ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ∀ a ∈ S, (a : ℂ_[l]) ^ n = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), by simp⟩
  | insert a S _ ih =>
    obtain ⟨n, hn, hln, hS⟩ := ih
    obtain ⟨m, hm, hlm, ha⟩ := a.2
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
      · exact hln h
      · exact hlm h
    · intro b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · rw [mul_comm, pow_mul, ha, one_pow]
      · rw [pow_mul, hS b hb, one_pow]

theorem muM_exists_gen (n : ℕ) (hn : 0 < n) :
    ∃ g : ℂ_[l], g ^ n = 1 ∧ ∀ a : ℂ_[l], a ^ n = 1 → ∃ k : ℕ, g ^ k = a := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := rootsOfUnity n ℂ_[l])
  refine ⟨((g : ℂ_[l]ˣ) : ℂ_[l]), ?_, fun a ha => ?_⟩
  · have := g.2
    rw [mem_rootsOfUnity'] at this
    exact this
  · obtain ⟨k, hk⟩ := hg (rootsOfUnity.mkOfPowEq a ha)
    refine ⟨k, ?_⟩
    have := congrArg (fun x : rootsOfUnity n ℂ_[l] => ((x : ℂ_[l]ˣ) : ℂ_[l])) hk
    simpa using this

theorem muM_eval_pow_eq_zero {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 0 < n) (hln : ¬ l ∣ n)
    (g : K) (hg : g ^ n = 1) (p : ℤ[X]) (hp : p.eval₂ (Int.castRingHom K) g = 0) :
    p.eval₂ (Int.castRingHom K) (g ^ l) = 0 := by
  rw [← algebraMap_int_eq, ← aeval_def] at hp ⊢
  have hd : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one hg
  have hd0 : 0 < orderOf g := Nat.pos_of_dvd_of_pos hd hn
  have hprim : IsPrimitiveRoot g (orderOf g) := IsPrimitiveRoot.orderOf g
  have hcop : Nat.Coprime l (orderOf g) :=
    ((Fact.out : l.Prime).coprime_iff_not_dvd).2 fun h => hln (h.trans hd)
  have hdvd : minpoly ℤ g ∣ p := minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hd0) hp
  rw [hprim.minpoly_eq_pow_coprime hcop] at hdvd
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (g ^ l))

def phiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] := MonoidAlgebra.lift ℤ ℂ_[l] (muM l) (muM l).subtype

def psiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] :=
  MonoidAlgebra.lift ℤ ℂ_[l] (muM l) ((muM l).subtype.comp (powMonoidHom l))

theorem phiM_ker_le (f : MonoidAlgebra ℤ (muM l)) (hf : phiM l f = 0) : psiM l f = 0 := by
  classical
  obtain ⟨n, hn, hln, hS⟩ := muM_common l f.coeff.support
  obtain ⟨g, hg, hgen⟩ := muM_exists_gen l n hn
  have hk : ∀ a : muM l, ∃ k : ℕ, a ∈ f.coeff.support → g ^ k = (a : ℂ_[l]) := by
    intro a
    by_cases ha : a ∈ f.coeff.support
    · obtain ⟨k, hk⟩ := hgen a (hS a ha)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose k hk using hk
  let p : ℤ[X] := ∑ a ∈ f.coeff.support, C (f.coeff a) * X ^ (k a)
  have h1 : p.eval₂ (Int.castRingHom ℂ_[l]) g = 0 := by
    rw [← hf, phiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, hk a ha]
    simp [zsmul_eq_mul]
  have h2 := muM_eval_pow_eq_zero l n hn hln g hg p h1
  rw [← h2, psiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← pow_mul, mul_comm l, pow_mul, hk a ha]
  simp [zsmul_eq_mul]

theorem phiM_mem (f : MonoidAlgebra ℤ (muM l)) : phiM l f ∈ Rmu l := by
  rw [phiM, MonoidAlgebra.lift_apply]
  exact Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure a.2) _

theorem psiM_mem (f : MonoidAlgebra ℤ (muM l)) : psiM l f ∈ Rmu l := by
  rw [psiM, MonoidAlgebra.lift_apply]
  exact Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure (a ^ l).2) _

theorem phiM_surj (x : ℂ_[l]) (hx : x ∈ Rmu l) : ∃ f, phiM l f = x := by
  have : Rmu l ≤ (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).range := by
    refine Subring.closure_le.2 fun ζ hζ => ⟨MonoidAlgebra.single ⟨ζ, hζ⟩ 1, ?_⟩
    simp [phiM]
  exact this hx

theorem rmu_sigma : ∃ s : Rmu l →+* Rmu l,
    ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l), ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l := by
  let φ : MonoidAlgebra ℤ (muM l) →+* Rmu l :=
    (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) (phiM_mem l)
  let ψ : MonoidAlgebra ℤ (muM l) →+* Rmu l :=
    (psiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) (psiM_mem l)
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨f, hf⟩ := phiM_surj l x hx
    exact ⟨f, Subtype.ext hf⟩
  have hker : RingHom.ker φ ≤ RingHom.ker ψ := by
    intro f hf
    rw [RingHom.mem_ker] at hf ⊢
    exact Subtype.ext (phiM_ker_le l f (congrArg Subtype.val hf))
  refine ⟨RingHom.liftOfSurjective φ hφ ⟨ψ, hker⟩, fun ζ hζ => ?_⟩
  have h1 : (⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) = φ (MonoidAlgebra.single ⟨ζ, hζ⟩ 1) :=
    Subtype.ext (by simp [φ, phiM])
  rw [h1, RingHom.liftOfRightInverse_comp_apply]
  simp [ψ, psiM]

theorem rmu_sigma_congr (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ∃ r ∈ Rmu l, ((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l = (l : ℂ_[l]) * r := by
  have hl : l.Prime := Fact.out
  have key : ∀ (y : ℂ_[l]) (hy : y ∈ Rmu l), ∃ r : Rmu l, s ⟨y, hy⟩ - ⟨y, hy⟩ ^ l = (l : Rmu l) * r := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem ζ hζ => exact ⟨0, Subtype.ext (by simp [hs ζ hζ])⟩
    | zero =>
      refine ⟨0, ?_⟩
      have : (⟨0, zero_mem _⟩ : Rmu l) = 0 := rfl
      rw [this, map_zero, zero_pow hl.ne_zero]; simp
    | one =>
      refine ⟨0, ?_⟩
      have : (⟨1, one_mem _⟩ : Rmu l) = 1 := rfl
      rw [this, map_one, one_pow]; simp
    | add a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      obtain ⟨u, hu⟩ := exists_add_pow_prime_eq hl (⟨a, ha⟩ : Rmu l) ⟨b, hb⟩
      refine ⟨r + t - ⟨a, ha⟩ * ⟨b, hb⟩ * u, ?_⟩
      have : (⟨a + b, add_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this, map_add (f := _), hu]
      linear_combination hr + ht
    | neg a ha iha =>
      obtain ⟨r, hr⟩ := iha
      have : (⟨-a, neg_mem ha⟩ : Rmu l) = -⟨a, ha⟩ := rfl
      rw [this, map_neg]
      rcases hl.eq_two_or_odd' with h2 | hodd
      · refine ⟨-r - ⟨a, ha⟩ ^ 2, ?_⟩
        subst h2
        push_cast at hr ⊢
        linear_combination -hr
      · refine ⟨-r, ?_⟩
        rw [hodd.neg_pow]
        linear_combination -hr
    | mul a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      refine ⟨r * s ⟨b, hb⟩ + ⟨a, ha⟩ ^ l * t, ?_⟩
      have : (⟨a * b, mul_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this, map_mul, mul_pow]
      linear_combination s ⟨b, hb⟩ * hr + ⟨a, ha⟩ ^ l * ht
  obtain ⟨r, hr⟩ := key x.1 x.2
  refine ⟨r, r.2, ?_⟩
  have := congrArg (Subtype.val) hr
  simpa using this

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.SemilinNormPowSubPow
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

omit [CompleteSpace K] [CharZero K] in
theorem semilin_norm_add_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

omit [CompleteSpace K] [CharZero K] in
theorem semilin_norm_sub_le {a b : K} {t : ℝ} (ha : ‖a‖ ≤ t) (hb : ‖b‖ ≤ t) : ‖a - b‖ ≤ t := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))


omit [CompleteSpace K] [CharZero K] in
theorem semilin_norm_pow_sub_pow {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a‖ * ‖a ^ n - b ^ n‖ ≤ 1 * ‖a - b‖ := mul_le_mul ha ih (norm_nonneg _) zero_le_one
        _ = ‖a - b‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖a - b‖ * ‖b‖ ^ n ≤ ‖a - b‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _)
        _ = ‖a - b‖ := mul_one _


omit [CompleteSpace K] [CharZero K] in
theorem FrobField.norm_sq_sub_pow_le {l : ℕ} {σ : K →+* K} (h : FrobField K l σ) (x : K) (hx : ‖x‖ ≤ 1) :
    ‖σ (σ x) - x ^ (l ^ 2)‖ ≤ ‖(l : K)‖ := by
  have hp : x ^ (l ^ 2) = (x ^ l) ^ l := by rw [← pow_mul, sq]
  have e : σ (σ x) - x ^ (l ^ 2) = σ (σ x - x ^ l) + ((σ x) ^ l - (x ^ l) ^ l) := by
    rw [hp, map_sub, map_pow]
    ring
  have h1 : ‖σ x - x ^ l‖ ≤ ‖(l : K)‖ := h.frob x hx
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [h.isom]; exact h1
  · refine (semilin_norm_pow_sub_pow (by rw [h.isom]; exact hx) ?_ l).trans h1
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx


open Polynomial in
theorem semilin_root {l : ℕ} (hR : ResClosed K l) {m : ℕ} (hm : 2 ≤ m) (a b : K) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) : ∃ x : K, ‖x‖ ≤ 1 ∧ ‖x ^ m + a * x + b‖ ≤ ‖(l : K)‖ := by
  have hdeg : (C a * X + C b : K[X]).degree < (X ^ m : K[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast hm)
  have hmon : (X ^ m + (C a * X + C b) : K[X]).Monic := monic_X_pow_add (by rwa [degree_X_pow] at hdeg)
  have hnat : (X ^ m + (C a * X + C b) : K[X]).natDegree = m := by
    rw [natDegree_add_eq_left_of_degree_lt hdeg, natDegree_X_pow]
  have hco : ∀ i, ‖(X ^ m + (C a * X + C b) : K[X]).coeff i‖ ≤ 1 := by
    intro i
    simp only [coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))) <;> split_ifs <;> simp [ha, hb]
  obtain ⟨x, hx, hev⟩ := hR _ hmon (by omega) hco
  refine ⟨x, hx, ?_⟩
  simpa [add_assoc] using hev


open Filter Topology in
theorem lang_semilinear {l : ℕ} {σ : K →+* K} (h : FrobField K l σ) (hR : ResClosed K l)
    (c : K) (hc : ‖c‖ = 1) : ∃ ε : K, ‖ε‖ = 1 ∧ ε = c * σ (σ ε) := by
  have hl2 : 2 ≤ l := h.prime.two_le
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr h.prime.ne_zero
  have hl1 := h.norm_l
  have hq4 : 4 ≤ l ^ 2 := by nlinarith

  let P : ℕ → K → Prop := fun n ε => ‖ε‖ = 1 ∧ ‖ε - c * σ (σ ε)‖ ≤ ‖(l : K)‖ ^ (n + 1)
  have h0 : ∃ ε, P 0 ε := by
    obtain ⟨x, hx, hev⟩ := semilin_root hR (m := l ^ 2 - 1) (by omega) 0 (-c⁻¹) (by simp)
      (by rw [norm_neg, hci])
    rw [zero_mul, add_zero, ← sub_eq_add_neg] at hev
    have hx1 : ‖x‖ = 1 := by
      have h1 : ‖x ^ (l ^ 2 - 1)‖ = 1 := by
        have e : x ^ (l ^ 2 - 1) = c⁻¹ + (x ^ (l ^ 2 - 1) - c⁻¹) := by ring
        rw [e, semilin_norm_add_of_lt (by rw [hci]; exact hev.trans_lt hl1), hci]
      rw [norm_pow] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h1
    refine ⟨x, hx1, ?_⟩
    have hxq : x ^ (l ^ 2) = x * x ^ (l ^ 2 - 1) := by
      rw [← pow_succ']; congr 1; omega
    have e : x - c * σ (σ x) = -(c * x) * (x ^ (l ^ 2 - 1) - c⁻¹) - c * (σ (σ x) - x ^ (l ^ 2)) := by
      rw [hxq]
      linear_combination (-x) * hcc
    rw [e, zero_add, pow_one]
    refine semilin_norm_sub_le ?_ ?_
    · rw [norm_mul, norm_neg, norm_mul, hc, hx1, one_mul, one_mul]; exact hev
    · rw [norm_mul, hc, one_mul]; exact h.norm_sq_sub_pow_le x hx
  have hstep : ∀ n ε, P n ε → ∃ ε', P (n + 1) ε' ∧ ‖ε' - ε‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
    rintro n ε ⟨hε1, hε2⟩
    have hlam0 : (l : K) ^ (n + 1) ≠ 0 := pow_ne_zero _ hl0
    have hnl : ‖(l : K) ^ (n + 1)‖ = ‖(l : K)‖ ^ (n + 1) := norm_pow _ _
    have hsm : ‖(l : K)‖ ^ (n + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hl1 (Nat.succ_ne_zero n)
    obtain ⟨ρ, hρ⟩ : ∃ ρ, ε - c * σ (σ ε) = (l : K) ^ (n + 1) * ρ :=
      ⟨(ε - c * σ (σ ε)) / (l : K) ^ (n + 1), by field_simp⟩
    have hρ1 : ‖ρ‖ ≤ 1 := by
      have hpos : 0 < ‖(l : K)‖ ^ (n + 1) := by rw [← hnl]; exact norm_pos_iff.mpr hlam0
      rw [hρ, norm_mul, hnl] at hε2
      exact le_of_mul_le_mul_left (by rwa [mul_one]) hpos
    obtain ⟨δ, hδ, hev⟩ := semilin_root hR (m := l ^ 2) (by omega) (-c⁻¹) (-(c⁻¹ * ρ))
      (by rw [norm_neg, hci]) (by rw [norm_neg, norm_mul, hci, one_mul]; exact hρ1)
    have hσl : σ (σ ((l : K) ^ (n + 1))) = (l : K) ^ (n + 1) := by simp [map_pow, map_natCast]
    have hlδ : ‖(l : K) ^ (n + 1) * δ‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
      rw [norm_mul, hnl]
      calc ‖(l : K)‖ ^ (n + 1) * ‖δ‖ ≤ ‖(l : K)‖ ^ (n + 1) * 1 :=
            mul_le_mul_of_nonneg_left hδ (by positivity)
        _ = _ := mul_one _
    refine ⟨ε + (l : K) ^ (n + 1) * δ, ⟨?_, ?_⟩, ?_⟩
    · rw [semilin_norm_add_of_lt (by rw [hε1]; exact hlδ.trans_lt hsm), hε1]
    · have e : ε + (l : K) ^ (n + 1) * δ - c * σ (σ (ε + (l : K) ^ (n + 1) * δ)) =
          (l : K) ^ (n + 1) * (-c * (δ ^ (l ^ 2) + -c⁻¹ * δ + -(c⁻¹ * ρ)) - c * (σ (σ δ) - δ ^ (l ^ 2))) := by
        rw [map_add (f := _), map_add (f := _), map_mul, map_mul, hσl]
        linear_combination hρ - ((l : K) ^ (n + 1) * ρ + (l : K) ^ (n + 1) * δ) * hcc
      rw [e, norm_mul, hnl, pow_succ ‖(l : K)‖ (n + 1)]
      refine mul_le_mul_of_nonneg_left (semilin_norm_sub_le ?_ ?_) (by positivity)
      · rw [norm_mul, norm_neg, hc, one_mul]; exact hev
      · rw [norm_mul, hc, one_mul]; exact h.norm_sq_sub_pow_le δ hδ
    · rw [add_sub_cancel_left]; exact hlδ

  obtain ⟨ε0, hε0⟩ := h0
  choose g hg using hstep
  let v : (n : ℕ) → {x : K // P n x} := fun n =>
    Nat.rec (motive := fun n => {x : K // P n x}) ⟨ε0, hε0⟩
      (fun n ih => ⟨g n ih.1 ih.2, (hg n ih.1 ih.2).1⟩) n
  let u : ℕ → K := fun n => (v n).1
  have hu : ∀ n, P n (u n) := fun n => (v n).2
  have hud : ∀ n, ‖u (n + 1) - u n‖ ≤ ‖(l : K)‖ ^ (n + 1) := fun n => (hg n (u n) (hu n)).2
  have hcau : CauchySeq u := by
    refine cauchySeq_of_le_geometric ‖(l : K)‖ ‖(l : K)‖ hl1 fun n => ?_
    rw [dist_eq_norm, norm_sub_rev, ← pow_succ']
    exact hud n
  obtain ⟨ε, hlim⟩ := cauchySeq_tendsto_of_complete hcau
  have hσc : Continuous σ := ((AddMonoidHomClass.isometry_iff_norm σ).mpr h.isom).continuous
  have hres : Filter.Tendsto (fun n => u n - c * σ (σ (u n))) Filter.atTop (nhds (ε - c * σ (σ ε))) :=
    hlim.sub ((((hσc.comp hσc).tendsto ε).comp hlim).const_mul c)
  have hres0 : Filter.Tendsto (fun n => u n - c * σ (σ (u n))) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun n => (hu n).2.trans (pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ n)))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl1)
  have hn : Filter.Tendsto (fun n => ‖u n‖) Filter.atTop (nhds ‖ε‖) := hlim.norm
  have hconst : (fun n => ‖u n‖) = fun _ => (1 : ℝ) := funext fun n => (hu n).1
  rw [hconst] at hn
  exact ⟨ε, tendsto_nhds_unique hn tendsto_const_nhds, sub_eq_zero.mp (tendsto_nhds_unique hres hres0)⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

