module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesCoeffsInIdealPowEqFactorialMul
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DPSeries

section SlopeTestRemainingChoices

variable {B : Type} [CommRing B] {τ : Type}

def coeffIdeal (J : Ideal B) (τ : Type) : Ideal (MvPowerSeries τ B) where
  carrier := {f | ∀ α, coeff α f ∈ J}
  add_mem' {a b} ha hb α := by
    rw [map_add (f := _)]
    exact J.add_mem (ha α) (hb α)
  zero_mem' α := by simp
  smul_mem' c f hf α := by
    classical
    rw [smul_eq_mul, coeff_mul]
    exact J.sum_mem fun x _ => J.mul_mem_left _ (hf _)

theorem coeff_pow_congr {f g : MvPowerSeries τ B} {β : τ →₀ ℕ}
    (h : ∀ α ≤ β, coeff α f = coeff α g) : ∀ n, ∀ α ≤ β, coeff α (f ^ n) = coeff α (g ^ n) := by
  classical
  intro n
  induction n with
  | zero => intro α _; rfl
  | succ n ih =>
    intro α hα
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h1 : x.1 ≤ β := le_trans (by rw [← hx]; exact le_self_add) hα
    have h2 : x.2 ≤ β := le_trans (by rw [← hx]; exact le_add_self) hα
    rw [ih _ h1, h _ h2]

variable (p : ℕ) (J : Ideal B)

def HasPDiv (f : MvPowerSeries τ B) : Prop :=
  f ∈ coeffIdeal J τ ∧ ∃ y ∈ coeffIdeal J τ, f ^ p = (p : MvPowerSeries τ B) * y

variable {p J}

theorem hasPDiv_add (hp : p.Prime) {a b : MvPowerSeries τ B} (ha : HasPDiv p J a)
    (hb : HasPDiv p J b) : HasPDiv p J (a + b) := by
  obtain ⟨ha, ya, hya, hpa⟩ := ha
  obtain ⟨hb, yb, hyb, hpb⟩ := hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp a b
  refine ⟨(coeffIdeal J τ).add_mem ha hb, ya + yb + a * b * r, ?_, ?_⟩
  · exact (coeffIdeal J τ).add_mem ((coeffIdeal J τ).add_mem hya hyb)
      ((coeffIdeal J τ).mul_mem_right _ ((coeffIdeal J τ).mul_mem_right _ ha))
  · rw [hr, hpa, hpb]; ring

theorem hasPDiv_monomial (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (α : τ →₀ ℕ) {c : B}
    (hc : c ∈ J) : HasPDiv p J (monomial α c) := by
  classical
  obtain ⟨y, hy, hcy⟩ := hJ c hc
  refine ⟨fun γ => ?_, monomial (p • α) y, fun γ => ?_, ?_⟩
  · rw [coeff_monomial]; split_ifs
    · exact hc
    · exact J.zero_mem
  · rw [coeff_monomial]; split_ifs
    · exact hy
    · exact J.zero_mem
  · rw [monomial_pow, hcy]
    ext γ
    rw [coeff_monomial, ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul, coeff_monomial]
    split_ifs <;> simp

theorem hasPDiv_sum (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y)
    (c : (τ →₀ ℕ) → B) (hc : ∀ α, c α ∈ J) (s : Finset (τ →₀ ℕ)) :
    HasPDiv p J (∑ α ∈ s, monomial α (c α)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (coeffIdeal J τ).zero_mem, 0, (coeffIdeal J τ).zero_mem, ?_⟩
    simp [hp.ne_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasPDiv_add hp (hasPDiv_monomial hJ a (hc a)) ih

theorem pow_prime_eq (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y)
    {w : MvPowerSeries τ B} (hw : w ∈ coeffIdeal J τ) :
    ∃ y ∈ coeffIdeal J τ, w ^ p = (p : MvPowerSeries τ B) * y := by
  classical
  have key : ∀ β : τ →₀ ℕ, ∃ c ∈ J, coeff β (w ^ p) = p * c := by
    intro β
    set w' : MvPowerSeries τ B := ∑ α ∈ Finset.Iic β, monomial α (coeff α w) with hw'
    have hagree : ∀ α ≤ β, coeff α w = coeff α w' := by
      intro α hα
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hw', map_sum]
      simp_rw [coeff_monomial]
      rw [Finset.sum_ite_eq]
      simp [Finset.mem_Iic.mpr hα]
    obtain ⟨_, y, hy, hpy⟩ := hasPDiv_sum hp hJ (fun α => coeff α w) hw (Finset.Iic β)
    refine ⟨coeff β y, hy β, ?_⟩
    have hpy' : w' ^ p = (p : MvPowerSeries τ B) * y := hpy
    rw [coeff_pow_congr hagree p β le_rfl, hpy',
      ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul]
  choose c hcJ hc using key
  let y : MvPowerSeries τ B := fun β => c β
  have hy : ∀ β, coeff β y = c β := fun _ => rfl
  refine ⟨y, fun β => by rw [hy]; exact hcJ β, ?_⟩
  ext β
  rw [hc, ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul, hy]

theorem pow_eq_pow_factorization_mul (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) :
    ∀ n : ℕ, 0 < n → ∀ w ∈ coeffIdeal J τ, ∃ y ∈ coeffIdeal J τ,
      w ^ n = (p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn w hw
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hmn : m < p * m := by nlinarith [hp.two_le]
    obtain ⟨z, hz, hwz⟩ := pow_prime_eq hp hJ hw
    obtain ⟨y, hy, hzy⟩ := ih m hmn hm z hz
    refine ⟨y, hy, ?_⟩
    rw [Nat.factorization_factorial_mul hp, pow_mul, hwz, mul_pow, hzy]
    ring
  · rcases Nat.lt_or_ge n 2 with h | h
    · have h1 : n = 1 := by omega
      subst h1
      exact ⟨w, hw, by simp⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨y, hy, hwy⟩ := ih k (by omega) (by omega) w hw
      refine ⟨w * y, (coeffIdeal J τ).mul_mem_left _ hy, ?_⟩
      have hv : (k + 1).factorial.factorization p = k.factorial.factorization p := by
        rw [Nat.factorial_succ, Nat.factorization_mul (Nat.succ_ne_zero k)
          (Nat.factorial_ne_zero k), Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hpn, zero_add]
      rw [hv, pow_succ, hwy]; ring

end SlopeTestRemainingChoices

theorem pow_eq_factorial_mul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B,
    (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (τ : Type) (w : MvPowerSeries τ B),
    (∀ α, coeff α w ∈ J) → ∀ n : ℕ, 0 < n → ∃ y : MvPowerSeries τ B,
    (∀ α, coeff α y ∈ J) ∧ w ^ n = (n.factorial : MvPowerSeries τ B) * y := by
  intro p hpf B O Q _ _ _ _ θ hF J hJ τ w hw n hn
  have hp : p.Prime := hpf.out
  obtain ⟨y, hy, hwy⟩ := pow_eq_pow_factorization_mul hp hJ n hn w hw
  obtain ⟨c, hc_def⟩ : ∃ c, c = ordCompl[p] n.factorial := ⟨_, rfl⟩
  have hcop : Nat.Coprime c p := by
    rw [hc_def]; exact (Nat.coprime_ordCompl hp (Nat.factorial_ne_zero n)).symm
  obtain ⟨u, hu⟩ := hF.unit_coprime c hcop
  refine ⟨C (↑u⁻¹ : B) * y, (coeffIdeal J τ).mul_mem_left _ hy, ?_⟩
  have hnat : p ^ (n.factorial.factorization p) * c = n.factorial := by
    rw [hc_def]; exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hfac : (p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * (c : MvPowerSeries τ B) =
      (n.factorial : MvPowerSeries τ B) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, hnat]
  have hcu : (c : MvPowerSeries τ B) * C (↑u⁻¹ : B) = 1 := by
    rw [← map_natCast (C (σ := τ) (R := B)) c, ← hu, ← map_mul, Units.mul_inv, map_one]
  rw [hwy, ← hfac]
  linear_combination (-((p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * y)) * hcu

end GlobalTheory.DPSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesLiftQuotient
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem mvPowerSeries_lift_quotient :
    ∀ (O σ : Type) [CommRing O] (I : Ideal O), (∀ g : MvPowerSeries σ (O ⧸ I), ∃ f : MvPowerSeries σ O, map (Ideal.Quotient.mk I) f = g ∧ (constantCoeff g = 0 → constantCoeff f = 0)) ∧ (∀ f : MvPowerSeries σ O, map (Ideal.Quotient.mk I) f = 0 ↔ ∀ α, coeff α f ∈ I) ∧ ∀ (a : O) (f : MvPowerSeries σ O), (∀ α, a ∣ coeff α f) ↔ ∃ g, f = a • g := by
  classical
  intro O σ _ I
  refine ⟨?_, ?_, ?_⟩
  · intro g
    let s : O ⧸ I → O := fun x => if x = 0 then 0 else Quotient.out x
    have hs : ∀ x, Ideal.Quotient.mk I (s x) = x := by
      intro x
      by_cases hx : x = 0
      · simp [s, hx]
      · simp only [s, if_neg hx]
        exact Ideal.Quotient.mk_out x
    let f : MvPowerSeries σ O := fun α => s (coeff α g)
    refine ⟨f, ?_, ?_⟩
    · ext α
      rw [coeff_map]
      exact hs _
    · intro h0
      have : coeff (0 : σ →₀ ℕ) g = 0 := by simpa [coeff_zero_eq_constantCoeff_apply] using h0
      rw [← coeff_zero_eq_constantCoeff_apply]
      show s (coeff 0 g) = 0
      simp [s, this]
  · intro f
    constructor
    · intro h α
      have := congrArg (coeff α) h
      rw [coeff_map, map_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    · intro h
      ext α
      rw [coeff_map, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h α)
  · intro a f
    constructor
    · intro h
      choose c hc using h
      let g : MvPowerSeries σ O := fun α => c α
      have hg : ∀ α, coeff α g = c α := fun _ => rfl
      refine ⟨g, ?_⟩
      ext α
      rw [coeff_smul, hg, hc α]
    · rintro ⟨g, rfl⟩ α
      rw [coeff_smul]
      exact dvd_mul_right _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesSubstCoeffSubMemIdeal
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.SubstMod

theorem order_prod_sub_prod {R τ ι : Type} [CommRing R] (s : Finset ι)
    (a b : ι → MvPowerSeries τ R) (k : ι → ℕ)
    (ha : ∀ i ∈ s, (k i : ℕ∞) ≤ (a i).order) (hb : ∀ i ∈ s, (k i : ℕ∞) ≤ (b i).order)
    (hab : ∀ i ∈ s, (k i : ℕ∞) + 1 ≤ (a i - b i).order) :
    (∑ i ∈ s, (k i : ℕ∞)) + 1 ≤ (∏ i ∈ s, a i - ∏ i ∈ s, b i).order := by
  first
  | exact @_root_.GlobalTheory.OrderProductDifference.target
  | exact _root_.GlobalTheory.OrderProductDifference.target
  | (apply _root_.GlobalTheory.OrderProductDifference.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrderProductDifference.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrderProductDifference.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrderProductDifference.target ..)

theorem order_pow_sub_pow {R τ : Type} [CommRing R] (u l : MvPowerSeries τ R)
    (hu : constantCoeff u = 0) (hl : constantCoeff l = 0) (hul : (2 : ℕ∞) ≤ (u - l).order)
    (n : ℕ) : (n : ℕ∞) + 1 ≤ (u ^ n - l ^ n).order := by
  have := order_prod_sub_prod (Finset.range n) (fun _ => u) (fun _ => l) (fun _ => 1)
    (fun _ _ => by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hu)
    (fun _ _ => by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hl)
    (fun _ _ => by simpa [one_add_one_eq_two] using hul)
  simpa [Finset.prod_const] using this

theorem order_monoProd_sub {R σ τ : Type} [CommRing R] (u l : σ → MvPowerSeries τ R)
    (hu : ∀ s, constantCoeff (u s) = 0) (hl : ∀ s, constantCoeff (l s) = 0)
    (hul : ∀ s, (2 : ℕ∞) ≤ (u s - l s).order) (α : σ →₀ ℕ) :
    (α.degree : ℕ∞) + 1 ≤
      ((α.prod fun s e => u s ^ e) - α.prod fun s e => l s ^ e).order := by
  have := order_prod_sub_prod α.support (fun s => u s ^ α s) (fun s => l s ^ α s) α
    (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hu s))
    (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hl s))
    (fun s _ => order_pow_sub_pow _ _ (hu s) (hl s) (hul s) _)
  rw [Finsupp.degree_apply]
  push_cast
  exact this

theorem subst_coeff_sub_mem : ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ]
    (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) →
    (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) →
    ∀ (m : ℕ) (c : MvPowerSeries σ Q), (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) →
    ∀ (w : τ →₀ ℕ), w.degree = m →
      ∃ r ∈ N, coeff w (subst (up Q u) c) - coeff w (subst (up Q ℓ) c) = algebraMap B Q r := by
  intro B Q σ τ _ _ _ _ N u ℓ hu hl m c hc w hw
  have hℓ : ∀ s, constantCoeff (ℓ s) = 0 := fun s => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← hl s 0 (by simp), coeff_zero_eq_constantCoeff_apply,
      hu s]
  have hul : ∀ s, (2 : ℕ∞) ≤ (u s - ℓ s).order := fun s =>
    nat_le_order (n := 2) fun β hβ => by
      rw [map_sub, hl s β (by omega), sub_self]
  have hU : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun s => by
    simp [up, hu s]
  have hL : HasSubst (up Q ℓ) := hasSubst_of_constantCoeff_zero fun s => by
    simp [up, hℓ s]
  rw [coeff_subst hU, coeff_subst hL,
    ← finsum_sub_distrib (coeff_subst_finite hU c w) (coeff_subst_finite hL c w)]
  refine finsum_induction (fun x : Q => ∃ r ∈ N, x = algebraMap B Q r) ⟨0, N.zero_mem, by simp⟩
    (fun x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩ => ⟨r + t, N.add_mem hr ht, by rw [hx, hy, map_add (f := _)]⟩)
    fun α => ?_
  have hprod : ∀ v : σ → MvPowerSeries τ B, (α.prod fun s e => up Q v s ^ e) =
      map (algebraMap B Q) (α.prod fun s e => v s ^ e) := by
    intro v
    simp only [up, Finsupp.prod, map_prod, map_pow]
  rw [hprod u, hprod ℓ, coeff_map, coeff_map, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub,
    ← map_sub]
  by_cases h : α.degree < m
  · obtain ⟨b, hb, hcb⟩ := hc α h
    exact ⟨b * _, N.mul_mem_right _ hb, by rw [hcb, map_mul]⟩
  · have h0 : coeff w ((α.prod fun s e => u s ^ e) - α.prod fun s e => ℓ s ^ e) = 0 := by
      refine coeff_of_lt_order (lt_of_lt_of_le ?_ (order_monoProd_sub u ℓ hu hℓ hul α))
      have : w.degree ≤ α.degree := by omega
      exact_mod_cast Nat.lt_succ_of_le this
    exact ⟨0, N.zero_mem, by rw [h0, map_zero, mul_zero]⟩

end GlobalTheory.SubstMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmulSucc
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.MapNMul

theorem cc_subst {R : Type} [CommRing R] {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem nmul_succ {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (k : ℕ) :
    nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem cc_nmul {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) : ∀ (k : ℕ) (i : Fin d), constantCoeff (nmul μ k i) = 0 := by
  intro k
  induction k with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ]
    simp only [op, at2]
    rw [cc_subst (fun s => by cases s <;> simp [ih]), hμ]

theorem map_nmul (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) :
    ∀ (k : ℕ) (i : Fin d), map φ (nmul μ k i) = nmul (fun j => map φ (μ j)) k i := by
  intro k
  induction k with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ, nmul_succ]
    simp only [op, at2]
    have hs : HasSubst (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R))) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [cc_nmul μ hμ]
    rw [map_subst hs]
    congr 1
    funext s
    cases s <;> simp [ih]

end GlobalTheory.MapNMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneTmulQuotReduction
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem one_tmul_quot_reduction :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (I : Ideal O),
      (∀ y : (O ⧸ I) ⊗[O] M, ∃ b : M, y = 1 ⊗ₜ b) ∧
      (∀ b : M, (1 : O ⧸ I) ⊗ₜ[O] b = 0 ↔ b ∈ I • (⊤ : Submodule O M)) ∧
      ∀ (a : O) (b : M), b ∈ Ideal.span {a} • (⊤ : Submodule O M) ↔ ∃ z, b = a • z := by
  intro O M _ _ _ I
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule O M))
      (TensorProduct.quotTensorEquivQuotSMul M I y)
    refine ⟨b, ?_⟩
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk I b, hb, LinearEquiv.symm_apply_apply]
  · intro b
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
  · intro a b
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, -, hz⟩
      exact ⟨z, hz.symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, Submodule.mem_top, rfl⟩

end GlobalTheory.PDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousMvPowerSeriesAlgHomExt
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PadicMvPowerSeriesExt

theorem eq_zero_of_forall_pow_dvd (p : ℕ) (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (A : Type) [CommRing A] [Algebra O A]
    [Module.Projective O A] (x : A) (hx : ∀ m : ℕ, (p : A) ^ m ∣ x) : x = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O A)
  have h0 : s x = 0 := by
    ext a
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : O)}) O) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    obtain ⟨y, hy⟩ := hx n
    have hxy : x = ((p : O) ^ n) • y := by
      rw [Algebra.smul_def, map_pow, map_natCast, hy]
    rw [hxy, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have h1 := LinearMap.congr_fun hs x
  rw [LinearMap.comp_apply, h0, map_zero, LinearMap.id_apply] at h1
  exact h1.symm

theorem algHom_ext : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] (F F' : MvPowerSeries σ O →ₐ[O] A), (∀ i, F (X i) = F' (X i)) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F f) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F' f) → F = F' := by
  classical
  intro p O _ _ σ _ A _ _ _ _ F F' hX hF hF'
  apply AlgHom.ext
  intro f
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pow_dvd p O A _ fun m => ?_
  obtain ⟨N₁, hN₁⟩ := hF m
  obtain ⟨N₂, hN₂⟩ := hF' m
  set g := MvPowerSeries.trunc' O (Finsupp.equivFunOnFinite.symm fun _ : σ => max N₁ N₂) f with hg
  have hpoly : F.comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      F'.comp (MvPolynomial.coeToMvPowerSeries.algHom O) :=
    MvPolynomial.algHom_ext fun i => by simpa using hX i
  have hg' : F (g : MvPowerSeries σ O) = F' (g : MvPowerSeries σ O) := by
    simpa using DFunLike.congr_fun hpoly g
  have hlow : ∀ α : σ →₀ ℕ, α.degree < max N₁ N₂ →
      MvPowerSeries.coeff α (f - (g : MvPowerSeries σ O)) = 0 := by
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, hg, MvPowerSeries.coeff_trunc', if_pos, sub_self]
    intro i
    exact (Finsupp.le_degree i α).trans (by simpa using hα.le)
  have hdiff : F f - F' f = F (f - (g : MvPowerSeries σ O)) - F' (f - (g : MvPowerSeries σ O)) := by
    rw [map_sub, map_sub, hg']
    ring
  rw [hdiff]
  exact dvd_sub (hN₁ _ fun α h => hlow α (lt_of_lt_of_le h (le_max_left _ _)))
    (hN₂ _ fun α h => hlow α (lt_of_lt_of_le h (le_max_right _ _)))

end GlobalTheory.PadicMvPowerSeriesExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveDvdOfForallDualDvd
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem projective_dvd_of_forall_dual_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Projective O M] (a : O) (b : M),
      (∀ φ : Module.Dual O M, a ∣ φ b) → ∃ z, b = a • z := by
  intro O M _ _ _ _ a b h
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective O M)
  have hc : ∀ i : M, a ∣ s b i := fun i => h ((Finsupp.lapply i).comp s)
  choose c hc using hc
  refine ⟨∑ i ∈ (s b).support, c i • i, ?_⟩
  have hb : Finsupp.linearCombination O id (s b) = b := by
    simpa using LinearMap.congr_fun hs b
  rw [Finset.smul_sum]
  conv_lhs => rw [← hb]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← hc i]
  rfl

end GlobalTheory
end

