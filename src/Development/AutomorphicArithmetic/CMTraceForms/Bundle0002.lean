module

public import Mathlib
public import Development.AutomorphicArithmetic.CMTraceForms.Places

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CMTraceForms.CmDatumSplitPlacesConjStable
section
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth

private theorem bar_rt' {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.bar H.rt = -H.rt := by
  have h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h2 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    have h3 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h2] at h3
    have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa using this
    have h5 : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h3.symm
    have h6 := congrArg Complex.re h4
    simp [sq, h5] at h6
    have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  · exact h

private theorem host_bar_w0_eq_one_sub_w0 {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.bar H.w0 = 1 - H.w0 := by
  have h := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, bar_rt', map_ofNat] at h
  have h2 : (2 : 𝓞 E) * H.bar H.w0 = 2 * (1 - H.w0) := by linear_combination h + H.two_weight_eq_one_add_root
  exact mul_left_cancel₀ two_ne_zero h2

private theorem exists_beta {p : ℕ} (hp : p.Prime) {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (hs : SplitAt H.d p) : ¬ p ∣ H.d ∧ ∃ (β γ : 𝓞 E) (n t : ℕ), H.bar β = γ ∧ H.bar γ = β ∧ γ * β = (n : 𝓞 E) ∧
      β + γ = (t : 𝓞 E) ∧ p ∣ n ∧ ¬ p ∣ t := by
  haveI := Fact.mk hp
  have hdm := H.d_mod
  by_cases hp2 : p = 2
  · subst hp2
    have hpd : ¬ 2 ∣ H.d := by omega
    refine ⟨hpd, H.w0, H.bar H.w0, (H.d + 1) / 4, 1, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [host_bar_w0_eq_one_sub_w0, map_sub, map_one, host_bar_w0_eq_one_sub_w0]
      ring
    · have hn4 : 4 * ((H.d + 1) / 4) = H.d + 1 := by omega
      have hn4' : (4 : 𝓞 E) * (((H.d + 1) / 4 : ℕ) : 𝓞 E) = (H.d : 𝓞 E) + 1 := by
        exact_mod_cast hn4
      rw [host_bar_w0_eq_one_sub_w0]
      apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
      linear_combination (-(2 * H.w0 - 1 + H.rt)) * H.two_weight_eq_one_add_root - H.rt_sq - hn4'
    · rw [host_bar_w0_eq_one_sub_w0]
      push_cast
      ring
    · omega
    · omega
  · have hjac : jacobiSym (-(H.d : ℤ)) p = 1 := by
      rcases hs with h | h
      · exact absurd h hp2
      · exact h
    have hleg : legendreSym p (-(H.d : ℤ)) = 1 := by
      rw [jacobiSym.legendreSym.to_jacobiSym]
      exact hjac
    have hpd : ¬ p ∣ H.d := by
      intro hdiv
      have h0 : ((-(H.d : ℤ) : ℤ) : ZMod p) = 0 := by
        push_cast
        rw [(ZMod.natCast_eq_zero_iff _ _).mpr hdiv, neg_zero]
      rw [(legendreSym.eq_zero_iff p _).mpr h0] at hleg
      exact zero_ne_one hleg
    have hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      apply hpd
      rw [← ZMod.natCast_eq_zero_iff]
      have : -((H.d : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      exact neg_eq_zero.mp this
    obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hne).mp hleg
    obtain ⟨a, hra⟩ : ∃ a : ℕ, (a : ZMod p) = r := ⟨r.val, ZMod.natCast_zmod_val r⟩
    have hn : p ∣ a ^ 2 + H.d := by
      rw [← ZMod.natCast_eq_zero_iff]
      have hr' : -((H.d : ℕ) : ZMod p) = r * r := by exact_mod_cast hr
      push_cast
      rw [hra, sq, ← hr']
      ring
    have ht : ¬ p ∣ 2 * a := by
      intro h2a
      rcases (Nat.Prime.dvd_mul hp).mp h2a with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      · apply hne
        have : r = 0 := by
          rw [← hra]
          exact (ZMod.natCast_eq_zero_iff _ _).mpr h
        rw [hr, this, mul_zero]
    refine ⟨hpd, (a : 𝓞 E) + H.rt, (a : 𝓞 E) - H.rt, a ^ 2 + H.d, 2 * a, ?_, ?_, ?_, ?_, hn, ht⟩
    · rw [map_add (f := _), map_natCast, bar_rt']
      ring
    · rw [map_sub, map_natCast, bar_rt']
      ring
    · push_cast
      linear_combination (-1 : 𝓞 E) * H.rt_sq
    · push_cast
      ring

theorem UpperTheory.cmDatum_splitPlaces_conj_stable :
    ∀ (p : ℕ), p.Prime → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), SplitAt H.d p →
      ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ¬ IsUnit (p : O) →
      (∀ σ : 𝓞 E →+* O, IsUnit (σ H.w0 - σ (H.bar H.w0))) ∧ ∀ x : O, x ≠ 0 → ∃ N : ℕ, v (N : C) < v (algebraMap O C x) ∧
        ∀ σ : 𝓞 E →+* O, ∃ a : 𝓞 E, H.bar a * a = (N : 𝓞 E) ∧ v (algebraMap O C (σ a - 1)) < v (algebraMap O C x) := by
  intro p hp E _ _ _ H hs C _ _ v O _ _ hv hpu
  haveI := Fact.mk hp
  obtain ⟨hpd, β, γ, n, t, hβ, hγ, hn, ht, hpn, hpt⟩ := exists_beta hp H hs
  have vle : ∀ z : ℤ, v (z : C) ≤ 1 := fun z => by
    have h := hv.map_le_one (z : O)
    rwa [map_intCast] at h
  have vp : v (p : C) < 1 := by
    have h1 := hv.map_le_one (p : O)
    rw [map_natCast] at h1
    refine lt_of_le_of_ne h1 ?_
    intro h
    apply hpu
    apply hv.isUnit_of_one'
    rw [map_natCast]
    exact h
  have vcop : ∀ m : ℕ, ¬ p ∣ m → v (m : C) = 1 := by
    intro m hm
    have hle : v (m : C) ≤ 1 := by exact_mod_cast vle m
    refine le_antisymm hle ?_
    by_contra hlt
    push_neg at hlt
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
    have hb := Nat.gcd_eq_gcd_ab p m
    rw [Nat.Coprime.gcd_eq_one hcop] at hb
    have h1 : (1 : C) = (p : C) * (Nat.gcdA p m : C) + (m : C) * (Nat.gcdB p m : C) := by
      exact_mod_cast hb
    have h2 : v (1 : C) < 1 := by
      rw [h1]
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left (by positivity) vp (vle _)
      · rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left (by positivity) hlt (vle _)
    simp at h2
  have vn : v (n : C) ≤ v (p : C) := by
    have h := hv.le_of_dvd (Nat.cast_dvd_cast hpn : (p : O) ∣ (n : O))
    simpa only [map_natCast] using h
  have key : ∀ (b g : O), b * g = (n : O) → b + g = (t : O) → v (algebraMap O C b) = 1 →
      ∀ k : ℕ, (p : O) ^ (k + 1) ∣ b ^ ((p - 1) * p ^ k) - 1 := by
    intro b g hbg hbgt hb k
    have hvn : v (algebraMap O C g) = v (n : C) := by
      rw [← map_natCast (algebraMap O C) n, ← hbg, map_mul, map_mul, hb, one_mul]
    have hpg : (p : O) ∣ g := by
      apply hv.dvd_of_le
      rw [hvn, map_natCast (algebraMap O C)]
      exact vn
    have hpb : (p : O) ∣ b - t := by
      have h : b - t = -g := by
        rw [← hbgt]
        ring
      rw [h]
      exact (dvd_neg).mpr hpg
    have h1 : (p : O) ∣ b ^ (p - 1) - (t : O) ^ (p - 1) :=
      dvd_trans hpb (sub_dvd_pow_sub_pow _ _ _)
    have h2 := dvd_sub_pow_of_dvd_sub h1 k
    rw [← pow_mul, ← pow_mul] at h2
    have hcop : Nat.Coprime t (p ^ (k + 1)) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpt).symm
    have h3 := Nat.ModEq.pow_totient hcop
    rw [Nat.totient_prime_pow_succ hp k] at h3
    have h4 := map_dvd (Int.castRingHom O) h3.symm.dvd
    push_cast [eq_intCast] at h4
    rw [mul_comm (p ^ k)] at h4
    have h5 : b ^ ((p - 1) * p ^ k) - 1 = (b ^ ((p - 1) * p ^ k) - (t : O) ^ ((p - 1) * p ^ k)) +
        ((t : O) ^ ((p - 1) * p ^ k) - 1) := by ring
    rw [h5]
    exact dvd_add h2 h4
  refine ⟨?_, ?_⟩
  · intro σ
    have hw : σ H.w0 - σ (H.bar H.w0) = σ H.rt := by
      rw [host_bar_w0_eq_one_sub_w0, ← map_sub]
      congr 1
      linear_combination H.two_weight_eq_one_add_root
    rw [hw]
    have hdu : IsUnit (H.d : O) := hv.isUnit_of_one' (by rw [map_natCast]; exact vcop _ hpd)
    have hsq : σ H.rt ^ 2 = -(H.d : O) := by
      rw [← map_pow, H.rt_sq, map_neg, map_natCast]
    have hu : IsUnit (σ H.rt ^ 2) := by
      rw [hsq]
      exact hdu.neg
    exact (isUnit_pow_iff two_ne_zero).mp hu
  · intro x hx
    have hvx : 0 < v (algebraMap O C x) := hv.valuation_pos_iff_ne_zero.mpr hx
    obtain ⟨k, hk⟩ := NNReal.exists_pow_lt_of_lt_one hvx vp
    have hkM : k + 1 ≤ (p - 1) * p ^ k := by
      have h1 : k < p ^ k := Nat.lt_pow_self hp.one_lt
      have h2 : 1 ≤ p - 1 := by
        have := hp.two_le
        omega
      nlinarith
    refine ⟨n ^ ((p - 1) * p ^ k), ?_, ?_⟩
    · calc v (((n ^ ((p - 1) * p ^ k) : ℕ)) : C) = v (n : C) ^ ((p - 1) * p ^ k) := by
            rw [Nat.cast_pow, map_pow]
        _ ≤ v (p : C) ^ ((p - 1) * p ^ k) := pow_le_pow_left₀ (by positivity) vn _
        _ ≤ v (p : C) ^ k := pow_le_pow_of_le_one (by positivity) vp.le (by omega)
        _ < _ := hk
    · intro σ
      have hbg : σ β * σ γ = (n : O) := by
        rw [← map_mul, mul_comm β γ, hn, map_natCast]
      have hsum : σ β + σ γ = (t : O) := by
        rw [← map_add (f := _), ht, map_natCast]
      have close : ∀ b : O, (p : O) ^ (k + 1) ∣ b ^ ((p - 1) * p ^ k) - 1 →
          v (algebraMap O C (b ^ ((p - 1) * p ^ k) - 1)) < v (algebraMap O C x) := by
        intro b hb
        calc v (algebraMap O C (b ^ ((p - 1) * p ^ k) - 1))
            ≤ v (algebraMap O C ((p : O) ^ (k + 1))) := hv.le_of_dvd hb
          _ = v (p : C) ^ (k + 1) := by rw [map_pow, map_natCast, map_pow]
          _ ≤ v (p : C) ^ k := pow_le_pow_of_le_one (by positivity) vp.le (by omega)
          _ < _ := hk
      have hor : v (algebraMap O C (σ β)) = 1 ∨ v (algebraMap O C (σ γ)) = 1 := by
        by_contra hc
        push_neg at hc
        have h1 : v (algebraMap O C (σ β)) < 1 := lt_of_le_of_ne (hv.map_le_one _) hc.1
        have h2 : v (algebraMap O C (σ γ)) < 1 := lt_of_le_of_ne (hv.map_le_one _) hc.2
        have h3 : v (algebraMap O C (σ β + σ γ)) < 1 := by
          rw [map_add (f := _)]
          exact Valuation.map_add_lt v h1 h2
        rw [hsum, map_natCast, vcop t hpt] at h3
        exact lt_irrefl _ h3
      rcases hor with h | h
      · refine ⟨β ^ ((p - 1) * p ^ k), ?_, ?_⟩
        · rw [map_pow, hβ, ← mul_pow, hn, Nat.cast_pow]
        · rw [map_pow]
          exact close _ (key _ _ hbg hsum h k)
      · refine ⟨γ ^ ((p - 1) * p ^ k), ?_, ?_⟩
        · rw [map_pow, hγ, ← mul_pow, mul_comm β γ, hn, Nat.cast_pow]
        · rw [map_pow]
          exact close _ (key _ _ (by rw [mul_comm]; exact hbg) (by rw [add_comm]; exact hsum) h k)
end

-- bundled from Development.AutomorphicArithmetic.CMTraceForms.ExistsSplitIdempotentOfSplitAt
section
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth

namespace UpperTheory.Depth.SplitIdem

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem cmHost_bar_halfIntegerGenerator (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  have hsq : H.bar H.rt ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have hrt : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exfalso
      have h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h2 := IsCMField.complexEmbedding_complexConj E τ (H.rt : E)
      rw [h1] at h2
      have h3 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        rw [← map_pow]
        have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
        simpa using this
      have h4 : (τ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h2.symm
      have h5 := congrArg Complex.re h3
      simp [sq, h4] at h5
      have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    · exact h
  apply mul_left_cancel₀ (by norm_num : (2 : 𝓞 E) ≠ 0)
  have := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, hrt, map_ofNat] at this
  linear_combination this + H.two_weight_eq_one_add_root

private theorem exists_root_two (k : ℕ) : ∃ β γ : ℤ_[2], β * β = β - 2 * k ∧ γ * (1 - 2 * β) = 1 := by
  have h2 : ‖(2 : ℤ_[2])‖ < 1 := by
    have := PadicInt.norm_p (p := 2)
    simp only [Nat.cast_ofNat] at this
    rw [this]; norm_num
  have hlt : ∀ x : ℤ_[2], ‖2 * x‖ < 1 := fun x => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one x)) h2
  obtain ⟨β, hβ, -⟩ := hensels_lemma (p := 2) (R := ℤ_[2])
    (F := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * (k : ℤ_[2]))) (a := 0) (by
      simpa using hlt k)
  have hu : IsUnit (1 - 2 * β) := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    rw [PadicInt.mem_nonunits]
    exact hlt β
  obtain ⟨γ, hγ⟩ := hu.exists_left_inv
  refine ⟨β, γ, ?_, hγ⟩
  simp only [map_add (f := _), map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply] at hβ
  linear_combination hβ

private theorem exists_root (p : ℕ) [hp : Fact p.Prime] (d k : ℕ) (hk : d + 1 = 8 * k) (hs : SplitAt d p) :
    ∃ β γ : ℤ_[p], β * β = β - 2 * k ∧ γ * (1 - 2 * β) = 1 := by
  by_cases h2 : p = 2
  · subst h2
    exact exists_root_two k
  have hj : jacobiSym (-(d : ℤ)) p = 1 := hs.resolve_left h2
  have hne : ((-(d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro h
    rw [← jacobiSym.legendreSym.to_jacobiSym, (legendreSym.eq_zero_iff p _).2 h] at hj
    exact zero_ne_one hj
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective r
  have ha : (a : ZMod p) ≠ 0 := fun h => hne (by rw [hr, h, mul_zero])
  have h2' : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  have hunit : ∀ n : ℤ, (n : ZMod p) ≠ 0 → ‖(n : ℤ_[p])‖ = 1 := fun n hn => by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hn ?_)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (PadicInt.norm_int_lt_one_iff_dvd n).1 h
  have hlt : ‖((a ^ 2 + d : ℤ) : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    linear_combination -hr
  have hder : ‖((2 * a : ℤ) : ℤ_[p])‖ = 1 := hunit _ (by
    rw [Int.cast_mul]; exact mul_ne_zero h2' ha)
  obtain ⟨α, hα, -⟩ := hensels_lemma (p := p) (R := ℤ_[p])
    (F := Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[p])) (a := (a : ℤ_[p])) (by
      push_cast at hlt hder
      have e1 : Polynomial.aeval (a : ℤ_[p]) (Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[p])) = (a : ℤ_[p]) ^ 2 + d := by
        simp
      have e2 : Polynomial.aeval (a : ℤ_[p])
          (Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[p]))) = 2 * (a : ℤ_[p]) := by
        simp [one_add_one_eq_two]
      rw [e1, e2, hder, one_pow]
      exact hlt)
  simp only [map_add (f := _), map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply] at hα
  obtain ⟨u, hu⟩ := (PadicInt.isUnit_iff.2 (hunit 2 h2')).exists_left_inv
  obtain ⟨v, hv⟩ := (PadicInt.isUnit_iff.2 (hunit _ hne)).exists_left_inv
  push_cast at hu hv
  have hk' : (d : ℤ_[p]) + 1 = 8 * k := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[p]) hk
  refine ⟨u * (1 - α), v * α, ?_, ?_⟩
  · linear_combination u ^ 2 * hα - u ^ 2 * hk' + (u * (1 - α) - 2 * k * (2 * u + 1)) * hu
  · linear_combination hv + v * hα - v * α * (1 - α) * hu

end UpperTheory.Depth.SplitIdem

theorem UpperTheory.exists_splitIdempotent_of_splitAt :
    ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), SplitAt H.d p →
      letI := H.starRing; ∃ (e : ℤ_[p] ⊗[ℤ] 𝓞 E) (α : ℤ_[p]), e * e = e ∧ e ≠ 0 ∧ e ≠ 1 ∧ e + sig p (𝓞 E) e = 1 ∧ α ^ 2 = -(H.d : ℤ_[p]) ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Algebra ℤ_[p] O] (σ : 𝓞 E →+* O),
          (σ ∈ Emb (O := O) e ↔ σ H.rt = algebraMap ℤ_[p] O α) ∧ (σ ∈ Emb (O := O) (1 - e) ↔ σ H.rt = - algebraMap ℤ_[p] O α) := by
  intro p _ E _ _ _ H hs
  letI := H.starRing
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d + 1 = 8 * k := ⟨(H.d + 1) / 8, by have := H.d_mod; omega⟩
  obtain ⟨β, γ, hβ, hγ⟩ := UpperTheory.Depth.SplitIdem.exists_root p H.d k hk hs
  have hw : H.w0 * H.w0 = H.w0 - 2 * k := by
    apply mul_left_cancel₀ (by norm_num : (4 : 𝓞 E) ≠ 0)
    have hk' : (H.d : 𝓞 E) + 1 = 8 * k := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) hk
    linear_combination (2 * H.w0 - 1 + H.rt) * H.two_weight_eq_one_add_root + H.rt_sq - hk'
  let ι : ℤ_[p] →+* ℤ_[p] ⊗[ℤ] 𝓞 E := algebraMap _ _
  let j : 𝓞 E →+* ℤ_[p] ⊗[ℤ] 𝓞 E :=
    (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom
  have hβ' : ι β * ι β = ι β - 2 * k := by
    have := congrArg ι hβ
    simpa only [map_mul, map_sub, map_ofNat, map_natCast] using this
  have hγ' : ι γ * (1 - 2 * ι β) = 1 := by
    have := congrArg ι hγ
    simpa only [map_mul, map_sub, map_ofNat, map_one] using this
  have hw' : j H.w0 * j H.w0 = j H.w0 - 2 * k := by
    have := congrArg j hw
    simpa only [map_mul, map_sub, map_ofNat, map_natCast] using this
  have hsι : ∀ x, sig p (𝓞 E) (ι x) = ι x := fun x => (sig p (𝓞 E)).commutes x
  have hsj : sig p (𝓞 E) (j H.w0) = 1 - j H.w0 := by
    have h1 : sig p (𝓞 E) (j H.w0) = j (H.bar H.w0) := by
      show sig p (𝓞 E) (1 ⊗ₜ H.w0) = 1 ⊗ₜ (H.bar H.w0)
      unfold sig
      rw [Algebra.TensorProduct.map_tmul]
      rfl
    rw [h1, UpperTheory.Depth.SplitIdem.cmHost_bar_halfIntegerGenerator, map_sub, map_one]
  have hsum : ι γ * (j H.w0 - ι β) + sig p (𝓞 E) (ι γ * (j H.w0 - ι β)) = 1 := by
    rw [map_mul, map_sub, hsι, hsι, hsj]
    linear_combination hγ'
  haveI : Nontrivial (ℤ_[p] ⊗[ℤ] 𝓞 E) := Module.FaithfullyFlat.rTensor_nontrivial ℤ (𝓞 E) ℤ_[p]
  refine ⟨ι γ * (j H.w0 - ι β), 1 - 2 * β, ?_, ?_, ?_, hsum, ?_, ?_⟩
  · linear_combination (ι γ) ^ 2 * hw' - (ι γ) ^ 2 * hβ' + ι γ * (j H.w0 - ι β) * hγ'
  · intro h
    rw [h, map_zero, add_zero] at hsum
    exact zero_ne_one hsum
  · intro h
    rw [h, map_one] at hsum
    exact one_ne_zero (add_left_cancel (hsum.trans (add_zero _).symm))
  · have hk' : (H.d : ℤ_[p]) + 1 = 8 * k := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[p]) hk
    linear_combination 4 * hβ + hk'
  · intro O _ _ _ _ σ
    have hτ : tauExt (p := p) σ (ι γ * (j H.w0 - ι β)) =
        algebraMap ℤ_[p] O γ * (σ H.w0 - algebraMap ℤ_[p] O β) := by
      have h1 : ∀ x, tauExt (p := p) σ (ι x) = algebraMap ℤ_[p] O x := fun x => (tauExt σ).commutes x
      have h2 : tauExt (p := p) σ (j H.w0) = σ H.w0 := by
        show tauExt (p := p) σ (1 ⊗ₜ H.w0) = _
        unfold tauExt
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rfl
      rw [map_mul, map_sub, h1, h1, h2]
    have hg : algebraMap ℤ_[p] O γ * (1 - 2 * algebraMap ℤ_[p] O β) = 1 := by
      have := congrArg (algebraMap ℤ_[p] O) hγ
      simpa only [map_mul, map_sub, map_ofNat, map_one] using this
    have hr : 2 * σ H.w0 = 1 + σ H.rt := by
      have := congrArg σ H.two_weight_eq_one_add_root
      simpa only [map_mul, map_add (f := _), map_ofNat, map_one] using this
    have ha : algebraMap ℤ_[p] O (1 - 2 * β) = 1 - 2 * algebraMap ℤ_[p] O β := by
      simp only [map_mul, map_sub, map_ofNat, map_one]
    have h2 : (2 : O) ≠ 0 := two_ne_zero
    simp only [Emb, Set.mem_setOf_eq]
    rw [map_sub (tauExt σ) 1, map_one, hτ, ha]
    set g := algebraMap ℤ_[p] O γ
    set b := algebraMap ℤ_[p] O β
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · linear_combination 2 * (1 - 2 * b) * h - 2 * (σ H.w0 - b) * hg - hr
    · apply mul_left_cancel₀ h2
      linear_combination g * hr + g * h + 2 * hg
    · linear_combination -2 * (1 - 2 * b) * h - 2 * (σ H.w0 - b) * hg - hr
    · apply mul_left_cancel₀ h2
      linear_combination - g * hr - g * h
end

