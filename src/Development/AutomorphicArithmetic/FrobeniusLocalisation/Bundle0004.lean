module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0001
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0002
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0003
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.DvdDiscrOfInertia

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.CondESpec
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.condE_spec :
    ∀ {φ : Frame} (H : HostRaw φ), H.condE ∣ H.condN ∧ 0 < H.condE ∧ ∀ f : ℕ, f ∣ H.condN → (H.imgOne f = ⊥ ↔ H.condE ∣ f) := by
  intro φ H
  have hN0 : H.condN ≠ 0 := H.condN_ne_zero
  have hN : H.imgOne H.condN = ⊥ := by
    rw [H.imgOne_eq_bot_iff dvd_rfl]
    intro u hu
    have h1 : u = 1 := by
      haveI : NeZero H.condN := ⟨hN0⟩
      apply Units.ext
      have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 hu
      rw [ZMod.natCast_zmod_val, Nat.cast_one] at h2
      exact h2
    rw [h1, map_one]
  have hmem : H.condE ∣ H.condN ∧ H.imgOne H.condE = ⊥ :=
    Nat.sInf_mem (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥}) ⟨H.condN, dvd_rfl, hN⟩
  have hpos : 0 < H.condE := Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hN0)
  refine ⟨hmem.1, hpos, fun f hf => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hg : H.imgOne (Nat.gcd H.condE f) = ⊥ := by
      rw [UpperTheory.HF.imgOne_gcd H hmem.1 hf, hmem.2, h, sup_bot_eq]
    have hle : H.condE ≤ Nat.gcd H.condE f :=
      Nat.sInf_le (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥})
        ⟨(Nat.gcd_dvd_right _ _).trans hf, hg⟩
    have heq : Nat.gcd H.condE f = H.condE := le_antisymm (Nat.gcd_le_left _ hpos) hle
    rw [← heq]
    exact Nat.gcd_dvd_right _ _
  · exact le_bot_iff.1 (hmem.2 ▸ H.imgOne_anti h hf)
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobHOrder
section
open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

private theorem two_pow_dvd_sq_pm_one_iff_of_odd (a : ℤ) (ha : Odd a) (k : ℕ) :
    ((2:ℤ) ^ (k + 1 + 1) ∣ a ^ 2 - 1 ∨ (2:ℤ) ^ (k + 1 + 1) ∣ a ^ 2 + 1) ↔
      ((2:ℤ) ^ (k + 1) ∣ a - 1 ∨ (2:ℤ) ^ (k + 1) ∣ a + 1) := by
  obtain ⟨t, rfl⟩ := ha
  constructor
  · rintro (h | h)
    · have e1 : (2 * t + 1) ^ 2 - 1 = 2 ^ 2 * (t * (t + 1)) := by ring
      have e2 : (2:ℤ) ^ (k + 1 + 1) = 2 ^ 2 * 2 ^ k := by ring
      rw [e1, e2] at h
      have h' : (2:ℤ) ^ k ∣ t * (t + 1) := (mul_dvd_mul_iff_left (by norm_num)).1 h
      rcases Int.even_or_odd t with ⟨r, hr⟩ | ⟨r, hr⟩
      · have hc : IsCoprime ((2:ℤ) ^ k) (t + 1) := by
          apply IsCoprime.pow_left
          exact ⟨-r, 1, by rw [hr]; ring⟩
        obtain ⟨c, hc'⟩ := hc.dvd_of_dvd_mul_right h'
        exact Or.inl ⟨c, by rw [hc']; ring⟩
      · have hc : IsCoprime ((2:ℤ) ^ k) t := by
          apply IsCoprime.pow_left
          exact ⟨-r, 1, by rw [hr]; ring⟩
        rw [mul_comm] at h'
        obtain ⟨c, hc'⟩ := hc.dvd_of_dvd_mul_right h'
        exact Or.inr ⟨c, by linear_combination 2 * hc'⟩
    · exfalso
      have h4 : (4:ℤ) ∣ (2:ℤ) ^ (k + 1 + 1) := ⟨2 ^ k, by ring⟩
      have h5 := dvd_trans h4 h
      have e1 : (2 * t + 1) ^ 2 + 1 = 4 * (t ^ 2 + t) + 2 := by ring
      rw [e1] at h5
      generalize t ^ 2 + t = s at h5
      omega
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · exact Or.inl ⟨c * (2 ^ k * c + 1), by linear_combination (2 * t + 2 ^ (k + 1) * c + 2) * hc⟩
    · exact Or.inl ⟨c * (2 ^ k * c - 1), by linear_combination (2 * t + 2 ^ (k + 1) * c) * hc⟩

private theorem two_pow_dvd_pow_two_pow_sub_or_add_iff (j : ℕ) : ∀ (a : ℤ), Odd a → ∀ k : ℕ,
    ((2:ℤ) ^ (k + 1 + j) ∣ a ^ (2 ^ j) - 1 ∨ (2:ℤ) ^ (k + 1 + j) ∣ a ^ (2 ^ j) + 1) ↔
      ((2:ℤ) ^ (k + 1) ∣ a - 1 ∨ (2:ℤ) ^ (k + 1) ∣ a + 1) := by
  induction j with
  | zero => intro a _ k; simp
  | succ j ih =>
    intro a ha k
    have h1 : (a ^ 2) ^ (2 ^ j) = a ^ (2 ^ (j + 1)) := by rw [← pow_mul, ← pow_succ']
    have h2 : k + 1 + (j + 1) = (k + 1) + 1 + j := by omega
    rw [← h1, h2, ih (a ^ 2) ha.pow (k + 1)]
    exact two_pow_dvd_sq_pm_one_iff_of_odd a ha k

private theorem cast_eq_one_or_neg_one_iff_dvd (n : ℕ) (a : ℤ) :
    ((a : ZMod n) = 1 ∨ (a : ZMod n) = -1) ↔ ((n : ℤ) ∣ a - 1 ∨ (n : ℤ) ∣ a + 1) := by
  have e1 : ((a : ZMod n) = 1) ↔ (((a - 1 : ℤ) : ZMod n) = 0) := by
    push_cast; exact sub_eq_zero.symm
  have e2 : ((a : ZMod n) = -1) ↔ (((a + 1 : ℤ) : ZMod n) = 0) := by
    push_cast; exact eq_neg_iff_add_eq_zero
  rw [e1, e2, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem UpperTheory.HF.frob_h_order :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ), p.Prime → ¬ p ∣ H.condN →
      (∀ j : ℕ, orderOf (φ.hH (H.frobG p).2) ≤ 2 ^ j ↔
        ((p : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (p : ZMod (2 ^ (φ.e + 2 - j))) = -1)) ∧
      (∃ j ≤ φ.e, orderOf (φ.hH (H.frobG p).2) = 2 ^ j) ∧
      2 ^ (φ.e + 2) ≤ (p + 1) * orderOf (φ.hH (H.frobG p).2) ∧
      (φ.hH (H.frobG p).2 = 1 ↔ ((p : ZMod (2 ^ (φ.e + 2))) = 1 ∨ (p : ZMod (2 ^ (φ.e + 2))) = -1)) := by
  intro φ H p hp hpN
  haveI := Fact.mk hp
  obtain ⟨-, -, -, -, -, v, hv, hx⟩ := frobG_spec φ H p hpN
  rw [hx]
  set x := hcl φ.e v with hxdef
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpN (HostRaw.two_dvd_condN _)
  have hodd : Odd (p : ℤ) := (Int.odd_coe_nat p).2 (hp.odd_of_ne_two hp2)
  have key : ∀ k : ℕ, x ^ k = 1 ↔
      ((2:ℤ) ^ (φ.e + 2) ∣ (p : ℤ) ^ k - 1 ∨ (2:ℤ) ^ (φ.e + 2) ∣ (p : ℤ) ^ k + 1) := by
    intro k
    rw [hxdef, Group.hcl_pow_eq_one]
    simp only [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hv]
    have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2)) ((p : ℤ) ^ k)
    push_cast at hc
    exact hc
  have hx4 : x ^ (2 ^ φ.e) = 1 := by
    rw [key]
    have h := (two_pow_dvd_pow_two_pow_sub_or_add_iff φ.e (p : ℤ) hodd 1).2 (by
      obtain ⟨t, ht⟩ := hodd
      rw [ht]
      have : (2:ℤ) ^ (1 + 1) = 4 := by norm_num
      rw [this]
      omega)
    rwa [show 1 + 1 + φ.e = φ.e + 2 by omega] at h
  obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx4)
  have cl1 : ∀ j : ℕ, orderOf x ≤ 2 ^ j ↔
      ((p : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (p : ZMod (2 ^ (φ.e + 2 - j))) = -1) := by
    intro j
    by_cases hj : j ≤ φ.e + 1
    · obtain ⟨m, hm⟩ : ∃ m, φ.e + 2 - j = m + 1 := ⟨φ.e + 1 - j, by omega⟩
      rw [hm]
      have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (m + 1)) (p : ℤ)
      push_cast at hc
      rw [hc, ← two_pow_dvd_pow_two_pow_sub_or_add_iff j (p : ℤ) hodd m, show m + 1 + j = φ.e + 2 by omega, ← key,
        ← orderOf_dvd_iff_pow_eq_one, hord, Nat.pow_dvd_pow_iff_le_right (by norm_num),
        Nat.pow_le_pow_iff_right (by norm_num)]
    · have h0 : φ.e + 2 - j = 0 := by omega
      rw [h0, hord]
      haveI : Subsingleton (ZMod (2 ^ 0)) := ZMod.subsingleton_iff.2 (by norm_num)
      constructor
      · intro _
        exact Or.inl (Subsingleton.elim _ _)
      · intro _
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨cl1, ⟨i, hi, hord⟩, ?_, ?_⟩
  · have h := (cl1 i).1 (le_of_eq hord)
    have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2 - i)) (p : ℤ)
    push_cast at hc
    have h2p := hp.two_le
    have hb : ((2 ^ (φ.e + 2 - i) : ℕ) : ℤ) ≤ (p : ℤ) + 1 := by
      push_cast
      rcases hc.1 h with hd | hd
      · have := Int.le_of_dvd (by omega) hd
        linarith
      · exact Int.le_of_dvd (by omega) hd
    have hb' : 2 ^ (φ.e + 2 - i) ≤ p + 1 := by exact_mod_cast hb
    calc 2 ^ (φ.e + 2) = 2 ^ (φ.e + 2 - i) * 2 ^ i := by
          rw [← pow_add]
          congr 1
          omega
      _ ≤ (p + 1) * 2 ^ i := Nat.mul_le_mul_right _ hb'
      _ = (p + 1) * orderOf x := by rw [hord]
  · have h := key 1
    simp only [pow_one] at h
    rw [h]
    have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2)) (p : ℤ)
    push_cast at hc
    rw [hc]
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.GrpBridge
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem card_eq_of_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {A : Subgroup G} {B : Subgroup G'}
    (h : ∀ g, g ∈ A ↔ e g ∈ B) : Nat.card A = Nat.card B :=
  Nat.card_congr (e.toEquiv.subtypeEquiv h)

theorem UpperTheory.HF.grp_bridge :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ H.gal σ ∈ H.inertG l) ∧ (∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer _ P ↔ H.gal σ ∈ H.decG l) ∧ P.ramificationIdx ℤ = H.el l ∧ P.inertiaDeg ℤ = H.nw l ∧ Nat.card (H.decG l) = H.el l * H.nw l ∧ (primesOver (span {(l : ℤ)}) (𝓞 H.E)).ncard * (H.el l * H.nw l) = 4 * φ.ord := by
  intro φ H l hl P _ _
  haveI : Fact l.Prime := ⟨hl⟩
  haveI := H.galois
  haveI hmax : (span {(l : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have hI : ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ H.gal σ ∈ H.inertG l := fun σ =>
    (H.der.inertia l P σ).trans (H.mem_inertG l _).symm
  have hD : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer _ P ↔ H.gal σ ∈ H.decG l := fun σ =>
    (H.der.decomp l P σ).trans ((UpperTheory.HF.artL_spec H.toHostRaw hl).2.2 _).symm
  have hcI : Nat.card (P.inertia Gal(H.E/ℚ)) = H.el l :=
    card_eq_of_iff H.gal (fun σ => AddSubgroup.mem_inertia.trans (hI σ))
  have hcD : Nat.card (MulAction.stabilizer Gal(H.E/ℚ) P) = Nat.card (H.decG l) :=
    card_eq_of_iff H.gal hD
  have hle : H.inertG l ≤ H.decG l := le_sup_left
  have hmul : Nat.card (H.decG l) = H.el l * H.nw l := by
    rw [← ((H.inertG l).subgroupOf (H.decG l)).card_mul_index,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    rfl
  have he : (span {(l : ℤ)}).ramificationIdxIn (𝓞 H.E) = H.el l := by
    rw [← hcI, card_inertia_eq_ramificationIdxIn (G := Gal(H.E/ℚ)) (span {(l : ℤ)}) P]
  have hf : (span {(l : ℤ)}).inertiaDegIn (𝓞 H.E) = H.nw l := by
    have h := card_stabilizer_eq (G := Gal(H.E/ℚ)) (span {(l : ℤ)}) P
    rw [hcD, hmul, he] at h
    exact (Nat.eq_of_mul_eq_mul_left (H.el_pos l) h).symm
  refine ⟨hI, hD, ?_, ?_, hmul, ?_⟩
  · rw [← he, ramificationIdxIn_eq_ramificationIdx (span {(l : ℤ)}) P Gal(H.E/ℚ)]
  · rw [← hf, inertiaDegIn_eq_inertiaDeg (span {(l : ℤ)}) P Gal(H.E/ℚ)]
  · rw [← he, ← hf, ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(l : ℤ)}) (𝓞 H.E) Gal(H.E/ℚ),
      IsGalois.card_aut_eq_finrank, H.der.finrank_E]
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.NormDiffEK
section
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem absNorm_smul_gal {K : Type} [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K) (I : Ideal (𝓞 K)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  have e : (𝓞 K ⧸ I) ≃+* (𝓞 K ⧸ (σ • I)) :=
    Ideal.quotientEquiv I (σ • I) (MulSemiringAction.toRingEquiv (K ≃ₐ[ℚ] K) (𝓞 K) σ) rfl
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr e.toEquiv).symm

theorem UpperTheory.HF.norm_diff_EK :
    ∀ {φ : Frame} (H : HostAx φ), absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) * H.d ^ (2 * φ.ord) = (discr H.E).natAbs ∧ Real.log (absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E))) = 2 * (2 * φ.ord) * (Real.log H.rd - 1 / 2 * Real.log H.d) ∧ ∀ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → absNorm 𝔟 ^ 2 = absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) ∧ Real.log (absNorm 𝔟) = (2 * φ.ord) * (Real.log H.rd - 1 / 2 * Real.log H.d) := by
  intro φ H
  have h1 : absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) * H.d ^ (2 * φ.ord) = (discr H.E).natAbs := by
    have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow H.K (𝓞 H.K) H.E (𝓞 H.E)
    rw [H.finrank_EK, (UpperTheory.HF.discr_K H).1] at h
    exact h.symm
  have hd : discr H.E ≠ 0 := discr_ne_zero H.E
  have hd' : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hd
  have habs : |(discr H.E : ℝ)| = ((discr H.E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hpos : 0 < |(discr H.E : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd)
  have hn : absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact hd' h1.symm
  have hord : (φ.ord : ℝ) ≠ 0 := Nat.cast_ne_zero.2 φ.ord_pos.ne'
  have hrd : Real.log ((discr H.E).natAbs : ℝ) = 4 * φ.ord * Real.log H.rd := by
    unfold HostRaw.rd
    rw [Real.log_rpow hpos, habs, H.finrank_cmField]
    push_cast
    field_simp
  have h2 : Real.log (absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E))) =
      2 * (2 * φ.ord) * (Real.log H.rd - 1 / 2 * Real.log H.d) := by
    rw [← h1, Nat.cast_mul, Nat.cast_pow,
      Real.log_mul (Nat.cast_ne_zero.2 hn) (pow_ne_zero _ (Nat.cast_ne_zero.2 H.d_prime.ne_zero)),
      Real.log_pow] at hrd
    push_cast at hrd
    linarith
  refine ⟨h1, h2, fun 𝔟 h𝔟 => ?_⟩
  have h3 : absNorm 𝔟 ^ 2 = absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) := by
    rw [h𝔟, map_mul, absNorm_smul_gal, sq]
  refine ⟨h3, ?_⟩
  rw [← h3, Nat.cast_pow, Real.log_pow] at h2
  push_cast at h2
  linarith
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.VdFormula
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem regroup {N : ℕ} (hN : N ≠ 0) (f : ℕ → ℝ) :
    ∑ m ∈ N.divisors, ArithmeticFunction.vonMangoldt m * f (N / m) =
      ∑ l ∈ N.primeFactors, (∑ j ∈ Finset.range (N.factorization l), f (ordCompl[l] N * l ^ j)) * Real.log l := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_sigma', ← Finset.sum_filter_add_sum_filter_not N.divisors IsPrimePow,
    Finset.sum_eq_zero (s := N.divisors.filter fun m => ¬ IsPrimePow m) (fun m hm => by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 (Finset.mem_filter.1 hm).2, zero_mul]), add_zero]
  symm
  refine Finset.sum_bij (fun x _ => x.1 ^ (N.factorization x.1 - x.2)) ?_ ?_ ?_ ?_
  · rintro ⟨l, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors] at hx
    refine Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨?_, hN⟩, ?_⟩
    · exact (pow_dvd_pow l (Nat.sub_le _ _)).trans (Nat.ordProj_dvd N l)
    · exact hx.1.1.isPrimePow.pow (by dsimp only; omega)
  · rintro ⟨l, j⟩ hx ⟨l', j'⟩ hy h
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors] at hx hy
    dsimp only at h
    have h1 : l = l' := by
      refine (Nat.prime_dvd_prime_iff_eq hx.1.1 hy.1.1).1 (hx.1.1.dvd_of_dvd_pow (n := N.factorization l' - j') ?_)
      rw [← h]; exact dvd_pow_self l (by omega)
    subst h1
    have h2 := Nat.pow_right_injective hx.1.1.two_le h
    obtain rfl : j = j' := by omega
    rfl
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).1 hm2
    have hd := Nat.dvd_of_mem_divisors hm1
    have hle : k ≤ N.factorization p := (hp.pow_dvd_iff_le_factorization hN).1 hd
    refine ⟨⟨p, N.factorization p - k⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors]
      exact ⟨⟨hp, (dvd_pow_self p hk.ne').trans hd, hN⟩, by omega⟩
    · dsimp only
      congr 1; omega
  · rintro ⟨l, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors] at hx
    dsimp only
    have hl := hx.1.1
    have h4 : N / l ^ (N.factorization l - j) = ordCompl[l] N * l ^ j := by
      refine Nat.div_eq_of_eq_mul_right (pow_pos hl.pos _) ?_
      rw [mul_comm (ordCompl[l] N), ← mul_assoc, ← pow_add, Nat.sub_add_cancel hx.2.le]
      exact (Nat.ordProj_mul_ordCompl_eq_self N l).symm
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hl, h4, mul_comm]

theorem UpperTheory.HF.vd_formula :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → H.vdH l = ∑ j ∈ Finset.range (H.condN.factorization l), (1 - 1 / (Nat.card (H.imgOne (ordCompl[l] H.condN * l ^ j)) : ℝ)) := by
  intro φ H l hl
  have hN : H.condN ≠ 0 := NeZero.ne _
  obtain ⟨-, h2, h3, -⟩ := UpperTheory.HF.log_rd_sum H
  by_cases hlN : l ∈ H.condN.primeFactors
  · have h4 := Formalism.HC.Der.Rd.log_rd_eq H.toHostRaw
    rw [Formalism.HC.Der.Rd.SS, regroup hN (Formalism.HC.Der.Rd.rho H.art.ker), h2] at h4
    let a : ℕ → ℚ := fun p => (padicValNat p (NumberField.discr H.E).natAbs : ℚ) / (Module.finrank ℚ H.E : ℚ)
    let b : ℕ → ℚ := fun p => ∑ j ∈ Finset.range (H.condN.factorization p),
      (1 - 1 / (Nat.card (H.imgOne (ordCompl[p] H.condN * p ^ j)) : ℚ))
    have ha : ∀ p, (a p : ℝ) = H.vdH p := fun p => by
      simp only [a, HostRaw.vdH]; push_cast; rfl
    have hb : ∀ p, (b p : ℝ) = ∑ j ∈ Finset.range (H.condN.factorization p),
        (1 - 1 / (Nat.card (H.imgOne (ordCompl[p] H.condN * p ^ j)) : ℝ)) := fun p => by
      simp only [b]; push_cast; rfl
    have h5 := UpperTheory.HF.log_prime_indep H.condN.primeFactors a b (fun p hp => Nat.prime_of_mem_primeFactors hp)
      (by
        simp_rw [ha, hb]
        rw [h4]
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        refine UpperTheory.HF.rho_art H.toHostRaw ?_
        conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self H.condN p, mul_comm]
        exact mul_dvd_mul_left _ (pow_dvd_pow p (Finset.mem_range.1 hj).le)) l hlN
    rw [← ha, ← hb, h5]
  · have h6 : H.condN.factorization l = 0 := by
      rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hlN
    have h7 : ¬ l ∣ (NumberField.discr H.E).natAbs := fun hd =>
      hlN (h3 (Nat.mem_primeFactors.2 ⟨hl, hd, Int.natAbs_ne_zero.2 (discr_ne_zero H.E)⟩))
    rw [h6, Finset.sum_range_zero, HostRaw.vdH, Nat.padicValNat_def,
      multiplicity_eq_zero_of_not_dvd h7, Nat.cast_zero, zero_div]
end

