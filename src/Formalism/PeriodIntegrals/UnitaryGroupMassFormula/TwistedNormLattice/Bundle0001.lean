module

public import Formalism.PeriodIntegrals.Bundle0008

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.CombinationEquivInvMemUnipotentFlagGroup
section
open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

variable {K : Type} [Field K] {n : ℕ}

def Zab (k : ℕ) (v : Fin n → K) : Prop := ∀ l : Fin n, k ≤ l.1 → v l = 0

def UT (b : Fin n → Fin n → K) : Prop := ∀ l k : Fin n, l < k → b l k = 0

theorem comb_zab {b : Fin n → Fin n → K} (hb : UT b) (w : Fin n → K) (k0 : ℕ) (hw : Zab k0 w) :
    Zab k0 (∑ i, w i • b i) := by
  intro l hl
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : k0 ≤ i.1
  · rw [hw i hi, zero_mul]
  · have hil : i < l := Fin.lt_def.2 (by omega)
    rw [hb i l hil, mul_zero]

theorem comb_reflect {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) (w : Fin n → K) (k0 : ℕ)
    (h : Zab k0 (∑ i, w i • b i)) : Zab k0 w := by
  have key : ∀ d : ℕ, ∀ l : Fin n, n - l.1 ≤ d → k0 ≤ l.1 → w l = 0 := by
    intro d
    induction d with
    | zero => intro l hl _; have := l.2; omega
    | succ d ih =>
      intro l hl hk
      have hs := h l hk
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
      rw [Finset.sum_eq_single l] at hs
      · exact (mul_eq_zero.1 hs).resolve_right (hd l)
      · intro i _ hil
        rcases lt_or_gt_of_ne hil with hlt | hgt
        · rw [hb i l hlt, mul_zero]
        · have h2 := Fin.lt_def.1 hgt
          have h3 := i.2
          rw [ih i (by omega) (by omega), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ l) h'
  intro l hl
  exact key (n - l.1) l le_rfl hl

def combL (b : Fin n → Fin n → K) : (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun w := ∑ i, w i • b i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' t x := by simp [Finset.smul_sum, mul_smul]

theorem combL_apply (b : Fin n → Fin n → K) (w : Fin n → K) : combL b w = ∑ i, w i • b i := rfl

theorem combL_single (b : Fin n → Fin n → K) (l : Fin n) : combL b (Pi.single l 1) = b l := by
  rw [combL_apply, Finset.sum_eq_single l (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_smul])
    (fun h => absurd (Finset.mem_univ l) h), Pi.single_eq_same, one_smul]

theorem combL_inj {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) : Function.Injective (combL b) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  have hz : Zab 0 (∑ i, w i • b i) := by
    intro l _
    rw [← combL_apply, hw]
    rfl
  funext l
  exact comb_reflect hb hd w 0 hz l (Nat.zero_le _)

def combE {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofInjectiveEndo (combL b) (combL_inj hb hd)

theorem combE_apply {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) (w : Fin n → K) :
    combE hb hd w = ∑ i, w i • b i := rfl

theorem combE_symm_zab {b : Fin n → Fin n → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0) (k0 : ℕ) (v : Fin n → K)
    (hv : Zab k0 v) : Zab k0 ((combE hb hd).symm v) := by
  have h := combE_apply hb hd ((combE hb hd).symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  refine comb_reflect hb hd _ k0 ?_
  rw [← h]
  exact hv

theorem eN_eq_single (l : Fin n) : Loc.eN K n l.1 = Pi.single l 1 := by
  funext m
  simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem eN_eq_zero {i : ℕ} (hi : n ≤ i) : Loc.eN K n i = 0 := by
  funext m
  have := m.2
  simp only [Loc.eN, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem mem_Ufl_iff {N c i : ℕ} (v : Fin (N + c) → K) : v ∈ Loc.Ufl K N c i ↔ Zab (N + i) v := by
  show (∀ l : Fin (N + c), l.1 ∉ {l : ℕ | l < N + i} → v l = 0) ↔ ∀ l : Fin (N + c), N + i ≤ l.1 → v l = 0
  simp only [Set.mem_ofPred_eq, not_lt]

private theorem R1cond_combE {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    Loc.R1cond K N c (combE hb hd) := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [mem_Ufl_iff] at hv ⊢
    rw [combE_apply]
    exact comb_zab hb v _ hv
  · by_cases hN : N < N + c
    · have he : Loc.eN K (N + c) N = Pi.single (⟨N, hN⟩ : Fin (N + c)) 1 := eN_eq_single (⟨N, hN⟩ : Fin (N + c))
      rw [he]
      change combL b (Pi.single _ 1) = _
      rw [combL_single, ha hN]
    · have he : Loc.eN K (N + c) N = 0 := eN_eq_zero (by omega)
      rw [he, map_zero]
  · rw [mem_Ufl_iff]
    by_cases hi : N + i < N + c
    · have he : Loc.eN K (N + c) (N + i) = Pi.single (⟨N + i, hi⟩ : Fin (N + c)) 1 := eN_eq_single (⟨N + i, hi⟩ : Fin (N + c))
      rw [he]
      change Zab (N + i) (combL b (Pi.single _ 1) - _)
      rw [combL_single]
      intro m hm
      simp only [Pi.sub_apply]
      rcases lt_or_eq_of_le hm with hlt | heq
      · have hne : m ≠ ⟨N + i, hi⟩ := by
          intro h
          subst h
          exact lt_irrefl _ hlt
        rw [hb _ _ (Fin.lt_def.2 hlt), Pi.single_eq_of_ne hne, sub_zero]
      · have hm' : m = ⟨N + i, hi⟩ := Fin.ext heq.symm
        subst hm'
        rw [Pi.single_eq_same, h1 _ (Nat.le_add_right N i), sub_self]
    · have he : Loc.eN K (N + c) (N + i) = 0 := eN_eq_zero (by omega)
      rw [he, map_zero, sub_zero]
      intro m _
      rfl

private theorem R1cond_combE_symm {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    Loc.R1cond K N c (combE hb hd).symm := by
  have hT := R1cond_combE hb hd h1 ha
  have hs : ∀ i, ∀ v ∈ Loc.Ufl K N c i, (combE hb hd).symm v ∈ Loc.Ufl K N c i := fun i v hv =>
    (mem_Ufl_iff _).2 (combE_symm_zab hb hd _ v ((mem_Ufl_iff _).1 hv))
  refine ⟨hs, (LinearEquiv.symm_apply_eq _).2 hT.2.1.symm, fun i => ?_⟩
  have h3 := hs i _ (hT.2.2 i)
  rw [map_sub, LinearEquiv.symm_apply_apply] at h3
  have h4 := (Loc.Ufl K N c i).neg_mem h3
  rwa [neg_sub] at h4

theorem combinationEquiv_inv_mem_unipotentFlagGroup {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    (combE hb hd)⁻¹ ∈ Loc.R1 K N c := by
  show Loc.R1cond K N c (combE hb hd)⁻¹ ∧ Loc.R1cond K N c (combE hb hd)⁻¹⁻¹
  rw [inv_inv]
  exact ⟨R1cond_combE_symm hb hd h1 ha, R1cond_combE hb hd h1 ha⟩

end PI.TwNormLat.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.UniformContinuityGaloisGroup
section
open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem one_notMem' : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem mul_notMem' {s t : 𝓞 E} (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) : s * t ∉ P.asIdeal :=
  fun h => (P.isPrime.mem_or_mem h).elim hs ht

theorem intAt_zero : IntAt P (0 : E) := by
  exact ⟨0, 1, PI.TwNormLat.W.one_notMem' P, by simp⟩

theorem intAt_one : IntAt P (1 : E) := by
  exact ⟨1, 1, PI.TwNormLat.W.one_notMem' P, by simp⟩

theorem intAt_natCast (k : ℕ) : IntAt P (k : E) := by
  exact ⟨k, 1, PI.TwNormLat.W.one_notMem' P, by simp⟩

theorem intAt_add {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨r * s' + s * r', s * s', PI.TwNormLat.W.mul_notMem' P hs hs', ?_⟩
  simp only [map_add (f := _), map_mul]
  rw [← h, ← h']
  ring

theorem intAt_mul {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨r * r', s * s', PI.TwNormLat.W.mul_notMem' P hs hs', ?_⟩
  simp only [map_mul]
  rw [← h, ← h']
  ring

theorem intAt_neg {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h⟩ := ha
  refine ⟨-r, s, hs, ?_⟩
  rw [map_neg, ← h]
  ring

theorem intAt_sub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  rw [sub_eq_add_neg]
  exact PI.TwNormLat.W.intAt_add P ha (PI.TwNormLat.W.intAt_neg P hb)

theorem intAt_pow {a : E} (ha : IntAt P a) (k : ℕ) : IntAt P (a ^ k) := by
  induction k with
  | zero => simpa using PI.TwNormLat.W.intAt_one P
  | succ k ih =>
    rw [pow_succ]
    exact PI.TwNormLat.W.intAt_mul P ih ha

abbrev qE : E := ((Ideal.absNorm P.asIdeal : ℕ) : E)

theorem qE_ne_zero (hp : (Ideal.absNorm P.asIdeal).Prime) : qE P ≠ 0 := by
  show ((Ideal.absNorm P.asIdeal : ℕ) : E) ≠ 0
  exact Nat.cast_ne_zero.mpr hp.ne_zero

theorem uniform_continuity_galois_group (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {r : 𝓞 E} (hr : r ∈ P.asIdeal) :
    ∃ s t : 𝓞 E, s ∉ P.asIdeal ∧ t * ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) = s * r := by
  have hqP : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal
  have hle : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr hqP
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hJ'
    apply hq
    have hsq : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right hJ'
    exact hsq (Ideal.mem_span_singleton_self _)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.mp hJP
  have hmem : s * r ∈ Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} := by
    rw [hJ, mul_comm s r]
    exact Ideal.mul_mem_mul hr hsJ
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨s, t, hsP, ht⟩

theorem unit_of_not_div (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {y : E} (hy : IntAt P y)
    (hy' : ¬ IntAt P (y / qE P)) : IntAt P y⁻¹ := by
  obtain ⟨r, s, hs, h⟩ := hy
  by_cases hr : r ∈ P.asIdeal
  · exfalso
    obtain ⟨s', t, hs', ht⟩ := PI.TwNormLat.W.uniform_continuity_galois_group P hq hr
    apply hy'
    refine ⟨t, s * s', PI.TwNormLat.W.mul_notMem' P hs hs', ?_⟩
    have hq0 := PI.TwNormLat.W.qE_ne_zero P hp
    have ht' : algebraMap (𝓞 E) E t * qE P = algebraMap (𝓞 E) E s' * algebraMap (𝓞 E) E r := by
      have e := congrArg (algebraMap (𝓞 E) E) ht
      simpa using e
    rw [map_mul, mul_div_assoc', div_eq_iff hq0, ht', ← h]
    ring
  · refine ⟨s, r, hr, ?_⟩
    have hr0 : algebraMap (𝓞 E) E r ≠ 0 := by
      intro h0
      apply hr
      have hr' : r = 0 := IsFractionRing.injective (𝓞 E) E (by rw [h0, map_zero])
      rw [hr']
      exact P.asIdeal.zero_mem
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hr0
      rw [← h, mul_zero]
    rw [← h, mul_assoc, mul_inv_cancel₀ hy0, mul_one]

theorem mem_stdAt {n : ℕ} (v : Sp E n) : v ∈ stdAt E n P ↔ ∀ l, IntAt P (v l) := by
  change (∃ s ∈ P.asIdeal.primeCompl, s • v ∈ stdLat E n) ↔ _
  constructor
  · rintro ⟨s, hs, hv⟩ l
    have hl : (s • v) l ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_pi.mp hv l (Set.mem_univ l)
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hl
    refine ⟨r, s, hs, ?_⟩
    rw [hr, Pi.smul_apply, Algebra.smul_def]
  · intro h
    choose r s hs hrs using h
    refine ⟨∏ l, s l, Submonoid.prod_mem _ (fun l _ => hs l), ?_⟩
    refine Submodule.mem_pi.mpr fun l _ => ?_
    refine Submodule.mem_one.mpr ⟨(∏ l' ∈ Finset.univ.erase l, s l') * r l, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ l),
      map_mul, map_mul, ← hrs l]
    ring

theorem mem_lam (N c : ℕ) (v : Sp E (N + c)) :
    v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ ∀ l, IntAt P (v l) := by
  show v ∈ Submodule.comap _ (stdAt E (N + c) P) ↔ _
  rw [Submodule.mem_comap, ← mem_stdAt P]
  refine Iff.of_eq (congrArg (· ∈ stdAt E (N + c) P) ?_)
  funext l
  simp [LocE.scE]

end PI.TwNormLat.W
end
end

