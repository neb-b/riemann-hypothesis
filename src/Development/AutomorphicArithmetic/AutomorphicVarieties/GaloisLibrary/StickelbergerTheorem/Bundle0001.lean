module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.CombFloor
section
open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

private theorem combFloor_step (M : ℕ) [NeZero M] (k : ℕ) (t : ZMod M) :
    (k + 1) * t.val / M = k * t.val / M + carry M ((k : ZMod M) * t) (1 * t) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have key : ∀ a v : ℕ, v < M → (a + v) / M = a / M + (if M ≤ a % M + v then 1 else 0) := by
    intro a v hv
    have hr := Nat.mod_lt a hM
    conv_lhs => rw [← Nat.div_add_mod a M, add_assoc, Nat.mul_add_div hM]
    congr 1
    split_ifs with h
    · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · exact Nat.div_eq_of_lt (by omega)
  have hkt : ((k : ZMod M) * t).val = k * t.val % M := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  show _ = _ + (if M ≤ ((k : ZMod M) * t).val + (1 * t).val then 1 else 0)
  rw [hkt, one_mul, add_mul, one_mul, key _ _ (ZMod.val_lt t)]

theorem UpperTheory.V.Stick.combFloor :
    ∀ (M : ℕ) [NeZero M] (A : Type) [CommGroup A] (x : (ZMod M)ˣ → A),
    (∀ a b : ZMod M, ∏ t : (ZMod M)ˣ, x t ^ carry M (a * t) (b * t) = 1) →
    ∀ k : ℕ, ∏ t : (ZMod M)ˣ, x t ^ (k * (t : ZMod M).val / M) = 1 := by
  intro M _ A _ x hx k
  induction k with
  | zero => simp
  | succ k ih =>
    simp_rw [combFloor_step M k, pow_add]
    rw [Finset.prod_mul_distrib, ih, hx, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.FfsumPow
section
open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

private theorem ffsum_pow (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n < 2 * (p - 1)) :
    ∑ x : ZMod p, x ^ n = if n = p - 1 then -1 else 0 := by
  classical
  have hp2 := hp.out.two_le
  rcases lt_or_ge n (p - 1) with h | h
  · rw [if_neg h.ne]
    have := FiniteField.sum_pow_lt_card_sub_one (ZMod p) n (by rw [ZMod.card]; exact h)
    exact this
  · have hn0 : n ≠ 0 := by omega
    let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x => x, Units.val_injective⟩
    have hmap : Finset.univ.map φ = Finset.univ \ {0} := by
      ext x
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_singleton, φ, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨u, rfl⟩
        exact u.ne_zero
      · intro hx
        exact ⟨Units.mk0 x hx, rfl⟩
    have hs : ∑ x : ZMod p, x ^ n = ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ n := by
      rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))), Finset.sum_singleton,
        zero_pow hn0, add_zero, ← hmap, Finset.sum_map]
      rfl
    rw [hs, FiniteField.sum_pow_units, ZMod.card]
    have hiff : p - 1 ∣ n ↔ n = p - 1 := by
      constructor
      · rintro ⟨c, rfl⟩
        rcases c with _ | _ | c
        · omega
        · ring
        · nlinarith
      · rintro rfl
        exact dvd_refl _
    simp only [hiff]

theorem UpperTheory.V.Stick.ffsum :
    ∀ (p : ℕ) [Fact p.Prime] (i j : ℕ), 0 < i → i < p - 1 → 0 < j → j < p - 1 →
    (∑ x : ZMod p, x ^ i * (1 - x) ^ j = 0 ↔ i + j < p - 1) := by
  intro p hp i j hi0 hip hj0 hjp
  have hpp : p.Prime := hp.out
  have key : ∑ x : ZMod p, x ^ i * (1 - x) ^ j =
      ∑ m ∈ Finset.range (j + 1), (-1) ^ m * (j.choose m : ZMod p) * ∑ x : ZMod p, x ^ (i + m) := by
    have h1 : ∀ x : ZMod p, (1 - x) ^ j =
        ∑ m ∈ Finset.range (j + 1), (-x) ^ m * 1 ^ (j - m) * (j.choose m : ZMod p) := by
      intro x
      rw [← add_pow, neg_add_eq_sub]
    simp_rw [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => ?_
    rw [neg_pow, one_pow, pow_add]
    ring
  have key2 : ∑ m ∈ Finset.range (j + 1), (-1) ^ m * (j.choose m : ZMod p) * ∑ x : ZMod p, x ^ (i + m) =
      ∑ m ∈ Finset.range (j + 1),
        if p - 1 - i = m then -((-1) ^ m * (j.choose m : ZMod p)) else 0 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [ffsum_pow p (i + m) (by omega)]
    by_cases h : i + m = p - 1
    · rw [if_pos h, if_pos (by omega)]
      ring
    · rw [if_neg h, if_neg (by omega), mul_zero]
  rw [key, key2, Finset.sum_ite_eq]
  split_ifs with h
  · rw [Finset.mem_range] at h
    constructor
    · intro h0
      exfalso
      have hc : (j.choose (p - 1 - i) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have hdf : p ∣ j.factorial := by
          rw [← Nat.choose_mul_factorial_mul_factorial (show p - 1 - i ≤ j by omega), mul_assoc]
          exact Dvd.dvd.mul_right hd _
        have := (Nat.Prime.dvd_factorial hpp).mp hdf
        omega
      have hu : ((-1 : ZMod p) ^ (p - 1 - i)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
      exact mul_ne_zero hu hc (neg_eq_zero.mp h0)
    · intro h'
      omega
  · rw [Finset.mem_range] at h
    constructor
    · intro _
      omega
    · intro _
      rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsBis
section
open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.red :
    ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)),
    (Ideal.absNorm P = p → ∃ π : 𝓞 K →+* ZMod p, RingHom.ker π = P) ∧
    ∀ π : 𝓞 K →+* ZMod p, RingHom.ker π = P → Ideal.absNorm P = p ∧ P.IsMaximal ∧ Prime P ∧ (p : 𝓞 K) ∈ P := by
  intro K _ _ p hp P
  have hpp : p.Prime := hp.out
  have hcard : ∀ π : 𝓞 K →+* ZMod p, Function.Surjective π := fun π x => by
    refine ⟨(x.val : 𝓞 K), ?_⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  refine ⟨fun h => ?_, fun π hπ => ?_⟩
  · have hfin : Finite (𝓞 K ⧸ P) := by
      rw [← Ideal.absNorm_ne_zero_iff, h]
      exact hpp.ne_zero
    let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
    have hc : Fintype.card (𝓞 K ⧸ P) = p := by
      rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, h]
    let e := ZMod.ringEquivOfPrime (𝓞 K ⧸ P) hpp hc
    refine ⟨(e.symm : (𝓞 K ⧸ P) →+* ZMod p).comp (Ideal.Quotient.mk P), ?_⟩
    rw [RingHom.ker_comp_of_injective _ e.symm.injective, Ideal.mk_ker]
  · have hs := hcard π
    have e : (𝓞 K ⧸ P) ≃+* ZMod p := hπ ▸ RingHom.quotientKerEquivOfSurjective hs
    have hn : Ideal.absNorm P = p := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr e.toEquiv, Nat.card_zmod]
    have hmax : P.IsMaximal := hπ ▸ RingHom.ker_isMaximal_of_surjective π hs
    refine ⟨hn, hmax, ?_, ?_⟩
    · refine Ideal.prime_of_isPrime ?_ hmax.isPrime
      rintro rfl
      rw [Ideal.absNorm_bot] at hn
      exact hpp.ne_zero hn.symm
    · rw [← hπ, RingHom.mem_ker, map_natCast, ZMod.natCast_self]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsTer
section
open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.teich :
    ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime] (π : R →+* ZMod p) (M d : ℕ) (ζ : R),
    IsPrimitiveRoot ζ M → IsPrimitiveRoot (π ζ) M → M * d = p - 1 →
    ∃ χ : MulChar (ZMod p) R, (∀ x : ZMod p, x ≠ 0 → χ x ^ M = 1 ∧ π (χ x) = x ^ d) ∧ orderOf χ = M := by
  intro R _ _ p hp π M d ζ hζ hv hMd
  have hpp : p.Prime := hp.out
  have hM : M ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hMd
    have := hpp.two_le
    omega
  have hd : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hMd
    have := hpp.two_le
    omega
  haveI : NeZero M := ⟨hM⟩
  have U : ∀ r s : R, r ^ M = 1 → s ^ M = 1 → π r = π s → r = s := by
    intro r s hr hs h
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hr
    obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hs
    rw [map_pow, map_pow] at h
    rw [hv.pow_inj hi hj h]
  have E : ∀ y : ZMod p, y ^ M = 1 → ∃ r : R, r ^ M = 1 ∧ π r = y := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := hv.eq_pow_of_pow_eq_one hy
    refine ⟨ζ ^ i, ?_, by rw [map_pow]⟩
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have P : ∀ x : ZMod p, x ≠ 0 → (x ^ d) ^ M = 1 := by
    intro x hx
    rw [← pow_mul, mul_comm, hMd]
    exact ZMod.pow_card_sub_one_eq_one hx
  classical
  let L : ZMod p → R := fun x => if h : x = 0 then 0 else (E _ (P x h)).choose
  have L1 : ∀ x (h : x ≠ 0), L x ^ M = 1 ∧ π (L x) = x ^ d := by
    intro x h
    simp only [L, dif_neg h]
    exact (E _ (P x h)).choose_spec
  have L0 : L 0 = 0 := by simp [L]
  let χ : MulChar (ZMod p) R :=
    { toFun := L
      map_one' := by
        have h1 := L1 1 one_ne_zero
        exact U _ _ h1.1 (one_pow M) (by rw [h1.2, one_pow, map_one])
      map_mul' := by
        intro x y
        by_cases hx : x = 0
        · rw [hx, zero_mul, L0, zero_mul]
        by_cases hy : y = 0
        · rw [hy, mul_zero, L0, mul_zero]
        have hxy := L1 (x * y) (mul_ne_zero hx hy)
        have h1 := L1 x hx
        have h2 := L1 y hy
        refine U _ _ hxy.1 (by rw [mul_pow, h1.1, h2.1, one_mul]) ?_
        rw [hxy.2, map_mul, h1.2, h2.2, mul_pow]
      map_nonunit' := by
        intro a ha
        have : a = 0 := by
          by_contra h
          exact ha (isUnit_iff_ne_zero.mpr h)
        rw [this]
        exact L0 }
  have hχ : ∀ x : ZMod p, x ≠ 0 → χ x ^ M = 1 ∧ π (χ x) = x ^ d := L1
  refine ⟨χ, hχ, ?_⟩
  have hpow : χ ^ M = 1 := by
    ext a
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    exact (hχ a a.ne_zero).1
  have hdvd : orderOf χ ∣ M := orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  set k := orderOf χ with hk
  have hk1 : χ ^ k = 1 := pow_orderOf_eq_one χ
  have hgk : (χ g) ^ k = 1 := by
    rw [← MulChar.pow_apply_coe, hk1, MulChar.one_apply_coe]
  have hgdk : g ^ (d * k) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul, ← (hχ g g.ne_zero).2, ← map_pow, hgk,
      map_one]
  have h2 : M * d ∣ d * k := by
    rw [hMd, ← hog]
    exact orderOf_dvd_of_pow_eq_one hgdk
  rw [mul_comm M d] at h2
  have h3 : M ∣ k := (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd)).mp h2
  exact Nat.dvd_antisymm hdvd h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.JacDvd
section
open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.jacDvd :
    ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (p : ℕ) [Fact p.Prime] (χ φ : MulChar (ZMod p) R),
    χ ≠ 1 → φ ≠ 1 → χ * φ ≠ 1 → jacobiSum χ φ ∣ (p : R) := by
  intro R _ _ _ p _ χ φ hχ hφ hχφ
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  have : CharZero K := charZero_of_injective_algebraMap hf
  have hc : ringChar K ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]
    exact (Fact.out : p.Prime).ne_zero.symm
  have h1 : χ.ringHomComp f ≠ 1 := (MulChar.ringHomComp_ne_one_iff hf).mpr hχ
  have h2 : φ.ringHomComp f ≠ 1 := (MulChar.ringHomComp_ne_one_iff hf).mpr hφ
  have h3 : χ.ringHomComp f * φ.ringHomComp f ≠ 1 := by
    rw [← MulChar.ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff hf).mpr hχφ
  have key := jacobiSum_mul_jacobiSum_inv hc h1 h2 h3
  rw [MulChar.ringHomComp_inv, MulChar.ringHomComp_inv, jacobiSum_ringHomComp,
    jacobiSum_ringHomComp, ← map_mul, ZMod.card, ← map_natCast f] at key
  exact ⟨_, (hf key).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.RedRoot
section
open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.redRoot :
    ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime] (π : R →+* ZMod p) (M : ℕ) (ζ : R),
    p.Coprime M → IsPrimitiveRoot ζ M → IsPrimitiveRoot (π ζ) M ∧ M ∣ p - 1 := by
  intro R _ _ p hp π M ζ hcop hζ
  have hpp : p.Prime := hp.out
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with rfl | h
    · exact absurd (Nat.coprime_zero_right p |>.mp hcop) hpp.one_lt.ne'
    · exact h
  have hne : NeZero (M : ZMod p) := by
    refine ⟨fun h => ?_⟩
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h)
  have hroot : (Polynomial.cyclotomic M R).IsRoot ζ := hζ.isRoot_cyclotomic hM
  have hroot' : (Polynomial.cyclotomic M (ZMod p)).IsRoot (π ζ) := by
    rw [← Polynomial.map_cyclotomic M π]
    exact hroot.map π
  have hprim : IsPrimitiveRoot (π ζ) M := (Polynomial.isRoot_cyclotomic_iff).mp hroot'
  refine ⟨hprim, hprim.dvd_of_pow_eq_one _ ?_⟩
  exact ZMod.pow_card_sub_one_eq_one (hprim.ne_zero hM.ne')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.Sqfree
section
open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

private theorem sub_prod {R : Type} [CommRing R] [IsDedekindDomain R] {ι : Type} (P : ι → Ideal R)
    (hP : ∀ i, Prime (P i)) (t : Finset ι) :
    ∀ I : Ideal R, I ∣ ∏ i ∈ t, P i → ∃ u : Finset ι, u ⊆ t ∧ I = ∏ i ∈ u, P i := by
  classical
  refine Finset.induction_on t ?_ ?_
  · intro I h
    rw [Finset.prod_empty] at h
    have h1 := Ideal.dvd_iff_le.1 h
    rw [Ideal.one_eq_top, top_le_iff] at h1
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    rw [Finset.prod_empty, h1, Ideal.one_eq_top]
  · intro a t ha ih I h
    rw [Finset.prod_insert ha] at h
    obtain ⟨K, hK⟩ := h
    have hpa := hP a
    by_cases hd : P a ∣ I
    · obtain ⟨J, rfl⟩ := hd
      have h' : J ∣ ∏ i ∈ t, P i := ⟨K, mul_left_cancel₀ hpa.ne_zero (by rw [hK, mul_assoc])⟩
      obtain ⟨u, hu, rfl⟩ := ih J h'
      refine ⟨insert a u, Finset.insert_subset_insert a hu, ?_⟩
      rw [Finset.prod_insert (fun h => ha (hu h))]
    · have hk : P a ∣ K := (hpa.dvd_or_dvd ⟨_, hK.symm⟩).resolve_left hd
      obtain ⟨L, rfl⟩ := hk
      have h' : I ∣ ∏ i ∈ t, P i := ⟨L, mul_left_cancel₀ hpa.ne_zero (by rw [hK]; exact mul_left_comm _ _ _)⟩
      obtain ⟨u, hu, e⟩ := ih I h'
      exact ⟨u, hu.trans (Finset.subset_insert a t), e⟩

theorem UpperTheory.V.Stick.sqfree :
    ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι] (P : ι → Ideal R),
    Function.Injective P → (∀ i, Prime (P i)) → ∀ (x : R) (s : Finset ι), Ideal.span {x} ∣ ∏ i, P i →
    (∀ i, i ∈ s ↔ x ∈ P i) → Ideal.span {x} = ∏ i ∈ s, P i := by
  classical
  intro R _ _ ι _ P hinj hP x s hdiv hs
  obtain ⟨u, -, hu⟩ := sub_prod P hP Finset.univ _ hdiv
  rw [hu]
  congr 1
  ext i
  rw [hs i, ← Ideal.dvd_span_singleton, hu]
  constructor
  · intro hi
    exact Finset.dvd_prod_of_mem P hi
  · intro hd
    have hex : ∀ t : Finset ι, P i ∣ ∏ j ∈ t, P j → ∃ j ∈ t, P i ∣ P j := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        intro h
        exact False.elim ((hP i).not_unit (isUnit_iff_dvd_one.mpr h))
      | @insert a t ha ih =>
        rw [Finset.prod_insert ha]
        intro h
        rcases (hP i).dvd_or_dvd h with h | h
        · exact ⟨a, Finset.mem_insert_self _ _, h⟩
        · obtain ⟨j, hj, hjd⟩ := ih h
          exact ⟨j, Finset.mem_insert_of_mem hj, hjd⟩
    obtain ⟨j, hj, hij⟩ := hex u hd
    have e := ((hP i).dvd_prime_iff_associated (hP j)).1 hij
    rw [associated_iff_eq] at e
    rwa [hinj e]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ZpowSumEqProd
section
open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.comb :
    ∀ (M : ℕ) [NeZero M] (A : Type) [CommGroup A] (x : (ZMod M)ˣ → A),
    (∀ k : ℕ, ∏ t : (ZMod M)ˣ, x t ^ (k * (t : ZMod M).val / M) = 1) →
    ∀ β γ : (ZMod M)ˣ → ℤ, (∀ t, (M : ℤ) * γ t = ∑ s, β s * (((s : ZMod M) * (t : ZMod M)).val : ℤ)) →
    ∏ t, x t ^ γ t = 1 := by
  intro M _ A _ x hx β γ hγ
  classical
  set F : (ZMod M)ˣ → ℤ := fun t =>
    ∑ s, β s * ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ) with hF
  set B : ℤ := ∑ s, β s * ((s : ZMod M).val : ℤ) with hB
  have key : ∀ t, (M : ℤ) * (γ t + F t) = B * ((t : ZMod M).val : ℤ) := by
    intro t
    rw [mul_add, hγ t, hF, hB]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ZMod.val_mul]
    have h0 := Nat.mod_add_div ((s : ZMod M).val * (t : ZMod M).val) M
    have h' : ((((s : ZMod M).val * (t : ZMod M).val % M : ℕ)) : ℤ)
        + (M : ℤ) * ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ)
        = ((s : ZMod M).val : ℤ) * ((t : ZMod M).val : ℤ) := by exact_mod_cast h0
    linear_combination β s * h'
  have hdiv : (M : ℤ) ∣ B := by
    rcases Nat.lt_or_ge 1 M with hM | hM
    · haveI : Fact (1 < M) := ⟨hM⟩
      have h1 := key 1
      rw [Units.val_one, ZMod.val_one, Nat.cast_one, mul_one] at h1
      exact ⟨_, h1.symm⟩
    · have hM1 : M = 1 := le_antisymm hM (NeZero.pos M)
      subst hM1
      refine ⟨0, ?_⟩
      rw [hB, mul_zero]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [Nat.lt_one_iff.mp (ZMod.val_lt (s : ZMod 1))]
      simp
  obtain ⟨b, hb⟩ := hdiv
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hγ' : ∀ t, γ t = b * ((t : ZMod M).val : ℤ) - F t := by
    intro t
    have h1 := key t
    rw [hb, mul_assoc] at h1
    have h2 := mul_left_cancel₀ hM h1
    linarith
  have h1 : ∏ t, x t ^ ((t : ZMod M).val : ℤ) = 1 := by
    have h3 := hx M
    simp only [Nat.mul_div_cancel_left _ (NeZero.pos M)] at h3
    simpa only [zpow_natCast] using h3
  have h2 : ∀ s : (ZMod M)ˣ,
      ∏ t, x t ^ ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ) = 1 := by
    intro s
    simpa only [zpow_natCast] using hx (s : ZMod M).val
  have hzs : ∀ (a : A) (g : (ZMod M)ˣ → ℤ) (u : Finset (ZMod M)ˣ),
      a ^ (∑ s ∈ u, g s) = ∏ s ∈ u, a ^ g s := by
    intro a g u
    induction u using Finset.induction_on with
    | empty => simp
    | insert i u hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]
  have hFprod : ∏ t, x t ^ F t = 1 := by
    simp only [hF, hzs]
    rw [Finset.prod_comm]
    have h4 : ∀ s : (ZMod M)ˣ, ∏ t, x t ^ (β s * ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ))
        = (∏ t, x t ^ ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ)) ^ β s := by
      intro s
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [← zpow_mul, mul_comm]
    simp only [h4, h2, one_zpow, Finset.prod_const_one]
  calc ∏ t, x t ^ γ t
      = ∏ t, (x t ^ ((t : ZMod M).val : ℤ)) ^ b / x t ^ F t := by
        refine Finset.prod_congr rfl fun t _ => ?_
        rw [hγ' t, zpow_sub, ← zpow_mul, mul_comm b, div_eq_mul_inv]
    _ = 1 := by
        rw [Finset.prod_div_distrib, Finset.prod_zpow, h1, hFprod]
        simp
end

