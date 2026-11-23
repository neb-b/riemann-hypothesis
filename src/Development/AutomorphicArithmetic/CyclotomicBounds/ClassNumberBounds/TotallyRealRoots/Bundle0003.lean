module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalRoots
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

private theorem gr_enough [CharZero E] (i : ℕ) :
    HasEnoughRootsOfUnity (AlgebraicClosure E) (l ^ i) := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  infer_instance

theorem eps_mem_princ_iff [CharZero E] (g : Gal(AlgebraicClosure E/E)) (n : ℕ) :
    eps l E g ∈ princ l n ↔ ∀ ζ : AlgebraicClosure E, ζ ^ l ^ n = 1 → g ζ = ζ := by
  haveI := fun i => gr_enough (l := l) (E := E) i
  set L := AlgebraicClosure E
  set σ : L ≃+* L := MulSemiringAction.toRingAut Gal(L/E) L g with hσ
  have hσg : ∀ x : L, σ x = g x := fun x => rfl
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity L (l ^ n)
  have key : eps l E g ∈ princ l n ↔
      (modularCyclotomicCharacter L hn σ : ZMod (l ^ n)) = 1 := by
    rw [← cyclotomicCharacter.toZModPow]
    simp only [princ, redPow, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
      map_one]
    rfl
  have hpow : ∀ {M : Type _} [Monoid M] (a : M), a ^ l ^ n = 1 →
      a ^ (1 : ZMod (l ^ n)).val = a := by
    intro M _ a ha
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ha, pow_one]
  rw [key]
  constructor
  · intro h ζ hζ
    have := cyclotomicCharacter.spec l σ ζ hζ
    rw [cyclotomicCharacter.toZModPow, h] at this
    rw [← hσg, this, hpow ζ hζ]
  · intro h
    symm
    apply modularCyclotomicCharacter.unique
    intro t ht
    rw [mem_rootsOfUnity] at ht
    have ht' : (t : L) ^ l ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    rw [hpow (t : L) ht', hσg, h _ ht']

theorem isClosed_galImage [CharZero E] : IsClosed (galImage l E : Set ℤ_[l]ˣ) := by
  have hc : Continuous (eps l E) :=
    cyclotomicCharacter.continuous l E (AlgebraicClosure E)
  have : (galImage l E : Set ℤ_[l]ˣ) = Set.range (eps l E) := by
    ext x
    simp [galImage]
  rw [this]
  exact (isCompact_range hc).isClosed

end KStar.TotallyRealRoots
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Generate
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem gen_exists_nat {t : ℤ_[l]} (ht : IsUnit t) (d : ℤ_[l]) :
    ∃ j : ℕ, (l : ℤ_[l]) ∣ d + t * j := by
  have htz : PadicInt.toZMod t ≠ 0 := (ht.map PadicInt.toZMod).ne_zero
  refine ⟨(-(PadicInt.toZMod d) * (PadicInt.toZMod t)⁻¹ : ZMod l).val, ?_⟩
  have hm : d + t * ((-(PadicInt.toZMod d) * (PadicInt.toZMod t)⁻¹ : ZMod l).val : ℤ_[l]) ∈
      RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    rw [RingHom.mem_ker, map_add (f := _), map_mul, map_natCast, ZMod.natCast_zmod_val]
    field_simp
    ring
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  exact hm

private theorem gen_emult {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]}
    (hu : emultiplicity (l : ℤ_[l]) (u - 1) = a) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ l ^ n - 1) = ((a + n : ℕ) : ℕ∞) := by
  have hlp : Prime l := Nat.prime_iff.mp Fact.out
  have h1 : (l : ℤ_[l]) ∣ u - 1 := by
    have := pow_dvd_of_le_emultiplicity (k := 1) (a := (l : ℤ_[l])) (b := u - 1)
      (by rw [hu]; exact_mod_cast ha)
    simpa using this
  by_cases hl : l = 2
  · have h2 : (l : ℤ_[l]) ^ 2 ∣ u - 1 :=
      pow_dvd_of_le_emultiplicity (by rw [hu]; exact_mod_cast ha2 hl)
    rw [emultiplicity_pow_sub_one_sq h2, hu, emultiplicity_pow_self_of_prime hlp]
    push_cast
    rfl
  · rw [emultiplicity_pow_sub_one_odd hl h1, hu, emultiplicity_pow_self_of_prime hlp]
    push_cast
    rfl

private theorem isUnit_padicInt_of_not_dvd {t : ℤ_[l]} (h : ¬ (l : ℤ_[l]) ∣ t) : IsUnit t := by
  by_contra hne
  have hm : t ∈ IsLocalRing.maximalIdeal ℤ_[l] := hne
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  exact h hm

private theorem exists_pow_eq_one_add_mul_sub_add_sq (v : ℤ_[l]) (j : ℕ) :
    ∃ c : ℤ_[l], v ^ j = 1 + (j : ℤ_[l]) * (v - 1) + (v - 1) ^ 2 * c := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨j + v * c, ?_⟩
    push_cast
    rw [pow_succ, hc]
    ring

private theorem gen_dvd {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]} (hunit : IsUnit u)
    (hu : emultiplicity (l : ℤ_[l]) (u - 1) = a) {x : ℤ_[l]} (hx : (l : ℤ_[l]) ^ a ∣ x - 1)
    (n : ℕ) : ∃ k : ℕ, (l : ℤ_[l]) ^ (a + n) ∣ u ^ k - x := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    rw [pow_zero, add_zero]
    have : (1 : ℤ_[l]) - x = -(x - 1) := by ring
    rw [this]
    exact (dvd_neg).mpr hx
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨d, hd⟩ := hk
    set v := u ^ l ^ n with hvdef
    have hv := gen_emult ha ha2 hu n
    have hvd : (l : ℤ_[l]) ^ (a' + 1 + n) ∣ v - 1 :=
      pow_dvd_of_le_emultiplicity (le_of_eq hv.symm)
    obtain ⟨t, ht⟩ := hvd
    have htu : IsUnit t := by
      apply isUnit_padicInt_of_not_dvd
      rintro ⟨s, hs⟩
      have hdv : (l : ℤ_[l]) ^ (a' + 1 + n + 1) ∣ v - 1 := ⟨s, by rw [ht, hs]; ring⟩
      have := le_emultiplicity_of_pow_dvd hdv
      rw [hv] at this
      norm_cast at this
      omega
    obtain ⟨j, e, he⟩ := gen_exists_nat ((hunit.pow k).mul htu) d
    obtain ⟨c, hc⟩ := exists_pow_eq_one_add_mul_sub_add_sq v j
    refine ⟨k + l ^ n * j, e + (l : ℤ_[l]) ^ (a' + n) * u ^ k * t ^ 2 * c, ?_⟩
    rw [pow_add, pow_mul, ← hvdef]
    linear_combination u ^ k * hc + hd + ((u ^ k) * j + u ^ k * c *
      (v - 1 + (l : ℤ_[l]) ^ (a' + 1 + n) * t)) * ht + (l : ℤ_[l]) ^ (a' + 1 + n) * he

theorem exists_pow_redPow_eq {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]ˣ}
    (hu : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a) {x : ℤ_[l]ˣ} (hx : x ∈ princ l a) (b : ℕ) :
    ∃ k : ℕ, redPow l b (u ^ k) = redPow l b x := by
  rw [mem_princ] at hx
  obtain ⟨k, hk⟩ := gen_dvd ha ha2 u.isUnit hu hx b
  refine ⟨k, Units.ext ?_⟩
  have hkb : (l : ℤ_[l]) ^ b ∣ (u : ℤ_[l]) ^ k - x :=
    (pow_dvd_pow _ (Nat.le_add_left b a)).trans hk
  have hm : (u : ℤ_[l]) ^ k - x ∈ RingHom.ker (PadicInt.toZModPow b : ℤ_[l] →+* ZMod (l ^ b)) := by
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact hkb
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  simpa [redPow] using hm

theorem princ_le_of_isClosed {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {U : Subgroup ℤ_[l]ˣ}
    (hU : IsClosed (U : Set ℤ_[l]ˣ)) {u : ℤ_[l]ˣ} (huU : u ∈ U)
    (hu : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a) : princ l a ≤ U := by
  intro x hx
  refine mem_of_isClosed hU fun b => ?_
  obtain ⟨k, hk⟩ := exists_pow_redPow_eq ha ha2 hu hx b
  exact ⟨u ^ k, U.pow_mem huU k, hk⟩

end KStar.TotallyRealRoots
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LevelGroupSupLevelInertia
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem lv_princ_le (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    princ l (N.factorization l) ≤ levelGroup l N H := by
  intro u hu
  refine mem_levelGroup.mpr ⟨1, H.one_mem, ?_⟩
  rw [map_one]
  exact (MonoidHom.mem_ker.mp hu).symm

private theorem lv_red_surjective : Function.Surjective (red l) := by
  intro v
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective (v : ZMod l)
  have hx : PadicInt.toZMod (k : ℤ_[l]) = (v : ZMod l) := by
    rw [map_natCast, hk]
  have hu : IsUnit (k : ℤ_[l]) := by
    by_contra hne
    have hm : (k : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := hne
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hx] at hm
    exact v.ne_zero hm
  refine ⟨hu.unit, Units.ext ?_⟩
  simp [red, hx]

theorem princ_le_levelGroup (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    princ l (N.factorization l) ≤ levelGroup l N H ∧ IsOpen (levelGroup l N H : Set ℤ_[l]ˣ) :=
  ⟨lv_princ_le N H, Subgroup.isOpen_mono (lv_princ_le N H) (isOpen_princ _)⟩

theorem levelGroup_eq_top {N : ℕ} (hN : ¬ l ∣ N) (H : Subgroup (ZMod N)ˣ) :
    levelGroup l N H = ⊤ ∧ resOrder l (levelGroup l N H) = l - 1 := by
  have h : levelGroup l N H = ⊤ := by
    rw [eq_top_iff]
    intro u _
    apply lv_princ_le N H
    rw [mem_princ, Nat.factorization_eq_zero_of_not_dvd hN, pow_zero]
    exact one_dvd _
  refine ⟨h, ?_⟩
  rw [h, resOrder, Subgroup.map_top_of_surjective _ lv_red_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units]

end KStar.TotallyRealRoots
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuFormula
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem nf_nu_le {U : Subgroup ℤ_[l]ˣ} {u : ℤ_[l]ˣ} (hu : u ∈ U) (tr : ℕ) :
    nu l U tr ≤ emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ tr - 1) :=
  sInf_le ⟨u, ⟨u, hu, rfl⟩, rfl⟩

end KStar.TotallyRealRoots
end

