module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPComplexMultiplicationCongruenceModPr
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPTorsionIntegralAndDistinctMod
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantCongruencesImaginaryQuadratic
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.WeberCongruence

theorem mem_of_isIntegral (W : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : x ∈ W := by
  have h1 : IsIntegral W x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  exact y.2

theorem mem_of_pow_mem (W : ValuationSubring ℂ) {x : ℂ} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n ∈ W) :
    x ∈ W := by
  rw [← W.valuation_le_one_iff] at hx ⊢
  rw [map_pow] at hx
  exact (pow_le_one_iff_of_nonneg zero_le hn).mp hx

theorem mul_mem_nonunits (W : ValuationSubring ℂ) {x y : ℂ} (hx : x ∈ W.nonunits) (hy : y ∈ W) :
    x * y ∈ W.nonunits := by
  rw [W.mem_nonunits_iff] at hx ⊢
  rw [← W.valuation_le_one_iff] at hy
  rw [map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hx hy

theorem mem_nonunits_of_mul (W : ValuationSubring ℂ) {x y : ℂ} (hx : x ∉ W.nonunits)
    (h : x * y ∈ W.nonunits) : y ∈ W.nonunits := by
  rw [W.mem_nonunits_iff] at hx h ⊢
  rw [map_mul] at h
  by_contra hy
  exact absurd h (not_lt.mpr (one_le_mul_of_one_le_of_one_le (not_lt.mp hx) (not_lt.mp hy)))

theorem sub_mem_nonunits_iff (W : ValuationSubring ℂ) (x y : W) :
    (x : ℂ) - y ∈ W.nonunits ↔ IsLocalRing.residue W x = IsLocalRing.residue W y := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem charP_residueField (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime)
    (h : (p : ℂ) ∈ W.nonunits) : CharP (IsLocalRing.ResidueField W) p := by
  rw [CharP.charP_iff_prime_eq_zero hp]
  have := (sub_mem_nonunits_iff W (p : W) 0).mp (by simpa using h)
  simpa using this

theorem inv_natCast_mem (W : ValuationSubring ℂ) {p m : ℕ} (hp : p.Prime)
    (h : (p : ℂ) ∈ W.nonunits) (hm : ¬ p ∣ m) : (m : ℂ)⁻¹ ∈ W := by
  have := charP_residueField W hp h
  have h1 : (m : ℂ) ∉ W.nonunits := fun hc ↦ by
    have := (sub_mem_nonunits_iff W (m : W) 0).mp (by simpa using hc)
    rw [map_natCast, map_zero, CharP.cast_eq_zero_iff _ p] at this
    exact hm this
  rw [ValuationSubring.mem_nonunits_iff_or] at h1
  push Not at h1
  exact h1.2

theorem pow_six_eq_one {k : Type*} [CommRing k] {p : ℕ} (hp : p.Prime) [CharP k p] {g h a : k}
    (e : g ^ 3 - 27 * h ^ 2 = 1) (h2 : g = a ^ 2 * g ^ p) (h3 : h = a ^ 3 * h ^ p) :
    a ^ 6 = 1 := by
  have := Fact.mk hp
  have e1 := congrArg (frobenius k p) e
  simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, frobenius_def] at e1
  generalize g ^ p = G at *
  generalize h ^ p = H at *
  subst h2 h3
  linear_combination e - a ^ 6 * e1

theorem congruences (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    {g h a : ℂ} (hg : g ∈ W) (hh : h ∈ W) (ha : a ∈ W) (e : g ^ 3 - 27 * h ^ 2 = 1)
    (h2 : g - a ^ 2 * g ^ p ∈ W.nonunits) (h3 : h - a ^ 3 * h ^ p ∈ W.nonunits) :
    g ^ 3 - (g ^ 3) ^ p ∈ W.nonunits ∧ ∀ x y, x ∈ W → y - a * x ^ p ∈ W.nonunits →
      g * h * y - (g * h * x) ^ p ∈ W.nonunits := by
  have := charP_residueField W hp hW
  lift g to W using hg
  lift h to W using hh
  lift a to W using ha
  have e' : g ^ 3 - 27 * h ^ 2 = 1 := Subtype.ext e
  have e1 := congrArg (IsLocalRing.residue W) e'
  have e2 := (sub_mem_nonunits_iff W g (a ^ 2 * g ^ p)).mp h2
  have e3 := (sub_mem_nonunits_iff W h (a ^ 3 * h ^ p)).mp h3
  simp only [map_sub, map_mul, map_pow, map_one, map_ofNat] at e1 e2 e3
  have e4 := pow_six_eq_one hp e1 e2 e3
  refine ⟨(sub_mem_nonunits_iff W (g ^ 3) ((g ^ 3) ^ p)).mpr ?_, fun x y hx hy ↦ ?_⟩
  · simp only [map_pow]
    rw [← pow_mul _ 3 p, mul_comm 3 p, pow_mul]
    generalize IsLocalRing.residue W g ^ p = G at *
    rw [e2]
    linear_combination G ^ 3 * e4
  · lift x to W using hx
    have hy' : y ∈ W := by
      have := add_mem (W.nonunits_subset hy) (a * x ^ p).2
      simpa using this
    lift y to W using hy'
    have e5 := (sub_mem_nonunits_iff W y (a * x ^ p)).mp hy
    refine (sub_mem_nonunits_iff W (g * h * y) ((g * h * x) ^ p)).mpr ?_
    simp only [map_mul, map_pow, mul_pow] at e5 ⊢
    generalize IsLocalRing.residue W g ^ p = G at *
    generalize IsLocalRing.residue W h ^ p = H at *
    rw [e2, e3, e5]
    linear_combination G * H * IsLocalRing.residue W x ^ p * e4

theorem norm_sq_eq_absNorm {K : Type*} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (π : 𝓞 K) :
    ‖σ π‖ ^ 2 = Ideal.absNorm (Ideal.span {π}) := by
  have h1 : Fintype.card (InfinitePlace K) = 1 := by
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h4 := IsTotallyComplex.nrRealPlaces_eq_zero K
    omega
  have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp h1.le
  have h5 := InfinitePlace.prod_eq_abs_norm (π : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk σ), IsTotallyComplex.mult_eq,
    InfinitePlace.apply] at h5
  rw [h5, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

theorem weber_congruences : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ (W : ValuationSubring ℂ) (π : 𝓞 K) (p : ℕ), p.Prime → 5 ≤ p → Ideal.absNorm (Ideal.span {π}) = p → ((π : K) : ℂ) ∈ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∈ W ∧ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ^ p ∈ W.nonunits ∧ ∀ (m : ℕ), Odd m → ¬ p ∣ m → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ∈ W ∧ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (((π : K) : ℂ) * t)) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ^ p ∈ W.nonunits) ∧ ((L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∉ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - 1 ∉ W.nonunits → ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice) := by
  intro K _ _ hK L hL W π p hp h5 hN hπ
  have hcm : ∀ a : 𝓞 K, ∀ z ∈ L.lattice, ((a : K) : ℂ) * z ∈ L.lattice := fun a z hz ↦ by
    obtain ⟨b, rfl⟩ := (hL z).mp hz
    exact (hL _).mpr ⟨a * b, by simp⟩
  have hj := mem_of_isIntegral W
    (CMCurves.isIntegral_latticeJ hK (K.val : K →+* ℂ) L hcm)
  have hn : ‖((π : K) : ℂ)‖ ^ 2 = p := by
    rw [← hN]; exact norm_sq_eq_absNorm hK (K.val : K →+* ℂ) π
  have hπi : IsIntegral ℤ ((π : K) : ℂ) :=
    (RingOfIntegers.isIntegral_coe π).map (K.val : K →+* ℂ).toIntAlgHom
  have hpW : (p : ℂ) ∈ W.nonunits := by
    have := mul_mem_nonunits W hπ
      (mem_of_isIntegral W (hπi.map (starRingEnd ℂ).toIntAlgHom))
    convert this using 1
    change _ = _ * (starRingEnd ℂ) _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  have i2 : (2 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 2) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have i3 : (3 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 3) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have hΔ := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (n := 12) (by norm_num)
  have hc0 : c ≠ 0 := by rintro rfl; exact hΔ (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  generalize scalePeriods L c hc0 = L' at H
  have hΔ' : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = 1 := by
    rw [H.g₂_eq, H.g₃_eq]; field_simp; linear_combination -hc
  have eJ : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = L'.g₂ ^ 3 := by
    rw [H.g₂_eq, ← hc]; field_simp
  have eW : ∀ t, L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t =
      L'.g₂ * L'.g₃ * L'.weierstrassP (c * t) := fun t ↦ by
    rw [H.g₂_eq, H.g₃_eq, H.weierstrassP_mul, ← hc]; field_simp
  have hJ : L'.g₂ ^ 3 ∈ W := by
    have := mul_mem (mul_mem (pow_mem i2 6) (pow_mem i3 3)) hj
    convert this using 1
    rw [← eJ, CMCurves.latticeJ]; ring
  have hg := mem_of_pow_mem W three_ne_zero hJ
  have hh : L'.g₃ ∈ W := by
    refine mem_of_pow_mem W two_ne_zero ?_
    have := mul_mem (pow_mem i3 3) (sub_mem hJ (one_mem W))
    convert this using 1
    linear_combination (-1 / 27 : ℂ) * hΔ'
  have hD : (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)⁻¹ ∈ W := by rw [hΔ', inv_one]; exact one_mem W
  obtain ⟨a, ha, -, -, a2, a3, a4⟩ := _root_.GlobalTheory.EisensteinCongruence.weierstrassP_mul_congr_pow L' W ((π : K) : ℂ) p i2 i3 hg hh hD hp hpW hπ
    (fun l hl ↦ by
      obtain ⟨z, rfl⟩ : ∃ z, l = c * z := ⟨c⁻¹ * l, by field_simp⟩
      rw [mul_left_comm]
      exact (H _).mpr (hcm π z ((H z).mp hl))) hn
  obtain ⟨c1, c2⟩ := congruences W hp hpW hg hh ha hΔ' a2 a3
  simp only [eW]
  rw [eJ]
  refine ⟨hJ, c1, fun m hm hpm ↦ ?_⟩
  have im := inv_natCast_mem W hp hpW hpm
  obtain ⟨t1, t2⟩ := _root_.GlobalTheory.TorsionIntegral.torsion_integral_distinct L' W m i2 i3 hg hh hD hm im
  have s1 : ∀ t, (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (c * t) ∈ L'.lattice := fun t ht ↦ by
    rw [mul_left_comm]; exact (H _).mpr ht
  refine ⟨fun t ht ht' ↦ ?_, fun n1 n2 t t' ht ht0 ht' ht0' h ↦ ?_⟩
  · have hx := t1 (c * t) (s1 t ht) ((H t).not.mpr ht')
    refine ⟨mul_mem (mul_mem hg hh) hx, c2 _ _ hx ?_⟩
    rw [mul_left_comm]
    exact a4 m (c * t) hm im (s1 t ht) ((H t).not.mpr ht')
  · have n3 : L'.g₂ ∉ W.nonunits := fun h ↦ n1 (by
      simpa [pow_succ'] using mul_mem_nonunits W h (pow_mem hg 2))
    have n4 : L'.g₃ ∉ W.nonunits := fun h ↦ n2 (by
      have := mul_mem_nonunits W h (mul_mem (ofNat_mem W 27) hh)
      convert this using 1
      linear_combination hΔ')
    rw [← mul_sub, mul_assoc] at h
    have := t2 (c * t) (c * t') (s1 t ht) ((H t).not.mpr ht0) (s1 t' ht') ((H t').not.mpr ht0')
      (mem_nonunits_of_mul W n4 (mem_nonunits_of_mul W n3 h))
    rwa [← mul_sub, ← mul_add, H, H] at this

end GlobalTheory.WeberCongruence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPMulCongrFrobeniusOfPrimeNorm
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.EisensteinCongruence

theorem weierstrassP_mul_congr_pow_of_pos : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (α : ℂ) (p : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → p.Prime → (p : ℂ) ∈ W.nonunits → α ∈ W.nonunits → (∀ l ∈ L.lattice, α * l ∈ L.lattice) → ‖α‖ ^ 2 = p → ∃ a : ℂ, a ∈ W ∧ a⁻¹ ∈ W ∧ a ≠ 0 ∧ L.g₂ - a ^ 2 * L.g₂ ^ p ∈ W.nonunits ∧ L.g₃ - a ^ 3 * L.g₃ ^ p ∈ W.nonunits ∧ ∀ (m : ℕ) (t : ℂ), 0 < m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP (α * t) - a * L.weierstrassP t ^ p ∈ W.nonunits := by
  intro L W α p h2 h3 hg₂ hg₃ hΔ hp hpW hαW hα hN
  have hΔ0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := TorsionIntegral.disc L
  have h0 : α ≠ 0 := by
    rintro rfl
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hN
    exact hp.ne_zero (by exact_mod_cast hN.symm)
  haveI : Fact p.Prime := ⟨hp⟩
  set ρ := IsLocalRing.residue W with hρ
  have hpk : (p : IsLocalRing.ResidueField W) = 0 := by
    rw [← map_natCast ρ, residue_eq_zero_iff']
    simpa using hpW
  haveI : CharP (IsLocalRing.ResidueField W) p := (CharP.charP_iff_prime_eq_zero hp).mpr hpk
  have hcop : ∀ m : ℕ, 0 < m → (m : ℂ)⁻¹ ∈ W → p.Coprime m := by
    intro m hm hmW
    rw [hp.coprime_iff_not_dvd, ← CharP.cast_eq_zero_iff (IsLocalRing.ResidueField W) p,
      ← map_natCast ρ]
    apply residue_ne_zero_of_inv_mem
    · simpa using hm.ne'
    · simpa using hmW
  obtain ⟨A, D, hD, hAd, hDd, hev, hode⟩ := exists_weierstrassP_mul_ode L α p h0 hα hN
  obtain ⟨c, A₀, D₀, hc, hA₀, hD₀, hne⟩ := exists_scaling W A D hD
  have hmul : ∀ (m : ℕ) (t : ℂ), (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (α * t) ∈ L.lattice := by
    intro m t h
    have := hα _ h
    rwa [mul_left_comm] at this

  have rel : ∀ (m : ℕ) (t : ℂ), 0 < m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice →
      t ∉ L.lattice → ∃ x y : W, (x : ℂ) = L.weierstrassP t ∧ (y : ℂ) = L.weierstrassP (α * t) ∧
        (A₀.map ρ).eval (ρ x) = ρ y * (D₀.map ρ).eval (ρ x) := by
    intro m t hm hmW hmt ht
    have hαt : α * t ∉ L.lattice := fun h => ht (mem_of_mul_mem L h0 hα hN (hcop m hm hmW) hmt h)
    have T := (_root_.GlobalTheory.TorsionIntegralPos.torsion_integral_distinct_of_pos L W m h2 h3 hg₂ hg₃ hΔ hm hmW).1
    refine ⟨⟨_, T t hmt ht⟩, ⟨_, T _ (hmul m t hmt) hαt⟩, rfl, rfl, ?_⟩
    rw [eval_map_apply, eval_map_apply, ← map_mul]
    congr 1
    apply W.subtype_injective
    rw [map_mul, ← eval_map_apply, ← eval_map_apply, hA₀, hD₀]
    obtain ⟨e1, e2⟩ := hev t hαt
    simp only [eval_mul, eval_C, ValuationSubring.coe_subtype]
    rw [e2]
    field_simp
  have h3n : ∀ n : ℕ, ((3 ^ n : ℕ) : ℂ)⁻¹ ∈ W := fun n => by
    rw [Nat.cast_pow, ← inv_pow]
    exact pow_mem (by simpa using h3) n
  have hpos : ∀ n : ℕ, 0 < 3 ^ n := fun n => by positivity
  have hpow : ∀ i j : ℕ, i + 1 ≤ j → ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (i + 1)) ∈ L.lattice := by
    intro i j hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    convert L.lattice.smul_mem ((3 : ℤ) ^ d) L.ω₁_mem_lattice using 1
    simp only [zsmul_eq_mul]
    push_cast
    field_simp
    ring
  have hthird : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (j + 1)) = L.ω₁ / 3 := by
    intro j
    push_cast
    field_simp
    ring
  have hns : ∀ (n : ℕ) (z : ℂ), z ∈ L.lattice → (n : ℂ) * z ∈ L.lattice := fun n z hz => by
    simpa using L.lattice.smul_mem (n : ℤ) hz
  have hnot : ∀ j : ℕ, L.ω₁ / 3 ^ (j + 1) ∉ L.lattice := fun j h =>
    third_notMem L (hthird j ▸ hns _ _ h)
  have h33 : ((3 : ℕ) : ℂ) * (L.ω₁ / 3) ∈ L.lattice := by simpa using hpow 0 1 le_rfl
  have hαthird : α * (L.ω₁ / 3) ∉ L.lattice := fun h => third_notMem L
    (mem_of_mul_mem L h0 hα hN (hcop 3 (by decide) (by simpa using h3)) h33 h)

  have dist : ∀ β : ℂ, (∀ l ∈ L.lattice, β * l ∈ L.lattice) → β * (L.ω₁ / 3) ∉ L.lattice →
      ∀ x : ℕ → W, (∀ j, (x j : ℂ) = L.weierstrassP (β * (L.ω₁ / 3 ^ (j + 1)))) →
      Function.Injective fun j => ρ (x j) := by
    intro β hβ hβ3 x hx
    have hm : ∀ i j : ℕ, i + 1 ≤ j →
        ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (i + 1))) ∈ L.lattice := by
      intro i j hij
      rw [mul_left_comm]
      exact hβ _ (hpow i j hij)
    have hn : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (j + 1))) ∉ L.lattice := by
      intro j
      rw [mul_left_comm, hthird]
      exact hβ3
    refine Function.Injective.of_lt_imp_ne fun i j hij h => ?_
    have T := (_root_.GlobalTheory.TorsionIntegralPos.torsion_integral_distinct_of_pos L W (3 ^ (j + 1)) h2 h3 hg₂ hg₃ hΔ
      (hpos _) (h3n _)).2 _ _ (hm i _ (by omega)) (fun h => hn i (hns _ _ h))
      (hm j _ le_rfl) (fun h => hn j (hns _ _ h)) (by
        rw [← hx, ← hx]
        have : ρ (x i - x j) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr h
        exact (residue_eq_zero_iff' W _).mp this)
    apply hn j
    rcases T with T | T
    · convert L.lattice.sub_mem (hm i j hij) (hns (3 ^ j) _ T) using 1
      ring
    · convert L.lattice.sub_mem (hns (3 ^ j) _ T) (hm i j hij) using 1
      ring
  choose x y hx hy hxy using fun j : ℕ =>
    rel (3 ^ (j + 1)) (L.ω₁ / 3 ^ (j + 1)) (hpos _) (h3n _) (hpow j _ le_rfl) (hnot j)
  have hxi := dist 1 (by simp) (by simpa using third_notMem L) x (by simpa using hx)
  have hyi := dist α hα hαthird y hy
  let g₂ : W := ⟨L.g₂, hg₂⟩
  let g₃ : W := ⟨L.g₃, hg₃⟩
  let α₀ : W := ⟨α, W.nonunits_subset hαW⟩
  have hode' : C (α ^ 2) * (C c * D) * (4 * (C c * A) ^ 3 - C L.g₂ * (C c * A) * (C c * D) ^ 2 -
      C L.g₃ * (C c * D) ^ 3) = (derivative (C c * A) * (C c * D) -
        (C c * A) * derivative (C c * D)) ^ 2 * (4 * X ^ 3 - C L.g₂ * X - C L.g₃) := by
    simp only [derivative_C_mul]
    linear_combination C c ^ 4 * hode
  have hode₀ : C (α₀ ^ 2) * D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3) =
      (derivative A₀ * D₀ - A₀ * derivative D₀) ^ 2 * (4 * X ^ 3 - C g₂ * X - C g₃) := by
    apply Polynomial.map_injective W.subtype W.subtype_injective
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
      Polynomial.map_ofNat, ← derivative_map, hA₀, hD₀]
    exact hode'
  have hdvd₀ : (4 * X ^ 3 - C g₂ * X - C g₃ : W[X]) ∣
      D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3) := by
    apply cubic_dvd W h2
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C,
      Polynomial.map_ofNat, hA₀, hD₀]
    have hu : IsUnit (C (α ^ 2) : ℂ[X]) := isUnit_C.mpr (Ne.isUnit (pow_ne_zero _ h0))
    rw [← hu.dvd_mul_left, ← mul_assoc]
    exact Dvd.intro_left _ hode'.symm
  have hdeg : ∀ (B₀ : W[X]) (B : ℂ[X]), B₀.map W.subtype = C c * B →
      (B₀.map ρ).natDegree ≤ B.natDegree := by
    intro B₀ B h
    refine natDegree_map_le.trans ?_
    rw [← natDegree_map_eq_of_injective W.subtype_injective, h, natDegree_C_mul hc]
  have hα₀ : ρ α₀ = 0 := (residue_eq_zero_iff' W _).mpr hαW
  obtain ⟨a, d, ha, hd, eD, eA, e2, e3⟩ := residue_form p (ρ g₂) (ρ g₃) (A₀.map ρ) (D₀.map ρ)
    (by
      rw [← map_ofNat ρ 2]
      exact residue_ne_zero_of_inv_mem W _ (two_ne_zero (α := ℂ)) h2)
    (by
      rw [← map_ofNat ρ 3]
      exact residue_ne_zero_of_inv_mem W _ (three_ne_zero (α := ℂ)) h3)
    (by
      have := residue_ne_zero_of_inv_mem W (g₂ ^ 3 - 27 * g₃ ^ 2) hΔ0 hΔ
      simpa [map_ofNat] using this)
    hne (hAd ▸ hdeg A₀ A hA₀) (lt_of_le_of_lt (hdeg D₀ D hD₀) (by omega))
    _ _ hxi hyi hxy
    (by
      have := congrArg (Polynomial.map ρ) hode₀
      simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
        Polynomial.map_ofNat, ← derivative_map, map_pow, hα₀, map_zero] at this
      rw [← this]
      ring)
    (by
      have := Polynomial.map_dvd ρ hdvd₀
      simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
        Polynomial.map_ofNat] using this)
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
  have ha' : (a₀ : ℂ) ∉ W.nonunits := fun h => ha ((residue_eq_zero_iff' W _).mpr h)
  rw [W.mem_nonunits_iff_or] at ha'
  push Not at ha'
  refine ⟨a₀, a₀.2, ha'.2, ha'.1, ?_, ?_, ?_⟩
  · refine (residue_eq_zero_iff' W (g₂ - a₀ ^ 2 * g₂ ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow, map_pow]
    exact sub_eq_zero.mpr e2
  · refine (residue_eq_zero_iff' W (g₃ - a₀ ^ 3 * g₃ ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow, map_pow]
    exact sub_eq_zero.mpr e3
  · intro m t hm hmW hmt ht
    obtain ⟨u, v, hu, hv, huv⟩ := rel m t hm hmW hmt ht
    rw [← hu, ← hv]
    refine (residue_eq_zero_iff' W (v - a₀ * u ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow]
    rw [eA, eD] at huv
    simp only [eval_mul, eval_C, eval_pow, eval_X] at huv
    apply mul_left_cancel₀ hd
    linear_combination -huv

end GlobalTheory.EisensteinCongruence
end

