module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Sinnott
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinnott :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [Nonempty ι] (η : ι → ℤ_[l]ˣ) (N : ℕ), N ≠ 0 → (∀ i j, i ≠ j → ∀ a b : ℤ, (a : ℤ_[l]) * η i = (b : ℤ_[l]) * η j → a = 0) → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (k : Type) [CommRing k] (P : ℕ → k) (α : ZMod (l ^ n) → k), (∀ y, α y - α (y - N) = ∑ s ∈ Finset.range N, if (s : ZMod (l ^ n)) = y then P s else 0) → (∀ y, ∑ i, α (((redU l n (η i))⁻¹ : (ZMod (l ^ n))ˣ) * y) = 0) → ∀ s < N, P s = 0 := by
  intro l _ ι _ _ η N hN hind
  classical
  obtain ⟨S, hS⟩ := sinSupp ℤ_[l] ι (fun i => (η i : ℤ_[l])) N
  obtain ⟨n₀, hn₀⟩ := sep l S
  refine ⟨n₀, fun n hn k _ P α h1 h2 => ?_⟩
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h3 := sinFin k ι (l ^ n) (fun i => redU l n (η i)) N P α h1 h2
  have h4 := sinMap k ℤ_[l] (ZMod (l ^ n)) ι
    (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toAddMonoidHom (fun i => (η i : ℤ_[l])) N P
  have h5 : AddMonoidAlgebra.mapDomainRingHom k
      (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toAddMonoidHom
      (sinE (fun i => (η i : ℤ_[l])) N P) = 0 := h4.trans h3
  have h6 : Finsupp.mapDomain (PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n))
      (sinE (fun i => (η i : ℤ_[l])) N P).coeff = 0 := by
    have := congrArg AddMonoidAlgebra.coeff h5
    simpa using this
  have h7 : (sinE (fun i => (η i : ℤ_[l])) N P).coeff = 0 := by
    apply Finsupp.mapDomain_injOn (S : Set ℤ_[l]) (hn₀ n hn)
    · intro a ha
      exact hS k P a (Finsupp.mem_support_iff.mp ha)
    · simp
    · simpa using h6
  refine sinLem k ℤ_[l] ι (fun i => (η i : ℤ_[l])) N P hN ?_ ?_ ?_
  · intro i m hm
    simp only [zsmul_eq_mul] at hm
    have := (Units.mul_left_eq_zero (η i)).mp hm
    exact_mod_cast this
  · intro i j hij a b hab
    simp only [zsmul_eq_mul] at hab
    exact hind i j hij a b hab
  · ext a
    simp [h7]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Struct
section
open UpperTheory.V.FW

private theorem ee_bd (l : ℕ) : 1 ≤ ee l ∧ ee l ≤ 2 := by
  unfold ee; split_ifs <;> omega

private theorem neg_mem_WW (l : ℕ) [hl : Fact l.Prime] : (-1 : ℤ_[l]ˣ) ∈ WW l := by
  have h2 : 2 < l ^ ee l := by
    unfold ee
    split_ifs with h
    · subst h; norm_num
    · have := hl.out.two_le
      rw [pow_one]; omega
  unfold WW
  rw [mem_rootsOfUnity]
  exact (Nat.totient_even h2).neg_one_pow

private theorem red_red (l : ℕ) [Fact l.Prime] (m n : ℕ) (hmn : m ≤ n) (w : ℤ_[l]ˣ) :
    ZMod.unitsMap (pow_dvd_pow l hmn) (redU l n w) = redU l m w := by
  ext
  simp only [ZMod.unitsMap_def, redU, Units.coe_map, MonoidHom.coe_coe]
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n hmn) (w : ℤ_[l])

theorem UpperTheory.V.FW.struct :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ), f.Coprime l → 2 ≤ n → ∃ (γ : (ZMod (f * l ^ n))ˣ) (p : (ZMod (f * l ^ n))ˣ →* (ZMod (f * l ^ n))ˣ), (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l ∧ γ ^ l ^ n = 1 ∧ (Subgroup.zpowers γ).index = Nat.totient (f * l ^ ee l) ∧ (∀ g, p g ∈ Subgroup.zpowers γ) ∧ (∀ g, (g * (p g)⁻¹) ^ Nat.totient (f * l ^ ee l) = 1) ∧ p (-1) = 1 ∧ ∀ (n₀ : ℕ) (h : l ^ n₀ ∣ f * l ^ n), n₀ ≤ n → (∀ g, piQ l n₀ h (p g) = piQ l n₀ h g) ∧ piQ l n₀ h γ ^ l ^ n₀ = 1 := by
  intro l _ f n hf hn
  have hl : l.Prime := Fact.out
  have hee := ee_bd l
  have hen : ee l ≤ n := by omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hf
    exact hl.one_lt.ne' hf
  have hdiv : f * l ^ ee l ∣ f * l ^ n := Nat.mul_dvd_mul_left f (pow_dvd_pow l hen)
  have hdiv' : l ^ n ∣ f * l ^ n := Dvd.intro_left f rfl
  haveI : NeZero (f * l ^ n) := ⟨mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (f * l ^ ee l) := ⟨mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  have hnil : IsNilpotent ((f : ZMod (f * l ^ n)) * (l : ZMod (f * l ^ n)) ^ ee l) := by
    refine ⟨n, ?_⟩
    have hz : ((f ^ n * l ^ (ee l * n) : ℕ) : ZMod (f * l ^ n)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.mul_dvd_mul (dvd_pow_self f (by omega))
        (pow_dvd_pow l (Nat.le_mul_of_pos_left n (by omega)))
    rw [mul_pow, ← pow_mul]
    exact_mod_cast hz
  obtain ⟨γ, hγ⟩ := hnil.isUnit_one_add
  obtain ⟨hker, hγpow⟩ := gamGen l f n hdiv γ hf hen hγ
  have hbij := deltaBij l f n hdiv hdiv' hf hen
  let e := MulEquiv.ofBijective _ hbij
  let σ : (ZMod (f * l ^ n))ˣ →* (ZMod (f * l ^ n))ˣ :=
    (Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l))).subtype.comp
      (e.symm.toMonoidHom.comp (ZMod.unitsMap hdiv))
  have hσπ : ∀ g, ZMod.unitsMap hdiv (σ g) = ZMod.unitsMap hdiv g := fun g =>
    e.apply_symm_apply (ZMod.unitsMap hdiv g)
  have hσH : ∀ x ∈ Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l)),
      σ x = x := by
    intro x hx
    have h1 : ZMod.unitsMap hdiv x = e ⟨x, hx⟩ := rfl
    show ((e.symm (ZMod.unitsMap hdiv x) : _) : (ZMod (f * l ^ n))ˣ) = x
    rw [h1, e.symm_apply_apply]
  have hcard : Nat.card (ZMod (f * l ^ ee l))ˣ = (f * l ^ ee l).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hσpow : ∀ g, σ g ^ (f * l ^ ee l).totient = 1 := by
    intro g
    have h1 : (ZMod.unitsMap hdiv g) ^ (f * l ^ ee l).totient = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    show ((e.symm (ZMod.unitsMap hdiv g) : _) : (ZMod (f * l ^ n))ˣ) ^ _ = 1
    rw [← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]
  let p : (ZMod (f * l ^ n))ˣ →* (ZMod (f * l ^ n))ˣ := MonoidHom.id _ / σ
  have hp : ∀ g, p g = g / σ g := fun g => rfl
  have hQ : ∀ (n₀ : ℕ) (h : l ^ n₀ ∣ f * l ^ n), n₀ ≤ n →
      ∀ x ∈ Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l)),
      piQ l n₀ h x = 1 := by
    intro n₀ h hn₀ x hx
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)
    have hc := DFunLike.congr_fun (ZMod.unitsMap_comp (pow_dvd_pow l hn₀) hdiv') x
    simp only [MonoidHom.comp_apply] at hc
    show (QuotientGroup.mk' _) (ZMod.unitsMap h x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨w, hw, ?_⟩
    rw [← red_red l n₀ n hn₀ w, hwx]
    exact hc
  refine ⟨γ, p, hγ, hγpow, ?_, ?_, ?_, ?_, ?_⟩
  · have hsurj : Function.Surjective (ZMod.unitsMap hdiv) := fun y => by
      obtain ⟨x, hx⟩ := hbij.2 y
      exact ⟨x.1, hx⟩
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcard]
  · intro g
    rw [← hker, MonoidHom.mem_ker, hp, map_div, hσπ, div_self']
  · intro g
    rw [hp, inv_div, mul_div_cancel]
    exact hσpow g
  · have hm : (-1 : (ZMod (f * l ^ n))ˣ) ∈
        Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l)) := by
      rw [Subgroup.mem_comap, Subgroup.mem_map]
      refine ⟨-1, neg_mem_WW l, ?_⟩
      ext
      simp [redU, ZMod.unitsMap_def]
    rw [hp, hσH _ hm, div_self']
  · intro n₀ h hn₀
    refine ⟨fun g => ?_, ?_⟩
    · rw [hp, map_div, hQ n₀ h hn₀ (σ g) (e.symm (ZMod.unitsMap hdiv g)).2, div_one]
    · haveI : NeZero (l ^ n₀) := ⟨pow_ne_zero _ hl.ne_zero⟩
      have h1 : ZMod.unitsMap h γ ^ l ^ n = 1 := by rw [← map_pow, hγpow, map_one]
      have h2 : ZMod.unitsMap h γ ^ (l ^ n₀).totient = 1 := by
        rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
        exact pow_card_eq_one'
      obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one h1)
      have hle : l ^ j ≤ l ^ n₀ := by
        rw [← hjx]
        exact (Nat.le_of_dvd (Nat.totient_pos.mpr (pow_pos hl.pos _))
          (orderOf_dvd_of_pow_eq_one h2)).trans (Nat.totient_le _)
      have hj0 : j ≤ n₀ := (Nat.pow_le_pow_iff_right hl.one_lt).mp hle
      have hx : ZMod.unitsMap h γ ^ l ^ n₀ = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hjx]
        exact pow_dvd_pow l hj0
      show (QuotientGroup.mk' _) (ZMod.unitsMap h γ) ^ l ^ n₀ = 1
      rw [← map_pow, hx, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwCoef
section
open UpperTheory.V.FW

private theorem push_units {k : Type} [CommRing k] {M : ℕ} [NeZero M] {m : ℕ} (h : m ∣ M)
    (χ : (ZMod M)ˣ →* kˣ) (g : ZMod M → k) (z : ZMod m) :
    push h (fun s => g s * MulChar.ofUnitHom χ s) z =
      ∑ s : (ZMod M)ˣ with ((ZMod.unitsMap h s : (ZMod m)ˣ) : ZMod m) = z, g s * (χ s : k) := by
  classical
  unfold push
  symm
  refine Finset.sum_bij_ne_zero (fun (u : (ZMod M)ˣ) _ _ => (u : ZMod M)) ?_ ?_ ?_ ?_
  · intro u hu _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [← hu]
    rfl
  · intro u₁ _ _ u₂ _ _ h12
    exact Units.ext h12
  · intro s hs hne
    have hu : IsUnit s := by
      by_contra hn
      apply hne
      show g s * (MulChar.ofUnitHom χ) s = 0
      rw [MulChar.map_nonunit _ hn, mul_zero]
    refine ⟨hu.unit, ?_, ?_, hu.unit_spec⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [← hs]
      show (ZMod.castHom h (ZMod m)) (hu.unit : ZMod M) = _
      rw [hu.unit_spec]
    · have hne' : g s * (MulChar.ofUnitHom χ) s ≠ 0 := hne
      rwa [← hu.unit_spec, MulChar.ofUnitHom_coe] at hne'
  · intro u _ _
    show g u * (χ u : k) = g u * (MulChar.ofUnitHom χ) u
    rw [MulChar.ofUnitHom_coe]

private theorem half_val {M : ℕ} [NeZero M] (hM : 2 < M) (s : (ZMod M)ˣ) :
    2 * ((-s : (ZMod M)ˣ) : ZMod M).val < M ↔ ¬ 2 * (s : ZMod M).val < M := by
  haveI : Fact (1 < M) := ⟨by omega⟩
  have hs0 : (s : ZMod M) ≠ 0 := s.ne_zero
  have hv : (s : ZMod M).val < M := ZMod.val_lt _
  have hne : 2 * (s : ZMod M).val ≠ M := by
    intro h2
    have h3 : ((2 * (s : ZMod M).val : ℕ) : ZMod M) = 0 := by
      rw [h2]
      exact ZMod.natCast_self M
    push_cast at h3
    rw [ZMod.natCast_zmod_val] at h3
    have h4 : (2 : ZMod M) = 0 := by
      have := congrArg (· * ((s⁻¹ : (ZMod M)ˣ) : ZMod M)) h3
      simpa [mul_assoc] using this
    have h5 : ((2 : ℕ) : ZMod M) = 0 := by exact_mod_cast h4
    rw [ZMod.natCast_eq_zero_iff] at h5
    have := Nat.le_of_dvd (by norm_num) h5
    omega
  rw [Units.val_neg, ZMod.neg_val, if_neg hs0]
  omega

theorem UpperTheory.V.FW.twCoef :
    ∀ (l : ℕ) [Fact l.Prime] (M n₀ : ℕ) [NeZero M] (h : l ^ n₀ ∣ M) (k : Type) [CommRing k] (χ : (ZMod M)ˣ →* kˣ) (g : ZMod M → ℤ) (R : Finset ℤ_[l]ˣ), 2 ≤ n₀ → χ (-1) = -1 → (∀ s : (ZMod M)ˣ, g (-(s : ZMod M)) = -g s) → (∀ r ∈ R, r ∈ WW l) → (∀ r ∈ R, -r ∉ R) → (∀ w ∈ WW l, w ∈ R ∨ -w ∈ R) → tw χ (piQ l n₀ h) (toK k _ (∑ s ∈ Finset.univ.filter fun s : (ZMod M)ˣ => 2 * (s : ZMod M).val < M, MonoidAlgebra.single s (g s))) = 0 → ∀ y : ZMod (l ^ n₀), ∑ r : R, push h (fun s => (g s : k) * MulChar.ofUnitHom χ s) (((redU l n₀ r.1)⁻¹ : (ZMod (l ^ n₀))ˣ) * y) = 0 := by
  intro l _ M n₀ _ h k _ χ g R hn₀ hχ hg hRW hRneg hWR htw y
  classical
  have hl : l.Prime := Fact.out
  have hM : 2 < M := by
    have h4 : 4 ≤ l ^ n₀ :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ l ^ 2 := Nat.pow_le_pow_left hl.two_le 2
        _ ≤ l ^ n₀ := Nat.pow_le_pow_right hl.pos hn₀
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h
    omega
  have hneg1 : (-1 : ℤ_[l]ˣ) ∈ WW l := by
    show (-1 : ℤ_[l]ˣ) ∈ rootsOfUnity (l ^ ee l).totient ℤ_[l]
    rw [mem_rootsOfUnity]
    apply Even.neg_one_pow
    apply Nat.totient_even
    have h2 := hl.two_le
    unfold ee
    split_ifs with h2'
    · subst h2'
      norm_num
    · rw [pow_one]
      omega
  have hnegmem : ∀ v ∈ WW l, -v ∈ WW l := fun v hv => by
    rw [← neg_one_mul v]
    exact mul_mem hneg1 hv
  obtain ⟨-, -, -, -, -, -, -, hinj⟩ := reps l
  have hredneg : ∀ v : ℤ_[l]ˣ, redU l n₀ (-v) = -redU l n₀ v := fun v => by
    ext
    simp [redU]
  have hρneg : ∀ x : (ZMod M)ˣ, ZMod.unitsMap h (-x) = -ZMod.unitsMap h x := fun x => by
    ext
    simp [ZMod.unitsMap_def]
  have hredinj : ∀ v ∈ WW l, ∀ w ∈ WW l, redU l n₀ v = redU l n₀ w → v = w := by
    intro v hv w hw hvw
    have h1 : redU l n₀ (v * w⁻¹) = 1 := by rw [map_mul, map_inv, hvw, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj n₀ hn₀ _ (mul_mem hv (inv_mem hw)) h1)
  have hcoef : ∀ q, ∑ s ∈ (Finset.univ.filter fun s : (ZMod M)ˣ => 2 * (s : ZMod M).val < M).filter
      (fun s => piQ l n₀ h s = q), (g s : k) * (χ s : k) = 0 := by
    intro q
    have h1 := congrArg (fun x => MonoidAlgebra.coeff x q) htw
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, toK, MonoidAlgebra.mapRingHom_single, eq_intCast, tw_single,
      MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.single_apply,
      MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    rw [Finset.sum_filter]
    exact h1
  have hpu : ∀ z, push h (fun s => (g s : k) * MulChar.ofUnitHom χ s) z =
      ∑ s : (ZMod M)ˣ with ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) = z,
        (g s : k) * (χ s : k) := fun z => push_units h χ (fun s => (g s : k)) z
  simp only [hpu]
  by_cases hy : IsUnit y
  swap
  · apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro s hs
    exfalso
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    apply hy
    have : y = ((redU l n₀ r.1 : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) *
        ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) := by
      rw [hs, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [this]
    exact (Units.isUnit _).mul (Units.isUnit _)
  obtain ⟨u, rfl⟩ := hy
  let t : R → Finset (ZMod M)ˣ := fun r =>
    Finset.univ.filter fun s => ZMod.unitsMap h s = (redU l n₀ r.1)⁻¹ * u
  have hgoal : ∀ r : R, ∑ s ∈ Finset.univ.filter (fun s : (ZMod M)ˣ =>
      ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) =
        (((redU l n₀ r.1)⁻¹ : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) * (u : ZMod (l ^ n₀))),
      (g s : k) * (χ s : k) = ∑ s ∈ t r, (g s : k) * (χ s : k) := fun r =>
    Finset.sum_congr (Finset.filter_congr (fun s _ => by rw [Units.ext_iff, Units.val_mul]))
      (fun _ _ => rfl)
  refine Eq.trans (Finset.sum_congr rfl (fun r _ => hgoal r)) ?_
  have hdisj : (↑(Finset.univ : Finset R) : Set R).PairwiseDisjoint t := by
    intro r₁ _ r₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hs1 hs2
    apply hne
    apply Subtype.ext
    apply hredinj _ (hRW _ r₁.2) _ (hRW _ r₂.2)
    have h12 := hs1.symm.trans hs2
    rw [mul_left_inj, inv_inj] at h12
    exact h12
  refine Eq.trans (Finset.sum_biUnion hdisj).symm ?_
  have hπ : ∀ v ∈ WW l, ∀ x : (ZMod M)ˣ, ZMod.unitsMap h x = (redU l n₀ v)⁻¹ * u →
      piQ l n₀ h x = QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) u := by
    intro v hv x hx
    have h1 : QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) (redU l n₀ v)⁻¹ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact inv_mem (Subgroup.mem_map_of_mem _ hv)
    show QuotientGroup.mk' _ (ZMod.unitsMap h x) = _
    rw [hx, map_mul, h1, one_mul]
  refine Eq.trans (halfSum (ZMod M)ˣ k Neg.neg _ _ (fun s => (g s : k) * (χ s : k))
    ?_ ?_ ?_ ?_ ?_ ?_) (hcoef (QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) u))
  · exact fun x => neg_neg x
  · intro x
    have hχx : (χ (-x) : k) = -(χ x : k) := by
      rw [← neg_one_mul x, map_mul, hχ, Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul]
    show ((g ((-x : (ZMod M)ˣ) : ZMod M)) : k) * (χ (-x) : k) = (g x : k) * (χ x : k)
    rw [hχx, Units.val_neg, hg x]
    push_cast
    ring
  · intro x hx hnx
    simp only [t, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and] at hx hnx
    obtain ⟨r, hr⟩ := hx
    obtain ⟨r', hr'⟩ := hnx
    rw [hρneg, hr, ← neg_mul] at hr'
    have h2 := mul_right_cancel hr'
    have h3 : redU l n₀ r'.1 = redU l n₀ (-r.1) := by
      rw [hredneg, ← inv_inj, ← h2, inv_neg]
    have h4 := hredinj _ (hRW _ r'.2) _ (hnegmem _ (hRW _ r.2)) h3
    exact hRneg _ r.2 (h4 ▸ r'.2)
  · intro x hx hnx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hnx
    exact ((half_val hM x).mp hnx.1) hx.1
  · intro x hx
    simp only [t, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and] at hx
    obtain ⟨r, hr⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hh : 2 * (x : ZMod M).val < M
    · exact Or.inl ⟨hh, hπ r.1 (hRW _ r.2) x hr⟩
    · refine Or.inr ⟨(half_val hM x).mpr hh, hπ (-r.1) (hnegmem _ (hRW _ r.2)) (-x) ?_⟩
      rw [hρneg, hr, hredneg, inv_neg, neg_mul]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨-, hq⟩ := hx
    have hq' : QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) (ZMod.unitsMap h x) =
        QuotientGroup.mk' _ u := hq
    rw [QuotientGroup.mk'_eq_mk'] at hq'
    obtain ⟨z, hz, hxz⟩ := hq'
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have hx' : ZMod.unitsMap h x = (redU l n₀ w)⁻¹ * u :=
      eq_inv_mul_of_mul_eq ((mul_comm _ _).trans hxz)
    rcases hWR w hw with hR | hR
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨⟨w, hR⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩⟩)
    · refine Or.inr (Finset.mem_biUnion.mpr ⟨⟨-w, hR⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩)
      show ZMod.unitsMap h (-x) = (redU l n₀ (-w))⁻¹ * u
      rw [hρneg, hx', hredneg, inv_neg, neg_mul]
end

