module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.DvrIntClosure
section
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem UpperTheory.V.abelian₂.isIntegral_iff_norm_le_one_bis {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (φ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : IsIntegral ℤ_[l] x ↔ ‖φ x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖φ x‖ = spectralValue (minpoly ℚ_[l] (φ x)) := rfl
  rw [h0, minpoly.algHom_eq φ φ.injective, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem UpperTheory.V.abelian₂.dvr_intClosure :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
      [FiniteDimensional ℚ_[l] K],
      IsDiscreteValuationRing (integralClosure ℤ_[l] K) ∧ Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) ∧
        IsFractionRing (integralClosure ℤ_[l] K) K := by
  intro l hl K _ _ _ _ _
  let φ : K →ₐ[ℚ_[l]] PadicAlgCl l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hint := UpperTheory.V.abelian₂.isIntegral_iff_norm_le_one_bis φ
  have hunit : ∀ a : integralClosure ℤ_[l] K, ‖φ a‖ = 1 → IsUnit a := by
    intro a ha
    have h0 : (a : K) ≠ 0 := by
      intro h
      rw [h] at ha
      simp at ha
    have hi : IsIntegral ℤ_[l] (a : K)⁻¹ := by
      rw [hint, map_inv₀, norm_inv, ha, inv_one]
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : integralClosure ℤ_[l] K) (Subtype.ext (mul_inv_cancel₀ h0))
  have hloc : IsLocalRing (integralClosure ℤ_[l] K) := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    have ha : ‖φ a‖ ≤ 1 := (hint _).1 a.2
    rcases ha.eq_or_lt with h | h
    · exact Or.inl (hunit a h)
    · refine Or.inr (hunit _ (le_antisymm ((hint _).1 (1 - a).2) ?_))
      by_contra hlt
      push Not at hlt
      have h1 : φ ((1 - a : integralClosure ℤ_[l] K) : K) + φ a = 1 := by simp
      have h2 := (PadicAlgCl.isNonarchimedean l _ _).trans_lt (max_lt hlt h)
      simp only [h1] at h2
      simp at h2
  have hded : IsDedekindDomain (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] K)) := by
    intro a b hab
    have h := congrArg (fun x : integralClosure ℤ_[l] K => (x : K)) hab
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K] at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] K).injective h)
  have hnf : ¬ IsField (integralClosure ℤ_[l] K) := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l] ((Algebra.IsIntegral.isField_iff_isField hinj).2 hf)
  exact ⟨((IsDiscreteValuationRing.TFAE _ hnf).out 1 3).mpr hded,
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K),
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] K⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsUnitAddMem
section
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem binom_prime {R : Type*} [CommRing R] {l : ℕ} (hl : l.Prime) (y : R) :
    ∃ s : R, (1 + y) ^ l - 1 = y ^ l + l * y * (1 + y * s) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl (1 : Polynomial ℤ) Polynomial.X
  have h1 := congrArg (fun p : Polynomial ℤ => p.coeff 1) hr
  have hl1 : (1 : ℕ) ≠ l := hl.one_lt.ne
  have e : ((l : Polynomial ℤ) * 1 * Polynomial.X * r) = Polynomial.C (l : ℤ) * (Polynomial.X * r) := by
    simp [mul_assoc]
  simp only [Polynomial.coeff_one_add_X_pow, Nat.choose_one_right, one_pow, Polynomial.coeff_add,
    Polynomial.coeff_X_pow, if_neg hl1, e, Polynomial.coeff_C_mul, Polynomial.coeff_one] at h1
  have h2 : (Polynomial.X * r).coeff 1 = r.coeff 0 := Polynomial.coeff_X_mul r 0
  rw [h2] at h1
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have h3 : r.coeff 0 = 1 := by
    apply mul_left_cancel₀ hl0
    simpa using h1.symm
  have h4 : r = 1 + Polynomial.X * r.divX := by
    have := Polynomial.X_mul_divX_add r
    rw [h3] at this
    rw [add_comm]
    simpa using this.symm
  refine ⟨Polynomial.aeval y r.divX, ?_⟩
  have h5 := congrArg (Polynomial.aeval y) hr
  rw [h4] at h5
  simp only [map_pow, map_add (f := _), map_one, Polynomial.aeval_X, map_mul, map_natCast] at h5
  rw [h5]
  ring

private theorem binom_one {R : Type*} [CommRing R] (y : R) (n : ℕ) :
    ∃ s : R, (1 + y) ^ n - 1 = y * (n + y * s) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨n + s + y * s, ?_⟩
    rw [pow_succ, sub_eq_iff_eq_add.1 hs]
    push_cast
    ring

private theorem isUnit_add_mem {O : Type*} [CommRing O] [IsLocalRing O] {a b : O} (ha : IsUnit a)
    (hb : b ∈ maximalIdeal O) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ maximalIdeal O := h
  have h2 : a ∈ maximalIdeal O := by simpa using (maximalIdeal O).sub_mem h1 hb
  exact h2 ha

private theorem step_prime {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {l : ℕ} (hl : l.Prime) {y : O} (hy : y ∈ maximalIdeal O)
    (h : addVal O (l : O) < ((l - 1 : ℕ) : ℕ∞) * addVal O y) :
    addVal O ((1 + y) ^ l - 1) = addVal O y + addVal O (l : O) := by
  have h' : addVal O (l : O) < addVal O (y ^ (l - 1)) := by
    rwa [IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul]
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h'.le
  have hcm : c ∈ maximalIdeal O := by
    intro hu
    rw [hc, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu,
      add_zero] at h'
    exact lt_irrefl _ h'
  obtain ⟨s, hs⟩ := binom_prime hl y
  have e : y ^ l = y * (l * c) := by
    rw [← hc, ← pow_succ', Nat.sub_add_cancel hl.one_lt.le]
  have hu : IsUnit (1 + (y * s + c)) :=
    isUnit_add_mem isUnit_one ((maximalIdeal O).add_mem (Ideal.mul_mem_right _ _ hy) hcm)
  have e2 : (1 + y) ^ l - 1 = y * l * (1 + (y * s + c)) := by rw [hs, e]; ring
  rw [e2, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu, add_zero]

private theorem lte_nat {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {l : ℕ} (hl : l.Prime) (hlm : (l : O) ∈ maximalIdeal O) (n : ℕ) :
    ∀ y : O, y ∈ maximalIdeal O → addVal O (l : O) < ((l - 1 : ℕ) : ℕ∞) * addVal O y →
      addVal O ((1 + y) ^ n - 1) = addVal O y + addVal O (n : O) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    by_cases hd : l ∣ n
    · obtain ⟨k, rfl⟩ := hd
      have hk : 0 < k := Nat.pos_of_mul_pos_left hn
      have hlt : k < l * k := lt_mul_of_one_lt_left hk hl.one_lt
      have h1 := step_prime hl hy h
      have hy' : (1 + y) ^ l - 1 ∈ maximalIdeal O := by
        obtain ⟨s, hs⟩ := binom_one y l
        rw [hs]
        exact Ideal.mul_mem_right _ _ hy
      have h2 := ih k hlt _ hy' (h.trans_le (by
        rw [h1]
        gcongr
        exact le_self_add))
      rw [add_sub_cancel, ← pow_mul, h1] at h2
      rw [h2, Nat.cast_mul, IsDiscreteValuationRing.addVal_mul, add_assoc]
    · have hu : IsUnit (n : O) := by
        by_contra hnu
        have hnm : (n : O) ∈ maximalIdeal O := hnu
        have hc : IsCoprime (l : O) (n : O) := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).cast
        obtain ⟨a, b, hab⟩ := hc
        have : (1 : O) ∈ maximalIdeal O :=
          hab ▸ (maximalIdeal O).add_mem (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hnm)
        exact this isUnit_one
      obtain ⟨s, hs⟩ := binom_one y n
      rw [hs, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu,
        IsDiscreteValuationRing.addVal_eq_zero_iff.2 (isUnit_add_mem hu (Ideal.mul_mem_right _ _ hy))]

theorem UpperTheory.V.abelian₂.lte :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (l : ℕ), l.Prime → (l : O) ∈ maximalIdeal O → ∀ u : oneUnits O,
      addVal O (l : O) < ((l - 1 : ℕ) : ℕ∞) * addVal O (pt u : O) → (∀ n : ℤ, addVal O (pt (u ^ n) : O) = addVal O (pt u : O) + addVal O (n : O)) := by
  intro O _ _ _ _ l hl hlm u h n
  have key : ∀ k : ℕ, addVal O (((u : Oˣ) : O) ^ k - 1) = addVal O (pt u : O) + addVal O (k : O) := by
    intro k
    have := lte_nat hl hlm k _ (pt u).2 h
    rwa [coe_pt, add_sub_cancel] at this
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, Int.cast_natCast, ← key k, coe_pt]
    simp
  · have e : (pt (u ^ (-(k : ℤ))) : O) = ((-((u : Oˣ) ^ k)⁻¹ : Oˣ) : O) * (((u : Oˣ) : O) ^ k - 1) := by
      rw [coe_pt, zpow_neg, zpow_natCast, ← Units.val_pow_eq_pow_val, Units.val_neg, neg_mul, mul_sub,
        Units.inv_mul, mul_one, neg_sub]
      simp
    rw [e, IsDiscreteValuationRing.addVal_mul, key k,
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 (Units.isUnit _), zero_add, Int.cast_neg,
      Int.cast_natCast, AddValuation.map_neg]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.MemMaxPow
section
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem mem_max_iff {O : Type} [CommRing O] [IsLocalRing O] (f : O⟦X⟧) :
    f ∈ maximalIdeal O⟦X⟧ ↔ constantCoeff f ∈ maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]

private theorem C_mem_pow {O : Type} [CommRing O] [IsLocalRing O] (k : ℕ) (a : O)
    (ha : a ∈ maximalIdeal O ^ k) : (C a : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ ^ k := by
  have h1 : Ideal.map (C : O →+* O⟦X⟧) (maximalIdeal O) ≤ maximalIdeal O⟦X⟧ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_max_iff]
    simpa using hx
  have h2 := Ideal.mem_map_of_mem (C : O →+* O⟦X⟧) ha
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 k h2

theorem UpperTheory.V.abelian₂.mem_max_pow :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (f : O⟦X⟧) (n : ℕ),
      f ∈ maximalIdeal O⟦X⟧ ^ n ↔ ∀ i, coeff i f ∈ maximalIdeal O ^ (n - i) := by
  intro O _ _ f n
  constructor
  · intro hf
    induction n generalizing f with
    | zero => intro i; simp
    | succ n ih =>
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb i
        rw [PowerSeries.coeff_mul]
        refine Ideal.sum_mem _ ?_
        intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        have h1 := ih a ha p.1
        have h2 : coeff p.2 b ∈ maximalIdeal O ^ (1 - p.2) := by
          rcases Nat.eq_zero_or_pos p.2 with h | h
          · rw [h, PowerSeries.coeff_zero_eq_constantCoeff_apply]
            simpa using (mem_max_iff b).1 hb
          · rw [Nat.sub_eq_zero_of_le h]
            simp
        have h3 := Ideal.mul_mem_mul h1 h2
        rw [← pow_add] at h3
        exact Ideal.pow_le_pow_right (by omega) h3
      · intro x y hx hy i
        rw [map_add (f := _)]
        exact Ideal.add_mem _ (hx i) (hy i)
  · intro h
    induction n generalizing f with
    | zero => simp
    | succ n ih =>
      rw [PowerSeries.eq_X_mul_shift_add_const f]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ']
        refine Ideal.mul_mem_mul ?_ ?_
        · exact (mem_max_iff X).2 (by simp)
        · apply ih
          intro i
          rw [PowerSeries.coeff_mk]
          have := h (i + 1)
          simpa using this
      · apply C_mem_pow
        have := h 0
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.MuDvd
section
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

theorem UpperTheory.V.abelian₂.mu_dvd :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ f : O⟦X⟧,
      (∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f) ∧ (mu f = 0 ↔ map (residue O) f ≠ 0) ∧
        (mu f = 0 → lam f = (map (residue O) f).order.toNat) ∧
        ∀ m : ℕ, mu (C ϖ ^ m * f) = m + mu f ∧ lam (C ϖ ^ m * f) = lam f := by
  intro O _ _ _ ϖ hϖ f
  have hpow : ∀ m : ℕ, addVal O (ϖ ^ m) = m := by
    intro m
    rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp
  have hdvd : ∀ m : ℕ, C ϖ ^ m ∣ f ↔ ∀ n, ϖ ^ m ∣ coeff n f := by
    intro m
    constructor
    · rintro ⟨g, rfl⟩ n
      rw [← map_pow, PowerSeries.coeff_C_mul]
      exact dvd_mul_right _ _
    · intro h
      choose g hg using h
      refine ⟨PowerSeries.mk g, ?_⟩
      ext n
      rw [← map_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hg n]
  have h1 : ∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f := by
    intro m
    rw [hdvd, mu, le_iInf_iff]
    refine forall_congr' fun n => ?_
    rw [← hpow m, IsDiscreteValuationRing.addVal_le_iff_dvd]
  have hmu0 : mu f = 0 → map (residue O) f ≠ 0 := by
    intro h hzero
    have hc := addVal_coeff_lam f
    rw [h, IsDiscreteValuationRing.addVal_eq_zero_iff, ← residue_ne_zero_iff_isUnit] at hc
    apply hc
    rw [← PowerSeries.coeff_map, hzero, map_zero]
  refine ⟨h1, ⟨hmu0, ?_⟩, ?_, ?_⟩
  · intro h
    obtain ⟨n, hn⟩ : ∃ n, coeff n (map (residue O) f) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact h (PowerSeries.ext fun n => by simpa using hall n)
    rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit,
      ← IsDiscreteValuationRing.addVal_eq_zero_iff] at hn
    have hle := mu_le f n
    rw [hn] at hle
    exact le_antisymm hle bot_le
  · intro h
    have hord : (map (residue O) f).order = (lam f : ℕ∞) := by
      rw [PowerSeries.order_eq_nat]
      constructor
      · rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit,
          ← IsDiscreteValuationRing.addVal_eq_zero_iff, addVal_coeff_lam, h]
      · intro i hi
        rw [PowerSeries.coeff_map]
        by_contra hne
        have hu : IsUnit (coeff i f) := (residue_ne_zero_iff_isUnit _).1 hne
        rw [← IsDiscreteValuationRing.addVal_eq_zero_iff] at hu
        have hli : lam f ≤ i := Nat.sInf_le (by
          show addVal O (coeff i f) = mu f
          rw [hu, h])
        omega
    rw [hord, ENat.toNat_coe]
  · intro m
    have hcoeff : ∀ n, addVal O (coeff n (C ϖ ^ m * f)) = m + addVal O (coeff n f) := by
      intro n
      rw [← map_pow, PowerSeries.coeff_C_mul, IsDiscreteValuationRing.addVal_mul, hpow]
    have hmu : mu (C ϖ ^ m * f) = m + mu f := by
      rw [mu, mu, ENat.add_iInf]
      exact iInf_congr hcoeff
    refine ⟨hmu, ?_⟩
    rw [lam, lam]
    congr 1
    ext n
    simp only [Set.mem_setOf_eq, hcoeff, hmu]
    exact ⟨fun h => WithTop.add_left_cancel (ENat.coe_ne_top m) h, fun h => by rw [h]⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
section
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem mem_smul_top_iff_repr {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun a c ha hc => ?_)
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · rw [map_add (f := _), Finsupp.add_apply]
      exact I.add_mem ha hc
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial

private theorem prec_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] :
    IsPrecomplete I M := ⟨fun f hf => by
  let b := Module.Free.chooseBasis R M
  have key : ∀ i, ∃ L : R, ∀ k, b.repr (f k) i - L ∈ I ^ k := fun i => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun k => b.repr (f k) i)
      (fun {m n} hmn => by
        have h := hf hmn
        rw [SModEq.sub_mem, mem_smul_top_iff_repr b] at h
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using h i)
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using key
  refine ⟨b.equivFun.symm L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
  intro i
  have : b.repr (b.equivFun.symm L) i = L i := by
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [map_sub, Finsupp.sub_apply, this]
  exact hL i n⟩

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

theorem UpperTheory.V.abelian₂.dvr_finite :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      IsAdicComplete (maximalIdeal O) O ∧ Finite (ResidueField O) ∧ (l : O) ∈ maximalIdeal O ∧
        Function.Injective (algebraMap ℤ_[l] O) ∧ Module.Free ℤ_[l] O ∧ IsLocalHom (algebraMap ℤ_[l] O) := by
  intro l hl O _ _ _ _ _ _
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hinj : Function.Injective (algebraMap ℤ_[l] O) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    exact mul_ne_zero ((PadicInt.unitCoeff h0).isUnit.map _).ne_zero (pow_ne_zero _ hl0) hx
  have : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hfree : Module.Free ℤ_[l] O := Module.free_of_finite_type_torsion_free'
  have hloc : IsLocalHom (algebraMap ℤ_[l] O) := inferInstance
  have hlm : (l : O) ∈ maximalIdeal O := by
    have h : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    have := map_nonunit (algebraMap ℤ_[l] O) _ h
    rwa [map_natCast] at this
  have hres : Finite (ResidueField O) := by
    have : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  refine ⟨?_, hres, hlm, hinj, hfree, hloc⟩
  have hP : IsPrecomplete (maximalIdeal O) O := by
    have h1 : IsPrecomplete ((maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) O :=
      IsPrecomplete.map_algebraMap_iff.2 (prec_free _)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast] at h1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := Ideal.span {(l : O)}) (by simpa using hl0) hϖ
    refine prec_cofinal ((Ideal.span_singleton_le_iff_mem _).2 hlm) (e := e) ?_ h1
    rw [he, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
end

