module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvr
section
open scoped NNReal TensorProduct

namespace GlobalTheory.KLC

open IsDedekindDomain

theorem completeSpace_withAbs_of_unitBall (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K]
    [Algebra R K] [IsFractionRing R K] (f : AbsoluteValue K ℝ)
    (h : ∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) :
    CompleteSpace (WithAbs f) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let em : R →+* WithAbs f := (WithAbs.equiv f).symm.toRingHom.comp (algebraMap R K)
  have hnorm : ∀ x : R, ‖em x‖ = f (algebraMap R K x) := fun x => rfl
  have hinj : Function.Injective em := (WithAbs.equiv f).symm.injective.comp hinjK
  have hem0 : em π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have hpos : 0 < ‖em π‖ := norm_pos_iff.2 hem0
  have hle : ∀ x, ‖em x‖ ≤ 1 := fun x => (h _).2 ⟨x, rfl⟩
  have key : ∀ (n : ℕ) (x : R), x ∈ IsLocalRing.maximalIdeal R ^ n ↔ ‖em x‖ ≤ ‖em π‖ ^ n := by
    intro n x
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      rw [map_mul, map_pow, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hle y)
    · intro hx
      rw [hnorm, hnorm] at hx
      have hπK : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinjK).2 hπ.ne_zero
      obtain ⟨y, hy⟩ := (h (algebraMap R K x / algebraMap R K π ^ n)).1 (by
        rw [map_div₀, map_pow]
        exact div_le_one_of_le₀ hx (by positivity))
      refine ⟨y, hinjK ?_⟩
      rw [map_mul, map_pow, hy, mul_div_cancel₀ _ (pow_ne_zero _ hπK)]
  have hlt : ‖em π‖ < 1 := by
    by_contra hge
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R ^ 1 := (key 1 1).2 (by simpa using hge)
    rw [pow_one] at this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine Metric.complete_of_convergent_controlled_sequences (fun n => ‖em π‖ ^ n)
    (fun n => by positivity) ?_
  intro u hu
  have hv : ∀ n, ∃ v : R, em v = u n - u 0 := by
    intro n
    obtain ⟨v, hv⟩ := (h ((u n - u 0).ofAbs)).1 (by
      have := hu 0 n 0 (Nat.zero_le _) le_rfl
      rw [dist_eq_norm, pow_zero, WithAbs.norm_eq_apply_ofAbs] at this
      exact this.le)
    refine ⟨v, ?_⟩
    show WithAbs.toAbs f (algebraMap R K v) = _
    rw [hv, WithAbs.toAbs_ofAbs]
  choose v hv using hv
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal R) (M := R) inferInstance
    (f := v) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv, hv,
        sub_sub_sub_cancel_right]
      have := hu m m n le_rfl hmn
      rw [dist_eq_norm] at this
      exact this.le)
  refine ⟨em L + u 0, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt)
  have := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv] at this
  rw [dist_eq_norm]
  have e : u n - (em L + u 0) = u n - u 0 - em L := by abel
  rw [e]
  exact this

theorem exists_absoluteValue_completeSpace_of_isDiscreteValuationRing :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K] [Algebra R K]
      [IsFractionRing R K], ∃ f : AbsoluteValue K ℝ, IsNonarchimedean f ∧ f.IsNontrivial ∧
      (∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) ∧ CompleteSpace (WithAbs f) := by
  intro R K _ _ _ _ _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let v := IsDiscreteValuationRing.maximalIdeal R
  have hb : (1 : ℝ≥0) < 2 := one_lt_two
  have hball : ∀ x : K, v.adicAbv hb x ≤ 1 ↔ x ∈ Set.range (algebraMap R K) := by
    intro x
    have : v.adicAbv hb x ≤ 1 ↔ v.valuation K x ≤ 1 := by
      rw [← WithZeroMulInt.toNNReal_le_one_iff hb, ← NNReal.coe_le_coe]
      rfl
    rw [this]
    exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one,
      fun ⟨y, hy⟩ => hy ▸ v.valuation_le_one y⟩
  refine ⟨v.adicAbv hb, v.isNonarchimedean_adicAbv hb, ?_, hball,
    completeSpace_withAbs_of_unitBall R K _ hball⟩
  have hπK : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  have h1 : v.valuation K (algebraMap R K π) < 1 :=
    (v.valuation_lt_one_iff_mem π).2
      (show π ∈ IsLocalRing.maximalIdeal R from (IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)
  have h2 : WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) < 1 := by
    have := WithZeroMulInt.toNNReal_strictMono hb h1
    rwa [map_one] at this
  refine ⟨algebraMap R K π, hπK, ?_⟩
  intro heq
  have : ((WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) : ℝ≥0) : ℝ)
      = 1 := heq
  exact absurd (NNReal.coe_lt_coe.2 h2) (by rw [this]; simp)

end GlobalTheory.KLC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharParityMulNeOneMulInvNeOne
section
namespace GlobalTheory

theorem exists_char_parity_mul_ne_one_mul_inv_ne_one : ∀ (N r : ℕ) (χ : DirichletCharacter ℂ N) (sg : ℂ), 0 < N → r.Prime → 7 ≤ r → r ∣ N → (sg = 1 ∨ sg = -1) → ∃ θ : DirichletCharacter ℂ N, θ (-1) = sg ∧ θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1 := by
  intro N r χ sg hN hr hr7 hrN hsg
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hrle : r ≤ N := Nat.le_of_dvd hN hrN

  haveI : Fact (2 < N) := ⟨by omega⟩
  have hm1 : (-1 : ZMod N) ≠ 1 := ZMod.neg_one_ne_one
  obtain ⟨θ₁, hθ₁⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hm1
  have hsq : ∀ ψ : DirichletCharacter ℂ N, ψ (-1) * ψ (-1) = 1 := by
    intro ψ
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hθ₁' : θ₁ (-1) = -1 := by
    rcases mul_self_eq_one_iff.mp (hsq θ₁) with h | h
    · exact absurd h hθ₁
    · exact h

  have h16 : (16 : ZMod r) ≠ 1 := by
    intro h
    have h15 : ((15 : ℕ) : ZMod r) = 0 := by
      have : (16 : ZMod r) - 1 = 0 := by rw [h]; ring
      have e : ((15 : ℕ) : ZMod r) = (16 : ZMod r) - 1 := by push_cast; ring
      rw [e, this]
    rw [ZMod.natCast_eq_zero_iff] at h15
    have h35 : r ∣ 3 * 5 := by norm_num; exact h15
    rcases (Nat.Prime.dvd_mul hr).mp h35 with h3 | h5
    · have := Nat.le_of_dvd (by norm_num) h3; omega
    · have := Nat.le_of_dvd (by norm_num) h5; omega
  obtain ⟨κ, hκ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ h16
  set ψ : DirichletCharacter ℂ N := DirichletCharacter.changeLevel hrN κ with hψ
  have hη4 : ψ ^ 4 ≠ 1 := by
    intro h
    have h' : DirichletCharacter.changeLevel hrN (κ ^ 4) = DirichletCharacter.changeLevel hrN 1 := by
      rw [map_pow, map_one]; exact h
    have hk := DirichletCharacter.changeLevel_injective hrN h'
    apply hκ
    have : (κ ^ 4) 2 = (1 : DirichletCharacter ℂ r) 2 := by rw [hk]
    have hu : IsUnit (2 : ZMod r) := by
      have : (2 : ZMod r) = ((2 : ℕ) : ZMod r) := by norm_cast
      rw [this, ZMod.isUnit_iff_coprime]
      exact (Nat.coprime_primes Nat.prime_two hr).mpr (by omega)
    rw [MulChar.one_apply hu, MulChar.pow_apply' _ (by norm_num)] at this
    have e : (16 : ZMod r) = 2 ^ 4 := by norm_num
    rw [e, map_pow]; exact this
  set η : DirichletCharacter ℂ N := ψ ^ 2 with hηdef
  have hηsq : η ^ 2 ≠ 1 := by
    rw [hηdef, ← pow_mul]; exact hη4
  have hη1 : η ≠ 1 := by
    intro h; apply hηsq; rw [h, one_pow]
  have hη2 : η (-1) = 1 := by
    rw [hηdef, pow_two, MulChar.mul_apply, hsq]
  have hη2' : (η ^ 2) (-1) = 1 := by
    rw [pow_two, MulChar.mul_apply, hη2, mul_one]

  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : DirichletCharacter ℂ N, θ₀ (-1) = sg := by
    rcases hsg with h | h
    · exact ⟨1, by rw [h]; exact MulChar.one_apply (isUnit_one.neg)⟩
    · exact ⟨θ₁, by rw [h, hθ₁']⟩

  have hab : θ₀ ≠ θ₀ * η := by
    intro h; apply hη1; exact left_eq_mul.mp h
  have hbc : θ₀ * η ≠ θ₀ * η ^ 2 := by
    intro h; apply hη1
    have h' := mul_left_cancel h
    rw [pow_two] at h'
    exact left_eq_mul.mp h'
  have hac : θ₀ ≠ θ₀ * η ^ 2 := by
    intro h; apply hηsq; exact left_eq_mul.mp h
  have key : ∀ θ : DirichletCharacter ℂ N, ¬ (θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1) → θ = χ⁻¹ ∨ θ = χ := by
    intro θ h
    by_cases h1 : θ * χ = 1
    · exact Or.inl (eq_inv_of_mul_eq_one_left h1)
    · have h2 : θ * χ⁻¹ = 1 := by
        by_contra h2; exact h ⟨h1, h2⟩
      right
      have := eq_inv_of_mul_eq_one_left h2
      rwa [inv_inv] at this
  by_contra hno
  push_neg at hno
  have ha := key θ₀ (fun h => by have := hno θ₀ hθ₀ h.1; exact h.2 this)
  have hb := key (θ₀ * η) (fun h => by
    have := hno (θ₀ * η) (by rw [MulChar.mul_apply, hθ₀, hη2, mul_one]) h.1; exact h.2 this)
  have hc := key (θ₀ * η ^ 2) (fun h => by
    have := hno (θ₀ * η ^ 2) (by rw [MulChar.mul_apply, hθ₀, hη2', mul_one]) h.1; exact h.2 this)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    first
    | exact hab (ha.trans hb.symm)
    | exact hac (ha.trans hc.symm)
    | exact hbc (hb.trans hc.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsChooseSmallPadicValAxInduction
section
namespace GlobalTheory

private lemma not_dvd_choose_prime_pow_of_between {p : ℕ} (hp : p.Prime) :
    ∀ (k N : ℕ), p ^ k ≤ N → N < p ^ (k + 1) → ¬ p ∣ N.choose (p ^ k) := by
  haveI := Fact.mk hp
  intro k
  induction k with
  | zero =>
    intro N h1 h2 hdvd
    simp only [pow_zero, zero_add, pow_one, Nat.choose_one_right] at h1 h2 hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  | succ k ih =>
    intro N h1 h2 hdvd
    have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := N) (k := p ^ (k + 1))
      (p := p)
    rw [pow_succ, Nat.mul_mod_left, Nat.choose_zero_right, one_mul,
      Nat.mul_div_cancel _ hp.pos, ← pow_succ] at hmod
    refine ih (N / p) ?_ ?_ ((hmod.dvd_iff (dvd_refl p)).1 hdvd)
    · exact (Nat.le_div_iff_mul_le hp.pos).2 (by rw [← pow_succ]; exact h1)
    · exact (Nat.div_lt_iff_lt_mul hp.pos).2 (by rw [← pow_succ]; exact h2)

theorem _root_.GlobalTheory.exists_choose_small_valuation_ax : ∀ (p : ℕ), p.Prime → ∀ N : ℕ, 2 ≤ N →
    ∃ j e : ℕ, 0 < j ∧ j < N ∧ ¬ p ^ (e + 1) ∣ N.choose j ∧
  (e : ℚ) / ((N - j : ℕ) : ℚ) + (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p (N - j)) ≤ (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p N) := by
  intro p hp N hN
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨k, hk⟩ : ∃ k, Nat.log p N = k := ⟨_, rfl⟩
  have hkle : p ^ k ≤ N := hk ▸ Nat.pow_log_le_self p (by omega)
  have hlt : N < p ^ (k + 1) := hk ▸ Nat.lt_pow_succ_log_self hp1 N
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  rcases hkle.lt_or_eq with hlt' | heq
  · refine ⟨N - p ^ k, 0, by omega, by omega, ?_, ?_⟩
    · rw [Nat.choose_symm_of_eq_add (b := p ^ k) (by omega), zero_add, pow_one]
      exact not_dvd_choose_prime_pow_of_between hp k N hkle hlt
    · have hm : N - (N - p ^ k) = p ^ k := by omega
      rw [hm, Nat.log_pow hp1, hk]
      simp
  · subst heq
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hN
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hpk' : 0 < p ^ k' := pow_pos hp.pos k'
    have hsucc : p ^ (k' + 1) = p ^ k' * p := pow_succ p k'
    have h2 : 2 * p ^ k' ≤ p ^ (k' + 1) := by
      rw [hsucc, mul_comm]; exact Nat.mul_le_mul le_rfl hp.two_le
    refine ⟨p ^ k', 1, hpk', by omega, ?_, ?_⟩
    · have hmult := hp.emultiplicity_choose_prime_pow (n := k' + 1) (k := p ^ k')
        (by omega) (pow_ne_zero _ hp.ne_zero)
      rw [multiplicity_pow_self_of_prime hp.prime k'] at hmult
      rw [pow_dvd_iff_le_emultiplicity, hmult]
      norm_num
    · have hlogm : Nat.log p (p ^ (k' + 1) - p ^ k') = k' :=
        Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
      have hcast : ((p ^ (k' + 1) - p ^ k' : ℕ) : ℚ) = (p : ℚ) ^ k' * ((p : ℚ) - 1) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hp1' : (p : ℚ) - 1 ≠ 0 := by
        have : (1 : ℚ) < p := by exact_mod_cast hp1
        linarith
      rw [hlogm, Nat.log_pow hp1, hcast]
      apply le_of_eq
      field_simp
      ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousExtension
section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace GlobalTheory.ContinuousValuationExtension

theorem continuous_of_valuation_eq {A B Γ : Type} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ] (g : A →+* B)
    (hs : Function.Surjective (Valued.v : A → Γ))
    (hg : ∀ x : A, (Valued.v (g x) : Γ) = Valued.v x) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero A Γ).tendsto_iff (Valued.hasBasis_nhds_zero B Γ)]
  intro γ _

  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, ha]
    intro h0
    apply γ.ne_zero
    apply MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
    rw [h0, map_zero]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff, ha] at hx
  show (Valued.v : Valuation B Γ).restrict (g x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, hg]
  exact hx

theorem valuation_eq_of_denseRange {A B Γ ι : Type} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ] (φ : A →+* B)
    (hφ : Continuous φ) (j : ι → A) (hj : DenseRange j)
    (h : ∀ x : ι, (Valued.v (φ (j x)) : Γ) = Valued.v (j x)) (y : A) :
    (Valued.v (φ y) : Γ) = Valued.v y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hφy : φ y ≠ 0 := (map_ne_zero φ).2 hy

  have h1 : {z : A | (Valued.v z : Γ) = Valued.v y} ∈ nhds y :=
    Valued.locally_const ((Valuation.ne_zero_iff _).2 hy)
  have h2 : {z : A | (Valued.v (φ z) : Γ) = Valued.v (φ y)} ∈ nhds y :=
    hφ.continuousAt.preimage_mem_nhds (Valued.locally_const ((Valuation.ne_zero_iff _).2 hφy))
  obtain ⟨_, ⟨x, rfl⟩, hx1, hx2⟩ := hj.inter_nhds_nonempty (Filter.inter_mem h1 h2)
  have e1 : (Valued.v (j x) : Γ) = Valued.v y := hx1
  have e2 : (Valued.v (φ (j x)) : Γ) = Valued.v (φ y) := hx2
  rw [← e2, h x, e1]

theorem exists_continuous_extension {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] (w : HeightOneSpectrum (RingOfIntegers K))
    (u : HeightOneSpectrum (RingOfIntegers L)) (f : K →+* adicCompletion L u)
    (hf : ∀ x : K, (Valued.v (f x) : WithZero (Multiplicative ℤ)) = valuation K w x) :
    ∃ φ : adicCompletion K w →+* adicCompletion L u, Continuous φ ∧
      (∀ x : K, φ (algebraMap K (adicCompletion K w) x) = f x) ∧
      ∀ y : adicCompletion K w,
        (Valued.v (φ y) : WithZero (Multiplicative ℤ)) = Valued.v y := by
  let g : WithVal (w.valuation K) →+* adicCompletion L u :=
    f.comp (WithVal.equiv (w.valuation K)).toRingHom
  have hgv : ∀ x : WithVal (w.valuation K),
      (Valued.v (g x) : WithZero (Multiplicative ℤ)) = Valued.v x := fun x => hf x.ofVal
  have hsurj : Function.Surjective
      (Valued.v : WithVal (w.valuation K) → WithZero (Multiplicative ℤ)) := fun γ => by
    obtain ⟨a, ha⟩ := w.valuation_surjective K γ
    exact ⟨WithVal.toVal _ a, ha⟩
  have hgc : Continuous g := continuous_of_valuation_eq g hsurj hgv

  let φ : adicCompletion K w →+* adicCompletion L u :=
    (UniformSpace.Completion.extensionHom g hgc).comp (adicCompletion.equiv K w).toRingHom
  have hφc : Continuous φ :=
    UniformSpace.Completion.continuous_extension.comp (adicCompletion.continuous_toCompletion K w)
  have hφf : ∀ x : K, φ (algebraMap K (adicCompletion K w) x) = f x := fun x =>
    UniformSpace.Completion.extensionHom_coe g hgc (WithVal.toVal _ x)
  refine ⟨φ, hφc, hφf, fun y => ?_⟩
  refine valuation_eq_of_denseRange φ hφc (algebraMap K (adicCompletion K w))
    (denseRange_algebraMap (K := K) (v := w)) (fun x => ?_) y
  rw [hφf x, hf x]
  exact (adicCompletion.valued_coe K w x).symm

end GlobalTheory.ContinuousValuationExtension
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorValuationPrimeDvdPowSubOfFinitePa
section
namespace GlobalTheory

theorem exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt :
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ v : Valuation Ω NNReal, (∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1) → v (p : Ω) < 1 →
  ∀ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R → IsPrincipalIdealRing R →
  ∃ π ∈ R, π ≠ 0 ∧ v π < 1 ∧ (p : Ω) / π ∈ R ∧ ∃ f : ℕ, 0 < f ∧ ∀ t ∈ R, (t ^ p ^ f - t) / π ∈ R := by
  intro p _ Ω _ _ hinj v hint hp R hfin hpid
  have hle : ∀ x : R, v (x : Ω) ≤ 1 := fun x => hint _ ((IsIntegral.of_finite ℤ_[p] x).map R.val)
  obtain ⟨P, hP⟩ : ∃ P : Ideal R, ∀ x, x ∈ P ↔ v (x : Ω) < 1 := by
    refine ⟨{ carrier := {x | v (x : Ω) < 1}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun x => Iff.rfl⟩
    · intro a b ha hb
      simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at *
      exact lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)
    · simp
    · intro c x hx
      simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, map_mul] at *
      calc v (c:Ω) * v x ≤ 1 * v x := mul_le_mul' (hle c) le_rfl
        _ = v x := one_mul _
        _ < 1 := hx
  have hpR : ((p : R) : Ω) = (p : Ω) := by simp
  have hpP : (p : R) ∈ P := by rw [hP, hpR]; exact hp
  have hp0 : (p : Ω) ≠ 0 := by
    intro h
    have h1 : algebraMap ℤ_[p] Ω (p : ℤ_[p]) = algebraMap ℤ_[p] Ω 0 := by simp [h]
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (hinj h1)
  have hPprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro h
      have h1 : (1 : R) ∈ P := h ▸ Submodule.mem_top
      rw [hP] at h1; simp at h1
    · intro x y hxy
      rw [hP, hP]; rw [hP] at hxy
      simp only [Subalgebra.coe_mul, map_mul] at hxy
      by_contra hc
      push_neg at hc
      have hx1 : v x = 1 := le_antisymm (hle x) hc.1
      have hy1 : v y = 1 := le_antisymm (hle y) hc.2
      rw [hx1, hy1, one_mul] at hxy
      exact lt_irrefl _ hxy
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    apply hp0; rw [← hpR, hpP]; rfl
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hPne
  set g := Submodule.IsPrincipal.generator P with hgdef
  have hgmem : g ∈ P := Submodule.IsPrincipal.generator_mem P
  have hg0 : g ≠ 0 := by
    intro h; apply hPne
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero P).mpr h
  have hdvd : ∀ x : R, x ∈ P → ∃ c : R, x = g * c := fun x hx =>
    (Submodule.IsPrincipal.mem_iff_generator_dvd P).mp hx

  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hpk : ((p : ℕ) : R ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hpP
  have hchar : CharP (R ⧸ P) p := by
    rw [← ringChar.eq_iff]
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp (ringChar.dvd hpk) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  have hunder : P.under ℤ_[p] = IsLocalRing.maximalIdeal ℤ_[p] := by
    apply le_antisymm
    · apply IsLocalRing.le_maximalIdeal
      intro h
      apply hPprime.ne_top
      rw [Ideal.eq_top_iff_one] at h ⊢
      simpa [Ideal.mem_comap] using h
    · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]
      show (p : ℤ_[p]) ∈ P.comap (algebraMap ℤ_[p] R)
      rw [Ideal.mem_comap, map_natCast]; exact hpP
  haveI : Finite (ℤ_[p] ⧸ P.under ℤ_[p]) := by
    rw [hunder]
    exact Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  haveI : Finite (R ⧸ P) := Module.finite_of_finite (ℤ_[p] ⧸ P.under ℤ_[p])
  letI := Fintype.ofFinite (R ⧸ P)
  obtain ⟨n, -, hcard⟩ := FiniteField.card (R ⧸ P) p
  refine ⟨(g : Ω), g.2, ?_, ?_, ?_, (n : ℕ), n.pos, ?_⟩
  · exact fun h => hg0 (Subtype.ext h)
  · exact (hP g).mp hgmem
  · obtain ⟨c, hc⟩ := hdvd _ hpP
    have : (p : Ω) = (g : Ω) * (c : Ω) := by rw [← hpR, hc]; rfl
    rw [this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]
    exact c.2
  · intro t ht
    have hmk : Ideal.Quotient.mk P (⟨t, ht⟩ ^ p ^ (n : ℕ)) = Ideal.Quotient.mk P ⟨t, ht⟩ := by
      rw [map_pow, ← hcard, FiniteField.pow_card]
    rw [Ideal.Quotient.eq] at hmk
    obtain ⟨c, hc⟩ := hdvd _ hmk
    have : t ^ p ^ (n : ℕ) - t = (g : Ω) * (c : Ω) := by
      have := congrArg (fun x : R => (x : Ω)) hc
      simpa using this
    rw [this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]
    exact c.2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PosDefExistsFrame
section
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem posDef_exists_frame :
    ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℂ), G.PosDef →
      ∃ X : Matrix (Fin d) (Fin d) ℂ, IsUnit X.det ∧ (X⁻¹)ᴴ * X⁻¹ = G := by
  intro d G hG
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg
  have hu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hBu : IsUnit B.det := by
    rw [hB, Matrix.det_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det B hBu, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv B hBu, hB, Matrix.star_eq_conjTranspose]

end GlobalTheory
end

